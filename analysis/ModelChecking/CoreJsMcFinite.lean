/-
  # Core JavaScript — Model checking the program: the finite form

  The program automaton labeled by an analysis result (`CoreJsMcInstance.lean`)
  is not something the algorithm can run on: its location sets and value sets
  are predicates, its edges an inductive relation, and its abstract values
  (`Option ALoc`) infinitely many.  This file states what a *finite form* of
  it is, and proves that model checking a finite form finds every run of the
  program matching the query.

  * **Finitely many abstract values** (`FV locs`): an abstract location of a
    given finite list `locs`, or `•` (`none`) for every other one — and for a
    location the abstraction does not map.  The collapse `FV.cl` is what makes
    the non-relational domain and the trackers finite (`FV.mem_all`).
  * **Location-list actions** (`FAct V`) and **finite facts** (`FFacts V`),
    with their abstraction `listAbs`: matching is membership of a variable's
    value in a position's list, predicates read Boolean tables.  `listAbs` is
    sound (`listAbs_sound`) and separable (`listSep`), for any `V`.
  * **Finite form** (`FinForm Γ s₀ L locs`): a finite trace system over
    `FAct (FV locs)` with a complete walk for each complete walk of the
    automaton, whose labels contain the automaton's collapsed labels
    position by position (`FAct.Over`), and finite facts containing the
    collapsed final configurations (`FFacts.Over`).  Coverage moves from the
    automaton to the finite form (`Covers.of_finite`).
  * `FinForm.check` runs the algorithm (non-relational domain, enumerating
    trackers) on a finite form.  `FinForm.check_complete`: **every run of the
    program from its initial configuration that matches a well-formed query
    yields a witness**, for any analysis result and any finite form of it.
  * Finite forms always exist: `FinForm.univ` is the coarsest one (one state,
    every action, every fact), given the arities of the program's functions;
    `check_complete_univ` is the corollary with no finite-form assumption.

  Computing a finite form from the analysis — finite location sets in the
  labeling, and the automaton's reachable states and edges — is outside this
  development: the analysis is stated over predicates, and the least analysis
  result is not claimed computable (`CoreJsAutomatonTotality.lean`).

  Plain Lean 4 — no Mathlib required.
-/

import ModelChecking.CoreJsMcInstance

namespace CoreJS

/-! ## Finitely many abstract values -/

/-- An abstract location of `locs`, or `•` (`none`). -/
abbrev FV (locs : List ALoc) := {v : Option ALoc // ∀ al, v = some al → al ∈ locs}

/-- `•`. -/
def FV.none (locs : List ALoc) : FV locs := ⟨Option.none, fun _ h => by cases h⟩

instance (locs : List ALoc) : Inhabited (FV locs) := ⟨FV.none locs⟩

/-- The collapse: a location of `locs` stays itself, any other becomes `•`. -/
def FV.cl (locs : List ALoc) (al : ALoc) : FV locs :=
  if h : al ∈ locs then ⟨some al, fun _ e => Option.some.inj e ▸ h⟩ else FV.none locs

/-- Every value. -/
def FV.all (locs : List ALoc) : List (FV locs) :=
  FV.none locs :: locs.attach.map fun a => ⟨some a.1, fun _ e => Option.some.inj e ▸ a.2⟩

theorem FV.mem_all (locs : List ALoc) : ∀ v : FV locs, v ∈ FV.all locs
  | ⟨Option.none, _⟩ => List.mem_cons_self ..
  | ⟨some al, h⟩ => List.mem_cons_of_mem _ (List.mem_map.2 ⟨⟨al, h al rfl⟩, List.mem_attach .., rfl⟩)

/-! ## Location-list actions and finite facts -/

/-- Abstract actions whose positions are finite lists of values. -/
inductive FAct (V : Type) where
  | lookup (L₁ L₂ L₃ : List V)
  | update (L₁ L₂ L₃ : List V)
  | call   (f : V) (Ls : List (List V))
  | ret    (f : V) (L : List V)
  deriving DecidableEq

/-- Facts as Boolean tables over values. -/
structure FFacts (V : Type) where
  dep : V → V → Bool
  ac  : V → Bool
  sk  : V → Bool
  hv  : V → Val → Bool
  sv  : V → V → Bool

section listAbs

variable {V : Type} [DecidableEq V]

/-- A concrete action abstracted by a location-list action, under `α`. -/
def FActAlpha (α : Loc → V) : Act → FAct V → Prop
  | .lookup l₁ l₂ l₃, .lookup L₁ L₂ L₃ => α l₁ ∈ L₁ ∧ α l₂ ∈ L₂ ∧ α l₃ ∈ L₃
  | .update l₁ l₂ l₃, .update L₁ L₂ L₃ => α l₁ ∈ L₁ ∧ α l₂ ∈ L₂ ∧ α l₃ ∈ L₃
  | .call lf ls,      .call f Ls       => α lf = f ∧ Pointwise (fun l L => α l ∈ L) ls Ls
  | .ret lf l,        .ret f L         => α lf = f ∧ α l ∈ L
  | _,                _                => False

/-- A concrete observation abstracted by finite facts, under `α`. -/
def FFactsAlpha (α : Loc → V) (σ : Obs) (φ : FFacts V) : Prop :=
  (∀ l₁ l₂, σ.dep l₁ l₂ → φ.dep (α l₁) (α l₂) = true) ∧
  (∀ l, σ.ac l → φ.ac (α l) = true) ∧
  (∀ l, σ.sk l → φ.sk (α l) = true) ∧
  (∀ l v, σ.val l = some v → φ.hv (α l) v = true) ∧
  (∀ l₁ l₂ v, σ.val l₁ = some v → σ.val l₂ = some v → φ.sv (α l₁) (α l₂) = true)

/-! ### Matching, as constraints on single variables -/

/-- The constraints of the argument positions. -/
def sepArgs : List MVar → List (List V) → Option (List (MVar × (V → Bool)))
  | [],      []      => some []
  | x :: xs, L :: Ls => (sepArgs xs Ls).map ((x, fun v => decide (v ∈ L)) :: ·)
  | _,       _       => none

/-- The constraints of a query action against a location-list action
    (`none`: no match). -/
def fsep : QAct MVar → FAct V → Option (List (MVar × (V → Bool)))
  | .lookup x₁ x₂ x₃, .lookup L₁ L₂ L₃ =>
      some [(x₁, fun v => decide (v ∈ L₁)), (x₂, fun v => decide (v ∈ L₂)),
        (x₃, fun v => decide (v ∈ L₃))]
  | .update x₁ x₂ x₃, .update L₁ L₂ L₃ =>
      some [(x₁, fun v => decide (v ∈ L₁)), (x₂, fun v => decide (v ∈ L₂)),
        (x₃, fun v => decide (v ∈ L₃))]
  | .call xf xs,      .call f Ls       => (sepArgs xs Ls).map ((xf, fun v => decide (v = f)) :: ·)
  | .retn xf x,       .ret f L         =>
      some [(xf, fun v => decide (v = f)), (x, fun v => decide (v ∈ L))]
  | _,                _                => none

theorem sepArgs_vars : ∀ (xs : List MVar) (Ls : List (List V)) cs, sepArgs xs Ls = some cs →
    ∀ c ∈ cs, c.1 ∈ xs
  | [], [], cs, h => by simp [sepArgs] at h; subst h; simp
  | [], _ :: _, _, h => by simp [sepArgs] at h
  | _ :: _, [], _, h => by simp [sepArgs] at h
  | x :: xs, L :: Ls, cs, h => by
      simp only [sepArgs] at h
      cases hs : sepArgs xs Ls with
      | none => rw [hs] at h; cases h
      | some cs' =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (sepArgs_vars xs Ls cs' hs c hc)

theorem sepArgs_of_pointwise {α : Loc → V} {ξ : MEnv} :
    ∀ {xs : List MVar} {Ls : List (List V)}, Pointwise (fun l L => α l ∈ L) (xs.map ξ) Ls →
      ∃ cs, sepArgs xs Ls = some cs ∧ ∀ c ∈ cs, c.2 (α (ξ c.1)) = true
  | [], [], _ => ⟨[], rfl, by simp⟩
  | x :: _, L :: _, ⟨hx, h⟩ => by
      obtain ⟨cs, hcs, h'⟩ := sepArgs_of_pointwise h
      refine ⟨(x, fun v => decide (v ∈ L)) :: cs, by simp only [sepArgs, hcs, Option.map_some],
        fun c hc => ?_⟩
      rcases List.mem_cons.1 hc with rfl | hc
      · simpa using hx
      · exact h' c hc

/-- Matching a query action against a location-list action. -/
def FMatch (ξ : MVar → V) (b : QAct MVar) (B : FAct V) : Bool :=
  match fsep b B with
  | none    => false
  | some cs => cs.all fun c => c.2 (ξ c.1)

/-- Predicates read off the tables. -/
def FMay (φ : FFacts V) (ξ : MVar → V) : Pred MVar → Bool
  | .sk x      => φ.sk (ξ x)
  | .ac x      => φ.ac (ξ x)
  | .dep x₁ x₂ => φ.dep (ξ x₁) (ξ x₂)
  | .sv x₁ x₂  => φ.sv (ξ x₁) (ξ x₂)
  | .hv x c    => φ.hv (ξ x) c

/-- The abstraction by location-list actions and finite facts.  Nothing is
    certain: `must`, `mustA` and `inhab` are never true. -/
def listAbs : Abs (FAct V) V (FFacts V) where
  act    := FActAlpha
  facts  := FFactsAlpha
  matchA := FMatch
  may    := FMay
  must _ _ _  := false
  mustA _ _ _ := false
  inhab _ _   := false

theorem listAbs_sound : (listAbs : Abs (FAct V) V (FFacts V)).Sound where
  matchA α ξ a c B hB hc := by
    subst hc
    change FActAlpha α (a.inst ξ) B at hB
    show FMatch (α ∘ ξ) a B = true
    unfold FMatch
    cases a <;> cases B <;> simp only [QAct.inst, FActAlpha] at hB
    · simp [fsep, hB.1, hB.2.1, hB.2.2]
    · simp [fsep, hB.1, hB.2.1, hB.2.2]
    · obtain ⟨cs, hcs, h⟩ := sepArgs_of_pointwise hB.2
      simp only [fsep, hcs, Option.map_some, List.all_cons]
      simp only [Function.comp, hB.1, decide_true, Bool.true_and, List.all_eq_true]
      exact h
    · simp [fsep, hB.1, hB.2]
  may α σ φ ξ p hf hp := by
    obtain ⟨hdep, hac, hsk, hhv, hsv⟩ := hf
    show FMay φ (α ∘ ξ) p = true
    cases p with
    | sk x => exact hsk _ hp
    | ac x => exact hac _ hp
    | dep x₁ x₂ => exact hdep _ _ hp
    | sv x₁ x₂ => obtain ⟨v, h₁, h₂⟩ := hp; exact hsv _ _ v h₁ h₂
    | hv x c => exact hhv _ _ hp
  must _ _ _ _ _ _ h := by simp [listAbs] at h
  may_congr φ ξ ξ' p h := by
    show FMay φ ξ p = FMay φ ξ' p
    cases p <;> simp only [Pred.vars, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at h <;> simp only [FMay, h]
  must_congr _ _ _ _ _ := rfl
  mustA _ _ _ _ _ _ h := by simp [listAbs] at h
  mustA_congr _ _ _ _ _ := rfl
  inhab _ _ _ _ _ h := by simp [listAbs] at h

/-- Matching decomposes into constraints on single variables. -/
def listSep : (listAbs : Abs (FAct V) V (FFacts V)).Sep where
  sep := fsep
  spec ξ b B := by
    show FMatch ξ b B = true ↔ _
    unfold FMatch
    cases fsep b B <;> simp [List.all_eq_true]
  vars b B cs h := by
    cases b <;> cases B <;> simp only [fsep] at h <;> try cases h
    all_goals first
      | (intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
         rcases hc with rfl | rfl | rfl <;> simp [QAct.vars])
      | skip
    rename_i xf xs f Ls
    cases hs : sepArgs xs Ls with
    | none => rw [hs] at h; cases h
    | some cs' =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (sepArgs_vars xs Ls cs' hs c hc)

end listAbs

/-! ## From the automaton to a finite form -/

section over

variable {V : Type} (col : ALoc → V)

/-- The collapsed elements of a location set all lie in the list. -/
def SetOver (L : ALocSet) (M : List V) : Prop := ∀ al, L al → col al ∈ M

/-- The location-list action contains the automaton's action, collapsed by
    `col`. -/
def FAct.Over : AAct → FAct V → Prop
  | .lookup L₁ L₂ L₃, .lookup M₁ M₂ M₃ => SetOver col L₁ M₁ ∧ SetOver col L₂ M₂ ∧ SetOver col L₃ M₃
  | .update L₁ L₂ L₃, .update M₁ M₂ M₃ => SetOver col L₁ M₁ ∧ SetOver col L₂ M₂ ∧ SetOver col L₃ M₃
  | .call lf Ls,      .call f Ms       => col lf = f ∧ Pointwise (SetOver col) Ls Ms
  | .ret lf L,        .ret f M         => col lf = f ∧ SetOver col L M
  | _,                _                => False

/-- The finite facts contain the abstract configuration's, collapsed by
    `col`. -/
def FFacts.Over (φf : FFacts V) (φ : AConf) : Prop :=
  (∀ a₁ a₂, φ.reg.dep a₁ a₂ → φf.dep (col a₁) (col a₂) = true) ∧
  (∀ al, (φ.reg.ac al ∨ ∃ al', φ.reg.ac al' ∧ φ.reg.dep al al') → φf.ac (col al) = true) ∧
  (∀ al, φ.reg.sk al → φf.sk (col al) = true) ∧
  (∀ al v, (φ.heap.val al).Mem v → φf.hv (col al) v = true) ∧
  (∀ a₁ a₂ v, (φ.heap.val a₁).Mem v → (φ.heap.val a₂).Mem v → φf.sv (col a₁) (col a₂) = true)

/-- `α` collapsed: `d` where `α` maps nothing. -/
def colAlpha (d : V) (α : AlphaFn) : Loc → V := fun l => (α l).elim d col

variable {col}

theorem colAlpha_some {d : V} {α : AlphaFn} {l : Loc} {al : ALoc} (h : α l = some al) :
    colAlpha col d α l = col al := by
  simp [colAlpha, h]

theorem pointwise_over {d : V} {α : AlphaFn} :
    ∀ {ls : List Loc} {Ls : List ALocSet} {Ms : List (List V)}, LocsAlpha α ls Ls →
      Pointwise (SetOver col) Ls Ms → Pointwise (fun l M => colAlpha col d α l ∈ M) ls Ms
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨⟨al, hal, hL⟩, h⟩, ⟨hM, h'⟩ =>
      ⟨show colAlpha col d α _ ∈ _ by rw [colAlpha_some hal]; exact hM al hL, pointwise_over h h'⟩

theorem act_over {d : V} {α : AlphaFn} :
    ∀ {c : Act} {A : AAct} {F : FAct V}, Act.Alpha α c A → FAct.Over col A F →
      FActAlpha (colAlpha col d α) c F
  | .lookup _ _ _, .lookup _ _ _, .lookup _ _ _, ⟨⟨a₁, h₁, m₁⟩, ⟨a₂, h₂, m₂⟩, ⟨a₃, h₃, m₃⟩⟩,
      ⟨o₁, o₂, o₃⟩ =>
    ⟨(by rw [colAlpha_some h₁]; exact o₁ _ m₁), (by rw [colAlpha_some h₂]; exact o₂ _ m₂), (by rw [colAlpha_some h₃]; exact o₃ _ m₃)⟩
  | .update _ _ _, .update _ _ _, .update _ _ _, ⟨⟨a₁, h₁, m₁⟩, ⟨a₂, h₂, m₂⟩, ⟨a₃, h₃, m₃⟩⟩,
      ⟨o₁, o₂, o₃⟩ =>
    ⟨(by rw [colAlpha_some h₁]; exact o₁ _ m₁), (by rw [colAlpha_some h₂]; exact o₂ _ m₂), (by rw [colAlpha_some h₃]; exact o₃ _ m₃)⟩
  | .call _ _, .call _ _, .call _ _, ⟨hf, hs⟩, ⟨of, os⟩ =>
    ⟨(colAlpha_some hf).trans of, pointwise_over hs os⟩
  | .ret _ _, .ret _ _, .ret _ _, ⟨hf, ⟨al, hal, hL⟩⟩, ⟨of, os⟩ =>
    ⟨(colAlpha_some hf).trans of, (by rw [colAlpha_some hal]; exact os _ hL)⟩
  | .lookup .., .lookup .., .update .., _, h => h.elim
  | .lookup .., .lookup .., .call .., _, h => h.elim
  | .lookup .., .lookup .., .ret .., _, h => h.elim
  | .update .., .update .., .lookup .., _, h => h.elim
  | .update .., .update .., .call .., _, h => h.elim
  | .update .., .update .., .ret .., _, h => h.elim
  | .call .., .call .., .lookup .., _, h => h.elim
  | .call .., .call .., .update .., _, h => h.elim
  | .call .., .call .., .ret .., _, h => h.elim
  | .ret .., .ret .., .lookup .., _, h => h.elim
  | .ret .., .ret .., .update .., _, h => h.elim
  | .ret .., .ret .., .call .., _, h => h.elim

theorem facts_over {d : V} {α : AlphaFn} {σ : Obs} {φ : AConf} {φf : FFacts V}
    (h : FactsAlpha α σ φ) (ho : FFacts.Over col φf φ) : FFactsAlpha (colAlpha col d α) σ φf := by
  obtain ⟨hval, hdep, hac, hsk⟩ := h
  obtain ⟨odep, oac, osk, ohv, osv⟩ := ho
  refine ⟨fun l₁ l₂ hd => ?_, fun l hl => ?_, fun l hl => ?_, fun l v hv => ?_,
    fun l₁ l₂ v h₁ h₂ => ?_⟩
  · obtain ⟨a₁, a₂, h₁, h₂, hd'⟩ := hdep l₁ l₂ hd
    rw [colAlpha_some h₁, colAlpha_some h₂]; exact odep _ _ hd'
  · obtain ⟨al, hal, h'⟩ := hac l hl
    rw [colAlpha_some hal]; exact oac _ h'
  · obtain ⟨al, hal, h'⟩ := hsk l hl
    rw [colAlpha_some hal]; exact osk _ h'
  · obtain ⟨al, hal, h'⟩ := hval l v hv
    rw [colAlpha_some hal]; exact ohv _ _ h'
  · obtain ⟨a₁, ha₁, m₁⟩ := hval l₁ v h₁
    obtain ⟨a₂, ha₂, m₂⟩ := hval l₂ v h₂
    rw [colAlpha_some ha₁, colAlpha_some ha₂]; exact osv _ _ _ m₁ m₂

theorem Pointwise.trans {α β γ : Type} {R₁ : α → β → Prop} {R₂ : β → γ → Prop}
    {R₃ : α → γ → Prop} (h : ∀ a b c, R₁ a b → R₂ b c → R₃ a c) :
    ∀ {as : List α} {bs : List β} {cs : List γ}, Pointwise R₁ as bs → Pointwise R₂ bs cs →
      Pointwise R₃ as cs
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h₁, t₁⟩, ⟨h₂, t₂⟩ => ⟨h _ _ _ h₁ h₂, Pointwise.trans h t₁ t₂⟩

/-- **Coverage moves to a finite form**: a finite trace system with a
    complete walk, with containing labels, for each complete walk of `S`, and
    finite facts containing `φ`. -/
theorem Covers.of_finite [DecidableEq V] {S : TSys AAct} {P : FinTSys (FAct V)} {d : V} {φ : AConf}
    {φf : FFacts V} {R : Exec → Prop}
    (hw : ∀ T s, S.Walk S.init T s → S.final s →
      ∃ Tf s', P.toTSys.Walk P.init Tf s' ∧ P.final s' = true ∧ Pointwise (FAct.Over col) T Tf)
    (hφ : FFacts.Over col φf φ) (h : Covers S autAbs φ R) : Covers P.toTSys listAbs φf R := by
  intro e he
  obtain ⟨T, s, α, hwalk, hs, hpw, hf⟩ := h e he
  obtain ⟨Tf, s', hw', hs', ho⟩ := hw T s hwalk hs
  exact ⟨Tf, s', colAlpha col d α, hw', hs',
    Pointwise.trans (R₁ := Act.Alpha α) (R₂ := FAct.Over col) (R₃ := FActAlpha (colAlpha col d α)) (fun _ _ _ h₁ h₂ => act_over h₁ h₂) hpw ho,
    facts_over hf hφ⟩

end over

/-! ## Finite forms of the labeled automaton, and the end-to-end theorem -/

section finForm

variable [Abstract] (Γ : Env) (s₀ : Stmt) (L : Labeling) (locs : List ALoc)

/-- A finite form of the automaton of `Γ, s₀` labeled by `L`, over the
    abstract locations `locs`: a finite trace system with a complete walk for
    each complete walk of the automaton, its labels containing the
    automaton's collapsed labels, and finite facts containing the collapsed
    final configurations. -/
structure FinForm where
  P     : FinTSys (FAct (FV locs))
  φ     : FFacts (FV locs)
  walks : ∀ T s, (autTSys Γ s₀ L).Walk (autTSys Γ s₀ L).init T s → (autTSys Γ s₀ L).final s →
    ∃ Tf s', P.toTSys.Walk P.init Tf s' ∧ P.final s' = true ∧
      Pointwise (FAct.Over (FV.cl locs)) T Tf
  facts : FFacts.Over (FV.cl locs) φ (topFacts Γ s₀ L)

variable {Γ s₀ L locs}

/-- Model checking a finite form: the non-relational domain over every value,
    the enumerating tracker over the `except` components' variables. -/
def FinForm.check (F : FinForm Γ s₀ L locs) (q : Query) (Δ : QProg) (hwf : QProg.WF (q :: Δ)) :
    List (F.P.St × QSt × (MVar → FV locs)) :=
  witnesses F.P (q.toQModel Δ).main
    (nonrel (FV.all locs) (q.toQModel Δ).main.labelVars listAbs F.φ listSep)
    (enumTracker listAbs F.φ (q.toQModel Δ) (FV.all locs) (q.toQModel Δ).compVars)
    (Query.toQModel_wf hwf).1 (nonrel_finite _ _ _ _ _) enumTracker_finite

/-- **Model checking the program is complete.** For any analysis result and
    any finite form of its labeled automaton, every run of the program from
    its initial configuration that matches a well-formed query yields a
    witness. -/
theorem FinForm.check_complete [Concrete] (cspec : ConcreteSpec) (xspec : CrossSpec)
    (hres : AnalysisResult Γ s₀ L) (F : FinForm Γ s₀ L locs) {Δ : QProg} {q : Query}
    (hwf : QProg.WF (q :: Δ)) {fs : List Fid} {r : Res}
    (hrun : BigStep Γ (Conf.init Γ fs s₀) s₀ r) {ls : List Loc}
    (hlen : ls.length = q.params.length) (hm : Exec.Matches (q :: Δ) (Exec.ofRes r) q.name ls) :
    F.check q Δ hwf ≠ [] :=
  model_check_complete_enum listAbs_sound listSep (FV.mem_all locs) hwf
    (Covers.of_finite (d := FV.none locs) F.walks F.facts (aut_covers Γ s₀ L cspec xspec hres))
    ⟨fs, r, hrun, rfl⟩ hlen hm

end finForm

/-! ## A finite form always exists

The coarsest finite form: one state, a self-loop for every location-list
action with full lists (calls at the arities `ns` of the program's
functions), and facts that hold of everything.  That it is a finite form of
*any* labeled automaton only needs every call label's arity to be some
function's parameter count (`AGraph.call_arity`). -/

section univ

variable [Abstract]

/-- A call label of an edge passes as many arguments as some function of `Γ`
    has parameters. -/
theorem AEdge.call_arity {Γ : Env} {cs : CallString} {entry : AState} {pending : AConf → AConf}
    {s : Stmt} {a b : AState} {C : Labeling → AConf} {ℓ : Labeling → Option AAct}
    (h : AEdge Γ cs entry pending s a b C ℓ) (L : Labeling) {lf : ALoc} {Ls : List ALocSet}
    (hℓ : ℓ L = some (.call lf Ls)) :
    ∃ f params body, Γ f = some (params, body) ∧ Ls.length = params.length := by
  induction h with
  | seqLeft _ ih => exact ih hℓ
  | seqRight _ _ ih => exact ih hℓ
  | ifThenBody _ ih => exact ih hℓ
  | ifElseBBody _ ih => exact ih hℓ
  | whileBody _ ih => exact ih hℓ
  | @callEntry entry pending x κ e es f params body hf harity =>
    simp only at hℓ
    split at hℓ
    · simp only [Option.some.injEq, AAct.call.injEq] at hℓ
      exact ⟨f, params, body, hf, by rw [← hℓ.2, aevalEs_length, harity]⟩
    · cases hℓ
  | callRet => simp only at hℓ; split at hℓ <;> simp at hℓ
  | callImplicitRet => simp only at hℓ; split at hℓ <;> simp at hℓ
  | _ => simp [AConf.actLookupS, AConf.actLookupD, AConf.actUpdateS, AConf.actUpdateD] at hℓ

theorem AGraph.call_arity {Γ : Env} {s₀ : Stmt} {a b : AState} {C : Labeling → AConf}
    {ℓ : Labeling → Option AAct} (h : AGraph Γ s₀ a b C ℓ) (L : Labeling) {lf : ALoc}
    {Ls : List ALocSet} (hℓ : ℓ L = some (.call lf Ls)) :
    ∃ f params body, Γ f = some (params, body) ∧ Ls.length = params.length := by
  cases h with
  | top he => exact he.call_arity L hℓ
  | body _ _ _ _ he => exact he.call_arity L hℓ

variable (locs : List ALoc) (ns : List Nat)

/-- Every location-list action with full lists, calls at the arities `ns`. -/
def univActs : List (FAct (FV locs)) :=
  [.lookup (FV.all locs) (FV.all locs) (FV.all locs),
   .update (FV.all locs) (FV.all locs) (FV.all locs)] ++
  (FV.all locs).flatMap fun f =>
    ns.map (fun n => .call f (List.replicate n (FV.all locs))) ++ [.ret f (FV.all locs)]

/-- One state, final, with a self-loop on every action of `univActs`. -/
def univTSys : FinTSys (FAct (FV locs)) where
  St     := Unit
  deq    := inferInstance
  init   := ()
  final _ := true
  succ _ := (univActs locs ns).map fun F => (some F, ())
  finite := ⟨[()], List.mem_singleton_self _, fun _ _ _ _ => List.mem_singleton.2 rfl⟩

/-- Facts holding of everything. -/
def univFacts : FFacts (FV locs) :=
  ⟨fun _ _ => true, fun _ => true, fun _ => true, fun _ _ => true, fun _ _ => true⟩

/-- The full action standing for an automaton action. -/
def univAct : AAct → FAct (FV locs)
  | .lookup .. => .lookup (FV.all locs) (FV.all locs) (FV.all locs)
  | .update .. => .update (FV.all locs) (FV.all locs) (FV.all locs)
  | .call lf Ls => .call (FV.cl locs lf) (List.replicate Ls.length (FV.all locs))
  | .ret lf _ => .ret (FV.cl locs lf) (FV.all locs)
  | .epsilon => .lookup (FV.all locs) (FV.all locs) (FV.all locs)

omit [Abstract] in
theorem setOver_all (L : ALocSet) : SetOver (FV.cl locs) L (FV.all locs) :=
  fun _ _ => FV.mem_all locs _

omit [Abstract] in
theorem pointwise_replicate : ∀ Ls : List ALocSet,
    Pointwise (SetOver (FV.cl locs)) Ls (List.replicate Ls.length (FV.all locs))
  | [] => trivial
  | L :: Ls => ⟨setOver_all locs L, pointwise_replicate Ls⟩

variable {Γ : Env} {s₀ : Stmt} {L : Labeling} {locs ns}

/-- Every walk of the automaton is a walk of `univTSys`, with containing
    labels. -/
theorem univ_walk (hns : ∀ f params body, Γ f = some (params, body) → params.length ∈ ns)
    {a b : (autTSys Γ s₀ L).St} {T : List AAct} (h : (autTSys Γ s₀ L).Walk a T b) :
    (univTSys locs ns).toTSys.Walk () (T.map (univAct locs)) () ∧
      Pointwise (FAct.Over (FV.cl locs)) T (T.map (univAct locs)) := by
  induction h with
  | nil => exact ⟨.nil, trivial⟩
  | silent _ _ ih => exact ih
  | @vis _ _ _ A T he _ ih =>
    obtain ⟨C, ℓ, act, hg, hℓ, hvis⟩ := he
    have hact : act = A := by
      cases act <;> simp [AAct.visible] at hvis <;> exact hvis
    subst hact
    have hmem : univAct locs act ∈ univActs locs ns := by
      cases act with
      | lookup => exact List.mem_cons_self ..
      | update => exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      | call lf Ls =>
        obtain ⟨f, params, body, hf, hlen⟩ := hg.call_arity L hℓ
        refine List.mem_append_right _ (List.mem_flatMap.2 ⟨FV.cl locs lf, FV.mem_all .., ?_⟩)
        exact List.mem_append_left _ (List.mem_map.2 ⟨Ls.length, hlen ▸ hns f params body hf, rfl⟩)
      | ret lf L' =>
        exact List.mem_append_right _ (List.mem_flatMap.2 ⟨FV.cl locs lf, FV.mem_all ..,
          List.mem_append_right _ (List.mem_singleton_self _)⟩)
      | epsilon => simp [AAct.visible] at hvis
    have hover : FAct.Over (FV.cl locs) act (univAct locs act) := by
      cases act with
      | lookup L₁ L₂ L₃ => exact ⟨setOver_all locs _, setOver_all locs _, setOver_all locs _⟩
      | update L₁ L₂ L₃ => exact ⟨setOver_all locs _, setOver_all locs _, setOver_all locs _⟩
      | call lf Ls => exact ⟨rfl, pointwise_replicate locs Ls⟩
      | ret lf L' => exact ⟨rfl, setOver_all locs _⟩
      | epsilon => simp [AAct.visible] at hvis
    exact ⟨.vis (List.mem_map.2 ⟨_, hmem, rfl⟩) ih.1, hover, ih.2⟩

variable (Γ s₀ L locs ns)

/-- **The coarsest finite form**, of any labeled automaton, given the arities
    `ns` of the program's functions. -/
def FinForm.univ (hns : ∀ f params body, Γ f = some (params, body) → params.length ∈ ns) :
    FinForm Γ s₀ L locs where
  P     := univTSys locs ns
  φ     := univFacts locs
  walks T _ hw _ := ⟨T.map (univAct locs), (), (univ_walk hns hw).1, rfl, (univ_walk hns hw).2⟩
  facts := ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

variable {Γ s₀ L locs ns}

/-- **Model checking the program is complete**, with no assumption on a
    finite form: on the coarsest one, every run of the program matching a
    well-formed query yields a witness. -/
theorem check_complete_univ [Concrete] (cspec : ConcreteSpec) (xspec : CrossSpec)
    (hres : AnalysisResult Γ s₀ L)
    (hns : ∀ f params body, Γ f = some (params, body) → params.length ∈ ns)
    {Δ : QProg} {q : Query} (hwf : QProg.WF (q :: Δ)) {fs : List Fid} {r : Res}
    (hrun : BigStep Γ (Conf.init Γ fs s₀) s₀ r) {ls : List Loc}
    (hlen : ls.length = q.params.length) (hm : Exec.Matches (q :: Δ) (Exec.ofRes r) q.name ls) :
    (FinForm.univ (Γ := Γ) (s₀ := s₀) (L := L) (locs := locs) (ns := ns) hns).check q Δ hwf ≠ [] :=
  FinForm.check_complete cspec xspec hres _ hwf hrun hlen hm

end univ

/-! ## Computed

The algorithm runs on the finite types: on the coarsest finite form over the
locations `[1, 2]` with unary calls, `Q(f) { ∃x: Call(f, [x]) }` finds
witnesses, among them `f = 1`. -/

section computed

private def qCall : Query :=
  { name := "Q", params := ["f"], body := { locals := ["x"], pattern := .act (.call "f" ["x"]) } }

private theorem qCall_wf : QProg.WF [qCall] :=
  ⟨⟨⟨by decide, by decide⟩, by simp [Query.CallsOK, QBody.calls, qCall, Pat.calls]⟩, rfl, trivial⟩

/-- The abstract locations `1` and `2` (`ALoc` has no numerals). -/
private def locs12 : List ALoc := [(1 : Nat), (2 : Nat)]

private def univCheck : List (Unit × QSt × (MVar → FV locs12)) :=
  witnesses (univTSys locs12 [1]) (qCall.toQModel []).main
    (nonrel (FV.all locs12) (qCall.toQModel []).main.labelVars listAbs (univFacts locs12) listSep)
    (enumTracker listAbs (univFacts locs12) (qCall.toQModel []) (FV.all locs12)
      (qCall.toQModel []).compVars)
    (Query.toQModel_wf qCall_wf).1 (nonrel_finite _ _ _ _ _) enumTracker_finite

#guard univCheck.any fun w => (w.2.2 (.src "f")).1 == some ((1 : Nat) : ALoc)

end computed

end CoreJS
