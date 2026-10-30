/-
  # Core JavaScript — Model checking: `except` trackers

  The abstract semantics (`QModel.ASat`) checks every `except` component of
  the final state reached against the *labels of the whole walk*.  The search
  cannot keep the walk: progress skips a search state reached a second time,
  and two walks reaching the same state can have different labels (a loop
  containing `Call(f, …)` against `except Call(f, _)`: skipping the loop and
  going round it once reach the same state, and only the first is a
  witness).  Keeping the labels instead makes the search space infinite.

  So each walk is summarised, incrementally, by a *tracker* (`Tracker`): a
  value updated at every visible label (`step`), from which the check at
  acceptance can be read off (`excl τ k ξ`: component `k` must accept the
  labels read so far, under `ξ`).  `Tracker.Spec` asks exactly that: after
  reading `T`, `excl` is `QModel.AExcl … T`; it only reads the variables
  `reads`; finitely many trackers are reachable.  Two walks with equal
  trackers are then interchangeable for every continuation, which is what
  progress needs.

  `enumTracker` is an instance: the set of entries `(k, q, vs)` such that
  component `k` reaches `q` by a must-run over the labels read so far, under
  the assignment `vs` of the components' variables `xs`, enumerated over a
  finite list of abstract values.  It is exact (`enumTracker_spec`), and
  exponential in the number of variables of the `except` components —
  typically few.  Each tracker is a filter of one finite universe, hence
  finitely many.

  Plain Lean 4 — no Mathlib required.
-/

import ModelChecking.CoreJsMcDomain

namespace CoreJS

variable {A V Φ : Type}

/-! ## The interface -/

/-- A summary of the labels read so far, sufficient to check the `except`
    components. -/
structure Tracker (A V : Type) where
  T     : Type
  deq   : DecidableEq T
  init  : T
  step  : T → A → T
  /-- Component `k` must accept the labels read so far, under `ξ`. -/
  excl  : T → Nat → (MVar → V) → Bool
  /-- The variables `excl` reads. -/
  reads : List MVar

/-- The tracker after reading `T`. -/
def Tracker.run (tr : Tracker A V) (T : List A) : tr.T := T.foldl tr.step tr.init

theorem Tracker.run_snoc (tr : Tracker A V) (T : List A) (a : A) :
    tr.run (T ++ [a]) = tr.step (tr.run T) a := by
  simp [Tracker.run]

/-- The specification of a tracker for the model `M`. -/
structure Tracker.Spec (tr : Tracker A V) (𝔄 : Abs A V Φ) (φ : Φ) (M : QModel) : Prop where
  excl   : ∀ T k ξ, tr.excl (tr.run T) k ξ = true ↔ M.AExcl 𝔄 φ T k ξ
  reads  : ∀ τ k (ξ₁ ξ₂ : MVar → V), (∀ x ∈ tr.reads, ξ₁ x = ξ₂ x) →
    tr.excl τ k ξ₁ = tr.excl τ k ξ₂
  /-- Finitely many trackers are reachable from `init`. -/
  finite : ∃ UT : List tr.T, tr.init ∈ UT ∧ ∀ τ ∈ UT, ∀ B, tr.step τ B ∈ UT

/-! ## Runs over label lists: composition -/

section lrun

variable {α : Type} {es : List QEdge} {F : List (QAct MVar) → α → Prop}

theorem LRun.append {s s' s'' : QSt} {w₁ w₂ : List α} (h₁ : LRun es F s w₁ s')
    (h₂ : LRun es F s' w₂ s'') : LRun es F s (w₁ ++ w₂) s'' := by
  induction h₁ with
  | nil => exact h₂
  | eps he _ ih => exact .eps he (ih h₂)
  | act he hf _ ih => exact .act he hf (ih h₂)

theorem LRun.split {s s'' : QSt} {w₁ w₂ : List α} (h : LRun es F s (w₁ ++ w₂) s'') :
    ∃ s', LRun es F s w₁ s' ∧ LRun es F s' w₂ s'' := by
  generalize hw : w₁ ++ w₂ = w at h
  induction h generalizing w₁ with
  | nil =>
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hw
    exact ⟨_, .nil, .nil⟩
  | eps he _ ih =>
    obtain ⟨s', h₁, h₂⟩ := ih hw
    exact ⟨s', .eps he h₁, h₂⟩
  | @act s s₁ s₂ as a w he hf hrest ih =>
    cases w₁ with
    | nil =>
      simp only [List.nil_append] at hw; subst hw
      exact ⟨s, .nil, .act he hf hrest⟩
    | cons b w₁ =>
      simp only [List.cons_append, List.cons.injEq] at hw
      obtain ⟨rfl, hw⟩ := hw
      obtain ⟨s', h₁, h₂⟩ := ih hw
      exact ⟨s', .act he hf h₁, h₂⟩

/-- Reading one label: `ε`-edges, one action edge, `ε`-edges. -/
theorem LRun.single_iff {s s' : QSt} {a : α} :
    LRun es F s [a] s' ↔ ∃ s₁ as s₂, LRun es F s [] s₁ ∧ (s₁, .act as, s₂) ∈ es ∧ F as a ∧
      LRun es F s₂ [] s' := by
  constructor
  · intro h
    generalize hw : [a] = w at h
    induction h with
    | nil => cases hw
    | eps he _ ih =>
      obtain ⟨s₁, as, s₂, h₁, he', hf, h₂⟩ := ih hw
      exact ⟨s₁, as, s₂, .eps he h₁, he', hf, h₂⟩
    | act he hf hrest =>
      simp only [List.cons.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨_, _, _, .nil, he, hf, hrest⟩
  · rintro ⟨s₁, as, s₂, h₁, he, hf, h₂⟩
    simpa using h₁.append (.act he hf h₂ : LRun es F s₁ [a] s')

/-- Runs of a closed component stay within its states. -/
theorem LRun.mem_states {c : QComp} (hc : c.Closed) {s s' : QSt} {w : List α}
    (h : LRun c.edges F s w s') (hs : s ∈ c.states) : s' ∈ c.states := by
  induction h with
  | nil => exact hs
  | eps he _ ih => exact ih (hc.edges _ _ _ he).2
  | act he _ _ ih => exact ih (hc.edges _ _ _ he).2

end lrun

/-! ## `ε`-closure -/

/-- The `ε`-successors of `q`. -/
def epsSucc (es : List QEdge) (q : QSt) : List QSt :=
  ((epsEdges es).filter fun e => decide (e.1 = q)).map Prod.snd

theorem epsSucc_closed (es : List QEdge) (q : QSt) :
    ∃ U : List QSt, q ∈ U ∧ SuccClosed (epsSucc es) U :=
  ⟨q :: (epsEdges es).map Prod.snd, List.mem_cons_self .., fun _ _ y hy => by
    simp only [epsSucc, List.mem_map, List.mem_filter] at hy
    obtain ⟨e, ⟨he, _⟩, rfl⟩ := hy
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem he)⟩

/-- The states reachable from `q` by `ε`-edges. -/
def epsClose (es : List QEdge) (q : QSt) : List QSt :=
  explore (epsSucc es) q (epsSucc_closed es q)

theorem mem_epsClose {α : Type} {es : List QEdge} {F : List (QAct MVar) → α → Prop}
    {q q' : QSt} : q' ∈ epsClose es q ↔ LRun es F q [] q' := by
  rw [epsClose, mem_explore]
  constructor
  · intro h
    induction h with
    | refl => exact .nil
    | step _ hz ih =>
      simp only [epsSucc, List.mem_map, List.mem_filter, decide_eq_true_eq] at hz
      obtain ⟨⟨a, b⟩, ⟨he, rfl⟩, rfl⟩ := hz
      simpa using ih.append (.eps (mem_epsEdges.1 he) .nil)
  · intro h
    generalize hw : ([] : List α) = w at h
    induction h with
    | nil => exact .refl
    | @eps s s' _ _ he _ ih =>
      exact Reach.head (List.mem_map.2 ⟨(s, s'), List.mem_filter.2
        ⟨mem_epsEdges.2 he, by simp⟩, rfl⟩) (ih hw)
    | act => cases hw

/-! ## Assignments from value lists -/

/-- `ys` bound to `vs` (the first occurrence of a variable wins), `ξ`
    elsewhere. -/
def bindV : List MVar → List V → (MVar → V) → MVar → V
  | y :: ys, v :: vs, ξ, x => if x = y then v else bindV ys vs ξ x
  | _,       _,       ξ, x => ξ x

theorem bindV_map (g ξ : MVar → V) {x : MVar} :
    ∀ {ys : List MVar}, x ∈ ys → bindV ys (ys.map g) ξ x = g x
  | [], h => by simp at h
  | y :: ys, h => by
      simp only [List.map_cons, bindV]
      by_cases hxy : x = y
      · subst hxy; simp
      · rw [if_neg hxy]; exact bindV_map g ξ ((List.mem_cons.1 h).resolve_left hxy)

/-- `bindV` reads `ξ` only at the variable looked up. -/
theorem bindV_congr {x : MVar} {ξ ξ' : MVar → V} (h : ξ x = ξ' x) :
    ∀ (ys : List MVar) (vs : List V), bindV ys vs ξ x = bindV ys vs ξ' x
  | [], _ => h
  | _ :: _, [] => h
  | y :: ys, v :: vs => by
      simp only [bindV]; split
      · rfl
      · exact bindV_congr h ys vs

theorem bindV_indep {x : MVar} : ∀ {ys : List MVar} {vs : List V}, x ∈ ys →
    ys.length = vs.length → ∀ ξ ξ' : MVar → V, bindV ys vs ξ x = bindV ys vs ξ' x
  | [], _, h, _, _, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | y :: ys, v :: vs, h, hl, ξ, ξ' => by
      simp only [bindV]
      by_cases hxy : x = y
      · simp [hxy]
      · rw [if_neg hxy, if_neg hxy]
        exact bindV_indep ((List.mem_cons.1 h).resolve_left hxy) (by simpa using hl) ξ ξ'

theorem bindV_mem_zip {x : MVar} : ∀ {ys : List MVar} {vs : List V}, x ∈ ys →
    ys.length = vs.length → ∀ ξ : MVar → V, (x, bindV ys vs ξ x) ∈ ys.zip vs
  | [], _, h, _, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | y :: ys, v :: vs, h, hl, ξ => by
      simp only [bindV, List.zip_cons_cons, List.mem_cons]
      by_cases hxy : x = y
      · subst hxy; simp
      · rw [if_neg hxy]
        exact Or.inr (bindV_mem_zip ((List.mem_cons.1 h).resolve_left hxy) (by simpa using hl) ξ)

theorem eq_of_mem_zip_map {g : MVar → V} {p : MVar × V} :
    ∀ {ys : List MVar}, p ∈ ys.zip (ys.map g) → p.2 = g p.1
  | [], h => by simp at h
  | y :: ys, h => by
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · rfl
      · exact eq_of_mem_zip_map h

theorem length_of_mem_tuples {β : Type} {B : List β} :
    ∀ {n : Nat} {d : List β}, d ∈ tuples B n → d.length = n
  | 0, d, h => by simp [tuples] at h; subst h; rfl
  | n + 1, d, h => by
      simp only [tuples, List.mem_flatMap, List.mem_map] at h
      obtain ⟨_, _, d', hd', rfl⟩ := h
      simp [length_of_mem_tuples hd']

/-- The variables occurring in the labels of a component. -/
def QComp.labelVars (c : QComp) : List MVar := c.edges.flatMap fun e => e.2.1.vars

theorem QComp.labelVars_good (c : QComp) :
    ∀ s as s', (s, .act as, s') ∈ c.edges → ∀ b ∈ as, ∀ x ∈ b.vars, x ∈ c.labelVars := by
  intro s as s' he b hb x hx
  simp only [QComp.labelVars, List.mem_flatMap]
  exact ⟨(s, .act as, s'), he, by simp only [MLbl.vars, List.mem_flatMap]; exact ⟨b, hb, hx⟩⟩

/-! ## The enumerating tracker -/

section enum

variable (𝔄 : Abs A V Φ) (φ : Φ) (M : QModel) (vals : List V) (xs : List MVar)

/-- All entries: a component, one of its states, values for `xs`. -/
def tUniv : List (Nat × QSt × List V) :=
  (List.range M.comps.length).flatMap fun k => match M.comps[k]? with
    | some c => c.states.flatMap fun q => (tuples vals xs.length).map fun vs => (k, q, vs)
    | none   => []

theorem mem_tUniv {k : Nat} {q : QSt} {vs : List V} :
    (k, q, vs) ∈ tUniv M vals xs ↔
      ∃ c, M.comps[k]? = some c ∧ q ∈ c.states ∧ vs ∈ tuples vals xs.length := by
  simp only [tUniv, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨k', hk', h⟩
    cases hc : M.comps[k']? with
    | none => rw [hc] at h; simp at h
    | some c =>
      rw [hc] at h
      simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq] at h
      obtain ⟨q', hq', vs', hvs', rfl, rfl, rfl⟩ := h
      exact ⟨c, hc, hq', hvs'⟩
  · rintro ⟨c, hc, hq, hvs⟩
    refine ⟨k, (List.getElem?_eq_some_iff.1 hc).1, ?_⟩
    rw [hc]
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨q, hq, vs, hvs, rfl⟩

variable [DecidableEq V] [Inhabited V]

/-- The assignment an entry stands for. -/
abbrev tAsg (vs : List V) : MVar → V := bindV xs vs fun _ => default

/-- `q₀` reaches `q` by a must-run reading `B`. -/
def oneStep (es : List QEdge) (ξ : MVar → V) (q₀ : QSt) (B : A) (q : QSt) : Bool :=
  (epsClose es q₀).any fun q₁ => (actEdges es).any fun e =>
    decide (e.1 = q₁) && e.2.1.all (fun b => 𝔄.mustA ξ b B) && decide (q ∈ epsClose es e.2.2)

omit [DecidableEq V] [Inhabited V] in
theorem oneStep_iff {es : List QEdge} {ξ : MVar → V} {q₀ q : QSt} {B : A} :
    oneStep 𝔄 es ξ q₀ B q = true ↔ LRun es (𝔄.MustFires ξ) q₀ [B] q := by
  rw [LRun.single_iff]
  simp only [oneStep, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨q₁, hq₁, ⟨s, as, s'⟩, he, ⟨rfl, hf⟩, hq⟩
    exact ⟨s, as, s', mem_epsClose.1 hq₁, mem_actEdges.1 he, hf, mem_epsClose.1 hq⟩
  · rintro ⟨q₁, as, q₂, h₁, he, hf, h₂⟩
    exact ⟨q₁, mem_epsClose.2 h₁, (q₁, as, q₂), mem_actEdges.2 he, ⟨rfl, hf⟩, mem_epsClose.2 h₂⟩

/-- `x` takes the entry's value inside `S`, `ξ`'s outside. -/
def mergeV (S : List MVar) (vs : List V) (ξ : MVar → V) : MVar → V :=
  fun x => if x ∈ S then bindV xs vs ξ x else ξ x

/-- The entry `e`, of component `k` (that is, `c`), makes `c` must-accept
    under `ξ`: a final state with no `except`s, the entry's values agreeing
    with `ξ` outside its scope, its invariants must-holding, the new values
    of the variables they read certainly denoting locations. -/
def ExclAt (c : QComp) (k : Nat) (ξ : MVar → V) (e : Nat × QSt × List V) : Prop :=
  e.1 = k ∧ e.2.1 ∈ c.finals ∧ c.exc e.2.1 = [] ∧
  (∀ p ∈ xs.zip e.2.2, p.1 ∈ c.scope e.2.1 ∨ p.2 = ξ p.1) ∧
  (∀ J ∈ c.inv e.2.1, 𝔄.inv φ (mergeV xs (c.scope e.2.1) e.2.2 ξ) false J = true) ∧
  ∀ x ∈ c.scope e.2.1, x ∈ (c.inv e.2.1).flatMap Inv.vars →
    𝔄.inhab φ (mergeV xs (c.scope e.2.1) e.2.2 ξ x) = true

instance (c : QComp) (k : Nat) (ξ : MVar → V) : DecidablePred (ExclAt 𝔄 φ xs c k ξ) :=
  fun e => by unfold ExclAt; infer_instance

/-- The entries reached from no label. -/
def enumInit : List (Nat × QSt × List V) :=
  (tUniv M vals xs).filter fun e => match M.comps[e.1]? with
    | some c => decide (e.2.1 ∈ epsClose c.edges c.start)
    | none   => false

/-- The entries reached by reading one more label `B`. -/
def enumStep (τ : List (Nat × QSt × List V)) (B : A) : List (Nat × QSt × List V) :=
  (tUniv M vals xs).filter fun e => match M.comps[e.1]? with
    | some c => τ.any fun e₀ => decide (e₀.1 = e.1) && decide (e₀.2.2 = e.2.2) &&
        oneStep 𝔄 c.edges (tAsg xs e.2.2) e₀.2.1 B e.2.1
    | none   => false

/-- Some entry makes component `k` must-accept under `ξ`. -/
def enumExcl (τ : List (Nat × QSt × List V)) (k : Nat) (ξ : MVar → V) : Bool :=
  match M.comps[k]? with
  | some c => decide (M.depth ≠ 0 ∧ ∃ e ∈ τ, ExclAt 𝔄 φ xs c k ξ e)
  | none   => false

/-- The enumerating tracker: entries `(k, q, vs)`, component `k` at `q` under
    `vs`. -/
def enumTracker : Tracker A V where
  T     := List (Nat × QSt × List V)
  deq   := inferInstance
  init  := enumInit M vals xs
  step  := enumStep 𝔄 M vals xs
  excl  := enumExcl 𝔄 φ M xs
  reads := xs

/-- `τ` holds exactly the entries reached by reading `T`. -/
def TRep (τ : List (Nat × QSt × List V)) (T : List A) : Prop :=
  ∀ e, e ∈ τ ↔ e ∈ tUniv M vals xs ∧ ∃ c, M.comps[e.1]? = some c ∧
    LRun c.edges (𝔄.MustFires (tAsg xs e.2.2)) c.start T e.2.1

variable {𝔄 φ M vals xs}

omit [DecidableEq V] in
theorem enumInit_rep : TRep 𝔄 M vals xs (enumInit M vals xs) [] := by
  rintro ⟨k, q, vs⟩
  rw [enumInit, List.mem_filter]
  cases hk : M.comps[k]? with
  | none => simp
  | some c =>
    simp only [decide_eq_true_eq, Option.some.injEq, exists_eq_left']
    rw [mem_epsClose]

theorem enumStep_rep (hc : ∀ c ∈ M.comps, c.Closed) {τ : List (Nat × QSt × List V)}
    {T : List A} (ih : TRep 𝔄 M vals xs τ T) (B : A) :
    TRep 𝔄 M vals xs (enumStep 𝔄 M vals xs τ B) (T ++ [B]) := by
  rintro ⟨k, q, vs⟩
  rw [enumStep, List.mem_filter]
  cases hk : M.comps[k]? with
  | none => simp
  | some c =>
    simp only [Option.some.injEq, exists_eq_left', List.any_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, oneStep_iff]
    constructor
    · rintro ⟨hu, ⟨k', q₀, vs'⟩, he, ⟨rfl, rfl⟩, h₂⟩
      obtain ⟨_, c', hc', h₁⟩ := (ih _).1 he
      rw [hk] at hc'; cases hc'
      exact ⟨hu, h₁.append h₂⟩
    · rintro ⟨hu, h⟩
      obtain ⟨q₀, h₁, h₂⟩ := h.split
      obtain ⟨c', hc', hq, hvs⟩ := (mem_tUniv M vals xs).1 hu
      rw [hk] at hc'; cases hc'
      have hcc := hc c (List.mem_of_getElem? hk)
      refine ⟨hu, (k, q₀, vs), (ih _).2 ⟨(mem_tUniv M vals xs).2
        ⟨c, hk, h₁.mem_states hcc hcc.start, hvs⟩, c, hk, h₁⟩, ⟨rfl, rfl⟩, h₂⟩

theorem enumTracker_rep (hc : ∀ c ∈ M.comps, c.Closed) (T : List A) :
    TRep 𝔄 M vals xs ((enumTracker 𝔄 φ M vals xs).run T) T := by
  have : ∀ (T T₀ : List A) τ, TRep 𝔄 M vals xs τ T₀ →
      TRep 𝔄 M vals xs (T.foldl (enumStep 𝔄 M vals xs) τ) (T₀ ++ T) := by
    intro T
    induction T with
    | nil => intro T₀ τ h; simpa using h
    | cons B T ih =>
      intro T₀ τ h
      have := ih (T₀ ++ [B]) _ (enumStep_rep hc h B)
      simpa using this
  exact this T [] _ enumInit_rep

/-- Finitely many trackers are reachable: each is a filter of `tUniv`. -/
theorem enumTracker_finite : ∃ UT : List (enumTracker 𝔄 φ M vals xs).T,
    (enumTracker 𝔄 φ M vals xs).init ∈ UT ∧
      ∀ τ ∈ UT, ∀ B, (enumTracker 𝔄 φ M vals xs).step τ B ∈ UT :=
  ⟨subs (tUniv M vals xs), mem_subs List.filter_sublist, fun _ _ _ => mem_subs List.filter_sublist⟩

/-- The variables of the `except` components' labels, and of the invariants of
    their final states. -/
def QModel.compVars (M : QModel) : List MVar :=
  M.comps.flatMap fun c => c.labelVars ++ c.finals.flatMap fun f => (c.inv f).flatMap Inv.vars

theorem QModel.compVars_labels {M : QModel} :
    ∀ c ∈ M.comps, ∀ s as s', (s, .act as, s') ∈ c.edges → ∀ b ∈ as, ∀ x ∈ b.vars,
      x ∈ M.compVars := by
  intro c hc s as s' he b hb x hx
  exact List.mem_flatMap.2 ⟨c, hc, List.mem_append_left _ (c.labelVars_good s as s' he b hb x hx)⟩

theorem QModel.compVars_inv {M : QModel} :
    ∀ c ∈ M.comps, ∀ f ∈ c.finals, ∀ J ∈ c.inv f, ∀ x ∈ J.vars, x ∈ M.compVars := by
  intro c hc f hf J hJ x hx
  exact List.mem_flatMap.2 ⟨c, hc, List.mem_append_right _
    (List.mem_flatMap.2 ⟨f, hf, List.mem_flatMap.2 ⟨J, hJ, hx⟩⟩)⟩

/-- **The enumerating tracker meets the specification**, when `vals` has every
    abstract value and `xs` every variable the components' labels and final
    invariants read. -/
theorem enumTracker_spec (h𝔄 : 𝔄.Sound) (hvals : ∀ v, v ∈ vals)
    (hc : ∀ c ∈ M.comps, c.Closed)
    (hxl : ∀ c ∈ M.comps, ∀ s as s', (s, .act as, s') ∈ c.edges → ∀ b ∈ as, ∀ x ∈ b.vars,
      x ∈ xs)
    (hxi : ∀ c ∈ M.comps, ∀ f ∈ c.finals, ∀ J ∈ c.inv f, ∀ x ∈ J.vars, x ∈ xs) :
    (enumTracker 𝔄 φ M vals xs).Spec 𝔄 φ M where
  excl T k ξ := by
    show enumExcl 𝔄 φ M xs ((enumTracker 𝔄 φ M vals xs).run T) k ξ = true ↔ _
    unfold enumExcl
    cases hk : M.comps[k]? with
    | none => simp [QModel.AExcl, hk]
    | some c =>
      have hcm := List.mem_of_getElem? hk
      have hrep := enumTracker_rep (𝔄 := 𝔄) (φ := φ) (vals := vals) (xs := xs) hc T
      simp only [decide_eq_true_eq, QModel.AExcl, hk, Option.some.injEq, exists_eq_left']
      refine and_congr_right fun _ => ?_
      constructor
      · rintro ⟨⟨k', f, vs⟩, he, rfl, hf, hexc, hagree, hinv, hinh⟩
        obtain ⟨hu, c', hc', hrun⟩ := (hrep _).1 he
        rw [hk] at hc'; cases hc'
        obtain ⟨_, _, _, hvs⟩ := (mem_tUniv M vals xs).1 hu
        have hlen := length_of_mem_tuples hvs
        refine ⟨f, hf, hexc, mergeV xs (c.scope f) vs ξ, fun v hv => by simp [mergeV, hv],
          hrun.mono_fires fun s as s' B he' hF b hb => ?_, hinv, hinh⟩
        rw [← hF b hb]
        refine h𝔄.mustA_congr _ _ b B fun x hx => ?_
        have hxs := hxl c hcm s as s' he' b hb x hx
        simp only [mergeV]
        split
        · exact bindV_indep hxs hlen.symm _ _
        · rename_i hs
          rcases hagree _ (bindV_mem_zip hxs hlen.symm fun _ => default) with h | h
          · exact absurd h hs
          · exact h.symm
      · rintro ⟨f, hf, hexc, ξ', hout, hrun, hinv, hinh⟩
        have hcc := hc c hcm
        have hm : ∀ x ∈ xs, tAsg xs (xs.map ξ') x = ξ' x := fun x hx => bindV_map _ _ hx
        have hmerge : ∀ x, x ∈ xs → mergeV xs (c.scope f) (xs.map ξ') ξ x = ξ' x := by
          intro x hx
          simp only [mergeV]
          split
          · exact bindV_map _ _ hx
          · rename_i hs; exact (hout x hs).symm
        refine ⟨(k, f, xs.map ξ'), (hrep _).2 ⟨(mem_tUniv M vals xs).2 ⟨c, hk, hcc.finals f hf,
            by simpa using mem_tuples (B := vals) (d := xs.map ξ') (by simp [hvals])⟩, c, hk,
            hrun.mono_fires fun s as s' B he' hF b hb => ?_⟩, rfl, hf, hexc, fun p hp => ?_,
            fun J hJ => ?_, fun x hs hx => ?_⟩
        · rw [← hF b hb]
          exact h𝔄.mustA_congr _ _ b B fun x hx => hm x (hxl c hcm s as s' he' b hb x hx)
        · by_cases hs : p.1 ∈ c.scope f
          · exact Or.inl hs
          · exact Or.inr ((eq_of_mem_zip_map hp).trans (hout _ hs))
        · rw [Abs.inv_congr h𝔄 φ false J (ξ' := ξ') fun x hx => hmerge x (hxi c hcm f hf J hJ x hx)]
          exact hinv J hJ
        · obtain ⟨J, hJ, hxJ⟩ := List.mem_flatMap.1 hx
          rw [hmerge x (hxi c hcm f hf J hJ x hxJ)]
          exact hinh x hs hx
  reads τ k ξ₁ ξ₂ hξ := by
    show enumExcl 𝔄 φ M xs τ k ξ₁ = enumExcl 𝔄 φ M xs τ k ξ₂
    unfold enumExcl
    cases hk : M.comps[k]? with
    | none => rfl
    | some c =>
      have hcm := List.mem_of_getElem? hk
      -- One direction, for any two assignments agreeing on `xs`.
      have dir : ∀ ξ₁ ξ₂ : MVar → V, (∀ x ∈ xs, ξ₁ x = ξ₂ x) → ∀ e,
          ExclAt 𝔄 φ xs c k ξ₁ e → ExclAt 𝔄 φ xs c k ξ₂ e := by
        rintro ξ₁ ξ₂ hξ ⟨k', f, vs⟩ ⟨rfl, hf, hexc, hagree, hinv, hinh⟩
        have hmerge : ∀ x ∈ xs, mergeV xs (c.scope f) vs ξ₁ x = mergeV xs (c.scope f) vs ξ₂ x := by
          intro x hx
          simp only [mergeV]
          split
          · exact bindV_congr (hξ x hx) _ _
          · exact hξ x hx
        refine ⟨rfl, hf, hexc, fun p hp => ?_, fun J hJ => ?_, fun x hs hx => ?_⟩
        · rcases hagree p hp with h | h
          · exact Or.inl h
          · exact Or.inr (h.trans (hξ _ (List.of_mem_zip hp).1))
        · rw [← Abs.inv_congr h𝔄 φ false J fun x hx => hmerge x (hxi c hcm f hf J hJ x hx)]
          exact hinv J hJ
        · obtain ⟨J, hJ, hxJ⟩ := List.mem_flatMap.1 hx
          rw [← hmerge x (hxi c hcm f hf J hJ x hxJ)]
          exact hinh x hs hx
      simp only [decide_eq_decide]
      exact and_congr_right fun _ =>
        ⟨fun ⟨e, he, h⟩ => ⟨e, he, dir ξ₁ ξ₂ hξ e h⟩,
         fun ⟨e, he, h⟩ => ⟨e, he, dir ξ₂ ξ₁ (fun x hx => (hξ x hx).symm) e h⟩⟩
  finite := enumTracker_finite

end enum

end CoreJS
