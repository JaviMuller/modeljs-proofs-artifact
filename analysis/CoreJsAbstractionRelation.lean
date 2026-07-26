/-
  # Core JavaScript — Abstraction Relation and Auxiliary Lemmas

  Formalisation of Appendix B.2 of
  "Model Checking Security Properties of Node.js Packages", up to but
  excluding the main theorem:

  * Def. B8   — the abstraction relation `∼α`
  * Lemma B9  — Expression Evaluation Lemma
  * Lemma B10 — α-Extension Lemma
  * Lemma B11 — Store Update Lemma
  * Lemma B12 — Correctness of the Least Upper Bound
                (already proved in `CoreJsAbstract.lean`; see the note below)
  * Lemma B13 — α-Monotonicity of Abstract Domains
  * Lemma B14 — the "Skip Extension Lemma", whose statement is missing from
                the paper; see REMARK 6 for what the main proof needs.

  Theorem B15 is deliberately left out.

  Deviations from the paper are tagged `REMARK n` and collected at the end.
-/

import CoreJsAbstractSemantics

namespace CoreJS

open Concrete Abstract

/-! ## Abstraction functions

`α : Loc ⇀ L̂oc`.  REMARK 1: Def. B8 declares `α` *total*, but §5.2 writes
`α : Loc ⇀ L̂oc` and the proof of Theorem B15 relies on partiality throughout —
it extends `α` at freshly allocated locations (`α' = α[l ↦ l̂]`) and appeals to
`α' ≥ α`, both of which are vacuous for total functions. -/

/-- Abstraction functions `α : Loc ⇀ L̂oc`. -/
def AbsFun := Loc → Option ALoc

/-- `α' ≥ α`: `α'` extends `α`. -/
def AbsFun.Le (α α' : AbsFun) : Prop := ∀ l «l̂», α l = some «l̂» → α' l = some «l̂»

/-- `α[l ↦ l̂]`. -/
def AbsFun.upd (α : AbsFun) (l : Loc) («l̂» : ALoc) : AbsFun :=
  fun l' => if l' = l then some «l̂» else α l'

/-- `α(l) = l̂`, in the partial reading. -/
def AbsFun.MapsTo (α : AbsFun) (l : Loc) («l̂» : ALoc) : Prop := α l = some «l̂»
/-- `α(l) ∈ L`: the atom out of which every clause of Def. B8 is built.
    Being an existential, it carries the requirement that `α` be defined at
    `l` (REMARK 2). -/
def AbsFun.In (α : AbsFun) (l : Loc) (L : ALocSet) : Prop :=
  ∃ «l̂», α l = some «l̂» ∧ L «l̂»

theorem AbsFun.le_refl (α : AbsFun) : α.Le α := fun _ _ h => h

theorem AbsFun.le_trans {α α' α'' : AbsFun} (h₁ : α.Le α') (h₂ : α'.Le α'') :
    α.Le α'' := fun l l̂ h => h₂ l l̂ (h₁ l l̂ h)

theorem AbsFun.In.mono {α α' : AbsFun} {l : Loc} {L : ALocSet}
    (h : α.In l L) (hle : α.Le α') : α'.In l L := by
  obtain ⟨l̂, h₁, h₂⟩ := h
  exact ⟨l̂, hle l l̂ h₁, h₂⟩

theorem AbsFun.In.mono_subset {α : AbsFun} {l : Loc} {L M : ALocSet}
    (h : α.In l L) (hsub : L ⊆ M) : α.In l M := by
  obtain ⟨l̂, h₁, h₂⟩ := h
  exact ⟨l̂, h₁, hsub l̂ h₂⟩

/-- The invariant that literal locations are abstracted by their abstract
    counterparts.  Implicitly assumed by the proof of Lemma B9 (REMARK 6). -/
def AbsFun.RespectsLits [Concrete] [Abstract] (α : AbsFun) : Prop :=
  ∀ v l̂, α (litLoc v) = some l̂ → l̂ = litLocA v

/-- The extension performed in case 1 of the proof of Lemma B9 preserves the
    invariant, provided literal locations are pairwise distinct
    (`ConcreteSpec.litLoc_inj`). -/
theorem AbsFun.RespectsLits.upd_lit [Concrete] [Abstract] {α : AbsFun}
    (hinj : ∀ v w : Val, litLoc v = litLoc w → v = w)
    (h : α.RespectsLits) (v : Val) :
    (α.upd (litLoc v) (litLocA v)).RespectsLits := by
  intro w l̂ hw
  by_cases hc : litLoc w = litLoc v
  · have hvw : w = v := hinj w v hc
    subst hvw
    simp [AbsFun.upd] at hw
    exact hw.symm
  · simp [AbsFun.upd, hc] at hw
    exact h w l̂ hw

/-! ## The abstraction relation (Definition B8)

Every clause below requires `α` to be defined at the concrete locations it
mentions, which is what makes the relation meaningful for a partial `α`
(REMARK 2). -/

/-- Def. B8.1.a: `∀ (l, p) ∈ dom(h.obj). α(h.obj(l, p)) ∈ ĥ.obj(α(l), p)`. -/
def AHeap.RelObj (α : AbsFun) (h : Heap) (ĥ : AHeap) : Prop :=
  ∀ l p l₂, h.obj l p = some l₂ →
    ∃ l̂ l̂₂, α l = some l̂ ∧ α l₂ = some l̂₂ ∧ ĥ.obj l̂ p l̂₂

/-- Def. B8.1.b: `∀ l ∈ dom(h.val). h.val(l) ∈ ĥ.val(α(l))`. -/
def AHeap.RelVal (α : AbsFun) (h : Heap) (ĥ : AHeap) : Prop :=
  ∀ l v, h.val l = some v → ∃ l̂, α l = some l̂ ∧ (ĥ.val l̂).Mem v

/-- Def. B8.1: `h ∼α ĥ`. -/
def AHeap.Rel (α : AbsFun) (h : Heap) (ĥ : AHeap) : Prop :=
  AHeap.RelObj α h ĥ ∧ AHeap.RelVal α h ĥ

/-- Def. B8.2: `ρ ∼α ρ̂`. -/
def ASto.Rel (α : AbsFun) (ρ : Sto) (ρ̂ : ASto) : Prop :=
  ∀ x l, ρ x = some l → α.In l (ρ̂ x)

/-- Def. B8.3 (with B8.3.a–c): `δ ∼α δ̂`. -/
def AReg.Rel (α : AbsFun) (δ : Reg) (δ̂ : AReg) : Prop :=
  (∀ l₁ l₂, δ.dep l₁ l₂ → ∃ l̂₁, α l₁ = some l̂₁ ∧ α.In l₂ (δ̂.dep l̂₁)) ∧
  (∀ l, δ.ac l → α.In l δ̂.ac) ∧
  (∀ l, δ.sk l → α.In l δ̂.sk)

/-- Def. B8.4 (with B8.4.a–b): `o ∼α ô`. -/
def AOut.Rel (α : AbsFun) : Out → AOut → Prop
  | .cont,  .cont  => True
  | .ret l, .ret L => α.In l L
  | _,      _      => False

/-- Componentwise relation of argument lists, used by Def. B8.5.c. -/
def ALocs.Rel (α : AbsFun) : List Loc → List ALocSet → Prop
  | [],      []      => True
  | l :: ls, L :: Ls => α.In l L ∧ ALocs.Rel α ls Ls
  | _,       _       => False

/-- Def. B8.5 (with B8.5.a–d): `a ∼α â`.  See REMARK 3 on the typos in
    B8.5.c/d. -/
def AAct.Rel (α : AbsFun) : Act → AAct → Prop
  | .lookup l₁ l₂ l₃, .lookup L₁ L₂ L₃ =>
      α.In l₁ L₁ ∧ α.In l₂ L₂ ∧ α.In l₃ L₃
  | .update l₁ l₂ l₃, .update L₁ L₂ L₃ =>
      α.In l₁ L₁ ∧ α.In l₂ L₂ ∧ α.In l₃ L₃
  | .call lf ls,      .call l̂f Ls     => α lf = some l̂f ∧ ALocs.Rel α ls Ls
  | .ret lf l,        .ret l̂f L       => α lf = some l̂f ∧ α.In l L
  | _,                _               => False

/-- Def. B8.6 (with B8.6.a–e): `t ∼α t̂`.

    Given inductively rather than by recursion, since the clauses for `|` and
    `*` are not structural in either argument.  The `act` clause is *not* in
    B8.6 but is indispensable — see REMARK 4. -/
inductive ATrc.Rel (α : AbsFun) : Trc → ATrc → Prop where
  /-- B8.6.a -/
  | emp : ATrc.Rel α .emp .emp
  /-- Missing from B8.6 (REMARK 4). -/
  | act {a â} : AAct.Rel α a â → ATrc.Rel α (.act a) (.act â)
  /-- B8.6.b -/
  | seq {t₁ t₂ u₁ u₂} : ATrc.Rel α t₁ u₁ → ATrc.Rel α t₂ u₂ →
      ATrc.Rel α (.seq t₁ t₂) (.seq u₁ u₂)
  /-- B8.6.c, left disjunct -/
  | altL {t u₁ u₂} : ATrc.Rel α t u₁ → ATrc.Rel α t (.alt u₁ u₂)
  /-- B8.6.c, right disjunct -/
  | altR {t u₁ u₂} : ATrc.Rel α t u₂ → ATrc.Rel α t (.alt u₁ u₂)
  /-- B8.6.d -/
  | starNil {u} : ATrc.Rel α .emp (.star u)
  /-- B8.6.e -/
  | starCons {t t' u} : ATrc.Rel α t u → ATrc.Rel α t' (.star u) →
      ATrc.Rel α (.seq t t') (.star u)

/-- `h, ρ, δ ∼α ĥ, ρ̂, δ̂`. -/
structure ConfRel (α : AbsFun) (c : Conf) (ĉ : AConf) : Prop where
  heap : AHeap.Rel α c.heap ĉ.heap
  sto  : ASto.Rel α c.sto ĉ.sto
  reg  : AReg.Rel α c.reg ĉ.reg

/-- `h', ρ', δ', t, o ∼α ĥ', ρ̂', δ̂', t̂, ô`. -/
structure ResRel (α : AbsFun) (r : Res) (r̂ : ARes) : Prop where
  heap : AHeap.Rel α r.heap r̂.heap
  sto  : ASto.Rel α r.sto r̂.sto
  reg  : AReg.Rel α r.reg r̂.reg
  trc  : ATrc.Rel α r.trc r̂.trc
  out  : AOut.Rel α r.out r̂.out

/-! ## Lemma B9 — Expression Evaluation Lemma

`ρ ∼α ρ̂ ⟹ ∃ α' ≥ α. α'(⟦e⟧ρ) ∈ ⟦e⟧ρ̂`.

Strengthened in two ways that the paper's statement leaves implicit: the
concrete evaluation is partial, so `⟦e⟧ρ = l` is a hypothesis; and the
invariant `RespectsLits` is both assumed and re-established, without which the
`α' = α[l_v ↦ l̂_v]` of case 1 need not extend `α` (REMARK 6). -/

theorem exprEval [Concrete] [Abstract] {α : AbsFun} {ρ : Sto} {ρ̂ : ASto}
    {e : Expr} {l : Loc}
    (hinj : ∀ v w : Val, litLoc v = litLoc w → v = w)
    (hlit : α.RespectsLits) (hρ : ASto.Rel α ρ ρ̂) (he : evalE ρ e = some l) :
    ∃ α', α.Le α' ∧ α'.RespectsLits ∧ α'.In l (aevalE ρ̂ e) := by
  cases e with
  | val v =>
      simp [evalE] at he
      subst he
      refine ⟨α.upd (litLoc v) (litLocA v), ?_, hlit.upd_lit hinj v, ?_⟩
      · intro l₀ l̂₀ h₀
        by_cases hc : l₀ = litLoc v
        · subst hc
          have hv : l̂₀ = litLocA v := hlit v l̂₀ h₀
          subst hv
          simp [AbsFun.upd]
        · simp [AbsFun.upd, hc, h₀]
      · exact ⟨litLocA v, by simp [AbsFun.upd], rfl⟩
  | var x =>
      refine ⟨α, α.le_refl, hlit, ?_⟩
      have hx : ρ x = some l := by simpa [evalE] using he
      exact hρ x l hx

/-! ## Lemma B10 — α-Extension Lemma

Every clause of Def. B8 is monotone in `α`. -/

theorem AHeap.Rel.mono {α α' : AbsFun} {h : Heap} {ĥ : AHeap}
    (hr : AHeap.Rel α h ĥ) (hle : α.Le α') : AHeap.Rel α' h ĥ := by
  obtain ⟨hobj, hval⟩ := hr
  refine ⟨?_, ?_⟩
  · intro l p l₂ hp
    obtain ⟨l̂, l̂₂, h₁, h₂, h₃⟩ := hobj l p l₂ hp
    exact ⟨l̂, l̂₂, hle l l̂ h₁, hle l₂ l̂₂ h₂, h₃⟩
  · intro l v hv
    obtain ⟨l̂, h₁, h₂⟩ := hval l v hv
    exact ⟨l̂, hle l l̂ h₁, h₂⟩

theorem ASto.Rel.mono {α α' : AbsFun} {ρ : Sto} {ρ̂ : ASto}
    (hr : ASto.Rel α ρ ρ̂) (hle : α.Le α') : ASto.Rel α' ρ ρ̂ :=
  fun x l hx => (hr x l hx).mono hle

theorem AReg.Rel.mono {α α' : AbsFun} {δ : Reg} {δ̂ : AReg}
    (hr : AReg.Rel α δ δ̂) (hle : α.Le α') : AReg.Rel α' δ δ̂ := by
  obtain ⟨hdep, hac, hsk⟩ := hr
  refine ⟨?_, ?_, ?_⟩
  · intro l₁ l₂ hd
    obtain ⟨l̂₁, h₁, h₂⟩ := hdep l₁ l₂ hd
    exact ⟨l̂₁, hle l₁ l̂₁ h₁, h₂.mono hle⟩
  · intro l hl; exact (hac l hl).mono hle
  · intro l hl; exact (hsk l hl).mono hle

theorem AOut.Rel.mono {α α' : AbsFun} (hle : α.Le α') :
    ∀ (o : Out) (ô : AOut), AOut.Rel α o ô → AOut.Rel α' o ô
  | .cont,  .cont,  _ => trivial
  | .ret _, .ret _, h => h.mono hle
  | _,      _,      h => False.elim h

theorem ALocs.Rel.mono {α α' : AbsFun} (hle : α.Le α') :
    ∀ (ls : List Loc) (Ls : List ALocSet), ALocs.Rel α ls Ls →
      ALocs.Rel α' ls Ls
  | [],      [],      _ => trivial
  | _ :: ls, _ :: Ls, h => by
      obtain ⟨h₁, h₂⟩ := h
      exact ⟨h₁.mono hle, ALocs.Rel.mono hle ls Ls h₂⟩
  | _,       _,       h => False.elim h

theorem AAct.Rel.mono {α α' : AbsFun} (hle : α.Le α') :
    ∀ (a : Act) (â : AAct), AAct.Rel α a â → AAct.Rel α' a â
  | .lookup _ _ _, .lookup _ _ _, h => by
      obtain ⟨h₁, h₂, h₃⟩ := h
      exact ⟨h₁.mono hle, h₂.mono hle, h₃.mono hle⟩
  | .update _ _ _, .update _ _ _, h => by
      obtain ⟨h₁, h₂, h₃⟩ := h
      exact ⟨h₁.mono hle, h₂.mono hle, h₃.mono hle⟩
  | .call lf ls,   .call l̂f Ls,   h => by
      obtain ⟨h₁, h₂⟩ := h
      exact ⟨hle lf l̂f h₁, ALocs.Rel.mono hle ls Ls h₂⟩
  | .ret lf _,     .ret l̂f _,     h => by
      obtain ⟨h₁, h₂⟩ := h
      exact ⟨hle lf l̂f h₁, h₂.mono hle⟩
  | _,             _,             h => False.elim h

theorem ATrc.Rel.mono {α α' : AbsFun} {t : Trc} {u : ATrc}
    (hr : ATrc.Rel α t u) (hle : α.Le α') : ATrc.Rel α' t u := by
  induction hr with
  | emp => exact .emp
  | act ha => exact .act (AAct.Rel.mono hle _ _ ha)
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | altL _ ih => exact .altL ih
  | altR _ ih => exact .altR ih
  | starNil => exact .starNil
  | starCons _ _ ih₁ ih₂ => exact .starCons ih₁ ih₂

/-- Lemma B10 on configurations. -/
theorem ConfRel.mono {α α' : AbsFun} {c : Conf} {ĉ : AConf}
    (hr : ConfRel α c ĉ) (hle : α.Le α') : ConfRel α' c ĉ :=
  ⟨hr.heap.mono hle, hr.sto.mono hle, hr.reg.mono hle⟩

/-- Lemma B10 on results. -/
theorem ResRel.mono {α α' : AbsFun} {r : Res} {r̂ : ARes}
    (hr : ResRel α r r̂) (hle : α.Le α') : ResRel α' r r̂ :=
  ⟨hr.heap.mono hle, hr.sto.mono hle, hr.reg.mono hle,
   hr.trc.mono hle, AOut.Rel.mono hle _ _ hr.out⟩

/-! ## Lemma B11 — Store Update Lemma

`ρ ∼α ρ̂ ∧ α(l) ∈ L ⟹ ρ[x ↦ l] ∼α ρ̂[x ↦ L]`. -/

theorem ASto.Rel.upd {α : AbsFun} {ρ : Sto} {ρ̂ : ASto} {x : Var} {l : Loc}
    {L : ALocSet} (hr : ASto.Rel α ρ ρ̂) (hl : α.In l L) :
    ASto.Rel α (ρ.upd x l) (ρ̂.upd x L) := by
  intro y l₀ hy
  by_cases hc : y = x
  · subst hc
    simp [Sto.upd] at hy
    subst hy
    simpa [ASto.upd] using hl
  · simp [Sto.upd, hc] at hy
    simpa [ASto.upd, hc] using hr y l₀ hy

/-! ## Lemma B12 — Correctness of the Least Upper Bound

Proved in `CoreJsAbstract.lean` for every domain whose join is total:
`ALocSet.subset_union_left/right`, `ALocSet.union_subset`,
`VSet.le_join_left/right`, `VSet.join_le`, `ASto.le_join_left/right`,
`ASto.join_le`, `AHeap.le_join_left/right`, `AHeap.join_le`,
`AReg.le_join_left/right`, `AReg.join_le`.  The outcome and action joins of
Defs. B5.4/B5.5 are partial; see REMARK 2 of that file. -/

/-! ## Lemma B13 — α-Monotonicity of Abstract Domains

`x ∼α ŷ₁ ∧ ŷ₁ ⊑ ŷ₂ ⟹ x ∼α ŷ₂`.

Theorem B15 applies this only to heaps, stores, registers and outcomes (the
[If True] and [If False] cases, where the branch results are joined); traces
are handled directly by clause B8.6.c.  The analogous statements for actions
and traces do hold, and are proved the same way. -/

theorem VSet.Mem.mono_le {V W : VSet} {v : Val} (h : V.Mem v) (hle : V.Le W) :
    W.Mem v := hle v h

theorem AHeap.Rel.mono_le {α : AbsFun} {h : Heap} {ĥ₁ ĥ₂ : AHeap}
    (hr : AHeap.Rel α h ĥ₁) (hle : AHeap.Le ĥ₁ ĥ₂) : AHeap.Rel α h ĥ₂ := by
  obtain ⟨hobj, hval⟩ := hr
  obtain ⟨kobj, kval⟩ := hle
  refine ⟨?_, ?_⟩
  · intro l p l₂ hp
    obtain ⟨l̂, l̂₂, h₁, h₂, h₃⟩ := hobj l p l₂ hp
    exact ⟨l̂, l̂₂, h₁, h₂, kobj l̂ p l̂₂ h₃⟩
  · intro l v hv
    obtain ⟨l̂, h₁, h₂⟩ := hval l v hv
    exact ⟨l̂, h₁, kval l̂ v h₂⟩

theorem ASto.Rel.mono_le {α : AbsFun} {ρ : Sto} {ρ̂₁ ρ̂₂ : ASto}
    (hr : ASto.Rel α ρ ρ̂₁) (hle : ASto.Le ρ̂₁ ρ̂₂) : ASto.Rel α ρ ρ̂₂ :=
  fun x l hx => (hr x l hx).mono_subset (hle x)

theorem AReg.Rel.mono_le {α : AbsFun} {δ : Reg} {δ̂₁ δ̂₂ : AReg}
    (hr : AReg.Rel α δ δ̂₁) (hle : AReg.Le δ̂₁ δ̂₂) : AReg.Rel α δ δ̂₂ := by
  obtain ⟨hdep, hac, hsk⟩ := hr
  obtain ⟨kdep, kac, ksk⟩ := hle
  refine ⟨?_, ?_, ?_⟩
  · intro l₁ l₂ hd
    obtain ⟨l̂₁, h₁, h₂⟩ := hdep l₁ l₂ hd
    exact ⟨l̂₁, h₁, h₂.mono_subset (kdep l̂₁)⟩
  · intro l hl; exact (hac l hl).mono_subset kac
  · intro l hl; exact (hsk l hl).mono_subset ksk

theorem AOut.Rel.mono_le {α : AbsFun} :
    ∀ (o : Out) (ô₁ ô₂ : AOut), AOut.Rel α o ô₁ → AOut.Le ô₁ ô₂ →
      AOut.Rel α o ô₂
  | .cont,  .cont,  .cont,  _,  _   => trivial
  | .ret _, .ret _, .ret _, hr, hle => hr.mono_subset hle
  | _,      _,      _,      hr, hle => by
      first
        | exact False.elim hr
        | exact False.elim hle

/-! ## Lemma B14 — the missing lemma

The paper states "Lemma B14 (Skip Extension Lemma)" and gives no statement.
The property the [While] case of Theorem B15 actually appeals to — its step
I6.1, `t̂* ≡ (t̂; t̂*) | ε̂` — is the closure of `∼α` under one unfolding of the
Kleene star, which we prove below.  Note that a *syntactic* equivalence `≡` on
abstract traces is never defined in the paper; with this lemma it is not
needed. -/

theorem ATrc.Rel.star_unfold {α : AbsFun} {t : Trc} {u : ATrc} :
    ATrc.Rel α t (.star u) ↔ ATrc.Rel α t (.alt (.seq u (.star u)) .emp) := by
  constructor
  · intro h
    cases h with
    | starNil => exact .altR .emp
    | starCons h₁ h₂ => exact .altL (.seq h₁ h₂)
  · intro h
    cases h with
    | altL h' =>
        cases h' with
        | seq h₁ h₂ => exact .starCons h₁ h₂
    | altR h' =>
        cases h' with
        | emp => exact .starNil

/-! ## Optional: a language-based reading of B8.6

REMARK 5 argues that relating a concrete trace to an abstract trace
*structurally* is fragile.  The robust alternative is to relate the flattened
action word of the concrete trace to some word of the language denoted by the
abstract trace.  We record the definitions; `ATrc.Rel α t u → ATrc.RelL α t u`
is the direction worth checking if this route is taken. -/

/-- The action word of a concrete trace. -/
def Trc.word : Trc → List Act
  | .emp       => []
  | .act a     => [a]
  | .seq t₁ t₂ => t₁.word ++ t₂.word

/-- `as ∈ L(t̂)`: the finite words denoted by an abstract trace. -/
inductive ATrc.Word : ATrc → List AAct → Prop where
  | emp : ATrc.Word .emp []
  | act {a} : ATrc.Word (.act a) [a]
  | seq {t u as bs} : ATrc.Word t as → ATrc.Word u bs →
      ATrc.Word (.seq t u) (as ++ bs)
  | altL {t u as} : ATrc.Word t as → ATrc.Word (.alt t u) as
  | altR {t u as} : ATrc.Word u as → ATrc.Word (.alt t u) as
  | starNil {t} : ATrc.Word (.star t) []
  | starCons {t as bs} : ATrc.Word t as → ATrc.Word (.star t) bs →
      ATrc.Word (.star t) (as ++ bs)

/-- Pointwise lifting of `∼α` to words. -/
def AActs.Rel (α : AbsFun) : List Act → List AAct → Prop
  | [],      []      => True
  | a :: as, b :: bs => AAct.Rel α a b ∧ AActs.Rel α as bs
  | _,       _       => False

/-- Suggested replacement for Def. B8.6. -/
def ATrc.RelL (α : AbsFun) (t : Trc) (u : ATrc) : Prop :=
  ∃ bs, u.Word bs ∧ AActs.Rel α t.word bs

/-!
## REMARKS

**1. `α` is partial.** Def. B8 introduces `α : Loc → L̂oc`, but §5.2 writes
`α : Loc ⇀ L̂oc` and the whole proof of Theorem B15 depends on partiality: it
extends `α` at every freshly allocated location and threads an `α' ≥ α`
through the induction. For total `α`, `α' ≥ α` can only mean `α' = α`, and the
[Binary Operation] and [Object Initialization] cases break. The declaration in
Def. B8 should read `⇀`, and `≥` should be defined (as `AbsFun.Le` above).

**2. The clauses of B8 must require `α` to be defined.** `α(l) ∈ L` is
formalised as `∃ l̂. α(l) = l̂ ∧ l̂ ∈ L`, so relatedness *asserts* that `α`
covers every location reachable in the concrete state. This is the reading the
proof uses (it establishes `α'(l) ∈ L` immediately after extending `α'` at
`l`), and it is what makes the relation strong enough to be preserved by
property lookup, where the looked-up location must itself be abstracted.

**3. Two typos in B8.5.** In B8.5.c the second premise reads
`α(l̂ᵢ) ∈ Lᵢ|³ᵢ₌₁` — `α` is applied to an *abstract* location, and the bound
should be `n`, not 3. In B8.5.d the premise reads `α(lᵢ) ∈ Lᵢ|ⁿᵢ₌₁`, but
`Ret(l_f, l) ∼α Ret(l̂_f, L)` has a single returned location: it should be
`α(l) ∈ L`.

**4. B8.6 has no clause for a single action.** The concrete and abstract trace
grammars both admit an atomic action (`t ::= ε | a | t₁; t₂` and
`t̂ ::= ε̂ | â | ...`), and every rule that emits a trace emits exactly such an
atom, yet B8.6 defines `∼α` only for `ε`, `;`, `|` and `*`. Read literally, no
concrete trace containing an action is related to any abstract trace, and the
trace component of Theorem B15 is unprovable for, say, [Static Property
Update]. The clause `a ∼α â ⟺ a ∼α â` (lifting B8.5) is missing.

**5. B8.6 is very syntax-sensitive.** As defined, `∼α` requires the two traces
to have the same regular skeleton: `ε` is related to `ε̂` and to `t̂*`, but not
to `ε̂; ε̂`; and an atom is not related to `ε̂; â`. This happens to work because
the two semantics build traces in lockstep, but it makes the relation brittle
under any reassociation — and it is why step I6.1 of the [While] case needs an
equivalence `≡` on abstract traces that is nowhere defined. Defining `∼α` on
the *language* of `t̂` instead (`ATrc.RelL` above) removes the dependence on
the syntactic shape, at the cost of one extra lemma per trace-emitting rule.

**6. Lemma B9 needs an invariant on literal locations.** Case 1 of its proof
takes `α' = α[l_v ↦ l̂_v]` and asserts `α' ≥ α`. That fails when `α` is already
defined at `l_v` with a different image, which nothing rules out. The fix is
to carry `α(l_v) = l̂_v` (whenever defined) as an invariant of the induction —
`AbsFun.RespectsLits` above — which is preserved by the extension provided
`v ↦ l_v` is injective (`ConcreteSpec.litLoc_inj`). Note also that the concrete
`⟦e⟧ρ` is partial while the abstract `⟦e⟧ρ̂` is total, so the lemma needs
`⟦e⟧ρ = l` as a hypothesis rather than as notation.

**7. Lemma B14 has no statement in the paper** — only a name. `star_unfold`
above is what the [While] case needs; if something else was intended, the case
still requires a lemma of this kind, since the abstract [While] rule produces
`t̂*` while the concrete [While] rule unfolds into a conditional.
-/

end CoreJS
