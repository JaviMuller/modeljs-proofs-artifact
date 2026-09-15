/-
  # Core JavaScript — Abstraction Relation

  Formalisation of Appendix B.2.1 of
  "Model Checking Security Properties of Node.js Packages":

  * Def. B8  — the abstraction relation `∼α`
  * Lemma B9  — expression evaluation
  * Lemma B10 — `α`-extension
  * Lemma B11 — store update
  * Lemma B13 — `α`-monotonicity of the abstract domains

  Deviations from the paper are tagged `REMARK` and collected at the end.
-/

import CoreJsSemantics
import CoreJsAbstractSemantics

namespace CoreJS

/-! ## Abstraction functions

REMARK A.  The paper writes `α : Loc → L̂oc` as a *total* function and relates
abstraction functions by `α' ≥ α`.  That order is not expressible for total
functions: there is no order on `L̂oc` itself, and `≥` is used throughout the
proof to mean "agrees wherever `α` was already committed, and may now be
defined on more locations" (see the proof of Lemma B9, which builds
`α' = α[l_v ↦ l̂_v]`).  We therefore model `α` as a *partial* map.  Every bare
`α(l)` of Def. B8 becomes `∃ l̂, α l = some l̂ ∧ …`. -/

/-- `α : Loc ⇀ L̂oc`. -/
abbrev AlphaFn := Loc → Option ALoc

/-- `α' ≥ α`: `α'` agrees with `α` wherever `α` is defined. -/
def AlphaFn.Extends (α' α : AlphaFn) : Prop :=
  ∀ l al, α l = some al → α' l = some al

@[inherit_doc] scoped infix:50 " ≥α " => AlphaFn.Extends

theorem AlphaFn.Extends.refl (α : AlphaFn) : α ≥α α := fun _ _ h => h

theorem AlphaFn.Extends.trans {α₁ α₂ α₃ : AlphaFn} (h₁ : α₂ ≥α α₁) (h₂ : α₃ ≥α α₂) :
    α₃ ≥α α₁ := fun l al h => h₂ l al (h₁ l al h)

/-- `α l ∈ L`: the abstract counterpart of `l` exists and lies in `L`. -/
def AlphaFn.MapsInto (α : AlphaFn) (l : Loc) (L : ALocSet) : Prop :=
  ∃ al, α l = some al ∧ L al

theorem AlphaFn.MapsInto.mono {α α' : AlphaFn} {l L} (he : α' ≥α α)
    (h : α.MapsInto l L) : α'.MapsInto l L := by
  obtain ⟨al, hal, hL⟩ := h
  exact ⟨al, he l al hal, hL⟩

theorem AlphaFn.MapsInto.subset {α : AlphaFn} {l L L'} (hs : L ⊆ L')
    (h : α.MapsInto l L) : α.MapsInto l L' := by
  obtain ⟨al, hal, hL⟩ := h
  exact ⟨al, hal, hs al hL⟩

/-! ### Literal locations

REMARK B.  Lemma B9 extends `α` at every *evaluation* of a literal, so that
`α'(l_v) = l̂_v`.  Since `l_v` and `l̂_v` are fixed by the parameters of the two
semantics and never change, it is equivalent — and considerably lighter — to
require this of `α` once, as an invariant preserved by every rule, rather than
re-establishing it at each use.  It also covers `undefined`, which the
[Function Call] rules read but which no *expression* ever evaluates, so the
paper's lazy extension would never fire for it. -/

/-- `α` maps every literal location to its abstract counterpart. -/
def AlphaFn.Lits [Concrete] [Abstract] (α : AlphaFn) : Prop :=
  ∀ v : Val, α (Concrete.litLoc v) = some (Abstract.litLocA v)

/-! ## The abstraction relation (Definition B8) -/

/-- Def. B8.1 (with B8.1.a and B8.1.b). -/
def Heap.Alpha (α : AlphaFn) (h : Heap) (ah : AHeap) : Prop :=
  (∀ l p l', h.obj l p = some l' →
      ∃ al al', α l = some al ∧ α l' = some al' ∧ ah.obj al p al') ∧
  (∀ l v, h.val l = some v → ∃ al, α l = some al ∧ (ah.val al).Mem v)

/-- Def. B8.2. -/
def Sto.Alpha (α : AlphaFn) (ρ : Sto) (aρ : ASto) : Prop :=
  ∀ x l, ρ x = some l → α.MapsInto l (aρ x)

/-- Def. B8.3 (with B8.3.a–c). -/
def Reg.Alpha (α : AlphaFn) (δ : Reg) (aδ : AReg) : Prop :=
  (∀ l₁ l₂, δ.dep l₁ l₂ →
      ∃ a₁ a₂, α l₁ = some a₁ ∧ α l₂ = some a₂ ∧ aδ.dep a₁ a₂) ∧
  (∀ l, δ.ac l → α.MapsInto l aδ.ac) ∧
  (∀ l, δ.sk l → α.MapsInto l aδ.sk)

/-- Def. B8.4 (with B8.4.a and B8.4.b).

    REMARK C.  A concrete `r⟨l⟩` is related to an abstract outcome of *either*
    kind, provided `α(l)` is among the collected return locations: an abstract
    `·`-outcome carrying a non-empty `locs` records exactly the situation where
    some analysed path returned and another fell through, and the concrete
    execution may have taken the returning one.  A concrete `·` against an
    abstract `r⟨L⟩` is genuinely unrelated — the analysis would be claiming
    every path returns while the concrete execution continued. -/
def Out.Alpha (α : AlphaFn) : Out → AOut → Prop
  | .cont,  ⟨.cont, _⟩ => True
  | .cont,  ⟨.ret,  _⟩ => False
  | .ret l, ⟨_,     L⟩ => α.MapsInto l L

/-- Componentwise relation of a concrete argument list to an abstract one. -/
def LocsAlpha (α : AlphaFn) : List Loc → List ALocSet → Prop
  | [],      []      => True
  | l :: ls, L :: Ls => α.MapsInto l L ∧ LocsAlpha α ls Ls
  | _,       _       => False

/-- Def. B8.5 (with B8.5.a–d). -/
def Act.Alpha (α : AlphaFn) : Act → AAct → Prop
  | .lookup l₁ l₂ l₃, .lookup L₁ L₂ L₃ =>
      α.MapsInto l₁ L₁ ∧ α.MapsInto l₂ L₂ ∧ α.MapsInto l₃ L₃
  | .update l₁ l₂ l₃, .update L₁ L₂ L₃ =>
      α.MapsInto l₁ L₁ ∧ α.MapsInto l₂ L₂ ∧ α.MapsInto l₃ L₃
  | .call lf ls,      .call alf Ls     => α lf = some alf ∧ LocsAlpha α ls Ls
  | .ret lf l,        .ret alf L       => α lf = some alf ∧ α.MapsInto l L
  | _,                _                => False

/-- Def. B8.6 (with B8.6.a–e), plus the clause for `μ`.

    Stated as an inductive relation rather than by recursion: the `μ` clause
    relates a concrete trace to `μX. t̂` by *unfolding*, which is not
    structurally decreasing in the abstract trace.  It is well founded all the
    same, because every unfolding that contributes anything consumes at least
    one action of the (finite) concrete trace. -/
inductive Trc.Alpha (α : AlphaFn) : Trc → ATrc → Prop where
  /-- B8.6.a -/
  | emp : Trc.Alpha α .emp .emp
  /-- A single action (Def. B8.5). -/
  | act {a b} : Act.Alpha α a b → Trc.Alpha α (.act a) (.act b)
  /-- B8.6.b -/
  | seq {t₁ t₂ u₁ u₂} :
      Trc.Alpha α t₁ u₁ → Trc.Alpha α t₂ u₂ →
      Trc.Alpha α (.seq t₁ t₂) (.seq u₁ u₂)
  /-- B8.6.c, left -/
  | altL {t u₁ u₂} : Trc.Alpha α t u₁ → Trc.Alpha α t (.alt u₁ u₂)
  /-- B8.6.c, right -/
  | altR {t u₁ u₂} : Trc.Alpha α t u₂ → Trc.Alpha α t (.alt u₁ u₂)
  /-- B8.6.d -/
  | starNil {u} : Trc.Alpha α .emp (.star u)
  /-- B8.6.e -/
  | starCons {t t' u} :
      Trc.Alpha α t u → Trc.Alpha α t' (.star u) →
      Trc.Alpha α (.seq t t') (.star u)
  /-- `μ`: unfold once. -/
  | mu {t u} : Trc.Alpha α t u.unfold → Trc.Alpha α t (.mu u)

/-! ## Lemma B10 (α-Extension)

Every clause of Def. B8 is positive in `α` — it only ever asserts that `α` *is*
defined somewhere and lands in a given set — so all of them are preserved by
extension.  The paper states this for all domains at once; we prove it
componentwise. -/

theorem Heap.Alpha.mono {α α' : AlphaFn} {h ah} (he : α' ≥α α)
    (k : Heap.Alpha α h ah) : Heap.Alpha α' h ah := by
  refine ⟨?_, ?_⟩
  · intro l p l' hl
    obtain ⟨al, al', h1, h2, h3⟩ := k.1 l p l' hl
    exact ⟨al, al', he l al h1, he l' al' h2, h3⟩
  · intro l v hl
    obtain ⟨al, h1, h2⟩ := k.2 l v hl
    exact ⟨al, he l al h1, h2⟩

theorem Sto.Alpha.mono {α α' : AlphaFn} {ρ aρ} (he : α' ≥α α)
    (k : Sto.Alpha α ρ aρ) : Sto.Alpha α' ρ aρ :=
  fun x l hl => (k x l hl).mono he

theorem Reg.Alpha.mono {α α' : AlphaFn} {δ aδ} (he : α' ≥α α)
    (k : Reg.Alpha α δ aδ) : Reg.Alpha α' δ aδ := by
  refine ⟨?_, ?_, ?_⟩
  · intro l₁ l₂ hl
    obtain ⟨a₁, a₂, h1, h2, h3⟩ := k.1 l₁ l₂ hl
    exact ⟨a₁, a₂, he l₁ a₁ h1, he l₂ a₂ h2, h3⟩
  · intro l hl
    exact (k.2.1 l hl).mono he
  · intro l hl
    exact (k.2.2 l hl).mono he

theorem Out.Alpha.mono {α α' : AlphaFn} {o ao} (he : α' ≥α α)
    (k : Out.Alpha α o ao) : Out.Alpha α' o ao := by
  cases o with
  | cont =>
      cases ao with
      | mk kind locs => cases kind with
        | cont => exact trivial
        | ret  => exact False.elim k
  | ret l =>
      cases ao with
      | mk kind locs => exact AlphaFn.MapsInto.mono he k

/-- A concrete `·` is only ever related to an abstract outcome that also says
    `·`; needed by `[Sequence]`, whose second half only runs when the first
    behaved this way. -/
theorem Out.Alpha.cont_kind {α : AlphaFn} {ao : AOut} (h : Out.Alpha α .cont ao) :
    ao.kind = .cont := by
  cases ao with
  | mk kind locs => cases kind with
    | cont => rfl
    | ret => exact h.elim

theorem LocsAlpha.mono {α α' : AlphaFn} (he : α' ≥α α) :
    ∀ {ls Ls}, LocsAlpha α ls Ls → LocsAlpha α' ls Ls
  | [],      [],      _ => trivial
  | _ :: ls, _ :: Ls, k => ⟨k.1.mono he, LocsAlpha.mono he (Ls := Ls) (ls := ls) k.2⟩

theorem Act.Alpha.mono {α α' : AlphaFn} (he : α' ≥α α) :
    ∀ {a b}, Act.Alpha α a b → Act.Alpha α' a b := by
  intro a b k
  cases a <;> cases b <;> simp_all [Act.Alpha] <;>
    first
      | exact ⟨k.1.mono he, k.2.mono he, k.2.mono he⟩
      | skip
  all_goals
    first
      | exact ⟨k.1.mono he, k.2.1.mono he, k.2.2.mono he⟩
      | exact ⟨he _ _ k.1, LocsAlpha.mono he k.2⟩
      | exact ⟨he _ _ k.1, k.2.mono he⟩

theorem Trc.Alpha.mono {α α' : AlphaFn} (he : α' ≥α α) :
    ∀ {t u}, Trc.Alpha α t u → Trc.Alpha α' t u := by
  intro t u k
  induction k with
  | emp => exact .emp
  | act h => exact .act (Act.Alpha.mono he h)
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | altL _ ih => exact .altL ih
  | altR _ ih => exact .altR ih
  | starNil => exact .starNil
  | starCons _ _ ih₁ ih₂ => exact .starCons ih₁ ih₂
  | mu _ ih => exact .mu ih

/-! ## Lemma B9 (Expression Evaluation)

REMARK B above makes this sharper than the paper's version: no extension of
`α` is needed, because `AlphaFn.Lits` already commits `α` on literal
locations. -/

theorem eval_alpha [Concrete] [Abstract] {α : AlphaFn} {ρ aρ e l}
    (hlit : α.Lits) (hρ : Sto.Alpha α ρ aρ) (he : evalE ρ e = some l) :
    α.MapsInto l (aevalE aρ e) := by
  cases e with
  | val v =>
      have : l = Concrete.litLoc v := by
        simpa [evalE] using he.symm
      subst this
      exact ⟨Abstract.litLocA v, hlit v, rfl⟩
  | var x =>
      exact hρ x l (by simpa [evalE] using he)

theorem evals_alpha [Concrete] [Abstract] {α : AlphaFn} {ρ aρ} (hlit : α.Lits)
    (hρ : Sto.Alpha α ρ aρ) :
    ∀ (es : List Expr) {ls}, evalEs ρ es = some ls → LocsAlpha α ls (aevalEs aρ es)
  | [],      ls, he => by
      simp only [evalEs, Option.some.injEq] at he
      subst he
      exact trivial
  | e :: es, ls, he => by
      rw [evalEs] at he
      cases hE : evalE ρ e with
      | none => rw [hE] at he; simp at he
      | some l =>
        cases hEs : evalEs ρ es with
        | none => rw [hE, hEs] at he; simp at he
        | some ls' =>
          rw [hE, hEs] at he
          have hx : l :: ls' = ls := by injection he
          subst hx
          exact ⟨eval_alpha hlit hρ hE, evals_alpha hlit hρ es hEs⟩

/-! ## Lemma B11 (Store Update) -/

theorem sto_upd_alpha {α : AlphaFn} {ρ aρ x l L} (hρ : Sto.Alpha α ρ aρ)
    (hl : α.MapsInto l L) : Sto.Alpha α (ρ.upd x l) (aρ.upd x L) := by
  intro y l' hy
  by_cases hxy : y = x
  · subst hxy
    have : l' = l := by simpa [Sto.upd] using hy.symm
    subst this
    simpa [ASto.upd] using hl
  · have hy' : ρ y = some l' := by simpa [Sto.upd, hxy] using hy
    have := hρ y l' hy'
    simpa [ASto.upd, hxy] using this

/-! ## Heap lookup soundness

Not a lemma the paper names separately, but needed by the `[Lookup]`/`[Update]`
cases of Theorem B15: `Heap.Alpha`'s own clauses only relate a *single*
concrete location to its abstract counterpart, whereas the abstract semantics
reads the heap through `objOf`/`valOf`/`objOfV`, the liftings to sets defined
in `CoreJsAbstractSemantics.lean`. These lift the relation accordingly. -/

theorem Heap.Alpha.objOf {α : AlphaFn} {h : Heap} {ah : AHeap} {l₁ l₂ : Loc}
    {L : ALocSet} {p : PropName}
    (k : Heap.Alpha α h ah) (hL : α.MapsInto l₁ L) (hobj : h.obj l₁ p = some l₂) :
    α.MapsInto l₂ (ah.objOf L p) := by
  obtain ⟨al, hal, hLal⟩ := hL
  obtain ⟨al', al'', hal', hal'', hobj'⟩ := k.1 l₁ p l₂ hobj
  rw [hal] at hal'
  cases hal'
  exact ⟨al'', hal'', al, hLal, hobj'⟩

theorem Heap.Alpha.valOf {α : AlphaFn} {h : Heap} {ah : AHeap} {l : Loc} {v : Val}
    {L : ALocSet}
    (k : Heap.Alpha α h ah) (hL : α.MapsInto l L) (hval : h.val l = some v) :
    (ah.valOf L).Mem v := by
  obtain ⟨al, hal, hLal⟩ := hL
  obtain ⟨al', hal', hmem⟩ := k.2 l v hval
  rw [hal] at hal'
  cases hal'
  exact ⟨al, hLal, hmem⟩

theorem Heap.Alpha.objOfV {α : AlphaFn} {h : Heap} {ah : AHeap} {l₁ l₂ : Loc}
    {L : ALocSet} {V : VSet} {p : PropName}
    (k : Heap.Alpha α h ah) (hL : α.MapsInto l₁ L) (hV : V.Mem (.str p))
    (hobj : h.obj l₁ p = some l₂) :
    α.MapsInto l₂ (ah.objOfV L V) := by
  obtain ⟨al, hal, hLal⟩ := hL
  obtain ⟨al', al'', hal', hal'', hobj'⟩ := k.1 l₁ p l₂ hobj
  rw [hal] at hal'
  cases hal'
  exact ⟨al'', hal'', al, p, hLal, hV, hobj'⟩

/-! ## Lemma B13 (α-Monotonicity of the abstract domains)

If a concrete object is related to an abstract one, it is related to every
larger abstract one.  This is what lets `[If-Then-Else]` and `[While]` join
branch results without losing the relation, and what discharges the
`[Weakening]` rule in the soundness proof. -/

theorem Heap.Alpha.le {α : AlphaFn} {h ah ah'} (k : Heap.Alpha α h ah)
    (hle : ah ⊑ ah') : Heap.Alpha α h ah' := by
  refine ⟨?_, ?_⟩
  · intro l p l' hl
    obtain ⟨al, al', h1, h2, h3⟩ := k.1 l p l' hl
    exact ⟨al, al', h1, h2, hle.1 al p al' h3⟩
  · intro l v hl
    obtain ⟨al, h1, h2⟩ := k.2 l v hl
    exact ⟨al, h1, hle.2 al v h2⟩

theorem Sto.Alpha.le {α : AlphaFn} {ρ aρ aρ'} (k : Sto.Alpha α ρ aρ)
    (hle : aρ ⊑ aρ') : Sto.Alpha α ρ aρ' :=
  fun x l hl => (k x l hl).subset (hle x)

theorem Reg.Alpha.le {α : AlphaFn} {δ aδ aδ'} (k : Reg.Alpha α δ aδ)
    (hle : aδ ⊑ aδ') : Reg.Alpha α δ aδ' := by
  refine ⟨?_, ?_, ?_⟩
  · intro l₁ l₂ hl
    obtain ⟨a₁, a₂, h1, h2, h3⟩ := k.1 l₁ l₂ hl
    exact ⟨a₁, a₂, h1, h2, hle.1 a₁ a₂ h3⟩
  · intro l hl
    exact (k.2.1 l hl).subset hle.2.1
  · intro l hl
    exact (k.2.2 l hl).subset hle.2.2

theorem Out.Alpha.le {α : AlphaFn} {o ao ao'} (k : Out.Alpha α o ao)
    (hle : ao ⊑ ao') : Out.Alpha α o ao' := by
  cases o with
  | cont =>
      cases ao with
      | mk kind locs =>
        cases ao' with
        | mk kind' locs' =>
          cases kind with
          | ret => exact False.elim k
          | cont =>
              cases kind' with
              | cont => exact trivial
              | ret  => exact False.elim hle
  | ret l =>
      cases ao with
      | mk kind locs =>
        cases ao' with
        | mk kind' locs' =>
          cases kind <;> cases kind' <;>
            first
              | exact k.subset hle
              | exact False.elim hle

theorem LocsAlpha.le {α : AlphaFn} :
    ∀ {ls : List Loc} {Ls Ms : List ALocSet},
      LocsAlpha α ls Ls → ALocSets.Le Ls Ms → LocsAlpha α ls Ms
  | [],      [],      [],      _, _ => trivial
  | [],      [],      _ :: _,  _, h => h.elim
  | [],      _ :: _,  _,       k, _ => k.elim
  | _ :: _,  [],      _,       k, _ => k.elim
  | _ :: _,  _ :: _,  [],      _, h => h.elim
  | _ :: ls, _ :: Ls, _ :: Ms, k, h => ⟨k.1.subset h.1, LocsAlpha.le k.2 h.2⟩

theorem Act.Alpha.le {α : AlphaFn} :
    ∀ {a b b'}, Act.Alpha α a b → b ⊑ b' → Act.Alpha α a b' := by
  intro a b b' k hle
  cases a <;> cases b <;> cases b' <;>
    simp only [Act.Alpha, LE.le, AAct.Le] at k hle ⊢ <;>
    first
      | exact k.elim
      | exact hle.elim
      | exact ⟨k.1.subset hle.1, k.2.1.subset hle.2.1, k.2.2.subset hle.2.2⟩
      | exact ⟨hle.1 ▸ k.1, LocsAlpha.le k.2 hle.2⟩
      | exact ⟨hle.1 ▸ k.1, k.2.subset hle.2⟩

/-! ### Traces

The `μ` case needs substitution to respect the order: relating a concrete
trace to `μX. t̂` proceeds by unfolding, so a larger `μ`-body must unfold to a
larger trace. -/

theorem ATrc.subst_le {v w : ATrc} (hv : v.Le w) :
    ∀ {t u : ATrc}, t.Le u → (t.subst v).Le (u.subst w) := by
  intro t
  induction t with
  | emp =>
      intro u h; cases u <;> first | exact trivial | exact h.elim
  | act a =>
      intro u h; cases u <;> first | exact h | exact h.elim
  | seq t₁ t₂ ih₁ ih₂ =>
      intro u h; cases u <;> first | exact ⟨ih₁ h.1, ih₂ h.2⟩ | exact h.elim
  | alt t₁ t₂ ih₁ ih₂ =>
      intro u h; cases u <;> first | exact ⟨ih₁ h.1, ih₂ h.2⟩ | exact h.elim
  | star t₁ ih =>
      intro u h; cases u <;> first | exact ih h | exact h.elim
  | tvar =>
      intro u h; cases u <;> first | exact hv | exact h.elim
  | mu t₁ ih =>
      intro u h; cases u <;> first | exact h | exact h.elim

/-- `μ`-unfolding is monotone. -/
theorem ATrc.unfold_le {t u : ATrc} (h : t.Le u) : t.unfold.Le u.unfold :=
  ATrc.subst_le (v := .mu t) (w := .mu u) h h

/-- Lemma B13, trace component. -/
theorem Trc.Alpha.le {α : AlphaFn} {t : Trc} {u : ATrc} (k : Trc.Alpha α t u) :
    ∀ {u' : ATrc}, u.Le u' → Trc.Alpha α t u' := by
  induction k with
  | emp =>
      intro u' h; cases u' <;> first | exact .emp | exact h.elim
  | act ha =>
      intro u' h; cases u' <;> first | exact .act (Act.Alpha.le ha h) | exact h.elim
  | seq _ _ ih₁ ih₂ =>
      intro u' h; cases u' <;> first | exact .seq (ih₁ h.1) (ih₂ h.2) | exact h.elim
  | altL _ ih =>
      intro u' h; cases u' <;> first | exact .altL (ih h.1) | exact h.elim
  | altR _ ih =>
      intro u' h; cases u' <;> first | exact .altR (ih h.2) | exact h.elim
  | starNil =>
      intro u' h; cases u' <;> first | exact .starNil | exact h.elim
  | starCons _ _ ih₁ ih₂ =>
      intro u' h; cases u' <;> first | exact .starCons (ih₁ h) (ih₂ h) | exact h.elim
  | mu _ ih =>
      intro u' h; cases u' <;> first | exact .mu (ih (ATrc.unfold_le h)) | exact h.elim

/-- The `n`-ary form of B8.6.c: relatedness to any element of a choice list
    lifts to the whole choice.  This is what the multi-target [Function Call]
    case of the soundness proof uses — the concrete execution picks one
    candidate callee, and that candidate's branch is one element of the list. -/
theorem Trc.Alpha.choice {α : AlphaFn} {t : Trc} {u : ATrc} (k : Trc.Alpha α t u) :
    ∀ {us : List ATrc}, u ∈ us → Trc.Alpha α t (ATrc.choice us)
  | [],             hmem => absurd hmem (by simp)
  | [_],            hmem => by
      rw [List.mem_singleton] at hmem
      subst hmem
      simpa [ATrc.choice] using k
  | _ :: _ :: us,   hmem => by
      rcases List.mem_cons.mp hmem with rfl | htl
      · exact .altL k
      · exact .altR (Trc.Alpha.choice k htl)

end CoreJS
