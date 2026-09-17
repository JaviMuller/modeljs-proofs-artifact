/-
  # Core JavaScript — Automaton Abstraction Relation

  This file is *not* a transcription of any figure in the paper. It
  generalises Appendix B.2.1's abstraction relation (Def. B8) from a single
  concrete/abstract configuration pair to the automaton model of
  `CoreJsAutomatonSemantics.lean`: relating a concrete configuration to the
  `AConf` a *labeling* assigns to a given automaton state.

  Independent of the old `CoreJsAbstractionRelation.lean` (kept only as
  reference material — see `CoreJsAutomatonSemantics.lean`'s header and
  `PROBLEMS.md` decision 6): `Heap.Alpha`/`Sto.Alpha`/`Reg.Alpha` and the
  supporting lemmas below are re-derived against this branch's own `AHeap`/
  `ASto`/`AReg`/`ALoc` (`CoreJsAutomatonSemantics.lean`), not imported.
  `Out.Alpha`/`Act.Alpha`/`Trc.Alpha`/`LocsAlpha` have no counterpart here at
  all — decision 2 of `PROBLEMS.md` drops action/trace labels from this phase
  entirely, and "did this statement return" is a structural fact about which
  automaton states/edges exist (`AExit`'s absence for `ret`), never a value
  carried on a result the way `Out.Alpha` related.

  See `PROBLEMS.md` for further decisions made while writing this file.
-/

import CoreJsAutomatonSemantics

namespace CoreJS

/-! ## Abstraction functions (Def. B8, REMARK A/B of the old
    `CoreJsAbstractionRelation.lean`, ported unchanged: `α` is a *partial*
    map, extended monotonically, and commits literal locations once and for
    all via `AlphaFn.Lits` rather than lazily at each evaluation). -/

/-- `α : Loc ⇀ L̂oc`. -/
abbrev AlphaFn := Loc → Option ALoc

def AlphaFn.Extends (α' α : AlphaFn) : Prop :=
  ∀ l al, α l = some al → α' l = some al

scoped infix:50 " ≥α " => AlphaFn.Extends

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

/-- `α` maps every literal location to its abstract counterpart, once and for
    all (this is what makes Lemma B9 below need no extension of `α`). -/
def AlphaFn.Lits [Concrete] [Abstract] (α : AlphaFn) : Prop :=
  ∀ v : Val, α (Concrete.litLoc v) = some (Abstract.litLocA v)

/-! ## The abstraction relation (Def. B8.1–B8.3: heap, store, register —
    B8.4–B8.6, about outcomes/actions/traces, have no counterpart here). -/

def Heap.Alpha (α : AlphaFn) (h : Heap) (ah : AHeap) : Prop :=
  (∀ l p l', h.obj l p = some l' →
      ∃ al al', α l = some al ∧ α l' = some al' ∧ ah.obj al p al') ∧
  (∀ l v, h.val l = some v → ∃ al, α l = some al ∧ (ah.val al).Mem v)

def Sto.Alpha (α : AlphaFn) (ρ : Sto) (aρ : ASto) : Prop :=
  ∀ x l, ρ x = some l → α.MapsInto l (aρ x)

def Reg.Alpha (α : AlphaFn) (δ : Reg) (aδ : AReg) : Prop :=
  (∀ l₁ l₂, δ.dep l₁ l₂ →
      ∃ a₁ a₂, α l₁ = some a₁ ∧ α l₂ = some a₂ ∧ aδ.dep a₁ a₂) ∧
  (∀ l, δ.ac l → α.MapsInto l aδ.ac) ∧
  (∀ l, δ.sk l → α.MapsInto l aδ.sk)

/-- Bundles the three components: `c ∼α ac`, `c` a concrete configuration and
    `ac` the `AConf` a labeling assigns to some automaton state. -/
def AConf.Alpha (α : AlphaFn) (c : Conf) (ac : AConf) : Prop :=
  Heap.Alpha α c.heap ac.heap ∧ Sto.Alpha α c.sto ac.sto ∧ Reg.Alpha α c.reg ac.reg

/-! ## Lemma B10 (α-Extension): every clause above is positive in `α`. -/

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

theorem AConf.Alpha.mono {α α' : AlphaFn} {c ac} (he : α' ≥α α)
    (k : AConf.Alpha α c ac) : AConf.Alpha α' c ac :=
  ⟨k.1.mono he, k.2.1.mono he, k.2.2.mono he⟩

/-! ## Lemma B9 (Expression Evaluation) -/

theorem eval_alpha [Concrete] [Abstract] {α : AlphaFn} {ρ aρ e l}
    (hlit : α.Lits) (hρ : Sto.Alpha α ρ aρ) (he : evalE ρ e = some l) :
    α.MapsInto l (aevalE aρ e) := by
  cases e with
  | val v =>
      have : l = Concrete.litLoc v := by simpa [evalE] using he.symm
      subst this
      exact ⟨Abstract.litLocA v, hlit v, rfl⟩
  | var x => exact hρ x l (by simpa [evalE] using he)

/-- Componentwise relation of a concrete argument list to an abstract one
    (ported from the old `CoreJsAbstractionRelation.lean`, where it also
    related `Act.call`/`Act.ret`'s argument lists — no counterpart of that
    here, but it is still exactly what relates a call's concrete argument
    locations to its abstract argument location sets, needed for the
    `callEntry` edge's soundness). -/
def LocsAlpha (α : AlphaFn) : List Loc → List ALocSet → Prop
  | [],      []      => True
  | l :: ls, L :: Ls => α.MapsInto l L ∧ LocsAlpha α ls Ls
  | _,       _       => False

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

theorem LocsAlpha.mono {α α' : AlphaFn} (he : α' ≥α α) :
    ∀ {ls Ls}, LocsAlpha α ls Ls → LocsAlpha α' ls Ls
  | [],      [],      _ => trivial
  | _ :: ls, _ :: Ls, k => ⟨k.1.mono he, LocsAlpha.mono he (Ls := Ls) (ls := ls) k.2⟩

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

/-! ## Heap lookup soundness (needed by `lookupS`/`lookupD`) -/

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

/-! ## Heap update soundness (needed by `updateS`/`updateD`)

No counterpart in the old `CoreJsAbstractionRelation.lean` — its generation
lemmas stopped at `lookupS`/`lookupD` (see its own "Remaining work" notes). -/

theorem Heap.Alpha.setObj {α : AlphaFn} {h : Heap} {ah : AHeap} {l1 l2 : Loc}
    {p : PropName} {L1 L2 : ALocSet} (k : Heap.Alpha α h ah)
    (h1 : α.MapsInto l1 L1) (h2 : α.MapsInto l2 L2) :
    Heap.Alpha α (h.setObj l1 p l2) (ah.weakSetObj L1 p L2) := by
  refine ⟨?_, k.2⟩
  intro l q l' hl
  simp only [Heap.setObj] at hl
  split at hl
  case isTrue heq =>
      obtain ⟨al1, hal1, hL1⟩ := h1
      obtain ⟨al2, hal2, hL2⟩ := h2
      obtain ⟨heql, heqq⟩ := heq
      subst heql; subst heqq
      have hll2 : l2 = l' := by injection hl
      subst hll2
      exact ⟨al1, al2, hal1, hal2, Or.inr ⟨hL1, rfl, hL2⟩⟩
  case isFalse hne =>
      obtain ⟨al, al', ha, ha', hobj⟩ := k.1 l q l' hl
      exact ⟨al, al', ha, ha', Or.inl hobj⟩

theorem Heap.Alpha.setObjV {α : AlphaFn} {h : Heap} {ah : AHeap} {l1 l3 : Loc}
    {p : PropName} {L1 L3 : ALocSet} {V : VSet} (k : Heap.Alpha α h ah)
    (h1 : α.MapsInto l1 L1) (hV : V.Mem (.str p)) (h3 : α.MapsInto l3 L3) :
    Heap.Alpha α (h.setObj l1 p l3) (ah.weakSetObjV L1 V L3) := by
  refine ⟨?_, k.2⟩
  intro l q l' hl
  simp only [Heap.setObj] at hl
  split at hl
  case isTrue heq =>
      obtain ⟨al1, hal1, hL1⟩ := h1
      obtain ⟨al3, hal3, hL3⟩ := h3
      obtain ⟨heql, heqq⟩ := heq
      subst heql; subst heqq
      have hll3 : l3 = l' := by injection hl
      subst hll3
      exact ⟨al1, al3, hal1, hal3, Or.inr ⟨hL1, hV, hL3⟩⟩
  case isFalse hne =>
      obtain ⟨al, al', ha, ha', hobj⟩ := k.1 l q l' hl
      exact ⟨al, al', ha, ha', Or.inl hobj⟩

/-! ## Lemma B13 (α-Monotonicity of the abstract domains) -/

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

theorem AConf.Alpha.le {α : AlphaFn} {c ac ac'} (k : AConf.Alpha α c ac)
    (hle : ac ⊑ ac') : AConf.Alpha α c ac' :=
  ⟨k.1.le hle.1, k.2.1.le hle.2.1, k.2.2.le hle.2.2⟩

end CoreJS
