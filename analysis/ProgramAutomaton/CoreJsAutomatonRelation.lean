/-
  # Core JavaScript — Automaton Abstraction Relation

  Relates concrete configurations and traces to the abstract ones of
  `CoreJsAutomatonSemantics.lean`, through an abstraction function `α` from
  concrete to abstract locations:

  * `Heap.Alpha`/`Sto.Alpha`/`Reg.Alpha`/`AConf.Alpha`: a concrete
    configuration against the `AConf` a labeling assigns to a state;
  * `Act.Alpha`/`Trc.Alpha`: a concrete trace against a walk's abstract
    actions, position by position;
  * the lemmas the soundness proof uses for each statement shape, and the
    invariant (`AlphaFn.AllocSafe`) and assumptions (`CrossSpec`) that let
    `α` be extended at every allocation.

  There is no relation on outcomes: whether a statement returned is a
  structural fact about which automaton states and edges exist, never a
  value carried on a result.

  Names follow the paper: concrete heaps, stores, registers, traces and
  locations are `h`, `ρ`, `δ`, `t`, `l`, and their abstract counterparts —
  written with a hat in the paper — are `hₐ`, `ρₐ`, `δₐ`, `tₐ`, `lₐ`
  (a Lean identifier cannot carry a combining hat); `cₐ` is an abstract
  configuration and `aₐ` an abstract action.

  The relations are written as in the paper, `x ∼α xₐ` (scoped notation; `α`
  is any abstraction function, `l ∼α' L` works as well): `l ∼α L`
  (`AlphaFn.MapsInto`), `h ∼α hₐ`, `ρ ∼α ρₐ`, `δ ∼α δₐ`, `c ∼α cₐ`
  (`Heap`/`Sto`/`Reg`/`AConf.Alpha`), `ls ∼α Ls` (`LocsAlpha`), `a ∼α aₐ`
  and `t ∼α tₐ` (`Act`/`ActsAlpha`/`Trc.Alpha`). One notation names all of
  them, so the types of both sides must be known where it is used: binders
  of a statement using it carry their types.
-/

import ProgramAutomaton.CoreJsAutomatonSemantics

namespace CoreJS

/-! ## Abstraction functions

`α` is a *partial* map, extended monotonically along a run (every relation
below is positive in `α`), and it commits literal locations once and for all
(`AlphaFn.Lits`) rather than lazily at each evaluation, so evaluating an
expression never needs to extend it. -/

/-- `α : Loc ⇀ ALoc`. -/
abbrev AlphaFn := Loc → Option ALoc

def AlphaFn.Extends (α' α : AlphaFn) : Prop :=
  ∀ l lₐ, α l = some lₐ → α' l = some lₐ

scoped infix:50 " ≥α " => AlphaFn.Extends

theorem AlphaFn.Extends.refl (α : AlphaFn) : α ≥α α := fun _ _ h => h

theorem AlphaFn.Extends.trans {α₁ α₂ α₃ : AlphaFn} (h₁ : α₂ ≥α α₁) (h₂ : α₃ ≥α α₂) :
    α₃ ≥α α₁ := fun l lₐ h => h₂ l lₐ (h₁ l lₐ h)

/-- `α l ∈ L`: the abstract counterpart of `l` exists and lies in `L`. -/
def AlphaFn.MapsInto (α : AlphaFn) (l : Loc) (L : ALocSet) : Prop :=
  ∃ lₐ, α l = some lₐ ∧ L lₐ

/-- `l ∼α L`, as in the paper. -/
scoped notation:50 (name := mapsIntoNotation) l:51 " ∼" α:max L:51 => AlphaFn.MapsInto α l L

theorem AlphaFn.MapsInto.mono {α α' : AlphaFn} {l : Loc} {L : ALocSet} (he : α' ≥α α)
    (h : l ∼α L) : l ∼α' L := by
  obtain ⟨lₐ, hlₐ, hL⟩ := h
  exact ⟨lₐ, he l lₐ hlₐ, hL⟩

theorem AlphaFn.MapsInto.subset {α : AlphaFn} {l : Loc} {L L' : ALocSet} (hs : L ⊆ L')
    (h : l ∼α L) : l ∼α L' := by
  obtain ⟨lₐ, hlₐ, hL⟩ := h
  exact ⟨lₐ, hlₐ, hs lₐ hL⟩

/-- `α` maps every literal location to its abstract counterpart, once and for
    all (this is what makes `eval_alpha` below need no extension of `α`). -/
def AlphaFn.Lits [Concrete] [Abstract] (α : AlphaFn) : Prop :=
  ∀ v : Val, α (Concrete.litLoc v) = some (Abstract.litLocA v)

/-! ## The abstraction relation on configurations -/

def Heap.Alpha (α : AlphaFn) (h : Heap) (hₐ : AHeap) : Prop :=
  ∀ l p l', h.obj l p = some l' →
    ∃ lₐ lₐ', α l = some lₐ ∧ α l' = some lₐ' ∧ hₐ.obj lₐ p lₐ'

/-- `h ∼α hₐ`, the paper's `h ∼α ĥ`. -/
scoped notation:50 (name := heapAlphaNotation) h:51 " ∼" α:max hₐ:51 => Heap.Alpha α h hₐ

def Sto.Alpha (α : AlphaFn) (ρ : Sto) (ρₐ : ASto) : Prop :=
  ∀ x l, ρ x = some l → l ∼α ρₐ x

/-- `ρ ∼α ρₐ`, as in the paper. -/
scoped notation:50 (name := stoAlphaNotation) ρ:51 " ∼" α:max ρₐ:51 => Sto.Alpha α ρ ρₐ

def Reg.Alpha (α : AlphaFn) (δ : Reg) (δₐ : AReg) : Prop :=
  (∀ l v, δ.val l = some v → ∃ lₐ, α l = some lₐ ∧ (δₐ.val lₐ).Mem v) ∧
  (∀ l₁ l₂, δ.dep l₁ l₂ →
      ∃ a₁ a₂, α l₁ = some a₁ ∧ α l₂ = some a₂ ∧ δₐ.dep a₁ a₂) ∧
  (∀ l, δ.ac l → l ∼α δₐ.ac) ∧
  (∀ l, δ.sk l → l ∼α δₐ.sk)

/-- `δ ∼α δₐ`, as in the paper. -/
scoped notation:50 (name := regAlphaNotation) δ:51 " ∼" α:max δₐ:51 => Reg.Alpha α δ δₐ

/-- Bundles the three components: `c ∼α cₐ`, `c` a concrete configuration and
    `cₐ` the `AConf` a labeling assigns to some automaton state. -/
def AConf.Alpha (α : AlphaFn) (c : Conf) (cₐ : AConf) : Prop :=
  c.heap ∼α cₐ.heap ∧ c.sto ∼α cₐ.sto ∧ c.reg ∼α cₐ.reg

/-- `c ∼α cₐ`. -/
scoped notation:50 (name := confAlphaNotation) c:51 " ∼" α:max cₐ:51 => AConf.Alpha α c cₐ

/-! ## Extending `α`: every clause above is positive in `α` -/

theorem Heap.Alpha.mono {α α' : AlphaFn} {h : Heap} {hₐ : AHeap} (he : α' ≥α α)
    (k : h ∼α hₐ) : h ∼α' hₐ := by
  intro l p l' hl
  obtain ⟨lₐ, lₐ', h1, h2, h3⟩ := k l p l' hl
  exact ⟨lₐ, lₐ', he l lₐ h1, he l' lₐ' h2, h3⟩

theorem Sto.Alpha.mono {α α' : AlphaFn} {ρ : Sto} {ρₐ : ASto} (he : α' ≥α α)
    (k : ρ ∼α ρₐ) : ρ ∼α' ρₐ :=
  fun x l hl => (k x l hl).mono he

theorem Reg.Alpha.mono {α α' : AlphaFn} {δ : Reg} {δₐ : AReg} (he : α' ≥α α)
    (k : δ ∼α δₐ) : δ ∼α' δₐ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l v hl
    obtain ⟨lₐ, h1, h2⟩ := k.1 l v hl
    exact ⟨lₐ, he l lₐ h1, h2⟩
  · intro l₁ l₂ hl
    obtain ⟨a₁, a₂, h1, h2, h3⟩ := k.2.1 l₁ l₂ hl
    exact ⟨a₁, a₂, he l₁ a₁ h1, he l₂ a₂ h2, h3⟩
  · intro l hl
    exact (k.2.2.1 l hl).mono he
  · intro l hl
    exact (k.2.2.2 l hl).mono he

theorem AConf.Alpha.mono {α α' : AlphaFn} {c : Conf} {cₐ : AConf} (he : α' ≥α α)
    (k : c ∼α cₐ) : c ∼α' cₐ :=
  ⟨k.1.mono he, k.2.1.mono he, k.2.2.mono he⟩

/-! ## Expression evaluation -/

theorem eval_alpha [Concrete] [Abstract] {α : AlphaFn} {ρ : Sto} {ρₐ : ASto} {e : Expr} {l : Loc}
    (hlit : α.Lits) (hρ : ρ ∼α ρₐ) (he : ⟦e⟧ρ = some l) :
    l ∼α ⟦e⟧ρₐ := by
  cases e with
  | val v =>
      have : l = Concrete.litLoc v := by simpa [evalE] using he.symm
      subst this
      exact ⟨Abstract.litLocA v, hlit v, rfl⟩
  | var x => exact hρ x l (by simpa [evalE] using he)

/-- Componentwise relation of a concrete argument list to an abstract one:
    relates a call's concrete argument locations to its abstract argument
    location sets, both for the callee's initial store and for the call's
    trace action. -/
def LocsAlpha (α : AlphaFn) : List Loc → List ALocSet → Prop
  | [],      []      => True
  | l :: ls, L :: Ls => l ∼α L ∧ LocsAlpha α ls Ls
  | _,       _       => False

/-- `ls ∼α Ls`, componentwise. -/
scoped notation:50 (name := locsAlphaNotation) ls:51 " ∼" α:max Ls:51 => LocsAlpha α ls Ls

theorem evals_alpha [Concrete] [Abstract] {α : AlphaFn} {ρ : Sto} {ρₐ : ASto} (hlit : α.Lits)
    (hρ : ρ ∼α ρₐ) :
    ∀ (es : List Expr) {ls}, ⟦es⟧ρ = some ls → ls ∼α ⟦es⟧ρₐ
  | [],      ls, he => by
      simp only [evalEs, Option.some.injEq] at he
      subst he
      exact trivial
  | e :: es, ls, he => by
      rw [evalEs] at he
      cases hE : ⟦e⟧ρ with
      | none => rw [hE] at he; simp at he
      | some l =>
        cases hEs : ⟦es⟧ρ with
        | none => rw [hE, hEs] at he; simp at he
        | some ls' =>
          rw [hE, hEs] at he
          have hx : l :: ls' = ls := by injection he
          subst hx
          exact ⟨eval_alpha hlit hρ hE, evals_alpha hlit hρ es hEs⟩

theorem LocsAlpha.mono {α α' : AlphaFn} (he : α' ≥α α) :
    ∀ {ls : List Loc} {Ls : List ALocSet}, ls ∼α Ls → ls ∼α' Ls
  | [],      [],      _ => trivial
  | _ :: ls, _ :: Ls, k => ⟨k.1.mono he, LocsAlpha.mono he (Ls := Ls) (ls := ls) k.2⟩

/-! ## Store update -/

theorem sto_upd_alpha {α : AlphaFn} {ρ : Sto} {ρₐ : ASto} {x : Var} {l : Loc} {L : ALocSet}
    (hρ : ρ ∼α ρₐ)
    (hl : l ∼α L) : ρ.upd x l ∼α ρₐ.upd x L := by
  intro y l' hy
  by_cases hxy : y = x
  · subst hxy
    have : l' = l := by simpa [Sto.upd] using hy.symm
    subst this
    simpa [ASto.upd] using hl
  · have hy' : ρ y = some l' := by simpa [Sto.upd, hxy] using hy
    have := hρ y l' hy'
    simpa [ASto.upd, hxy] using this

/-! ## Heap and value lookup soundness (needed by `lookupS`/`lookupD`) -/

theorem Heap.Alpha.objOf {α : AlphaFn} {h : Heap} {hₐ : AHeap} {l₁ l₂ : Loc}
    {L : ALocSet} {p : PropName}
    (k : h ∼α hₐ) (hL : l₁ ∼α L) (hobj : h.obj l₁ p = some l₂) :
    l₂ ∼α hₐ.objOf L p := by
  obtain ⟨lₐ, hlₐ, hLlₐ⟩ := hL
  obtain ⟨lₐ', lₐ'', hlₐ', hlₐ'', hobj'⟩ := k l₁ p l₂ hobj
  rw [hlₐ] at hlₐ'
  cases hlₐ'
  exact ⟨lₐ'', hlₐ'', lₐ, hLlₐ, hobj'⟩

theorem Reg.Alpha.valOf {α : AlphaFn} {δ : Reg} {δₐ : AReg} {l : Loc} {v : Val}
    {L : ALocSet}
    (k : δ ∼α δₐ) (hL : l ∼α L) (hval : δ.val l = some v) :
    (δₐ.valOf L).Mem v := by
  obtain ⟨lₐ, hlₐ, hLlₐ⟩ := hL
  obtain ⟨lₐ', hlₐ', hmem⟩ := k.1 l v hval
  rw [hlₐ] at hlₐ'
  cases hlₐ'
  exact ⟨lₐ, hLlₐ, hmem⟩

theorem Heap.Alpha.objOfV {α : AlphaFn} {h : Heap} {hₐ : AHeap} {l₁ l₂ : Loc}
    {L : ALocSet} {V : VSet} {p : PropName}
    (k : h ∼α hₐ) (hL : l₁ ∼α L) (hV : V.HasKey p)
    (hobj : h.obj l₁ p = some l₂) :
    l₂ ∼α hₐ.objOfV L V := by
  obtain ⟨lₐ, hlₐ, hLlₐ⟩ := hL
  obtain ⟨lₐ', lₐ'', hlₐ', hlₐ'', hobj'⟩ := k l₁ p l₂ hobj
  rw [hlₐ] at hlₐ'
  cases hlₐ'
  exact ⟨lₐ'', hlₐ'', lₐ, p, hLlₐ, hV, hobj'⟩

/-! ## Heap update soundness (needed by `updateS`/`updateD`) -/

theorem Heap.Alpha.setObj {α : AlphaFn} {h : Heap} {hₐ : AHeap} {l1 l2 : Loc}
    {p : PropName} {L1 L2 : ALocSet} (k : h ∼α hₐ)
    (h1 : l1 ∼α L1) (h2 : l2 ∼α L2) :
    h.setObj l1 p l2 ∼α hₐ.weakSetObj L1 p L2 := by
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
      obtain ⟨lₐ, lₐ', ha, ha', hobj⟩ := k l q l' hl
      exact ⟨lₐ, lₐ', ha, ha', Or.inl hobj⟩

theorem Heap.Alpha.setObjV {α : AlphaFn} {h : Heap} {hₐ : AHeap} {l1 l3 : Loc}
    {p : PropName} {L1 L3 : ALocSet} {V : VSet} (k : h ∼α hₐ)
    (h1 : l1 ∼α L1) (hV : V.HasKey p) (h3 : l3 ∼α L3) :
    h.setObj l1 p l3 ∼α hₐ.weakSetObjV L1 V L3 := by
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
      obtain ⟨lₐ, lₐ', ha, ha', hobj⟩ := k l q l' hl
      exact ⟨lₐ, lₐ', ha, ha', Or.inl hobj⟩

/-! ## Monotonicity in the abstract side: a relation to a configuration
    carries over to any larger one -/

theorem Heap.Alpha.le {α : AlphaFn} {h : Heap} {hₐ hₐ' : AHeap} (k : h ∼α hₐ)
    (hle : hₐ ⊑ hₐ') : h ∼α hₐ' := by
  intro l p l' hl
  obtain ⟨lₐ, lₐ', h1, h2, h3⟩ := k l p l' hl
  exact ⟨lₐ, lₐ', h1, h2, hle lₐ p lₐ' h3⟩

theorem Sto.Alpha.le {α : AlphaFn} {ρ : Sto} {ρₐ ρₐ' : ASto} (k : ρ ∼α ρₐ)
    (hle : ρₐ ⊑ ρₐ') : ρ ∼α ρₐ' :=
  fun x l hl => (k x l hl).subset (hle x)

theorem Reg.Alpha.le {α : AlphaFn} {δ : Reg} {δₐ δₐ' : AReg} (k : δ ∼α δₐ)
    (hle : δₐ ⊑ δₐ') : δ ∼α δₐ' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l v hl
    obtain ⟨lₐ, h1, h2⟩ := k.1 l v hl
    exact ⟨lₐ, h1, hle.1 lₐ v h2⟩
  · intro l₁ l₂ hl
    obtain ⟨a₁, a₂, h1, h2, h3⟩ := k.2.1 l₁ l₂ hl
    exact ⟨a₁, a₂, h1, h2, hle.2.1 a₁ a₂ h3⟩
  · intro l hl
    exact (k.2.2.1 l hl).subset hle.2.2.1
  · intro l hl
    exact (k.2.2.2 l hl).subset hle.2.2.2

theorem AConf.Alpha.le {α : AlphaFn} {c : Conf} {cₐ cₐ' : AConf} (k : c ∼α cₐ)
    (hle : cₐ ⊑ cₐ') : c ∼α cₐ' :=
  ⟨k.1.le hle.1, k.2.1.le hle.2.1, k.2.2.le hle.2.2⟩

/-! ## Updates at a fresh allocation (needed by `binOp`/`objLit`)

Unlike `setObj`/`setObjV` above, these write at the location an allocation
just returned, which `α` must already map to that allocation's abstract
site (`AlphaFn.AllocSafe.extend` below provides such an `α`). -/

theorem VSet.mem_join_left {V₁ V₂ : VSet} {v : Val} (h : V₁.Mem v) : (VSet.join V₁ V₂).Mem v := by
  cases V₁ <;> cases V₂ <;> first | trivial | exact Or.inl h

theorem VSet.mem_join_right {V₁ V₂ : VSet} {v : Val} (h : V₂.Mem v) : (VSet.join V₁ V₂).Mem v := by
  cases V₁ <;> cases V₂ <;> first | trivial | exact Or.inr h

theorem Reg.Alpha.setVal {α : AlphaFn} {δ : Reg} {δₐ : AReg} {l : Loc} {lₐ : ALoc}
    {v : Val} {V : VSet} (k : δ ∼α δₐ) (hl : α l = some lₐ) (hv : V.Mem v) :
    δ.setVal l v ∼α δₐ.weakSetVal lₐ V := by
  refine ⟨?_, k.2⟩
  intro l' v' hl'
  by_cases e : l' = l
  · subst e
    simp only [Reg.setVal, if_pos] at hl'
    cases hl'
    exact ⟨lₐ, hl, by simpa [AReg.weakSetVal] using VSet.mem_join_left hv⟩
  · have hl'' : δ.val l' = some v' := by simpa [Reg.setVal, e] using hl'
    obtain ⟨lₐ', hlₐ', hmem⟩ := k.1 l' v' hl''
    refine ⟨lₐ', hlₐ', ?_⟩
    by_cases e' : lₐ' = lₐ
    · simpa [AReg.weakSetVal, e'] using VSet.mem_join_right (V₁ := V) (e' ▸ hmem)
    · simpa [AReg.weakSetVal, e'] using hmem

theorem Heap.Alpha.setObjs {α : AlphaFn} {l : Loc} {lₐ : ALoc} (hl : α l = some lₐ) :
    ∀ (ps : List PropName) {h : Heap} {hₐ : AHeap} {ls : List Loc} {Ls : List ALocSet},
      h ∼α hₐ → ls ∼α Ls →
      h.setObjs l (ps.zip ls) ∼α hₐ.weakSetObjs lₐ (ps.zip Ls)
  | [],      _, _, _,       _,       k, _  => k
  | _ :: _,  _, _, [],      [],      k, _  => k
  | _ :: ps, _, _, _ :: _,  _ :: _,  k, hLs =>
      Heap.Alpha.setObjs hl ps (k.setObj ⟨lₐ, hl, rfl⟩ hLs.1) hLs.2
  | _ :: _,  _, _, [],      _ :: _,  _, hLs => hLs.elim
  | _ :: _,  _, _, _ :: _,  [],      _, hLs => hLs.elim

/-! ## Register update soundness (needed by `binOp`/`objLit`) -/

theorem Reg.Alpha.binOp {α : AlphaFn} {δ : Reg} {δₐ : AReg} {l l₁ l₂ : Loc} {lₐ : ALoc}
    {L₁ L₂ : ALocSet} (k : δ ∼α δₐ) (hl : α l = some lₐ)
    (h₁ : l₁ ∼α L₁) (h₂ : l₂ ∼α L₂) :
    Reg.Alpha α (δ.setDep l (δ.dep l₁ ∪ δ.dep l₂ ∪ {l₁, l₂}))
      (δₐ.weakSetDep lₐ (δₐ.depOf L₁ ∪ δₐ.depOf L₂ ∪ L₁ ∪ L₂)) := by
  obtain ⟨lₐ₁, hlₐ₁, hL₁⟩ := h₁
  obtain ⟨lₐ₂, hlₐ₂, hL₂⟩ := h₂
  refine ⟨k.1, ?_, k.2.2⟩
  intro a b hab
  by_cases ea : a = l
  · subst ea
    have hab' : (δ.dep l₁ ∪ δ.dep l₂ ∪ {l₁, l₂}) b := by simpa [Reg.setDep] using hab
    have hnew : ∀ b', (δₐ.depOf L₁ ∪ δₐ.depOf L₂ ∪ L₁ ∪ L₂) b' →
        (δₐ.weakSetDep lₐ (δₐ.depOf L₁ ∪ δₐ.depOf L₂ ∪ L₁ ∪ L₂)).dep lₐ b' := by
      intro b' hb'
      simp only [AReg.weakSetDep, if_pos]
      exact Or.inl hb'
    rcases mem_binOpDep.1 hab' with hb | hb | rfl | rfl
    · obtain ⟨a₁, b₁, ha₁, hb₁, hdep⟩ := k.2.1 _ _ hb
      rw [hlₐ₁] at ha₁; cases ha₁
      exact ⟨lₐ, b₁, hl, hb₁, hnew _ (Or.inl (Or.inl (Or.inl ⟨lₐ₁, hL₁, hdep⟩)))⟩
    · obtain ⟨a₂, b₂, ha₂, hb₂, hdep⟩ := k.2.1 _ _ hb
      rw [hlₐ₂] at ha₂; cases ha₂
      exact ⟨lₐ, b₂, hl, hb₂, hnew _ (Or.inl (Or.inl (Or.inr ⟨lₐ₂, hL₂, hdep⟩)))⟩
    · exact ⟨lₐ, lₐ₁, hl, hlₐ₁, hnew _ (Or.inl (Or.inr hL₁))⟩
    · exact ⟨lₐ, lₐ₂, hl, hlₐ₂, hnew _ (Or.inr hL₂)⟩
  · have hab' : δ.dep a b := by simpa [Reg.setDep, ea] using hab
    obtain ⟨a₁, b₁, ha₁, hb₁, hdep⟩ := k.2.1 _ _ hab'
    refine ⟨a₁, b₁, ha₁, hb₁, ?_⟩
    by_cases e : a₁ = lₐ
    · simp only [AReg.weakSetDep, e, if_pos]
      exact Or.inr (e ▸ hdep)
    · simpa [AReg.weakSetDep, e] using hdep

theorem Reg.Alpha.setDep_empty {α : AlphaFn} {δ : Reg} {δₐ : AReg} {l : Loc}
    (k : δ ∼α δₐ) : δ.setDep l ∅ ∼α δₐ := by
  refine ⟨k.1, ?_, k.2.2⟩
  intro a b hab
  by_cases ea : a = l
  · subst ea
    have : (∅ : LocSet) b := by simpa [Reg.setDep] using hab
    exact this.elim
  · exact k.2.1 a b (by simpa [Reg.setDep, ea] using hab)

/-! ## Keeping `α` extensible at allocations

`α` is only ever extended at a location an allocation has just returned, and
the extension must agree with whatever `α` already says there. It never has
to: a location an allocation returns is free in the current memory
(`ConcreteSpec.allocC_fresh`) — and every allocated location holds a value
afterwards (an object its reference, `.loc l`), so no allocation ever returns
a location again — and it is not a literal location (`ConcreteSpec.allocC_lit`). So if
every location `α` maps is in use or a literal location, `α` does not map the
new one yet. -/

/-- Every location `α` maps is in use in the memory `⟨h, δ⟩`, or a literal
    location. -/
def AlphaFn.AllocSafe [Concrete] (α : AlphaFn) (h : Heap) (δ : Reg) : Prop :=
  ∀ l lₐ, α l = some lₐ → h.Defined δ l ∨ ∃ v, l = Concrete.litLoc v

/-- `AllocSafe` survives any memory change that keeps every in-use location in
    use. -/
theorem AlphaFn.AllocSafe.mono_heap [Concrete] {α : AlphaFn} {h h' : Heap} {δ δ' : Reg}
    (k : α.AllocSafe h δ) (hd : ∀ l, h.Defined δ l → h'.Defined δ' l) :
    α.AllocSafe h' δ' := by
  intro l lₐ hl
  rcases k l lₐ hl with hdef | hrest
  · exact Or.inl (hd l hdef)
  · exact Or.inr hrest

theorem AlphaFn.Lits.mono [Concrete] [Abstract] {α α' : AlphaFn} (he : α' ≥α α)
    (k : α.Lits) : α'.Lits :=
  fun v => he _ _ (k v)

/-! ## Assumptions relating the concrete and abstract parameters

`ConcreteSpec` and `AbstractSpec` each constrain one side; the soundness proof
also needs the two sides' binary operators to agree. -/

structure CrossSpec [Concrete] [Abstract] : Prop where
  /-- `opSemA` (the abstract `⊕`) soundly over-approximates `opSem` (`⊕`). -/
  opSem_sound : ∀ op v₁ v₂ (V₁ V₂ : VSet), V₁.Mem v₁ → V₂.Mem v₂ →
    (Abstract.opSemA op V₁ V₂).Mem (Concrete.opSem op v₁ v₂)
/-- Extending `α` at a fresh allocation: `α` does not map the allocated
    location yet, so it can be extended to map it to its abstract site, and the
    extension stays allocation-safe for any memory that keeps in use what the
    current one does, plus the allocated location itself. -/
theorem AlphaFn.AllocSafe.extend [Concrete] [Abstract] (cspec : ConcreteSpec)
    {α : AlphaFn} {h : Heap} {δ : Reg} (k : α.AllocSafe h δ)
    (hfin : h.Finite δ) (κ : Idx) (hₐ : AHeap) (δₐ : AReg) :
    ∃ α', α' ≥α α ∧ α' (Concrete.allocC h δ κ) = some (Abstract.allocA hₐ δₐ κ) ∧
      ∀ (h' : Heap) (δ' : Reg), (∀ l, h.Defined δ l → h'.Defined δ' l) →
        h'.Defined δ' (Concrete.allocC h δ κ) → α'.AllocSafe h' δ' := by
  let l := Concrete.allocC h δ κ
  let α' : AlphaFn := fun l' => if l' = l then some (Abstract.allocA hₐ δₐ κ) else α l'
  have hnone : ∀ lₐ, α l ≠ some lₐ := by
    intro lₐ hl
    rcases k l lₐ hl with hdef | ⟨v, hv⟩
    · exact Heap.not_defined_of_free (cspec.allocC_fresh h δ κ hfin) hdef
    · exact cspec.allocC_lit h δ κ v hfin hv
  refine ⟨α', ?_, if_pos rfl, ?_⟩
  · intro l' lₐ hl'
    by_cases e : l' = l
    · subst e; exact absurd hl' (hnone lₐ)
    · simpa [α', e] using hl'
  · intro h' δ' hd hl l' lₐ hl'
    by_cases e : l' = l
    · subst e; exact Or.inl hl
    · have : α l' = some lₐ := by simpa [α', e] using hl'
      rcases k l' lₐ this with hdef | hlit
      · exact Or.inl (hd l' hdef)
      · exact Or.inr hlit

/-! ## The initial abstraction

At the start of a run `α` maps exactly the literal locations, each to its
abstract counterpart. -/

open Classical in
/-- `α` defined exactly on literal locations: `l_v ↦ litLocA v`. -/
noncomputable def AlphaFn.lits [Concrete] [Abstract] : AlphaFn := fun l =>
  if h : ∃ v, Concrete.litLoc v = l then some (Abstract.litLocA (Classical.choose h)) else none

theorem AlphaFn.lits_lits [Concrete] [Abstract] (cspec : ConcreteSpec) :
    (AlphaFn.lits : AlphaFn).Lits := by
  intro v
  have h : ∃ w, Concrete.litLoc w = Concrete.litLoc v := ⟨v, rfl⟩
  simp only [AlphaFn.lits, dif_pos h]
  rw [cspec.litLoc_inj _ _ (Classical.choose_spec h)]

theorem AlphaFn.lits_allocSafe [Concrete] [Abstract] (h : Heap) (δ : Reg) :
    (AlphaFn.lits : AlphaFn).AllocSafe h δ := by
  intro l lₐ hl
  by_cases e : ∃ v, Concrete.litLoc v = l
  · obtain ⟨v, hv⟩ := e
    exact Or.inr ⟨v, hv.symm⟩
  · simp [AlphaFn.lits, e] at hl

/-- The initial configuration of a run relates to the initial abstract
    configuration. -/
theorem AConf.Alpha.init [Concrete] [Abstract] (cspec : ConcreteSpec) (Γ : Env)
    (fs : List Fid) (s : Stmt) :
    AConf.Alpha AlphaFn.lits (Conf.init Γ fs s) (AConf.init Γ s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l p l' h; exact absurd h (by simp [Conf.init, Heap.empty])
  · intro x l h; exact absurd h (by simp [Conf.init, Sto.empty])
  rotate_left
  · intro l₁ l₂ h; exact (h : False).elim
  · intro l h; exact (h : False).elim
  · intro l h; exact (h : False).elim
  intro l v hl
  have hl' : (initLits Γ fs s).find? (fun w => Concrete.litLoc w == l) = some v := hl
  have hmem := List.mem_of_find?_eq_some hl'
  have hp := List.find?_some hl'
  simp only [beq_iff_eq] at hp
  subst hp
  have hinit : InitLit Γ s v := by
    rcases List.mem_cons.1 hmem with rfl | hmem
    · exact Or.inl (List.mem_cons_self ..)
    · rcases List.mem_append.1 hmem with hs | hΓ
      · exact Or.inl (List.mem_cons_of_mem _ hs)
      · exact Or.inr (Env.mem_lits hΓ)
  exact ⟨Abstract.litLocA v, AlphaFn.lits_lits cspec v, hinit, rfl⟩

/-! ## Actions and traces

The abstraction relation extended pointwise to trace actions, and then to
traces: a concrete trace relates to a list of abstract actions when both
have the same length and their actions relate position by position. A
callee position relates exactly (`α lf = some lfₐ`), since the abstract
action names a single location there. -/

def Act.Alpha (α : AlphaFn) : Act → AAct → Prop
  | .lookup l₁ l₂ l₃, .lookup L₁ L₂ L₃ =>
      l₁ ∼α L₁ ∧ l₂ ∼α L₂ ∧ l₃ ∼α L₃
  | .update l₁ l₂ l₃, .update L₁ L₂ L₃ =>
      l₁ ∼α L₁ ∧ l₂ ∼α L₂ ∧ l₃ ∼α L₃
  | .call lf ls, .call lfₐ Ls => α lf = some lfₐ ∧ ls ∼α Ls
  | .ret lf l, .ret lfₐ L     => α lf = some lfₐ ∧ l ∼α L
  | _, _                      => False

/-- `a ∼α aₐ`, the paper's `a ∼α â`. -/
scoped notation:50 (name := actAlphaNotation) a:51 " ∼" α:max aₐ:51 => Act.Alpha α a aₐ

theorem Act.Alpha.mono {α α' : AlphaFn} (he : α' ≥α α) :
    ∀ {a : Act} {aₐ : AAct}, a ∼α aₐ → a ∼α' aₐ
  | .lookup _ _ _, .lookup _ _ _, k => ⟨k.1.mono he, k.2.1.mono he, k.2.2.mono he⟩
  | .update _ _ _, .update _ _ _, k => ⟨k.1.mono he, k.2.1.mono he, k.2.2.mono he⟩
  | .call _ _,     .call _ _,     k => ⟨he _ _ k.1, k.2.mono he⟩
  | .ret _ _,      .ret _ _,      k => ⟨he _ _ k.1, k.2.mono he⟩

/-- Position-by-position relation of concrete to abstract action lists. -/
def ActsAlpha (α : AlphaFn) : List Act → List AAct → Prop
  | [],      []      => True
  | a :: t, aₐ :: tₐ => a ∼α aₐ ∧ ActsAlpha α t tₐ
  | _,       _       => False

/-- `t ∼α tₐ` for a list `t` of actions, position by position. -/
scoped notation:50 (name := actsAlphaNotation) t:51 " ∼" α:max tₐ:51 => ActsAlpha α t tₐ

theorem ActsAlpha.mono {α α' : AlphaFn} (he : α' ≥α α) :
    ∀ {t : List Act} {tₐ : List AAct}, t ∼α tₐ → t ∼α' tₐ
  | [],      [],      _ => trivial
  | _ :: _,  _ :: _,  k => ⟨k.1.mono he, ActsAlpha.mono he k.2⟩

theorem ActsAlpha.append {α : AlphaFn} :
    ∀ {t₁ t₂ : List Act} {tₐ₁ tₐ₂ : List AAct},
      t₁ ∼α tₐ₁ → t₂ ∼α tₐ₂ → t₁ ++ t₂ ∼α tₐ₁ ++ tₐ₂
  | [],      _, [],      _, _,  k₂ => k₂
  | _ :: _,  _, _ :: _,  _, k₁, k₂ => ⟨k₁.1, ActsAlpha.append k₁.2 k₂⟩

/-- A concrete trace relates to a list of abstract actions. -/
def Trc.Alpha (α : AlphaFn) (t : Trc) (tₐ : List AAct) : Prop :=
  t.toList ∼α tₐ

/-- `t ∼α tₐ`, as in the paper. -/
scoped notation:50 (name := trcAlphaNotation) t:51 " ∼" α:max tₐ:51 => Trc.Alpha α t tₐ

theorem Trc.Alpha.mono {α α' : AlphaFn} (he : α' ≥α α) {t : Trc} {tₐ : List AAct}
    (k : t ∼α tₐ) : t ∼α' tₐ :=
  ActsAlpha.mono he k

theorem Trc.Alpha.seq {α : AlphaFn} {t₁ t₂ : Trc} {tₐ₁ tₐ₂ : List AAct}
    (k₁ : t₁ ∼α tₐ₁) (k₂ : t₂ ∼α tₐ₂) :
    .seq t₁ t₂ ∼α tₐ₁ ++ tₐ₂ :=
  ActsAlpha.append k₁ k₂

end CoreJS
