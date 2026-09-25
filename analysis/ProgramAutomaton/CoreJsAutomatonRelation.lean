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
-/

import ProgramAutomaton.CoreJsAutomatonSemantics

namespace CoreJS

/-! ## Abstraction functions

`α` is a *partial* map, extended monotonically along a run (every relation
below is positive in `α`), and it commits literal locations once and for all
(`AlphaFn.Lits`) rather than lazily at each evaluation, so evaluating an
expression never needs to extend it. -/

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
    all (this is what makes `eval_alpha` below need no extension of `α`). -/
def AlphaFn.Lits [Concrete] [Abstract] (α : AlphaFn) : Prop :=
  ∀ v : Val, α (Concrete.litLoc v) = some (Abstract.litLocA v)

/-! ## The abstraction relation on configurations -/

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

/-! ## Extending `α`: every clause above is positive in `α` -/

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

/-! ## Expression evaluation -/

theorem eval_alpha [Concrete] [Abstract] {α : AlphaFn} {ρ aρ e l}
    (hlit : α.Lits) (hρ : Sto.Alpha α ρ aρ) (he : evalE ρ e = some l) :
    α.MapsInto l (aevalE aρ e) := by
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

/-! ## Store update -/

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

/-! ## Heap update soundness (needed by `updateS`/`updateD`) -/

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

/-! ## Monotonicity in the abstract side: a relation to a configuration
    carries over to any larger one -/

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

/-! ## Heap update soundness at a fresh allocation (needed by `binOp`/`objLit`)

Unlike `setObj`/`setObjV` above, these write at the location an allocation
just returned, which `α` must already map to that allocation's abstract
site (`AlphaFn.AllocSafe.extend` below provides such an `α`). -/

theorem VSet.mem_join_left {V₁ V₂ : VSet} {v : Val} (h : V₁.Mem v) : (VSet.join V₁ V₂).Mem v := by
  cases V₁ <;> cases V₂ <;> first | trivial | exact Or.inl h

theorem VSet.mem_join_right {V₁ V₂ : VSet} {v : Val} (h : V₂.Mem v) : (VSet.join V₁ V₂).Mem v := by
  cases V₁ <;> cases V₂ <;> first | trivial | exact Or.inr h

theorem Heap.Alpha.setVal {α : AlphaFn} {h : Heap} {ah : AHeap} {l : Loc} {al : ALoc}
    {v : Val} {V : VSet} (k : Heap.Alpha α h ah) (hl : α l = some al) (hv : V.Mem v) :
    Heap.Alpha α (h.setVal l v) (ah.weakSetVal al V) := by
  refine ⟨k.1, ?_⟩
  intro l' v' hl'
  by_cases e : l' = l
  · subst e
    simp only [Heap.setVal, if_pos] at hl'
    cases hl'
    exact ⟨al, hl, by simpa [AHeap.weakSetVal] using VSet.mem_join_left hv⟩
  · have hl'' : h.val l' = some v' := by simpa [Heap.setVal, e] using hl'
    obtain ⟨al', hal', hmem⟩ := k.2 l' v' hl''
    refine ⟨al', hal', ?_⟩
    by_cases e' : al' = al
    · simpa [AHeap.weakSetVal, e'] using VSet.mem_join_right (V₁ := V) (e' ▸ hmem)
    · simpa [AHeap.weakSetVal, e'] using hmem

theorem Heap.Alpha.setObjs {α : AlphaFn} {l : Loc} {al : ALoc} (hl : α l = some al) :
    ∀ (ps : List PropName) {h : Heap} {ah : AHeap} {ls : List Loc} {Ls : List ALocSet},
      Heap.Alpha α h ah → LocsAlpha α ls Ls →
      Heap.Alpha α (h.setObjs l (ps.zip ls)) (ah.weakSetObjs al (ps.zip Ls))
  | [],      _, _, _,       _,       k, _  => k
  | _ :: _,  _, _, [],      [],      k, _  => k
  | _ :: ps, _, _, _ :: _,  _ :: _,  k, hLs =>
      Heap.Alpha.setObjs hl ps (k.setObj ⟨al, hl, rfl⟩ hLs.1) hLs.2
  | _ :: _,  _, _, [],      _ :: _,  _, hLs => hLs.elim
  | _ :: _,  _, _, _ :: _,  [],      _, hLs => hLs.elim

/-! ## Register update soundness (needed by `binOp`/`objLit`) -/

theorem Reg.Alpha.binOp {α : AlphaFn} {δ : Reg} {aδ : AReg} {l l₁ l₂ : Loc} {al : ALoc}
    {L₁ L₂ : ALocSet} (k : Reg.Alpha α δ aδ) (hl : α l = some al)
    (h₁ : α.MapsInto l₁ L₁) (h₂ : α.MapsInto l₂ L₂) :
    Reg.Alpha α (δ.setDep l (δ.dep l₁ ∪ δ.dep l₂ ∪ {l₁, l₂}))
      (aδ.weakSetDep al (aδ.depOf L₁ ∪ aδ.depOf L₂ ∪ L₁ ∪ L₂)) := by
  obtain ⟨al₁, hal₁, hL₁⟩ := h₁
  obtain ⟨al₂, hal₂, hL₂⟩ := h₂
  refine ⟨?_, k.2.1, k.2.2⟩
  intro a b hab
  by_cases ea : a = l
  · subst ea
    have hab' : (δ.dep l₁ ∪ δ.dep l₂ ∪ {l₁, l₂}) b := by simpa [Reg.setDep] using hab
    have hnew : ∀ b', (aδ.depOf L₁ ∪ aδ.depOf L₂ ∪ L₁ ∪ L₂) b' →
        (aδ.weakSetDep al (aδ.depOf L₁ ∪ aδ.depOf L₂ ∪ L₁ ∪ L₂)).dep al b' := by
      intro b' hb'
      simp only [AReg.weakSetDep, if_pos]
      exact Or.inl hb'
    rcases mem_binOpDep.1 hab' with hb | hb | rfl | rfl
    · obtain ⟨a₁, b₁, ha₁, hb₁, hdep⟩ := k.1 _ _ hb
      rw [hal₁] at ha₁; cases ha₁
      exact ⟨al, b₁, hl, hb₁, hnew _ (Or.inl (Or.inl (Or.inl ⟨al₁, hL₁, hdep⟩)))⟩
    · obtain ⟨a₂, b₂, ha₂, hb₂, hdep⟩ := k.1 _ _ hb
      rw [hal₂] at ha₂; cases ha₂
      exact ⟨al, b₂, hl, hb₂, hnew _ (Or.inl (Or.inl (Or.inr ⟨al₂, hL₂, hdep⟩)))⟩
    · exact ⟨al, al₁, hl, hal₁, hnew _ (Or.inl (Or.inr hL₁))⟩
    · exact ⟨al, al₂, hl, hal₂, hnew _ (Or.inr hL₂)⟩
  · have hab' : δ.dep a b := by simpa [Reg.setDep, ea] using hab
    obtain ⟨a₁, b₁, ha₁, hb₁, hdep⟩ := k.1 _ _ hab'
    refine ⟨a₁, b₁, ha₁, hb₁, ?_⟩
    by_cases e : a₁ = al
    · simp only [AReg.weakSetDep, e, if_pos]
      exact Or.inr (e ▸ hdep)
    · simpa [AReg.weakSetDep, e] using hdep

theorem Reg.Alpha.setDep_empty {α : AlphaFn} {δ : Reg} {aδ : AReg} {l : Loc}
    (k : Reg.Alpha α δ aδ) : Reg.Alpha α (δ.setDep l ∅) aδ := by
  refine ⟨?_, k.2.1, k.2.2⟩
  intro a b hab
  by_cases ea : a = l
  · subst ea
    have : (∅ : LocSet) b := by simpa [Reg.setDep] using hab
    exact this.elim
  · exact k.1 a b (by simpa [Reg.setDep, ea] using hab)

/-! ## Keeping `α` extensible at allocations

`α` is only ever extended at a location an allocation has just returned, and
the extension must agree with whatever `α` already says there. A location an
allocation returns is not in use in the current heap (`ConcreteSpec.
allocC_fresh`) and is not a literal location (`CrossSpec.allocC_lit`,
`CoreJsAutomatonSoundness.lean`). Neither fact on its own rules out that `α`
already maps it: an object literal with no fields allocates a location and
leaves it unused (`Heap.setObjs l []` is `h`), so a later allocation may
return that same location again. `AllocSafe` therefore also admits a
location some earlier allocation returned, provided `α` maps it to that
allocation's abstract site. Re-allocating it is then harmless when the
allocator's result determines the abstract site (`CrossSpec.allocC_site`). -/

/-- Every location `α` maps is in use in `h`, a literal location, or a location
    some allocation returns, mapped to that allocation's abstract site. -/
def AlphaFn.AllocSafe [Concrete] [Abstract] (α : AlphaFn) (h : Heap) : Prop :=
  ∀ l al, α l = some al →
    h.Defined l ∨ (∃ v, l = Concrete.litLoc v) ∨
    ∃ (h₀ : Heap) (κ : Idx), h₀.Finite ∧ Concrete.allocC h₀ κ = l ∧
      al = Abstract.allocA AHeap.bot κ

/-- `AllocSafe` survives any heap change that keeps every in-use location in
    use. -/
theorem AlphaFn.AllocSafe.mono_heap [Concrete] [Abstract] {α : AlphaFn} {h h' : Heap}
    (k : α.AllocSafe h) (hd : ∀ l, h.Defined l → h'.Defined l) : α.AllocSafe h' := by
  intro l al hl
  rcases k l al hl with hdef | hrest
  · exact Or.inl (hd l hdef)
  · exact Or.inr hrest

theorem AlphaFn.Lits.mono [Concrete] [Abstract] {α α' : AlphaFn} (he : α' ≥α α)
    (k : α.Lits) : α'.Lits :=
  fun v => he _ _ (k v)

/-! ## Assumptions relating the concrete and abstract parameters

Beyond `ConcreteSpec` and `AbstractSpec`, which each constrain one side, the
soundness proof needs the two sides' binary operators and allocators to
agree, and two further facts about the concrete parameters that the query
development has no use for (kept here rather than in `ConcreteSpec` so that
the run-record theorems of `CoreJsSemantics.lean` (`BigStep.obs_wf`, …) do
not acquire hypotheses they never use). -/

structure CrossSpec [Concrete] [Abstract] : Prop where
  /-- `⊕̂` soundly over-approximates `⊕`. -/
  opSem_sound : ∀ op v₁ v₂ (V₁ V₂ : VSet), V₁.Mem v₁ → V₂.Mem v₂ →
    (Abstract.opSemA op V₁ V₂).Mem (Concrete.opSem op v₁ v₂)
  /-- Binary operators never produce a function value, so a function value
      lives only at its own literal location (`Heap.FidCanon`). -/
  opSem_fid : ∀ op v₁ v₂ f, Concrete.opSem op v₁ v₂ ≠ .fid f
  /-- An allocation never returns a literal location. -/
  allocC_lit : ∀ h κ v, h.Finite → Concrete.allocC h κ ≠ Concrete.litLoc v
  /-- Two allocations that return the same location have the same abstract
      site: re-allocating a location (possible after an object literal with
      no fields, which leaves its location unused) never needs `α` to
      re-map it. -/
  allocC_site : ∀ (h h' : Heap) κ κ' (ah ah' : AHeap), h.Finite → h'.Finite →
    Concrete.allocC h κ = Concrete.allocC h' κ' → Abstract.allocA ah κ = Abstract.allocA ah' κ'

/-- Extending `α` at a fresh allocation: `α` is extended (or already agrees)
    to map the allocated location to its abstract site, and stays
    allocation-safe for any heap that keeps in use what the current one does. -/
theorem AlphaFn.AllocSafe.extend [Concrete] [Abstract] (cspec : ConcreteSpec)
    (xspec : CrossSpec) {α : AlphaFn} {h : Heap} (k : α.AllocSafe h) (hfin : h.Finite)
    (κ : Idx) (ah : AHeap) :
    ∃ α', α' ≥α α ∧ α' (Concrete.allocC h κ) = some (Abstract.allocA ah κ) ∧
      ∀ h' : Heap, (∀ l, h.Defined l → h'.Defined l) → α'.AllocSafe h' := by
  let l := Concrete.allocC h κ
  let α' : AlphaFn := fun l' => if l' = l then some (Abstract.allocA ah κ) else α l'
  have hsite : Abstract.allocA AHeap.bot κ = Abstract.allocA ah κ :=
    xspec.allocC_site h h κ κ _ _ hfin hfin rfl
  refine ⟨α', ?_, if_pos rfl, ?_⟩
  · intro l' al hl'
    by_cases e : l' = l
    · subst e
      simp only [α', if_pos]
      rcases k _ al hl' with hdef | ⟨v, hv⟩ | ⟨h₀, κ₀, hfin₀, hl₀, hal⟩
      · exact absurd hdef (Heap.not_defined_of_fresh (cspec.allocC_fresh h κ hfin))
      · exact absurd hv (xspec.allocC_lit h κ v hfin)
      · rw [hal]
        exact congrArg some (xspec.allocC_site h₀ h κ₀ κ AHeap.bot ah hfin₀ hfin hl₀).symm
    · simpa [α', e] using hl'
  · intro h' hd l' al hl'
    by_cases e : l' = l
    · subst e
      simp only [α', if_pos, Option.some.injEq] at hl'
      exact Or.inr (Or.inr ⟨h, κ, hfin, rfl, hl' ▸ hsite.symm⟩)
    · have : α l' = some al := by simpa [α', e] using hl'
      rcases k l' al this with hdef | hrest
      · exact Or.inl (hd l' hdef)
      · exact Or.inr hrest

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

theorem AlphaFn.lits_allocSafe [Concrete] [Abstract] (h : Heap) :
    (AlphaFn.lits : AlphaFn).AllocSafe h := by
  intro l al hl
  by_cases e : ∃ v, Concrete.litLoc v = l
  · obtain ⟨v, hv⟩ := e
    exact Or.inr (Or.inl ⟨v, hv.symm⟩)
  · simp [AlphaFn.lits, e] at hl

/-- The initial configuration of a run relates to the initial abstract
    configuration. -/
theorem AConf.Alpha.init [Concrete] [Abstract] (cspec : ConcreteSpec) (s : Stmt) :
    AConf.Alpha AlphaFn.lits (Conf.init s) (AConf.init s) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro l p l' h; exact absurd h (by simp [Conf.init, Heap.init])
  rotate_left
  · intro x l h; exact absurd h (by simp [Conf.init, Sto.empty])
  · intro l₁ l₂ h; exact (h : False).elim
  · intro l h; exact (h : False).elim
  · intro l h; exact (h : False).elim
  intro l v hl
  have hl' : (Val.undef :: s.lits).find? (fun w => Concrete.litLoc w == l) = some v := hl
  have hmem := List.mem_of_find?_eq_some hl'
  have hp := List.find?_some hl'
  simp only [beq_iff_eq] at hp
  subst hp
  exact ⟨Abstract.litLocA v, AlphaFn.lits_lits cspec v, hmem, rfl⟩

/-! ## Actions and traces

The abstraction relation extended pointwise to trace actions, and then to
traces: a concrete trace relates to a list of abstract actions when both
have the same length and their actions relate position by position. A
callee position relates exactly (`α lf = some alf`), since the abstract
action names a single location there. -/

def Act.Alpha (α : AlphaFn) : Act → AAct → Prop
  | .lookup l₁ l₂ l₃, .lookup L₁ L₂ L₃ =>
      α.MapsInto l₁ L₁ ∧ α.MapsInto l₂ L₂ ∧ α.MapsInto l₃ L₃
  | .update l₁ l₂ l₃, .update L₁ L₂ L₃ =>
      α.MapsInto l₁ L₁ ∧ α.MapsInto l₂ L₂ ∧ α.MapsInto l₃ L₃
  | .call lf ls, .call alf Ls => α lf = some alf ∧ LocsAlpha α ls Ls
  | .ret lf l, .ret alf L     => α lf = some alf ∧ α.MapsInto l L
  | _, _                      => False

theorem Act.Alpha.mono {α α' : AlphaFn} (he : α' ≥α α) :
    ∀ {a : Act} {A : AAct}, Act.Alpha α a A → Act.Alpha α' a A
  | .lookup _ _ _, .lookup _ _ _, k => ⟨k.1.mono he, k.2.1.mono he, k.2.2.mono he⟩
  | .update _ _ _, .update _ _ _, k => ⟨k.1.mono he, k.2.1.mono he, k.2.2.mono he⟩
  | .call _ _,     .call _ _,     k => ⟨he _ _ k.1, k.2.mono he⟩
  | .ret _ _,      .ret _ _,      k => ⟨he _ _ k.1, k.2.mono he⟩

/-- Position-by-position relation of concrete to abstract action lists. -/
def ActsAlpha (α : AlphaFn) : List Act → List AAct → Prop
  | [],      []      => True
  | a :: as, A :: As => Act.Alpha α a A ∧ ActsAlpha α as As
  | _,       _       => False

theorem ActsAlpha.mono {α α' : AlphaFn} (he : α' ≥α α) :
    ∀ {as : List Act} {As : List AAct}, ActsAlpha α as As → ActsAlpha α' as As
  | [],      [],      _ => trivial
  | _ :: _,  _ :: _,  k => ⟨k.1.mono he, ActsAlpha.mono he k.2⟩

theorem ActsAlpha.append {α : AlphaFn} :
    ∀ {as₁ as₂ : List Act} {As₁ As₂ : List AAct},
      ActsAlpha α as₁ As₁ → ActsAlpha α as₂ As₂ → ActsAlpha α (as₁ ++ as₂) (As₁ ++ As₂)
  | [],      _, [],      _, _,  k₂ => k₂
  | _ :: _,  _, _ :: _,  _, k₁, k₂ => ⟨k₁.1, ActsAlpha.append k₁.2 k₂⟩

/-- A concrete trace relates to a list of abstract actions. -/
def Trc.Alpha (α : AlphaFn) (t : Trc) (As : List AAct) : Prop :=
  ActsAlpha α t.toList As

theorem Trc.Alpha.mono {α α' : AlphaFn} (he : α' ≥α α) {t : Trc} {As : List AAct}
    (k : Trc.Alpha α t As) : Trc.Alpha α' t As :=
  ActsAlpha.mono he k

theorem Trc.Alpha.seq {α : AlphaFn} {t₁ t₂ : Trc} {As₁ As₂ : List AAct}
    (k₁ : Trc.Alpha α t₁ As₁) (k₂ : Trc.Alpha α t₂ As₂) :
    Trc.Alpha α (.seq t₁ t₂) (As₁ ++ As₂) :=
  ActsAlpha.append k₁ k₂

end CoreJS
