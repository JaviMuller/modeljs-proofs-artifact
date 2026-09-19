/-
  # Core JavaScript — Concrete Runs as Execution Records

  Bridge between the concrete semantics (`CoreJsSemantics.lean`) and the
  query semantics (`CoreJsQuerySemantics.lean`): the final configuration of a
  `BigStep` run yields an execution record (`Exec.ofRes`), and that record's
  observation is well formed (`Obs.WF`) — provided the initial configuration
  satisfies the dependency invariant `Reg.DepInv` (which holds, e.g., when the
  initial `dep` is empty).

  The proof rests on one invariant of `(heap, reg)` pairs:

  * `dep` is transitive, and
  * every location that some location depends on holds a value.

  The second conjunct is what makes `[Binary Operation]` preserve the first:
  the freshly allocated location holds no value (`allocC_fresh`, which needs
  the current heap to be finite, `Heap.Finite`; finiteness is itself
  preserved by every rule, `BigStep.finite`), so it occurs in no dependency
  set, and giving it a dependency set cannot break the transitivity of
  another location's.

  Plain Lean 4 — no Mathlib required.
-/

import CoreJsQuerySemantics

namespace CoreJS

/-- The observation of a concrete run is well formed as soon as `dep` is
    transitive: `ac` is closed under reverse dependency by construction. -/
theorem Obs.WF.ofRun_of_trans {h : Heap} {δ : Reg}
    (htrans : ∀ l₁ l₂ l₃, δ.dep l₁ l₂ → δ.dep l₂ l₃ → δ.dep l₁ l₃) :
    (Obs.ofRun h δ).WF where
  dep_trans := htrans
  ac_closed := by
    intro l₁ l₂ h₂₁ hac
    rcases hac with hac | ⟨l', hl', h₁'⟩
    · exact Or.inr ⟨l₁, hac, h₂₁⟩
    · exact Or.inr ⟨l', hl', htrans _ _ _ h₂₁ h₁'⟩

/-- The execution record of a concrete run. -/
def Exec.ofRes (r : Res) : Exec :=
  ⟨r.trc, Obs.ofRun r.heap r.reg⟩

/-! ## The dependency invariant -/

/-- `dep` is transitive, and every location depended upon holds a value. -/
structure Reg.DepInv (h : Heap) (δ : Reg) : Prop where
  trans   : ∀ l₁ l₂ l₃, δ.dep l₁ l₂ → δ.dep l₂ l₃ → δ.dep l₁ l₃
  defined : ∀ l₁ l₂, δ.dep l₁ l₂ → h.val l₂ ≠ none

/-- An empty `dep` satisfies the invariant. -/
theorem Reg.DepInv.of_empty {h : Heap} {δ : Reg} (hd : ∀ l₁ l₂, ¬ δ.dep l₁ l₂) :
    Reg.DepInv h δ where
  trans   := fun l₁ l₂ _ h₁₂ _ => absurd h₁₂ (hd l₁ l₂)
  defined := fun l₁ l₂ h₁₂ => absurd h₁₂ (hd l₁ l₂)

/-- The invariant only depends on the heap's `val` and the register's `dep`. -/
theorem Reg.DepInv.congr {h h' : Heap} {δ δ' : Reg} (hI : Reg.DepInv h δ)
    (hv : h'.val = h.val) (hd : δ'.dep = δ.dep) : Reg.DepInv h' δ' where
  trans   := by rw [hd]; exact hI.trans
  defined := by rw [hd, hv]; exact hI.defined

theorem Reg.setDep_self (δ : Reg) (l : Loc) (d : LocSet) : (δ.setDep l d).dep l = d := by
  simp [Reg.setDep]

theorem Reg.setDep_ne (δ : Reg) {a l : Loc} (d : LocSet) (h : a ≠ l) :
    (δ.setDep l d).dep a = δ.dep a := by
  simp [Reg.setDep, h]

theorem Heap.setObjs_val (h : Heap) (l : Loc) (ps : List (PropName × Loc)) :
    (h.setObjs l ps).val = h.val := by
  induction ps generalizing h with
  | nil => rfl
  | cons p ps ih => exact ih _

theorem Heap.setVal_defined {h : Heap} {l x : Loc} {v : Val} (hx : h.val x ≠ none) :
    (h.setVal l v).val x ≠ none := by
  by_cases e : x = l
  · simp [Heap.setVal, e]
  · simpa [Heap.setVal, e] using hx

/-- Membership in the dependency set built by `[Binary Operation]`. -/
theorem mem_binOpDep {δ : Reg} {l₁ l₂ l' : Loc} :
    (δ.dep l₁ ∪ δ.dep l₂ ∪ {l₁, l₂}) l' ↔
      δ.dep l₁ l' ∨ δ.dep l₂ l' ∨ l' = l₁ ∨ l' = l₂ := by
  show (δ.dep l₁ l' ∨ δ.dep l₂ l') ∨ (l' = l₁ ∨ l' = l₂) ↔ _
  constructor
  · rintro ((h | h) | h | h) <;> simp [h]
  · rintro (h | h | h | h) <;> simp [h]

/-- `[Binary Operation]` preserves the invariant. -/
theorem Reg.DepInv.binOp {h : Heap} {δ : Reg} {l l₁ l₂ : Loc} {v : Val}
    (hI : Reg.DepInv h δ) (hl : h.val l = none)
    (hl₁ : h.val l₁ ≠ none) (hl₂ : h.val l₂ ≠ none) :
    Reg.DepInv (h.setVal l v) (δ.setDep l (δ.dep l₁ ∪ δ.dep l₂ ∪ {l₁, l₂})) := by
  -- every member of the new dependency set holds a value, so is not `l`
  have hdef : ∀ x, (δ.dep l₁ ∪ δ.dep l₂ ∪ {l₁, l₂}) x → h.val x ≠ none := by
    intro x hx
    rcases mem_binOpDep.1 hx with hx | hx | rfl | rfl
    · exact hI.defined _ _ hx
    · exact hI.defined _ _ hx
    · exact hl₁
    · exact hl₂
  have hne : ∀ x, (δ.dep l₁ ∪ δ.dep l₂ ∪ {l₁, l₂}) x → x ≠ l := by
    intro x hx e
    exact hdef x hx (e ▸ hl)
  have hne' : ∀ a b, δ.dep a b → b ≠ l := by
    intro a b hab e
    exact hI.defined a b hab (e ▸ hl)
  constructor
  · intro a b c hab hbc
    by_cases ea : a = l
    · subst ea
      rw [Reg.setDep_self] at hab ⊢
      rw [Reg.setDep_ne _ _ (hne _ hab)] at hbc
      rcases mem_binOpDep.1 hab with h₁ | h₁ | rfl | rfl
      · exact mem_binOpDep.2 (Or.inl (hI.trans _ _ _ h₁ hbc))
      · exact mem_binOpDep.2 (Or.inr (Or.inl (hI.trans _ _ _ h₁ hbc)))
      · exact mem_binOpDep.2 (Or.inl hbc)
      · exact mem_binOpDep.2 (Or.inr (Or.inl hbc))
    · rw [Reg.setDep_ne _ _ ea] at hab ⊢
      rw [Reg.setDep_ne _ _ (hne' _ _ hab)] at hbc
      exact hI.trans _ _ _ hab hbc
  · intro a b hab
    by_cases ea : a = l
    · subst ea
      rw [Reg.setDep_self] at hab
      exact Heap.setVal_defined (hdef _ hab)
    · rw [Reg.setDep_ne _ _ ea] at hab
      exact Heap.setVal_defined (hI.defined _ _ hab)

/-- `[Object Initialization]` preserves the invariant. -/
theorem Reg.DepInv.objLit {h h' : Heap} {δ : Reg} {l : Loc}
    (hI : Reg.DepInv h δ) (hl : h.val l = none) (hv : h'.val = h.val) :
    Reg.DepInv h' (δ.setDep l ∅) := by
  have hne' : ∀ a b, δ.dep a b → b ≠ l := by
    intro a b hab e
    exact hI.defined a b hab (e ▸ hl)
  constructor
  · intro a b c hab hbc
    by_cases ea : a = l
    · subst ea
      rw [Reg.setDep_self] at hab
      exact absurd hab id
    · rw [Reg.setDep_ne _ _ ea] at hab ⊢
      rw [Reg.setDep_ne _ _ (hne' _ _ hab)] at hbc
      exact hI.trans _ _ _ hab hbc
  · intro a b hab
    by_cases ea : a = l
    · subst ea
      rw [Reg.setDep_self] at hab
      exact absurd hab id
    · rw [Reg.setDep_ne _ _ ea] at hab
      rw [hv]
      exact hI.defined _ _ hab

/-- Every rule of the concrete semantics preserves the invariant, on finite
    heaps. -/
theorem BigStep.depInv [Concrete] (hs : ConcreteSpec) {Γ : Env} {c : Conf} {s : Stmt}
    {r : Res} (hb : BigStep Γ c s r) :
    c.heap.Finite → Reg.DepInv c.heap c.reg → Reg.DepInv r.heap r.reg := by
  induction hb with
  | skip => exact fun _ => id
  | assign _ _ => exact fun _ => id
  | @binOp h h' ρ ρ' δ δ' x κ op e₁ e₂ l₁ l₂ v₁ v₂ l v d _ _ hv₁ hv₂ hl _ hh' _ hd hδ' =>
    intro hF hI
    subst hh' hd hδ'
    have hfr : h.val l = none := hl ▸ (hs.allocC_fresh h κ hF).1
    exact hI.binOp hfr (by simp [hv₁]) (by simp [hv₂])
  | @objLit h h' ρ ρ' δ δ' x κ fs ls l _ hl hh' _ hδ' =>
    intro hF hI
    subst hh' hδ'
    have hfr : h.val l = none := hl ▸ (hs.allocC_fresh h κ hF).1
    exact hI.objLit hfr (Heap.setObjs_val _ _ _)
  | lookupS _ _ _ => exact fun _ => id
  | lookupD _ _ _ _ _ => exact fun _ => id
  | updateS _ _ hh' => intro _ hI; subst hh'; exact hI.congr rfl rfl
  | updateD _ _ _ _ hh' => intro _ hI; subst hh'; exact hI.congr rfl rfl
  | seqRet _ ih => exact ih
  | seqCont hb₁ _ ih₁ ih₂ => exact fun hF hI => ih₂ (hb₁.finite hF) (ih₁ hF hI)
  | callRet _ _ _ _ _ _ _ ih => exact ih
  | callCont _ _ _ _ _ _ _ ih => exact ih
  | ifTrue _ _ _ ih => exact ih
  | ifFalse _ _ _ ih => exact ih
  | whileDo _ ih => exact ih
  | ret _ => exact fun _ => id
  | setTaint _ hδ' => intro _ hI; subst hδ'; exact hI.congr rfl rfl
  | setSink _ hδ' => intro _ hI; subst hδ'; exact hI.congr rfl rfl

/-- **Bridge.**  The execution record of a concrete run has a well-formed
    observation, provided the initial configuration satisfies the invariant
    (for instance, an empty initial `dep`). -/
theorem BigStep.obs_wf [Concrete] (hs : ConcreteSpec) {Γ : Env} {c : Conf} {s : Stmt}
    {r : Res} (hb : BigStep Γ c s r) (hF : c.heap.Finite) (hI : Reg.DepInv c.heap c.reg) :
    (Exec.ofRes r).obs.WF :=
  Obs.WF.ofRun_of_trans (hb.depInv hs hF hI).trans

/-! ## Runs from the initial configuration -/

/-- The empty register satisfies the invariant, for any heap. -/
theorem Reg.DepInv.empty (h : Heap) : Reg.DepInv h Reg.empty :=
  Reg.DepInv.of_empty (fun _ _ hd => hd)

/-- A run that starts from the empty taint register — over *any* finite heap
    and store — has a well-formed observation.  (The heap need not be well
    formed in the sense of `Heap.WF`: `dep` starts empty, and freshness of
    allocation is a property of `allocC` on finite heaps.) -/
theorem BigStep.obs_wf_empty [Concrete] (hs : ConcreteSpec) {Γ : Env} {h : Heap} {ρ : Sto}
    {s : Stmt} {r : Res} (hb : BigStep Γ ⟨h, ρ, Reg.empty⟩ s r) (hF : h.Finite) :
    (Exec.ofRes r).obs.WF :=
  hb.obs_wf hs hF (Reg.DepInv.empty h)

/-- **Initial-configuration bridge.**  Starting from the minimal well-formed
    heap, the empty store and the empty register, a concrete run yields a
    well-formed observation. -/
theorem BigStep.obs_wf_init [Concrete] (hs : ConcreteSpec) {Γ : Env} {s : Stmt} {r : Res}
    (hb : BigStep Γ (Conf.init s) s r) : (Exec.ofRes r).obs.WF :=
  hb.obs_wf_empty hs (Heap.init_finite s)

end CoreJS
