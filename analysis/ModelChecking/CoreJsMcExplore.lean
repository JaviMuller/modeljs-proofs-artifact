/-
  # Core JavaScript — Model checking: exploration with progress

  The generic search underlying model checking: a worklist exploration of the
  states reachable from an initial one, keeping the set of states already
  visited and never expanding a state twice (*progress*).  Proved once, for
  any successor function:

  * `explore` terminates whenever the reachable states lie in some finite list
    closed under successors — the list is only used by the termination
    proof (it is an existential, erased at run time), never enumerated;
  * `mem_explore`: its result contains exactly the reachable states.

  Skipping a visited state loses nothing because successors depend only on
  the state: whatever is reachable from it has been, or will be, explored
  from its first visit.

  Plain Lean 4 — no Mathlib required.
-/

import ModelChecking.CoreJsMcInterface

namespace CoreJS

variable {σ : Type}

/-- `Reach succ x y`: `y` is reachable from `x`. -/
inductive Reach (succ : σ → List σ) (x : σ) : σ → Prop where
  | refl : Reach succ x x
  | step {y z} : Reach succ x y → z ∈ succ y → Reach succ x z

theorem Reach.trans {succ : σ → List σ} {x y z : σ} (h₁ : Reach succ x y)
    (h₂ : Reach succ y z) : Reach succ x z := by
  induction h₂ with
  | refl => exact h₁
  | step _ hz ih => exact .step ih hz

theorem Reach.head {succ : σ → List σ} {x y z : σ} (hy : y ∈ succ x) (h : Reach succ y z) :
    Reach succ x z :=
  (Reach.step .refl hy).trans h

/-- `U` is closed under successors. -/
def SuccClosed (succ : σ → List σ) (U : List σ) : Prop := ∀ x ∈ U, ∀ y ∈ succ x, y ∈ U

/-- Removing one more element from the elements kept by a filter shortens it. -/
theorem filter_length_lt {p q : σ → Bool} :
    ∀ {U : List σ}, (∀ y, q y = true → p y = true) → (∃ y ∈ U, p y = true ∧ q y = false) →
      (U.filter q).length < (U.filter p).length
  | [], _, ⟨_, hy, _⟩ => by simp at hy
  | a :: U, hqp, ⟨y, hy, hp, hq⟩ => by
      have le : ∀ {U : List σ}, (U.filter q).length ≤ (U.filter p).length := by
        intro U
        induction U with
        | nil => simp
        | cons b U ih =>
          simp only [List.filter_cons]
          cases hqb : q b <;> cases hpb : p b <;> simp <;> try omega
          exact absurd (hqp b hqb) (by simp [hpb])
      rcases List.mem_cons.1 hy with rfl | hy
      · simp only [List.filter_cons, hp, hq]
        simp; exact Nat.lt_succ_of_le le
      · have ih := filter_length_lt hqp ⟨y, hy, hp, hq⟩
        simp only [List.filter_cons]
        cases hqa : q a <;> cases hpa : p a <;> simp <;> try omega
        exact absurd (hqp a hqa) (by simp [hpa])

variable [DecidableEq σ]

/-- The exploration loop: `work` remains to be expanded, `visited` has been.
    `hfin` provides a finite list containing the initial state and closed
    under successors; the work list stays inside it (`hw`). -/
def exploreAux (succ : σ → List σ) (init : σ)
    (hfin : ∃ U : List σ, init ∈ U ∧ SuccClosed succ U) :
    (work visited : List σ) → (∀ x ∈ work, x ∈ Classical.choose hfin) → List σ
  | [], visited, _ => visited
  | x :: work, visited, hw =>
      if hx : x ∈ visited then exploreAux succ init hfin work visited
        (fun y hy => hw y (List.mem_cons_of_mem _ hy))
      else exploreAux succ init hfin (succ x ++ work) (x :: visited) (fun y hy => by
        rcases List.mem_append.1 hy with hy | hy
        · exact (Classical.choose_spec hfin).2 x (hw x (List.mem_cons_self ..)) y hy
        · exact hw y (List.mem_cons_of_mem _ hy))
termination_by work visited =>
  (((Classical.choose hfin).filter (fun y => decide (y ∉ visited))).length, work.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · refine Prod.Lex.left _ _ (filter_length_lt (fun y h => ?_)
      ⟨x, hw x (List.mem_cons_self ..), by simp [hx], by simp⟩)
    simp only [decide_eq_true_eq, List.mem_cons, not_or] at h ⊢
    exact h.2

/-- All states reachable from `init`. -/
def explore (succ : σ → List σ) (init : σ)
    (hfin : ∃ U : List σ, init ∈ U ∧ SuccClosed succ U) : List σ :=
  exploreAux succ init hfin [init] [] (fun y hy => by
    rw [List.mem_singleton.1 hy]; exact (Classical.choose_spec hfin).1)

/-- Everything returned was visited already or is reachable from the work list. -/
theorem exploreAux_sound (succ : σ → List σ) (init : σ)
    (hfin : ∃ U : List σ, init ∈ U ∧ SuccClosed succ U) (work visited : List σ)
    (hw : ∀ x ∈ work, x ∈ Classical.choose hfin) (y : σ) :
    y ∈ exploreAux succ init hfin work visited hw →
      y ∈ visited ∨ ∃ w ∈ work, Reach succ w y := by
  induction work, visited, hw using exploreAux.induct succ init hfin with
  | case1 visited hw _ => intro h; rw [exploreAux] at h; exact Or.inl h
  | case2 x work visited hw hx _ ih =>
    intro h
    rw [exploreAux, dif_pos hx] at h
    rcases ih h with h | ⟨w, hw', hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw', hr⟩
  | case3 x work visited hw hx _ ih =>
    intro h
    rw [exploreAux, dif_neg hx] at h
    rcases ih h with h | ⟨w, hw', hr⟩
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr ⟨y, List.mem_cons_self .., .refl⟩
      · exact Or.inl h
    · rcases List.mem_append.1 hw' with hw' | hw'
      · exact Or.inr ⟨x, List.mem_cons_self .., Reach.head hw' hr⟩
      · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw', hr⟩

/-- If every successor of a visited state is visited or still to be expanded,
    the result contains the visited states and the work list, and is closed
    under successors. -/
theorem exploreAux_complete (succ : σ → List σ) (init : σ)
    (hfin : ∃ U : List σ, init ∈ U ∧ SuccClosed succ U) (work visited : List σ)
    (hw : ∀ x ∈ work, x ∈ Classical.choose hfin) :
    (∀ v ∈ visited, ∀ z ∈ succ v, z ∈ visited ∨ z ∈ work) →
      (∀ y ∈ visited, y ∈ exploreAux succ init hfin work visited hw) ∧
      (∀ y ∈ work, y ∈ exploreAux succ init hfin work visited hw) ∧
      SuccClosed succ (exploreAux succ init hfin work visited hw) := by
  induction work, visited, hw using exploreAux.induct succ init hfin with
  | case1 visited hw _ =>
    intro hinv
    rw [exploreAux]
    refine ⟨fun _ h => h, fun _ h => by simp at h, fun v hv z hz => ?_⟩
    rcases hinv v hv z hz with h | h
    · exact h
    · simp at h
  | case2 x work visited hw hx _ ih =>
    intro hinv
    rw [exploreAux, dif_pos hx]
    obtain ⟨h₁, h₂, h₃⟩ := ih (by
      intro v hv z hz
      rcases hinv v hv z hz with h | h
      · exact Or.inl h
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inl hx
        · exact Or.inr h)
    refine ⟨h₁, fun y hy => ?_, h₃⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h₁ y hx
    · exact h₂ y hy
  | case3 x work visited hw hx _ ih =>
    intro hinv
    rw [exploreAux, dif_neg hx]
    obtain ⟨h₁, h₂, h₃⟩ := ih (by
      intro v hv z hz
      rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inr (List.mem_append_left _ hz)
      · rcases hinv v hv z hz with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inl (List.mem_cons_self ..)
          · exact Or.inr (List.mem_append_right _ h))
    refine ⟨fun y hy => h₁ y (List.mem_cons_of_mem _ hy), fun y hy => ?_, h₃⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h₁ y (List.mem_cons_self ..)
    · exact h₂ y (List.mem_append_right _ hy)

/-- **Exploration is exact**: it returns exactly the states reachable from
    `init`. -/
theorem mem_explore (succ : σ → List σ) (init : σ)
    (hfin : ∃ U : List σ, init ∈ U ∧ SuccClosed succ U) (y : σ) :
    y ∈ explore succ init hfin ↔ Reach succ init y := by
  constructor
  · intro h
    rcases exploreAux_sound succ init hfin [init] [] _ y h with h | ⟨w, hw, hr⟩
    · simp at h
    · rw [List.mem_singleton.1 hw] at hr; exact hr
  · have hc := exploreAux_complete succ init hfin [init] [] (fun z hz => by
      rw [List.mem_singleton.1 hz]; exact (Classical.choose_spec hfin).1) (by simp)
    intro h
    induction h with
    | refl => exact hc.2.1 init (List.mem_singleton_self _)
    | step _ hz ih => exact hc.2.2 _ ih _ hz

end CoreJS
