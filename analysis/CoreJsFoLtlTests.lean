/-
  # Core JavaScript — FO-LTL Test Suite

  Compile-time tests for `CoreJsFoLtl.lean`.  The model is that of `eTaint`, an
  explicit execution record with the trace and the relevant observation facts of
  the run of `pTaint` (`CoreJsQueryTests.lean`): trace `[call 204 [1100], ret 204 0]`,
  hence two states and boundaries `0, 1, 2` (`2` being the sentinel).
  `link_eTaint` ties the explicit record to the real run.  Formulas are over string
  variables, valued by `ξt`: `f ↦ 204` (the sink), `x ↦ 1100`, `r ↦ 0`.

  Plain Lean 4 — no Mathlib required.
-/

import CoreJsQueryTests
import CoreJsFoLtl

namespace CoreJS.Tests

open CoreJS

/-- The explicit record: two actions; `204` is a sink; `15` and `1100` are attacker-controlled. -/
def eTaint : Exec where
  trc := .act (.call 204 [1100]) ;; .act (.ret 204 0)
  obs := ⟨fun _ => none, fun _ => ∅, fun l => l = 15 ∨ l = 1100, fun l => l = 204⟩

/-- `eTaint` is the record of the run of `pTaint`, as far as trace and sinks go. -/
theorem link_eTaint : Runs pTaint fun r =>
    (Exec.ofRes r).trc.toList = eTaint.trc.toList ∧
    ∀ l, (Exec.ofRes r).obs.sk l ↔ eTaint.obs.sk l := by
  run refine ⟨rfl, fun l => ?_⟩
      have h204 : Concrete.litLoc (Val.fid "sink") = 204 := rfl
      simp +decide [Exec.ofRes, Obs.ofRun, eTaint, Reg.empty, Reg.setDep, h204]

def ξt : Var → Loc := fun v => if v = "f" then 204 else if v = "x" then 1100 else 0

def callFx : Ltl Var := .atom (.call "f" ["x"])
def retFr  : Ltl Var := .atom (.retn "f" "r")

/-- Two states, hence boundaries `0, 1, 2`. -/
theorem len_eTaint : eTaint.toModel.len = 2 := by
  rw [Exec.toModel_len]; rfl

/-- `A₁ ; A₂ ≡ F(A₁ ∧ X F A₂)`: the call happens, and the return strictly after it. -/
theorem fo_seq :
    (Ltl.F (.and callFx (.next (Ltl.F retFr)))).Holds eTaint.toModel ξt := by
  simp only [Ltl.Holds, Ltl.sat_F, Ltl.Sat, callFx, retFr, Atom.Sat, Exec.holds_toModel,
    Exec.toModel_len]
  exact ⟨0, Nat.le_refl _, by decide, by decide, by decide, 1, by decide, by decide, by decide⟩

/-- ... and not the other way round: there is no call after the return. -/
theorem fo_seq_rev_no :
    ¬ (Ltl.F (.and retFr (.next (Ltl.F callFx)))).Holds eTaint.toModel ξt := by
  simp only [Ltl.Holds, Ltl.sat_F, Ltl.Sat, callFx, retFr, Atom.Sat, Exec.holds_toModel,
    Exec.toModel_len]
  rintro ⟨k, _, hk, h₁, _, k', h₂, h₃, h₄⟩
  have hlen : eTaint.trc.toList.length = 2 := rfl
  rw [hlen] at hk h₃
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  all_goals obtain rfl | rfl | rfl : k' = 0 ∨ k' = 1 ∨ k' = 2 := by omega
  all_goals revert h₁ h₂ h₄; decide

/-- `X` is strong and boundary `n` is a sentinel: `X X ⊤` holds at `0`, `X X X ⊤` does not. -/
theorem fo_sentinel :
    (Ltl.next (Ltl.next .tt) : Ltl Var).Holds eTaint.toModel ξt ∧
    ¬ (Ltl.next (Ltl.next (Ltl.next .tt)) : Ltl Var).Holds eTaint.toModel ξt := by
  simp only [Ltl.Holds, Ltl.Sat, Exec.toModel_len]
  decide

/-- No action holds at the sentinel: `F(a ∧ X ⊤)` and `F a` agree. -/
theorem fo_action_next :
    (Ltl.F (.and callFx (.next .tt))).Holds eTaint.toModel ξt ↔
    (Ltl.F callFx).Holds eTaint.toModel ξt :=
  Ltl.sat_F_action_next (by simp [Atom.IsAction] : (Atom.call "f" ["x"]).IsAction)

/-- State atoms hold at every boundary or none: `G sk(f) ≡ sk(f) ≡ F sk(f)`. -/
theorem fo_state_always :
    (Ltl.G (.atom (.sk "f"))).Holds eTaint.toModel ξt ∧
    (Ltl.F (.atom (.sk "f"))).Holds eTaint.toModel ξt := by
  have hs : eTaint.toModel.obs.sk (ξt "f") := by
    simp [Exec.toModel, eTaint, ξt]
  exact ⟨(Ltl.sat_G_state (by simp [Atom.IsAction]) (Nat.zero_le _)).2 hs,
         (Ltl.sat_F_state (by simp [Atom.IsAction]) (Nat.zero_le _)).2 hs⟩

/-- Attacker control is a state atom too, and `¬ac(f)` is stable. -/
theorem fo_ac :
    (Ltl.G (.atom (.ac "x"))).Holds eTaint.toModel ξt ∧
    (Ltl.G (.not (.atom (.ac "f")))).Holds eTaint.toModel ξt := by
  refine ⟨(Ltl.sat_G_state (by simp [Atom.IsAction]) (Nat.zero_le _)).2 ?_, ?_⟩
  · simp [Atom.Sat, Exec.toModel, eTaint, ξt]
  · rw [Ltl.Holds, Ltl.sat_G]
    intro k _ _
    simp [Ltl.Sat, Atom.Sat, Exec.toModel, eTaint, ξt]

/-- Rigid quantification: `∃x. ∃r. F(call(f,[x]) ∧ X F retn(f,r))`, witnessed by the
    locations of the trace. -/
theorem fo_exists :
    (Ltl.ex "x" (Ltl.ex "r" (Ltl.F (.and callFx (.next (Ltl.F retFr)))))).Holds
      eTaint.toModel ξt := by
  refine ⟨1100, 0, ?_⟩
  simp only [Ltl.sat_F, Ltl.Sat, callFx, retFr, Atom.Sat, Exec.holds_toModel,
    Exec.toModel_len, upd]
  exact ⟨0, Nat.le_refl _, by decide, by decide, by decide, 1, by decide, by decide, by decide⟩

/-- Multiple actions cannot happen at the same time: the model satisfies the exclusivity
    formula (for any set of shapes, here those used above). -/
theorem fo_excl :
    (Ltl.excl (fun k => s!"v{k}") [.call 1, .retn, .lookup, .update]).Holds eTaint.toModel ξt :=
  Exec.toModel_sat_excl _ _ _ _

end CoreJS.Tests
