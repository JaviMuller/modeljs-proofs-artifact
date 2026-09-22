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



/-! ### Past operators -/

/-- `Y ⊤` is false at `0`, true at `1` and `2`. -/
theorem fo_yesterday :
    ¬ (Ltl.yesterday .tt : Ltl Var).Sat eTaint.toModel ξt 0 ∧
    (Ltl.yesterday .tt : Ltl Var).Sat eTaint.toModel ξt 1 ∧
    (Ltl.yesterday .tt : Ltl Var).Sat eTaint.toModel ξt 2 := by
  simp only [Ltl.Sat]
  decide

/-- `O(retn(f,r))`: the return, once made, stays "once true" forever after (it does not
    yet hold at `0`, the call's own position). -/
theorem fo_once :
    ¬ (Ltl.O retFr).Sat eTaint.toModel ξt 0 ∧
    (Ltl.O retFr).Sat eTaint.toModel ξt 1 ∧
    (Ltl.O retFr).Sat eTaint.toModel ξt 2 := by
  simp only [Ltl.sat_O, retFr, Ltl.Sat, Atom.Sat, Exec.holds_toModel]
  refine ⟨?_, ⟨1, by decide, by decide⟩, ⟨1, by decide, by decide⟩⟩
  rintro ⟨k, hk, hc⟩
  have : k = 0 := by omega
  subst this
  exact absurd hc (by decide)

/-- `H(¬retn(f,r))`: "no return has happened yet" holds at `0`, fails from `1` on. -/
theorem fo_historically :
    (Ltl.H (.not retFr)).Sat eTaint.toModel ξt 0 ∧
    ¬ (Ltl.H (.not retFr)).Sat eTaint.toModel ξt 1 := by
  simp only [Ltl.sat_H, retFr, Ltl.Sat, Atom.Sat, Exec.holds_toModel]
  constructor
  · intro k hk
    have : k = 0 := by omega
    subst this
    decide
  · intro h; exact (h 1 (by decide)) (by decide)

/-- `atStart(sk(f))` holds at every boundary, reaching back to the start, even nested
    under `X X`. -/
theorem fo_atStart_nested :
    (Ltl.next (Ltl.next (Ltl.atStart (.atom (.sk "f"))))).Holds eTaint.toModel ξt := by
  have h0 : (Ltl.atStart (.atom (.sk "f")) : Ltl Var).Sat eTaint.toModel ξt 0 :=
    Ltl.sat_atStart.2 (by simp [Atom.Sat, Exec.toModel, eTaint, ξt] : (Atom.sk "f").Sat eTaint.toModel ξt 0)
  refine ⟨by decide, by decide, ?_⟩
  exact Ltl.sat_atStart_indep.2 h0

/-- `atStart(¬call(f,[x]))` is false at `0` (the call *does* happen at `0`), matching what
    a query's `except` translation would report for `except Call(f,[x])` at any position. -/
theorem fo_atStart_except_no :
    ¬ (Ltl.atStart (.not callFx)).Holds eTaint.toModel ξt := by
  rw [Ltl.Holds, Ltl.sat_atStart]
  simp only [Ltl.Sat, callFx, Atom.Sat, Exec.holds_toModel]
  decide

end CoreJS.Tests
