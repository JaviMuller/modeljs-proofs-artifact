/-
  # Core JavaScript — Model checking: tests

  The algorithm of `CoreJsMcAlgorithm.lean` run, at compile time, on a toy
  finite trace system and abstraction: four abstract locations, abstract
  actions with explicit location lists, facts given as lists.  The toy
  abstraction has no concrete side (it only exercises the search); `sv`/`hv`
  are always possible since it records no values.

  The program reads `call 0([1])` then `ret 0(2)`.  The query of the reported
  issue,

  ```
  Query Q(f, x, y) { ∃z: Call(f, [x]) ; Retn(f, y)
                     when sv(x, y) ∧ dep(x, z) ∧ dep(y, z) ∧ ac(z) }
  ```

  has `z` in no action, only in the invariant: it is constrained from the
  start like every variable, so the result depends on the facts about `z`.
  Likewise `∃z: ε when ac(z)` holds only if some location is tainted.

  `except`s are tested with `R(f) { ∃r: Retn(f, r) except C(f) }`, `C`
  calling `f`: a call that certainly happens excludes the match, one that
  only may happen does not, and a loop of calls that can be skipped keeps the
  witness of the walk skipping it (the trackers tell the two walks apart).
  The toy must-matching asks for single-location positions.

  Plain Lean 4 — no Mathlib required.
-/

import ModelChecking.CoreJsMcAlgorithm

namespace CoreJS.McTests

/-- Toy abstract locations and values (`none`: a location nothing is known of). -/
abbrev TLoc := Fin 4
abbrev TV := Option TLoc

/-- Toy abstract actions. -/
inductive TAct where
  | call (f : TLoc) (args : List (List TLoc))
  | ret  (f : TLoc) (L : List TLoc)
  deriving DecidableEq

/-- Toy facts. -/
structure TFacts where
  dep : List (TLoc × TLoc)
  ac  : List TLoc
  sk  : List TLoc

def inL (L : List TLoc) : TV → Bool
  | some l => L.contains l
  | none   => false

def tsep : QAct MVar → TAct → Option (List (MVar × (TV → Bool)))
  | .call xf xs, .call f Ls =>
      if xs.length = Ls.length then
        some ((xf, fun v => v == some f) :: (xs.zip Ls).map fun p => (p.1, inL p.2))
      else none
  | .retn xf x,  .ret f L   => some [(xf, fun v => v == some f), (x, inL L)]
  | _,           _          => none

def tmay (φ : TFacts) (ξ : MVar → TV) : Pred MVar → Bool
  | .ac x      => match ξ x with
    | some l => φ.ac.contains l || φ.ac.any fun l' => φ.dep.contains (l, l')
    | none   => false
  | .dep x y   => match ξ x, ξ y with
    | some a, some b => φ.dep.contains (a, b)
    | _,      _      => false
  | .sk x      => match ξ x with
    | some l => φ.sk.contains l
    | none   => false
  | .sv _ _    => true
  | .hv _ _    => true

/-- Must-matching: the callee is the function, every argument position a single
    location equal to the variable's value. -/
def inOne (L : List TLoc) (v : TV) : Bool :=
  match L with
  | [l] => v == some l
  | _   => false

def tmustA (ξ : MVar → TV) : QAct MVar → TAct → Bool
  | .call xf xs, .call f Ls =>
      ξ xf == some f && xs.length == Ls.length && (xs.zip Ls).all fun p => inOne p.2 (ξ p.1)
  | .retn xf x,  .ret f L   => ξ xf == some f && inOne L (ξ x)
  | _,           _          => false

def tAbs : Abs TAct TV TFacts where
  act _ _ _   := True
  facts _ _ _ := True
  matchA ξ b B := match tsep b B with
    | none    => false
    | some cs => cs.all fun c => c.2 (ξ c.1)
  may  := tmay
  must _ _ _ := false
  mustA := tmustA
  inhab _ v := v.isSome

def tSep : tAbs.Sep where
  sep := tsep
  spec ξ b B := by
    simp only [tAbs]
    cases tsep b B <;> simp [List.all_eq_true]
  vars b B cs h := by
    cases b <;> cases B <;> simp only [tsep] at h
    all_goals first | (simp at h) | skip
    · obtain ⟨_, rfl⟩ := h
      intro c hc
      simp only [List.mem_cons, List.mem_map] at hc
      rcases hc with rfl | ⟨⟨x, L⟩, hx, rfl⟩
      · simp [QAct.vars]
      · exact List.mem_cons_of_mem _ (List.of_mem_zip hx).1
    · cases h; intro c hc; simp at hc; rcases hc with rfl | rfl <;> simp [QAct.vars]

/-- The program: `call 0([1])`, then `ret 0(2)`. -/
def prog : FinTSys TAct where
  St     := Nat
  deq    := inferInstance
  init   := 0
  final s := s == 2
  succ
    | 0 => [(some (.call 0 [[1]]), 1)]
    | 1 => [(some (.ret 0 [2]), 2)]
    | _ => []
  finite := ⟨[0, 1, 2], by decide, by
    intro s hs e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> simp at he <;> subst he <;> decide⟩

def vals : List TV := [none, some 0, some 1, some 2, some 3]

/-- Model checking `q`, invoking queries of `Δ`, against `P` with facts `φ`. -/
def checkIn (P : FinTSys TAct) (q : Query) (Δ : QProg) (hwf : QProg.WF (q :: Δ)) (φ : TFacts) :
    List (P.St × QSt × (MVar → TV)) :=
  witnesses P (q.toQModel Δ).main (nonrel vals (q.toQModel Δ).main.labelVars tAbs φ tSep)
    (enumTracker tAbs φ (q.toQModel Δ) vals (q.toQModel Δ).compVars)
    (Query.toQModel_wf hwf).1 (nonrel_finite vals _ tAbs φ tSep)
    enumTracker_finite

/-- Model checking `q` (without invocations) against `prog` with facts `φ`. -/
def check (q : Query) (hwf : QProg.WF [q]) (φ : TFacts) : List (Nat × QSt × (MVar → TV)) :=
  checkIn prog q [] hwf φ

/-! ## The reported issue: `z` occurs only in the invariant -/

def qIssue : Query :=
  { name := "Q", params := ["f", "x", "y"],
    body := { locals := ["z"],
              pattern := .seq (.act (.call "f" ["x"])) (.act (.retn "f" "y")),
              when := .and (.pred (.sv "x" "y")) (.and (.pred (.dep "x" "z"))
                (.and (.pred (.dep "y" "z")) (.pred (.ac "z")))) } }

theorem qIssue_wf : QProg.WF [qIssue] :=
  ⟨⟨⟨by decide, by decide⟩, by simp [Query.CallsOK, QBody.calls, qIssue, Pat.calls]⟩, rfl, trivial⟩

/-- `1` and `2` both depend on the tainted `3`. -/
def φGood : TFacts := { dep := [(1, 3), (2, 3)], ac := [3], sk := [] }
/-- Nothing is tainted. -/
def φNoTaint : TFacts := { dep := [(1, 3), (2, 3)], ac := [], sk := [] }
/-- `2` depends on nothing. -/
def φNoDep : TFacts := { dep := [(1, 3)], ac := [3], sk := [] }

-- A witness, with `z` bound to the tainted location both arguments depend on.
#guard (check qIssue qIssue_wf φGood).any fun w =>
  w.2.2 (.src "f") == some 0 && w.2.2 (.src "x") == some 1 && w.2.2 (.src "y") == some 2 &&
    w.2.2 (.src "z") == some 3
-- No tainted location: `z` has no possible value, no witness.
#guard (check qIssue qIssue_wf φNoTaint).isEmpty
-- `y` depends on nothing: no `z` satisfies `dep(y, z)`, no witness.
#guard (check qIssue qIssue_wf φNoDep).isEmpty

/-! ## `∃z. ac(z)`, with `z` in no action -/

def qSomeTaint : Query :=
  { name := "T", params := [],
    body := { locals := ["z"], pattern := .eps, when := .pred (.ac "z") } }

theorem qSomeTaint_wf : QProg.WF [qSomeTaint] :=
  ⟨⟨⟨by decide, by decide⟩, by simp [Query.CallsOK, QBody.calls, qSomeTaint, Pat.calls]⟩, rfl, trivial⟩

#guard !(check qSomeTaint qSomeTaint_wf φGood).isEmpty
#guard (check qSomeTaint qSomeTaint_wf φNoTaint).isEmpty

/-! ## `except`, checked along the walk by the trackers

`R(f) { ∃r: Retn(f, r) except C(f) }` with `C(f) { ∃a: Call(f, [a]) }`:
`f` returns without having been called.  The local `a` of `C` is bound inside
the `except`; the toy abstraction must-matches a call whose argument position
is a single location. -/

def qC : Query :=
  { name := "C", params := ["f"],
    body := { locals := ["a"], pattern := .act (.call "f" ["a"]) } }

def qR : Query :=
  { name := "R", params := ["f"],
    body := { locals := ["r"], pattern := .act (.retn "f" "r"), except := some (.query "C" ["f"]) } }

/-- The same without the `except`. -/
def qRpos : Query := { qR with body := { qR.body with except := none } }

theorem qR_wf : QProg.WF [qR, qC] :=
  ⟨⟨⟨by decide, by decide⟩, by simp [Query.CallsOK, QBody.calls, qR, qC, Pat.calls, QProg.find?]⟩,
    by decide, ⟨⟨by decide, by decide⟩, by simp [Query.CallsOK, QBody.calls, qC, Pat.calls]⟩,
    rfl, trivial⟩

theorem qRpos_wf : QProg.WF [qRpos] :=
  ⟨⟨⟨by decide, by decide⟩, by simp [Query.CallsOK, QBody.calls, qRpos, qR, Pat.calls]⟩, rfl, trivial⟩

/-- `call 0([1])` *must* happen before `ret 0(2)`. -/
def progMust : FinTSys TAct := prog

/-- The call's argument is one of two locations: the call only *may* match. -/
def progMay : FinTSys TAct where
  St     := Nat
  deq    := inferInstance
  init   := 0
  final s := s == 2
  succ
    | 0 => [(some (.call 0 [[1, 3]]), 1)]
    | 1 => [(some (.ret 0 [2]), 2)]
    | _ => []
  finite := ⟨[0, 1, 2], by decide, by
    intro s hs e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> simp at he <;> subst he <;> decide⟩

/-- A loop of calls `call 0([1])` at `0`, which may be skipped before
    `ret 0(2)`.  The walk skipping the loop and the walk going round it once
    reach the same program and query state with the same assignments; only
    their trackers differ, so neither is skipped by progress. -/
def progLoop : FinTSys TAct where
  St     := Nat
  deq    := inferInstance
  init   := 0
  final s := s == 1
  succ
    | 0 => [(some (.call 0 [[1]]), 0), (some (.ret 0 [2]), 1)]
    | _ => []
  finite := ⟨[0, 1], by decide, by
    intro s hs e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> simp at he <;> rcases he with rfl | rfl <;> decide⟩

def φNone : TFacts := { dep := [], ac := [], sk := [] }

-- Without the `except`, `R` matches the program.
#guard !(checkIn progMust qRpos [] qRpos_wf φNone).isEmpty
-- The call certainly happened: the `except` excludes every walk.
#guard (checkIn progMust qR [qC] qR_wf φNone).isEmpty
-- The call only may have happened (to `1` or `3`): no exclusion.
#guard !(checkIn progMay qR [qC] qR_wf φNone).isEmpty
-- The walk skipping the loop is a witness, with `f = 0`.
#guard (checkIn progLoop qR [qC] qR_wf φNone).any fun w => w.2.2 (.src "f") == some 0

end CoreJS.McTests
