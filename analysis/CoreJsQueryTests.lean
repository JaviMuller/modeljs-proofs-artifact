/-
  # Core JavaScript — Query Test Suite

  A regression suite for the concrete semantics and the query semantics.  It
  is compiled, not executed: every `theorem` below is a machine-checked
  statement about a small concrete program, so the file stops type-checking if
  a rule of `CoreJsSemantics.lean` or of `CoreJsQuerySemantics.lean` changes
  in a way that breaks it.

  1. **Statement shapes.**  One program per statement shape of `Stmt`, run from
     the initial configuration `Conf.init`, checking the resulting trace and
     the relevant part of the final heap/store/register.
  2. **Queries.**  Queries over the execution records of two of those
     programs, covering every action, every predicate, `;`, `‖`, `&`,
     `exists`, `when`, `except` and query invocation, each with matching and
     non-matching cases.

  The `Concrete` instance below is *test-only*: it is not injective on `Val`,
  so it does not satisfy `ConcreteSpec`, and the bridge theorems of
  `CoreJsQueryBridge.lean` cannot be applied to it.  Its allocator hands out
  consecutive fresh locations per allocation site, which is all the programs
  below need.

  Plain Lean 4 — no Mathlib required.
-/

import CoreJsQueryBridge

namespace CoreJS.Tests

open CoreJS

/-! ## Test parameters -/

instance : Concrete where
  litLoc
    | .undef      => 0
    | .bool false => 1
    | .bool true  => 2
    | .num n      => 10 + n.toNat
    | .str s      => 100 + s.length
    | .fid f      => 200 + f.length
    | .loc l      => 300 + l
  -- Site `κ` owns the block `[1000 + 100κ, 1000 + 100κ + 8)`; its next free
  -- location is the first one of the block not holding a value yet.
  allocC h κ :=
    1000 + 100 * κ + (List.range 8).countP (fun i => (h.val (1000 + 100 * κ + i)).isSome)
  opSem op v₁ v₂ :=
    match op, v₁, v₂ with
    | .add,    .num a, .num b => .num (a + b)
    | .lt,     .num a, .num b => .bool (decide (a < b))
    | .eq,     .num a, .num b => .bool (decide (a = b))
    | .concat, .str a, .str b => .str (a ++ b)
    | _, _, _ => .undef

/-- Function environment: `id(a) { return a }`, `nop(a) { skip }`,
    `sink(p) { skip }`.  Bodies mention no literals (the initial heap only
    holds the literals of the main statement). -/
def Γ₀ : Env := fun f =>
  if f = "id" then some (["a"], .ret (.var "a")) else
  if f = "nop" then some (["a"], .skip) else
  if f = "sink" then some (["p"], .skip) else none

/-! ## Proof automation

`bigstep` builds a derivation of `BigStep Γ c s ?r` for a concrete program,
discovering the result `?r` as it goes: every premise of a rule is an equation
that `rfl` closes, apart from the `if`/`seq` choices, resolved by
backtracking. -/

syntax "bigstep" : tactic
macro_rules
  | `(tactic| bigstep) => `(tactic| first
      | (apply BigStep.skip)
      | (apply BigStep.assign <;> rfl)
      | (apply BigStep.binOp <;> rfl)
      | (apply BigStep.objLit <;> rfl)
      | (apply BigStep.lookupS <;> rfl)
      | (apply BigStep.lookupD <;> rfl)
      | (apply BigStep.updateS <;> rfl)
      | (apply BigStep.updateD <;> rfl)
      | (apply BigStep.ret <;> rfl)
      | (apply BigStep.setTaint <;> rfl)
      | (apply BigStep.setSink <;> rfl)
      | (apply BigStep.seqCont <;> bigstep)
      | (apply BigStep.seqRet <;> bigstep)
      | (apply BigStep.ifTrue <;> first | rfl | bigstep)
      | (apply BigStep.ifFalse <;> first | rfl | bigstep)
      | (apply BigStep.whileDo <;> bigstep)
      | (apply BigStep.callRet <;> first | rfl | bigstep)
      | (apply BigStep.callCont <;> first | rfl | bigstep))

/-- `run tac`: goal `∃ r, BigStep Γ (Conf.init s) s r ∧ P r`; derive the run,
    then prove `P r` with `tac`. -/
macro "run " tac:tacticSeq : tactic =>
  `(tactic| (apply Exists.intro; apply And.intro; (· bigstep); · $tac))

@[simp] theorem LocSet.union_apply (A B : LocSet) (l : Loc) : (A ∪ B) l = (A l ∨ B l) := rfl
@[simp] theorem LocSet.insert_apply (a : Loc) (A : LocSet) (l : Loc) :
    (insert a A : LocSet) l = (l = a ∨ A l) := rfl
@[simp] theorem LocSet.singleton_apply (a l : Loc) : ({a} : LocSet) l = (l = a) := rfl
@[simp] theorem LocSet.empty_apply (l : Loc) : (∅ : LocSet) l = False := rfl

/-- The run of `s` from the initial configuration satisfies `P`. -/
def Runs (s : Stmt) (P : Res → Prop) : Prop :=
  ∃ r, BigStep Γ₀ (Conf.init s) s r ∧ P r

/-! ## 1. Statement shapes -/

open Stmt Expr

-- Some literals used throughout: `num n` sits at location `10 + n`, `str "p"`
-- at 101, `fid "id"` at 202, `undef` at 0, `true` at 2 and `false` at 1.

/-- `skip` -/
def pSkip : Stmt := skip
theorem run_skip : Runs pSkip fun r => r.trc.toList = [] ∧ r.out = .cont := by
  run exact ⟨rfl, rfl⟩

/-- `x := e` -/
def pAssign : Stmt := assign "a" (val (.num 3))
theorem run_assign : Runs pAssign fun r => r.trc.toList = [] ∧ r.sto "a" = some 13 := by
  run exact ⟨rfl, rfl⟩

/-- `x :=κ e₁ ⊕ e₂`: the result is fresh (`1100`), holds `7`, and depends on both operands. -/
def pBin : Stmt :=
  assign "a" (val (.num 3)) ;; assign "b" (val (.num 4)) ;;
  binOp "c" 1 .add (var "a") (var "b")
theorem run_binOp : Runs pBin fun r =>
    r.sto "c" = some 1100 ∧ r.heap.val 1100 = some (.num 7) ∧
    r.reg.dep 1100 13 ∧ r.reg.dep 1100 14 ∧ ¬ r.reg.dep 1100 15 := by
  run refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> simp +decide [Reg.setDep, Reg.empty]

/-- `x :=κ {pᵢ : eᵢ}` -/
def pObjLit : Stmt :=
  assign "a" (val (.num 5)) ;; objLit "o" 2 [("p", var "a")]
theorem run_objLit : Runs pObjLit fun r =>
    r.trc.toList = [] ∧ r.sto "o" = some 1200 ∧ r.heap.obj 1200 "p" = some 15 ∧
    r.heap.obj 1200 "q" = none := by
  run exact ⟨rfl, rfl, rfl, rfl⟩

/-- `x :=κ e.p` -/
def pLookupS : Stmt := pObjLit ;; lookupS "r" 3 (var "o") "p"
theorem run_lookupS : Runs pLookupS fun r =>
    r.trc.toList = [.lookup 15 1200 101] ∧ r.sto "r" = some 15 := by
  run exact ⟨rfl, rfl⟩

/-- `x :=κ e₁[e₂]` -/
def pLookupD : Stmt := pObjLit ;; assign "k" (val (.str "p")) ;; lookupD "r" 3 (var "o") (var "k")
theorem run_lookupD : Runs pLookupD fun r =>
    r.trc.toList = [.lookup 15 1200 101] ∧ r.sto "r" = some 15 := by
  run exact ⟨rfl, rfl⟩

/-- `e₁.p :=κ e₂` -/
def pUpdateS : Stmt :=
  assign "a" (val (.num 5)) ;; objLit "o" 2 [] ;; updateS 3 (var "o") "p" (var "a")
theorem run_updateS : Runs pUpdateS fun r =>
    r.trc.toList = [.update 1200 101 15] ∧ r.heap.obj 1200 "p" = some 15 := by
  run exact ⟨rfl, rfl⟩

/-- `e₁[e₂] :=κ e₃` -/
def pUpdateD : Stmt :=
  assign "k" (val (.str "p")) ;; assign "a" (val (.num 5)) ;; objLit "o" 2 [] ;;
  updateD 3 (var "o") (var "k") (var "a")
theorem run_updateD : Runs pUpdateD fun r =>
    r.trc.toList = [.update 1200 101 15] ∧ r.heap.obj 1200 "p" = some 15 := by
  run exact ⟨rfl, rfl⟩

/-- `x :=κ f(e⃗)`, explicit return: the call evaluates to the returned location. -/
def pCallRet : Stmt := assign "a" (val (.num 3)) ;; call "r" 1 (val (.fid "id")) [var "a"]
theorem run_callRet : Runs pCallRet fun r =>
    r.trc.toList = [.call 202 [13], .ret 202 13] ∧ r.sto "r" = some 13 := by
  run exact ⟨rfl, rfl⟩

/-- `x :=κ f(e⃗)`, implicit return: the call evaluates to `undefined`. -/
def pCallCont : Stmt := assign "a" (val (.num 3)) ;; call "r" 1 (val (.fid "nop")) [var "a"]
theorem run_callCont : Runs pCallCont fun r =>
    r.trc.toList = [.call 203 [13], .ret 203 0] ∧ r.sto "r" = some 0 := by
  run exact ⟨rfl, rfl⟩

/-- `if(e) {s₁} else {s₂}`: the two branches leave different traces. -/
def pIf (b : Bool) : Stmt :=
  assign "a" (val (.num 5)) ;; objLit "o" 2 [] ;; assign "c" (val (.bool b)) ;;
  ifElse 1 (var "c") (updateS 3 (var "o") "p" (var "a")) (updateS 4 (var "o") "qq" (var "a"))
theorem run_ifTrue : Runs (pIf true) fun r => r.trc.toList = [.update 1200 101 15] := by
  run rfl
theorem run_ifFalse : Runs (pIf false) fun r => r.trc.toList = [.update 1200 102 15] := by
  run rfl

/-- `while(e) {s}`: two iterations, each allocating a fresh counter and a fresh
    flag (sites 3 and 4), so the loop never reuses a location. -/
def pWhile : Stmt :=
  assign "i" (val (.num 0)) ;; assign "lim" (val (.num 2)) ;; assign "one" (val (.num 1)) ;;
  objLit "o" 5 [] ;; binOp "b" 1 .lt (var "i") (var "lim") ;;
  whileDo 2 (var "b")
    (updateS 6 (var "o") "p" (var "i") ;;
     binOp "i" 3 .add (var "i") (var "one") ;;
     binOp "b" 4 .lt (var "i") (var "lim"))
theorem run_while : Runs pWhile fun r =>
    r.trc.toList = [.update 1500 101 10, .update 1500 101 1300] ∧
    r.sto "i" = some 1301 ∧ r.heap.val 1301 = some (.num 2) ∧
    r.heap.val 1401 = some (.bool false) := by
  run exact ⟨rfl, rfl, rfl, rfl⟩

/-- `return e` -/
def pRet : Stmt := assign "a" (val (.num 3)) ;; ret (var "a")
theorem run_ret : Runs pRet fun r => r.trc.toList = [] ∧ r.out = .ret 13 := by
  run exact ⟨rfl, rfl⟩

/-- `return` cuts the sequence short: `[Sequence Ret]`. -/
def pSeqRet : Stmt := (assign "a" (val (.num 3)) ;; ret (var "a")) ;; assign "a" (val (.num 4))
theorem run_seqRet : Runs pSeqRet fun r => r.out = .ret 13 ∧ r.sto "a" = some 13 := by
  run exact ⟨rfl, rfl⟩

/-- `setTaint e`, `setSink e`, and a call of the sink on a tainted value.

    This is also the program the query tests below run on.  `a` is
    attacker-controlled; `b = a + 1` (location 1100) depends on it and is
    therefore attacker-controlled in the observation, although not in the
    register; `sink` is the sink function; `six` holds the same value as `b`. -/
def pTaint : Stmt :=
  setSink (val (.fid "sink")) ;;
  assign "a" (val (.num 5)) ;; setTaint (var "a") ;;
  assign "one" (val (.num 1)) ;; assign "six" (val (.num 6)) ;;
  binOp "b" 1 .add (var "a") (var "one") ;;
  call "r" 2 (val (.fid "sink")) [var "b"]
theorem run_taint : Runs pTaint fun r =>
    r.trc.toList = [.call 204 [1100], .ret 204 0] ∧
    r.reg.sk 204 ∧ ¬ r.reg.sk 15 ∧ r.reg.ac 15 ∧ ¬ r.reg.ac 1100 ∧
    (Exec.ofRes r).obs.ac 1100 ∧ ¬ (Exec.ofRes r).obs.ac 11 := by
  run refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      <;> simp +decide [Exec.ofRes, Obs.ofRun, Reg.setDep, Reg.empty]

/-! ## 2. Queries

Every query is run on the execution record of `pTaint` (trace
`[call 204 [1100], ret 204 0]`; `204` is the sink function, `1100` the tainted
value `b`, `16` the location of the literal `6`, `0` the location of
`undefined`), except the lookup/update queries, which run on `pObjRT`. -/

/-- A query with (optionally) an invariant, an excluded pattern and locals. -/
def mkQ (name : QName) (params : List Var) (F : Pat) (I : Inv := .tt)
    (E : Option Pat := none) (locals : List Var := []) : Query :=
  ⟨name, params, { locals, body := F, when := I, except := E }⟩

/-- `Q` matches the execution record of the run of `s` on the arguments `ls`. -/
def QRuns (s : Stmt) (Δ : QProg) (Q : QName) (ls : List Loc) (b : Prop) : Prop :=
  Runs s fun r => Exec.Matches Δ (Exec.ofRes r) Q ls ↔ b

/-- Matching a query with no locals: body, invariant, and (absent) `except`. -/
theorem _root_.CoreJS.Guarded.Sat.simple {Θ t σ ξ} {g : Guarded} {i j : Nat} (hl : g.locals = [])
    (hn : g.except = none) (hb : Pat.Sat Θ t σ ξ g.body i j) (hi : Inv.Sat σ ξ g.when) :
    Guarded.Sat Θ t σ ξ g i j :=
  .mk (ls := []) (by simp [hl]) (by rw [hl]; rfl) hb hi (by simp [hn])

/-- Inversion for a query with no locals. -/
theorem _root_.CoreJS.Guarded.Sat.invert {Θ t σ ξ} {g : Guarded} {i j : Nat} (hl : g.locals = [])
    (h : Guarded.Sat Θ t σ ξ g i j) :
    Pat.Sat Θ t σ ξ g.body i j ∧ Inv.Sat σ ξ g.when ∧
      ∀ F', g.except = some F' → ∀ k, ¬ Pat.Sat Θ t σ ξ F' i k := by
  cases h with
  | mk hlen hξ hb hi he =>
    rw [hl] at hlen hξ
    have : ‹List Loc› = [] := List.length_eq_zero_iff.1 hlen
    subst this
    subst hξ
    exact ⟨hb, hi, he⟩

/-- `simp` set that evaluates predicates on the observation of a run. -/
syntax "obs_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| obs_simp [$ids,*]) =>
    `(tactic| simp +decide [$ids,*, mkQ, Inv.Sat, Pred.Sat, Exec.ofRes, Obs.ofRun, LEnv.bind,
        LEnv.empty, Reg.setDep, Reg.empty])

/-- `simp` set that evaluates the trace of a run and the action patterns against it. -/
syntax "tr_simp" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| tr_simp $[$loc]?) =>
    `(tactic| simp +decide [Exec.ofRes, Trc.toList, LEnv.bind, LEnv.empty, QAct.inst] $[$loc]?)

/-- Head query of a program matches: unfold and supply the guarded pattern. -/
theorem matches_of {q : Query} {Δ : QProg} {e : Exec} {ls : List Loc} {j : Nat}
    (hlen : ls.length = q.params.length)
    (h : Guarded.Sat (Δ.interp e.trc.toList e.obs) e.trc.toList e.obs
           (LEnv.empty.bind q.params ls) q.body 0 j) :
    Exec.Matches (q :: Δ) e q.name ls :=
  (Exec.Matches.iff_head q Δ e ls).2 ⟨hlen, j, h⟩

/-- Head query of a program does not match: the guarded pattern has no match. -/
theorem not_matches_of {q : Query} {Δ : QProg} {e : Exec} {ls : List Loc}
    (h : ∀ j, ¬ Guarded.Sat (Δ.interp e.trc.toList e.obs) e.trc.toList e.obs
           (LEnv.empty.bind q.params ls) q.body 0 j) :
    ¬ Exec.Matches (q :: Δ) e q.name ls := by
  rintro ⟨j, hj⟩
  exact h j ((QProg.interp_head q Δ _ _ ls 0 j).1 hj).2

/-! ### Actions, sequencing, invariants -/

/-- `Call(f, [x]) when sk(f) ∧ ac(x)`: the sink is called with a tainted value. -/
def qSink : Query :=
  mkQ "Sink" ["f", "x"] (.act (.call "f" ["x"])) (.and (.pred (.sk "f")) (.pred (.ac "x")))

theorem q_sink : Runs pTaint fun r => Exec.Matches [qSink] (Exec.ofRes r) "Sink" [204, 1100] := by
  run exact matches_of (j := 1) rfl
        (Guarded.Sat.simple rfl rfl (.act (by decide) (by decide) (by decide)) (by obs_simp [qSink]))

/-- The same with `¬ac(x)`: no match, since `1100` is attacker-controlled. -/
def qSinkClean : Query :=
  mkQ "SinkClean" ["f", "x"] (.act (.call "f" ["x"])) (.and (.pred (.sk "f")) (.not (.pred (.ac "x"))))

theorem q_sinkClean_no :
    Runs pTaint fun r => ¬ Exec.Matches [qSinkClean] (Exec.ofRes r) "SinkClean" [204, 1100] := by
  run refine not_matches_of fun j hj => ?_
      obtain ⟨_, hi, _⟩ := hj.invert rfl
      revert hi
      obs_simp [qSinkClean]

/-- ... and the untainted literal `5` (location 15, but also attacker-controlled
    here, being `a`'s location) versus `1` (location 11, untainted): the call
    has to be *of* the given arguments, so `[204, 11]` does not match at all. -/
theorem q_sink_wrongArg : Runs pTaint fun r =>
    ¬ Exec.Matches [qSink] (Exec.ofRes r) "Sink" [204, 11] := by
  run refine not_matches_of fun j hj => ?_
      obtain ⟨hb, _, _⟩ := hj.invert rfl
      cases hb with
      | @act _ _ j h₁ h₂ h₃ =>
        rcases j with _ | _ | _ | j <;> tr_simp at h₂ h₃ <;> omega

/-- `Call(f,[x]) ; Retn(f,r)` -/
def qSeq : Query := mkQ "Seq" ["f", "x", "r"] (.seq (.act (.call "f" ["x"])) (.act (.retn "f" "r")))
theorem q_seq : Runs pTaint fun r => Exec.Matches [qSeq] (Exec.ofRes r) "Seq" [204, 1100, 0] := by
  run exact matches_of (j := 2) rfl
        (Guarded.Sat.simple rfl rfl (.seq (k := 1) (.act (by decide) (by decide) (by decide))
          (.act (by decide) (by decide) (by decide))) (by obs_simp [qSeq]))

/-- `Retn(f,r) ; Call(f,[x])`: the actions occur in the other order. -/
def qSeqRev : Query := mkQ "SeqRev" ["f", "x", "r"] (.seq (.act (.retn "f" "r")) (.act (.call "f" ["x"])))
theorem q_seqRev_no : Runs pTaint fun r =>
    ¬ Exec.Matches [qSeqRev] (Exec.ofRes r) "SeqRev" [204, 1100, 0] := by
  run refine not_matches_of fun j hj => ?_
      obtain ⟨hb, _, _⟩ := hj.invert rfl
      cases hb with
      | @seq _ _ _ k j h₁ h₂ =>
        cases h₁ with
        | @act _ _ _ b₁ b₂ b₃ =>
          cases h₂ with
          | @act _ _ _ c₁ c₂ c₃ =>
            rcases k with _ | _ | k <;> tr_simp at b₂ b₃ c₁ c₂ c₃ <;> omega

/-- `Retn(f,x) ‖ Call(f,[x])`: the second alternative matches. -/
def qAlt : Query := mkQ "Alt" ["f", "x"] (.alt (.act (.retn "f" "x")) (.act (.call "f" ["x"])))
theorem q_alt : Runs pTaint fun r => Exec.Matches [qAlt] (Exec.ofRes r) "Alt" [204, 1100] := by
  run exact matches_of (j := 1) rfl
        (Guarded.Sat.simple rfl rfl (.altR (.act (by decide) (by decide) (by decide))) (by obs_simp [qAlt]))

/-- `Retn(f,r) & Call(f,[x])`: both performed, in either order; ends at the later. -/
def qBoth : Query := mkQ "Both" ["f", "x", "r"] (.both (.act (.retn "f" "r")) (.act (.call "f" ["x"])))
theorem q_both : Runs pTaint fun r => Exec.Matches [qBoth] (Exec.ofRes r) "Both" [204, 1100, 0] := by
  run exact matches_of (j := 2) rfl
        (Guarded.Sat.simple rfl rfl (.both (j₁ := 2) (j₂ := 1) (.act (by decide) (by decide) (by decide))
          (.act (by decide) (by decide) (by decide)) rfl) (by obs_simp [qBoth]))

/-- `a & a` is matched as soon as `a` is: one action serves both sides. -/
def qBothSelf : Query := mkQ "BothSelf" ["f", "x"] (.both (.act (.call "f" ["x"])) (.act (.call "f" ["x"])))
theorem q_bothSelf : Runs pTaint fun r =>
    Exec.Matches [qBothSelf] (Exec.ofRes r) "BothSelf" [204, 1100] := by
  run exact matches_of (j := 1) rfl
        (Guarded.Sat.simple rfl rfl (.both (j₁ := 1) (j₂ := 1) (.act (by decide) (by decide) (by decide))
          (.act (by decide) (by decide) (by decide)) rfl) (by obs_simp [qBothSelf]))

/-- `ε` is matched by every execution. -/
def qEps : Query := mkQ "Eps" [] .eps
theorem q_eps : Runs pTaint fun r => Exec.Matches [qEps] (Exec.ofRes r) "Eps" [] := by
  run exact matches_of (j := 0) rfl (Guarded.Sat.simple rfl rfl .eps (by obs_simp [qEps]))

/-! ### `exists` and `except` -/

/-- `exists y: Retn(f, y)`: the local `y` is chosen by the matcher. -/
def qExists : Query := mkQ "Exists" ["f"] (.act (.retn "f" "y")) .tt none ["y"]
theorem q_exists : Runs pTaint fun r => Exec.Matches [qExists] (Exec.ofRes r) "Exists" [204] := by
  run exact matches_of (j := 2) rfl
        (.mk (ls := [0]) rfl rfl (.act (by decide) (by decide) (by decide)) (by obs_simp [qExists])
          (fun _ h => nomatch h))

/-- `Call(f,[x]) except Retn(f,r)`: the mitigation `Retn(f,r)` does occur, so
    the query is not matched. -/
def qExceptHit : Query :=
  mkQ "ExceptHit" ["f", "x", "r"] (.act (.call "f" ["x"])) .tt (some (.act (.retn "f" "r")))
theorem q_exceptHit_no : Runs pTaint fun r =>
    ¬ Exec.Matches [qExceptHit] (Exec.ofRes r) "ExceptHit" [204, 1100, 0] := by
  run refine not_matches_of fun j hj => ?_
      obtain ⟨_, _, he⟩ := hj.invert rfl
      exact he _ rfl 2 (.act (by decide) (by decide) (by decide))

/-- ... whereas excluding `Retn(f,x)` (never performed: it would return `1100`) leaves it matched. -/
def qExceptMiss : Query :=
  mkQ "ExceptMiss" ["f", "x"] (.act (.call "f" ["x"])) .tt (some (.act (.retn "f" "x")))
theorem q_exceptMiss : Runs pTaint fun r =>
    Exec.Matches [qExceptMiss] (Exec.ofRes r) "ExceptMiss" [204, 1100] := by
  run refine matches_of (j := 1) rfl
        (.mk (ls := []) rfl rfl (.act (by decide) (by decide) (by decide)) (by obs_simp [qExceptMiss])
          fun F' hF' k hk => ?_)
      cases hF'
      cases hk with
      | @act _ _ k h₁ h₂ h₃ =>
        rcases k with _ | _ | _ | k <;> tr_simp at h₂ h₃ <;> omega

/-! ### Predicates -/

/-- `dep(x, y)`: `1100 = a + 1` depends on `a` (location 15) and on `1` (location 11). -/
def qDep : Query := mkQ "Dep" ["x", "y"] .eps (.pred (.dep "x" "y"))
theorem q_dep : Runs pTaint fun r => Exec.Matches [qDep] (Exec.ofRes r) "Dep" [1100, 15] := by
  run exact matches_of (j := 0) rfl (Guarded.Sat.simple rfl rfl .eps (by obs_simp [qDep]))
theorem q_dep_no : Runs pTaint fun r => ¬ Exec.Matches [qDep] (Exec.ofRes r) "Dep" [15, 1100] := by
  run refine not_matches_of fun j hj => ?_
      obtain ⟨_, hi, _⟩ := hj.invert rfl
      revert hi
      obs_simp [qDep]

/-- `hv(x, 6)`, and `sv(x, y)`: `1100` and `16` both hold `6`; `1100` and `15` do not
    hold the same value; neither do two locations holding no value. -/
def qHv : Query := mkQ "Hv" ["x"] .eps (.pred (.hv "x" (.num 6)))
def qSv : Query := mkQ "Sv" ["x", "y"] .eps (.pred (.sv "x" "y"))
theorem q_hv : Runs pTaint fun r => Exec.Matches [qHv] (Exec.ofRes r) "Hv" [1100] := by
  run exact matches_of (j := 0) rfl (Guarded.Sat.simple rfl rfl .eps (by obs_simp [qHv]))
theorem q_hv_no : Runs pTaint fun r => ¬ Exec.Matches [qHv] (Exec.ofRes r) "Hv" [15] := by
  run refine not_matches_of fun j hj => ?_
      obtain ⟨_, hi, _⟩ := hj.invert rfl
      revert hi
      obs_simp [qHv]
theorem q_sv : Runs pTaint fun r => Exec.Matches [qSv] (Exec.ofRes r) "Sv" [1100, 16] := by
  run exact matches_of (j := 0) rfl (Guarded.Sat.simple rfl rfl .eps (by obs_simp [qSv]))
theorem q_sv_no : Runs pTaint fun r => ¬ Exec.Matches [qSv] (Exec.ofRes r) "Sv" [1100, 15] := by
  run refine not_matches_of fun j hj => ?_
      obtain ⟨_, hi, _⟩ := hj.invert rfl
      revert hi
      obs_simp [qSv]
theorem q_sv_undefined_no :
    Runs pTaint fun r => ¬ Exec.Matches [qSv] (Exec.ofRes r) "Sv" [5000, 5001] := by
  run refine not_matches_of fun j hj => ?_
      obtain ⟨_, hi, _⟩ := hj.invert rfl
      revert hi
      obs_simp [qSv]

/-- `sk(x)`: `204` is a sink, `1100` is not. -/
def qSk : Query := mkQ "Sk" ["x"] .eps (.pred (.sk "x"))
theorem q_sk : Runs pTaint fun r => Exec.Matches [qSk] (Exec.ofRes r) "Sk" [204] := by
  run exact matches_of (j := 0) rfl (Guarded.Sat.simple rfl rfl .eps (by obs_simp [qSk]))
theorem q_sk_no : Runs pTaint fun r => ¬ Exec.Matches [qSk] (Exec.ofRes r) "Sk" [1100] := by
  run refine not_matches_of fun j hj => ?_
      obtain ⟨_, hi, _⟩ := hj.invert rfl
      revert hi
      obs_simp [qSk]

/-- `true`, `false`, `∧`, `∨`, `¬`: `(true ∧ false) ∨ ¬false` holds, `true ∧ false` does not. -/
def qLogic : Query := mkQ "Logic" [] .eps (.or (.and .tt .ff) (.not .ff))
def qLogicNo : Query := mkQ "LogicNo" [] .eps (.and .tt .ff)
theorem q_logic : Runs pTaint fun r => Exec.Matches [qLogic] (Exec.ofRes r) "Logic" [] := by
  run exact matches_of (j := 0) rfl (Guarded.Sat.simple rfl rfl .eps (by obs_simp [qLogic]))
theorem q_logic_no : Runs pTaint fun r => ¬ Exec.Matches [qLogicNo] (Exec.ofRes r) "LogicNo" [] := by
  run refine not_matches_of fun j hj => ?_
      obtain ⟨_, hi, _⟩ := hj.invert rfl
      revert hi
      obs_simp [qLogicNo]

/-! ### Query invocation -/

/-- `Outer(g, y) { exists r: Sink(g, y) ; Retn(g, r) }`.  The parameters of `Sink`
    are named `f, x`; `Outer` renames them to `g, y` at the call, and its local
    `r` is private to it. -/
def qOuter : Query :=
  mkQ "Outer" ["g", "y"] (.seq (.query "Sink" ["g", "y"]) (.act (.retn "g" "r"))) .tt none ["r"]
theorem q_outer : Runs pTaint fun r =>
    Exec.Matches [qOuter, qSink] (Exec.ofRes r) "Outer" [204, 1100] := by
  run refine matches_of (j := 2) rfl
        (.mk (ls := [0]) rfl rfl
          (.seq (k := 1) (.query ?_) (.act (by decide) (by decide) (by decide))) (by obs_simp [qOuter])
          (fun _ h => nomatch h))
      refine (QProg.interp_head qSink [] _ _ _ 0 1).2 ⟨rfl, Guarded.Sat.simple rfl rfl ?_ ?_⟩
      · exact .act (by decide) (by decide) (by decide)
      · obs_simp [qSink]

/-- The invoked query's invariant is enforced: passing the sink and its argument in the
    wrong order violates `sk(f)` inside `Sink`, so `Outer` is not matched. -/
def qOuterSwap : Query :=
  mkQ "OuterSwap" ["g", "y"] (.query "Sink" ["y", "g"])
theorem q_outerSwap_no : Runs pTaint fun r =>
    ¬ Exec.Matches [qOuterSwap, qSink] (Exec.ofRes r) "OuterSwap" [204, 1100] := by
  run refine not_matches_of fun j hj => ?_
      obtain ⟨hb, _, _⟩ := hj.invert rfl
      cases hb with
      | query h =>
        obtain ⟨_, hg⟩ := (QProg.interp_head qSink [] _ _ _ _ _).1 h
        obtain ⟨_, hi, _⟩ := hg.invert rfl
        revert hi
        obs_simp [qSink, qOuterSwap]

/-! ### Lookup and update actions

Run on `pObjRT`: `o.p := a ; r := o.p`, with trace
`[update 1200 101 15, lookup 15 1200 101]`. -/

def pObjRT : Stmt := pUpdateS ;; lookupS "r" 4 (var "o") "p"

/-- `o[k] := v ; r := o[k]` (with `x₁[x₂] := x₃` and `x₁ := x₂[x₃]`). -/
def qStoreLoad : Query :=
  mkQ "StoreLoad" ["o", "k", "v"] (.seq (.act (.update "o" "k" "v")) (.act (.lookup "v" "o" "k")))
def qLoadStore : Query :=
  mkQ "LoadStore" ["o", "k", "v"] (.seq (.act (.lookup "v" "o" "k")) (.act (.update "o" "k" "v")))
theorem q_storeLoad : Runs pObjRT fun r =>
    Exec.Matches [qStoreLoad] (Exec.ofRes r) "StoreLoad" [1200, 101, 15] := by
  run exact matches_of (j := 2) rfl
        (Guarded.Sat.simple rfl rfl (.seq (k := 1) (.act (by decide) (by decide) (by decide))
          (.act (by decide) (by decide) (by decide))) (by obs_simp [qStoreLoad]))
theorem q_loadStore_no : Runs pObjRT fun r =>
    ¬ Exec.Matches [qLoadStore] (Exec.ofRes r) "LoadStore" [1200, 101, 15] := by
  run refine not_matches_of fun j hj => ?_
      obtain ⟨hb, _, _⟩ := hj.invert rfl
      cases hb with
      | @seq _ _ _ k j h₁ h₂ =>
        cases h₁ with
        | @act _ _ _ b₁ b₂ b₃ =>
          cases h₂ with
          | @act _ _ _ c₁ c₂ c₃ =>
            rcases k with _ | _ | k <;> tr_simp at b₂ b₃ c₁ c₂ c₃ <;> omega
