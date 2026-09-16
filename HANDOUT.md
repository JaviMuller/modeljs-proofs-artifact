# Handout: automaton-based trace model for Theorem B15

This branch (`automaton-trace-model`) is a design exploration, not yet any
Lean code. It exists to record a long design conversation so a fresh
conversation/model can pick up implementation without re-deriving everything.
Read this whole document before writing any Lean.

## 1. Why this branch exists

While proving Theorem B15 (`analysis/CoreJsAbstractionSoundness.lean`,
`soundnessN`) on `main`, the `[Sequence]` case hit a genuine gap, *not* a
missing proof technique:

- Concretely, `s1 ;; s2` can have `s1` return (so `s2` never runs).
- Abstractly, `s1`'s own analysis can be imprecise (e.g. via `[If-Then-Else]`
  joining a returning branch with a continuing one) and conclude `.cont` even
  though *this* concrete execution of `s1` returned.
- When that happens, `[Sequence Cont]` fires abstractly, and `s2` gets
  analyzed with a **strong** `ASto.upd` (store update — it overwrites, it does
  not join). That overwritten store has nothing to do with the real,
  never-executed-concretely `s2`.
- Result: `Sto.Alpha α' r.sto ar.sto` is not just hard to prove in this case —
  it is **false**, for no choice of `α'`. (Concrete example: `s2` does
  `w := 10`, but concretely `w` still holds its old, unrelated value, since
  `s2` never ran.)
- Crucially, this is *specific to the store*: every `AHeap` update
  (`weakSetVal`, `weakSetObj`, `weakSetObjV`, `weakSetObjs`) is weak/monotonic
  (union-based), so `Heap.Alpha` survives spurious exploration fine. `AReg`'s
  `ac`/`sk` are always weak (union) too; `AReg.dep` is weak in `binOp`,
  strong only in `objLit`'s reset (a *different*, already-documented gap, see
  REMARK 3 in `CoreJsAbstractSemantics.lean`). `ASto.upd` is the only
  *unconditionally* strong update, used by every variable-assigning rule.
  `[If-Then-Else]`'s own store combinator is `ρ₁ ⊔ ρ₂` — a join, not an
  overwrite — so this specific failure mode is confined to `[Sequence]`
  (and, by inheritance, `[While]`, which unfolds via `seq`).

The current `sorry` for this is at `analysis/CoreJsAbstractionSoundness.lean`,
in `soundnessN`'s `seqRet` case, clearly commented in place.

## 2. The settled fix for the store issue (independent of everything else in this handout)

Condition `Sto.Alpha` on the outcome being `.cont`; keep `Heap.Alpha`,
`Reg.Alpha`, `Trc.Alpha`, `Out.Alpha` **unconditional**. This is *not* "drop
the store always" — that would break the induction, because a `.cont`-outcome
statement might have more code sequenced after it, and *that* code needs the
store relation as an input hypothesis (this is exactly what the already-proved
`seqCont` "aligned" case relies on). Only `.ret`-outcome results get to skip
it — matching `callRet`'s own behavior of discarding the callee's final store
`ρf'` entirely (nothing downstream, within that function, ever reads it
again).

This fix:
- Is provable **against the existing `main`-branch semantics** (the
  regex/`mu`-trace one), no automaton needed.
- Requires no change to `abs_gen_seq`, `abs_gen_skip`, etc. — only to the
  shape of `soundnessN`/`soundness`/`soundness_top`'s conclusion, and to the
  cases that currently unconditionally prove `Sto.Alpha` (a mechanical,
  low-risk change for `skip`/`assign`/`ret`/`setTaint`/`setSink`/`lookupS`/
  `lookupD`/`seq`, since all but `seq`'s broken sub-case already prove the
  *stronger* unconditional fact for free).
- Is what `main` should actually implement. **This branch is not about that
  fix** — it is a separate, larger exploration of a different problem (below).

Two alternatives were considered and rejected — both fail for the *same*
underlying reason, which is worth recording so no one re-proposes either:

**Option B** — restrict `return` to tail position of the function body,
possibly via a `returned`/`retval` flag-variable transform (guarding every
statement after a potential early return in `if (!returned) { ... }`).
Rejected twice, for two different reasons. First: `[If-Then-Else]` explores
both branches unconditionally regardless of the guard ("the guard is not
inspected," per its own doc comment), so the guard doesn't actually suppress
anything at the abstract level. Second, and more fundamental, once you notice
that `⊔` preserves the "guard false" alternative's value rather than
discarding it (this is true, and is *why* `ifElse` itself never had this
problem) — wrapping *every* subsequent statement in its own `if (!returned)`
means *every* one of them now joins its own effect with whatever was true
immediately before it. Chain that across a whole function body and every
variable's abstract value becomes the union of every value it was ever
assigned, anywhere in the function — not "some precision lost," but the
strong/precise character of `ASto.upd` defeated almost entirely. Rejected.

**Option D** (proposed and then withdrawn in this session) — instead of
transforming the source, change `[Sequence Cont]`'s *abstract rule itself* to
join its heap/store/reg result with the pre-`s2` (post-`s1`) state as a
built-in safety net, and widen the trace to an alternation between "just
`s1`" and "`s1` followed by `s2`." This looked promising component-by-component
(heap/store/reg transport through the join's upper-bound property directly,
sidestepping `r2` entirely; the trace alternation and outcome relation both
check out) — but it has *exactly* the same fatal flaw as option B, for the
same reason: `s1 ;; s2 ;; s3` associates as `s1 ;; (s2 ;; s3)`, so the safety
net fires at *every* `[Sequence Cont]` application in a chain, with nothing
in `AOut.mk .cont L` able to distinguish "this `.cont` is safe" from "this
`.cont` is hiding a joined-away return" to apply it selectively. `w := 1; w
:= 2; w := 3` would abstractly yield `w ↦ {1,2,3}`, not `{3}`. Withdrawn.

**The reason option A avoids this entirely**: it changes *nothing* about
`CoreJsAbstractSemantics.lean` — `SA` computes exactly the same heap/store/
reg/trace it always did, at exactly the same precision. Only the *theorem's*
bookkeeping changes (what we claim to prove about the relationship between
that unchanged computation and the concrete semantics), and only in the one
case (`.ret` outcome) where the store claim is neither true nor needed.
That's what makes it different from B/D: those tried to fix the *analysis*
(or a *transform* feeding it) to make the stronger claim true; A instead
notices the stronger claim was never the right thing to ask for in the first
place.

**Decision (this session): implement option A on `main`, fully, until no
`sorry` remains in `CoreJsAbstractionSoundness.lean`.** This branch's
automaton exploration continues separately, for the finiteness/decidability
goal in §3 — it is not blocking, and not required for A.

## 3. What this branch is actually about: a finite, decidable automaton

Separately from the store issue, the user's static-analysis tool builds a
**finite-state automaton** as its actual output model, and this finiteness is
load-bearing for the paper, not an implementation convenience: the downstream
security-query search algorithm relies on it for termination/decidability
(if a `(program-state, query-state)` pair is revisited, stop exploring — this
only works if the state space is finite). Whether/how to formalize *this*
specific artifact, and prove Theorem B15 against it (or against something that
implies its soundness), is the open question this branch explores.

### 3.1 The current `ATrc.mu`/`tvar` mechanism is not what the tool does, and is not even correct for mutual recursion

`ATrc` (in `CoreJsAbstractSyntax.lean`) has `emp | act | seq | alt | star |
tvar | mu`, with a single anonymous recursion variable. `CoreJsAbstractSemantics.lean`'s `[Call-Fix]`/`[Call-Assume]` (via `ACallBranch`/`ASummary`/`ASigma`) use this: `[Call-Assume]` contributes bare `tvar`
when a function's summary is already assumed (`Sg f = some s`); `[Call-Fix]`
assumes a summary, analyzes the body, checks a post-fixed-point condition,
and wraps the body's trace in `.mu`.

**This is sound for a function that is directly self-recursive.** For mutual
recursion it is not, as this session discovered concretely:

Program:
```js
function f(x) {
  if (x) { var z = !x; var u = g(z); } else { return 0; }
  return 1;
}
function g(y) { var x = f(y); var z = x + 1; return z; }
module.exports = f
```

Trace: analyzing `f` assumes `s_f` (`Sg₁ = Sg.upd f s_f`). `f` calls `g`,
which isn't assumed yet, so `[Call-Fix]` fires for `g` too: assume `s_g`
(`Sg₂ = Sg₁.upd g s_g`), analyze `g`'s body. `g` calls back into `f`; now
`Sg₂ f = s_f` *is* defined, so `[Call-Assume]` fires, contributing bare
`tvar` — this becomes part of `t_g` (g's own body trace, which is
straight-line: `Call(f); tvar; Ret(f)`, no branching, since `g`'s body has
none). Then **`g`'s own** `[Call-Fix]` wraps all of `t_g` as `.mu t_g`,
binding that `tvar` — but that `tvar` was never about `g`'s own recursion
(`g` doesn't call `g`); it was `f`'s recursion point, captured by the wrong
binder purely because of nesting order.

Consequence: `.mu t_g` unfolded only ever offers, at that call site,
"`Call(f); (another copy of g's body); Ret(f)`" — never "immediately
`Ret(f)`, nothing in between." But `f`'s `else` branch (`return 0`) is a
real, valid concrete behavior `f` can take on *this* recursive invocation
too. There is no number of unfoldings of `.mu t_g` that produces an empty gap
between `Call(f)` and `Ret(f)`, because `g`'s structure has no such
alternative. `SigmaValid` doesn't happen to check the trace at all (only
heap/reg/ret), so this specifically breaks trace-relatedness
(`Trc.Alpha`/`Theorem B15`) for mutual recursion — a genuine soundness gap in
`main`'s current `[Call-Fix]`/`[Call-Assume]`, independent of anything in
this handout about automata.

**The fix** (needed either way, automaton or not): stop assuming/fixing one
function's summary at a time, incrementally, in whatever order recursion
happens to be encountered. Assume summaries for an entire mutually-recursive
group (an SCC of the call graph) *simultaneously*, analyze every function in
the group once under the *whole* assumption set, verify the post-fixed-point
condition for all of them at once. This needs **named** recursion variables
(`var f` / `mu f`, one per function in the group) instead of anonymous
`tvar`/`mu`, so a call back into `f` from inside `g` refers to `f`'s own
binder, not whichever function's `[Call-Fix]` happened to close last.

**Action item for whoever works on `main`'s `[Call-Fix]`/`[Call-Assume]`
cases (item 6 of "Remaining work" in `CoreJsAbstractionSoundness.lean`):**
this needs the named/simultaneous-fixpoint generalization regardless of
whether the automaton work below ever lands. It has not been fixed yet
anywhere. Flag it there.

### 3.2 Balanced (regex/`mu`-style) traces cannot be finite-state for unbounded recursion

Before designing the automaton, this session tried "just generalize `tvar`/
`mu` to named variables and keep everything properly nested." That fails for
a different reason than 3.1: even fixed, a properly-nested/balanced
representation is provably **not regular**. Eliminating `Xg` from the system
`Xf := Retf | Callg;Xg;Retg;Retf`, `Xg := Callf;Xf;Retf;Retg` gives
`Xf = b | a;Xf;c` for fixed `a,b,c`, which unfolds to `{aⁿ b cⁿ}` — the
textbook non-regular language, needing a stack/counter, not a bounded number
of states.

This is fine for a `Prop`-valued relation like the current `Trc.Alpha` (it
never needs to decide membership, only relate one finite concrete trace to
*some* finite unfolding), and is in fact *sharper* than a finite automaton —
the existing doc comment on `ATrc.mu` already says as much for the
single-function case ("soundness against μ therefore implies soundness
against the automaton"). But it is **not** what's needed here, because of
§3's central point: the tool needs actual finiteness, not just a `Prop` that
happens to be provable. **Unbalancedness — deliberately losing the exact
call/return correlation — is the price paid for finiteness under (mutual)
recursion, not an implementation shortcut.** This was the user's own insight,
confirmed by the above derivation.

## 4. The automaton construction, as extracted from worked examples

Everything below was reverse-engineered from hand-traced examples the user
worked through by hand (see conversation for the full worked traces — not
reproduced verbatim here, but every rule below was explicitly confirmed).

### 4.1 State allocation rule (per statement kind)

Confirmed: every construct except `call` allocates states 1-1 with its own
AST node (so indexable by something like the existing `Idx` site convention
used for `allocA`/`allocC`). `call` is the *only* construct whose *entry*
state is shared across multiple syntactic occurrences (all call sites
targeting the same function share one entry state — this is what keeps
recursion's state count bounded).

| Construct | New states | Behavior |
|---|---|---|
| `skip`, `assign`, `binOp`, `objLit`, `setTaint`, `setSink` | 0 | update store/heap/reg "in place" at the current state; control doesn't move; these are not real trace actions |
| `lookupS`/`lookupD`, `updateS`/`updateD` | 1 | edge: current state → new state, labeled with the lookup/update action |
| `call` | 2 | edge: current state → callee-entry (`Call` label); callee-entry is **shared across all call sites** to that function; a second new state is the continuation (specific to *this* call site — continuations are not shared) |
| `ret` | 0 | edge: current state → **every** registered continuation site of the enclosing function (`Ret` label, cross-product over all call sites known so far); nothing downstream of the `ret` in program order is ever reached from here |
| `seq` | 0 | purely structural — whatever "current state" processing `s1` left you at becomes the input to processing `s2` |
| `ifElse` | 3 | two entry states (epsilon from current state, one per branch), one end state — epsilon into the end state **only** from branches that fell through, **never** from branches that returned |
| `whileDo` | 2 | header = the current state (reused, not new); epsilon from header to a new "inside" state and a new "outside" state; the loop body's own final state gets an epsilon back to the header (closing the loop) |

Confirmed: "processing a statement" is a function from one "current state" to
one "current state" — even `ifElse`/`whileDo`, despite allocating several
internal states, resolve back to a single state (the end-state /
outside-state) that whatever's sequenced next continues from. A branch's own
processing (however deeply nested) always closes to exactly one such state,
or terminates via `ret` instead (never both, never neither, never more than
one).

### 4.2 Why this fixes the §1 store issue "for free" — but only if state values are per-state, not projected after the fact

**This was the user's own question, and the answer is yes.** The `ifElse`
end-state's epsilon edges come *only* from non-returning branches. A `ret`
transitions straight to the enclosing function's continuation sites, bypassing
the end-state entirely. So the state representing "whatever comes after the
`if`" structurally has no incoming edge from a path that returned — unlike
`main`'s current `[If-Then-Else]`, which joins *both* branches into one
result regardless of outcome kind, which `[Sequence Cont]` then blindly
continues from.

This only actually buys anything if each automaton **state carries its own
abstract heap/store/reg**, computed dataflow-style: joined (`⊔`) only over
the edges that actually, structurally, lead into it. If the automaton were
merely a trace-shaped side artifact sitting on top of the *current*
structural big-step semantics (heap/sto/reg still computed the old way), none
of this would help — the fix has to be in how state (not just the trace) is
threaded. **Confirmed with the user**: yes, per-state dataflow, this is the
right, and only, way this resolves the issue.

Per-edge semantics (confirmed): since `assign`/`binOp`/`objLit`/`setTaint`/
`setSink` allocate no states, their effects live on whichever edge crosses
them — i.e. each edge conceptually carries a (possibly empty) straight-line
code fragment, applied to the source state's value before joining into the
target. This reuses the same per-statement update rules `ABigStep` already
has (weak heap/reg updates, strong store update), just applied edge-locally
instead of recursively over the whole program.

### 4.3 Shared entry states, widening, and the "no store needed" resolution

The shared entry state for a function must be sound for *every* caller
simultaneously. Confirmed: its value is exactly "params ↦ union of every call
site's argument sets," and everything downstream inherits that by ordinary
propagation — no bespoke mechanism beyond "some states have more incoming
edges than others, using the same join everywhere." As more call sites are
discovered (including recursive ones), the union grows and the body must be
re-analyzed against the wider input; this is confirmed as the source of the
"reeval with larger args" step seen in the worked examples.

Return values (confirmed, user's own choice after weighing precision vs.
simplicity): **over-approximate**. Every `Ret` edge out of a function carries
the *entire* accumulated return-value set for that function (union of every
`return` statement's value, everywhere in the function), not something
precise per return-site. This matches how every other abstract domain in this
project already works (`AOut`, `ASummary.ret` are single joined
over-approximations, not path-precise) — consistency, not just convenience,
was the deciding factor.

**Resolution of the original open question this whole branch was spun up
to investigate:** the user, independently, confirmed they only actually need
`Trc.Alpha`/`Heap.Alpha`/`Reg.Alpha` related at the end — not the store,
"because it will no longer be used." This is the *same* conclusion as §2's
fix, reached from the automaton side. One correction made to the user in
conversation and worth repeating here: it has to be **conditional on `.cont`**,
not "drop always," or the inductive composition (a `.cont` state's store being
read by whatever's sequenced after it) breaks. §2's fix is what to actually
implement for this on `main`; it does not require anything in this handout.

## 5. What's still open (do not assume answers to these — ask)

1. **Declarative vs. operational formalization** (settled: declarative). Do
   not formalize the iterative widening/fixpoint-search algorithm itself
   (growing `Call sites`/`Return sites`/`Continuations` sets, re-analysis
   triggers) or prove it terminates. Instead: define what makes a graph a
   *valid* automaton for a program (closure conditions — every registered
   call site has an edge to its function's shared entry carrying at least the
   args that reach it, every return site has an edge to every continuation
   carrying at least the accumulated return set, etc. — a generalization of
   `SigmaValid`'s post-fixed-point style to a whole simultaneous system, not
   one function at a time), and prove *any* graph satisfying those
   conditions over-approximates the concrete semantics. Finiteness comes from
   the *state space's type* (derived from the program's finite syntax, §4.1),
   not from an algorithm-termination argument.

2. **The exact Lean state type.** Something like a sum indexed by `Idx`/`Fid`,
   e.g. roughly `AState := EntryState (f : Fid) | ContState (callSite : Idx)
   | ActionState (site : Idx) | IfThenEntry (site : Idx) | IfElseEntry (site
   : Idx) | IfEnd (site : Idx) | WhileInside (site : Idx) | WhileOutside
   (site : Idx)` — not yet drafted or reviewed with the user. Start here, but
   check every constructor against §4.1's table and the worked examples
   before trusting it.

3. **§3.1's mutual-recursion fix (named/simultaneous `mu`-summaries) is
   `main`-only — it does NOT apply to, and is not needed by, the automaton.**
   This was checked explicitly with the user and is worth over-stating so it
   doesn't get re-confused later: named/nested `mu`-variables are *still*
   the same non-regular, stack-needing construct as the balanced system in
   §3.2 (that's what a "named" version of it would literally be, if built
   the same way) — fine for `main`'s `Prop`-valued `Trc.Alpha`, which was
   never trying to be finite/decidable, but exactly what the automaton
   exists to avoid. The automaton's own answer to mutual recursion is
   entirely different and has no version of the §3.1 bug to begin with: one
   *shared* entry state per function (not "per assumed variable"), reached
   the same way regardless of who's calling, with return-sites
   cross-producted to every continuation (§4.1/§4.3). There is no binder to
   mis-scope, because there is no binder — just a bounded set of graph nodes
   and edges. Do not try to build the automaton's recursion handling out of
   named `mu`/`tvar`; that would silently reintroduce the exact
   non-regularity §3.2 rules out. Treat §3.1 as a separate, `main`-only
   fix, unrelated to this branch's actual design (§4).

4. **Relationship to `main`.** This branch's automaton work is additional,
   parallel work motivated by finiteness/decidability for the downstream
   query-checker — it is not a prerequisite for finishing Theorem B15 as
   currently scoped on `main` (§2's fix suffices for that, independent of
   everything here). Confirm with the user whether/when to merge, or whether
   this stays a long-running separate track.

5. Nothing about `[Binary Operation]`/`[Object Literal]`'s `α`-growth
   (allocation sites), `[Call-Fix]`'s post-fixed-point search, or the
   ascending-chain-condition machinery already in
   `CoreJsAbstractionSoundness.lean` has been reconsidered against the
   automaton model yet. Don't assume it transfers unchanged.

## 6. Preliminary implementation plan (once the above is confirmed with the user)

1. Define `Idx`-derived (or similar) finite state type per §4.1's table;
   validate every constructor against the worked `f`/`g` and `h(x)` examples
   by hand before writing any semantics.
2. Define the automaton's edges (epsilon and action-labeled) and per-edge
   transformation semantics (§4.2), reusing existing `AHeap`/`ASto`/`AReg`
   update definitions where the corresponding statement already has one.
3. Define per-state abstract values as a labeling `AState → AHeap × ASto ×
   AReg` (or similar), and "valid labeling" as a declarative closure
   condition over every edge (§5.1) — no algorithm, no termination proof.
4. Define trace-relatedness (`Trc.Alpha`-equivalent) for paths through this
   graph, replacing/subsuming `ATrc.tvar`/`mu`'s role — likely need to resolve
   §3.1's named-variable question as part of this, since call/return edges
   are exactly where that bug lives.
5. Restate and prove a Theorem-B15-equivalent against this structure. Expect
   to reuse essentially all of the non-call-related generation lemmas already
   proved on `main` (`abs_gen_skip`/`assign`/`ret`/`setTaint`/`setSink`/`seq`/
   `lookupS`/`lookupD`) for the per-edge transformation proofs in step 2 — the
   underlying single-statement/single-edge reasoning doesn't change, only how
   edges compose into a whole-program structure changes.
