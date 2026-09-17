# Design and implementation plan: the call-string automaton trace model

This document supersedes `HANDOUT.md` (removed by this commit). It records
the full outcome of a design session held on this branch
(`automaton-trace-model`): every decision made, the reasoning behind it, the
concrete design that follows from those decisions, and an ordered
implementation plan. Read it top to bottom before writing any Lean — later
sections depend on earlier ones.

**Status: design only. No Lean has been written yet.** This document is
itself the deliverable of the session; implementation starts from §5.

## 1. Why this branch exists, and its relationship to `main`

While proving Theorem B15 (`analysis/CoreJsAbstractionSoundness.lean`,
`soundnessN`) on `main`, the `[Sequence]` case hit a genuine gap: `s1 ;; s2`
can have `s1` return concretely while the abstract analysis of `s1`
(imprecisely) says `.cont`, because `[If-Then-Else]` joins a returning branch
with a continuing one into a single outcome. When that happens, `s2` gets
analyzed against a store that has nothing to do with the real, never-executed
`s2` — `Sto.Alpha` becomes unprovably false for that case, not just hard to
prove.

Two things happened after this branch was created, independently of it:

- `main` implemented the fix for exactly that problem (conditioning
  `Sto.Alpha` on the outcome being `.cont`). This is `main` commit `7b23138`.
- `main` then went further and adopted a **reduced-scope language**
  (`2fff359`): calls are syntactically direct (no first-class functions),
  `return` occurs exactly once, at the end of a function body, and recursion
  is banned outright via a rank function. This sidesteps the original
  problem by construction, and `main` now has a complete, `sorry`-free
  soundness proof for that reduced scope.

**This branch does not build on either of those `main` changes.** The
decision (made explicitly, this session) is that this branch keeps pursuing
the *general* language this branch already has: calls through variables
(functions are first-class-ish, resolved via `IsCandidate`), `return` at any
point in a function body, and recursion (direct and mutual). `main`'s
reduced-scope proof is a separate, parallel deliverable; the two are not
being reconciled. If a future session wants to merge them, that is a fresh
decision to make then, not a consequence of this plan.

Separately from the `[Sequence]` store issue, the actual motivation for
*this* branch is that the paper's downstream security-query search algorithm
needs the analysis's own output to be a **finite-state automaton** — not an
implementation convenience, but load-bearing for decidability (revisiting a
`(program-state, query-state)` pair must be how the search terminates). The
current `ATrc` (`emp | act | seq | alt | star | tvar | mu`) is not that: it is
exact regular-language-generating machinery for *one* self-recursive
function, and is provably unsound for mutual recursion as currently wired
(see §1.1 below) — quite apart from not being finite at all once you try to
use it as the tool's actual output model.

### 1.1 A pre-existing, separate soundness gap (not addressed by this plan)

`[Call-Fix]`/`[Call-Assume]` (`ACallBranch`/`ASummary`/`ASigma` in
`CoreJsAbstractSemantics.lean`) assume/discharge summaries one function at a
time, in whatever order recursion is encountered. For mutual recursion this
mis-scopes the anonymous recursion variable `tvar`/`mu` — a concrete
worked example (`f`/`g` calling each other) shows the μ-binder that should
belong to `f`'s recursion ends up captured by `g`'s `[Call-Fix]` instead,
because it closes last. This is a real, independent bug in the *current*
`main`-lineage machinery (before this branch touches anything), needing named
per-function summary variables assumed *simultaneously* for a whole
call-graph SCC. It is **not** fixed by the automaton design below — the
automaton's own recursion handling (§4) has no binder to mis-scope at all
(shared entry states, not named recursion variables) and so has no version of
this bug to begin with. Flagging it here only so it isn't rediscovered and
confused with automaton work later; it would need its own fix if the
old μ-trace machinery were ever revived, which this plan does not do.

## 2. Scope of this document

Agreed explicitly this session: this document plans **only** the state type,
the automaton's edges (and their per-edge value transformations), and what a
"valid labeling" of the resulting graph means (steps 1–3 of the original
handout's preliminary plan). It does **not** plan:

- How the abstraction relation `∼α` (Def. B8) generalizes to per-state
  relatedness and to paths through the graph.
- Restating and proving a Theorem-B15-equivalent soundness result against
  this structure.
- How an exported/entry-point function's own unconstrained parameters get an
  initial label (the "what code gets analyzed and how does the environment
  get built" question). The user does not intend to implement this at all —
  the goal is proving totality and soundness of the abstract semantics given
  an already-well-formed input, not building a whole-program entry-point
  discovery convention.

The first two are real, necessary follow-up work; they are deferred to a
*later* planning pass, once the state/edge/labeling design below exists as
actual Lean and can be pointed at concretely instead of guessed at. Their
eventual file homes are already named (decision 11): the generalized
abstraction relation goes in `CoreJsAutomatonRelation.lean`, and the
soundness-plus-totality result in `CoreJsAutomatonSoundness.lean`.

## 3. Decisions made this session, with justification

Recorded in the order they were settled, since several later decisions
correct or refine earlier ones — read this as a log, not a flat list.

1. **Base model.** Build against this branch's current, general
   `CoreJsSyntax`/`CoreJsSemantics`/`CoreJsAbstractSyntax`/
   `CoreJsAbstractSemantics` (calls via variables, `IsCandidate` resolution,
   `return` anywhere, recursion via `ASigma`), not against `main`'s
   reduced-scope rewrite. *Why:* the automaton exists specifically to make
   recursion's state space finite; a scope that has already banned recursion
   has no need for it.

2. **What's reused vs. replaced.** `ASto`/`AHeap`/`AReg`/`AAct`, `⊑`, `⊔`, and
   the `Join` typeclass stay as they are — nothing about how a heap, store or
   register value looks, or how they're ordered/joined, changes. `ATrc`
   (`tvar`/`mu`/the regex constructors), `AOut`, `ASummary`, `ASigma`,
   `ACallBranch`, and the corresponding cases of `ABigStep`/`soundnessN` are
   deleted outright and replaced by the automaton — not kept in parallel.
   *Why:* keeping the old μ-trace machinery as a "sharper Prop-level fact"
   alongside the automaton (an option considered and declined) would mean
   maintaining two abstract semantics and eventually two soundness proofs,
   for no payoff once the automaton exists — and the old machinery has the
   mutual-recursion bug of §1.1 regardless.

3. **Outcomes.** `AOut` (the `.cont`/`.ret`-tagged type, with its totalized
   join) disappears entirely as a type. Whether a given piece of control flow
   "returned" or "continued" is purely a structural fact about which states
   and edges exist and are reachable in the graph — never a value carried on
   a result. *Why:* this is what the automaton gives for free (§4.2 below)
   and is *exactly* what would have avoided the original `[Sequence]` store
   problem in the first place: a returning `if`-branch never gets an edge
   into whatever continues, so nothing downstream ever has to "know" a
   branch returned via a tagged value — it simply has no path from it.

4. **Site identity.** Every construct that needs a unique per-occurrence
   identity in the automaton (`call`, `lookupS`, `lookupD`, `updateS`,
   `updateD`, `ifElse`, `whileDo`) gets an explicit `Idx` field added to its
   `Stmt` constructor, exactly mirroring the existing precedent set by
   `binOp`/`objLit`'s `κ`. This needs a new well-formedness side condition —
   site indices pairwise distinct across all relevant occurrences in a
   program — analogous to `EnvSpec`/`ConcreteSpec`, and a `REMARK` noting
   this is a deliberate deviation from the paper's Fig. A1 syntax. *Why:*
   the alternative (deriving site identity structurally from AST position,
   without touching `CoreJsSyntax.lean`) was raised but not pursued once the
   call-string discovery (below) made clear that a bare per-occurrence index
   isn't sufficient identity anyway — call sites need to combine with a
   call-string, and an explicit syntactic index composes with that far more
   simply than a derived path type would.

   **Not re-confirmed after the call-string discovery** — flagged explicitly
   so it isn't silently assumed: this was the recommended option going in,
   and everything decided afterward is consistent with it, but there was no
   final explicit sign-off once the design moved on. Worth a one-line check
   before starting implementation.

5. **Call-string-based instantiation (the central discovery of this
   session).** Reading `HANDOUT.md`'s §4.1 table literally — "callee-entry is
   shared across all call sites to that function" — is wrong for anything
   beyond a single self-recursive function. Worked through with concrete
   examples, the actual rule is:

   - A **non-recursive** call (target `Fid` not already open on the current
     call path) gets a **fresh** instantiation: a new entry state *and* a
     new continuation state, and this freshness propagates transitively
     through everything the callee itself calls, all the way down (confirmed
     with a diamond example: `top` calls `A` twice non-recursively; `A` has
     one lexical call site to `C`; `C` still gets *two* instantiations, one
     nested under each of `A`'s two instantiations — not one shared `C`).
     This is full call-string sensitivity (closer to unbounded-depth
     call-string/1-CFA than to a flat "one entry per function"), not the
     naive globally-shared, argument-unioned entry the handout's table
     literally describes.
   - A **recursive** call (target `Fid` already open on the current call
     path) does *not* create a new instantiation. It **does** still create
     a fresh continuation state for that call site (continuations are
     *never* shared, recursive or not — confirmed directly in the worked
     `f`/`g` example: the initial call to `f` and the recursive call to `f`
     from inside `g` get two different continuations, `s2` and `s6`, both
     targeting the *same* shared entry `s1`). The Call edge for the
     recursive occurrence targets the entry state of that `Fid`'s *first*
     (outermost) open occurrence on the current call path — not a fresh one.

   *Why this is right, and still finite:* the call graph, once each
   recursive/mutually-recursive cluster is collapsed to a point, is a finite
   DAG (`Γ`'s domain is finite — `EnvSpec.fin`). Duplicating per call-string
   rather than per bare call site is what preserves precision for the
   non-recursive case (each of `A`'s two invocations gets its own, exact
   argument values, rather than being joined together the way the naive
   shared-entry reading would force) — and finiteness survives because no
   `Fid` can repeat within one call-string (the moment it would, recursion
   kicks in and the call-string stops extending), so every call-string has
   length at most `|dom(Γ)|`.

6. **Indirect/multi-candidate calls.** A call site whose callee expression
   might resolve to several functions (calls through a variable) gets a
   **structural, static** edge to *every* arity-matching `Fid` in `Γ`'s
   (finite) domain — always present in the graph, regardless of whether it
   will turn out plausible for a given execution. Whether an edge actually
   contributes anything to its target is gated by an `IsCandidate`-style
   check evaluated against *the source state's own label* — this lives
   entirely inside that edge's contribution function (an ordinary
   `if IsCandidate(...) then {params ↦ args} else ∅`), not as a separate
   "liveliness" property attached to states or edges anywhere. Confirmed
   against two worked examples (`apply(fn, v) { return fn(v); }` called as
   both `apply(inc, 1)` and `apply(dec, 2)`; and an exported `h(x) { x(); }`
   where `x` could denote any nullary function in scope). *Why:* since `Val`
   has no dynamic function creation (a `.fid` value can only originate from a
   literal in source text) and `Γ`'s domain is finite, the full candidate set
   at any call site is already a static, syntactic fact — nothing about
   resolving it needs to wait for any value or fixpoint.

7. **`ret` edges are unconditional — the *only* directional asymmetry with
   call edges.** A `ret` inside a given instantiation gets an edge to *every*
   continuation state structurally reachable via the call-string mechanism
   (every call site whose call-string, after truncation, lands on this exact
   entry), carrying that function's **entire accumulated return-value set**
   (over-approximated — every return site's value is unioned together, not
   tracked per return-site; this matches how every other abstract domain in
   this project already over-approximates, e.g. `AOut.retLocs`/`ASummary.ret`
   today). No `IsCandidate`-style gating on the `ret` side: once you are
   inside a body producing a return, every continuation the call-string
   mechanism connects you to is, by construction, one that could have called
   you.

8. **Top-level `ret` is banned**, the same way JavaScript treats a
   syntactically invalid `return` outside a function as a `SyntaxError`. No
   distinguished top-level sink state is needed as a consequence — `ret`
   only ever occurs inside a function body, so it always has a real,
   non-empty set of continuations to fan out to. The top level itself is
   simply the call-string `[]`; it needs no distinguished state of its own
   either (exactly as today's `SA` needs no special state for its initial
   `AHeap.bot`/`ASto.bot`/`AReg.bot` — it's a premise, not a node).

9. **`ifElse` allocates 3 states, matching `HANDOUT.md`'s original table —
   an earlier reading of the worked traces as "0 states" was wrong.** Two
   branch-entry states are always allocated (epsilon-reached from the
   incoming state, one per branch); a third, join state is allocated **only
   if at least one branch continues** (does not return), with epsilon edges
   into it only from the branch(es) that actually continue. The reason
   neither worked trace initially *appeared* to show separate branch-entry
   states is that in both, exactly one branch returned and the other
   continued trivially (no actions of its own) straight through — the
   *printed* trace elides that, but the states are logically still there.
   This is confirmed by a third worked example where *both* branches
   continue, where the branch-entry and join states are unambiguously
   present. *Why this needs no value-dependent gating either:* "does this
   branch return" is not evaluated by inspecting the guard (never inspected,
   matching the existing doc comment) — it falls out structurally from
   letting a compound statement's processing resolve to a *set* of open
   (dangling) states rather than a single one. A leaf that ends in `ret`
   contributes to the enclosing function's `Ret`-fanout and nothing else; a
   leaf that doesn't contributes to whatever the next real action allocates.
   This composes correctly through arbitrarily nested `if`/`while` without
   needing anything like the old `AOut.kind`.

10. **Declarative, not operational — re-affirmed after a direct stress
    test.** `HANDOUT.md` had already settled this in principle; this session
    re-derived *why* it still holds even given a fully worked, genuinely
    procedural description of the analysis algorithm (states discovered as
    call sites are encountered; argument locations "deferred" until a
    callee's return set stabilizes; re-analysis triggered by argument-set
    growth; final "materialization" once a fixpoint is reached). The
    resolution: **the state and edge set is entirely static** — a function
    of `Γ`'s call graph alone, closed under the call-string truncation rule,
    with no reference to any value or analysis result (see decisions 5–6).
    Only the **labeling** (the abstract heap/store/register value living at
    each state) is fixpoint-dependent, and that is exactly the same kind of
    existential `[While]`/`[Call-Fix]` already rely on today — "some
    post-fixed point exists" — just generalized from one independent unknown
    per loop/summary to one *simultaneous* system of inequalities over the
    whole reachable state graph at once (Tarski/Kleene's fixpoint theorem
    doesn't care that the domain is now a big product instead of one small
    lattice). The worklist/re-analysis-on-widening procedure described this
    session is the (deliberately unformalized, exactly as already decided)
    *algorithm* for finding such a fixpoint — not evidence that one can't be
    characterized declaratively.

11. **File naming: track paper figures, not implementation churn.** `main`
    kept its existing filenames through a comparably dramatic rewrite because
    its reduced-scope model still *is* Fig B1/B6/B7's content, just with
    fewer constructors. The automaton's state/edge/labeling machinery is not
    from any paper figure at all — it's this branch's own contribution — so
    it gets its own, clearly-labeled files rather than being folded into
    files whose header comments claim to be literal transcriptions of
    Appendix B. Concretely: `CoreJsAbstractSyntax.lean`/
    `CoreJsAbstractSemantics.lean` are *kept*, trimmed back to what's still
    actually Fig B1/B4/B5 and Fig B6 (domains, order, join, expression
    evaluation, and the per-statement value-update math with no control-flow
    content — everything decision 2 already said gets reused). Fig B7's
    *control-flow* rules (`seq`/`ifElse`/`whileDo`/`call`/`ret`), which the
    automaton replaces outright, move to new files: `CoreJsAutomatonSyntax.lean`
    (`CallString`, `AState`) and `CoreJsAutomatonSemantics.lean` (edges,
    per-edge contributions, labeling, validity) for this session's scope;
    later, `CoreJsAutomatonRelation.lean` and `CoreJsAutomatonSoundness.lean`
    for the deferred phase (§2).

12. **Totality, for the deferred phase: aim for a non-trivial witness, not
    `main`'s `⊤`-shortcut.** `main`'s `SA_total` gets existence for free by
    noting `⊤` is trivially a post-fixed point of any monotone transformer —
    cheap, but the witness it produces is maximally imprecise by
    construction. The better-established alternative, standard in the
    abstract-interpretation literature: Kleene-iterate the whole-graph
    transformer from `⊥` (`F(⊥), F(F(⊥)), ...`); the ascending chain cannot
    rise forever because the state space is finite and each component
    domain satisfies the ascending chain condition (already partly
    scaffolded in `CoreJsAbstractionSoundness.lean`'s "Termination of the
    fixpoint search" section — `AFinite`, `AscendingHeap`, etc.); so it must
    stabilize at some finite `n` with `F(F^n(⊥)) ⊑ F^n(⊥)`, which is exactly
    the post-fixed point `[While]`/`[Call-Fix]`-style rules need, and is
    additionally *not* forced to be `⊤` the way starting from `⊤` is.
    Whether it ends up strictly more precise than `⊤` isn't something to
    promise as a theorem about every well-formed program (a sufficiently
    loose widening threshold could still legitimately bottom out at `⊤` for
    some programs) — only that the method doesn't manufacture triviality the
    way the shortcut does. This is a generic mathematical existence
    argument, not a formalization of the worklist/reeval procedure walked
    through by hand this session (§3, decision 10 still holds: the search
    algorithm itself stays unformalized) — it requires real additional proof
    work (building the iteration, proving monotone ascent, invoking ACC for
    termination) beyond `main`'s shortcut, but reuses groundwork already
    partly in place. Deferred to the same later planning pass as the rest of
    §2 — recorded here now so it isn't re-litigated as "is this even
    possible" when that pass starts.

## 4. The concrete design

### 4.1 Syntax changes (`CoreJsSyntax.lean`)

Add an `Idx` (site identifier) field to: `call`, `lookupS`, `lookupD`,
`updateS`, `updateD`, `ifElse`, `whileDo` — joining `binOp`/`objLit`'s
existing `κ`. Add a well-formedness predicate (new, analogous to
`EnvSpec`/`ConcreteSpec`) requiring every one of these indices, together with
existing `κ`s, to be pairwise distinct across a program (`Stmt`/`Env`). Add a
`REMARK` at the syntax file's existing `REMARK`-collection point noting this
deviates from the paper's literal Fig. A1.

**Mechanical ripple:** `CoreJsSemantics.lean`'s `BigStep`/`BigStepN` pattern
matches on these constructors need the new binders added (unused by the
concrete semantics, exactly as `κ` already is not consumed by anything except
the allocator). `Stmt.lits` needs no change (it doesn't inspect these
fields).

### 4.2 `CallString` and `AState`

```
-- one call-site index paired with the target Fid actually taken there;
-- no Fid may repeat (well-formedness, needed for both correctness of the
-- "reuse the first/outermost occurrence" rule and for finiteness)
abbrev CallString := List (Idx × Fid)

inductive AState where
  | action    (cs : CallString) (site : Idx)  -- lookupS/lookupD/updateS/updateD
  | cont      (cs : CallString) (site : Idx)  -- call continuation; always fresh per call site
  | entry     (cs : CallString)               -- body-start; cs's own last element is (site, f);
                                               -- two entry states are equal iff their call-strings are
  | ifThen    (cs : CallString) (site : Idx)
  | ifElseB   (cs : CallString) (site : Idx)
  | ifEnd     (cs : CallString) (site : Idx)  -- only ever reachable if ≥1 branch continues; always
                                               -- exists as a constructor, reachability is a graph fact
  | whileIn   (cs : CallString) (site : Idx)
  | whileOut  (cs : CallString) (site : Idx)
```

`skip`, `assign`, `binOp`, `objLit`, `setTaint`, `setSink`, `seq`, and `ret`
allocate no state of their own (see §4.3). The top level uses `cs = []`.

`entry`'s sharing rule, as a function on call-strings — given a current
call-string `cs` and a new call `(site, f)`:

```
targetCallString cs site f :=
  if f ∈ (cs.map Prod.snd) then
    -- truncate right after f's first occurrence: reuse that instantiation
    cs.takeWhile (fun p => p.2 ≠ f) ++ [cs.find (fun p => p.2 = f)]  -- (sketch; exact
                                                                      --  Lean formulation TBD in implementation)
  else
    cs ++ [(site, f)]
```

The exact Lean formulation of the truncation (likely via `List.takeWhile` +
a lookup, or a small helper recursion) is left to implementation — the
*specification* above (truncate to the prefix ending at `f`'s first
occurrence) is what's settled.

**Finiteness.** No `Fid` repeats within a `CallString`, so its length is
bounded by `|dom(Γ)|` (finite by `EnvSpec.fin`), and `Idx`/`Fid` are each
finite per program — giving a finite `AState` type for any fixed, finite
program. This is the formal counterpart of `AFinite`/the ascending-chain
groundwork already sketched in `CoreJsAbstractionSoundness.lean`, now
applying to the *state space* rather than just `ALoc`.

### 4.3 Edges and per-edge contributions

Each row: what states/edges the construct contributes, and what value
transformation (a function of the source state's own label) travels along
its edge(s). Reuses the existing `AHeap`/`ASto`/`AReg` update definitions
from `CoreJsAbstractSemantics.lean` wherever the corresponding statement
already has one — this is the "some parts might be reused" the user
identified: the actual value-update math for `assign`/`binOp`/`objLit`/
`lookupS`/`lookupD`/`updateS`/`updateD`/`setTaint`/`setSink` does not change,
only how it's attached (edge-locally, instead of via a recursive judgement
over whole configurations).

| Construct | States | Edges / contribution |
|---|---|---|
| `skip`, `assign`, `binOp`, `objLit`, `setTaint`, `setSink` | none | no new state; effect folded into whichever edge crosses this point in the statement sequence (the edge's contribution function composes this statement's existing update definition) |
| `seq s1 s2` | none | purely structural: `s1`'s own exit state(s) become the state(s) `s2`'s own processing starts from |
| `lookupS`/`lookupD`/`updateS`/`updateD` | 1 (`action`) | edge in from the current state, carrying the lookup/update action and its existing effect |
| `ifElse` (site) | 2 always (`ifThen`, `ifElseB`); a 3rd (`ifEnd`) iff ≥1 branch continues | epsilon edges from the current state into both branch-entries; each branch processed independently from there; epsilon into `ifEnd` only from branch(es) that continue — no value-dependent gating, purely structural (which leaves end in `ret` vs. not) |
| `whileDo` (site) | 2 (`whileIn`, `whileOut`); header is the *current* state, reused, not new | epsilon from current state to both `whileIn`/`whileOut`; body processed from `whileIn`; body's own continuing exit state(s) epsilon back to the header; `whileOut` is where whatever's sequenced next continues from |
| `ret e` | none | edge(s) out from the current state to *every* continuation state whose call-string, after truncation, targets this exact entry; contribution is the function's entire accumulated return-location set (unconditional, over-approximated — see decision 7) |
| `call x e es` (site) | 1 always (`cont`, fresh per call site); `entry` fresh or reused per decision 5 | for every arity-matching `f ∈ dom(Γ)`: a structural edge from the current state to `entry(targetCallString cs site f)`, contribution `if IsCandidate(...) then {params ↦ args} else ∅` (decision 6); the call's own continuation state receives the union of all live candidates' return contributions the same way `ret` targets it |

### 4.4 Labeling and validity (step 3)

A labeling is a total function `L : AState → AHeap × ASto × AReg` (or an
equivalent structure bundling the three, mirroring `AConf`/`ARes`'s existing
shape). A labeling is **valid** when, for every structural edge `e : s → s'`
with contribution function `C_e`, `C_e(L(s)) ⊑ L(s')` — i.e. `L(s')` must
dominate the *join*, over every edge landing at `s'`, of that edge's
contribution computed from its own source's label. This is a direct,
whole-graph generalization of the per-statement weak/strong update rules
already in `CoreJsAbstractSemantics.lean`, and of the post-fixed-point
condition `[While]`/`[Call-Fix]` already check today — just stated once, as
one property of one labeling over the whole reachable state graph, rather
than function-by-function or loop-by-loop.

**Declarative, existential, no algorithm formalized** (decision 10): the
top-level result this session is aiming toward (though its exact Lean
statement is deferred to the next planning pass, per §2) is of the shape
"there exists a valid labeling `L`" — analogous to today's `SA` existentially
quantifying the final heap/register/outcome. Nothing about *finding* `L` (the
worklist/re-analysis-on-widening procedure worked through by hand this
session) is modeled; only its existence, and that any labeling satisfying
the validity condition above soundly over-approximates every concrete
execution, is what gets proved.

## 5. Implementation plan

Ordered; each step should type-check on its own before moving to the next.

1. **`CoreJsSyntax.lean`.** Add the new `Idx` fields (§4.1). Add the
   site-distinctness well-formedness predicate. Update the file's own doc
   comments / add the `REMARK`.
2. **`CoreJsSemantics.lean`.** Mechanical: thread the new unused `Idx`
   binders through `BigStep`/`BigStepN`'s pattern matches and the
   `.mono`/`.toN`/`.toBigStep` lemmas that case on every constructor.
3. **New file `CoreJsAutomatonSyntax.lean`** (naming mirrors the existing
   `CoreJsSyntax`/`CoreJsAbstractSyntax` convention). Defines `CallString`
   (+ its well-formedness and the `targetCallString` truncation function)
   and `AState`, plus whatever finiteness instance (`AFinite AState`, or
   similar) is provable directly from `EnvSpec.fin` and the no-repeat
   invariant. Imports `CoreJsSyntax` and `CoreJsAbstractSyntax` (for `AHeap`/
   `ASto`/`AReg`, reused unchanged).
4. **New file `CoreJsAutomatonSemantics.lean`.** Defines the edge/
   contribution functions per §4.3 (reusing `CoreJsAbstractSemantics.lean`'s
   existing `weakSetVal`/`weakSetObj`/`ASto.upd`/`aevalE`/etc. wherever
   applicable), the labeling type, and the validity condition of §4.4.
5. **Trim `CoreJsAbstractSyntax.lean`/`CoreJsAbstractSemantics.lean`.**
   Remove `ATrc`'s `tvar`/`mu` constructors (keep `emp`/`act`/`seq`/`alt`/
   `star` only if anything downstream still needs a plain regex trace type —
   otherwise remove `ATrc` entirely once it's clear nothing references it),
   `AOut`, `ASummary`, `ASigma`, `ACallBranch`, and the corresponding
   `ABigStep` constructors (`ifElse`'s outcome-joining shape, `call`/
   `callNone`'s `AOut`-producing shape, `whileDo`'s outcome-carrying shape,
   `ret`). Delete the now-vacuous `soundnessN` cases that only existed to
   handle those (`seqRet`'s `sorry`, the call-related "remaining work" items
   6). Keep `assign`/`binOp`/`objLit`/`lookupS`/`lookupD`/`updateS`/
   `updateD`/`setTaint`/`setSink`'s definitions — they're exactly what §4.3
   reuses.
6. **Validate against the worked examples** (§6 below) by hand: for each,
   confirm the `AState`/`CallString` values the design produces match what
   was traced, and that a labeling satisfying §4.4's validity condition
   against those states reproduces the same heap/store/register values the
   trace computed. Do this *before* trusting the design enough to build the
   next phase (trace-relatedness/soundness) on top of it.
7. **Stop here for this plan.** Steps 4–5 of the original preliminary
   plan (trace/path-relatedness generalizing `Trc.Alpha`, and restating +
   proving a Theorem-B15-equivalent) are deliberately out of scope for this
   document (§2) and need their own planning pass once 1–6 above exist as
   real Lean.

Decision 4 (site identity via explicit `Idx` fields, not a derived
AST-position path) has since been explicitly re-confirmed after the
call-string discovery reframed the problem it was originally answering — no
longer a loose end.

## 6. Worked examples (reference material for step 6 above)

Reproduced verbatim from the session, as hand-traced by the user. Any
implementation of §4 must reproduce these.

### 6.1 Mutual recursion: `f`/`g`

```js
function f(x) {
  if (x) {
    var z = !x;
    var u = g(z);
  } else {
    return 0;
  }
  return 1;
}

function g(y) {
  var x = f(y);
  var z = x + 1;
  return z;
}

module.exports = f
```

```
f (function)   -> l_0
x (f.params.1) -> l_1
g (function)   -> l_2
z = !x         -> l_3
0              -> l_4
1              -> l_5
z = x + 1      -> l_6

Initial call to f (entry point as given in exports)
| Args f : 0 -> l_1
| Ret f :
| Call sites f : s0
| Return sites f :
| Continuations f : s2
| Body start f = s1

Starting evaluation on body start (s1) with store configured by args:

[If True - line 4]
s1 -> s3 <UnOp(l_3, .not, f.args)>  [line 5]
New function evaluation (G)        [line 6] --> Pending analysis when finishing f
| Args g : 0 -> l_3
| Ret g :
| Call sites g : s3
| Return sites g :
| Continuations g : s5
| Body start g = s4

[If False - line 4]
Register new return site for f with new values [line 8]
| Args f : 0 -> l_1
| Ret f : l_4
| Call sites f : s0
| Return sites f : s1
| Continuations f : s2
| Body start f = s1

[Only the top branch escapes the loop at s5 (the return from the call to g)]
Register new return site for f with new values [line 10]
| Args f : 0 -> l_1
| Ret f : l_4, l_5
| Call sites f : s0
| Return sites f : s1, s5
| Continuations f : s2
| Body start f = s1

--- Analysis of g (starting at s4)
Register new call site for f WITH NEW ARGS [line 14] --> Need reeval of f
| Args f : 0 -> l_1, l_3
| Ret f : l_4, l_5
| Call sites f : s0, s4
| Return sites f : s1, s5
| Continuations f : s2, s6
| Body start f = s1
s6 -> s7 <BinOp(l_6, .plus, f.ret, {l_5})>  [line 15]
Register new return site for g [line 16]
| Args g : 0 -> l_3
| Ret g : l_6
| Call sites g : s3
| Return sites g : s7
| Continuations g : s5
| Body start g = s4

--- Reeval of f (larger args)

[If true - line 4]
s1 -> s3 <UnOp(l_3, .not, f.args)>  [line 5]
Function g called with the same arguments, nothing changes    [line 6]
| Args g : 0 -> l_3
| Ret g : l_6
| Call sites g : s3
| Return sites g : s7
| Continuations g : s5
| Body start g = s4

[If false - line 4]
Return site for f with no new return values
| Args f : 0 -> l_1, l_3
| Ret f : l_4, l_5
| Call sites f : s0, s4
| Return sites f : s1, s5
| Continuations f : s2, s6
| Body start f = s1

Return site for f with no new return values
| Args f : 0 -> l_1, l_3
| Ret f : l_4, l_5
| Call sites f : s0, s4
| Return sites f : s1, s5
| Continuations f : s2, s6
| Body start f = s1

--- Analysis finished, automaton generated:
s0 -> s1 <Call(l_0, [{l_1, l_3}])>
s1 -> s2 <Ret(l_0, {l_4, l_5})>
s1 -> s3 <UnOp(l_3, .not, {l_1, l_3})>
s1 -> s6 <Ret(l_0, {l_4, l_5})>
s3 -> s4 <Call(l_2, [{l_3}])> (Calls to g do not widen, no need to reevaluate the body of g)
s4 -> s1 <Call(l_0, [{l_1, l_3}])>
s5 -> s2 <Ret(l_0, {l_4, l_5})>
s5 -> s6 <Ret(l_0, {l_4, l_5})>
s6 -> s7 <BinOp(l_6, .plus, {l_4, l_5}, {l_5})>
s7 -> s5 <Ret(l_2, {l_6})>
```

### 6.2 Simple early return: `h(x)`

```js
function h(x) {
  if (x) {
    return 1;
  }
  w = 2;
  return w;
}

module.exports = h
```

```
h  (function) -> l_0
x  (h.args.0) -> l_1
1             -> l_2
2             -> l_3

Initial call to h:
| Args h : 0 -> l_1
| Ret h :
| Call sites h : s0
| Return sites h :
| Continuations h : s2
| Body start h = s1

[If true - line 131]
Add return site to h with new values [line 132]:
| Args h : 0 -> l_1
| Ret h : l_2
| Call sites h : s0
| Return sites h : s1
| Continuations h : s2
| Body start h = s1
<Branch does not continue>

[If false - line 131] (implicit, continue at s1 after if)

s1 -> s3 <Assign('w', l_3)> [line 134]
Add return site to h with new values [line 135]:
| Args h : 0 -> l_1
| Ret h : l_2, l_3
| Call sites h : s0
| Return sites h : s1, s3
| Continuations h : s2
| Body start h = s1

No other functions/recursive calls to analyse, generated trace:
s0 -> s1 <Call(l_0, [{l_1}])>
s1 -> s2 <Ret(l_0, {l_2, l_3})>
s1 -> s3 <Assign('w', l_3)>
s3 -> s2 <Ret(l_0, {l_2, l_3})>
```

Note: this trace has both `ifElse` branches apparently sharing state `s1`
directly (no separate `ifThen`/`ifElseB` visible) — this is the case that
initially misled the design toward "`ifElse` allocates 0 states." It works
out because the `false` branch here has no actions of its own before
reaching the assignment, so its (logically separate) branch-entry state has
no distinguishing effect and is elided in the printed trace. See §6.3 for a
case where both branch-entry states and the join state are all visible.

### 6.3 Both branches continue, with a deferred (recursive) argument: `f(x,y)`/`g(x)`

```js
function f(x, y) {
  if (x) {
    z = g(y);
  } else {
    z = false;
  }
  return z;
}

function g(x) {
  return !f(false, x)
}
```

Analysis starts at `f`. Initial state `s0`; `f`'s body start registered as
`s1`, `f`'s continuation as `s2`.

Processing from `s1`: two states are generated immediately, one per `if`
branch; a third (the join) is generated because at least one branch (in fact
both) does not return.

- **True branch:** registers a new call site to `g`. States for `g`'s body
  start and continuation are created, but `g` is not analyzed yet — the
  store records that `z` holds `g`'s return value, but the `ALocSet` is
  *deferred* until `g`'s analysis completes (recursion inside `g` can still
  grow it). The branch does not return, so its last state links to the
  if-join state with an epsilon transition.
- **False branch:** no states of its own; the store records `z ↦ {l_false}`.
  Does not return either, so it also links to the if-join state.
- Neither branch returns, so the join takes the union of both branches'
  heap/store/etc. (had one returned, the join would instead simply carry the
  non-returning branch's state, unchanged — no merge).
- `return z` at the join registers a new return site and return locations
  for `f`.

Worklist now analyzes `g` (registered but not yet visited): `g` registers a
new call site back to `f`, with `f`'s first argument's `ALocSet` now widened
(includes the location for the literal `false`). Because the arguments grew,
`f` is queued for re-analysis with the wider arguments; this repeats until a
fixpoint (guaranteed by the allocation strategy). Only once the fixpoint is
reached are the deferred, argument-dependent transitions materialized into
concrete `ALocSet`s.

This example is what settled decision 10 (declarative is still viable: the
*states* here — `g`'s entry/continuation — are created the moment their call
site is seen, before any value is known, confirming state/edge existence is
structural; only the *label* at those states is what the worklist is
iterating to a fixpoint).

### 6.4 Indirect/multi-candidate calls

```js
function f() { return true }
function g() { return false }
function h(x) { x() }
```

Analysis starting at `h`: since `x` is supplied from outside (an
unconstrained parameter), the call `x()` must consider every nullary
function in scope — `f` and `g` — as a candidate, i.e. a choice/fan-out edge
to each. This confirmed decision 6: the fan-out itself (which candidates
exist at all) is a static fact about `Γ`'s arities, not something requiring
any value to be known first; only whether each candidate edge actually
*contributes* anything is value-gated.
