# TODO — Review items for the automaton implementation

This file is **not** an implementation log like `PROBLEMS.md` — it records
*proposed* changes and extensions to the automaton model
(`CoreJsAutomaton*.lean`), identified during an interactive walkthrough of
that model with the user, that have not yet been implemented. Nothing here
should be assumed to already be true of the code.

Each entry states: the intent behind the change, the concrete design decided
on (including alternatives considered and rejected during discussion), a plan
for implementing it, the limitation(s) of the current implementation it
addresses, and any sub-decisions still open at the time of writing that a
future implementation pass will need to pin down.

---

## Entry 1 — Re-add action labels (`AAct`) to automaton edges; gate call/return
edges on `IsCandidate`; establish a well-formed `Fid`↔`ALoc` correspondence

**Status:** design only, not implemented.

### Intent

`PROBLEMS.md` Decision 2 deliberately dropped `AAct`-style action labels from
`AEdge` for the first implementation pass — edges carry only a value
transform `C : AConf → AConf`, no label — because `DESIGN_AND_PLAN.md` §2
explicitly scoped that pass to state/edge/labeling only and deferred
trace/path-relatedness (and the query language that consumes it) to a later
pass. This entry *is* that later pass's first step.

The target result this is building toward: **every execution record
producible by a concrete execution is matched by a walk through the
automaton**, related via the abstraction relation between concrete and
abstract locations — a path-level, existential counterpart to the state-level
soundness theorem already proved (`step_sound`/`sound`/`sound_top` in
`CoreJsAutomatonSoundness.lean`). This is the actual payoff of the automaton
design in the first place (`DESIGN_AND_PLAN.md` §1: the paper's downstream
security-query search algorithm needs to walk a finite-state automaton), not
yet realized by the current, unlabeled edges.

### Design

**1. `AAct` — the abstract action type.** Mirrors concrete `Act`
(`CoreJsSemantics.lean`: `lookup`/`update`/`call`/`ret`), with every location
argument widened to an `ALocSet` — *except* the callee/function-identity
position of `call` and `ret`, which stays a single `ALoc` (justified by
decision 4 below: functions get a canonical, one-to-one location, so there is
nothing to over-approximate there). A fifth constructor, `.epsilon`, is added
for structurally silent transitions:

```
inductive AAct where
  | lookup (l₁ l₂ l₃ : ALocSet)
  | update (l₁ l₂ l₃ : ALocSet)
  | call   (lf : ALoc) (ls : List ALocSet)
  | ret    (lf : ALoc) (l : ALocSet)
  | epsilon
```

**2. Where the label lives, and its type.** `AEdge` gains a field
`ℓ : AConf → Option AAct`, alongside the existing `C : AConf → AConf` — so
`AEdge Γ cs entry pending s a b C ℓ`. Three distinct outcomes, deliberately
not collapsed into two:

- `none` — this specific edge instance is **not walkable** at this
  configuration (its guard failed). Produced only by `callEntry`/`callRet`/
  `callImplicitRet` when `IsCandidate` is false.
- `some .epsilon` — **always walkable**, contributes no action to the trace.
  Used unconditionally by every purely structural edge: `ifThen`/`ifElseB`/
  `ifThenJoin`/`ifElseBJoin`/`whileHeaderIn`/`.whileHeaderOut`/`whileBackIn`/
  `.whileBackOut`/`callPassThrough` (`seqLeft`/`seqRight` just forward
  whatever label the recursed-into edge already carries, they don't
  introduce a new one).

  > **Overruled for `callPassThrough` (interactive walkthrough, see
  > `WALKTHROUGH_PLAN.md`, change 4).** `callPassThrough` is labelled `none`,
  > not `some .epsilon`: it still contributes to `cont`'s label (the caller's
  > locals), but no walk may take it. As `epsilon` it let a walk skip a call
  > entirely — no `call` action, no callee actions — while arriving at a
  > `cont` whose label includes the callee's return, so e.g. a query with
  > `except call(sanitize, …)` would match every sanitized flow (systematic
  > false positives). Soundness never walks through it (the call case walks
  > `callEntry` → body → `callRet`), and `Valid` ignores labels.
- `some (.lookup/.update/.call/.ret ...)` — walkable, contributes a genuine
  action, computed from the accumulated `pending c` the same way `C` already
  is (and, for `callRet`/`callImplicitRet`, from `rpending c`/`ypending c`
  for the returned value).

An earlier version of this design used only `Option AAct` with no `.epsilon`
constructor, treating `none` as "no action" for *both* structural edges and
failed guards — rejected during discussion because a walk relation reading
only `ℓ c` couldn't distinguish "always free to take" from "blocked right
now," which would let a walk sneak into a non-candidate function's entry by
treating the failed guard as if it were a free epsilon step.

**3. Closing Decision 7's imprecision — gate `callRet`/`callImplicitRet` on
the *same* `IsCandidate` check as `callEntry`.** Currently (`PROBLEMS.md`
Decision 7) a return's edge into `cont` is unconditional — "every
continuation the call-string mechanism connects to is one that *could* have
called you." Sound for the value-soundness direction (over-approximation is
harmless there), but too imprecise for the walk-matching goal: if call site
`B` never actually calls `f` at a given configuration, a walk should not be
able to "return" into `B`'s own `cont` just because some *other* call site
legitimately invoked `f` and shares the same `entry`. Fix: both `callRet`'s
and `callImplicitRet`'s `C` (not just `ℓ`) get the same guard, evaluated
against the *same* call-site configuration `callEntry` already uses
(`pending c` — the configuration arriving at this call statement):

```
fun c =>
  let vc := pending c
  if IsCandidate Γ vc.heap (aevalE vc.sto e) es.length f then
    let v := rpending c   -- ypending c for callImplicitRet
    { ... real contribution, as today ... }
  else AConf.bot
```

with `ℓ` following the same branch (`some (.ret ...)` / `none`). This is a
genuine tightening of `C`, not just of `ℓ` — the soundness proof's already-
proved `callRet`/`callCont` cases will need re-checking against it.

**4. A well-formed one-to-one correspondence between `Fid` and `ALoc`.**
Needed to make `.call`/`.ret`'s callee position a single `ALoc` meaningful:

- **(a)** `litLocA` restricted to `{.fid f | f ∈ dom Γ}` is a bijection onto
  its image (distinct functions get distinct canonical locations, and every
  function has one — the latter is automatic from `litLocA`'s totality, the
  content here is the injectivity). Static, instance-level — belongs in
  `AbstractSpec`, parallel to `allocA_site`.
- **(b)** every valid label keeps `h.val (litLocA (.fid f)) = {.fid f}`
  exactly — nothing else ever joins into a function's canonical location.
  State-dependent, unlike (a), so needs either a new conjunct in
  `Labeling.Valid`, or a lemma that every edge's `C` preserves it (closed
  over by `AnalysisResult`). Left to whoever implements this to determine
  which is more natural once attempted — flagged as open below.
- **(c)** no value-producing transform can manufacture a `.fid` value at a
  fresh location: `∀ op V₁ V₂ f, ¬ (opSemA op V₁ V₂).Mem (.fid f)`, added to
  `AbstractSpec`. (Confirmed with the user: `opSemA` may still be *invoked
  with* `.fid`-valued operands — JavaScript allows functions as binop
  operands — it must simply never *produce* one.) Separately needs checking
  that `allocA`'s image never coincides with `litLocA`'s image on `.fid`
  values — i.e. a fresh allocation can never accidentally land on a
  function's reserved location — not yet verified against the existing
  `AbstractSpec`/`ConcreteSpec`.

**5. Labels are computed generically; "the fixpoint" enters only by
application.** `ℓ`, like `C`, stays a plain function `AConf → Option AAct`,
defined uniformly for any configuration — nothing new is needed to make it
"fixpoint-aware." Once a valid labeling `L` (`Labeling`/`Labeling.Valid`,
`CoreJsAutomatonSemantics.lean:513–524`) is fixed, the actual, materialized
action at a specific edge `a → b` is `ℓ (L a)`. This is also why `ℓ`'s
`ALocSet` arguments are automatically the over-approximated sets the
fixpoint computes — no separate mechanism is needed beyond `ℓ` being defined
the same way `C` already is.

**6. The eventual walk/path relation and its connection to `Trc` — sketched,
not designed here.** Needs its own pass once 1–5 type-check, since it's what
actually exercises whether the label design above is right, but the target
shape: a *walk* is a sequence of `AEdge` steps starting at `entry []`, where
a step through edge `(a, b, C, ℓ)` is legal at running abstract configuration
`c` iff `ℓ c ≠ none`; the walk's own trace is the sequence of `some act`
values encountered along it (`.epsilon`s contribute nothing); the target
theorem relates this trace, via the abstraction relation extended pointwise
to `Act`/`Trc` (parallel to the `Act.Alpha`/`Trc.Alpha` that
`CoreJsAutomatonRelation.lean`'s header already flags as having "no
counterpart here," lines 10–19), to every concrete execution record's own
trace.

### Plan

1. Add `AAct` to `CoreJsAutomatonSemantics.lean` (near `AHeap`/`ASto`/`AReg`,
   mirroring `Act`'s placement in `CoreJsSemantics.lean`).
2. Add the `Fid`↔`ALoc` well-formedness pieces (4a, 4c) to `AbstractSpec`
   *before* touching `AEdge` — `.call`/`.ret`'s labels need
   `litLocA (.fid f)` to already be meaningful.
3. Add `ℓ` as a new field to every `AEdge` constructor: `some .epsilon` for
   the purely structural ones; `some (.lookup/.update ...)` for `lookupS`/
   `lookupD`/`updateS`/`updateD` (unconditional — no guard); the
   `IsCandidate`-gated `Option` for `callEntry`/`callRet`/`callImplicitRet`,
   including the `C` tightening of decision 3 for the latter two.
4. Re-check `Labeling.Valid`/`AnalysisResult` need no change (they shouldn't
   — `ℓ` doesn't participate in the `⊑` inequality, only `C` does), but
   confirm the `callRet`/`callImplicitRet` `C` change doesn't break the
   closure argument anywhere.
5. Re-run the soundness proof's `callRet`/`callCont` cases
   (`CoreJsAutomatonSoundness.lean`) against the tightened `C`. These are two
   of the already-proved cases; confirm they still go through — the guard
   should be dischargeable precisely because the proof already knows, from
   the concrete premise, exactly which `f` was really called (the same way
   it already discharges `callEntry`'s `IsCandidate` obligation).
6. Add invariant 4(b), landing wherever step 2's investigation determines it
   belongs.
7. Only then: design the walk/path relation and the `Act.Alpha`/`Trc.Alpha`
   extension (decision 6) — a separate, later pass.

### Limitations of the current implementation this addresses

- No way to relate an automaton path to a concrete `Trc` at all — the
  current model can only certify value-soundness at individual states, not
  that a matching *execution* exists (`PROBLEMS.md` Decision 2's explicit,
  intentional gap for this phase).
- `callRet`/`callImplicitRet`'s unconditional fan-out (`PROBLEMS.md`
  Decision 7) is sound but avoidably imprecise for path-level reasoning —
  harmless for `Labeling.Valid` alone, but would let a constructed
  "matching walk" claim a return to a call site that never actually made the
  call.

### Open sub-items (not blocking this plan, flagged so they aren't silently assumed)

- Exact home for invariant 4(b): a `Labeling.Valid` conjunct vs. a
  separately-proved preservation lemma.
- Whether `allocA`'s image is already known (or provable) to avoid
  `litLocA`'s image, or needs a new disjointness assumption added somewhere.
- Whether gating the walk relation by `ℓ (L a)` (the fixpoint's own,
  over-approximated value) vs. by a specific real run's actual configuration
  needs an extra monotonicity lemma about `IsCandidate` — informal argument
  from the design discussion: `IsCandidate` should be monotone in the heap
  (heap components only grow under join), so gating against `L a` should
  never block a step a genuine matching witness needs; worth confirming as
  an actual lemma once the walk relation is written, not just assumed. This
  same concern applies one level up, to call-string reachability, not just
  candidate liveness — see the discussion under `Labeling.Valid`'s closure
  scope (`CoreJsAutomatonSemantics.lean:515-518`): a call-string that is
  concretely unreachable can still receive a non-`bot` abstract label purely
  from ordinary over-approximation, so a walk gated by `L a` could in
  principle enter a call-string-unreachable instantiation, not just a
  non-candidate one. Not a new hazard (it's the same, already-accepted kind
  of imprecision as everywhere else in the system), but the walk relation's
  eventual definition should account for it explicitly rather than by
  accident.

---

## Entry 2 — Restate soundness as a walk-matching theorem: every concrete
execution record is matched by a walk through the labeled automaton

**Status:** design only, not implemented. **Blocked on Entry 1** (needs
`ℓ`-equipped edges to exist first — a walk is a sequence of `AEdge` steps
gated by `ℓ`, so there is nothing to walk until Entry 1 lands) **and on
resolving `step_sound`'s existing `binOp`/`objLit` `sorry`s** — see
"Dependency on the pre-existing `binOp`/`objLit` gap" below. That gap is not
new work this entry introduces; it predates this whole walkthrough, but this
entry cannot be completed without it resolved.

### Intent

The existing soundness theorem (`step_sound`/`sound`/`sound_top`,
`CoreJsAutomatonSoundness.lean`) is **state-level**: it relates a concrete
execution's *final* heap/register to a valid labeling's value at whatever
automaton state the execution structurally lands on. It says nothing about
*how* the execution got there — no relation to the sequence of actions along
the way. That's exactly the gap Entry 1's labels exist to close, and this
entry is the theorem that actually exercises them.

Target statement, in the user's own framing (recorded here since it's the
clearest statement of it): every execution record produced by a concrete run
is matched by a walk through the automaton, transformed by an abstraction
relation between concrete and abstract locations, where:

- the execution's **heap and register** relate to a **single, fixed**
  abstract counterpart — the configuration at the walk's own final state
  (this half is not new work — it is exactly what `step_sound`/`sound`
  already establish; the "fixed counterpart" framing is just a precise way
  of stating what those theorems already do);
- the execution's **trace** relates to the **walk itself** — the sequence of
  the program's concrete `Act`s corresponds, pointwise and in order, to the
  sequence of non-`.epsilon` `AAct` labels encountered along the walk (this
  half is genuinely new — it needs the `Act.Alpha`/`Trc.Alpha` extension
  `CoreJsAutomatonRelation.lean`'s own header already flags as having "no
  counterpart here," lines 10-19).

### Design

1. **A walk** is a finite sequence of `AEdge` steps, starting at `entry []`
   (the top-level program's entry) and ending at whatever state `s₀`'s own
   `AExit` fact designates (well-defined because top-level `ret` is banned —
   `DESIGN_AND_PLAN.md` decision 8 — so `s₀` always has a genuine,
   non-returning exit to end at). Each step carries a running configuration
   forward by composing `C`s, and is legal only when `ℓ c ≠ none` at that
   configuration (Entry 1's gating).

   Function calls need no special-casing here, worth recording so it isn't
   re-derived from scratch later: `callRet`/`callImplicitRet`'s edge is
   sourced exactly at `r`/`y`, the state *inside* the callee where the
   return/fall-through actually happens — not at the call site. So a walk
   can only take that edge after it has already stepped `callEntry` →
   through the callee's own internal edges (naturally recording everything
   the callee does along the way) → reached `r`/`y`. Plain "follow any
   `AEdge` sourced at the current state" already produces the complete,
   correct trace through a call, with no extra machinery needed.

2. **`Act.Alpha`/`Trc.Alpha`** — pointwise extension of the existing
   `AlphaFn`-based relation (`CoreJsAutomatonRelation.lean`) to actions, e.g.
   `Act.Alpha α (.lookup l₁ l₂ l₃) (.lookup L₁ L₂ L₃) := α.MapsInto l₁ L₁ ∧
   α.MapsInto l₂ L₂ ∧ α.MapsInto l₃ L₃`, similarly for `.update`/`.call`/
   `.ret` (the latter two using Entry 1's `Fid`↔`ALoc` well-formedness for
   the callee position). `Trc.Alpha` then relates `t.toList` to the walk's
   own non-`.epsilon` label sequence, elementwise, in order.

3. **The target theorem**, shape TBD precisely, but structurally: for a
   valid `AnalysisResult`, every `BigStep`-derivable run of `s₀` has *some*
   walk and *some* `α` such that the run's trace `Act.Alpha`-relates to the
   walk's non-epsilon labels in order, and the run's final heap/register
   `Heap.Alpha`/`Reg.Alpha`-relate to the walk's final configuration.

### Relationship to the existing state-level soundness proof

Not a replacement — an extension. `step_sound`'s existing induction (on
`BigStepN`'s derivation height, threading `hvalidS`) already establishes
exactly the heap/register-relatedness half, state by state. The new proof
most likely reuses the same inductive shape, but additionally accumulates
the walk/trace witness alongside the relatedness fact at each step, instead
of discarding it once the next state is reached. Expect every case —
including the 15 already proved — to need revisiting, since the statement
itself is strictly stronger, even where the underlying argument carries
over.

### Dependency on the pre-existing `binOp`/`objLit` gap

Not new work this entry introduces — `step_sound`'s `binOp`/`objLit` cases
were already left as `sorry` before any of this walkthrough, needing an
`α`-freshness invariant: proof that a freshly-allocated concrete location
isn't already in `α`'s domain, so it can be safely added to it. That gap is
orthogonal to labels/trace-matching and could, in principle, be tackled
entirely independently of Entries 1/2.

But this entry has a *hard*, not merely thematic, dependency on it: a walk's
own `.lookup`/`.update` labels can reference locations that were freshly
allocated earlier in the *same* run (e.g. `y := x + 1; z := y.p` — the
lookup's location came from the preceding `binOp`). `Trc.Alpha` relating
such an action correctly requires `α` to already have been extended at that
earlier allocation. Since this entry's proof is built by the same kind of
induction over `BigStepN` as `step_sound` (just carrying more data through),
it has a `binOp`/`objLit` case too, and that case is stuck on exactly the
same obstacle the existing `sorry`s are — so this entry cannot be completed
until that gap is resolved, even though the gap's own content has nothing to
do with this entry's subject matter.

**Design of the fix**, worked out during this walkthrough:

`step_sound`'s induction (`CoreJsAutomatonSoundness.lean:113`) carries
`AConf.Alpha α c (pending (L entry))` as its relatedness hypothesis and
produces an extended `α' ≥α α` at the end of each case, but nothing in the
current signature relates `α`'s domain to the current concrete heap
`c.heap` — that's the missing piece. `ConcreteSpec.allocC_fresh`
(`CoreJsSemantics.lean:254`) only promises the freshly-allocated location
`l = allocC h κ` is *undefined in the current heap* (`h.val l = none ∧
∀ p, h.obj l p = none`), not "beyond some threshold" — so the invariant to
add is the mirror image: **every location in `α`'s domain is defined in the
current concrete heap** (call it `AlphaFn.DefinedIn α c.heap`). Given that,
`allocC_fresh` directly gives `l ∉ dom(α)` by contradiction, which is
exactly what justifies extending `α[l ↦ allocA c.heap κ]` safely.

This invariant needs two things to survive the induction:
- **At the start**: trivial — `α`'s domain is initially just the literals
  (`α.Lits`), all defined in `Heap.init s` by `Heap.WF`.
- **Preserved at every step**: needs a new lemma, "a location defined in
  `c.heap` stays defined in `r.heap`" along a `BigStep` derivation. Not
  proved anywhere yet, but there is an exact template to copy:
  `BigStep.finite` (`CoreJsSemantics.lean:769`) proves the analogous fact
  for heap *finiteness* by induction on the `BigStep` derivation itself,
  using the per-operation lemmas (`Heap.Finite.setVal`/`.setObj`/
  `.setObjs`) at the leaves and just forwarding the IH through composite
  rules (`seqCont`, `callRet`/`callCont`, etc.). A
  `BigStep.heap_defined_mono`-shaped lemma would have the identical
  structure, tracking "`l` defined" instead of "heap finite."

Once `l ∉ dom(α)` is established, the rest of `binOp`'s case needs a new
`Heap.Alpha.setVal` lemma, using `OpSemSound` — already threaded as a
hypothesis into `step_sound` (`opspec : OpSemSound`, currently unused) — to
relate `opSem op v₁ v₂` to `opSemA op V₁ V₂`. `objLit`'s case needs the same
freshness argument but no `OpSemSound` (no binop involved), just
heap/store/reg relatedness for `weakSetObjs`.

Note `Heap.Alpha.setVal` is not quite "parallel to `Heap.Alpha.setObj`/
`.setObjV`" the way that might first sound: those two keep the *same* `α`
throughout, since `updateS`/`updateD` write to an already-existing
location — no fresh allocation involved. `setVal` is different in kind: it
has to extend `α` *and* update the heap simultaneously, since `binOp`
allocates fresh. Worth not underestimating it as a copy-paste of the
existing pattern — it needs the `DefinedIn`-based extension argument above
folded in, which the existing two lemmas never had to do.

### Plan

1. Land Entry 1 first (blocking).
2. Resolve `step_sound`'s existing `binOp`/`objLit` `sorry`s — also
   blocking, independent of Entry 1's content, but required before step 5
   below can proceed past those two statement shapes:
   1. Define `AlphaFn.DefinedIn α h` (every location `α` maps is defined in
      `h`) in `CoreJsAutomatonRelation.lean`.
   2. Prove `BigStep.heap_defined_mono`, mirroring `BigStep.finite`'s proof
      shape (`CoreJsSemantics.lean:769`) exactly.
   3. Thread `AlphaFn.DefinedIn α c.heap` through `step_sound`'s induction
      as a new hypothesis, established at the base case from `Heap.WF` and
      maintained via `BigStep.heap_defined_mono` at every step.
   4. Use it with `ConcreteSpec.allocC_fresh` to justify the `α` extension
      at `binOp`/`objLit`'s fresh allocation.
   5. Add `Heap.Alpha.setVal` (parallel to `Heap.Alpha.setObj`/`.setObjV`),
      using the already-threaded `OpSemSound` hypothesis for `binOp`.
   6. Complete both cases' store/register relatedness and discharge the two
      `sorry`s.
3. Add `Act.Alpha`/`Trc.Alpha` to `CoreJsAutomatonRelation.lean`.
4. Define the walk type/relation itself (a new inductive, or a
   list-of-edge-facts structure — home and exact shape TBD). If this ends up
   in a new file, remember to add its module name to `lakefile.toml`'s
   `globs` (`CLAUDE.md`'s own warning — a file not listed there is silently
   skipped by `lake build`).
5. Restate `step_sound`'s induction to also produce/extend a walk witness at
   each case, not just a relatedness fact — including, now, the `binOp`/
   `objLit` cases resolved in step 2.
6. Re-examine whether `sound`/`sound_top`'s existing wrapping still makes
   sense as-is, or should be subsumed by the new theorem entirely.

### Limitations this addresses

The current soundness theorem only ever says "the final values are
covered" — it says nothing about how the run got there, which is exactly
what any downstream query/model-checking consumer needs (e.g. "does a
tainted value flow from a lookup to a sink" is inherently a trace-level
question, not a final-state-level one).

### Open sub-items

- Exact representation of "a walk" — a list of `AEdge` facts, or a
  dedicated inductive relation (`AWalk`, mirroring `BigStep`'s own shape)?
  Left open.

---

## Entry 3 — Prove `exists_valid_labeling` (totality): a valid labeling
actually exists for any well-formed `(Γ, s₀)`

**Status:** design only, not implemented. **Independent of Entries 1/2** —
does not touch labels, the `Fid`↔`ALoc` invariant, or the walk/`Trc`
relation at all, and can be tackled before, after, or in parallel with them.
One interaction worth noting: if Entry 1's invariant 4(b) ends up added as a
new `Labeling.Valid` conjunct (one of the two options Entry 1 leaves open),
this entry's transformer and its stabilization argument would need to
account for that extra conjunct too — worth settling Entry 1's own
invariant-4(b) home before finalizing this entry's transformer definition,
even though the two pieces of work are otherwise unrelated.

### Intent

Prove `exists_valid_labeling` (currently `sorry`, `CoreJsAutomatonSoundness.
lean`) — that a valid labeling actually *exists* for any well-formed
`(Γ, s₀)`, not merely that soundness holds *if* one does. Per
`DESIGN_AND_PLAN.md` decision 12, the goal is a non-trivial witness via
Kleene iteration from `⊥`, not `main`'s "cheap `⊤`" shortcut — `⊤` is
trivially a post-fixed point of any monotone transformer, so it proves
existence for free, but the witness it produces carries zero analysis
information and is useless for anything downstream.

### Design (following `DESIGN_AND_PLAN.md` decision 12)

1. Restrict `AState` to a genuine finite type (a `Fintype`-style instance or
   equivalent), built from `CallString.length_le` (already proved,
   `CoreJsAutomatonSyntax.lean`). `PROBLEMS.md` decision 1 notes the
   finiteness *argument* already exists but does not confirm an actual
   finite-type instance has been built — this is the first prerequisite
   step, not yet done.
2. Define the whole-graph monotone transformer `F : Labeling → Labeling`,
   `F(L)(b) = ` the join, over every edge `C` landing on `b`, of `C(L(a))` —
   mirroring `Labeling.Valid`'s own "join over incoming edges" reading
   directly.
3. Prove `F` is monotone (`⊑`-preserving).
4. Iterate `F` from `⊥` (the constant-`⊥` labeling): `F(⊥), F(F(⊥)), ...`;
   prove the resulting chain is ascending.
5. Invoke an ascending-chain-condition argument (each component domain —
   `ALocSet`/`VSet`/`AHeap`/`ASto`/`AReg` — satisfies ACC over a finite state
   space) to prove the chain stabilizes at some finite `n`. Partially
   scaffolded already in the old (now-deleted, per `CLAUDE.md`)
   `CoreJsAbstractionSoundness.lean`'s "Termination of the fixpoint search"
   section (`AFinite`, `AscendingHeap`, etc.) — since those files are gone,
   this groundwork would need to be recovered from git history or rebuilt
   from scratch, not reused directly.
6. The stabilized value `Fⁿ(⊥)` is the witness: prove it satisfies
   `Labeling.Valid` (a post-fixed point is valid by construction of `F`).
7. Specifically confirm (per `CoreJsAutomatonSoundness.lean`'s own
   "Remaining work" note) that this witness satisfies the `whileBackIn`/
   `.whileBackOut` edges' inequalities introduced by `PROBLEMS.md` decision
   8's fix — not expected to be a problem, but explicitly worth confirming
   rather than assuming, given that fix was itself a correction to an
   earlier, subtler bug that no worked example caught.

### Plan

As the design steps above, in order (1 through 7).

### Limitations this addresses

Currently there is no proof that any `(Γ, s₀)` has a valid labeling at
all — every soundness result (`step_sound`/`sound`/`sound_top`, and the
eventual Entry 2 theorem) is conditional on "given a valid labeling `L`,"
with no guarantee one exists. Without this, the whole development proves
nothing unconditionally.

### Open sub-items

- Whether the old `CoreJsAbstractionSoundness.lean`'s ACC-related
  scaffolding (`AFinite`, `AscendingHeap`) is recoverable from git history
  or needs rebuilding from scratch, since the files themselves are now
  deleted (per `CLAUDE.md`).
- Whether "monotone ascent" needs to separately account for the gated
  contributions Entry 1 introduces (`IsCandidate`-style `if`-`then`-`else`
  branches) — these should still be monotone, since `IsCandidate` itself
  should be monotone in the heap (the same argument already sketched in
  Entry 1's open items), but worth confirming explicitly rather than
  assuming, given this project's own history of exactly this kind of silent
  gap (`PROBLEMS.md` decisions 3, 7, 8).

---

## Entry 4 — Cleanup: retire the design documents, de-paper the comments,
write a standard README

**Status:** design only, not implemented. **Blocked on every entry above**
(and on any further entry this file gains before implementation starts) —
this only runs once `lake build` is green and `grep -n sorry analysis/*.lean`
is empty, i.e. once the automaton development is actually finished, not
merely once Entries 1-3 as currently written are done.

### Intent

`DESIGN_AND_PLAN.md` and `PROBLEMS.md` are artifacts of an *active design
process* — a session log and a decision log — not documentation of a
finished system. Once the automaton development they were guiding is
actually complete and `sorry`-free, they stop being the right thing for a
reader (human or agent) to be pointed at: `CLAUDE.md` currently tells
readers to consult them before touching automaton code, but a finished
deliverable should be legible from its own code and comments plus a README,
the way `CoreJsAutomatonSyntax.lean`'s header already insists it is "not a
transcription of any figure in the paper: it is this branch's own
contribution" — extending that same self-containedness to the rest of the
repository, and to its relationship with the external paper, once the work
that justified the design documents' existence is done.

### Plan

1. **Confirm the gate.** `lake build` green, `grep -n sorry analysis/*.lean`
   empty, every entry above (and any added later) implemented. Do not start
   the rest of this entry before this holds.
2. **Delete `DESIGN_AND_PLAN.md` and `PROBLEMS.md`** (via normal `git rm` /
   commit, so they remain recoverable from git history — not a claim that
   their content should be preserved anywhere in the working tree, e.g. as
   a condensed "history" section somewhere; the user's instruction was to
   remove them outright, and git history is where prior-state recovery
   belongs, not a live document).
3. **Sweep every file under `analysis/`** — confirmed broad: not just the
   automaton files. A survey during this walkthrough found 38 paper
   citations (`Fig.`, `Def.`, `Appendix`, `Lemma B*`, literal "the paper")
   across 10 of the 13 files, concentrated in `CoreJsSemantics.lean` (12),
   `CoreJsAutomatonRelation.lean` (9), and `CoreJsAutomatonSemantics.lean`
   (8), so this is a genuinely repository-wide pass, not one scoped to the
   files this particular walkthrough covered. They fall into two kinds,
   handled differently:
   - **Organizational headers** — section names/labels mirroring the
     paper's own structure for cross-reference (e.g. `## Semantic domains
     (Fig. A2)`, `Lemma B9`/`B10`/`B11`/`B13` labels on this repo's own
     theorems). Just drop the citation and keep a plain description; nothing
     is lost (`## Semantic domains`).
   - **Substantive fidelity explanations** — comments that justify an
     implementation choice *by* comparing it to the paper (e.g.
     `Heap.setObjs`'s note that it updates left-to-right rather than
     simultaneously, "which agrees with [the paper] when the `pᵢ` are
     pairwise distinct"). **Confirmed rule: keep the underlying reasoning
     for the implementation decision, rewritten to stand alone, whenever
     the reasoning is more than just "because this is how the paper does
     it."** Only strip outright the ones whose sole content *is* "the paper
     does it this way" with no independent justification of their own.
   - Removing now-stale references to `DESIGN_AND_PLAN.md`/`PROBLEMS.md`
     (e.g. `CoreJsAutomatonSemantics.lean`'s header currently cites
     "Decisions 1, 2, 3, 4, 5"; `CoreJsAutomatonSoundness.lean`'s currently
     describes "18 of the 19" cases and lists specific `sorry`s — both will
     be wrong once this development is finished).
   - Checking every remaining comment is accurate against the code as it
     actually stands post-implementation, fixing whatever drifted.
   - Adding a comment only where something genuinely non-obvious (a hidden
     invariant, a subtle reason for a specific formulation) would otherwise
     confuse a reader — not filling in explanatory comments generally; this
     project's own commenting style is already deliberately sparse.
4. **Update `CLAUDE.md`.** At minimum: remove the "Two design documents
   live at the repository root" paragraph and every other reference to
   `DESIGN_AND_PLAN.md`/`PROBLEMS.md` (including in the `sorry` policy
   section); rewrite the "Architecture" section's per-file descriptions to
   reflect the finished state (no more "Incomplete", no more listing
   specific remaining `sorry`s, since there are none).
5. **Write `README.md`** — a standard top-level README, distinct in
   audience from `CLAUDE.md` (which stays as agent-facing operational
   guidance and can reference the README rather than duplicate it): what
   this repository is and what it proves, the file structure and how the
   pieces depend on each other, build/compile instructions (`lake build`,
   toolchain via `elan`), and any other information a new reader (not
   necessarily an AI agent) would need to get oriented.

### Limitations this addresses

Right now, understanding *why* the code looks the way it does requires
reading two large, discussion-log-style documents that reference "the
paper" throughout — appropriate for an active design session, not for a
finished, self-contained deliverable someone encounters cold.

### Open sub-items

None remaining — scope and the rewrite-vs-strip rule were both confirmed
during this walkthrough (see the plan's step 3 above).
