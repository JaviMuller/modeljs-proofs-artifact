# Implementation decision log — TODO.md entries 1–4

This document records, for the implementation of `TODO.md`'s four entries,
the places where `TODO.md` left something open, where its sketch turned out
not to work as written and had to be changed, and where a real difficulty
came up. It follows `PROBLEMS.md`: a numbered log written while the work was
being done, in the order the decisions came up. Each entry gives where the
decision applies, the gap, the alternatives considered, and the decision
taken, so a reader who disagrees can go back to that specific point.

---

## Decision 1 — the gated return edges must read the *caller's* label, so contributions and labels take the whole labeling

**Where:** `CoreJsAutomatonSemantics.lean`, `AEdge` (every constructor's
`C`/`ℓ` indices), in particular `callRet`/`callImplicitRet`. TODO.md Entry 1,
design item 3.

**The gap.** TODO.md sketches the gated return contribution as

```
fun c => let vc := pending c
         if IsCandidate Γ vc.heap (aevalE vc.sto e) es.length f then
           let v := rpending c ...
```

with `c` the edge's source label. But a return edge's source is `r`/`y`, a
state *inside the callee*, and `pending` is the *caller's* transform from
the caller's `entry`. `pending (L r)` applies the caller's pending effects to
the callee's configuration and evaluates the callee expression `e` in the
callee's store, where it usually does not even occur. Implemented as written,
the guard is false for most real calls. The contribution then collapses to
`AConf.bot`, and the already-proved `callRet`/`callCont` soundness cases
become unprovable, and in fact false: `cont`'s `x` slot no longer receives
the returned locations.

A source-label-only contribution `AConf → AConf` cannot express the intended
guard. The guard needs the caller's configuration at the call site
(`pending (L entry)`), and the returned value needs the callee's
(`rpending (L r)`). These are the labels of two different states.

**Alternatives considered.**
- Leave the return edges unguarded (the pre-TODO state). Rejected: this is
  exactly the imprecision Entry 1 set out to remove. A walk could then return
  into a call site that never made the call.
- Add a new automaton state per (call site, callee) pair, so that one state
  carries both configurations. Rejected: that state's label would have to
  merge a caller store and a callee store, which are different variable
  namespaces. It would also add states that no worked example has.
- Keep `C : AConf → AConf` and add a separate guard `g : Labeling → Prop` to
  every edge. Rejected: `ℓ` needs the same guard to return `none`, so it has
  to see the labeling anyway. Two different shapes of function per edge buys
  nothing.
- **Chosen:** every edge's `C` has type `Labeling → AConf` and its `ℓ` has
  type `Labeling → Option AAct`. Most edges read only their source's label
  (`fun L => pending (L entry)`, etc.). The two return edges read
  `pending (L entry)` for the guard and `rpending (L r)`/`ypending (L y)` for
  the value. `Labeling.Valid` becomes `C L ⊑ L b`. The guard is the same
  predicate as `callEntry`'s, factored out as `AConf.Calls`.

**Consequences checked.** The soundness proof's `callRet`/`callCont` cases
go through unchanged apart from discharging the guard with the same `hcand`
the `callEntry` step already builds (TODO.md Entry 1 plan step 5). Entry 3's
fixpoint argument needs each `C` to be monotone in the whole labeling, not
in one label. It still is: the guard is monotone in the heap and store, so
it can switch from false to true as `L` grows, but never back. See Entry 3's
decisions.

---

## Decision 2 — `Labeling.Valid` is stated over one `AGraph` predicate

**Where:** `CoreJsAutomatonSemantics.lean`, `AGraph`, `Labeling.Valid`.

**The gap.** Entry 2 needs a walk to follow "any edge of the automaton", and
Entry 3 needs "every edge into `b`". Before this change the edge set was
spelled out only inside `Labeling.Valid`'s two conjuncts (top-level
statement; every function body at every well-formed call string).

**Decision.** Name the edge set `AGraph Γ s₀ a b C ℓ`: an inductive with the
two cases `top`/`body` that used to be `Valid`'s two conjuncts. Then
`Labeling.Valid L := ∀ a b C ℓ, AGraph Γ s₀ a b C ℓ → C L ⊑ L b`. This is
equivalent to the old two-conjunct form and has exactly the same scope. It
gives the walk relation (Entry 2) and the fixpoint construction (Entry 3) one
shared definition of "an edge".

---

## Decision 3 — the `Fid`↔`ALoc` correspondence (TODO 4a) and `allocA`'s image

**Where:** `CoreJsAutomatonSemantics.lean`, `AbstractSpec.litLocA_fid`,
`AbstractSpec.allocA_fid`.

**The gap.** TODO 4a asks for `litLocA` restricted to function values to be
injective. Its first open sub-item asks whether `allocA`'s image is known to
avoid the functions' locations. It is not: nothing in `AbstractSpec`
constrains `allocA` except that it ignores its heap argument.

**Decision.**
- `litLocA_fid : litLocA (.fid f) = litLocA v → v = .fid f`. This is slightly
  stronger than injectivity among functions: a function's location is not
  shared with *any* other literal either. The stronger form is what
  invariant 4(b) needs (Decision 4), because the initial abstract heap writes
  each literal `v` at `litLocA v`. If a non-function literal shared a
  function's location, 4(b) would fail from the first state. It still allows
  an abstraction to merge non-function literals (for example, all numbers
  into one location), which full injectivity of `litLocA` would forbid.
- `allocA_fid : allocA h κ ≠ litLocA (.fid f)`, added as a new assumption:
  no allocation site is abstracted to a function's location. Without it,
  `binOp` could weakly write an arbitrary value set into a function's
  location, and 4(b) would be false.

---

## Decision 4 — invariant 4(b) is a proved preservation property, not a `Valid` conjunct, and it bounds from above only

**Where:** `CoreJsAutomatonSemantics.lean`, `AConf.FidReserved`,
`AEdge.fidReserved`, `AGraph.fidReserved`. The consequence for the
constructed labeling is in `CoreJsAutomatonTotality.lean` (Entry 3).

**The gap.** TODO 4(b) asks that every valid label keep
`h.val (litLocA (.fid f)) = {.fid f}` exactly, and leaves open whether it
should be a new conjunct of `Labeling.Valid` or a separately proved
preservation lemma.

**Two sub-problems.**
1. *Equality is not attainable.* A function never mentioned as a literal
   (not in the initial heap, never reached) has nothing at its location in
   any sensible label, and certainly not at `AConf.bot`. The meaningful half
   is the upper bound: nothing *other than* `.fid f` is ever at `f`'s
   location. That is what "nothing else ever joins into a function's
   canonical location" in the TODO text asks for.
2. *As a `Valid` conjunct* it would make validity no longer a pure
   post-fixed-point condition over the edges. The `⊤` labeling would not be
   valid, and Entry 3's existence argument would first need some valid
   labeling satisfying the bound, which is circular.

**Decision.** `AConf.FidReserved c` is the upper bound. Every edge's
contribution preserves it (`AEdge.fidReserved`, then `AGraph.fidReserved`):
if every state's label satisfies it, so does `C L`. The proof goes through
the new `PendingClosed` framework (below). Entry 3 then derives that the
least analysis result satisfies it at every state. `Labeling.Valid` is
unchanged.

To avoid a separate mutual induction for every property of
`pending`/`xpending`/`rpending`, `PendingClosed Q` packages "`Q` holds of `id`
and is preserved by post-composing each atomic effect", and
`AExit.closed`/`ARet.closed` prove once, by mutual structural recursion, that
every accumulated transform satisfies any such `Q`. Entry 3's monotonicity
argument reuses it.

---

## Decision 5 — TODO 4c ("`opSemA` never produces a function") moves to the concrete side

**Where:** TODO.md Entry 1, design item 4(c). The resolution lands with
Entry 2 (`CrossSpec.opSem_fid`, `CoreJsAutomatonSoundness.lean`).

**The gap.** 4(c) as written, `∀ op V₁ V₂ f, ¬ (opSemA op V₁ V₂).Mem (.fid f)`,
forbids `opSemA` from ever returning `VSet.top`, because `top` contains every
value. `VSet.top` exists precisely as the result of widening `⊕̂`, so this
assumption would make `top` unreachable and forbid the widening the abstract
domain was designed around.

Nothing on the abstract side needs 4(c). Invariant 4(b) needs only that
`binOp` never writes *at* a function's location (Decision 3's `allocA_fid`),
and what it writes elsewhere does not matter to it. The need is concrete.
The walk theorem (Entry 2) labels a call by `litLocA (.fid f)`, and relating
that to the concrete action `call l_f …` needs `α l_f = litLocA (.fid f)`,
so `l_f` must be `litLoc (.fid f)`. That holds only if no concrete binary
operation ever produces a function value somewhere else.

**Decision.** Do not add 4(c) to `AbstractSpec`. Add its concrete form,
`Concrete.opSem op v₁ v₂ ≠ .fid f`, to the concrete/abstract cross-spec that
Entry 2 introduces. There it supports the concrete invariant "a location
holding `.fid f` is `litLoc (.fid f)`" (`Heap.FidCanon`). This is also
weaker in the useful direction: the abstract side may still widen to `top`.

---

## Decision 6 — `AlphaFn.DefinedIn` is not enough to extend `α` at an allocation; the invariant becomes `AlphaFn.AllocSafe`, backed by two new cross assumptions

**Where:** `CoreJsAutomatonRelation.lean`, `AlphaFn.AllocSafe`,
`AlphaFn.AllocSafe.extend`, `CrossSpec.allocC_lit`, `CrossSpec.allocC_site`.
TODO.md Entry 2, "Dependency on the pre-existing `binOp`/`objLit` gap", plan
steps 2.1–2.4.

**The gap.** TODO.md proposes the invariant "every location in `α`'s domain
is defined in the current heap" (`DefinedIn`). With it, `allocC_fresh`
would give `l ∉ dom α` for the fresh location, so extending `α` there is
safe. The invariant fails for two independent reasons.

1. *It does not hold at the start.* TODO.md says it is trivial initially
   because "α's domain is initially just the literals (`α.Lits`), all defined
   in `Heap.init s`". But `α.Lits` fixes `α (litLoc v)` for *every* value
   `v`, infinitely many. `Heap.init s` defines only `s`'s own literals and
   `undefined`. Worse, nothing stops `allocC` from returning `litLoc v` for
   some `v` whose location is unused. `α` is then already committed there to
   `litLocA v`, not to the allocation site's abstract location.
2. *It is not preserved.* An object literal with no fields,
   `Heap.setObjs l []`, leaves the heap unchanged, so its location is in
   `α`'s domain but not in use. A later allocation may return the same
   location. For example, `x := {}; y := {}` with an allocator that ignores
   the site index gives `x` and `y` the same concrete location, while the
   abstract side keeps them at two different abstract locations. This
   breaks soundness itself, not only the proof: continue with `x.p := 1;
   z := y.p`. Concretely `z` is `1`. Abstractly `y`'s object has no `p`. The
   test suite uses `objLit "o" 2 []` routinely, so empty object literals are
   not a corner case.

**Alternatives considered.**
- Forbid empty object literals syntactically. Rejected: they are ordinary
  JavaScript and common in the tests. It also does not fix problem 1.
- Change the concrete `[Object Initialization]` rule to mark the location as
  in use (for example with a dummy value). Rejected: this changes the
  concrete semantics, its observations and the query tests, to work around
  a proof obligation. Any marker value would also have to be abstracted.
- Let `α` be a relation instead of a function. Rejected: the counterexample
  above is a real aliasing unsoundness, and a multi-valued `α` does not
  repair it.
- **Chosen:** keep the concrete semantics and constrain the allocator:
  - `CrossSpec.allocC_lit`: an allocation (on a finite heap) never returns a
    literal location.
  - `CrossSpec.allocC_site`: two allocations that return the same location
    have the same *abstract* site (`allocA … κ = allocA … κ'`). This is the
    weakest form that works. It holds trivially if the abstraction has a
    single allocation site, and it holds for any "allocation-site-
    partitioned" allocator. It allows the same concrete location to be
    returned again, and only requires that doing so never asks `α` to change
    its mind.
  - `AlphaFn.AllocSafe α h`: every location `α` maps is in use in `h`, or a
    literal location, or a location some allocation returns, mapped to that
    allocation's abstract site. `AllocSafe.extend` then produces, at any
    allocation on a finite heap, an extension `α' ≥α α` with
    `α' (allocC h κ) = allocA _ κ` that stays allocation-safe for the heap
    after the write.

**How the invariant is maintained.** TODO.md plans a
`BigStep.heap_defined_mono` lemma to carry `DefinedIn` across sub-runs. That
lemma is not needed. The `α'` a sub-run produces is existential, so a
monotonicity lemma about the *starting* `α` would not say anything about
it. `step_sound` therefore *returns* `α'.AllocSafe r.heap` as part of its
conclusion. The only monotonicity needed is at the leaves:
`Heap.Defined.setVal`/`.setObj`/`.setObjs`. Finiteness of the current heap,
which `allocC_fresh` needs, is threaded as a hypothesis and propagated with
the existing `BigStep.finite`.

---

## Decision 7 — object initialisation's abstract register update must be weak

**Where:** `CoreJsAutomatonSemantics.lean`, `AConf.doObjLit` (its `reg`
component). `AReg.setDep` was removed, since nothing else used it.

**The gap.** `doObjLit` did a strong update, `reg.setDep l ∅`, transcribed
from the old abstract semantics. An abstract location stands for every
concrete location allocated at sites it abstracts. Resetting its dependency
set to `∅` erases the dependencies of every other such concrete location. A
`binOp` result that shares the abstract location loses its dependencies,
either because the two sites share an abstract location, or because the
same concrete location was re-used after an empty object literal
(Decision 6). `Reg.Alpha` is then false for that location, so `objLit`'s
soundness case is unprovable. In general it is false.

**Decision.** Make the update weak. Joining `∅` into the dependency set
changes nothing, so `reg := c.reg`. The concrete side still resets to `∅`,
and relating `∅` needs nothing (`Reg.Alpha.setDep_empty`). Precision is lost
only when an object-literal site shares an abstract location with a site
that records dependencies. When the sites are separated, the abstract
dependency set at an object site is never written by anything else, so
weak and strong updates agree.

---

## Decision 8 — `AnalysisResult` must cover the initial heap, not equal `⊥` at the top-level entry

**Where:** `CoreJsAutomatonSemantics.lean`, `AHeap.init`, `AConf.init`,
`AnalysisResult`; `CoreJsAutomatonRelation.lean`, `AConf.Alpha.init`.

**The gap.** `AnalysisResult Γ s₀ L` required `L (.entry []) = AConf.bot`,
and `sound_top` required `AConf.Alpha α c (L (.entry []))`. `Heap.Alpha α h
AHeap.bot` holds only if `h` holds no value at all. Every well-formed heap
holds `undefined` at `l_undef` (`Heap.WF`), and `Conf.init s` holds all of
`s`'s literals. So `sound_top` applied to an `AnalysisResult` could only
ever be instantiated with an empty heap, and was vacuous for every real
program.

**Decision.** `AHeap.init s` / `AConf.init s` are the abstract counterparts
of `Heap.init s` / `Conf.init s`: each literal of `s`, and `undefined`, at
its abstract location, with an empty store and register.
`AnalysisResult Γ s₀ L := Labeling.Valid Γ s₀ L ∧ AConf.init s₀ ⊑ L (.entry [])`.
`AConf.Alpha.init` relates `Conf.init s` to `AConf.init s` under the
literal-only abstraction `AlphaFn.lits`. `sound_top` is now stated for a run
from `Conf.init s₀` and is no longer vacuous. Invariant 4(b) holds of
`AConf.init` (`AConf.FidReserved.init`); this is where Decision 3's
`litLocA_fid` is needed.

---

## Decision 9 — the cross-spec: `OpSemSound` becomes `CrossSpec`, kept out of `ConcreteSpec`

**Where:** `CoreJsAutomatonRelation.lean`, `CrossSpec`.

**Decision.** The soundness proof's extra assumptions are collected in one
structure. The old `OpSemSound.opSem_sound` becomes `CrossSpec.opSem_sound`,
alongside `opSem_fid` (Decision 5), `allocC_lit` and `allocC_site`
(Decision 6). `opSem_fid` and `allocC_lit` constrain only the concrete
parameters, but they are deliberately not added to `ConcreteSpec`: the query
bridge (`BigStep.obs_wf`, …) takes `ConcreteSpec` as a hypothesis, and adding
fields it never uses would narrow those theorems for no reason. The
structure moved from the soundness file to the relation file, because
`AllocSafe.extend` needs it.

---

## Decision 10 — relating `call`/`ret` actions needs a concrete invariant: function values live only at their literal locations

**Where:** `CoreJsSemantics.lean`, `Heap.FidCanon`, `BigStep.fidCanon`,
`Heap.init_fidCanon`.

**The gap.** An abstract `call`/`ret` label names the callee by the single
location `litLocA (.fid f)` (Entry 1). The concrete action names it by the
location `l_f` from which the call read `.fid f`. `Act.Alpha` needs
`α l_f = litLocA (.fid f)`. `α.Lits` gives that only when
`l_f = litLoc (.fid f)`. Assignments copy locations and so preserve that
equality, but a binary operation whose result is a function value would put
`.fid f` at a freshly allocated location, which `α` maps to an allocation
site.

**Decision.** `Heap.FidCanon h`: every location holding `.fid f` is
`litLoc (.fid f)`. It holds for `Heap.init s`, and is preserved by every rule
when `opSem` never produces a function value (`CrossSpec.opSem_fid`), since
`binOp` is the only rule that writes a value. It is threaded through
`step_sound` like heap finiteness.

---

## Decision 11 — walks: an inductive `AWalk` over `AGraph`, gated by the fixed labeling's labels

**Where:** `CoreJsAutomatonSemantics.lean`, `AWalk`; TODO.md Entry 2, open
sub-item "exact representation of a walk", and Entry 1's open sub-item on
gating.

**Decisions.**
- *Representation.* An inductive `AWalk Γ s₀ L a b acts`, with `nil` and
  `step` (take a graph edge whose label under `L` is `some act`, contributing
  `act.visible`: nothing for `epsilon`). It mirrors how the rest of the
  development defines relations, and makes concatenation (`AWalk.append`) a
  short induction. A list of edge facts would need a separate "consecutive"
  side condition.
- *Gating reads `ℓ L`, the fixed labeling's labels, not a configuration
  carried along the walk.* TODO.md Entry 2's sketch mentions "a running
  configuration … composing `C`s". Entry 1's design item 5 instead says the
  materialised action at an edge `a → b` is `ℓ (L a)`. These conflict. The
  second is what a downstream model checker explores, a finite automaton
  with fixed labels, so it was chosen. Composing contributions along a walk
  would also not produce the labels `L` actually assigns.
- *No `IsCandidate` monotonicity lemma is needed* for the soundness
  direction (Entry 1's third open sub-item). At a real call, the candidate
  check at `pending (L entry)` is derived directly from the run's
  `α`-relatedness to that same label, the same way `callEntry`'s validity
  step already did. Monotonicity is needed only for Entry 3's fixpoint, and
  is proved there.
- *Accepted over-approximation, made explicit.* `callPassThrough` is labeled
  `epsilon` as TODO.md specifies, so a walk may skip a call's body. Walks may
  also enter call-string instantiations no run reaches, since the graph
  closes over all well-formed call strings. Both only add walks. The theorem
  is existential ("some walk matches the run"), so neither affects it. They
  are the same kind of imprecision the rest of the analysis already accepts.

---

## Decision 12 — the shape of the strengthened soundness theorem

**Where:** `CoreJsAutomatonSoundness.lean`, `SoundRun`, `step_sound`,
`sound`, `sound_top`.

**Decisions.**
- `SoundRun Γ s₀ L cs entry pending s start α r` names the conclusion. It is
  the old disjunction (continued to an exit, or returned at a `ret`),
  extended with `α'.AllocSafe r.heap` and "some walk from `start` to that
  state has a trace `α'`-related to `r.trc`". The `start` parameter exists
  for `whileDo`'s nested induction, whose walks start at the current
  iteration's fan-out point rather than at `entry`.
- `step_sound` is replaced by the stronger statement instead of adding a
  second theorem, since the new statement implies the old one. Its
  hypothesis `hvalidS` ("this statement's edges satisfy validity") becomes
  `hsub` ("this statement's edges are graph edges"), from which validity
  follows through `hvalid`, and which is what the walk needs.
- `α'.Lits` is no longer part of the conclusion: it follows from `α' ≥α α`
  (`AlphaFn.Lits.mono`). The unused `EnvSpec`/`AbstractSpec` hypotheses were
  dropped.
- TODO.md Entry 2, plan step 6: `sound` (derivation height quantified away)
  and `sound_top` (whole program from `Conf.init s₀`, against an
  `AnalysisResult`, with `α := AlphaFn.lits`) are kept as the usable
  corollaries. They now carry the walk as well.

---

## Decision 13 — a satisfiability witness for all the assumptions

**Where:** `CoreJsAutomatonSoundness.lean`, `SpecModel.satisfiable`.

**Why.** Decisions 3, 5, 6 and 9 add assumptions. This repository has
already had one specification that turned out to be unsatisfiable, which
made every theorem assuming it vacuous (`ConcreteSpec.allocC_fresh`, per
`CLAUDE.md`). `SpecModel.satisfiable` exhibits a `Concrete`/`Abstract` pair
satisfying `ConcreteSpec`, `AbstractSpec` and `CrossSpec` together. Literals
sit at even locations through an injective encoding of values. Allocation
returns an odd location beyond a finite heap's support. There is a single
abstract allocation site, each function has its own abstract location, and
`⊕̂` always returns `⊤`. The witness is crude on purpose: it shows only
consistency, not a useful analysis.

---

## Decision 14 — small relocations

`Heap.setObjs_val`, `Heap.setVal_defined` and `mem_binOpDep` moved from
`CoreJsQueryBridge.lean` to `CoreJsSemantics.lean`. The automaton soundness
proof needs them too, and they mention only concrete-semantics notions. The
bridge still finds them through its import chain.

---

## Decision 15 — totality by the meet of all analysis results, not by Kleene iteration terminating under the ascending chain condition

**Where:** new file `CoreJsAutomatonTotality.lean` (`Labeling.least`,
`Labeling.least_result`, `exists_least_analysisResult`,
`exists_valid_labeling`, `Labeling.step`, `Labeling.kleene*`). TODO.md
Entry 3, design steps 1–6. `DESIGN_AND_PLAN.md` decision 12.

**The gap.** The planned argument iterates the whole-graph transformer from
`⊥` and concludes that the chain stabilises at some finite `n`, because
"each component domain satisfies the ascending chain condition". Under the
current assumptions that is false:
- `VSet` is a set of `Val`s, and `Val` is infinite (integers, strings).
  `AbstractSpec` requires only that `opSemA` is monotone, not that it widens
  or stays within a finite set of values. The paper's widening threshold
  was never formalised. With `opSemA add {1} {1} = {2}` and so on, the loop
  `while (…) { x := x + 1 }` gives the strictly ascending chain `{1}`,
  `{1,2}`, `{1,2,3}`, … at `x`'s allocation site, which never stabilises.
- Property names are unbounded strings, so the heap's object component does
  not live in a finite lattice either.

The old development's scaffolding, which TODO.md's first open sub-item asks
about, is recoverable from git history: `CoreJsAbstractionSoundness.lean` as
of the parent of commit `0eb7503`, section "Termination of the fixpoint
search". It contains only an `AFinite` class and a lemma that ascending
chains are monotone at every distance. It never proves stabilisation, and
its comment relies on the same unformalised "`⊤` absorbs once the widening
threshold is exceeded". There is nothing there to reuse.

**Alternatives considered.**
- Add a finite-height assumption (for example, `opSemA` returns `⊤` or a
  subset of a fixed finite set) and do the full ACC argument. Rejected as
  the main route: it adds a restriction on the abstraction that nothing else
  needs, and needs a finite-type encoding of the reachable state space
  (design step 1) plus a counting argument over `Prop`-valued sets. All of
  that would only prove existence, which is available without it.
- Use the `⊤` labeling. Rejected, as decision 12 requires: it is valid but
  carries no information.
- **Chosen: Knaster–Tarski.** The abstract domains are `Prop`-valued sets, so
  labelings have arbitrary meets (`AConf.inf`). Every edge's contribution
  is monotone in the labeling (`AGraph.lmono`, Decision 16). Hence the meet
  of all analysis results, `Labeling.least Γ s₀`, is itself one: it lies
  below each result `L`, so each edge's contribution from it lies below `L`'s
  target label, hence below their meet. This is the most precise possible
  witness (`exists_least_analysisResult`: below every analysis result),
  which is strictly more than decision 12 asked for ("not manufacture
  triviality").

**What is kept of the Kleene story.** `Labeling.step L` is the join over
every edge into each state (plus the initial configuration at the top
entry), built with the infinitary join `AConf.sup`. It is proved monotone.
Analysis results are exactly its post-fixed points (`result_iff`), and
`least` is a fixed point (`least_fixed`). The iterates `kleene n` from `⊥`
ascend (`kleene_ascending`) and stay below `least` (`kleene_le_least`), and
an iterate that is a post-fixed point is an analysis result equal to `least`
(`kleene_stable`). So whenever Kleene iteration does terminate, it computes
exactly the labeling constructed here. Only "it always terminates" is not
claimed, because it is not true in general (above).

**Design step 1 (a finite `AState` type) is not needed** and was not built.
The meet construction never iterates or enumerates states. `CallString.
length_le` remains available should a terminating algorithm be formalised
later.

---

## Decision 16 — monotonicity of the gated contributions, confirmed as a lemma

**Where:** `CoreJsAutomatonTotality.lean`, `AConf.Calls_mono`,
`AEdge.lmono`, `AGraph.lmono`. TODO.md Entry 3, second open sub-item.

The candidate check is monotone in the configuration (`Calls_mono`: the
callee's value set only grows with the heap and store). So an `if Calls then
X else ⊥` contribution can switch from `⊥` to `X` as the labeling grows, but
never back, and is monotone when `X` is. `AEdge.lmono` proves every edge's
contribution monotone as a function of the whole labeling (Decision 1). This
includes the return edges, which read two different states' labels. The
accumulated transforms are handled by `PendingClosed` (Decision 4) with the
property `AMono`. Monotonicity of `doBinOp`/`doObjLit` needs `AbstractSpec`
(`allocA_site`: the allocated abstract location does not depend on the
heap; `opSemA_mono`), so the totality theorems take `aspec`.

TODO.md design step 7 ("confirm the `whileBackIn`/`.whileBackOut` edges are
satisfied") holds with no special case. `least_result` proves every
`AGraph` edge's inequality by one uniform argument, and the two back edges
are ordinary constructors covered by `AEdge.lmono`.

---

## Decision 17 — `exists_valid_labeling`'s hypotheses

**Where:** `CoreJsAutomatonTotality.lean`, `exists_valid_labeling`.

The old statement took `[Concrete]` and `hΓ : EnvSpec Γ`, neither of which
the proof uses. It now takes `aspec : AbstractSpec`, which the monotonicity
argument needs. This is not a weakening in any meaningful sense: the bare
statement `∃ L, Labeling.Valid Γ s₀ L` is provable with no hypotheses at all,
by the `⊤` labeling. The substantive statement is
`exists_least_analysisResult`, which says the witness is the least analysis
result, and `exists_valid_labeling` is kept as its corollary so the name the
old plan used still exists. The theorem moved from the soundness file to the
new totality file (listed in `lakefile.toml`), and the soundness file imports
it for the headline corollary `sound_least`: every run is matched by a walk
of the least analysis result.

---

## Decision 18 — invariant 4(b) holds of the least analysis result

**Where:** `CoreJsAutomatonTotality.lean`, `AConf.restrictFid`,
`Labeling.least_fidReserved`. This completes Decision 4.

The least labeling is compared with its own restriction `L'`: every
function's location is cut down to at most that function. `L'` is itself an
analysis result. Each edge's contribution from `L'` lies below `least`'s
target label by monotonicity, and reserves functions' locations by
`AGraph.fidReserved`. The initial configuration reserves them by
`AConf.FidReserved.init`. So `least ≤ L'`, and `least` inherits the bound.
This is where the preservation-lemma formulation of Decision 4 pays off:
the proof needs only "each edge preserves the property", never a new
`Labeling.Valid` conjunct.

---
