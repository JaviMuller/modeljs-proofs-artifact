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
