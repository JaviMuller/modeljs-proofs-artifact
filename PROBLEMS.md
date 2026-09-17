# Implementation decision log — automaton-trace-model branch

This document records places where `DESIGN_AND_PLAN.md` left the exact Lean
formulation open (or, in one case, turned out to have an outright gap once
implementation started), the alternatives considered, and which one was
picked and why. Written so a reader who disagrees with a decision can ask to
go back to that point specifically rather than redoing everything after it.

Read in conjunction with `DESIGN_AND_PLAN.md`, which this document does not
repeat.

---

## Decision 1 — representing the automaton's edge/exit set as inductive relations, not a computed function

**Where:** `CoreJsAutomatonSemantics.lean`, the `AExit`/`AEdge` relations.

**The gap.** §3 decision 10 of `DESIGN_AND_PLAN.md` says the state/edge set is
"entirely static — a function of Γ's call graph alone" and explicitly calls it
a function. Taken literally, that means a computable `def`. But a `def`
recursing into `Γ.body f` for a *different* `Stmt` at a call site (needed for
`call`) is not structurally decreasing on the `Stmt` being processed — the
same obstacle `BigStep`/`ABigStep` already sidestep by living in `Prop`, not
`Type`. Formalizing the edge set as a literal terminating function would need
a well-founded recursion measure (something like `|dom Γ| - cs.length`,
justified by the no-repeat-in-a-call-string invariant of `CallString.WF`)
threaded through every recursive call — a substantial extra proof burden
*only* to make the definition compute, with no soundness payoff, since
nothing downstream (labeling validity, the soundness proof) needs the edge
set to be computable, only to be a well-defined relation.

**Decision.** Define the edge set as an ordinary mutually recursive
`inductive ... : ... → Prop`, exactly mirroring how `ABigStep` is already
built in this codebase (its `[Call-Fix]`/`callRet`/`whileDo` cases already
recurse into unrelated `Stmt` terms, e.g. `Γ.body f` or an unfolded
`ifElse`, without any termination proof, because inductive *Prop* definitions
in Lean only need strict positivity, not termination). "Declarative" is read
as "characterized by closure conditions", not "given by a terminating
algorithm" — consistent with decision 10's own later sentence: "the
worklist/re-analysis-on-widening procedure ... is the *algorithm* ... not
evidence that one can't be characterized declaratively."

Finiteness of the *type* `AState` (needed later for totality) is proved
directly from `CallString.length_le` (already in `CoreJsAutomatonSyntax.lean`)
and does not depend on how `AEdge`/`AExit` are defined.

**Alternative considered and rejected:** computable `def` with a
well-founded-recursion `termination_by`. Rejected for the reason above (extra
proof burden, no payoff) — flagged here in case a future session wants the
edge set to be literally executable (e.g. to extract a checker), which this
decision does not provide.

---

## Decision 2 — dropping trace/action labels from edges for this phase

**Where:** `CoreJsAutomatonSemantics.lean`, edge contributions.

**The gap.** §4.3's table prints edges with trace-action labels (`Call(...)`,
`Ret(...)`, `UnOp(...)`) matching the old `AAct`/`ATrc` vocabulary, suggesting
edges should carry both a value-transformation *and* an action label for the
eventual security-query language.

**Decision.** This phase's edges carry only the value-transformation
`AConf → AConf` (heap/store/register), not an action label. §2 of
`DESIGN_AND_PLAN.md` explicitly defers "trace/path-relatedness" and the query
language to a later planning pass; since nothing in the state/edge/labeling
validity condition (§4.4) or the soundness-for-values proof needs an action
label, carrying one now would be speculative work against an interface that
hasn't been designed yet. Re-adding an `AAct`-style label per edge later is a
mechanical, additive change (it does not require revisiting anything decided
here) once the query-language phase actually starts.

---

## Decision 3 — the `cont` state's label needs *two* kinds of incoming edges, not just `Ret` edges

**Where:** `CoreJsAutomatonSemantics.lean`, the `call` case of `AEdge`.

**The gap — a real, previously unnoticed hole in the design document.**
§4.3's table says a call site's continuation state receives contributions
only from the candidate callees' `Ret`-producing edges ("the call's own
continuation state receives the union of all live candidates' return
contributions the same way `ret` targets it"), and no worked trace in §6
draws any other edge into a `cont` state. Taken literally this is unsound:
`ASto` updates are *strong* (`ASto.upd` overwrites, not joins — see
`CoreJsAbstractSemantics.lean`), and a callee's own store lives in a
completely different variable namespace from the caller's. If `cont`'s label
is defined purely as the join of `Ret`-edge contributions, then:

- every caller-local variable *other than* the call's own LHS `x` would be
  unconstrained (in fact bottom) at `cont`, silently erasing the caller's
  other locals across every call — obviously wrong (the concrete `[Function
  Call]` rule only ever touches `ρ.upd x l`, nothing else);
- a call site with zero live candidates (`callNone` in the old semantics)
  would starve everything sequenced after it, contradicting the explicit
  design intent (preserved from the old `callNone` rule's comment) that "a
  dead call in one branch of an `if` does not starve the analysis of
  everything sequenced after it."

This is exactly the kind of elision the design document itself flags
elsewhere (§6.2's note on `ifThen`/`ifElseB` states being invisible in a
printed trace when they have no distinguishing effect) — every worked example
in §6 happens to not exercise a variable that would expose the missing edge,
so its absence went unnoticed during the design session.

**Decision.** `cont cs site` (for a call statement `x :=κ e(es)` at site `κ`)
receives edges from two distinct sources, combined by the ordinary "join over
all incoming edges" validity condition (no special-casing needed once both
edges exist):

1. **Exactly one pass-through edge**, from the call's own entry/pending point,
   contributing `fun c => {c with sto := c.sto.upd x ∅}` with heap/register
   unchanged — mirrors the old `callNone` rule exactly, and is what preserves
   every caller-local variable other than `x`, and what supplies the `⊥`
   default when no candidate is live.
2. **One edge per `ret` reachable inside a candidate callee's body**,
   contributing the callee's own heap/register at that point together with
   `ASto.bot.upd x (returned locations)` — using `ASto.bot` (not the callee's
   raw store) for every variable but `x` is what stops the callee's local
   variable namespace from leaking into the caller's; joining `ASto.bot.upd x
   L` into anything only ever affects the `x` slot, by construction of
   `ASto.join` as a pointwise union.

This is a *conservative extension* of the design document, not a
contradiction of it: every edge the document does mention is still present
exactly as specified; this decision only adds the one edge needed for
soundness that the document's table omitted.

**Alternative considered and rejected:** special-case `cont`'s validity
condition (rule (a) uses inclusion, rule (b) uses inclusion, but combined by
something other than the generic per-edge join). Rejected because it would
mean the labeling-validity definition (§4.4) is no longer uniform across
state kinds — every other state's validity is exactly "join over incoming
edges" — and the two-source-edges resolution above achieves the same result
while keeping §4.4 as stated, unmodified, for every state kind including
`cont`.

---

## Decision 4 — how a `ret`'s edge finds its call site(s)

**Where:** `CoreJsAutomatonSemantics.lean`, the `call` case of `AEdge`
(not `ret`'s own case — see below).

**The gap.** A `ret e` occurring inside a function `f`'s body, at call-string
`cs`, must emit an edge to *every* continuation whose call-string, after
`targetCallString`, truncates to `cs` (§4.3's `ret` row). Stated at `ret`'s
own processing site, this would require `ret` to somehow know, out of thin
air, which call sites elsewhere in the program target it — information not
locally available at a `ret` node.

**Decision.** Do not give `ret` its own free-standing edge-emitting
constructor at all. Instead, `call x κ e es`'s own `AEdge` derivation — which
already knows `x`, already computes `cs_f := targetCallString cs κ f` for
each candidate `f`, and already recurses into processing `Γ.body f` at
`cs_f` (exactly as the old `ABigStep.callRet`/`callCont` recursed into
`Γ.body f`) — additionally collects every `ret e'` reachable inside that
recursive processing (via a third relation, `ARet`, parallel to `AExit`/
`AEdge`, that records "processing `s` reaches a `ret e'` at state `r` with
value contribution `fun c => aevalE c.sto e'`") and, for each such fact,
itself emits the edge `r → cont cs site` with the store-namespace-safe
contribution described in Decision 3. This keeps all the "who calls whom"
bookkeeping localized to the one place (`call`'s own processing) that already
has every piece of information needed, and gives `ret` a role only as a leaf
fact-producer (`ARet`), never as an edge-emitter itself — matching §4.3's
statement that `ret` itself allocates no state and, in this formulation,
requires no existential search over the rest of the program to know its
targets either.

**Alternative considered and rejected:** give `ret` its own `AEdge`
constructor, existentially quantified over a matching call-site occurrence
found by searching the whole program (top-level statement or some `Γ g`'s
body) for a `.call x' κ' e' es'` subterm with `targetCallString cs' κ' f = cs`.
Rejected as strictly more complex than necessary — it needs a new
"occurs as a subterm anywhere in the program" predicate and duplicates
exactly the traversal `call`'s own recursion into `Γ.body f` already
performs — with no compensating benefit, since nothing else needs `ret` to be
self-contained.

---

## Decision 5 — `IsCandidate` gates the whole callee-entry contribution, not just the argument binding

**Where:** `CoreJsAutomatonSemantics.lean`, the `call` case, edge into
`entry cs_f`.

**The gap.** §4.3's table contribution for the call→entry edge is written
`if IsCandidate(...) then {params ↦ args} else ∅`, which reads as gating only
the *store* component (argument binding), leaving heap/register unconditional.

**Decision.** Gate the *entire* contribution (heap, store, and register all
become the bottom element) when `IsCandidate` fails at the source label,
not just the store. *Why:* the edge to `entry cs_f` is structurally present
for every arity-matching `f ∈ dom Γ` regardless of plausibility (decision 6
of the design document), so for an `f` that is not actually a live candidate
at a given label, nothing about that pairing should be attributed to `f`'s
entry at all — including heap/register, which the old `ABigStep.call` rule
also never contributed for a non-candidate (such an `f` was simply absent
from the `fs` list entirely, so its `hs`/`δs` never appeared in the
`AHeap.joinAll`/`AReg.joinAll` folds). Gating only the store would let a call
site that can never resolve to `f` still leak the caller's heap/register into
`f`'s entry, which is strictly more than the old semantics ever contributed
and is an unforced loss of precision (though not literally unsound, since
heap/reg only ever grow via `⊔`).

---

---

## Decision 6 — the automaton files are fully independent of the old abstract-semantics files; those are dropped from the build

**Where:** `lakefile.toml`, `CoreJsAutomatonSemantics.lean`.

**Instruction from the user, mid-implementation:** the old `CoreJsAbstractSyntax
.lean`/`CoreJsAbstractSemantics.lean`/`CoreJsAbstractionRelation.lean`/
`CoreJsAbstractionSoundness.lean` are reference material only — read for the
value-update math they already worked out — and are to be removed from the
project eventually. The automaton files must not import or depend on them.

**Consequence.** `CoreJsAutomatonSemantics.lean` re-declares its own copies
of `ALoc`/`ALocSet`/`VSet`/`AHeap`/`ASto`/`AReg`/`Abstract`/`AbstractSpec`/
`aevalE`/etc. rather than importing `CoreJsAbstractSyntax.lean`/
`CoreJsAbstractSemantics.lean`, even though the definitions are currently
identical — this is deliberate duplication, not an oversight, and should stay
in sync only by hand until the old files are actually deleted, at which point
there is exactly one copy again.

Separately: `CoreJsSyntax.lean`'s `Idx` site fields (Decision 4-worth of
`DESIGN_AND_PLAN.md`, implemented first) changed the arity of `ifElse`/
`whileDo`/`call`/`lookupS`/`lookupD`/`updateS`/`updateD`, which the old
`CoreJsAbstractSemantics.lean`'s `ABigStep` (and transitively
`CoreJsAbstractionSoundness.lean`) pattern-matches by the old arity — so
those files no longer type-check regardless of the independence question
above. Rather than patching them to compile (wasted effort on files headed
for deletion), `lakefile.toml`'s `globs` now lists only `CoreJsSyntax`,
`CoreJsSemantics`, `CoreJsAutomatonSyntax` and `CoreJsAutomatonSemantics`;
the four old files remain on disk, readable, but are no longer build targets
and no longer need to type-check. `lake build` is green with this set.

---

*(This document will grow as further decision points are reached —
particularly once the abstraction-relation and soundness/totality phase
starts, which is expected to surface more of these.)*
