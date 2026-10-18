# Walkthrough plan

Changes agreed during the interactive walkthrough of the automaton
development. Each entry: what to change, why, which files, and which proofs
it is expected to affect. Decisions of `PROBLEMS2.md` that were reviewed and
kept are listed at the end.

This file and `TODO.md` are temporary. **Not before the user says so**: after
the agreed changes are implemented they are the source material for slides
explaining the codebase (like `docs/slides/QueryLTLEquiv`). Then both are
deleted: `README.md` then states explicitly whatever
they were the reference for, and every reference to them (in sources,
`CLAUDE.md`, `PROBLEMS2.md`, `TODO.md`) is dropped.

Also part of that final cleanup:
- delete `exists_valid_labeling` (`CoreJsAutomatonTotality.lean`): it exists
  only so the name the old plan (`TODO.md`) used still exists, and its
  `aspec` hypothesis is misleading (a valid labeling exists with no
  hypotheses, by `⊤`); `exists_least_analysisResult` says strictly more.
  Update its mentions in `README.md`/`CLAUDE.md`.

## Order of application

*Kept up to date as changes are added.* Change numbers are the order in
which changes were agreed, not the order in which to apply them.

1. **Change 1** (un-mutual the edge relations) — first: it turns the
   `mutual` proof blocks that changes 3–5 touch into ordinary inductions.
2. **Change 4** (`callPassThrough` label `none`) — a one-line label change;
   no proof should move.
3. **Change 3** (`AGraph.body` restricted to entered instances of `f`) —
   touches `AGraph`'s pattern matches in Semantics, Totality, Soundness.
4. **Change 5** (`ReservedResult`) — additive, after change 3 so it is
   stated over the final `AGraph`.
5. **Change 6** (concrete heaps record allocated locations) — starts the
   concrete-side batch; removes `CrossSpec.allocC_site` and simplifies
   `AllocSafe`.
6. **Change 7** (initialise every function body's literals) — changes the
   `init` definitions and lemmas on both sides.
7. **Change 8** (specs by meaning) — last of the concrete-side group: it edits `CrossSpec` again after
   change 6, and `allocC_lit`'s new doc comment relies on change 7.

8. **Change 9** (missing property yields `undefined`) — independent of
   the others; after change 7 (so `undefined`'s location is set up by the
   final `init`) is convenient but not required.
9. **Change 10** (shared `Object.prototype`) — after change 9.
10. **Change 11** (key conversion) — after change 10.
11. **Change 12** (object references as values) — done, after change 11.

Change 2 is already applied. The automaton-side group (1, 4, 3, 5) and the
concrete-side group (6, 7, 8) are independent of each other; within each
group, keep the order. Run `lake build` (including the query tests) after
each change.

## Agreed changes

### 1. Un-mutual the edge relations — done

- **What:** replace the `mutual … end` block declaring `AExit`/`AEdge`/`ARet`
  (`CoreJsAutomatonSemantics.lean`) by three separate inductives, declared
  in dependency order `AExit`, then `ARet`, then `AEdge`. Fix the section
  header, whose claim that "`call`'s cases recurse into `Γ.body f`, which is
  not a subterm" is misleading: only `callRet`/`callImplicitRet` look into a
  callee's body, through `ARet`/`AExit` premises that are themselves
  structural on that body; the body's own edges come from `AGraph.body`.
- **Why:** there is no mutual dependency (`AExit` uses only itself, `ARet`
  uses itself and `AExit`, `AEdge` uses all three). The `mutual` block only
  costs: `induction` cannot be used, so every property is a `mutual` block
  of pattern-matching theorems.
- **Files:** `CoreJsAutomatonSemantics.lean`, `CoreJsAutomatonTotality.lean`,
  `CLAUDE.md` (the "Mutual inductives" gotcha and the
  `CoreJsAutomatonSemantics` entry's "mutually inductive edge relations",
  "reuse that rather than writing a new mutual induction").
- **Proofs affected:** `AExit.closed`/`ARet.closed` (become two sequential
  lemmas), `AEdge.fidReserved`, `AEdge.lmono` (Totality). No theorem
  statement changes.

### 2. Correct the `AExit` description in the edge-relations header — done

- **What:** the header said processing `s` leaves "one of the (possibly
  several) dangling continuing exits". Every statement shape has at most one
  `AExit` case, so `AExit` is a partial function (one exit or none); a
  structured statement exits at its join state whether or not anything
  reaches it. Rewritten accordingly.
- **Why:** the old wording suggested branching exits; the at-most-one fact
  is also what a procedural version can exploit (`Option` result).
- **Files:** `CoreJsAutomatonSemantics.lean` (comment only).
- **Proofs affected:** none. Applied during the walkthrough; builds.

### 3. `AGraph.body`: only instances of `f` that some edge enters — done

- **What:** add two premises to `AGraph.body` (`CoreJsAutomatonSemantics.lean`):
  ```lean
  | body : Γ f = some (params, body) → CallString.WF cs →
           (∃ cs' κ, cs = cs' ++ [(κ, f)]) →          -- cs is an instance of f
           AGraph Γ s₀ a' (.entry cs) C' ℓ' →          -- some graph edge enters it
           AEdge Γ cs (.entry cs) id body a b C ℓ → AGraph Γ s₀ a b C ℓ
  ```
  `AGraph` then refers to itself (positively) and is the *syntactically
  reachable* graph: instances grow outwards from `s₀`'s call sites. It does
  not depend on the labeling: phantom instances at real call sites (gated
  `callEntry`) stay in.
- **Why:** the current rule ties nothing between `f` and `cs`, and takes
  every well-formed `cs`. Consequences: (i) `f`'s body is processed from
  `.entry []`, so a walk from the top-level entry can run a function's body
  with no call (spurious traces for a model checker); (ii) `f`'s body is
  processed from another function's entry `.entry [(κ, g)]`, receiving `g`'s
  arguments; (iii) with no site-uniqueness assumption, a body processed
  under `[]` can create states (`.action [] κ`, …) that coincide with
  `s₀`'s own, polluting their labels; (iv) since sites range over `ℕ`, the
  graph is infinite, contradicting the "finite automaton" claim of
  `CoreJsAutomatonSyntax.lean`'s header, and a procedural construction
  (which computes only the reachable part) could not be proved equal to it.
  Soundness was never affected (extra edges only add walks).
- **Files:** `CoreJsAutomatonSemantics.lean` (`AGraph`, its section header,
  which currently calls the over-approximation "harmless"; `fidReserved`
  pattern matches), `CoreJsAutomatonSoundness.lean`,
  `CoreJsAutomatonTotality.lean` (pattern matches on `AGraph`),
  `CoreJsAutomatonSyntax.lean` (header: finiteness is of the reachable
  graph), `CLAUDE.md`/`README.md` if they describe `AGraph`'s scope.
- **Proofs affected:** soundness's two call cases using `.body`
  (`CoreJsAutomatonSoundness.lean`, around lines 360 and 419) need (a) a
  new lemma "`targetCallString cs κ f` ends with some `(κ', f)`" (short
  induction for the `truncateAt` case) and (b) the `callEntry` edge into
  the instance as an `AGraph` fact — already available from `hsub` at the
  call. `AGraph.lmono`, `AGraph.fidReserved`, `Labeling.step`,
  `Labeling.least`: only the new premises to carry through. No theorem
  statement changes. `PROBLEMS2.md` Decision 11's "walks may enter
  instantiations no run reaches" remains true only for phantom instances,
  which their gates make unenterable.

### 4. `callPassThrough` is not walkable: label `none` — done

- **What:** `AEdge.callPassThrough`'s label becomes `fun _ => none` (was
  `some .epsilon`). Its contribution is unchanged: the caller's
  configuration with `x ↦ ∅` still flows into `.cont cs κ`.
- **Why:** as an `epsilon` edge it let a walk skip a call altogether — no
  `call` action, no callee actions — while reaching a `cont` whose label
  includes the callee's return. A query with `except call(sanitize, …)`
  would then match every sanitized flow: systematic false positives for the
  model checker. Soundness never walks through it: the call case of
  `step_sound` walks `callEntry` → body → `callRet` and uses the
  pass-through only through validity (`hle`); `Valid` ignores labels. A walk
  at a call site with no live candidate now gets stuck, which is right: no
  concrete run passes such a site. Overrules `TODO.md` Entry 1 design item 2
  (note added there).
- **Files:** `CoreJsAutomatonSemantics.lean` (the constructor, its doc
  comment, `AAct`'s doc comment on `epsilon` if it mentions skipping);
  `PROBLEMS2.md` Decision 11's "accepted over-approximation" paragraph
  (annotate as superseded); `TODO.md` (note added).
- **Proofs affected:** expected none: `AGraph.lmono`, `fidReserved`,
  `Labeling.least`/`step` concern `C` only, and `step_sound`'s call cases do
  not use the pass-through's label. Check by building.

### 5. Name the reserved analysis results (`ReservedResult`) — done

- **What:** add to `CoreJsAutomatonTotality.lean`, after
  `Labeling.least_fidReserved`:
  ```lean
  def ReservedResult Γ s₀ L := AnalysisResult Γ s₀ L ∧ ∀ st, (L st).FidReserved
  theorem least_reservedResult : ReservedResult Γ s₀ (Labeling.least Γ s₀)
  -- and: least is below every ReservedResult (from Labeling.least_le)
  ```
- **Why:** `Valid`/`AnalysisResult` deliberately do not demand
  `FidReserved` (Decision 4: soundness holds for every valid labeling, and
  `Valid` stays a pure edge condition). Junk at a function's location never
  makes the executed body ambiguous — each call edge belongs to one
  candidate, which fixes both its target instance and its label — but it
  does create spurious candidates whose label is not among the callee
  expression's locations. A consumer of walk labels (the model checker)
  wants results without junk; this names that notion and states that the
  least result is one, and the least one.
- **Files:** `CoreJsAutomatonTotality.lean`; `README.md`/`CLAUDE.md`
  mention of `least_fidReserved` if worth extending.
- **Proofs affected:** none (purely additive).

### 6. Concrete heaps record allocated locations (overturns Decision 6) — done

*Mechanism superseded by change 12:* the `used` mark was removed once objects
hold their reference value, which keeps them in use; the effect (no location
is allocated twice) is unchanged.

- **What:** add an explicit "allocated" component to the concrete `Heap`
  (e.g. a field `used : Loc → Prop`, or `Bool`), set by `objLit` for the
  location it allocates (and harmlessly by `binOp`, which already defines
  `val`). `Heap.Defined l` additionally holds when `used l`. Then:
  - `ConcreteSpec.allocC_fresh` (stated via "not in use") makes every
    allocation distinct from every earlier one, empty objects included;
  - `AlphaFn.AllocSafe` simplifies to "in use in `h`, or a literal
    location" (the original `DefinedIn` idea plus literals);
  - `CrossSpec.allocC_site` is removed, and `AllocSafe.extend` simplifies.
- **Why:** the concrete semantics is unfaithful to JS today. `objLit` with no
  fields (`setObjs l []` is the identity) leaves its location free, so a
  later allocation can return it again — and must, when the heap is
  unchanged and the site is the same, since `allocC` is a function of both:
  `f() { r := {}; ret r }; a := f(); b := f(); a.p := 1; z := b.p` gives
  `z = 1` concretely, `undefined` in JS. Decision 6 only kept the *analysis*
  sound relative to this semantics (`allocC_site` rules out aliasing across
  different abstract sites, not within one). The query semantics and
  execution records run on the same concrete semantics, so they inherit the
  spurious aliasing too. Rejected alternatives: documenting it (unfaithful);
  a marker `Val` at the object's location (two objects would then satisfy
  `sv`, breaking queries).
- **Files:** `CoreJsSemantics.lean` (`Heap`, `Heap.Defined` and its
  per-update lemmas, the `objLit` rule and its `BigStepN` copy, `Heap.init`,
  `Heap.Finite`, `exists_allocator`, `ConcreteSpec`, run lemmas `finite`,
  `fidCanon`, `depInv`, `obs_wf`); `CoreJsAutomatonRelation.lean`
  (`AllocSafe`, its comment, `AllocSafe.extend`, `CrossSpec`);
  `CoreJsAutomatonSoundness.lean` (`objLit`/`binOp` cases, `SpecModel`);
  `CoreJsQueryTests.lean`, `CoreJsFoLtlTests.lean` (any `Heap` literals; a
  behavioural change in a test would expose a test relying on the aliasing);
  `CLAUDE.md`, `README.md` (mentions of `allocC_site`/`AllocSafe`);
  `PROBLEMS2.md` Decision 6 (annotate as superseded). Abstract side: no
  change.
- **Proofs affected:** as listed; mostly simplifications on the relation
  side. Decision 7's weak `dep` update at `objLit` stays (its other reason —
  a `binOp` site sharing the abstract location — still holds), but its doc
  comment's "re-used after an object literal with no fields" reason goes.
- **`Heap.Finite` must bound the new mark too:** today it says "beyond `n`
  no location holds a value or a property"; it must also say "or is marked
  allocated", or a heap could be finite with infinitely many marked
  locations, and `allocC_fresh` would no longer give a truly fresh location.
  Extend its preservation lemmas (`objLit` marks one more location). With
  that, `SpecModel`'s allocator ("odd location beyond the support") needs no
  change; only the proof of `allocC_fresh` is adjusted, and the proof of
  `allocC_site` is deleted.
- **Watch for:** the `Reg`/`Heap` structure-eta gotcha in `CLAUDE.md` —
  adding a field changes every `{ h with … }` and anonymous-constructor
  heap; prefer congruence lemmas.

### 7. Initialise the literals of every function body, not only `s₀`'s — done

*As implemented:* concretely `Heap.init Γ fs s`/`Conf.init Γ fs s` take an
explicit list `fs` of functions whose body literals are set up (`initLits`,
`Env.lits`), so the heap stays computable for the `rfl`-based tests;
abstractly `AHeap.init Γ s`/`AConf.init Γ s` cover every body of `Γ` through
the predicate `InitLit`, so `AnalysisResult`/`least` gained no parameter and
`sound_top` holds for every `fs`. `Env.params`/`Env.body` moved to
`CoreJsSemantics.lean`. New test `run_callLit` (a callee using a literal the
main statement does not mention).

- **What:** the initial heaps hold the literals of `s₀` **and of every
  function body in `Γ`** (plus `undefined`): `Heap.init`/`Conf.init`
  (`CoreJsSemantics.lean`) and `AHeap.init`/`AConf.init`
  (`CoreJsAutomatonSemantics.lean`) take `Γ` as well as `s₀`, and so does
  `Heap.WF` where it describes the initial heap. Finiteness of the initial
  heap needs `Γ` to have finitely many functions (`EnvSpec.fin`), so either
  thread `EnvSpec` or take the function list explicitly; definitions may be
  classical (`noncomputable`).
- **Why:** today `Heap.init s₀` stores only `s₀`'s literals. A literal that
  occurs only inside a function body has no value at its location, so any
  rule that reads it has no derivation: `y := x + 1` (binOp needs
  `h.val (litLoc 1)`), `if true …`, and calling another function by its
  literal (`r := g()` needs `h.val (litLoc (.fid g)) = some (.fid g)`).
  Every run reaching such a statement is outside the soundness theorem
  (and the query development's run records). Real functions use literals
  constantly. `CLAUDE.md` only states it as a test-writing rule
  ("function bodies in `Γ₀` must mention no literals").
- **Files:** `CoreJsSemantics.lean` (`Heap.init`, `Conf.init`, `Heap.WF`,
  `Heap.init_WF`, `Heap.init_finite`, `Heap.init_fidCanon`,
  `BigStep.obs_wf_init`); `CoreJsAutomatonSemantics.lean` (`AHeap.init`,
  `AConf.init`, `AnalysisResult`, `AConf.FidReserved.init`);
  `CoreJsAutomatonRelation.lean` (`AConf.Alpha.init`);
  `CoreJsAutomatonSoundness.lean` (`sound_top`, `sound_least`, `SpecModel`
  if it builds an initial heap); `CoreJsAutomatonTotality.lean` (uses of
  `AConf.init`); `CoreJsQueryTests.lean` (runs from `Conf.init`; the
  no-literals restriction on `Γ₀` can go); `CLAUDE.md` (drop that rule),
  `README.md`.
- **Proofs affected:** the init lemmas (now over a union of literal lists),
  everything that instantiates `Conf.init`/`AConf.init`. Theorem statements
  change only by the extra `Γ` argument to `init`.

### 8. Specs by meaning: concrete-only assumptions move to `ConcreteSpec` (overturns Decision 9) — done

- **What:** move `opSem_fid` and `allocC_lit` from `CrossSpec`
  (`CoreJsAutomatonRelation.lean`) into `ConcreteSpec`
  (`CoreJsSemantics.lean`). After this and change 6 (which removes
  `allocC_site`), `CrossSpec` contains only `opSem_sound`, the one
  assumption that mentions both sides. Correct `allocC_lit`'s doc comment:
  after change 7 every program literal's location is in use, so
  `allocC_lit` only reserves the addresses of literals occurring nowhere in
  the program — a modelling convention ("the literal region is reserved"),
  observationally invisible concretely, needed by the proof because
  `α.Lits` pre-commits every literal location. `opSem_fid`'s doc comment
  should list all operand-returning JS operators as expressed by
  statements: `&&`, `||`, `??` (via `if` + `assign`) and the comma operator
  `(a, b)` (evaluate `a`, then `x := b`); every other binary operator
  computes a new, non-function value.
- **Why:** each structure should mean what its name says: `ConcreteSpec` is
  where a reader learns what a concrete instance must look like, and no
  sensible instance violates either property. Decision 9 kept them out to
  avoid unused hypotheses on the query development's theorems
  (`BigStep.obs_wf`, …); the instances those theorems lose (allocators
  handing out literal addresses, operators manufacturing functions) are not
  sensible, so nothing of value is lost. Rejected alternative: removing
  `allocC_lit` by restricting `α.Lits` to program literals (needs a new
  hypothesis threaded through every case of `step_sound`).
- **Files:** `CoreJsSemantics.lean` (`ConcreteSpec`, and `BigStep.fidCanon`
  can then take `ConcreteSpec` instead of a bare `opSem_fid` argument);
  `CoreJsAutomatonRelation.lean` (`CrossSpec`, its section comment,
  `AllocSafe.extend`'s use of `allocC_lit`); `CoreJsAutomatonSoundness.lean`
  (`xspec.opSem_fid` → `cspec.opSem_fid`, `SpecModel`: the concrete model
  must now prove both fields as part of `ConcreteSpec`);
  `CoreJsQueryTests.lean` (its test-only `Concrete` instance already does
  not satisfy `ConcreteSpec`; nothing to do); `CLAUDE.md`, `README.md`
  (descriptions of the spec structures); `PROBLEMS2.md` Decision 9
  (annotate as superseded).
- **Proofs affected:** field accesses only; theorems taking `ConcreteSpec`
  gain two unused fields. Best done together with change 6, which also
  edits `CrossSpec`.

### 9. Reading a missing property yields `undefined` — done

*As implemented:* rules `lookupSMissing`/`lookupDMissing`, which also
require the receiver not to hold `undefined` (reading a property of
`undefined` throws in JS, so that case stays stuck; numbers and strings yield
`undefined`, as here). New tests `run_lookupMissing`, `run_lookupDMissing`.

- **What:** add concrete rules for `lookupS`/`lookupD` when the property is
  absent (`h.obj l₁ p = none`): `x ↦ litLoc .undef`, still emitting
  `lookup (litLoc .undef) l₁ l_p` (resp. `l₂` for the dynamic key); heap and
  register unchanged. Abstractly, `doLookupS`/`doLookupD` and the labels
  `actLookupS`/`actLookupD` add `{litLocA .undef}` to the looked-up set
  (the analysis cannot know a property is definitely present). The
  prototype chain stays unmodelled (prototype pollution is detectable from
  the trace).
- **Why:** today a lookup of a missing property has no rule, so every run
  that reads one (`if (opts.debug)`, optional configuration, …) has no
  derivation and is outside the soundness theorem and the query
  development. In JS it yields `undefined`; only `null`/`undefined`
  receivers throw, which stays "stuck".
- **Files:** `CoreJsSemantics.lean` (two `BigStep` rules, their `BigStepN`
  copies, `mono`/`mono_le`/`toN`/`toBigStep`, the run lemmas `finite`,
  `fidCanon`, `depInv`, `obs_wf` — easy: heap and register unchanged, and
  `litLoc .undef` holds `undefined` in every well-formed heap);
  `CoreJsAutomatonSemantics.lean` (`doLookupS`/`doLookupD`,
  `actLookupS`/`actLookupD`); `CoreJsAutomatonRelation.lean` (per-statement
  lookup lemmas); `CoreJsAutomatonSoundness.lean` (two new cases, mirroring
  the existing lookup cases, using `α.Lits` for `undefined`);
  `CoreJsAutomatonTotality.lean` (`lmono` for the changed effects);
  `CoreJsQueryTests.lean` (new `bigstep` tests for the missing case).
- **Proofs affected:** as listed; existing cases keep their proofs, with
  the extra `∪ {litLocA .undef}` carried through. Estimated smaller than
  change 6.

### 10. One shared `Object.prototype` (prototype chains of length one) — done

*As implemented:* abstract lookups are named `AHeap.lookupS`/`lookupD`
(own ∪ `Object.prototype`'s ∪ `undefined`). New test `run_pollute`.

- **What:** a marker value `Val.proto` whose literal location `litLoc .proto`
  is `Object.prototype` (reusing the literal machinery: fixed location,
  committed by `α.Lits`, never allocated by `allocC_lit`; source code can
  write `Object.prototype` as that literal). Object literals get
  `__proto__ ↦ litLoc .proto` before their own fields, so
  `o.__proto__.p = v` writes `Object.prototype.p`. A lookup whose own
  property is missing reads `Object.prototype`'s, and yields `undefined`
  only if that is missing too (rules `lookupSProto`/`lookupDProto` beside
  `lookupSMissing`/`lookupDMissing`). Abstractly, lookups return
  `own ∪ objOf {litLocA .proto} p ∪ {undefined}`, and `doObjLit` adds the
  `__proto__` property.
- **Why:** change 9 alone models the read of a polluted property as
  `undefined` (`o.__proto__.isAdmin = true; u = {}; u.isAdmin` is `true` in
  JS): the classic prototype-pollution gadget would be analysed wrongly. The
  implementation models prototypes (`model-js` `Heap.read_prototype`).
  Full chains (per-object prototypes, built-in prototypes per value kind,
  `Object.create`, constructors) are future work.
- **Files:** `CoreJsSyntax.lean` (`Val.proto`); `CoreJsSemantics.lean`
  (rules, transport cases, run lemmas); `CoreJsAutomatonSemantics.lean`
  (`doObjLit`, lookups and their labels); `CoreJsAutomatonRelation.lean`,
  `CoreJsAutomatonSoundness.lean` (cases, `SpecModel` encoding),
  `CoreJsAutomatonTotality.lean` (monotonicity); `CoreJsQueryTests.lean`
  (test `litLoc`, `bigstep`, a pollute-then-read test); `CoreJsFoLtl.lean`
  (printing `Val`).

### 11. Dynamic keys are converted to strings, as in JS — done

*As implemented:* abstractly through `VSet.HasKey V q` ("some `v ∈ V` with
`v.toKey = some q`"). New test `run_keyConv`. Matches `model-js`'s
`properties_of_locations` for primitive keys; there, object, function and
unknown keys become `Dynamic` (any property) rather than having no rule — a
possible follow-up: let such a key denote any property name concretely
(nondeterministically) and abstractly.

- **What:** a fixed conversion `Val.toKey : Val → Option PropName` (`str s`
  ↦ `s`, `num n` ↦ its decimal string, `bool` ↦ `"true"`/`"false"`,
  `undefined` ↦ `"undefined"`, `Object.prototype` ↦ `"[object Object]"`;
  function and `loc` values ↦ `none`). Dynamic lookups and updates require
  `h.val l₂ = some v` and `v.toKey = some p` instead of `.str p`; abstract
  `objOfV`/`weakSetObjV` use "some `v ∈ V` with `v.toKey = some q`".
- **Why:** JS converts every property key to a string (`a[undefined]` is
  `a["undefined"]`, `a[1]` is `a["1"]`); today any non-string key has no
  derivation.
- **Not covered, documented:** objects as keys (JS: `"[object Object]"`
  unless `toString` is overridden) stay stuck — an object's location holds
  no value, and covering it would add `"[object Object]"` to every abstract
  dynamic access; functions as keys (JS: their source text) stay stuck.
- **Files:** `CoreJsSyntax.lean` (`Val.toKey`); `CoreJsSemantics.lean`
  (dynamic rules and transport cases); `CoreJsAutomatonSemantics.lean`
  (`objOfV`, `weakSetObjV`); `CoreJsAutomatonRelation.lean`,
  `CoreJsAutomatonSoundness.lean`, `CoreJsAutomatonTotality.lean`;
  `CoreJsQueryTests.lean` (tests with `undefined` and number keys).

### 12. Object references are values; objects and functions as keys denote any property — done

- **What:** [Object Initialization] stores the object's reference value
  `.loc l` at its location `l` (`Val.loc`, from the paper's value grammar,
  previously unused); abstractly `doObjLit` adds `VSet.refs` ("some
  reference") at the abstract location. Keys go through `Val.KeyOf`: a value
  with a string form denotes exactly that property, an object reference or
  function denotes any property (concretely nondeterministic, abstractly
  `VSet.HasKey`), as `model-js`'s `Dynamic` properties. Change 6's separate
  `used` mark is removed: objects are in use through their value.
- **Why:** follow-up to change 11 — the abstract side cannot tell that a key
  location may hold an object unless objects have a value it can see.
- **Side effects (accepted):** binary operators accept object references
  (no longer stuck); in queries, `sv(x, y)` is true when `x`, `y` are the
  same object and false for different ones (before: false for any object,
  objects had no value); `hv` can see reference values.
- **Files:** `CoreJsSyntax.lean` (`Val.loc` doc, `Val.KeyOf`),
  `CoreJsSemantics.lean` (`Heap` without `used`, `objLit` rule, run
  lemmas), `CoreJsAutomatonSemantics.lean` (`VSet.refs`, `doObjLit`,
  `HasKey`, `FidReserved.pendingClosed`), `CoreJsAutomatonTotality.lean`,
  `CoreJsAutomatonSoundness.lean`, tests (`run_objLit` checks the reference
  value, new `run_objOp`).

## Future work

Not to be done now; recorded so it is not lost.

- **A procedural edge construction, proved equal to the declarative one.**
  All three edge relations are structurally recursive over `Stmt`, so the
  edges of a program can be computed by a function (e.g. returning the
  finite list of `(a, b, C, ℓ)` per statement, `AExit` exits as a list of
  `(x, xpending)`). Prove it matches the relations in both directions
  (every computed edge is an `AEdge`/`AGraph` fact and conversely), so the
  soundness and totality results transfer to the computed automaton. The
  computation produces only the reachable part (possibly with some
  unreachable leftovers, e.g. an `ifEnd` both of whose branches return, but
  always finite), which after change 3 is exactly `AGraph`. Best done after
  changes 1 and 3.
- **Open design question for the two procedural items above:** edges and
  the least labeling might be produced by a single procedure (exploring
  instances as their entry labels become non-`bot`) rather than two
  separate ones. To be discussed before implementing either.
- **Finiteness of the reachable graph.** After change 3, prove that
  `AGraph Γ s₀` has finitely many states and edges (finitely many call
  sites in `s₀` and `Γ`'s bodies, `EnvSpec.fin`, call strings bounded by
  `CallString.length_le`). This is what justifies the "finite automaton"
  claim and termination of a model checker's exploration.
- **A procedural labeling computation, proved to give the least analysis
  result.** On top of the computed edges, compute a labeling (e.g. by
  worklist/Kleene iteration of `Labeling.step`) and prove not only that it
  is an `AnalysisResult` (valid, covers `AConf.init s₀`) but that it equals
  `Labeling.least` — the minimal one (`Labeling.least_le`,
  `exists_least_analysisResult`, `Labeling.kleene_stable` in
  `CoreJsAutomatonTotality.lean` are the targets to connect to). Termination
  is the open point: Totality deliberately does not claim it (value sets
  range over an infinite domain, `opSemA` need not widen), so the
  computation needs either fuel with a "stable ⇒ least" result, or a new,
  satisfiable assumption guaranteeing finite ascending chains on the
  values reachable from the program (e.g. `opSemA` widening to `top`).
  Design agreed in the walkthrough:
  - **Why it does not terminate today:** abstract *locations* are finite
    (one per site and call string), but the value set at one location can
    grow forever: with a precise monotone `opSemA`, `x := 0; while c
    { x := x + 1 }` gives `{0} ⊂ {0,1} ⊂ {0,1,2} ⊂ …` at `allocA κ`;
    likewise property names (`k := k + "a"; o[k] := v`).
  - **Assumption:** `opSemA_bounded : ∃ k, ∀ op V₁ V₂, opSemA op V₁ V₂ =
    .top ∨ (opSemA op V₁ V₂ has at most k values)` — the implementation's
    widening threshold (default 5, `model-js` `evalop.ml`). Put it in a
    **separate** structure (e.g. `WideningSpec`) taken only by the
    termination theorem, not in `AbstractSpec`: a precise, non-widening
    `opSemA` is a sensible analysis for which soundness and totality hold.
    Extend `SpecModel` (its `opSemA` is constantly `top`, so it holds).
  - **Termination argument:** values enter the abstract heap only from
    literals (finitely many per program) and `binOp` results; at each
    `binOp` site the results form an increasing chain of `≤ k`-element sets
    or `top`, so they change at most `k + 1` times; reachable sites are
    finitely many (the finiteness item below); hence value sets, and with
    them property names, stabilise, and locations, variables and
    `dep`/`ac`/`sk` range over finite sets.
  - **Target theorem (chosen):** widening at the *operator* level (as
    above, matching the implementation's `widening_threshold`), so Kleene
    iteration terminates and, by `kleene_stable`, the procedure returns
    exactly `Labeling.least`. Rejected: widening accumulated *labels* (a
    location holding more than `n` values becomes `top` during iteration),
    which also terminates but yields an analysis result above `least`, i.e.
    only "returns *an* analysis result".
  - **Computable representation:** the current domains are `Prop`-valued
    predicates (good for proofs, not computable: stability of an iterate
    cannot be tested). The procedure needs finite sets/lists of values plus
    `top`, with a proof that they represent the predicate domains; the
    counting argument is done on that representation.

- **External (unavailable) functions.** Today `Γ` holds every function
  definition and a call to `f` with `Γ f = none` has no concrete rule, so a
  run that calls a missing dependency has no `BigStep` derivation and lies
  outside the soundness theorem. Real packages call unavailable dependencies
  routinely; the implementation treats them as unknown functions
  (`` `UnknownImport `` → `execute_unknown_call`, `model-js/src/model/builder.ml`).
  Design discussed, matching the implementation:
  - concrete rule for `Γ f = none`: trace `call l_f ls`, then optional
    callback runs (each function-valued argument may be invoked, with fresh
    parameters holding arbitrary values, as an ordinary `BigStep` of its
    body), then `ret l_f l`; result at the fresh `allocC h κ`, holding any
    non-function value (keeps `Heap.FidCanon`), `dep` = arguments and their
    dependencies; no other heap effect (as in the implementation);
  - abstract side: an external-candidate check (`.fid f ∈ valOf L_f ∧
    Γ f = none`), an intermediate state (e.g. `.ext cs κ`, since an edge
    carries one action) with a `call` edge in, callback edges to instances
    `targetCallString cs κ g` with `top` parameters and back, and a `ret`
    edge to `cont`; result at an external abstract location holding `top`;
  - later, optionally, heap havoc on objects reachable from the arguments.
  Cost: new `BigStep`/`BigStepN` rule and run lemmas, new `AState`
  constructor and `AEdge` cases, soundness/`lmono`/`fidReserved` cases,
  `SpecModel`. Best after changes 1 and 3. Until then, attacker inputs are
  modelled as arbitrary *values* (including references to program
  functions), which was judged a reasonable trade-off.

- **Prefix soundness.** The soundness theorem covers only complete runs
  (`BigStep` derivations). A safety violation is witnessed by a finite
  prefix, which may belong to a run that never terminates
  (`sink(t); while (true) {…}`, a server loop) or gets stuck afterwards
  (`sink(t); z := null.p`); such runs are not covered today. Add a
  "partial run" relation (`s` from `c` has produced trace `t` so far,
  possibly unfinished) and prove every partial run's trace is matched by a
  walk prefix from the entry, mirroring `step_sound`. Not to be implemented
  now; change 9 already shrinks the stuck case.

- **Full prototype chains** (after change 10): per-object prototypes and
  chains, built-in prototypes per value kind (`Number.prototype`, …),
  `Object.create`, constructor `prototype`s, as in `model-js`.

## Deferred decisions

To be settled when work on the bridge between the `ProgramAutomaton` and a
future query automaton (model checking) starts.

- **A final state and a record-level soundness corollary.** Today
  `sound_top` relates a run's final heap/store/register to `xpending (L x)`
  (`s₀`'s exit) or `rpending (L rst)` (a top-level `ret`) and its trace to a
  walk ending there; nothing is stated in terms of execution records
  (`Exec.ofRes r = ⟨trc, Obs.ofRun heap reg⟩`), which is what the query side
  consumes. Gaps: (i) the final abstract configuration is not a state's
  label when `s₀` ends with flat statements (`y := o.p; setTaint(y)`: the
  taint is only in `xpending (L x)`); (ii) a top-level `ret`'s end state is
  the last real state before it, which other walks may pass through, so a
  walk does not show that the run finished; (iii) there is one possible end
  point per top-level `ret` plus the exit. Options, to decide then:
  - **(a)** a state `.exit`, with silent edges from `s₀`'s exit (contribution
    `xpending (L x)`) and from each top-level `ret`'s end state
    (`rpending (L rst)`); `L .exit` is then the single final configuration
    (the join over all ways of finishing), and only complete runs' walks
    reach it;
  - **(b)** an abstract observation `AObs` from an `AConf` (`val`, `dep`,
    `ac` closed backwards under `dep` like `Obs.ofRun`, `sk`), a relation
    `Exec.Alpha`, and `sound_exec`: every run from the initial
    configuration has `Exec.ofRes r` related to `⟨trace of a walk from
    .entry [], AObs (final configuration)⟩`.
  Decided already: top-level `ret` stays allowed — it is the CommonJS module
  wrapper's `return` (legal in Node CommonJS files, a SyntaxError in scripts
  and ES modules); if `.exit` is added, its doc comment should say so.

## Decisions reviewed and kept

- **Decision 1** (gated call/return edges; `C : Labeling → AConf`,
  `ℓ : Labeling → Option AAct`). Kept. Clarified during the review: call
  edges are generated statically for *every* arity-matching function, so
  even a non-recursive site has a private instance of each such function
  whose transforms, applied to `bot`, need not stay `bot` (`ret 1`,
  `callImplicitRet`'s `undefined`); the return gate stops those phantom
  returns. Instances are shared only through recursion; an unreachable or
  non-`f` recursive call site inside `f`'s shared instance has both its
  entry and return gates closed, so it neither feeds `f`'s entry nor
  receives `f`'s returns. A live recursive call merges returns into every
  live call site of the shared instance — the accepted imprecision.
- **Decision 2** (one named edge set `AGraph`, shared by `Valid`, `AWalk`
  and Totality). Kept; it is what makes change 3 a single-place edit.
- **Decision 3** (`AbstractSpec.litLocA_fid`, `AbstractSpec.allocA_fid`).
  Kept. Note: the two fields exist only to establish `AConf.FidReserved`
  (`FidReserved.init` uses `litLocA_fid`, `FidReserved.pendingClosed` uses
  `allocA_fid`), and `FidReserved` itself (`AGraph.fidReserved`,
  `Labeling.least_fidReserved`) is currently used by nothing in
  `CoreJsAutomatonRelation.lean` or `CoreJsAutomatonSoundness.lean`:
  soundness relates `call`/`ret` through the concrete `Heap.FidCanon`
  instead. It is a guarantee for a future consumer of walk labels (e.g. the
  model checker): `lf` identifies the callee, and the heap at `lf` holds only
  it. The assumptions are cheap (satisfied by `SpecModel`), so they stay.
- **Decision 4** (`FidReserved` proved of `least`, not a conjunct of
  `Valid`; upper bound only). Kept. Discussed: the body a walk executes is
  fixed by the call edge (one edge per candidate), never by what the label's
  location holds, so junk is imprecision, not ambiguity; soundness is kept
  general over all valid labelings. "Exactly `{.fid f}`" is false for
  functions never mentioned as literals (`∅` there). The consumer-facing
  notion is added as change 5.
- **Decision 5** (`CrossSpec.opSem_fid`, concrete, instead of the abstract
  TODO 4c). Kept. Alternatives weighed: a set-valued callee label
  `call (Lf : ALocSet)` (drops `opSem_fid` and `Heap.FidCanon`, but labels no
  longer name the callee), and matching the implementation's `&&`/`||`
  (return an operand's location, no allocation; rejected: `opSem` stays an
  opaque parameter). A keeps single-location labels that name the callee, as
  the implementation's `Call of Location.t * …` does. `opSemA` may still
  return `top`. Consequences accepted: `BinOp.and`/`.or` cannot model JS's
  short-circuit `&&`/`||` (now stated in `opSem_fid`'s doc comment,
  `CoreJsAutomatonRelation.lean`); a future attacker-input model must keep
  program functions at their literal locations (`Heap.FidCanon` of the
  starting heap). Note: `PROBLEMS2.md`'s "forbids widening" overstates the
  cost of the abstract 4c — `.vals (non-functions)` is still expressible —
  the real reasons are that the abstract side does not need it and the
  concrete form is strictly weaker (implied by 4c plus `opSem_sound`).
  Revisited later in the walkthrough: making `||` return an operand's
  location was rejected again — it is already expressible as
  `c := ToBoolean(a); if c then x := a else x := b` (assignments copy the
  location, so no function value is copied); a dedicated statement would
  touch every induction for no gain. Stated in `opSem_fid`'s doc comment
  and in `BinOp`'s (`CoreJsSyntax.lean`). Also clarified: FidCanon matches
  JS reference semantics (passing/storing a function never copies it), so
  attacker-passed *program* functions are covered — `x ↦ {a_att} ∪
  {litLocA (.fid f) | f}` with `a_att ↦ top` models "any value".
- **Decision 7** (weak abstract register update at object initialisation).
  Kept: a strong update is sound only under extra site-separation
  assumptions, and the weak update loses no precision when sites don't
  collide. (After change 6, only the shared-abstract-location reason remains.)
- **Decision 8** (`AnalysisResult` covers `AConf.init s₀` with `⊑`, not
  `= ⊥`). Kept; becomes `AConf.init Γ s₀` with change 7.
- **Decision 10** (`Heap.FidCanon`: a function value lives only at its
  literal location). Kept. It matches JS reference semantics (passing or
  storing a function never copies it); maintained by `opSem_fid`, which
  moves to `ConcreteSpec` with change 8. Discussed together with Decisions
  3 and 5.
- **Decision 11** (walks as an inductive `AWalk`, gated by the fixed
  labeling's labels). Kept. Its "accepted over-approximation" paragraph is
  superseded: skipping a call's body is removed by change 4, and entering
  instances no run reaches is narrowed by change 3 to phantom instances,
  which their gates make unenterable. What remains is inherent to bounded
  call strings: with recursion, a walk can enter a shared instance from one
  call site and return to another call site that can also call `f`.
- **Decision 12** (shape of the soundness theorem: `SoundRun` with a
  `start` parameter for the loop's nested induction, `step_sound`
  strengthened in place with `hsub`, `Lits` dropped from the conclusion,
  `sound`/`sound_top`/`sound_least` as corollaries). Kept. Discussed: the
  theorem covers only complete runs (`BigStep` derivations); see change 9
  and the prefix-soundness item.
- **Decision 13** (`SpecModel.satisfiable`: a deliberately crude witness
  that `ConcreteSpec`, `AbstractSpec`, `CrossSpec` are jointly
  satisfiable). Kept: the theorems are generic over the parameters, the
  crude witness rules out vacuity, and interesting instances can satisfy the
  same specs. To update with changes 6 and 8 (see there).
- **Decision 15** (totality by the meet of all analysis results, Kleene
  reading kept as a characterisation). Kept: existence holds for every
  monotone `opSemA`, precise ones included; computation is the future
  procedural labeling under `WideningSpec`, which the Kleene reading
  (`kleene_stable`: a stable iterate is `least`) connects to.
- **Decision 16** (monotonicity of gated contributions via `Calls_mono`).
  Kept; unaffected by changes 3, 4, 9. A gate that could close as the
  labeling grows would break the meet argument.
- **Decision 17** (`exists_valid_labeling`'s hypotheses). Kept for now; the
  theorem is deleted in the final cleanup (see the top of this file).
- **Decision 18** (`least_fidReserved` via `restrictFid`). Kept; discussed
  with Decision 4.

---

# Queries / FO-LTL walkthrough

Changes agreed and decisions reviewed during the interactive walkthrough of
the query language and FO-LTL development (`analysis/Queries/`, plus the
execution records at the end of `CoreJsSemantics.lean`).

## Agreed changes

- **Removed `Query.Safe` and `Pat.bound`** (`CoreJsQuerySyntax.lean`, done).
  Unused anywhere, and `Pat.bound` assumed an invocation `Q(z⃗)` binds its
  arguments, which is false (`Query Q(x) { ε }` binds nothing). If the model
  checker later needs range restriction, define it then, with `bound`
  looking up the callee's body through `Δ`. CLAUDE.md updated.
- **Rename `Guarded.body` → `Guarded.pattern`** (done). `q.body.body` collided with
  `Query.body` (the whole guarded pattern) and misled the reading of
  `QProg.interp`. `Query.body` stays: it is the query's body `{ P }`. Fields
  then mirror the syntax: `pattern` / `when` / `except`. Touches
  `QuerySyntax`, `QuerySemantics`, `QueryTests`, `QueryToLtl` (≈35 sites plus
  `body :=` literals and doc comments). Rejected: `include` (a Lean keyword,
  and the opposite of "exclude", not "except"), `trigger`, `positive`.
- **Add `Pat.Sat.lower_start`** (done; `CoreJsQuerySemantics.lean`, after
  `QProg.interp_ok`, with `QBody.Sat.lower_start`, `Interp.LowerStart`,
  `QProg.interp_lowerStart` and the corollary `Exec.Matches.of_interp`). Statement: `F : i ⇝ j`, `i' ≤ i` ⟹
  `∃ j' ≤ j, F : i' ⇝ j'` ("starting earlier never forces finishing
  later"); the weaker "matches `0 ⇝ j'` for some `j'`" is not inductive
  (`ε ; F₂` lowers `ε`'s end). Needs the same property of `Θ` for the
  `query` case, as a separate predicate (e.g. `Interp.LowerStart`) with its
  instance for `QProg.interp` by induction on the program, which holds
  because `except` is whole-trace. Pins down formally the informal claim
  that `Exec.Matches` starting at `0` loses no generality. Purely additive:
  no existing proof changes.
- **Fixed `LVar`'s doc comment** (`CoreJsQueryToLtl.lean`, done). It said
  `Sum.inl` covers a top-level query's parameters *and locals*; locals are
  always renamed to fresh `Sum.inr` tags by `Guarded.Tr`, top level included.
- **Rename the type `Guarded` → `QBody`** (done, together with the
  `Guarded.body → pattern` rename above). Variables of type `QBody` are named
  `P` (the grammar's letter, `Query Q(x⃗) { P }`), and hypotheses about the
  pattern part are named `hpat`/`φ_pat`/`hPatTr`/`hcorrPat`.
  "Guarded" names a technicality, not what the thing is: the body `{ P }` of
  a query. With both renames, `Query.body : QBody` and its fields read
  `q.body.locals` / `.pattern` / `.when` / `.except`. Covers every derived
  name: `QBody.Sat`, `QBody.Tr`, `QBody.vars`, `QBody.calls`,
  `QBody.CallsOK`, `QBody.sat_coincide`, `QBody.Sat.simple`/`.invert`
  (tests), `GuardedCorrect`/`GuardedExists` → `QBodyCorrect`/`QBodyExists`,
  `Query.CallsOK.guarded`, and so on. About 115 identifier occurrences
  (`QueryToLtl` 66, `QueryTests` 22, `QuerySemantics` 20, `QuerySyntax` 7)
  plus CLAUDE.md (8); the ~20 prose mentions of "guarded pattern" in doc
  comments become "query body". No proof changes beyond renaming.
- **Add a computable translation `Pat.tr`/`QBody.tr`** (done;
  `CoreJsQueryToLtl.lean`, section `## Computing the translation`). As built:
  completeness (`tr_complete_all`, `Pat.Tr.tr_eq`) is by the same strong
  induction as soundness, not by recursion on the derivation (Lean's
  structural recursion rejected the mutual version); totality on well-formed
  programs follows from completeness plus `exists_all`. Six `#guard`
  examples (section `computed`), including the sanitizer and capture examples
  from the walkthrough. Original design: `Pat.Tr`/`Guarded.Tr` stay as the specification;
  the function is an executable implementation of it, so concrete queries can
  be `#eval`ed to the FO-LTL formula they produce. Design:
  - Signature mirroring the relation: `Pat.tr (ρ : Ren) (Δ : QProg) (F : Pat)
    (K : Ltl LVar) (n : Nat) : Option (Ltl LVar × Nat)`, and the same for
    `Guarded.tr`; `none` when an invocation finds no callee in `Δ` or has the
    wrong arity (the cases `QProg.WF` excludes).
  - Termination: an invocation recurses into the callee's body against the
    strictly shorter `Δ'` (`QProg.findRest?_length_lt`); every other case is
    structural on `Pat`. Either well-founded recursion on
    `(Δ.length, sizeOf F)` or fuel = `Δ.length`; pick whichever Lean accepts
    with less ceremony.
  - Proofs: soundness `Pat.tr … = some (φ, n') → Pat.Tr … φ n'` (so
    `correct_all` applies to its output unchanged), and totality on
    well-formed programs (`QProg.WF Δ` + calls OK ⟹ `isSome`). Then a
    corollary of `Query.exists_tr_correct` with the computed formula in
    place of the existential.
  - Display: `deriving Repr` (or a small `toString` with `∧ ∨ ¬ F X U Y S ∃`
    notation) for `Atom`/`Ltl`, and `#eval` examples, e.g. on `exSink` and a
    query with an invocation and an `except`, showing the fresh tags.
  - Fix `Query.exists_tr_correct`'s doc comment (line 1386), which currently
    claims the translation "can be *computed*" — true only once this exists;
    state that the computable version is `Pat.tr` and link the two.
  No existing proof changes.

## Decisions reviewed and kept

- **Final-snapshot `ac`/`sk`** (`Obs` is one rigid snapshot of the end of the
  run). Kept. `val`/`dep` are write-once (set only at fresh locations), so the
  snapshot is exact for them; `ac`/`sk` only grow, so the snapshot forgets
  *when* a location was marked: `y := f(x); setTaint(x)` matches
  `call(f, x) when ac(x)`. Accepted reading: `ac`/`sk` mean "declared
  attacker-controlled / sink at some point in the run"; `setTaint`/`setSink`
  are intended to be used only at the beginning of a program (harness
  prefix), where the two readings coincide. Alternatives rejected: making
  `setTaint`/`setSink` trace actions (breaks `ac`/`sk` as state atoms) and
  a syntactic prefix restriction (unnecessary for the intended usage).
- **Subsequence matching** (`Pat.Sat.act`: `i < j`, not `j = i + 1`). Kept.
  `F₁ ; F₂` means "`F₁`, then `F₂` strictly later", with gaps allowed. Calls
  and returns are not paired (`Call(f,[x]) ; Retn(f,y)` can pair a call with
  a later invocation's return); accepted as an over-approximation.
- **Whole-trace `except`.** Kept. Not a source of false negatives in the
  intended usage: a sanitizer is modelled by its *output*
  (`except Retn(san, y)`), and since locations are write-once, "`y` was
  returned by `san`" is a timeless fact. Anchoring the guard to the match
  would also break the in-place FO-LTL translation of `&`.
- **Shared literal locations under taint** (`assign x (val v)` binds `x` to
  `litLoc v`, so `setTaint` on a variable holding a literal taints every
  occurrence of that literal, and everything computed from one). Kept, no
  documentation change: marking a constant is the query author's/harness's
  responsibility.
- **Exclusivity (`Model.Excl`, `Shape`, `Ltl.excl`), soundness direction
  only.** Kept as is. Nothing but one test (`CoreJsFoLtlTests.lean`) uses it;
  the translation is proved over record models, which are exclusive by
  construction. Observations, for when a consumer appears: the plain
  converse (`m ⊨ Ltl.excl v shapes` ⟹ `m.Excl`) is false, since actions of
  shapes outside the list are unconstrained and `call_n` is infinite. For
  *shape-finite* models (finitely many shapes across all states; record
  models qualify, `Model` in general does not, e.g. a state `fun _ => True`)
  it becomes a characterisation with `shapes := the model's own shapes` and
  `v` injective. A validity/satisfiability check over arbitrary models would
  instead need the shape list taken from the *query*, plus a lemma that a
  formula cannot observe actions of shapes it does not mention: prove that
  one, not the characterisation, if the need arises.
