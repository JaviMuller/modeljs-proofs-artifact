# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repository is

A Lean 4 formalisation (no Mathlib) of a static analysis for security
properties of a small "Core JavaScript" language. `README.md` is the overview
for human readers (what is proved, how the files fit together); this file is
the operational guidance for working on the code.

- a small Core JavaScript language and its concrete big-step semantics;
- a static analysis over it, formulated as a call-string *automaton* with a
  *labeling* (an abstract configuration at every state), an abstraction
  relation, a soundness theorem (every concrete run is matched by a walk
  through the labeled automaton) and a totality theorem (every program has a
  least analysis result);
- a *query language* for describing vulnerable behaviours, with a satisfaction
  relation over execution records (trace + taint observation; every concrete
  run yields a well-formed one), and a semantics-preserving translation into
  first-order LTL over finite traces.

There is no application code — the entire deliverable is the Lean source under
`analysis/`. The source is meant to be self-explanatory: file headers and
comments state the reasons for non-obvious choices. `PROBLEMS2.md` at the
repository root is a decision log for the most recent round of changes to the
automaton development (labels, walks, soundness, totality); read the relevant
entry before revisiting one of those decisions.

## Build / check commands

- Build everything: `lake build`
- Type-check a single file: `lake env lean analysis/<Dir>/<File>.lean` (its
  imports must already be built, i.e. run `lake build` first).
- `lean-toolchain` pins `leanprover/lean4:v4.32.1`; use `lake`/`lean` via
  `elan`, no other setup is required.

### `lakefile.toml` lists modules explicitly

`globs` enumerates every module of the `Analysis` library; a `.lean` file that
is not listed is silently skipped by `lake build`. **When adding a file under
`analysis/`, add its module name to `globs`**: its path under `analysis/`,
without extension, with `/` replaced by `.` (e.g.
`ProgramAutomaton.CoreJsAutomatonSemantics`); `import` lines use the same
names. The list is currently complete.

### Layout

Sources live under `analysis/` in six directories (module names never
contain spaces, hence the camel case):

- `CoreJS/` — the language and its concrete semantics
  (`CoreJsSyntax`, `CoreJsSemantics`);
- `ProgramAutomaton/` — the automaton-based analysis (`CoreJsAutomaton*`);
- `Queries/QueryLanguage/` — queries, their semantics, and the query tests
  (`CoreJsQuery{Syntax,Semantics,Tests}`);
- `Queries/FoLtl/` — FO-LTL, its tests, and the query-to-FO-LTL translation
  (`CoreJsFoLtl`, `CoreJsFoLtlTests`, `CoreJsQueryToLtl`);
- `Queries/QueryModel/` — query models (the automaton form of queries, for
  the model checker) and the query-to-model translation
  (`CoreJsQModel{Syntax,Semantics}`, `CoreJsQueryToQModel`);
- `ModelChecking/` — model checking query models against an abstraction of
  the program (`CoreJsMc{Interface,Explore,Domain,Tracker,Algorithm,Instance,Finite,Tests}`).

## Architecture

All files are in `namespace CoreJS` (the namespace is unrelated to the
`CoreJS/` directory). What each file imports, by file name (the directories
are listed above):

- `CoreJsSemantics` ← `CoreJsSyntax`
- `CoreJsAutomatonSyntax` ← `CoreJsSyntax`
- `CoreJsAutomatonSemantics` ← `CoreJsAutomatonSyntax`, `CoreJsSemantics`
- `CoreJsAutomatonRelation` ← `CoreJsAutomatonSemantics`
- `CoreJsAutomatonTotality` ← `CoreJsAutomatonSemantics`
- `CoreJsAutomatonSoundness` ← `CoreJsAutomatonRelation`, `CoreJsAutomatonTotality`
- `CoreJsQuerySyntax` ← `CoreJsSyntax`
- `CoreJsQuerySemantics` ← `CoreJsSemantics`, `CoreJsQuerySyntax`
- `CoreJsQueryTests` ← `CoreJsQuerySemantics`
- `CoreJsFoLtl` ← `CoreJsSemantics`
- `CoreJsFoLtlTests` ← `CoreJsQueryTests`, `CoreJsFoLtl`
- `CoreJsQueryToLtl` ← `CoreJsQuerySemantics`, `CoreJsFoLtl`
- `CoreJsQModelSyntax` ← `CoreJsQuerySyntax`
- `CoreJsQModelSemantics` ← `CoreJsQuerySemantics`, `CoreJsQModelSyntax`
- `CoreJsQueryToQModel` ← `CoreJsQModelSemantics`
- `CoreJsMcInterface` ← `CoreJsQueryToQModel`; then `CoreJsMcExplore` ←
  `CoreJsMcInterface`, `CoreJsMcDomain` ← `CoreJsMcExplore`,
  `CoreJsMcTracker` ← `CoreJsMcDomain`, `CoreJsMcAlgorithm` ← `CoreJsMcTracker`,
  `CoreJsMcTests` ← `CoreJsMcAlgorithm`
- `CoreJsMcFinite` ← `CoreJsMcInstance`
- `CoreJsMcInstance` ← `CoreJsMcAlgorithm`, `CoreJsAutomatonSoundness` (the
  only file joining the query chain and the automaton chain)

The query chain and the automaton chain are independent of each other; both
sit on top of the concrete semantics, and meet only in `CoreJsMcInstance`.

### The language and concrete semantics

1. **`CoreJsSyntax.lean`** — `Val`, `Expr`, `BinOp`, `Stmt` (every call /
   lookup / update / `if` / `while` carries a site index `κ`, like
   `binOp`/`objLit`: the automaton names its states after them),
   `Stmt.lits`, `Stmt.sites`. `Loc := Nat` is an `abbrev` (see the `omega`
   gotcha below).
2. **`CoreJsSemantics.lean`** — semantic domains (`Sto`, `Heap`, `Reg`, `Trc`,
   `Act`, `Out`), the `Concrete` typeclass (`litLoc`, `allocC`, `opSem`),
   `ConcreteSpec` (what a sensible concrete instance looks like: injective
   literal locations, fresh allocation, no allocation at literal locations, no
   operator producing a function), `Heap.WF`, the big-step judgement
   `BigStep`, and `BigStepN`, a derivation-height-indexed copy needed because
   `BigStep` lives in `Prop` and has no recursor to induct on height, while
   the automaton soundness proof's `while` case needs the induction
   hypothesis several derivation levels down (`BigStep.toN`/
   `BigStepN.toBigStep` transport between the two; if you add a concrete
   rule, add the matching `BigStepN` constructor and extend `mono`/
   `mono_le`/`toN`/`toBigStep`). An object's location holds the object's
   reference value `.loc l` (object references are values: `sv` compares
   them, operators accept them; and an empty object's location is in use, so
   it is never allocated again). Prototypes are modelled to depth
   one: `Object.prototype` is the literal location of the marker value
   `Val.proto`, object literals get `__proto__ ↦ litLoc .proto`, and a
   lookup whose own property is missing reads `Object.prototype`'s, else
   yields `undefined` (`lookupSProto`/`lookupSMissing` and the dynamic
   twins); abstract lookups go through `AHeap.lookupS`/`lookupD`. Dynamic
   keys are converted to property names as in JS (`Val.toKey`: `a[undefined]`
   is `a["undefined"]`); an object reference or function as a key may denote
   *any* property (`Val.KeyOf`, as `model-js`'s `Dynamic`; abstractly
   `VSet.HasKey`). Also here: heap facts preserved along runs
   (`Heap.Finite`/`BigStep.finite`, `Heap.Defined` and its per-update lemmas,
   `Heap.FidCanon`/`BigStep.fidCanon`: function values live only at their
   literal locations), and the minimal initial configuration (`Reg.empty`,
   `Heap.init Γ fs s`/`Conf.init Γ fs s`: the literals of `s` and of the
   bodies of the functions `fs` — normally all of `Γ`'s, listed so the heap
   stays computable — plus `undefined`; `Heap.init_WF`, `Heap.init_finite`).
   - **`ConcreteSpec.allocC_fresh` only applies to finite heaps.** Demanding
     freshness of *every* heap made the spec unsatisfiable (a heap defined at
     every location has no free one), so anything assuming it was vacuous.
     Proofs using freshness therefore need `Heap.Finite` of the current heap;
     `BigStep.finite` propagates it along a run.
   - **Execution records** `Exec = ⟨trc, obs⟩`, `Obs = ⟨val, dep, ac, sk⟩`,
     `Trc.toList`, `Obs.ofRun`, `Obs.WF` also live here, not in
     `CoreJsQuerySemantics.lean`, even though the query language is their
     first consumer: they are built entirely from `Trc`/`Heap`/`Reg` (no
     dependency on the query syntax), and both `CoreJsQuerySemantics.lean`
     and `CoreJsFoLtl.lean` need them independently. The same goes for the
     record of a concrete run, `Exec.ofRes`, and its well-formedness:
     `Reg.DepInv` (transitive `dep`, every dependency target holds a value),
     `BigStep.depInv`, and `BigStep.obs_wf` / `obs_wf_empty` / `obs_wf_init`
     (a run yields a well-formed observation; needs `ConcreteSpec` and a
     finite starting heap), at the end of the file.

### The automaton-based analysis

3. **`CoreJsAutomatonSyntax.lean`** — call strings (`CallString`,
   `targetCallString`: a recursive call reuses the first open instantiation of
   its target, so no function repeats and `CallString.length_le` bounds the
   length) and the automaton state space `AState`.
4. **`CoreJsAutomatonSemantics.lean`** — the abstract domains (`ALoc`, `VSet`,
   `AHeap`, `ASto`, `AReg`, `AConf`), the `Abstract` class and `AbstractSpec`,
   abstract actions `AAct`, the per-statement effects, the edge relations
   `AExit`/`ARet`/`AEdge` (layered, not mutual: each refers only to itself
   and the ones before it), the whole graph `AGraph`,
   `Labeling`, `Labeling.Valid`, `AnalysisResult` (valid, and covering
   `AConf.init Γ s₀` at the top-level entry: the literals of `s₀` and of
   every body of `Γ`, as a predicate, so it covers `Conf.init Γ fs s₀` for
   every `fs`), walks `AWalk`, and the
   `PendingClosed` framework plus invariant `AConf.FidReserved`.
   - Every edge carries a contribution `C : Labeling → AConf` and an action
     label `ℓ : Labeling → Option AAct` (`none` = the edge cannot be taken
     under this labeling). They take the whole labeling, not only the
     source's label, because a call's return edges start inside the callee
     but are gated on the caller's configuration at the call site.
   - Properties of the accumulated `pending`/`xpending`/`rpending`
     transforms are proved once through `PendingClosed` +
     `AExit.closed`/`ARet.closed`; reuse that rather than writing a new
     induction over the edge relations.
5. **`CoreJsAutomatonRelation.lean`** — the abstraction relation (`AlphaFn`,
   `Heap.Alpha`/`Sto.Alpha`/`Reg.Alpha`/`AConf.Alpha`, `Act.Alpha`/
   `Trc.Alpha`), the per-statement lemmas, the allocation invariant
   `AlphaFn.AllocSafe` (every location `α` maps is in use or a literal
   location) with `AllocSafe.extend`, the cross-spec `CrossSpec` (the one
   assumption relating the two sides: `opSemA` over-approximates `opSem`),
   and the initial abstraction `AlphaFn.lits`. Spec structures are organised
   by meaning: a property of the concrete instance alone goes in
   `ConcreteSpec` even if only the analysis uses it.
6. **`CoreJsAutomatonTotality.lean`** — monotonicity of every edge
   contribution in the labeling (`AGraph.lmono`), arbitrary meets/joins of
   configurations, the least analysis result `Labeling.least` (the meet of
   all analysis results; `exists_least_analysisResult`,
   `exists_valid_labeling`), the propagation operator `Labeling.step` and its
   Kleene iterates (below `least`; a stable iterate *is* `least`), and
   `least_fidReserved` / `least_reservedResult` (the least result is the
   least `ReservedResult`). Termination of Kleene iteration is deliberately not
   claimed: value sets range over an infinite domain and `opSemA` need not
   widen.
7. **`CoreJsAutomatonSoundness.lean`** — `SoundRun` (the conclusion),
   `step_sound` (strong induction on derivation height), `sound`,
   `sound_top` (whole program from `Conf.init Γ fs s₀` against an
   `AnalysisResult`), `sound_least` (against the least one), and
   `SpecModel.satisfiable` (the specs are jointly satisfiable, so none of
   this is vacuous). `step_sound` threads, besides `α`-relatedness: `hsub`
   (the current statement's edges are graph edges), heap finiteness,
   `AllocSafe`, and `FidCanon`.

The concrete and abstract judgements are kept in lockstep: each abstract edge
is named and shaped after its concrete counterpart, and both state the result
configuration's components as variables fixed by equational premises. When you
change one semantics, check the abstraction relation, the soundness cases, and
the monotonicity/preservation lemmas in `CoreJsAutomatonTotality.lean` and at
the end of `CoreJsAutomatonSemantics.lean`.

### The query language

8. **`CoreJsQuerySyntax.lean`** — `Query Q(x⃗) { ∃y⃗: F₁ when I except F₂ }`:
   `QAct`, `Pred`, `Inv` (generic in the variable type, default `Var`, with
   renaming `map`s: the query model instantiates them with its own
   variables), `Pat`, `QBody` (fields `locals`/`pattern`/`when`/`except`),
   `Query`, and the well-formedness predicates `Query.WF`/`QProg.WF` (all variables declared in `x⃗ ∪ y⃗`,
   arities match, no duplicates, callees only *later* in the program list).
   The semantics does *not* assume either. There is no range restriction:
   a local occurring in no action (`∃y. hv(y, 3)`) ranges over all locations.
9. **`CoreJsQuerySemantics.lean`** — the satisfaction relations in interval
   form `t, σ, ξ ⊨ F : i ⇝ j` (`Pat.Sat`/`QBody.Sat`), over execution
   records `Exec`/`Obs` (defined in `CoreJsSemantics.lean` — see its entry
   above for why). Statements and rules are written in the paper's notation,
   as scoped Lean notation (table in the file header): `Θ ⬝ t ⬝ σ ⬝ ξ ⊨ F : i ⇝ j`
   (`Pat.Sat`, `QBody.Sat`; `Δ ⬝ …` for `QProg.Sat`, the paper's
   `Δ, t, σ, ξ ⊨ F : i ⇝ j`) and `σ ⬝ ξ ⊨ I` (`Inv.Sat`/`Pred.Sat`). Keep new
   statements in this notation.
   - The one systematic change from the paper: `⬝` everywhere for the paper's
     `,` (a term followed by `,` — or `;`, `·` — breaks tuples, `⟨…, …⟩` and
     tactic blocks). The paper has no `⊢`: the program is the first
     argument of the list, and `Θ` (its interpretation) takes its place.
   - One notation stands for several relations; the types of `Θ`/`Δ` and
     `F`/`P` pick one, so binders must be typed (`{Θ t σ ξ F i j}` is
     ambiguous; use the `variable`s of the file's sections).
   - The notations are declared *before* the inductive/recursive definitions
     they name (`set_option hygiene false in`) so the defining rules use
     them. `notation` then generates no unexpander, so each has a hand-written
     `app_unexpander` building the node of the notation's named kind. Name
     it without dots (`unexpandPatSat`): a dotted name puts a `scoped`
     attribute in the wrong namespace and it silently never fires.
   Semantic decisions made with the user, worth knowing before touching this
   file:
   - `F₁ & F₂ : i ⇝ j` needs both sides matched from `i`, `j = max j₁ j₂`; one
     action may serve both sides (`a & a ≡ a`).
   - `except F'` is checked over the **whole trace** (`F'` matched from `0`, for
     every end point `k`), for nested queries as well as the top-level one, so a
     guard does not depend on where its query starts. It only constrains the
     query body it belongs to: under `Q ‖ F`, a failing `except` inside `Q`
     just rules out that alternative. Position independence is what the FO-LTL
     translation relies on.
   - `dep(x₁,x₂)` is plain membership `ξ x₂ ∈ σ.dep (ξ x₁)` — no closure in the
     semantics; transitivity of `dep` and reverse-closure of `ac` are the
     `Obs.WF` predicate. `sv` requires both values *defined* and equal.
   - `Exec.Matches` matches from boundary `0`; `Exec.Matches.of_interp`
     (via `Pat.Sat.lower_start`: starting earlier never forces finishing later)
     shows this loses no generality.
   - Invocation `Q(z⃗)` runs `Q`'s body under `[xᵢ ↦ ξ(zᵢ)]` (valuation
     passing, equivalent to capture-free substitution; locals of `Q` are private).
   - Queries live in a **list** (`QProg`) and invocation is resolved by
     structural recursion (`QProg.interp`); `Pat.Sat` takes an interpretation
     `Θ` of invocations as a parameter. This is forced by strict positivity:
     `except` negates `Pat.Sat`, which cannot sit inside the inductive that
     defines it. Acyclicity is thereby built in.
10. **`CoreJsQueryTests.lean`** — a compile-time regression suite: one program
    per statement shape run through `BigStep`, then positive and negative
    query tests over the runs of `pTaint`/`pObjRT`. The `bigstep` tactic builds
    a derivation automatically; `run tac` wraps it for goals of the form
    `∃ r, BigStep … r ∧ P r`; `obs_simp [q]`/`tr_simp` discharge observation
    and trace facts. Its `Concrete` instance is test-only and does **not**
    satisfy `ConcreteSpec` (non-injective `litLoc`), so `BigStep.obs_wf` and
    its variants are not exercised by it. Its runs start from
    `Conf.init Γ₀ fs₀ s`, with `fs₀` listing every function of `Γ₀`; a
    function's string name determines its literal location, so new test
    functions need names of a length not used yet.
    After changing the semantics, `lake build` this file: a failure here means
    a rule or query semantics changed behaviourally.

### FO-LTL over finite traces

11. **`CoreJsFoLtl.lean`** — standard first-order past+future LTL over finite traces,
    organized the way a logic text would present it, with an explicit table in the file
    header mapping each usual component (signature/terms/atomic formulas/formula
    grammar/structures/satisfaction) to its Lean definition:
    - **Signature**: one sort of individuals (`Loc`); relation symbols `lookup/3`,
      `update/3`, `retn/2`, `eq/2`, `sk/1`, `ac/1`, `dep/2`, `sv/2`, `hv(_,c)/1` (one
      per `c : Val`), and the `call_n/(n+1)` family (one per arity `n`, enumerated by
      `Shape`). No function symbols (`## Terms`: only variables).
    - **Atomic formulas / formulas**: `Atom ν` / `Ltl ν` (generic in the variable type
      `ν` so translations can rename), primitives `⊤ ⊥ ¬ ∧ ∨ X U Y S ∃ ∀` with
      `F`/`G` (future) and `O`/`H` (past) derived from `U`/`S`. No normal-form
      restriction — formulas may nest/interleave arbitrarily.
    - **Structures**: `Model` — a rigid part (`obs : Obs`, constant across the trace)
      plus a temporal part (`states`, the actions holding at each position).
    - **Satisfaction**: `Atom.Sat`, `Ltl.Sat` (both written `m ⬝ ξ ⬝ i ⊨ φ`, the
      usual `m, ξ, i ⊨ φ`, same scheme as the query notation), `Ltl.Holds` (at
      boundary `0`).
    Conventions:
    - Positions are *boundaries* `0 … n` (`n` = number of states); boundary `n` is a
      sentinel where no action holds, matching the query semantics' indexing. `X` is
      strong (`i < n ∧ φ (i+1)`); `Y` is false at boundary `0` (no yesterday before the
      start) — both standard for LTL over finite/bounded traces.
    - `Ltl.first := ¬Y⊤` holds only at boundary `0`; `Ltl.atStart φ := O(φ ∧ first)`
      holds at *every* boundary iff `φ` holds at `0` (`sat_atStart`) — the standard way
      to reach back to the start of a finite trace from anywhere in a formula, used to
      translate queries' `except` (checked over the whole trace) without rewriting into
      any normal form. `atStart φ` then behaves like a state atom itself
      (`sat_atStart_indep`).
    - Action atoms are predicates of the state; state atoms read only `σ` and hold at
      every boundary or none (`G p ≡ p ≡ F p`, `sat_G_state`).
    - "Multiple actions cannot happen at the same time": `Model.Excl`,
      `Exec.toModel_excl`, and the finite first-order axiomatisation `Ltl.excl v shapes`
      (relative to a set of action `Shape`s, calls told apart by arity), satisfied by
      every record's model (`Exec.toModel_sat_excl`). Only the soundness direction is
      proved (models of records satisfy it), not that the formula characterises `Excl`.
    - `Model` is deliberately more general than `Exec` (a state is a *predicate* over
      actions, not one action): it is the logic's own class of models, independent of
      how one is produced. `Exec.toModel` is the intended-model construction connecting
      it to the query language; the eventual model-checking algorithm is being built on
      the automaton (`AWalk` over a labeled `AGraph`), not on `Ltl`/`Model` — this file
      stays a self-contained logic definition, not glued to that other development.
12. **`CoreJsFoLtlTests.lean`** — compile-time tests on `eTaint`, an explicit record
    for the run of `pTaint` (linked to the real run by `link_eTaint`): sequencing,
    sentinel, state atoms, quantification, exclusivity, and the past operators
    (`Y`/`O`/`H`/`atStart`).
13. **`CoreJsQueryToLtl.lean`** — the translation from queries into `Ltl LVar`
    (`LVar := Var ⊕ Nat`: original source names, or a synthetic tag freshly minted per
    invoked-query occurrence to avoid capture when inlining — see the file header for why
    this is needed independently of the in-place, non-prenex translation style), and the
    theorem that it is semantics-preserving over execution records (via
    `Exec.toModel`) — for the *full* query language, including guards, locals and
    invocation, not just an invocation-free fragment.
    - `Pat.Tr ρ Δ F K n φ n'` / `QBody.Tr ρ Δ P K n φ n'`: the translation as a
      *relation* (the specification), continuation-style. Genuinely mutually recursive with itself (a query's
      body may invoke further queries), which is fine for a `Prop` — unlike `Pat.Sat`, it
      never negates *itself* (a guard's `except` becomes `.not` applied to an
      already-produced formula, ordinary data, not a negated occurrence of the relation),
      so it needs no external `Interp`-style parameter.
    - `Pat.tr`/`QBody.tr`/`Query.tr` compute it (`Option`: `none` iff an invocation is
      unresolved or has the wrong arity), by well-founded recursion on
      `(Δ.length, sizeOf F)`. They agree with the relation both ways (`Pat.tr_sound`,
      `Pat.Tr.tr_eq`; `Query.tr_eq_some_iff`), so the relation is functional and the
      correctness theorems apply to the computed formula (`Query.tr_computed_correct`).
      `Query.trStr` renders the result (`Ltl.toStr` in `CoreJsFoLtl.lean`, fresh tags as
      `#k`); the `computed` section `#guard`s the formulas for example queries — update
      those strings deliberately if the translation changes.
    - A query body `∃y⃗: F when I except F'` translates to
      `∃y⃗: I ∧ atStart(¬ tr(F',⊤)) ∧ tr(F,K)`, written *in place* at the invocation — this
      is exactly why `except` has whole-trace semantics and why `Ltl.atStart` exists:
      both are needed together to make the `&` rule
      (`tr(F₁&F₂,K) = tr(F₁,K) ∧ tr(F₂,K)`) exact without hoisting into any normal form.
    - `correct_all` (`PatCorrect`/`QBodyCorrect`, by strong induction on the remaining
      program's length) proves every `Pat.Tr`/`QBody.Tr` witness semantics-preserving
      for every well-formed program; `exists_all` proves a witness always exists.
      Together, `Query.tr_correct`/`Query.exists_tr_correct` give the headline result:
      for a well-formed query at the head of a well-formed program, matching it on an
      execution record agrees with the record's model satisfying the translated formula
      at the query's own top environment (`Query.topEnv`). A worked example (`exSink`)
      exercises this concretely. The file's closing `## Proof structure` section lists
      the supporting machinery: renaming/freshness, the `updateFresh`/
      `Ren.sat_updateFresh_extendFresh` bridge to `LEnv.bind`, the coincidence/locality
      lemmas, and `Ltl.Indep` (continuations must be insensitive to fresh-tag updates for
      the guard case's `Mono` argument to transfer).

### Query models

14. **`CoreJsQModelSyntax.lean`** — the automaton form of a query, decided with
    the user for the model checker: one model (`QModel`) with every invocation
    inlined, made of components (`QComp`): the positive part `main` and one per
    `except` clause in `comps`, referred to by index. Variables `MVar`: `src x`
    (the top query's) or `tag n y` (local `y` of the `n`-th inlined
    invocation). States `QSt` are named after the pattern (`seqR f s`
    remembers the final state of the first half, `&` is a pair), so every state
    determines the invocations used to reach it. Edges are `ε` or
    `act as` (one trace action equal to every action of `as`; `act []` is
    `Any`, explicit self-loops on every state but `‖`'s start). Labels per
    state: `inv` (invariants accumulated so far — replaces a global invariant;
    the model checker prunes with it, sound because `inv` grows along edges,
    `QComp.Mono`), `scope` (variables bound at this level so far), and `exc`
    (except components, read at final states only).
15. **`CoreJsQModelSemantics.lean`** — `Run` (reads `t[i..j)`), `QComp.Acc`
    (new values for the final state's `scope`, a run, `inv` holds, no `exc`
    component satisfied), `compSat` (by fuel; `QModel.depth` bounds except
    nesting), `QModel.Sat`. Substitutions are total; why `scope` is needed (a
    local occurring only in an `except` is bound *outside* it): see the file
    header. `QComp.ReadsIn`/`acc_coincide`: a component only reads the
    variables of its caller and its own scope.
16. **`CoreJsQueryToQModel.lean`** — `Pat.build`/`QBody.build`/`QProg.build`
    (structural; invocations resolved like `QProg.interp`, through a `Builder`
    parameter; an unresolvable invocation is an automaton with no final state,
    so the translation is total) and `Query.toQModel`.
    `Query.toQModel_correct`: for `QProg.WF (q :: Δ)`, `(q.toQModel Δ).Sat e ls
    ↔ Exec.Matches (q :: Δ) e q.name ls`, for the full language;
    `Query.toQModel_wf`: components are `Closed` and `Mono`. Proof: `Built`
    (bookkeeping: fresh tags, scope, `ReadsIn`) and `Correct` per
    construction; `patOK` (induction on the pattern), `bodyOK`, `buildOK`
    (induction on the program). `#guard`s at the end show computed models —
    update them deliberately if the construction changes.

### Model checking

Formulated generically, over interfaces with specifications, decided with the
user (not tied to the OCaml verifier in `model-js/src/verifier`, of which it is
an abstraction). `MODELCHECK_PLAN.md` (untracked) records the design and the
phases; both (the positive part; `except` with *must* semantics and
trackers) are done.

17. **`CoreJsMcInterface.lean`** — trace systems `TSys` (walks yield abstract
    records: visible labels + facts), abstractions `Abs` (`act`/`facts` relate
    concrete to abstract; `matchA`, `may`, `must`, `mustA` are the abstract
    judgements, `inhab` says an abstract value certainly denotes a location;
    `Abs.Sound` their specification), `Covers` (every concrete record of
    interest is abstracted by a walk's — the shape of `sound_top`), invariants
    by polarity (`Abs.inv`), `LRun` (runs of a component over a list of
    labels; `Run.toLRun`/`LRun.toRun` bridge to and from `Run`), the abstract
    semantics `QModel.ASat` (main accepts in *may* polarity; no `except`
    component of the final state *must*-accepts the same labels,
    `QComp.AMust`/`QModel.AExcl`), and `QModel.asat_of_matches` (completeness
    of the abstraction).
    - `QComp.AMust` ignores final states with nested `except`s (no trackers
      of trackers) and asks `inhab` of the new values of the variables the
      final invariants read: a must-judgement needs a concrete location to
      instantiate the component's own variables with. Variables occurring in
      must-matched actions get one from the trace (`Abs.Sound.mustA`).
18. **`CoreJsMcExplore.lean`** — generic worklist exploration with a visited
    set (*progress*): terminates given an existential finite closed list
    (only in the termination measure; erased), `mem_explore` (exactly the
    reachable states). Proofs use the generated `exploreAux.induct`.
19. **`CoreJsMcDomain.lean`** — assignment domains `ADom` with `ADom.Spec`
    (`top`: every variable unconstrained — this is what constrains variables
    occurring only in invariants; `constrain` exact; `refine` loses no
    solution; `solve` exact, with an extra test `g` reading only given
    variables — the `except` check; finitely many reachable elements); separable
    matching `Abs.Sep`; the non-relational instance `nonrel` (generalised arc
    consistency, enumeration in `solve`) with `nonrel_spec`/`nonrel_finite`.
20. **`CoreJsMcTracker.lean`** — trackers `Tracker` (a summary of the labels
    read, `step`ped at every visible label; `excl` reads off the `except`
    check; `Tracker.Spec`: after reading `T`, `excl` is `QModel.AExcl … T`),
    `LRun` composition lemmas, `ε`-closure by `explore`, and the
    enumerating instance `enumTracker` (entries `(k, q, vs)`: component `k`
    at `q` under the values `vs` of `QModel.compVars`; always a filter of the
    finite `tUniv`) with `enumTracker_spec`.
21. **`CoreJsMcAlgorithm.lean`** — finite trace systems `FinTSys`, search
    states `(p, q, d, τ)` (`τ` a tracker), `mcSucc`, `witnesses` (acceptance
    passes `excOk` to `solve`); `witnesses_ne_nil_iff` (the search decides
    `ASat` exactly), `mem_witnesses`, `model_check_complete`(`_enum`).
    Refining with the current state's invariants is sound because of
    `QComp.Mono`. Trackers are deterministic in the labels
    (`reach_sound`: `τ = tr.run T`), which is why progress loses nothing.
22. **`CoreJsMcInstance.lean`** — the program automaton labeled by an analysis
    result as `autTSys`/`autAbs` (values `Option ALoc`, facts `topFacts` = join
    of the top-level final configurations, `must`/`mustA`/`inhab` never
    true, so `except`s never exclude there), `aut_covers` (from `sound_top`),
    `aut_asat`, `Covers.of_walks` (to move to a finite presentation).
    Must-matching on function identity would need `α` to map only
    `litLoc (.fid f)` to `litLocA (.fid f)`, an invariant `SoundRun` does not
    expose (`AllocSafe` does not say what allocated locations map to).
23. **`CoreJsMcFinite.lean`** — what the algorithm runs on for the program.
    Finitely many abstract values `FV locs` (a location of `locs` or `•`;
    `FV.cl` collapses, `FV.mem_all`), location-list actions `FAct V`, Boolean
    fact tables `FFacts V`, their abstraction `listAbs` (sound, separable:
    `listSep`); `FAct.Over`/`FFacts.Over` (containment of the automaton's
    collapsed labels and facts), `Covers.of_finite`; `FinForm Γ s₀ L locs`
    (finite trace system + facts + the two containment proofs),
    `FinForm.check` and **`FinForm.check_complete`** (the end-to-end
    theorem: every matching run of the program yields a witness); the
    coarsest finite form `FinForm.univ` (needs only the program's arities,
    via `AGraph.call_arity`) and `check_complete_univ`. The automaton's
    domains are predicates, so a *precise* finite form is not computed here.
24. **`CoreJsMcTests.lean`** — `#guard`s on a toy trace system, including the
    query of the issue where a variable occurs only in the invariant, and
    `except` tests (a certain call excludes, a possible one does not, a loop
    that can be skipped keeps its witness).

## Lean gotchas hit in this repository

- **`omega` cannot reason about `=`/`≠` on `Loc`** (an `abbrev` for `Nat`); it
  handles `≤`/`<`. Convert with explicit `Nat` lemmas (`Nat.ne_of_gt`,
  `Nat.le_trans`, `Nat.eq_of_mul_eq_mul_left`, …) or restate the fact over
  `Nat` (`have h' : (a : Nat) = b := h`) first.
- **`ALoc` is a `def`, not an `abbrev`**, for `Nat`: there are no numerals of
  type `ALoc` (write `(1 : Nat)` where an `ALoc` is expected), and `omega`
  does not see through it at all — restate over `Nat` first.
- **Helper lemmas for dot-notation must live in the type's namespace.** A
  `theorem QBody.Sat.simple` declared inside `namespace CoreJS.Tests` is
  *not* found by `.simple`/`h.simple`; declare it as
  `theorem _root_.CoreJS.QBody.Sat.simple`.
- **`;;` is overloaded** (`Stmt.seq` and `Trc.seq`, both scoped `infixr:70`);
  it resolves by expected type, so annotate when a literal is ambiguous.
- **Hole metavariables from `refine ⟨?r, …⟩` are opaque** and cannot be
  assigned by `apply`; use `apply Exists.intro` when a later tactic must
  discover the witness (this is what `run` does).
- Do not depend on `Reg`/`Heap` structure eta: `{ δ with ac := … }` is not
  definitionally `δ`. Use a congruence lemma (`Reg.DepInv.congr`) instead.
- **Mutual inductives (`Pat.Tr`/`QBody.Tr`):** the `induction` tactic cannot
  induct on a mutual-family hypothesis directly, but a `mutual` block of
  theorems defined by pattern matching on the hypothesis (structural
  recursion) works (`CoreJsQueryToLtl.lean`). The automaton's edge relations
  are deliberately *not* mutual, so plain `induction` works on them
  (`AExit.closed`/`ARet.closed`).
- **Spec structures with instance parameters** (`ConcreteSpec`,
  `AbstractSpec`, `CrossSpec`): an anonymous constructor `⟨…⟩` for them
  synthesizes the `[Concrete]`/`[Abstract]` argument by instance search, not
  from the expected type. To build one for a specific instance, make the
  instance local (`attribute [local instance] …`) — see `SpecModel`.
- **An inductive predicate may not recurse under `∃`** ("nested inductive
  datatypes parameters cannot contain local variables"): state the recursive
  premise as `∀ c', … → P c'` and any existence separately, non-recursively
  (`QComp.ReadsIn`).
- **`prefix` is a keyword**: it cannot name a structure field.
- When a lemma's implicit configuration can be inferred from more than one
  hypothesis, Lean picks the first; pass it explicitly (`(c := …)`) if that
  is the wrong one (the call cases of `step_sound` do this).

## `sorry` policy

There are no `sorry`s and no `axiom`s in the development
(`grep -rn sorry analysis` is empty; `#print axioms` on the headline
theorems shows only `propext`, `Classical.choice`, `Quot.sound`). Keep it
that way: if a proof cannot be completed, leave an explicit, commented `sorry`
stating exactly what is missing rather than papering over it with an `axiom`
or a weakened statement — but do not merge work in that state without saying
so. New assumptions belong in a spec structure (`ConcreteSpec`,
`AbstractSpec`, `CrossSpec`) and must stay jointly satisfiable: extend
`SpecModel.satisfiable` when you add one.
