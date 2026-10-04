# modeljs_proofs

A Lean 4 formalisation of a static analysis for security properties of
JavaScript programs, over a small core language. It proves the analysis
sound: every concrete execution is matched by the analysis's finite
automaton, trace included. It also formalises a query language for
vulnerable behaviours, together with a semantics-preserving translation of
queries into first-order linear temporal logic.

The core language and the query language come from the paper *Model Checking
Security Properties of Node.js Packages*. The analysis is formulated
differently here, as a finite-state automaton over call strings, because a
model checker searching the automaton for query matches needs a finite state
space to terminate.

Everything is plain Lean 4: no Mathlib, no `sorry`, no axioms beyond Lean's
standard three (`propext`, `Classical.choice`, `Quot.sound`).

## What is proved

**The language.** Core JavaScript has values, variables, binary operations,
object literals, static and dynamic property lookup and update, first-order
functions called through variables (with recursion and `return` anywhere),
`if`, `while`, and two taint statements (`setTaint`, `setSink`). Its concrete
semantics is a big-step judgement `Γ ⊢ ⟨h, ρ, δ, s⟩ ⇓ ⟨h', ρ', δ', t, o⟩` that
produces a heap, store, taint register, trace of heap/call actions, and
outcome. It is parametric in the literal-to-location injection, the
allocator and the binary operators (`Concrete`, constrained by
`ConcreteSpec`).

**The analysis.** The automaton's states are indexed by call strings: a
recursive call reuses its target's first open instantiation, so call strings
are bounded. Its edges are a static function of the program. A *labeling*
assigns an abstract heap, store and taint register to every state. It is
*valid* when every edge's contribution is below its target's label, and an
*analysis result* also covers the initial configuration. Edges carry
abstract actions, so a walk through the labeled automaton has a trace.

- **Soundness** (`sound_top`, `sound_least`, `CoreJsAutomatonSoundness.lean`).
  For every run of a program from its initial configuration and every
  analysis result `L`, there is an abstraction function `α` such that
  - the run's final heap, store and register are `α`-related to `L`'s label
    at the state the run ends at, and
  - some walk through the automaton labeled by `L` has a trace that is
    `α`-related, action by action, to the run's trace.
- **Totality** (`exists_least_analysisResult`, `CoreJsAutomatonTotality.lean`).
  Every program has a *least* analysis result, the most precise one: the
  meet of all analysis results. It is a fixed point of one-step propagation,
  it lies above every Kleene iterate from `⊥`, and it equals any iterate that
  stabilises.
- **Non-vacuity** (`SpecModel.satisfiable`). The assumptions the theorems
  make about the analysis's parameters (`ConcreteSpec`, `AbstractSpec`,
  `CrossSpec`) are jointly satisfiable.

**The query language.** Queries such as `Query Q(x⃗) { ∃y⃗: F when I except F' }`
describe patterns over execution records, i.e. traces together with taint
observations.

- **Runs yield well-formed records** (`BigStep.obs_wf_init`,
  `CoreJsSemantics.lean`).
- **Translation into FO-LTL** (`Query.tr_correct`, `Query.exists_tr_correct`,
  `CoreJsQueryToLtl.lean`). Every well-formed query has a translation into
  first-order past/future LTL over finite traces, and a record matches the
  query exactly when its model satisfies the translation. This covers the
  full query language, including guards, local variables and query
  invocation. The translation is also computable (`Query.tr`, with
  `Query.tr_computed_correct`); `#guard` checks in the same file show the
  formulas it produces for example queries.

## Repository layout

All sources are in `analysis/`, in namespace `CoreJS`, split into four
directories:

```
analysis/
├── CoreJS/                 the language and its concrete semantics
├── Queries/
│   ├── QueryLanguage/      queries, their semantics, tests
│   └── FoLtl/              FO-LTL, its tests, the query translation
└── ProgramAutomaton/       the automaton-based analysis
```

| File | Contents |
|---|---|
| **`CoreJS/`** | |
| `CoreJsSyntax.lean` | values, expressions, operators, statements (every construct the automaton needs to name carries a site index) |
| `CoreJsSemantics.lean` | semantic domains, execution records, `Concrete`/`ConcreteSpec`, the big-step semantics and its height-indexed copy, invariants preserved by runs, concrete runs as well-formed execution records |
| **`ProgramAutomaton/`** | |
| `CoreJsAutomatonSyntax.lean` | call strings and automaton states |
| `CoreJsAutomatonSemantics.lean` | abstract domains, `Abstract`/`AbstractSpec`, abstract actions, edges, the graph, labelings and their validity, analysis results, walks |
| `CoreJsAutomatonRelation.lean` | the abstraction relation on configurations and traces, `CrossSpec`, the allocation invariant |
| `CoreJsAutomatonTotality.lean` | monotonicity, the least analysis result, the fixpoint/Kleene reading |
| `CoreJsAutomatonSoundness.lean` | the soundness theorems, the satisfiability witness |
| **`Queries/QueryLanguage/`** | |
| `CoreJsQuerySyntax.lean` | queries and their well-formedness |
| `CoreJsQuerySemantics.lean` | satisfaction of queries over execution records |
| `CoreJsQueryTests.lean` | compile-time regression tests for the concrete and query semantics |
| **`Queries/FoLtl/`** | |
| `CoreJsFoLtl.lean` | first-order LTL over finite traces, and records as its models |
| `CoreJsFoLtlTests.lean` | compile-time tests for the logic |
| `CoreJsQueryToLtl.lean` | the query-to-FO-LTL translation and its correctness |

Imports, by file name (`A ← B, C`: `A` imports `B` and `C`):

```
CoreJsSemantics           ← CoreJsSyntax
CoreJsAutomatonSyntax     ← CoreJsSyntax
CoreJsAutomatonSemantics  ← CoreJsAutomatonSyntax, CoreJsSemantics
CoreJsAutomatonRelation   ← CoreJsAutomatonSemantics
CoreJsAutomatonTotality   ← CoreJsAutomatonSemantics
CoreJsAutomatonSoundness  ← CoreJsAutomatonRelation, CoreJsAutomatonTotality
CoreJsQuerySyntax         ← CoreJsSyntax
CoreJsQuerySemantics      ← CoreJsSemantics, CoreJsQuerySyntax
CoreJsQueryTests          ← CoreJsQuerySemantics
CoreJsFoLtl               ← CoreJsSemantics
CoreJsFoLtlTests          ← CoreJsQueryTests, CoreJsFoLtl
CoreJsQueryToLtl          ← CoreJsQuerySemantics, CoreJsFoLtl
```

The automaton development and the query development are independent of
each other. Both build on the concrete semantics.

A good reading order for the analysis is syntax → semantics → automaton
syntax → automaton semantics → relation → soundness, with totality at any
point after the automaton semantics. For the query side, read query syntax →
query semantics → FO-LTL → translation. Each file's header explains its
structure and the reasons for its non-obvious choices.

## Building

Requirements: [`elan`](https://github.com/leanprover/elan), which installs
the toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.32.1`)
automatically. Nothing else is needed.

```sh
lake build                               # check everything
lake env lean analysis/CoreJS/CoreJsSemantics.lean   # check one file (after `lake build`)
```

The test files are checked at compile time: if `lake build` succeeds, the
tests pass. Every module must be listed in `lakefile.toml`'s `globs` (by its
path under `analysis/`, dots for slashes, e.g. `CoreJS.CoreJsSyntax`), because
an unlisted file is silently skipped.
