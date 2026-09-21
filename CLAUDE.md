# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repository is

A Lean 4 formalisation (no Mathlib) built around the paper "Model Checking
Security Properties of Node.js Packages":

- a small "Core JavaScript" language and its concrete semantics (Appendix A);
- a static analysis over it, formulated on the `automaton-trace-model` branch
  as a call-string *automaton* with a *labeling* (replacing the paper's
  μ-trace/summary machinery), plus an abstraction relation and a soundness
  proof for it;
- a *query language* for describing vulnerable behaviours, with a satisfaction
  relation over execution records (trace + taint observation), and a bridge
  from concrete runs to such records.

There is no application code — the entire deliverable is the Lean source under
`analysis/`. Two design documents live at the repository root:
`DESIGN_AND_PLAN.md` (the automaton design) and `PROBLEMS.md` (a numbered log
of implementation decisions taken where the design left things open). The
file headers cite them by section / decision number; read the cited passage
before changing the code it explains.

## Build / check commands

- Build everything: `lake build`
- Type-check a single file: `lake env lean analysis/<File>.lean` (its imports
  must already be built, i.e. run `lake build` first).
- `lean-toolchain` pins `leanprover/lean4:v4.32.1`; use `lake`/`lean` via
  `elan`, no other setup is required.

### `lakefile.toml` lists modules explicitly

`globs` enumerates every module of the `Analysis` library; a `.lean` file that
is not listed is silently skipped by `lake build`. **When adding a file under
`analysis/`, add its module name (no extension) to `globs`.** The list is
currently complete. (The old `CoreJsAbstract*` files were deleted; do not
resurrect references to them — some header comments still mention them
historically.)

## Architecture

All files are in `namespace CoreJS`. What each file imports:

- `CoreJsSemantics` ← `CoreJsSyntax`
- `CoreJsAutomatonSyntax` ← `CoreJsSyntax`
- `CoreJsAutomatonSemantics` ← `CoreJsAutomatonSyntax`, `CoreJsSemantics`
- `CoreJsAutomatonRelation` ← `CoreJsAutomatonSemantics`
- `CoreJsAutomatonSoundness` ← `CoreJsAutomatonRelation`
- `CoreJsQuerySyntax` ← `CoreJsSyntax`
- `CoreJsQuerySemantics` ← `CoreJsSemantics`, `CoreJsQuerySyntax`
- `CoreJsQueryBridge` ← `CoreJsQuerySemantics`
- `CoreJsQueryTests` ← `CoreJsQueryBridge`
- `CoreJsFoLtl` ← `CoreJsQuerySemantics`
- `CoreJsFoLtlTests` ← `CoreJsQueryTests`, `CoreJsFoLtl`

The query chain and the automaton chain are independent of each other; both
sit on top of the concrete semantics.

### The language and concrete semantics

1. **`CoreJsSyntax.lean`** — `Val`, `Expr`, `BinOp`, `Stmt` (every call /
   lookup / update / `if` / `while` carries a site index `κ`, a deliberate
   deviation from the paper, see the file's REMARK), `Stmt.lits`, `Stmt.sites`.
   `Loc := Nat` is an `abbrev` (see the `omega` gotcha below).
2. **`CoreJsSemantics.lean`** — semantic domains (`Sto`, `Heap`, `Reg`, `Trc`,
   `Act`, `Out`), the `Concrete` typeclass (`litLoc`, `allocC`, `opSem`),
   `ConcreteSpec` (its side conditions), `Heap.WF`, the big-step judgement
   `BigStep`, and `BigStepN`, a derivation-height-indexed copy needed because
   `BigStep` lives in `Prop` and has no recursor to induct on height
   (`BigStep.toN`/`BigStepN.toBigStep` transport between the two; if you add a
   concrete rule, add the matching `BigStepN` constructor and extend `mono`/
   `mono_le`/`toN`/`toBigStep`). Also here: `Heap.Finite` (with
   `BigStep.finite`), and the minimal initial configuration
   (`Reg.empty`, `Heap.init`, `Conf.init`, `Heap.init_WF`, `Heap.init_finite`).
   - **`ConcreteSpec.allocC_fresh` only applies to finite heaps.** Demanding
     freshness of *every* heap made the spec unsatisfiable (a heap defined at
     every location has no free one), so anything assuming it was vacuous.
     Proofs using freshness therefore need `Heap.Finite` of the current heap;
     `BigStep.finite` propagates it along a run.

### The automaton-based analysis

3. **`CoreJsAutomatonSyntax.lean`** — call strings and the automaton state
   space `AState`.
4. **`CoreJsAutomatonSemantics.lean`** — the abstract domains (self-contained:
   `ALoc`, `VSet`, `AHeap`, `ASto`, `AReg`, `AConf`), the `Abstract` class, the
   per-statement effect functions, the mutually inductive edge relations
   `AExit`/`AEdge`/`ARet`, `Labeling`, `Labeling.Valid`, `AnalysisResult`.
5. **`CoreJsAutomatonRelation.lean`** — the abstraction relation (`AlphaFn`,
   `Heap.Alpha`/`Sto.Alpha`/`Reg.Alpha`/`AConf.Alpha`) and its lemmas.
6. **`CoreJsAutomatonSoundness.lean`** — `step_sound`, `sound`, `sound_top`.
   **Incomplete.** 18 of 19 statement-shape cases are proved. Remaining
   `sorry`s: the `binOp`/`objLit` cases of `step_sound` (need an
   `α`-freshness invariant, and now also `Heap.Finite` of the current heap as a
   hypothesis threaded through `sound`) and `exists_valid_labeling`. Read the
   "Remaining work" section at the end of the file for the plan.

The concrete and abstract judgements are kept in lockstep: each abstract rule
is named and shaped after its concrete counterpart, and both state the result
configuration's components as variables fixed by equational premises. When you
change one semantics, check the abstraction relation and the soundness cases.

### The query language

7. **`CoreJsQuerySyntax.lean`** — `Query Q(x⃗) { ∃y⃗: F₁ when I except F₂ }`:
   `QAct`, `Pred`, `Inv`, `Pat`, `Guarded`, `Query`, and the well-formedness
   predicates `Query.WF`/`QProg.WF` (all variables declared in `x⃗ ∪ y⃗`,
   arities match, no duplicates, callees only *later* in the program list) and
   the optional `Query.Safe` (range restriction). The semantics does *not*
   assume any of these.
8. **`CoreJsQuerySemantics.lean`** — execution records `Exec = ⟨trc, obs⟩`,
   `Obs = ⟨val, dep, ac, sk⟩`, `Obs.ofRun`, `Obs.WF`, and the satisfaction
   relations of Fig. 5 in interval form `t, σ, ξ ⊨ F : i ⇝ j`
   (`Pat.Sat`/`Guarded.Sat`). Semantic decisions made with the user, worth
   knowing before touching this file:
   - `F₁ & F₂ : i ⇝ j` needs both sides matched from `i`, `j = max j₁ j₂`; one
     action may serve both sides (`a & a ≡ a`).
   - `except F'` is checked over the **whole trace** (`F'` matched from `0`, for
     every end point `k`), for nested queries as well as the top-level one, so a
     guard does not depend on where its query starts. It only constrains the
     guarded pattern it belongs to: under `Q ‖ F`, a failing `except` inside `Q`
     just rules out that alternative. (Earlier it was checked from `i`; the
     change makes guards position-independent, which the FO-LTL translation
     relies on.)
   - `dep(x₁,x₂)` is plain membership `ξ x₂ ∈ σ.dep (ξ x₁)` — no closure in the
     semantics; transitivity of `dep` and reverse-closure of `ac` are the
     `Obs.WF` predicate. `sv` requires both values *defined* and equal.
   - Invocation `Q(z⃗)` runs `Q`'s body under `[xᵢ ↦ ξ(zᵢ)]` (valuation
     passing, equivalent to capture-free substitution; locals of `Q` are private).
   - Queries live in a **list** (`QProg`) and invocation is resolved by
     structural recursion (`QProg.interp`); `Pat.Sat` takes an interpretation
     `Θ` of invocations as a parameter. This is forced by strict positivity:
     `except` negates `Pat.Sat`, which cannot sit inside the inductive that
     defines it. Acyclicity is thereby built in.
9. **`CoreJsQueryBridge.lean`** — `Reg.DepInv` (transitive `dep`, every
   dependency target holds a value), `BigStep.depInv`, and the bridge theorems
   `BigStep.obs_wf` / `obs_wf_empty` / `obs_wf_init`: a concrete run yields a
   well-formed observation (needs `ConcreteSpec` and a finite starting heap).
10. **`CoreJsQueryTests.lean`** — a compile-time regression suite: one program
    per statement shape run through `BigStep`, then positive and negative
    query tests over the runs of `pTaint`/`pObjRT`. The `bigstep` tactic builds
    a derivation automatically; `run tac` wraps it for goals of the form
    `∃ r, BigStep … r ∧ P r`; `obs_simp [q]`/`tr_simp` discharge observation
    and trace facts. Its `Concrete` instance is test-only and does **not**
    satisfy `ConcreteSpec` (non-injective `litLoc`), so the bridge theorems are
    not exercised by it. Function bodies in its `Γ₀` must mention no literals
    (`Heap.init` only holds the main statement's literals).
    After changing the semantics, `lake build` this file: a failure here means
    a rule or query semantics changed behaviourally.

### FO-LTL over finite traces

11. **`CoreJsFoLtl.lean`** — first-order LTL (`Ltl ν`, primitives `⊤ ⊥ ¬ ∧ ∨ X U ∃ ∀`,
    with `F`/`G`/`imp`/`conj`/`disj` derived; atoms `Atom ν`: the four actions, the
    taint/value predicates and `=`; generic in the variable type `ν`), finite models
    (`Model`: list of states, each the set of actions holding there, plus a static
    `Obs`), and `Exec.toModel`, which materialises an execution record. Conventions
    worth knowing:
    - Positions are *boundaries* `0 … n` (`n` = number of states); boundary `n` is a
      sentinel where no action holds, matching the query semantics' indexing. `X` is
      strong (`i < n ∧ φ (i+1)`); `F φ := ⊤ U φ`. So `F(a ∧ X ⊤)` is "`a` occurs".
    - Action atoms are predicates of the state; state atoms read only `σ` and hold at
      every boundary or none (`G p ≡ p ≡ F p`, `sat_G_state`).
    - "Multiple actions cannot happen at the same time": `Model.Excl`,
      `Exec.toModel_excl`, and the finite first-order axiomatisation `Ltl.excl v shapes`
      (relative to a set of action `Shape`s, calls told apart by arity), satisfied by
      every record's model (`Exec.toModel_sat_excl`). Only the soundness direction is
      proved (models of records satisfy it), not that the formula characterises `Excl`.
12. **`CoreJsFoLtlTests.lean`** — compile-time tests on `eTaint`, an explicit record
    for the run of `pTaint` (linked to the real run by `link_eTaint`): sequencing,
    sentinel, state atoms, quantification, exclusivity.

## Lean gotchas hit in this repository

- **`omega` cannot reason about `=`/`≠` on `Loc`** (an `abbrev` for `Nat`); it
  handles `≤`/`<`. Convert with explicit `Nat` lemmas (`Nat.ne_of_gt`,
  `Nat.le_trans`, …) or state such facts over `Nat`.
- **Helper lemmas for dot-notation must live in the type's namespace.** A
  `theorem Guarded.Sat.simple` declared inside `namespace CoreJS.Tests` is
  *not* found by `.simple`/`h.simple`; declare it as
  `theorem _root_.CoreJS.Guarded.Sat.simple`.
- **`;;` is overloaded** (`Stmt.seq` and `Trc.seq`, both scoped `infixr:70`);
  it resolves by expected type, so annotate when a literal is ambiguous.
- **Hole metavariables from `refine ⟨?r, …⟩` are opaque** and cannot be
  assigned by `apply`; use `apply Exists.intro` when a later tactic must
  discover the witness (this is what `run` does).
- Do not depend on `Reg`/`Heap` structure eta: `{ δ with ac := … }` is not
  definitionally `δ`. Use a congruence lemma (`Reg.DepInv.congr`) instead.

## `sorry` policy

`CoreJsAutomatonSoundness.lean` is a proof in progress and its `sorry`s are
intentional placeholders for known-remaining work, not accidents — the file's
own header explains this. Don't paper over a `sorry` with an `axiom` or a
weakened statement to make the build "succeed"; either prove the case or leave
it as `sorry` and note what's missing. There are no `axiom`s in the
development; `grep -n sorry analysis/*.lean` shows exactly what remains. The
query files (`CoreJsQuery*.lean`) and the concrete semantics are `sorry`-free.
