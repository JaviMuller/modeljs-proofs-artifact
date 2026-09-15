# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repository is

A Lean 4 formalisation (no Mathlib) of the appendices of the paper "Model
Checking Security Properties of Node.js Packages": a small "Core JavaScript"
language, its concrete semantics, a static analysis (abstract semantics) over
it, an abstraction relation between the two, and a soundness proof for the
analysis. There is no application code — the entire deliverable is the Lean
source under `analysis/`.

## Build / check commands

- Build the default targets: `lake build`
- Type-check a single file without building the whole project:
  `lake env lean analysis/<File>.lean`
- `lean-toolchain` pins `leanprover/lean4:v4.32.1`; use `lake`/`lean` via
  `elan` as usual, no other toolchain setup is required.

### Important gotcha: `lakefile.toml`'s glob list is not the full file set

`lakefile.toml` declares the library's source files explicitly via `globs`,
and that list currently lags behind what's actually in `analysis/`:

```toml
globs = ["CoreJsSyntax", "CoreJsSemantics", "CoreJsAbstractSyntax", "CoreJsAbstractSemantics",
         "CoreJsAbstractionRelation"]
```

`CoreJsAbstractionSoundness.lean` exists and imports `CoreJsAbstractionRelation`,
but is **not** in this list, so a plain `lake build` silently skips it (no
error — it's simply not a target). To type-check it, either:
- add it to `globs` in `lakefile.toml`, or
- compile it directly: `lake env lean analysis/CoreJsAbstractionSoundness.lean`
  (its only local dependency, `CoreJsAbstractionRelation`, is already built by
  `lake build`).

When adding a new `.lean` file under `analysis/`, add its module name (no
extension) to `globs` so `lake build` actually covers it.

## Architecture

The files form a linear dependency chain, each corresponding to a specific
part of the paper's Appendix A/B. Read them in this order to build up
context; each file's header comment names the exact figures/definitions it
formalises:

1. **`CoreJsSyntax.lean`** — the language: `Val`, `Expr`, `BinOp`, `Stmt`.
   No semantics. Also defines `Stmt.lits`, the literal values occurring in a
   statement (needed by both well-formedness definitions below).
2. **`CoreJsSemantics.lean`** — the *concrete* semantics (Appendix A):
   semantic domains (`Sto`, `Heap`, `Reg`, `Trc`, `Act`, `Out`), the
   `Concrete` typeclass parameterising literal-location injection/allocator/
   operator interpretation, expression evaluation, heap well-formedness
   (`Heap.WF`), and the big-step judgement `BigStep` (`Γ ⊢ c ⇓[s] r`). Also
   defines `BigStepN`, a derivation-height-indexed copy of `BigStep` — needed
   because `BigStep` lives in `Prop` and has no recursor to do strong
   induction on height with; `BigStep.toN`/`BigStepN.toBigStep` show the two
   coincide.
3. **`CoreJsAbstractSyntax.lean`** — the abstract domains (Appendix B.1, Figs.
   B1/Def. B4/B5), independent of the concrete semantics: `ALoc`, `ALocSet`,
   `VSet` (value sets plus a `⊤`), `ASto`/`AHeap`/`AReg`/`AAct`/`ATrc`/`AOut`,
   the `⊑` order (`Def. B4`) and `⊔` join (`Def. B5`), plus the general-purpose
   `Join` typeclass introduced locally (no Mathlib).
4. **`CoreJsAbstractSemantics.lean`** — the abstract big-step semantics (Figs.
   B6/B7): abstract expression evaluation, weak vs. strong heap/register
   updates, the `Abstract` typeclass (abstract literal locations/allocator/
   `⊕̂`), the mutually-recursive `ABigStep`/`ACallBranch` judgement, call
   summaries (`ASummary`, `ASigma`) for handling recursion via
   assume/guarantee (`[Call-Fix]`/`[Call-Assume]`), and the top-level analysis
   entry point `SA`. **Read the `REMARKS` section at the end of this file
   first** — it documents several places where the implementation
   deliberately deviates from (or fixes gaps in) the paper's Fig. B7, e.g. the
   multi-target `[Function Call]` rule, the totalised `[If-Then-Else]` outcome
   join, and the strong update in `[Object Initialization]`.
5. **`CoreJsAbstractionRelation.lean`** — the relation `∼α` connecting
   concrete and abstract states (Def. B8) via a partial abstraction function
   `AlphaFn : Loc → Option ALoc`, plus the supporting lemmas the soundness
   proof needs: `α`-extension (Lemma B10), expression evaluation (Lemma B9),
   store update (Lemma B11), and `α`-monotonicity of the abstract domains
   (Lemma B13). See its `REMARK A/B/C` comments for how partiality of `α` and
   the `Out.Alpha` asymmetry (`ret ⊑ cont` but not the reverse) are handled.
6. **`CoreJsAbstractionSoundness.lean`** — Theorem B15 itself. Opens with a
   "Supporting order, monotonicity and finiteness results" section: facts
   needed by the proof but not involving the abstraction relation itself
   (`⊑` is a preorder on `AAct`/`AOut`/`ATrc`, substitution/unfolding laws for
   `μ`-traces, monotonicity of abstract evaluation such as `aevalE_mono`,
   and the ascending-chain-condition groundwork for why a `[Call-Fix]`
   fixpoint search terminates) — kept here rather than in
   `CoreJsAbstractionRelation.lean` precisely because they don't touch
   `AlphaFn`. **Currently incomplete**: the height-indexed statement
   (`soundnessN`), the `SigmaValid` assume/guarantee invariant, the
   `[Weakening]`-absorbing generation-lemma pattern (`abs_gen_skip`), and the
   `[Skip]` case are done; every other case is `sorry`. There are no
   `axiom`s, so `sorry` is the only way anything is left unproved — grep for
   it to see exactly what remains, and read the "Remaining work" section at
   the end of the file for the planned order of attack (generation lemmas per
   statement shape, then assignment/return/sequence/lookup/update, then the
   two cases where `α` grows (`binOp`/`objLit`), then `if`/`while`, then
   multi-target calls, then `[Call-Fix]`/`[Call-Assume]`).

   When adding a new lemma that this file's proof needs: if it mentions
   `AlphaFn`/`Heap.Alpha`/`Sto.Alpha`/etc., it belongs in
   `CoreJsAbstractionRelation.lean`; otherwise it belongs in the "Supporting
   ..." section here. Don't reintroduce a separate grab-bag file for it.

### Two semantics, one relation

The concrete (`CoreJsSemantics.lean`) and abstract (`CoreJsAbstractSemantics.lean`)
judgements are deliberately kept in lockstep: each abstract rule is named and
shaped after its concrete counterpart, and both are stated with the result
configuration's components introduced as variables fixed by equational
premises (so the Lean rule reads as a literal transcription of the paper's
figure). When modifying one semantics, check whether the abstraction relation
(`CoreJsAbstractionRelation.lean`) and the corresponding case of
`soundnessN` need to change too.

### Height-indexing pattern

`BigStep`/`ABigStep` are ordinary `Prop`-valued inductives, so Lean gives no
structural recursion principle strong enough for the soundness proof (in
particular, `[Call-Fix]`'s premise quantifies over *all* executions of a
callee body, not just sub-derivations of the term being inducted on).
`BigStepN Γ n` re-adds an explicit height so `soundnessN` can do strong
induction on it (`Nat.strongRecOn`); `.toN`/`.toBigStep` transport between the
heighted and unheighted relations at the boundary. If you add new concrete
rules, add the matching `BigStepN` constructor and extend `mono`/`mono_le`/
`toN`/`toBigStep`.

### `sorry` policy

`CoreJsAbstractionSoundness.lean` is a proof in progress and its `sorry`s are
intentional placeholders for known-remaining work, not accidents — the file's
own header explains this. Don't paper over a `sorry` with an `axiom` or a
weakened statement to make the build "succeed"; either prove the case or leave
it as `sorry` and note what's missing.
