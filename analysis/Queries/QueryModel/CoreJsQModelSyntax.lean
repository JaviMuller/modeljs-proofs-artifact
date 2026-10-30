/-
  # Core JavaScript — Query Models (syntax)

  A *query model* is the automaton form of a query, built for the model
  checker: every invocation is inlined, the positive pattern is a
  nondeterministic automaton over trace actions, and every `except` becomes a
  further component of the same model.  Its semantics is in
  `CoreJsQModelSemantics.lean`; the translation from queries, and the proof
  that it preserves their meaning, in `CoreJsQueryToQModel.lean`.

  ## Shape

  * **Variables** (`MVar`): the top query's own variables `src x`, and
    `tag n y`, the local `y` of the `n`-th inlined invocation.  Inlining needs
    the tags: two invocations of the same query, or a caller passing its own
    `y` to a query with a local `y`, must not share a variable.
  * **States** (`QSt`) are named after the pattern they come from
    (`seqL`/`seqR`/`altL`/`both`, …), so that composing automata needs no
    renumbering.  A state of a sequence remembers *which* final state of its
    first half it went through (`seqR f s`), and a state of `&` is a pair; so
    every state determines the invocations a run has gone through to reach
    it, which is what lets the labels below be functions of the state.
  * **Edges** (`QEdge`) are `ε`-edges or action edges `act as`: one trace
    action, equal to *every* action of `as` under the substitution.  `act []`
    is `Any`; a joint step of `&` concatenates the two sides' lists.  Every
    state except the transient start of `‖` has an explicit `Any` self-loop,
    so a run reads the *whole* trace (the query semantics allows arbitrary
    gaps before every action).
  * **Labels**, per state, accumulated along every run that reaches it:
    - `inv s`: the invariants (`when`) of the query and of every invocation
      entered so far — a model checker may discard a substitution as soon as
      it violates `inv` of the current state, since `inv` only grows along
      edges;
    - `scope s`: the variables bound (existentially) at this level so far:
      the query's locals and the tags of the invocations entered;
    - `exc s`, read only at final states: the indices of the `except`
      components the run must not match.
  * **Components** (`QComp`): one per automaton — the positive part `main`,
    and one per `except` clause in `comps` (the query's own and those of the
    inlined invocations).  An `except` component's own variables are the ones
    in its own `scope`; everything else it mentions is bound by the component
    referring to it.  Components refer to each other by their index in
    `comps`; all of them together form one automaton over the states
    `(component, QSt)`.
  * `depth` bounds the nesting of `except` components (an `except` invoking a
    query with an `except` of its own, …), which the semantics recurses on.

  Plain Lean 4 — no Mathlib required.
-/

import Queries.QueryLanguage.CoreJsQuerySyntax

namespace CoreJS

/-! ## Variables -/

/-- Variables of a query model. -/
inductive MVar where
  /-- A variable of the top query (parameter, local, or undeclared). -/
  | src (x : Var)
  /-- The local `x` of the `n`-th inlined invocation. -/
  | tag (n : Nat) (x : Var)
  deriving DecidableEq, Repr

/-- `v` is not a tag minted at or after `n`. -/
def MVar.Below (n : Nat) : MVar → Prop
  | .src _   => True
  | .tag k _ => k < n

/-- `v` is a tag minted in `[n, n')`. -/
def MVar.InRange (n n' : Nat) : MVar → Prop
  | .src _   => False
  | .tag k _ => n ≤ k ∧ k < n'

/-! ## Edges and states -/

/-- Edge labels. -/
inductive MLbl where
  /-- An `ε`-edge: reads nothing. -/
  | eps
  /-- Reads one trace action, equal to every action of `as`; `act []` is `Any`. -/
  | act (as : List (QAct MVar))
  deriving DecidableEq, Repr

/-- `Any`: reads one arbitrary action. -/
abbrev MLbl.any : MLbl := .act []

/-- Variables of an edge label. -/
def MLbl.vars : MLbl → List MVar
  | .eps    => []
  | .act as => as.flatMap QAct.vars

/-- States, named after the pattern they come from. -/
inductive QSt where
  /-- The state of `ε`, the state before an action, the state of an
      unresolvable invocation. -/
  | s0
  /-- The state after an action. -/
  | s1
  /-- The start of `F₁ ‖ F₂`. -/
  | altS
  /-- A state of the left/right alternative. -/
  | altL (s : QSt)
  | altR (s : QSt)
  /-- A state of the first half of `F₁ ; F₂`. -/
  | seqL (s : QSt)
  /-- A state `s` of the second half, entered from the final state `f` of the
      first half. -/
  | seqR (f s : QSt)
  /-- A state of `F₁ & F₂`. -/
  | both (s₁ s₂ : QSt)
  deriving DecidableEq, Repr

abbrev QEdge := QSt × MLbl × QSt

/-! ## Components and models -/

/-- One automaton with its labels. -/
structure QComp where
  start  : QSt
  states : List QSt
  edges  : List QEdge
  finals : List QSt
  /-- Invariants accumulated so far. -/
  inv    : QSt → List (Inv MVar)
  /-- Variables bound at this level so far. -/
  scope  : QSt → List MVar
  /-- The `except` components to avoid (read at final states). -/
  exc    : QSt → List Nat

/-- A query model. -/
structure QModel where
  /-- The top query's parameters, bound by the caller. -/
  params : List Var
  /-- The positive part. -/
  main   : QComp
  /-- The `except` components, referred to by index. -/
  comps  : List QComp
  /-- A bound on the nesting of `except` components. -/
  depth  : Nat

/-! ## Well-formedness

Properties of the models built by the translation (proved in
`CoreJsQueryToQModel.lean`); the semantics does not assume them. -/

/-- Start, edges and final states stay within `states`. -/
structure QComp.Closed (c : QComp) : Prop where
  start  : c.start ∈ c.states
  edges  : ∀ s l s', (s, l, s') ∈ c.edges → s ∈ c.states ∧ s' ∈ c.states
  finals : ∀ f ∈ c.finals, f ∈ c.states

/-- Invariants and scope only grow along edges, so a substitution violating
    `inv` at some state violates it at every state reachable from there. -/
def QComp.Mono (c : QComp) : Prop :=
  ∀ s l s', (s, l, s') ∈ c.edges → c.inv s ⊆ c.inv s' ∧ c.scope s ⊆ c.scope s'

end CoreJS
