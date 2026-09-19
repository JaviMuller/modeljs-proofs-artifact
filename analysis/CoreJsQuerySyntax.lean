/-
  # Core JavaScript — Query Syntax

  The query language used to describe (vulnerable) behaviours of executions:

  ```
  query ::= Query Q(x⃗) { P }
      P ::= ⟨exists y⃗:⟩ F₁ ⟨when I⟩ ⟨except F₂⟩
      F ::= ε | a | Q(x₁, ..., xₙ) | F ; F | F ‖ F | F & F
      a ::= x₁ := x₂[x₃] | x₁[x₂] := x₃ | Call(x_f, [x₁, ..., xₙ]) | Retn(x_f, x)
      I ::= p | ¬I | I ∨ I | I ∧ I | true | false
      p ::= sk(x) | ac(x) | dep(x₁, x₂) | sv(x₁, x₂) | hv(x, c)
  ```

  This file is syntax only: the satisfaction relation over execution records
  lives in `CoreJsQuerySemantics.lean`.  Besides the AST it defines the
  syntactic well-formedness conditions (`Query.WF`, `QProg.WF`) that the
  semantics does *not* assume, so that the semantics stays total.

  Plain Lean 4 — no Mathlib required.
-/

import CoreJsSyntax

namespace CoreJS

/-- Query names `Q`. -/
abbrev QName := String

/-! ## Query actions, predicates, invariants -/

/-- Query actions `a`, the syntactic counterparts of the trace actions. -/
inductive QAct where
  /-- `x₁ := x₂[x₃]` -/
  | lookup (x₁ x₂ x₃ : Var)
  /-- `x₁[x₂] := x₃` -/
  | update (x₁ x₂ x₃ : Var)
  /-- `Call(x_f, [x₁, ..., xₙ])` -/
  | call   (xf : Var) (xs : List Var)
  /-- `Retn(x_f, x)` -/
  | retn   (xf x : Var)
  deriving DecidableEq, Repr

/-- Taint/value predicates `p ::= sk(x) | ac(x) | dep(x₁, x₂) | sv(x₁, x₂) | hv(x, c)`. -/
inductive Pred where
  | sk  (x : Var)
  | ac  (x : Var)
  | dep (x₁ x₂ : Var)
  | sv  (x₁ x₂ : Var)
  | hv  (x : Var) (c : Val)
  deriving DecidableEq, Repr

/-- Query invariants `I ::= p | ¬I | I ∨ I | I ∧ I | true | false`. -/
inductive Inv where
  | pred (p : Pred)
  | not  (I : Inv)
  | or   (I₁ I₂ : Inv)
  | and  (I₁ I₂ : Inv)
  | tt
  | ff
  deriving DecidableEq, Repr

/-! ## Action patterns and guarded patterns -/

/-- Action patterns `F ::= ε | a | Q(x₁, ..., xₙ) | F ; F | F ‖ F | F & F`. -/
inductive Pat where
  /-- `ε` -/
  | eps
  /-- `a` -/
  | act   (a : QAct)
  /-- `Q(x₁, ..., xₙ)`, an invocation of another query. -/
  | query (Q : QName) (zs : List Var)
  /-- `F₁ ; F₂` -/
  | seq   (F₁ F₂ : Pat)
  /-- `F₁ ‖ F₂` -/
  | alt   (F₁ F₂ : Pat)
  /-- `F₁ & F₂` -/
  | both  (F₁ F₂ : Pat)
  deriving DecidableEq, Repr

/-- Guarded action patterns `P ::= ⟨exists y⃗:⟩ F₁ ⟨when I⟩ ⟨except F₂⟩`.

    The omitted clauses default, as in the paper, to no local variables
    (`locals = []`), `true` (`when = .tt`) and no excluded pattern
    (`except = none`). -/
structure Guarded where
  /-- `y⃗`, the local (existentially bound) variables. -/
  locals : List Var := []
  /-- `F₁`, the vulnerable behaviour. -/
  body   : Pat
  /-- `I`, the query invariant. -/
  when   : Inv := .tt
  /-- `F₂`, the excluded (mitigation) pattern. -/
  except : Option Pat := none
  deriving DecidableEq, Repr

/-- Queries `Query Q(x⃗) { P }`. -/
structure Query where
  name   : QName
  params : List Var
  body   : Guarded
  deriving DecidableEq, Repr

/-- A query program: a list of queries, each of which may only invoke queries
    that appear *later* in the list (see `QProg.WF`).  A cons-list rather than
    a map, so that the semantics is definable by structural recursion — the
    paper's requirement that query invocation be acyclic is then built in. -/
abbrev QProg := List Query

/-- The (first) query named `Q`. -/
def QProg.find? (Δ : QProg) (Q : QName) : Option Query :=
  List.find? (fun q => q.name == Q) Δ

/-! ## Variables and invocations occurring in a query -/

/-- Variables of a query action. -/
def QAct.vars : QAct → List Var
  | .lookup x₁ x₂ x₃ => [x₁, x₂, x₃]
  | .update x₁ x₂ x₃ => [x₁, x₂, x₃]
  | .call xf xs      => xf :: xs
  | .retn xf x       => [xf, x]

/-- Variables of a predicate. -/
def Pred.vars : Pred → List Var
  | .sk x       => [x]
  | .ac x       => [x]
  | .dep x₁ x₂  => [x₁, x₂]
  | .sv x₁ x₂   => [x₁, x₂]
  | .hv x _     => [x]

/-- Variables of an invariant. -/
def Inv.vars : Inv → List Var
  | .pred p   => p.vars
  | .not I    => I.vars
  | .or I₁ I₂ => I₁.vars ++ I₂.vars
  | .and I₁ I₂ => I₁.vars ++ I₂.vars
  | .tt       => []
  | .ff       => []

/-- Variables of an action pattern (including invocation arguments). -/
def Pat.vars : Pat → List Var
  | .eps        => []
  | .act a      => a.vars
  | .query _ zs => zs
  | .seq F₁ F₂  => F₁.vars ++ F₂.vars
  | .alt F₁ F₂  => F₁.vars ++ F₂.vars
  | .both F₁ F₂ => F₁.vars ++ F₂.vars

/-- The invocations `(Q, z⃗)` occurring in an action pattern. -/
def Pat.calls : Pat → List (QName × List Var)
  | .eps        => []
  | .act _      => []
  | .query Q zs => [(Q, zs)]
  | .seq F₁ F₂  => F₁.calls ++ F₂.calls
  | .alt F₁ F₂  => F₁.calls ++ F₂.calls
  | .both F₁ F₂ => F₁.calls ++ F₂.calls

/-- Variables of the body, invariant and excluded pattern of a guarded
    pattern (not including the `locals` binder list itself). -/
def Guarded.vars (g : Guarded) : List Var :=
  g.body.vars ++ g.when.vars ++ (g.except.map Pat.vars).getD []

/-- The invocations occurring in the body or the excluded pattern. -/
def Guarded.calls (g : Guarded) : List (QName × List Var) :=
  g.body.calls ++ (g.except.map Pat.calls).getD []

/-! ## Well-formedness

The satisfaction relation is defined for *every* query, well-formed or not;
these predicates single out the queries the paper talks about. -/

/-- Every variable used by the query is declared in `x⃗ ∪ y⃗`, and the two
    binder lists are together duplicate-free. -/
def Query.Declared (q : Query) : Prop :=
  (q.params ++ q.body.locals).Nodup ∧
  ∀ v ∈ q.body.vars, v ∈ q.params ∨ v ∈ q.body.locals

/-- Every invocation in `q` names a query of `Δ` and passes as many
    arguments as that query has parameters. -/
def Query.CallsOK (Δ : QProg) (q : Query) : Prop :=
  ∀ c ∈ q.body.calls, ∃ q', QProg.find? Δ c.1 = some q' ∧ q'.params.length = c.2.length

/-- A query is well formed with respect to the queries `Δ` it may invoke. -/
def Query.WF (Δ : QProg) (q : Query) : Prop :=
  q.Declared ∧ q.CallsOK Δ

/-- A query program is well formed iff every query is well formed with
    respect to the queries *after* it, and names are pairwise distinct.
    Acyclicity of invocation is thereby guaranteed. -/
def QProg.WF : QProg → Prop
  | []     => True
  | q :: Δ => q.WF Δ ∧ QProg.find? Δ q.name = none ∧ QProg.WF Δ

/-- Variables that are bound by an action of the pattern on every way of
    matching it.  An alternative binds only what both branches bind, and an
    invocation is *assumed* to bind its arguments (which is only right if
    the callee is itself safe — this is an approximation). -/
def Pat.bound : Pat → List Var
  | .eps        => []
  | .act a      => a.vars
  | .query _ zs => zs
  | .seq F₁ F₂  => F₁.bound ++ F₂.bound
  | .alt F₁ F₂  => F₁.bound.filter (· ∈ F₂.bound)
  | .both F₁ F₂ => F₁.bound ++ F₂.bound

/-- *Safety* (range restriction): every local variable occurs in an action
    of `F₁`.  Optional; not needed by the semantics.  Without it a local such
    as in `∃y. hv(y, 3)` ranges over locations that occur nowhere in the
    execution. -/
def Query.Safe (q : Query) : Prop :=
  ∀ y ∈ q.body.locals, y ∈ q.body.body.bound

end CoreJS
