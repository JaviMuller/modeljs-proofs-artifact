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

import CoreJS.CoreJsSyntax

namespace CoreJS

/-- Query names `Q`. -/
abbrev QName := String

/-! ## Predicates, invariants, query actions -/

/-! Actions, predicates and invariants are generic in the type `ν` of the
variables they mention, defaulting to the source variables `Var`: the query
model (`Queries/QueryModel/`) instantiates them with its own variables after
inlining invocations. -/

/-- Taint/value predicates `p ::= sk(x) | ac(x) | dep(x₁, x₂) | sv(x₁, x₂) | hv(x, c)`. -/
inductive Pred (ν : Type := Var) where
  | sk  (x : ν)
  | ac  (x : ν)
  | dep (x₁ x₂ : ν)
  | sv  (x₁ x₂ : ν)
  | hv  (x : ν) (c : Val)
  deriving DecidableEq, Repr

/-- Query invariants `I ::= p | ¬I | I ∨ I | I ∧ I | true | false`. -/
inductive Inv (ν : Type := Var) where
  | pred (p : Pred ν)
  | not  (I : Inv ν)
  | or   (I₁ I₂ : Inv ν)
  | and  (I₁ I₂ : Inv ν)
  | tt
  | ff
  deriving DecidableEq, Repr

/-- Query actions `a`, the syntactic counterparts of the trace actions. -/
inductive QAct (ν : Type := Var) where
  /-- `x₁ := x₂[x₃]` -/
  | lookup (x₁ x₂ x₃ : ν)
  /-- `x₁[x₂] := x₃` -/
  | update (x₁ x₂ x₃ : ν)
  /-- `Call(x_f, [x₁, ..., xₙ])` -/
  | call   (xf : ν) (xs : List ν)
  /-- `Retn(x_f, x)` -/
  | retn   (xf x : ν)
  deriving DecidableEq, Repr

/-! ## Action patterns and query bodies -/

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

/-- Query bodies `P ::= ⟨exists y⃗:⟩ F₁ ⟨when I⟩ ⟨except F₂⟩`.

    The omitted clauses default to no local variables
    (`locals = []`), `true` (`when = .tt`) and no excluded pattern
    (`except = none`). -/
structure QBody where
  /-- `y⃗`, the local (existentially bound) variables. -/
  locals  : List Var := []
  /-- `F₁`, the vulnerable behaviour. -/
  pattern : Pat
  /-- `I`, the query invariant. -/
  when    : Inv := .tt
  /-- `F₂`, the excluded (mitigation) pattern. -/
  except  : Option Pat := none
  deriving DecidableEq, Repr

/-- Queries `Query Q(x⃗) { P }`. -/
structure Query where
  name   : QName
  params : List Var
  body   : QBody
  deriving DecidableEq, Repr

/-- A query program: a list of queries, each of which may only invoke queries
    that appear *later* in the list (see `QProg.WF`).  A cons-list rather than
    a map, so that the semantics is definable by structural recursion —
    acyclic query invocation is then built in. -/
abbrev QProg := List Query

/-- The (first) query named `Q`. -/
def QProg.find? (Δ : QProg) (Q : QName) : Option Query :=
  List.find? (fun q => q.name == Q) Δ

/-! ## Variables and invocations occurring in a query -/

/-- Variables of a query action. -/
def QAct.vars {ν} : QAct ν → List ν
  | .lookup x₁ x₂ x₃ => [x₁, x₂, x₃]
  | .update x₁ x₂ x₃ => [x₁, x₂, x₃]
  | .call xf xs      => xf :: xs
  | .retn xf x       => [xf, x]

/-- Variables of a predicate. -/
def Pred.vars {ν} : Pred ν → List ν
  | .sk x       => [x]
  | .ac x       => [x]
  | .dep x₁ x₂  => [x₁, x₂]
  | .sv x₁ x₂   => [x₁, x₂]
  | .hv x _     => [x]

/-- Variables of an invariant. -/
def Inv.vars {ν} : Inv ν → List ν
  | .pred p   => p.vars
  | .not I    => I.vars
  | .or I₁ I₂ => I₁.vars ++ I₂.vars
  | .and I₁ I₂ => I₁.vars ++ I₂.vars
  | .tt       => []
  | .ff       => []

/-! Renaming the variables of actions, predicates and invariants. -/

def QAct.map {ν μ} (ρ : ν → μ) : QAct ν → QAct μ
  | .lookup x₁ x₂ x₃ => .lookup (ρ x₁) (ρ x₂) (ρ x₃)
  | .update x₁ x₂ x₃ => .update (ρ x₁) (ρ x₂) (ρ x₃)
  | .call xf xs      => .call (ρ xf) (xs.map ρ)
  | .retn xf x       => .retn (ρ xf) (ρ x)

def Pred.map {ν μ} (ρ : ν → μ) : Pred ν → Pred μ
  | .sk x      => .sk (ρ x)
  | .ac x      => .ac (ρ x)
  | .dep x₁ x₂ => .dep (ρ x₁) (ρ x₂)
  | .sv x₁ x₂  => .sv (ρ x₁) (ρ x₂)
  | .hv x c    => .hv (ρ x) c

def Inv.map {ν μ} (ρ : ν → μ) : Inv ν → Inv μ
  | .pred p    => .pred (p.map ρ)
  | .not I     => .not (I.map ρ)
  | .or I₁ I₂  => .or (I₁.map ρ) (I₂.map ρ)
  | .and I₁ I₂ => .and (I₁.map ρ) (I₂.map ρ)
  | .tt        => .tt
  | .ff        => .ff

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

/-- Variables of the pattern, invariant and excluded pattern of a query
    body (not including the `locals` binder list itself). -/
def QBody.vars (P : QBody) : List Var :=
  P.pattern.vars ++ P.when.vars ++ (P.except.map Pat.vars).getD []

/-- The invocations occurring in the body or the excluded pattern. -/
def QBody.calls (P : QBody) : List (QName × List Var) :=
  P.pattern.calls ++ (P.except.map Pat.calls).getD []

/-! ## Well-formedness

The satisfaction relation is defined for *every* query, well-formed or not;
these predicates single out the queries that make sense to write. -/

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

end CoreJS
