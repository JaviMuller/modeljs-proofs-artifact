/-
  # Core JavaScript — Syntax

  Formalisation of Figure A1 of Appendix A of
  "Model Checking Security Properties of Node.js Packages".

  Plain Lean 4 — no Mathlib required.
-/

namespace CoreJS

/-! ## Basic syntactic categories

The paper's leaf sorts.  We fix concrete representations for the sorts whose
internal structure is irrelevant to the semantics: identifiers are strings and
locations are natural numbers. -/

/-- Program variables `x ∈ Var`. -/
abbrev Var := String

/-- Function identifiers `f ∈ Fid`. -/
abbrev Fid := String

/-- Property names `p ∈ Prop ⊆ Str`.  (Named `PropName` because `Prop` is
    reserved in Lean.) -/
abbrev PropName := String

/-- Locations `l ∈ Loc`. -/
abbrev Loc := Nat

/-- Instruction indices `κ`, used by the heap allocator to annotate binary
    operations and object initialisations. -/
abbrev Idx := Nat

/-! ## Values, expressions, operators -/

/-- Values `v ∈ Val ::= n ∈ Num | s ∈ Str | b ∈ Bool | f ∈ Fid | l ∈ Loc`.

    `Num` is modelled by `Int`; nothing in the semantics depends on this
    choice (numbers are only ever consumed by `⊕`, which is a parameter). -/
inductive Val where
  | num  (n : Int)
  | str  (s : String)
  | bool (b : Bool)
  | fid  (f : Fid)
  | loc  (l : Loc)
  /-- `undefined`.  Introduced by the semantics as the implicit return value of
      a function body that falls through without an explicit `return`, and
      also writable directly in source text as an ordinary literal. -/
  | undef
  deriving DecidableEq, Repr, Inhabited

/-- Expressions `e ∈ Exp ::= v | x ∈ Var`. -/
inductive Expr where
  | val (v : Val)
  | var (x : Var)
  deriving DecidableEq, Repr

/-- Binary operators `⊕`.  The paper leaves the operator set abstract and
    only assumes an interpretation `⊕(v₁, v₂)`; we fix a representative set
    here and supply the interpretation as a parameter of the semantics
    (see `CoreJS.Concrete.opSem` in `CoreJsSemantics.lean`). -/
inductive BinOp where
  | add | sub | mul | div
  | eq | lt | le
  | and | or
  | concat
  deriving DecidableEq, Repr

/-! ## Statements -/

/-- Statements `s ∈ Stmt`.

    ```
    s ::= skip | x := e | x :=κ e₁ ⊕ e₂ | x :=κ {pᵢ : eᵢ | ⁿᵢ₌₁}
        | x := e.p | x := e₁[e₂] | e₁.p := e₂ | e₁[e₂] := e₃
        | x := e(e₁, ..., eₙ) | s₁; s₂ | if(e) {s₁} else {s₂}
        | while(e) {s} | return e | setTaint e | setSink e
    ```

    Object literals carry their fields as an association list; the semantics
    assumes the property names of a literal to be pairwise distinct. -/
inductive Stmt where
  /-- `skip` -/
  | skip
  /-- `x := e` -/
  | assign   (x : Var) (e : Expr)
  /-- `x :=κ e₁ ⊕ e₂` -/
  | binOp    (x : Var) (κ : Idx) (op : BinOp) (e₁ e₂ : Expr)
  /-- `x :=κ {pᵢ : eᵢ}` -/
  | objLit   (x : Var) (κ : Idx) (fs : List (PropName × Expr))
  /-- `x := e.p` (static property lookup) -/
  | lookupS  (x : Var) (e : Expr) (p : PropName)
  /-- `x := e₁[e₂]` (dynamic property lookup) -/
  | lookupD  (x : Var) (e₁ e₂ : Expr)
  /-- `e₁.p := e₂` (static property update) -/
  | updateS  (e₁ : Expr) (p : PropName) (e₂ : Expr)
  /-- `e₁[e₂] := e₃` (dynamic property update) -/
  | updateD  (e₁ e₂ e₃ : Expr)
  /-- `x := e(e₁, ..., eₙ)` -/
  | call     (x : Var) (e : Expr) (es : List Expr)
  /-- `s₁; s₂` -/
  | seq      (s₁ s₂ : Stmt)
  /-- `if(e) {s₁} else {s₂}` -/
  | ifElse   (e : Expr) (s₁ s₂ : Stmt)
  /-- `while(e) {s}` -/
  | whileDo  (e : Expr) (s : Stmt)
  /-- `return e` -/
  | ret      (e : Expr)
  /-- `setTaint e` -/
  | setTaint (e : Expr)
  /-- `setSink e` -/
  | setSink  (e : Expr)
  deriving Repr

@[inherit_doc] scoped infixr:70 (name := stmtSeq) " ;; " => Stmt.seq

/-! ## Literals occurring in a program

Needed for Definition A4 (well-formedness of concrete heaps w.r.t. a
statement): every literal `v` occurring in `s` must be stored at its fixed
location `l_v`.

Note that the static lookup/update rules emit trace actions mentioning `l_p`,
the location of the *string* `p`; so property names of static accesses are
counted as literals of the statement as well. -/

/-- Literal values occurring in an expression. -/
def Expr.lits : Expr → List Val
  | .val v => [v]
  | .var _ => []

private def litsOfExprs (es : List Expr) : List Val :=
  es.foldr (fun e acc => e.lits ++ acc) []

/-- Literal values occurring in a statement (including the property names of
    static property accesses, which are reified as string literals). -/
def Stmt.lits : Stmt → List Val
  | .skip              => []
  | .assign _ e        => e.lits
  | .binOp _ _ _ e₁ e₂ => e₁.lits ++ e₂.lits
  | .objLit _ _ fs     => litsOfExprs (fs.map Prod.snd)
  | .lookupS _ e p     => .str p :: e.lits
  | .lookupD _ e₁ e₂   => e₁.lits ++ e₂.lits
  | .updateS e₁ p e₂   => .str p :: (e₁.lits ++ e₂.lits)
  | .updateD e₁ e₂ e₃  => e₁.lits ++ e₂.lits ++ e₃.lits
  | .call _ e es       => e.lits ++ litsOfExprs es
  | .seq s₁ s₂         => s₁.lits ++ s₂.lits
  | .ifElse e s₁ s₂    => e.lits ++ s₁.lits ++ s₂.lits
  | .whileDo e s       => e.lits ++ s.lits
  | .ret e             => e.lits
  | .setTaint e        => e.lits
  | .setSink e         => e.lits

end CoreJS
