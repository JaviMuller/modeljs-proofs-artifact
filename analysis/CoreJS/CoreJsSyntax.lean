/-
  # Core JavaScript — Syntax

  Values, expressions, binary operators and statements of Core JavaScript, a
  small imperative core of JavaScript with first-order functions called
  through variables, objects with named properties, and two taint-tracking
  statements (`setTaint`, `setSink`).

  Plain Lean 4 — no Mathlib required.
-/

namespace CoreJS

/-! ## Basic syntactic categories

The leaf sorts. Those whose internal structure is irrelevant to the semantics
get fixed concrete representations: identifiers are strings and locations are
natural numbers. -/

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
  /-- An object reference: the value an object literal stores at its own
      location (so object references are values, compared by `sv`). -/
  | loc  (l : Loc)
  /-- `undefined`.  Introduced by the semantics as the implicit return value of
      a function body that falls through without an explicit `return`, and
      also writable directly in source text as an ordinary literal. -/
  | undef
  /-- Not a source value: a marker whose literal location `litLoc .proto` is
      `Object.prototype`, the one prototype object the semantics models
      (prototype chains of length one). Sharing the literal machinery gives
      it a fixed location, committed by the abstraction up front and never
      returned by allocation. Source code may write `Object.prototype` as
      this literal. -/
  | proto
  deriving DecidableEq, Repr, Inhabited

/-- The property name a value denotes when used as a key, when it has a
    fixed one: JS converts every key to a string (`a[undefined]` is
    `a["undefined"]`, `a[1]` is `a["1"]`). Object references and functions
    have none here: JS uses `"[object Object]"` (unless `toString` is
    overridden) and the function's source text, neither of which is
    modelled; see `Val.KeyOf`. -/
def Val.toKey : Val → Option PropName
  | .str s  => some s
  | .num n  => some (toString n)
  | .bool b => some (if b then "true" else "false")
  | .undef  => some "undefined"
  | .proto  => some "[object Object]"
  | .fid _  => none
  | .loc _  => none

/-- Used as a key, `v` may denote the property `p`: exactly its string form
    when it has one (`Val.toKey`), and *any* property otherwise (object
    references, functions) — the over-approximation `model-js` also makes
    (`Dynamic` properties). -/
def Val.KeyOf (v : Val) (p : PropName) : Prop :=
  match v.toKey with
  | some q => q = p
  | none   => True

/-- Expressions `e ∈ Exp ::= v | x ∈ Var`. -/
inductive Expr where
  | val (v : Val)
  | var (x : Var)
  deriving DecidableEq, Repr

/-- Binary operators `⊕`.  Only their interpretation `⊕(v₁, v₂)` matters to
    the semantics, and it is a parameter (`CoreJS.Concrete.opSem` in
    `CoreJsSemantics.lean`); the operator set itself is a representative
    choice. `and`/`or` produce a value: JS's short-circuit `&&`/`||`, which
    return one of their operands, are expressed with `ifElse` and `assign`
    instead (see `ConcreteSpec.opSem_fid` in `CoreJsSemantics.lean`). -/
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
  /-- `x :=κ e.p` (static property lookup) -/
  | lookupS  (x : Var) (κ : Idx) (e : Expr) (p : PropName)
  /-- `x :=κ e₁[e₂]` (dynamic property lookup) -/
  | lookupD  (x : Var) (κ : Idx) (e₁ e₂ : Expr)
  /-- `e₁.p :=κ e₂` (static property update) -/
  | updateS  (κ : Idx) (e₁ : Expr) (p : PropName) (e₂ : Expr)
  /-- `e₁[e₂] :=κ e₃` (dynamic property update) -/
  | updateD  (κ : Idx) (e₁ e₂ e₃ : Expr)
  /-- `x :=κ e(e₁, ..., eₙ)` -/
  | call     (x : Var) (κ : Idx) (e : Expr) (es : List Expr)
  /-- `s₁; s₂` -/
  | seq      (s₁ s₂ : Stmt)
  /-- `ifκ(e) {s₁} else {s₂}` -/
  | ifElse   (κ : Idx) (e : Expr) (s₁ s₂ : Stmt)
  /-- `whileκ(e) {s}` -/
  | whileDo  (κ : Idx) (e : Expr) (s : Stmt)
  /-- `return e` -/
  | ret      (e : Expr)
  /-- `setTaint e` -/
  | setTaint (e : Expr)
  /-- `setSink e` -/
  | setSink  (e : Expr)
  deriving Repr

@[inherit_doc] scoped infixr:70 (name := stmtSeq) " ;; " => Stmt.seq

/-! ## Literals occurring in a program

Needed for the well-formedness of concrete heaps w.r.t. a statement
(`Heap.WF`): every literal `v` occurring in `s` must be stored at its fixed
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
  | .lookupS _ _ e p   => .str p :: e.lits
  | .lookupD _ _ e₁ e₂ => e₁.lits ++ e₂.lits
  | .updateS _ e₁ p e₂ => .str p :: (e₁.lits ++ e₂.lits)
  | .updateD _ e₁ e₂ e₃ => e₁.lits ++ e₂.lits ++ e₃.lits
  | .call _ _ e es     => e.lits ++ litsOfExprs es
  | .seq s₁ s₂         => s₁.lits ++ s₂.lits
  | .ifElse _ e s₁ s₂  => e.lits ++ s₁.lits ++ s₂.lits
  | .whileDo _ e s     => e.lits ++ s.lits
  | .ret e             => e.lits
  | .setTaint e        => e.lits
  | .setSink e         => e.lits

/-! ## Site identifiers occurring in a statement

Besides `binOp`/`objLit`, whose `κ` the allocator uses, every `call`/
`lookupS`/`lookupD`/`updateS`/`updateD`/`ifElse`/`whileDo` carries a site index
of its own. The automaton-based analysis (`CoreJsAutomatonSyntax.lean`) names
its states after them: a call site's index, combined with a call string,
identifies that call's continuation, and an `ifElse`/`whileDo`'s index names
its branch/loop states. The index is explicit rather than derived from the
statement's position in the syntax tree because a call site's identity has
to be combined with a call string, which a plain index does at least as
simply as any derived path would.

Well-formedness (`Stmt.SitesWF`) requires all such indices, together with the
pre-existing `binOp`/`objLit` `κ`s, to be pairwise distinct across a program —
analogous to `EnvSpec`/`ConcreteSpec`'s side conditions elsewhere in this
development. -/

/-- Every site index occurring in a statement: the existing `binOp`/`objLit`
    `κ`s, together with the new `Idx` fields of `call`/`lookupS`/`lookupD`/
    `updateS`/`updateD`/`ifElse`/`whileDo`. -/
def Stmt.sites : Stmt → List Idx
  | .skip                 => []
  | .assign _ _           => []
  | .binOp _ κ _ _ _       => [κ]
  | .objLit _ κ _          => [κ]
  | .lookupS _ κ _ _       => [κ]
  | .lookupD _ κ _ _       => [κ]
  | .updateS κ _ _ _       => [κ]
  | .updateD κ _ _ _       => [κ]
  | .call _ κ _ _          => [κ]
  | .seq s₁ s₂             => s₁.sites ++ s₂.sites
  | .ifElse κ _ s₁ s₂      => κ :: (s₁.sites ++ s₂.sites)
  | .whileDo κ _ s         => κ :: s.sites
  | .ret _                 => []
  | .setTaint _            => []
  | .setSink _             => []

/-- Well-formedness: every site index occurring in `s` is pairwise distinct. -/
def Stmt.SitesWF (s : Stmt) : Prop := s.sites.Nodup

end CoreJS
