/-
  # Core JavaScript — Concrete Semantics

  Formalisation of Figures A2–A6 and Definition A4 of Appendix A of
  "Model Checking Security Properties of Node.js Packages":

  * Fig. A2  — semantic domains
  * Fig. A3  — expression evaluation `⟦e⟧ᵨ`
  * Def. A4  — well-formedness of concrete heaps w.r.t. a statement
  * Fig. A5/A6 — the big-step judgement `Γ ⊢ ⟨h, ρ, δ, s⟩ ⇓c ⟨h', ρ', δ', t, o⟩`

  Plain Lean 4 — no Mathlib required.
-/

import CoreJsSyntax

namespace CoreJS

/-! ## Sets of locations

`P(Loc)`, represented as predicates.  Only `∅`, `{·}`, `{·, ·}` and `∪` are
used by the semantics. -/

/-- `P(Loc)`. -/
def LocSet := Loc → Prop

instance : EmptyCollection LocSet := ⟨fun _ => False⟩
instance : Singleton Loc LocSet  := ⟨fun l l' => l' = l⟩
instance : Insert Loc LocSet     := ⟨fun l A l' => l' = l ∨ A l'⟩
instance : Union LocSet          := ⟨fun A B l => A l ∨ B l⟩

/-- Set inclusion, useful for stating soundness lemmas. -/
def LocSet.Subset (A B : LocSet) : Prop := ∀ l, A l → B l

/-! ## Semantic domains (Fig. A2) -/

/-- Program stores `ρ ∈ Sto : Var ⇀ Loc`. -/
def Sto := Var → Option Loc

/-- The empty store. -/
def Sto.empty : Sto := fun _ => none

/-- `ρ[x ↦ l]`. -/
def Sto.upd (ρ : Sto) (x : Var) (l : Loc) : Sto :=
  fun y => if y = x then some l else ρ y

/-- `[xᵢ ↦ lᵢ]`, the store built on function entry.  Parameter lists are
    assumed to be duplicate-free. -/
def Sto.ofParams : List Var → List Loc → Sto
  | x :: xs, l :: ls => (Sto.ofParams xs ls).upd x l
  | _,       _       => Sto.empty

/-- Function environments `Γ ∈ Env : Fid ⇀ Var list × Stmt`. -/
def Env := Fid → Option (List Var × Stmt)

/-- Memory heaps `h ∈ H`, a two-level structure:
    * `obj : Loc × Str ⇀ Loc` maps object properties to locations;
    * `val : Loc ⇀ Val`      maps locations to the values they store. -/
structure Heap where
  obj : Loc → PropName → Option Loc
  val : Loc → Option Val

/-- `h[val ↦ h.val[l ↦ v]]`. -/
def Heap.setVal (h : Heap) (l : Loc) (v : Val) : Heap :=
  { h with val := fun l' => if l' = l then some v else h.val l' }

/-- `h[obj ↦ h.obj[(l, p) ↦ l']]`. -/
def Heap.setObj (h : Heap) (l : Loc) (p : PropName) (l' : Loc) : Heap :=
  { h with obj := fun l₁ p₁ => if l₁ = l ∧ p₁ = p then some l' else h.obj l₁ p₁ }

/-- `h[obj ↦ h.obj[(l, pᵢ) ↦ lᵢ | ⁿᵢ₌₁]]`.  Simultaneous update of the paper;
    performed left-to-right here, which agrees with it when the `pᵢ` are
    pairwise distinct (as required for object literals). -/
def Heap.setObjs (h : Heap) (l : Loc) : List (PropName × Loc) → Heap
  | []            => h
  | (p, l') :: ps => (h.setObj l p l').setObjs l ps

/-- Taint registers `δ ∈ Reg`:
    * `dep` — dependencies between values (`l₂ ∈ δ.dep l₁`: the value in `l₁`
      was computed from the one in `l₂`);
    * `ac`  — directly attacker-controlled locations;
    * `sk`  — locations holding sensitive sinks.

    `dep` is total with default `∅`, which is how the paper uses it. -/
structure Reg where
  dep : Loc → LocSet
  ac  : LocSet
  sk  : LocSet

/-- `δ[dep ↦ δ.dep[l ↦ d]]`. -/
def Reg.setDep (δ : Reg) (l : Loc) (d : LocSet) : Reg :=
  { δ with dep := fun l' => if l' = l then d else δ.dep l' }

/-- Trace actions `a ∈ Act`. -/
inductive Act where
  /-- `l₁ := l₂[l₃]` -/
  | lookup (l₁ l₂ l₃ : Loc)
  /-- `l₁[l₂] := l₃` -/
  | update (l₁ l₂ l₃ : Loc)
  /-- `Call(l_f, [l₁, ..., lₙ])` -/
  | call   (lf : Loc) (ls : List Loc)
  /-- `Ret(l_f, l)` -/
  | ret    (lf l : Loc)
  deriving DecidableEq, Repr

/-- Execution traces `t ∈ Trc ::= ε | a | t₁; t₂`. -/
inductive Trc where
  /-- `ε`: the empty trace. -/
  | emp
  /-- A single action. -/
  | act (a : Act)
  /-- `t₁; t₂`: concatenation. -/
  | seq (t₁ t₂ : Trc)
  deriving Repr

@[inherit_doc] scoped infixr:70 (name := trcSeq) " ;; " => Trc.seq

/-- Execution outcomes `o ∈ Out ::= · | r⟨l⟩`. -/
inductive Out where
  /-- Continuation outcome `·`. -/
  | cont
  /-- Return outcome `r⟨l⟩`. -/
  | ret (l : Loc)
  deriving DecidableEq, Repr

/-- Initial configurations `⟨h, ρ, δ⟩`. -/
structure Conf where
  heap : Heap
  sto  : Sto
  reg  : Reg

/-- Final configurations `⟨h', ρ', δ', t, o⟩`. -/
structure Res where
  heap : Heap
  sto  : Sto
  reg  : Reg
  trc  : Trc
  out  : Out

/-! ## Parameters of the concrete semantics

The paper leaves three ingredients abstract: the injection `v ↦ l_v` of
literals into locations, the concrete allocator `alloc_c`, and the
interpretation of binary operators. -/

/-- Parameters of the concrete semantics. -/
class Concrete where
  /-- `l_v`: the fixed location at which the literal value `v` is stored. -/
  litLoc : Val → Loc
  /-- `alloc_c(h, κ)`: allocation of a fresh location. -/
  allocC : Heap → Idx → Loc
  /-- `⊕(v₁, v₂)`: interpretation of binary operators. -/
  opSem  : BinOp → Val → Val → Val

open Concrete

/-- The assumptions the paper makes about the parameters above: literal
    locations are pairwise distinct, and `alloc_c` returns a location that is
    unused in the current heap (hence, in a well-formed heap, distinct from
    every `l_v`).  The semantics itself does not depend on these; they are
    needed for the soundness proofs. -/
structure ConcreteSpec [Concrete] : Prop where
  litLoc_inj   : ∀ v w, litLoc v = litLoc w → v = w
  allocC_fresh : ∀ (h : Heap) (κ : Idx),
    h.val (allocC h κ) = none ∧ ∀ p, h.obj (allocC h κ) p = none

/-! ## Expression evaluation (Fig. A3)

`⟦e⟧ᵨ ≜ l`, with `⟦v⟧ᵨ ≜ l_v` and `⟦x⟧ᵨ ≜ ρ(x)`.  Partial, as `ρ` is. -/

/-- `⟦e⟧ᵨ`. -/
def evalE [Concrete] (ρ : Sto) : Expr → Option Loc
  | .val v => some (litLoc v)
  | .var x => ρ x

/-- `⟦e₁⟧ᵨ, ..., ⟦eₙ⟧ᵨ`, pointwise. -/
def evalEs [Concrete] (ρ : Sto) : List Expr → Option (List Loc)
  | []      => some []
  | e :: es => do
      let l  ← evalE ρ e
      let ls ← evalEs ρ es
      return l :: ls

/-! ## Well-formedness (Definition A4) -/

/-- A concrete heap `h` is well formed w.r.t. a statement `s` iff every
    literal value `v` occurring in `s` satisfies `h.val(l_v) = v`, and the
    global `undefined` cell holds `undefined`.

    The second conjunct is unconditional rather than gated on `s.lits`: no
    source statement need mention `undefined` syntactically, yet the
    [Function Call] rule below reads `l_undef` whenever a callee body falls
    through without an explicit `return`. -/
def Heap.WF [Concrete] (h : Heap) (s : Stmt) : Prop :=
  (∀ v ∈ s.lits, h.val (litLoc v) = some v) ∧
  h.val (litLoc .undef) = some .undef

/-! ## Big-step semantics (Figs. A5 and A6)

`Γ ⊢ ⟨h, ρ, δ, s⟩ ⇓c ⟨h', ρ', δ', t, o⟩`.

Each rule is stated exactly as in the paper: the components of the resulting
configuration are introduced as variables and defined by equational premises.

Since this is an *inductive* definition, only terminating executions are
derivable — which is what the paper's finite-trace semantics intends. -/

inductive BigStep [Concrete] (Γ : Env) : Conf → Stmt → Res → Prop where

  /-- [Skip] -/
  | skip {h ρ δ} :
      BigStep Γ ⟨h, ρ, δ⟩ .skip ⟨h, ρ, δ, .emp, .cont⟩

  /-- [Assignment] -/
  | assign {h ρ ρ' δ x e l} :
      evalE ρ e = some l →
      ρ' = ρ.upd x l →
      BigStep Γ ⟨h, ρ, δ⟩ (.assign x e) ⟨h, ρ', δ, .emp, .cont⟩

  /-- [Binary Operation] -/
  | binOp {h h' ρ ρ' δ δ' x κ op e₁ e₂ l₁ l₂ v₁ v₂ l v d} :
      evalE ρ e₁ = some l₁ →
      evalE ρ e₂ = some l₂ →
      h.val l₁ = some v₁ →
      h.val l₂ = some v₂ →
      l = allocC h κ →
      v = opSem op v₁ v₂ →
      h' = h.setVal l v →
      ρ' = ρ.upd x l →
      d = δ.dep l₁ ∪ δ.dep l₂ ∪ {l₁, l₂} →
      δ' = δ.setDep l d →
      BigStep Γ ⟨h, ρ, δ⟩ (.binOp x κ op e₁ e₂) ⟨h', ρ', δ', .emp, .cont⟩

  /-- [Object Initialization] -/
  | objLit {h h' ρ ρ' δ δ' x κ fs ls l} :
      evalEs ρ (fs.map Prod.snd) = some ls →
      l = allocC h κ →
      h' = h.setObjs l ((fs.map Prod.fst).zip ls) →
      ρ' = ρ.upd x l →
      δ' = δ.setDep l ∅ →
      BigStep Γ ⟨h, ρ, δ⟩ (.objLit x κ fs) ⟨h', ρ', δ', .emp, .cont⟩

  /-- [Static Property Lookup] -/
  | lookupS {h ρ ρ' δ x e p l₁ l₂} :
      evalE ρ e = some l₁ →
      h.obj l₁ p = some l₂ →
      ρ' = ρ.upd x l₂ →
      BigStep Γ ⟨h, ρ, δ⟩ (.lookupS x e p)
        ⟨h, ρ', δ, .act (.lookup l₂ l₁ (litLoc (.str p))), .cont⟩

  /-- [Dynamic Property Lookup] -/
  | lookupD {h ρ ρ' δ x e₁ e₂ l₁ l₂ l₃ p} :
      evalE ρ e₁ = some l₁ →
      evalE ρ e₂ = some l₂ →
      h.val l₂ = some (.str p) →
      h.obj l₁ p = some l₃ →
      ρ' = ρ.upd x l₃ →
      BigStep Γ ⟨h, ρ, δ⟩ (.lookupD x e₁ e₂)
        ⟨h, ρ', δ, .act (.lookup l₃ l₁ l₂), .cont⟩

  /-- [Static Property Update] -/
  | updateS {h h' ρ δ e₁ p e₂ l₁ l₂} :
      evalE ρ e₁ = some l₁ →
      evalE ρ e₂ = some l₂ →
      h' = h.setObj l₁ p l₂ →
      BigStep Γ ⟨h, ρ, δ⟩ (.updateS e₁ p e₂)
        ⟨h', ρ, δ, .act (.update l₁ (litLoc (.str p)) l₂), .cont⟩

  /-- [Dynamic Property Update] -/
  | updateD {h h' ρ δ e₁ e₂ e₃ l₁ l₂ l₃ p} :
      evalE ρ e₁ = some l₁ →
      evalE ρ e₂ = some l₂ →
      evalE ρ e₃ = some l₃ →
      h.val l₂ = some (.str p) →
      h' = h.setObj l₁ p l₃ →
      BigStep Γ ⟨h, ρ, δ⟩ (.updateD e₁ e₂ e₃)
        ⟨h', ρ, δ, .act (.update l₁ l₂ l₃), .cont⟩

  /-- [Sequence Ret] -/
  | seqRet {h h' ρ ρ' δ δ' s₁ s₂ t l} :
      BigStep Γ ⟨h, ρ, δ⟩ s₁ ⟨h', ρ', δ', t, .ret l⟩ →
      BigStep Γ ⟨h, ρ, δ⟩ (.seq s₁ s₂) ⟨h', ρ', δ', t, .ret l⟩

  /-- [Sequence Cont] -/
  | seqCont {h h' h'' ρ ρ' ρ'' δ δ' δ'' s₁ s₂ t₁ t₂ o} :
      BigStep Γ ⟨h, ρ, δ⟩ s₁ ⟨h', ρ', δ', t₁, .cont⟩ →
      BigStep Γ ⟨h', ρ', δ'⟩ s₂ ⟨h'', ρ'', δ'', t₂, o⟩ →
      BigStep Γ ⟨h, ρ, δ⟩ (.seq s₁ s₂) ⟨h'', ρ'', δ'', .seq t₁ t₂, o⟩

  /-- [Function Call], explicit return: the callee body terminates with
      `r⟨l⟩` and `l` is what the call evaluates to. -/
  | callRet {h h' ρ ρ' ρf' δ δ' x e es lf f params body ls l t} :
      evalE ρ e = some lf →
      h.val lf = some (.fid f) →
      Γ f = some (params, body) →
      evalEs ρ es = some ls →
      params.length = ls.length →
      BigStep Γ ⟨h, Sto.ofParams params ls, δ⟩ body ⟨h', ρf', δ', t, .ret l⟩ →
      ρ' = ρ.upd x l →
      BigStep Γ ⟨h, ρ, δ⟩ (.call x e es)
        ⟨h', ρ', δ',
         .seq (.act (.call lf ls)) (.seq t (.act (.ret lf l))), .cont⟩

  /-- [Function Call], implicit return: the callee body falls through with
      outcome `·`, and the call evaluates to `undefined` (JavaScript's
      behaviour for a function that returns no value).  The emitted `Ret`
      action mentions `l_undef`, so the trace records a return either way. -/
  | callCont {h h' ρ ρ' ρf' δ δ' x e es lf f params body ls t} :
      evalE ρ e = some lf →
      h.val lf = some (.fid f) →
      Γ f = some (params, body) →
      evalEs ρ es = some ls →
      params.length = ls.length →
      BigStep Γ ⟨h, Sto.ofParams params ls, δ⟩ body ⟨h', ρf', δ', t, .cont⟩ →
      ρ' = ρ.upd x (litLoc .undef) →
      BigStep Γ ⟨h, ρ, δ⟩ (.call x e es)
        ⟨h', ρ', δ',
         .seq (.act (.call lf ls))
              (.seq t (.act (.ret lf (litLoc .undef)))), .cont⟩

  /-- [If True] -/
  | ifTrue {h ρ δ e s₁ s₂ l r} :
      evalE ρ e = some l →
      h.val l = some (.bool true) →
      BigStep Γ ⟨h, ρ, δ⟩ s₁ r →
      BigStep Γ ⟨h, ρ, δ⟩ (.ifElse e s₁ s₂) r

  /-- [If False] -/
  | ifFalse {h ρ δ e s₁ s₂ l r} :
      evalE ρ e = some l →
      h.val l = some (.bool false) →
      BigStep Γ ⟨h, ρ, δ⟩ s₂ r →
      BigStep Γ ⟨h, ρ, δ⟩ (.ifElse e s₁ s₂) r

  /-- [While], by unfolding into a conditional. -/
  | whileDo {h ρ δ e s r} :
      BigStep Γ ⟨h, ρ, δ⟩ (.ifElse e (.seq s (.whileDo e s)) .skip) r →
      BigStep Γ ⟨h, ρ, δ⟩ (.whileDo e s) r

  /-- [Return] -/
  | ret {h ρ δ e l} :
      evalE ρ e = some l →
      BigStep Γ ⟨h, ρ, δ⟩ (.ret e) ⟨h, ρ, δ, .emp, .ret l⟩

  /-- [SetTaint] -/
  | setTaint {h ρ δ δ' e l} :
      evalE ρ e = some l →
      δ' = { δ with ac := {l} ∪ δ.ac } →
      BigStep Γ ⟨h, ρ, δ⟩ (.setTaint e) ⟨h, ρ, δ', .emp, .cont⟩

  /-- [SetSink] -/
  | setSink {h ρ δ δ' e l} :
      evalE ρ e = some l →
      δ' = { δ with sk := {l} ∪ δ.sk } →
      BigStep Γ ⟨h, ρ, δ⟩ (.setSink e) ⟨h, ρ, δ', .emp, .cont⟩


/-! ## Height-indexed derivations

`BigStep` lives in `Prop`, so Lean generates no `sizeOf` for it and its
recursor eliminates only into `Prop`: there is no derivation height available
to recurse on.  The soundness proof needs one — `[Call-Fix]` extends `Σ` with
a summary whose validity quantifies over *all* concrete executions of the
callee body, not merely over sub-derivations of the derivation being inducted
on, so structural induction does not reach it.

`BigStepN Γ n` is the same relation with an explicit bound on derivation
height: every rule concludes at `n+1` with its recursive premises at `n`.
`BigStep.toN` and `BigStepN.toBigStep` establish that the two agree, so
soundness may be proved by strong induction on `n` and then transported back. -/

inductive BigStepN [Concrete] (Γ : Env) : Nat → Conf → Stmt → Res → Prop where

  /-- [Skip] -/
  | skip {n h ρ δ} :
      BigStepN Γ (n+1) ⟨h, ρ, δ⟩ .skip ⟨h, ρ, δ, .emp, .cont⟩

  /-- [Assignment] -/
  | assign {n h ρ ρ' δ x e l} :
      evalE ρ e = some l →
      ρ' = ρ.upd x l →
      BigStepN Γ (n+1) ⟨h, ρ, δ⟩ (.assign x e) ⟨h, ρ', δ, .emp, .cont⟩

  /-- [Binary Operation] -/
  | binOp {n h h' ρ ρ' δ δ' x κ op e₁ e₂ l₁ l₂ v₁ v₂ l v d} :
      evalE ρ e₁ = some l₁ →
      evalE ρ e₂ = some l₂ →
      h.val l₁ = some v₁ →
      h.val l₂ = some v₂ →
      l = allocC h κ →
      v = opSem op v₁ v₂ →
      h' = h.setVal l v →
      ρ' = ρ.upd x l →
      d = δ.dep l₁ ∪ δ.dep l₂ ∪ {l₁, l₂} →
      δ' = δ.setDep l d →
      BigStepN Γ (n+1) ⟨h, ρ, δ⟩ (.binOp x κ op e₁ e₂) ⟨h', ρ', δ', .emp, .cont⟩

  /-- [Object Initialization] -/
  | objLit {n h h' ρ ρ' δ δ' x κ fs ls l} :
      evalEs ρ (fs.map Prod.snd) = some ls →
      l = allocC h κ →
      h' = h.setObjs l ((fs.map Prod.fst).zip ls) →
      ρ' = ρ.upd x l →
      δ' = δ.setDep l ∅ →
      BigStepN Γ (n+1) ⟨h, ρ, δ⟩ (.objLit x κ fs) ⟨h', ρ', δ', .emp, .cont⟩

  /-- [Static Property Lookup] -/
  | lookupS {n h ρ ρ' δ x e p l₁ l₂} :
      evalE ρ e = some l₁ →
      h.obj l₁ p = some l₂ →
      ρ' = ρ.upd x l₂ →
      BigStepN Γ (n+1) ⟨h, ρ, δ⟩ (.lookupS x e p)
        ⟨h, ρ', δ, .act (.lookup l₂ l₁ (litLoc (.str p))), .cont⟩

  /-- [Dynamic Property Lookup] -/
  | lookupD {n h ρ ρ' δ x e₁ e₂ l₁ l₂ l₃ p} :
      evalE ρ e₁ = some l₁ →
      evalE ρ e₂ = some l₂ →
      h.val l₂ = some (.str p) →
      h.obj l₁ p = some l₃ →
      ρ' = ρ.upd x l₃ →
      BigStepN Γ (n+1) ⟨h, ρ, δ⟩ (.lookupD x e₁ e₂)
        ⟨h, ρ', δ, .act (.lookup l₃ l₁ l₂), .cont⟩

  /-- [Static Property Update] -/
  | updateS {n h h' ρ δ e₁ p e₂ l₁ l₂} :
      evalE ρ e₁ = some l₁ →
      evalE ρ e₂ = some l₂ →
      h' = h.setObj l₁ p l₂ →
      BigStepN Γ (n+1) ⟨h, ρ, δ⟩ (.updateS e₁ p e₂)
        ⟨h', ρ, δ, .act (.update l₁ (litLoc (.str p)) l₂), .cont⟩

  /-- [Dynamic Property Update] -/
  | updateD {n h h' ρ δ e₁ e₂ e₃ l₁ l₂ l₃ p} :
      evalE ρ e₁ = some l₁ →
      evalE ρ e₂ = some l₂ →
      evalE ρ e₃ = some l₃ →
      h.val l₂ = some (.str p) →
      h' = h.setObj l₁ p l₃ →
      BigStepN Γ (n+1) ⟨h, ρ, δ⟩ (.updateD e₁ e₂ e₃)
        ⟨h', ρ, δ, .act (.update l₁ l₂ l₃), .cont⟩

  /-- [Sequence Ret] -/
  | seqRet {n h h' ρ ρ' δ δ' s₁ s₂ t l} :
      BigStepN Γ n ⟨h, ρ, δ⟩ s₁ ⟨h', ρ', δ', t, .ret l⟩ →
      BigStepN Γ (n+1) ⟨h, ρ, δ⟩ (.seq s₁ s₂) ⟨h', ρ', δ', t, .ret l⟩

  /-- [Sequence Cont] -/
  | seqCont {n h h' h'' ρ ρ' ρ'' δ δ' δ'' s₁ s₂ t₁ t₂ o} :
      BigStepN Γ n ⟨h, ρ, δ⟩ s₁ ⟨h', ρ', δ', t₁, .cont⟩ →
      BigStepN Γ n ⟨h', ρ', δ'⟩ s₂ ⟨h'', ρ'', δ'', t₂, o⟩ →
      BigStepN Γ (n+1) ⟨h, ρ, δ⟩ (.seq s₁ s₂) ⟨h'', ρ'', δ'', .seq t₁ t₂, o⟩

  /-- [Function Call], explicit return: the callee body terminates with
      `r⟨l⟩` and `l` is what the call evaluates to. -/
  | callRet {n h h' ρ ρ' ρf' δ δ' x e es lf f params body ls l t} :
      evalE ρ e = some lf →
      h.val lf = some (.fid f) →
      Γ f = some (params, body) →
      evalEs ρ es = some ls →
      params.length = ls.length →
      BigStepN Γ n ⟨h, Sto.ofParams params ls, δ⟩ body ⟨h', ρf', δ', t, .ret l⟩ →
      ρ' = ρ.upd x l →
      BigStepN Γ (n+1) ⟨h, ρ, δ⟩ (.call x e es)
        ⟨h', ρ', δ',
         .seq (.act (.call lf ls)) (.seq t (.act (.ret lf l))), .cont⟩

  /-- [Function Call], implicit return: the callee body falls through with
      outcome `·`, and the call evaluates to `undefined` (JavaScript's
      behaviour for a function that returns no value).  The emitted `Ret`
      action mentions `l_undef`, so the trace records a return either way. -/
  | callCont {n h h' ρ ρ' ρf' δ δ' x e es lf f params body ls t} :
      evalE ρ e = some lf →
      h.val lf = some (.fid f) →
      Γ f = some (params, body) →
      evalEs ρ es = some ls →
      params.length = ls.length →
      BigStepN Γ n ⟨h, Sto.ofParams params ls, δ⟩ body ⟨h', ρf', δ', t, .cont⟩ →
      ρ' = ρ.upd x (litLoc .undef) →
      BigStepN Γ (n+1) ⟨h, ρ, δ⟩ (.call x e es)
        ⟨h', ρ', δ',
         .seq (.act (.call lf ls))
              (.seq t (.act (.ret lf (litLoc .undef)))), .cont⟩

  /-- [If True] -/
  | ifTrue {n h ρ δ e s₁ s₂ l r} :
      evalE ρ e = some l →
      h.val l = some (.bool true) →
      BigStepN Γ n ⟨h, ρ, δ⟩ s₁ r →
      BigStepN Γ (n+1) ⟨h, ρ, δ⟩ (.ifElse e s₁ s₂) r

  /-- [If False] -/
  | ifFalse {n h ρ δ e s₁ s₂ l r} :
      evalE ρ e = some l →
      h.val l = some (.bool false) →
      BigStepN Γ n ⟨h, ρ, δ⟩ s₂ r →
      BigStepN Γ (n+1) ⟨h, ρ, δ⟩ (.ifElse e s₁ s₂) r

  /-- [While], by unfolding into a conditional. -/
  | whileDo {n h ρ δ e s r} :
      BigStepN Γ n ⟨h, ρ, δ⟩ (.ifElse e (.seq s (.whileDo e s)) .skip) r →
      BigStepN Γ (n+1) ⟨h, ρ, δ⟩ (.whileDo e s) r

  /-- [Return] -/
  | ret {n h ρ δ e l} :
      evalE ρ e = some l →
      BigStepN Γ (n+1) ⟨h, ρ, δ⟩ (.ret e) ⟨h, ρ, δ, .emp, .ret l⟩

  /-- [SetTaint] -/
  | setTaint {n h ρ δ δ' e l} :
      evalE ρ e = some l →
      δ' = { δ with ac := {l} ∪ δ.ac } →
      BigStepN Γ (n+1) ⟨h, ρ, δ⟩ (.setTaint e) ⟨h, ρ, δ', .emp, .cont⟩

  /-- [SetSink] -/
  | setSink {n h ρ δ δ' e l} :
      evalE ρ e = some l →
      δ' = { δ with sk := {l} ∪ δ.sk } →
      BigStepN Γ (n+1) ⟨h, ρ, δ⟩ (.setSink e) ⟨h, ρ, δ', .emp, .cont⟩



/-- Raising the height bound preserves derivability. -/
theorem BigStepN.mono [Concrete] {Γ : Env} :
    ∀ {n c s r}, BigStepN Γ n c s r → BigStepN Γ (n+1) c s r := by
  intro n c s r H
  induction H with
  | skip => exact .skip
  | assign h1 h2 => exact .assign h1 h2
  | binOp h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => exact .binOp h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  | objLit h1 h2 h3 h4 h5 => exact .objLit h1 h2 h3 h4 h5
  | lookupS h1 h2 h3 => exact .lookupS h1 h2 h3
  | lookupD h1 h2 h3 h4 h5 => exact .lookupD h1 h2 h3 h4 h5
  | updateS h1 h2 h3 => exact .updateS h1 h2 h3
  | updateD h1 h2 h3 h4 h5 => exact .updateD h1 h2 h3 h4 h5
  | seqRet _ ih => exact .seqRet ih
  | seqCont _ _ ih1 ih2 => exact .seqCont ih1 ih2
  | callRet h1 h2 h3 h4 h5 _ h7 ih => exact .callRet h1 h2 h3 h4 h5 ih h7
  | callCont h1 h2 h3 h4 h5 _ h7 ih => exact .callCont h1 h2 h3 h4 h5 ih h7
  | ifTrue h1 h2 _ ih => exact .ifTrue h1 h2 ih
  | ifFalse h1 h2 _ ih => exact .ifFalse h1 h2 ih
  | whileDo _ ih => exact .whileDo ih
  | ret h1 => exact .ret h1
  | setTaint h1 h2 => exact .setTaint h1 h2
  | setSink h1 h2 => exact .setSink h1 h2

theorem BigStepN.mono_le [Concrete] {Γ : Env} {n c s r} (H : BigStepN Γ n c s r) :
    ∀ {m}, n ≤ m → BigStepN Γ m c s r := by
  intro m
  induction m with
  | zero => intro hnm; exact (Nat.le_zero.mp hnm) ▸ H
  | succ k ih =>
      intro hnm
      rcases Nat.lt_or_ge n (k+1) with hlt | hge
      · exact BigStepN.mono (ih (Nat.lt_succ_iff.mp hlt))
      · exact (Nat.le_antisymm hnm hge) ▸ H

/-- Every plain derivation has a height. -/
theorem BigStep.toN [Concrete] {Γ : Env} {c s r} (H : BigStep Γ c s r) :
    ∃ n, BigStepN Γ n c s r := by
  induction H with
  | skip => exact ⟨1, .skip⟩
  | assign h1 h2 => exact ⟨1, .assign h1 h2⟩
  | binOp h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => exact ⟨1, .binOp h1 h2 h3 h4 h5 h6 h7 h8 h9 h10⟩
  | objLit h1 h2 h3 h4 h5 => exact ⟨1, .objLit h1 h2 h3 h4 h5⟩
  | lookupS h1 h2 h3 => exact ⟨1, .lookupS h1 h2 h3⟩
  | lookupD h1 h2 h3 h4 h5 => exact ⟨1, .lookupD h1 h2 h3 h4 h5⟩
  | updateS h1 h2 h3 => exact ⟨1, .updateS h1 h2 h3⟩
  | updateD h1 h2 h3 h4 h5 => exact ⟨1, .updateD h1 h2 h3 h4 h5⟩
  | seqRet _ ih => obtain ⟨n, d⟩ := ih; exact ⟨n+1, .seqRet d⟩
  | seqCont _ _ ih1 ih2 =>
      obtain ⟨n1, d1⟩ := ih1
      obtain ⟨n2, d2⟩ := ih2
      exact ⟨max n1 n2 + 1,
             .seqCont (d1.mono_le (Nat.le_max_left _ _)) (d2.mono_le (Nat.le_max_right _ _))⟩
  | callRet h1 h2 h3 h4 h5 _ h7 ih =>
      obtain ⟨n, d⟩ := ih; exact ⟨n+1, .callRet h1 h2 h3 h4 h5 d h7⟩
  | callCont h1 h2 h3 h4 h5 _ h7 ih =>
      obtain ⟨n, d⟩ := ih; exact ⟨n+1, .callCont h1 h2 h3 h4 h5 d h7⟩
  | ifTrue h1 h2 _ ih => obtain ⟨n, d⟩ := ih; exact ⟨n+1, .ifTrue h1 h2 d⟩
  | ifFalse h1 h2 _ ih => obtain ⟨n, d⟩ := ih; exact ⟨n+1, .ifFalse h1 h2 d⟩
  | whileDo _ ih => obtain ⟨n, d⟩ := ih; exact ⟨n+1, .whileDo d⟩
  | ret h1 => exact ⟨1, .ret h1⟩
  | setTaint h1 h2 => exact ⟨1, .setTaint h1 h2⟩
  | setSink h1 h2 => exact ⟨1, .setSink h1 h2⟩

/-- ... and a bounded derivation is a derivation. -/
theorem BigStepN.toBigStep [Concrete] {Γ : Env} :
    ∀ {n c s r}, BigStepN Γ n c s r → BigStep Γ c s r := by
  intro n c s r H
  induction H with
  | skip => exact .skip
  | assign h1 h2 => exact .assign h1 h2
  | binOp h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => exact .binOp h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  | objLit h1 h2 h3 h4 h5 => exact .objLit h1 h2 h3 h4 h5
  | lookupS h1 h2 h3 => exact .lookupS h1 h2 h3
  | lookupD h1 h2 h3 h4 h5 => exact .lookupD h1 h2 h3 h4 h5
  | updateS h1 h2 h3 => exact .updateS h1 h2 h3
  | updateD h1 h2 h3 h4 h5 => exact .updateD h1 h2 h3 h4 h5
  | seqRet _ ih => exact .seqRet ih
  | seqCont _ _ ih1 ih2 => exact .seqCont ih1 ih2
  | callRet h1 h2 h3 h4 h5 _ h7 ih => exact .callRet h1 h2 h3 h4 h5 ih h7
  | callCont h1 h2 h3 h4 h5 _ h7 ih => exact .callCont h1 h2 h3 h4 h5 ih h7
  | ifTrue h1 h2 _ ih => exact .ifTrue h1 h2 ih
  | ifFalse h1 h2 _ ih => exact .ifFalse h1 h2 ih
  | whileDo _ ih => exact .whileDo ih
  | ret h1 => exact .ret h1
  | setTaint h1 h2 => exact .setTaint h1 h2
  | setSink h1 h2 => exact .setSink h1 h2

/-- Notation for the big-step judgement:
    `Γ ⊢ c ⇓[s] r` is `Γ ⊢ ⟨h, ρ, δ, s⟩ ⇓c ⟨h', ρ', δ', t, o⟩`. -/
scoped notation:50 Γ " ⊢ " c " ⇓[" s "] " r => BigStep Γ c s r

end CoreJS
