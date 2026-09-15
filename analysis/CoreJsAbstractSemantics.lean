/-
  # Core JavaScript — Abstract Semantics

  Formalisation of Appendix B.1 of
  "Model Checking Security Properties of Node.js Packages":

  * Fig. B2  — abstract expression evaluation `⟦e⟧ρ̂`
  * Def. B3  — well-formedness of abstract heaps w.r.t. a statement
  * Figs. B6 and B7 — the abstract big-step judgement
                      `Γ ⊢ ⟨ĥ, ρ̂, δ̂, s⟩ ⇓a ⟨ĥ', ρ̂', δ̂', t̂, ô⟩`
  * §5.1 — the entry point `SA(Γ, s)`

  `CoreJsSemantics.lean` is imported only for the function environment
  `Env`, which the two semantics share (as in the paper).

  Deliberate deviations from the paper, and apparent gaps in it, are tagged
  `REMARK n` and collected at the end of the file.
-/

import CoreJsAbstractSyntax
import CoreJsSemantics

namespace CoreJS

/-! ## Lifting the abstract heap and register to sets of locations

Fig. B6 applies `ĥ.val`, `ĥ.obj` and `δ̂.dep` to *sets* of abstract locations
(and, in the dynamic property rules, to *sets* of property names).  These
liftings are left implicit in the paper; they are the pointwise unions. -/

/-- `ĥ.val(L) = ⋃_{l̂ ∈ L} ĥ.val(l̂)`.

    Note that if `ĥ.val(l̂) = ⊤` for some `l̂ ∈ L` then the result contains
    every value, hence is `⊑`-equivalent to `⊤`. -/
def AHeap.valOf (h : AHeap) (L : ALocSet) : VSet :=
  .vals (fun v => ∃ l, L l ∧ (h.val l).Mem v)

/-- `ĥ.obj(L, p) = ⋃_{l̂ ∈ L} ĥ.obj(l̂, p)`, the lookup of a static property
    `p`. -/
def AHeap.objOf (h : AHeap) (L : ALocSet) (p : PropName) : ALocSet :=
  fun l' => ∃ l, L l ∧ h.obj l p l'

/-- `ĥ.obj(L, V) = ⋃_{l̂ ∈ L} ⋃_{p ∈ V} ĥ.obj(l̂, p)`, the lookup of a dynamic
    property whose key may be any string in `V`. -/
def AHeap.objOfV (h : AHeap) (L : ALocSet) (V : VSet) : ALocSet :=
  fun l' => ∃ l p, L l ∧ V.Mem (.str p) ∧ h.obj l p l'

/-- `δ̂.dep(L) = ⋃_{l̂ ∈ L} δ̂.dep(l̂)`. -/
def AReg.depOf (δ : AReg) (L : ALocSet) : ALocSet :=
  fun l' => ∃ l, L l ∧ δ.dep l l'

/-! ## Abstract updates

All heap updates of Fig. B6 are *weak* (Def. of §5.1: "the property update
rules perform weak updates, adding the assigned locations to those previously
stored in the targeted heap cell"). -/

/-- `ĥ[val ↦ ĥ.val[l̂ ↦ V ∪ ĥ.val(l̂)]]`. -/
def AHeap.weakSetVal (h : AHeap) (l : ALoc) (V : VSet) : AHeap :=
  { h with val := fun l' => if l' = l then VSet.join V (h.val l') else h.val l' }

/-- `ĥ[obj ↦ ĥ.obj[(L, p) ↦ L' ∪ ĥ.obj(·, p)]]`: weak update of property `p`
    of every abstract location in `L` (see REMARK 5 on the paper's notation). -/
def AHeap.weakSetObj (h : AHeap) (L : ALocSet) (p : PropName) (L' : ALocSet) :
    AHeap :=
  { h with obj := fun l q l' => h.obj l q l' ∨ (L l ∧ q = p ∧ L' l') }

/-- Weak update of every property named by a string in `V`, of every abstract
    location in `L`. -/
def AHeap.weakSetObjV (h : AHeap) (L : ALocSet) (V : VSet) (L' : ALocSet) :
    AHeap :=
  { h with obj := fun l q l' =>
      h.obj l q l' ∨ (L l ∧ V.Mem (.str q) ∧ L' l') }

/-- Weak update of the fields of a freshly allocated abstract object. -/
def AHeap.weakSetObjs (h : AHeap) (l : ALoc) :
    List (PropName × ALocSet) → AHeap
  | []           => h
  | (p, L) :: ps => (h.weakSetObj {l} p L).weakSetObjs l ps

/-- `δ̂[dep ↦ δ̂.dep[l̂ ↦ d̂ ∪ δ̂.dep(l̂)]]`. -/
def AReg.weakSetDep (δ : AReg) (l : ALoc) (d : ALocSet) : AReg :=
  { δ with dep := fun l' => if l' = l then d ∪ δ.dep l' else δ.dep l' }

/-- `δ̂[dep ↦ δ̂.dep[l̂ ↦ d̂]]`: the *strong* counterpart of `weakSetDep`, which
    discards the dependencies previously recorded at `l̂`.  It mirrors the
    concrete `Reg.setDep` exactly, and is used only by [Object Initialization]
    (see REMARK 3 for why a strong update on a summary location deserves
    care). -/
def AReg.setDep (δ : AReg) (l : ALoc) (d : ALocSet) : AReg :=
  { δ with dep := fun l' => if l' = l then d else δ.dep l' }

/-- A strong update would normally break the monotonicity of the abstract
    transformer, which [Weakening], [While] and the fixed points of §5.1 rely
    on.  It does not here: both sides carry the same `d̂` at `l̂` afterwards. -/
theorem AReg.setDep_mono {δ₁ δ₂ : AReg} (k : δ₁ ⊑ δ₂) (l : ALoc)
    (d : ALocSet) : (δ₁.setDep l d) ⊑ (δ₂.setDep l d) := by
  refine ⟨?_, k.2.1, k.2.2⟩
  intro l'
  show (if l' = l then d else δ₁.dep l') ⊆ (if l' = l then d else δ₂.dep l')
  by_cases hl : l' = l
  · rw [if_pos hl, if_pos hl]
    exact ALocSet.subset_refl d
  · rw [if_neg hl, if_neg hl]
    exact k.1 l'

/-- `ρ̂[x ↦ L]`.  Unlike heap cells, the store is updated strongly. -/
def ASto.upd (ρ : ASto) (x : Var) (L : ALocSet) : ASto :=
  fun y => if y = x then L else ρ y

/-- `[xᵢ ↦ Lᵢ]`, the abstract store built on function entry. -/
def ASto.ofParams : List Var → List ALocSet → ASto
  | x :: xs, L :: Ls => (ASto.ofParams xs Ls).upd x L
  | _,       _       => ASto.bot

/-! ## Parameters of the abstract semantics -/

/-- Parameters of the analysis: the abstract literal locations `l̂_v`, the
    abstract allocator `alloc_a`, and the abstract binary operators `⊕̂`. -/
class Abstract where
  /-- `l̂_v`. -/
  litLocA : Val → ALoc
  /-- `alloc_a(ĥ, κ)` (see REMARK 6). -/
  allocA  : AHeap → Idx → ALoc
  /-- `⊕̂(V₁, V₂)`: the operator lifted to value sets, widening to `⊤`
      whenever the resulting set exceeds a configurable bound (§5.1). -/
  opSemA  : BinOp → VSet → VSet → VSet

open Abstract

/-- The assumptions the analysis relies on.  Soundness of `⊕̂` with respect to
    the concrete `⊕` belongs with the abstraction relation of Def. B8 and is
    therefore not stated here. -/
structure AbstractSpec [Abstract] : Prop where
  /-- `⊕̂` is monotone, as required by the [Weakening] rule. -/
  opSemA_mono : ∀ op V₁ V₁' V₂ V₂', V₁ ⊑ V₁' → V₂ ⊑ V₂' →
    (opSemA op V₁ V₂) ⊑ (opSemA op V₁' V₂')
  /-- The allocation strategy is *per instruction site*: it maps every
      instruction identifier to a fixed abstract location, independently of
      the current heap.  This — not the signature of `alloc_a` — is what makes
      the abstract location space finite, and hence the fixed points of §5.1
      reachable. -/
  allocA_site : ∀ h h' κ, allocA h κ = allocA h' κ

/-! ## Abstract expression evaluation (Fig. B2)

`⟦v⟧ρ̂ ≜ {l̂_v}` and `⟦x⟧ρ̂ ≜ ρ̂(x)`.  Unlike its concrete counterpart, this is
total: an unbound variable evaluates to `∅`. -/

/-- `⟦e⟧ρ̂`. -/
def aevalE [Abstract] (ρ : ASto) : Expr → ALocSet
  | .val v => {litLocA v}
  | .var x => ρ x

/-- `⟦e₁⟧ρ̂, ..., ⟦eₙ⟧ρ̂`, pointwise. -/
def aevalEs [Abstract] (ρ : ASto) : List Expr → List ALocSet
  | []      => []
  | e :: es => aevalE ρ e :: aevalEs ρ es

/-! ## Well-formedness (Definition B3) -/

/-- An abstract heap `ĥ` is well formed w.r.t. a statement `s` iff every
    literal `v` occurring in `s` belongs to the value set of its abstract
    location `l̂_v` (see REMARK 4). -/
def AHeap.WF [Abstract] (h : AHeap) (s : Stmt) : Prop :=
  (∀ v ∈ s.lits, (h.val (litLocA v)).Mem v) ∧
  (h.val (litLocA .undef)).Mem .undef

/-! ## Call candidates

REMARK 1 of the previous revision: Fig. B7 requires the callee expression to
evaluate to a *singleton* `{l̂_f}`, so a call site the analysis cannot resolve
uniquely (callbacks, methods read out of a polluted object) has no abstract
derivation at all, while the concrete semantics has one — and Theorem B15 is
then unprovable in that case.  The rule below instead analyses the body of
*every* candidate function and joins the results. -/

/-- Total accessors for the parameters and body of `f`, with the junk values
    `[]` / `skip` outside `dom(Γ)`.  Used only under a `(Γ f).isSome` premise. -/
def Env.params (Γ : Env) (f : Fid) : List Var :=
  ((Γ f).map Prod.fst).getD []

def Env.body (Γ : Env) (f : Fid) : Stmt :=
  ((Γ f).map Prod.snd).getD .skip

/-- `f` is a candidate callee at a site whose callee expression abstracts to
    `L_f` and which passes `n` arguments: some location in `L_f` may hold the
    function value `f`, `Γ` defines `f`, and the arity matches.

    Membership is *forced*, not chosen: the rule quantifies over exactly the
    `f` satisfying this, so it cannot silently analyse fewer branches than
    the concrete semantics can take. -/
def IsCandidate [Abstract] (Γ : Env) (h : AHeap) (L_f : ALocSet) (n : Nat)
    (f : Fid) : Prop :=
  ((h.valOf L_f).Mem (.fid f)) ∧ (Γ f).isSome ∧ (Γ.params f).length = n

/-- The analysis assumes `Γ` has finite domain — true of any real program, and
    what makes the candidate set at a call site enumerable as a list.  Note
    this cannot be recovered from the value domain instead: widening may send
    `ĥ.val(l̂)` to `⊤`, which is not finite. -/
structure EnvSpec (Γ : Env) : Prop where
  fin : ∃ fs : List Fid, ∀ f, (Γ f).isSome → f ∈ fs

/-- The locations a candidate branch may return, folding in the implicit-`undef`
    convention: a body that falls through returns `undefined`, so `l̂_undef` is
    added to whatever the partially-returning paths already collected. -/
def AOut.retLocs [Abstract] (o : AOut) : ALocSet :=
  match o.kind with
  | .ret  => o.locs
  | .cont => o.locs ∪ {litLocA .undef}

/-- One candidate's contribution to the call trace: its own `Call`, its body,
    and its own `Ret`, kept together as a single sequential unit so that the
    alternation below cannot interleave one candidate's `Call` with another's
    body or `Ret`. -/
def branchTrace [Abstract] (f : Fid) (Ls : List ALocSet) (t : ATrc)
    (L : ALocSet) : ATrc :=
  .seq (.act (.call (litLocA (.fid f)) Ls))
       (.seq t (.act (.ret (litLocA (.fid f)) L)))

/-! ## Call summaries and the summary environment

Recursion cannot be handled the way `[While]` handles loops.  `[While]`'s
premise mentions only the loop body, one level deep, so the rule is
self-contained and `t̂*` carries every iteration.  The premise of a call rule
instead demands a full sub-derivation of the callee body — and for a recursive
`f` that body contains a call to `f`, needing a further sub-derivation, so no
finite derivation tree exists.

The standard fix is assume/guarantee over *call summaries*: `[Fix]` analyses
the body against an assumed summary and validates it by a post-fixed-point
check (exactly `[While]`'s technique, lifted from states to summaries), and
`[Assume]` discharges the recursive occurrence against the assumption without
a sub-derivation, which is what makes the tree finite. -/

/-- The effect of a call to `f`: the heap and taint register it may produce,
    and the locations it may return. -/
structure ASummary where
  heap : AHeap
  reg  : AReg
  ret  : ALocSet

/-- `Σ`: the summaries currently *assumed* for functions whose analysis is in
    progress.  Empty at the top level; extended only by `[Fix]`, and only for
    a summary that the post-fixed-point check has validated. -/
def ASigma := Fid → Option ASummary

def ASigma.empty : ASigma := fun _ => none

def ASigma.upd (Sg : ASigma) (f : Fid) (s : ASummary) : ASigma :=
  fun g => if g = f then some s else Sg g

/-! ## Abstract configurations -/

/-- `⟨ĥ, ρ̂, δ̂⟩`. -/
structure AConf where
  heap : AHeap
  sto  : ASto
  reg  : AReg

/-- `⟨ĥ', ρ̂', δ̂', t̂, ô⟩`. -/
structure ARes where
  heap : AHeap
  sto  : ASto
  reg  : AReg
  trc  : ATrc
  out  : AOut

/-! ## Abstract big-step semantics (Figs. B6 and B7)

`Γ ⊢ ⟨ĥ, ρ̂, δ̂, s⟩ ⇓a ⟨ĥ', ρ̂', δ̂', t̂, ô⟩`.

As in the concrete semantics, each rule is stated with the components of the
resulting configuration introduced as variables and fixed by equational
premises, so that the correspondence with the figures is literal. -/

mutual

/-- `Γ; Σ ⊢ ⟨ĥ, ρ̂, δ̂, s⟩ ⇓a ⟨ĥ', ρ̂', δ̂', t̂, ô⟩`. -/
inductive ABigStep [Abstract] (Γ : Env) : ASigma → AConf → Stmt → ARes → Prop where

  /-- [Skip] -/
  | skip {Sg h ρ δ} :
      ABigStep Γ Sg ⟨h, ρ, δ⟩ .skip ⟨h, ρ, δ, .emp, ⟨.cont, ∅⟩⟩

  /-- [Assignment] -/
  | assign {Sg h ρ ρ' δ x e L} :
      aevalE ρ e = L →
      ρ' = ρ.upd x L →
      ABigStep Γ Sg ⟨h, ρ, δ⟩ (.assign x e) ⟨h, ρ', δ, .emp, ⟨.cont, ∅⟩⟩

  /-- [Binary Operation].  The value of the result location is joined, not
      overwritten, since several concrete objects share `l̂`. -/
  | binOp {Sg h h' ρ ρ' δ δ' x κ op e₁ e₂ L₁ L₂ V₁ V₂ V l d} :
      aevalE ρ e₁ = L₁ →
      aevalE ρ e₂ = L₂ →
      h.valOf L₁ = V₁ →
      h.valOf L₂ = V₂ →
      l = allocA h κ →
      V = opSemA op V₁ V₂ →
      h' = h.weakSetVal l V →
      ρ' = ρ.upd x {l} →
      d = δ.depOf L₁ ∪ δ.depOf L₂ ∪ L₁ ∪ L₂ →
      δ' = δ.weakSetDep l d →
      ABigStep Γ Sg ⟨h, ρ, δ⟩ (.binOp x κ op e₁ e₂) ⟨h', ρ', δ', .emp, ⟨.cont, ∅⟩⟩

  /-- [Object Initialization].  The freshly allocated location is given an
      empty dependency set, mirroring the concrete `δ.dep[l ↦ ∅]` and making
      step I13.1 of the proof of Theorem B15 hold by construction.  Note that,
      unlike every other register and heap update of the abstract semantics,
      this one is *strong* (see REMARK 3). -/
  | objLit {Sg h h' ρ ρ' δ δ' x κ fs Ls l} :
      aevalEs ρ (fs.map Prod.snd) = Ls →
      l = allocA h κ →
      h' = h.weakSetObjs l ((fs.map Prod.fst).zip Ls) →
      ρ' = ρ.upd x {l} →
      δ' = δ.setDep l ∅ →
      ABigStep Γ Sg ⟨h, ρ, δ⟩ (.objLit x κ fs) ⟨h', ρ', δ', .emp, ⟨.cont, ∅⟩⟩

  /-- [Static Property Lookup] -/
  | lookupS {Sg h ρ ρ' δ x e p L₁ L₂} :
      aevalE ρ e = L₁ →
      L₂ = h.objOf L₁ p →
      ρ' = ρ.upd x L₂ →
      ABigStep Γ Sg ⟨h, ρ, δ⟩ (.lookupS x e p)
        ⟨h, ρ', δ, .act (.lookup L₂ L₁ {litLocA (.str p)}), ⟨.cont, ∅⟩⟩

  /-- [Dynamic Property Lookup] -/
  | lookupD {Sg h ρ ρ' δ x e₁ e₂ L₁ L₂ L₃ V} :
      aevalE ρ e₁ = L₁ →
      aevalE ρ e₂ = L₂ →
      V = h.valOf L₂ →
      L₃ = h.objOfV L₁ V →
      ρ' = ρ.upd x L₃ →
      ABigStep Γ Sg ⟨h, ρ, δ⟩ (.lookupD x e₁ e₂)
        ⟨h, ρ', δ, .act (.lookup L₃ L₁ L₂), ⟨.cont, ∅⟩⟩

  /-- [Static Property Update].  The premise `ĥ.val(L₂) = V` of Fig. B6 is
      vestigial — `V` occurs nowhere else — and is omitted. -/
  | updateS {Sg h h' ρ δ e₁ p e₂ L₁ L₂} :
      aevalE ρ e₁ = L₁ →
      aevalE ρ e₂ = L₂ →
      h' = h.weakSetObj L₁ p L₂ →
      ABigStep Γ Sg ⟨h, ρ, δ⟩ (.updateS e₁ p e₂)
        ⟨h', ρ, δ, .act (.update L₁ {litLocA (.str p)} L₂), ⟨.cont, ∅⟩⟩

  /-- [Dynamic Property Update] -/
  | updateD {Sg h h' ρ δ e₁ e₂ e₃ L₁ L₂ L₃ V} :
      aevalE ρ e₁ = L₁ →
      aevalE ρ e₂ = L₂ →
      aevalE ρ e₃ = L₃ →
      V = h.valOf L₂ →
      h' = h.weakSetObjV L₁ V L₃ →
      ABigStep Γ Sg ⟨h, ρ, δ⟩ (.updateD e₁ e₂ e₃)
        ⟨h', ρ, δ, .act (.update L₁ L₂ L₃), ⟨.cont, ∅⟩⟩

  /-- [Sequence Ret] -/
  | seqRet {Sg h h' ρ ρ' δ δ' s₁ s₂ t L} :
      ABigStep Γ Sg ⟨h, ρ, δ⟩ s₁ ⟨h', ρ', δ', t, ⟨.ret, L⟩⟩ →
      ABigStep Γ Sg ⟨h, ρ, δ⟩ (.seq s₁ s₂) ⟨h', ρ', δ', t, ⟨.ret, L⟩⟩

  /-- [Sequence Cont] -/
  | seqCont {Sg h h' h'' ρ ρ' ρ'' δ δ' δ'' s₁ s₂ t₁ t₂ L₁ L₂ o} :
      ABigStep Γ Sg ⟨h, ρ, δ⟩ s₁ ⟨h', ρ', δ', t₁, ⟨.cont, L₁⟩⟩ →
      ABigStep Γ Sg ⟨h', ρ', δ'⟩ s₂ ⟨h'', ρ'', δ'', t₂, ⟨o, L₂⟩⟩ →
      ABigStep Γ Sg ⟨h, ρ, δ⟩ (.seq s₁ s₂) ⟨h'', ρ'', δ'', .seq t₁ t₂, ⟨o, L₁ ⊔ L₂⟩⟩

  /-- [If-Then-Else].  Both branches are analysed from the *same* input state
      and the results are joined; the guard is not inspected.  The outcome
      join is partial — see REMARK 2. -/
  | ifElse {Sg h h₁ h₂ h' ρ ρ₁ ρ₂ ρ' δ δ₁ δ₂ δ' e s₁ s₂ t₁ t₂ t o₁ o₂ o} :
      ABigStep Γ Sg ⟨h, ρ, δ⟩ s₁ ⟨h₁, ρ₁, δ₁, t₁, o₁⟩ →
      ABigStep Γ Sg ⟨h, ρ, δ⟩ s₂ ⟨h₂, ρ₂, δ₂, t₂, o₂⟩ →
      h' = h₁ ⊔ h₂ →
      ρ' = ρ₁ ⊔ ρ₂ →
      δ' = δ₁ ⊔ δ₂ →
      t = t₁ || t₂ →
      o = o₁ ⊔ o₂ →
      ABigStep Γ Sg ⟨h, ρ, δ⟩ (.ifElse e s₁ s₂) ⟨h', ρ', δ', t, o⟩

  /-- [While].  The body must be analysable in a state that it reproduces,
      i.e. in a post-fixed point of its own abstract transformer; the least
      such state is obtained by combining this rule with [Weakening]. -/
  | whileDo {Sg h ρ δ e s t L} :
      ABigStep Γ Sg ⟨h, ρ, δ⟩ s ⟨h, ρ, δ, t, ⟨_, L⟩⟩ →
      ABigStep Γ Sg ⟨h, ρ, δ⟩ (.whileDo e s) ⟨h, ρ, δ, .star t, ⟨.cont, L⟩⟩

  /-- [Function Call], multi-target.  `fs` enumerates *exactly* the candidate
      callees (`IsCandidate`); each is analysed by `ACallBranch` below, and the
      heap, register, return locations and trace are combined across them.

      The trace keeps each candidate's `Call`, body and `Ret` together as one
      unit and alternates over the units, so a `Call` of one candidate can
      never be paired with the `Ret` of another. -/
  | call {Sg h ρ δ x e es L_f Ls h' ρ' δ' L t} {fs : List Fid}
      {hs : Fid → AHeap} {δs : Fid → AReg}
      {ts : Fid → ATrc} {Ls' : Fid → ALocSet} :
      aevalE ρ e = L_f →
      aevalEs ρ es = Ls →
      fs ≠ [] →
      (∀ f, f ∈ fs ↔ IsCandidate Γ h L_f Ls.length f) →
      (∀ f ∈ fs, ACallBranch Γ Sg h δ f Ls (hs f) (δs f) (Ls' f) (ts f)) →
      h' = AHeap.joinAll (fs.map hs) →
      δ' = AReg.joinAll (fs.map δs) →
      L  = ALocSet.unionAll (fs.map Ls') →
      t  = ATrc.choice (fs.map (fun f => branchTrace f Ls (ts f) (Ls' f))) →
      ρ' = ρ.upd x L →
      ABigStep Γ Sg ⟨h, ρ, δ⟩ (.call x e es) ⟨h', ρ', δ', t, ⟨.cont, ∅⟩⟩

  /-- [Function Call], no candidate.  Only reachable at a call site no concrete
      execution `α`-related to `ĥ, ρ̂, δ̂` can perform (by B8.1.b the concrete
      callee's `fid` would otherwise be forced into `ĥ.valOf L_f`), so the
      result is unconstrained by soundness.  The state is passed through rather
      than collapsed to `⊥`, so that a dead call in one branch of an `if` does
      not starve the analysis of everything sequenced after it. -/
  | callNone {Sg h ρ δ x e es L_f Ls ρ'} :
      aevalE ρ e = L_f →
      aevalEs ρ es = Ls →
      (∀ f, ¬ IsCandidate Γ h L_f Ls.length f) →
      ρ' = ρ.upd x ∅ →
      ABigStep Γ Sg ⟨h, ρ, δ⟩ (.call x e es) ⟨h, ρ', δ, .emp, ⟨.cont, ∅⟩⟩

  /-- [Weakening]: a derivation from a larger input state, with a smaller
      result, yields a derivation from a smaller input state with a larger
      result. -/
  | weaken {Sg h h' h'' h''' ρ ρ' ρ'' ρ''' δ δ' δ'' δ''' s t t' o o'} :
      AHeap.Le h h'' →
      ASto.Le ρ ρ'' →
      AReg.Le δ δ'' →
      ABigStep Γ Sg ⟨h'', ρ'', δ''⟩ s ⟨h', ρ', δ', t, o⟩ →
      AHeap.Le h' h''' →
      ASto.Le ρ' ρ''' →
      AReg.Le δ' δ''' →
      ATrc.Le t t' →
      AOut.Le o o' →
      ABigStep Γ Sg ⟨h, ρ, δ⟩ s ⟨h''', ρ''', δ''', t', o'⟩

  /-- [Return] -/
  | ret {Sg h ρ δ e L} :
      aevalE ρ e = L →
      ABigStep Γ Sg ⟨h, ρ, δ⟩ (.ret e) ⟨h, ρ, δ, .emp, ⟨.ret, L⟩⟩

  /-- [SetTaint] -/
  | setTaint {Sg h ρ δ δ' e L} :
      aevalE ρ e = L →
      δ' = { δ with ac := L ∪ δ.ac } →
      ABigStep Γ Sg ⟨h, ρ, δ⟩ (.setTaint e) ⟨h, ρ, δ', .emp, ⟨.cont, ∅⟩⟩

  /-- [SetSink] -/
  | setSink {Sg h ρ δ δ' e L} :
      aevalE ρ e = L →
      δ' = { δ with sk := L ∪ δ.sk } →
      ABigStep Γ Sg ⟨h, ρ, δ⟩ (.setSink e) ⟨h, ρ, δ', .emp, ⟨.cont, ∅⟩⟩

/-- Analysis of a *single* candidate callee `f` at a call site passing the
    argument location sets `Ls`, producing the heap, register, return locations
    and body trace of that one branch. -/
inductive ACallBranch [Abstract] (Γ : Env) :
    ASigma → AHeap → AReg → Fid → List ALocSet →
    AHeap → AReg → ALocSet → ATrc → Prop where

  /-- [Call-Assume].  `f`'s summary is already assumed (we are inside the
      analysis of `f` itself), so the recursive occurrence is discharged
      against the assumption with *no* sub-derivation — this is what keeps the
      derivation tree finite — and contributes the recursion variable `X` to
      the trace. -/
  | assume {Sg h δ f Ls s} :
      Sg f = some s →
      ACallBranch Γ Sg h δ f Ls s.heap s.reg s.ret .tvar

  /-- [Call-Fix].  Analyse `f`'s body against an *assumed* summary `s`; if the
      result is within `s`, the assumption is a post-fixed point and hence
      valid, and the call may use it.  The emitted trace binds `μX`, so the
      recursion variables contributed by `[Call-Assume]` inside `t` refer back
      to this body.

      This is the exact analogue of `[While]`, which likewise requires the body
      to be analysable in a state it reproduces; the fixed point is reachable
      for the same reason — the abstract domains are finite (one abstract
      location per allocation site) and every transformer is monotone. -/
  | fix {Sg h δ f Ls s h' ρf' δ' t o} :
      ABigStep Γ (Sg.upd f s) ⟨h, ASto.ofParams (Γ.params f) Ls, δ⟩ (Γ.body f)
        ⟨h', ρf', δ', t, o⟩ →
      h' ⊑ s.heap →
      δ' ⊑ s.reg →
      o.retLocs ⊆ s.ret →
      ACallBranch Γ Sg h δ f Ls s.heap s.reg s.ret (.mu t)

end

/-- Notation for the abstract judgement. -/
scoped notation:50 Γ "; " Sg " ⊢ " c " ⇓a[" s "] " r => ABigStep Γ Sg c s r

/-! ## The analysis (§5.1)

`SA(Γ, s) = (t̂, Î)`: abstract evaluation of `s` from the default initial
abstract state.  We expose the final heap and register rather than the
taint-value interpretation `Î` they induce, since `Î` belongs with the query
language. -/

/-- `SA(Γ, s)` produced the abstract trace `t̂` and the final abstract heap and
    taint register `ĥ_f`, `δ̂_f`. -/
def SA [Abstract] (Γ : Env) (s : Stmt) (t : ATrc) (hf : AHeap) (δf : AReg) :
    Prop :=
  ∃ ρf o, ABigStep Γ ASigma.empty ⟨AHeap.bot, ASto.bot, AReg.bot⟩ s ⟨hf, ρf, δf, t, o⟩

/-!
## REMARKS

**1. [Function Call] is defined too narrowly, and drops `δ̂'`. (FIXED above.)**
Two premises are problematic. First, `⟦e⟧ρ̂ = {l̂_f}` requires the callee
expression to evaluate to a *singleton*; whenever the analysis cannot resolve
a call target uniquely — the common case for callbacks and for methods read
out of a polluted object — no abstract derivation exists at all, while the
concrete semantics has one. Second, `ĥ.val(l̂_f) = f` is ill-typed in the
abstract domain, since `ĥ.val` yields a set of values; the intended premise
is `f ∈ ĥ.val(l̂_f)`, which is what is formalised above. Both point to the
same fix: analyse the body for *every* `l̂ ∈ ⟦e⟧ρ̂` and every `f` with
`fid f ∈ ĥ.val(l̂)`, and join the results, so that a call site with several
possible targets over-approximates all of them. As it stands, the analysis
soundness theorem (B15) is not provable in the [Function Call] case: the
induction hypothesis is only available when the abstract call resolves
uniquely. Separately, the conclusion of the rule in Fig. B7 lists only four
components — `⟨ĥ', ρ̂', Call(...); t̂; Ret(...), ·⟩` — with `δ̂'` omitted.

**2. [If-Then-Else] uses a partial join on outcomes. (FIXED.)** Def. B5.4
leaves `ô₁ ⊔ ô₂` undefined when one branch returns and the other falls
through, so `if (c) { return x } else { y := 1 }` had no abstract derivation.
`AOut` above carries a kind together with the collected return locations, and
`AOut.join` is total: the result continues if either branch may continue,
while still collecting the return locations of the branch that returned.

**3. [Object Initialization] performs the reset that step I13.1 of the
soundness proof assumes.** Fig. B7's abstract rule leaves `δ̂` unchanged,
whereas the concrete rule sets `δ.dep[l ↦ ∅]`. The proof of Theorem B15
nevertheless asserts (I13.1) that `δ̂'.dep(l̂) = ∅`, justified by "the abstract
taint register assignment of empty dependency for new object allocations",
which Fig. B7 does not perform. The rule formalised above closes that gap on
the side of the semantics: it sets `δ̂' = δ̂[dep ↦ δ̂.dep[l̂ ↦ ∅]]` through
`AReg.setDep`, so the abstract rule, the concrete rule and I13.1 all agree,
and the abstract derivation follows the concrete one step for step. The price
is that this is the only *strong* update in the abstract semantics — every
other heap and register update is weak, precisely because abstract locations
summarise many concrete ones. Two consequences.

*Monotonicity is preserved.* [Weakening], [While] and the fixed points of §5.1
all require the abstract transformer to be monotone, and a strong update is
the kind of operation that typically destroys monotonicity. Here it does not:
`AReg.setDep_mono` above proves `δ̂₁ ⊑ δ̂₂ → δ̂₁[dep(l̂) ↦ d̂] ⊑ δ̂₂[dep(l̂) ↦ d̂]`,
since after the update both sides carry the same `d̂` at `l̂` and are unchanged
elsewhere.

*The soundness of the reset becomes a real obligation, discharged only for
injective allocators.* `l̂` is a summary location: under
`AbstractSpec.allocA_site` the same `l̂` is returned at every execution of the
site `κ`, so it abstracts every concrete object allocated there — one per loop
iteration, one per call. Discarding `δ̂.dep(l̂)` discards, with it, the recorded
dependencies of objects allocated at *earlier* iterations that are still
reachable, and that is what Def. B8.3.a forbids. Whether it can actually
happen depends on the allocation strategy. No rule other than [Binary
Operation] writes `dep`, and that rule writes at its own allocation site;
hence if `alloc_a` maps distinct instruction identifiers to distinct abstract
locations, `δ̂.dep(l̂)` is `∅` at every object-allocation site already and the
reset is a no-op — this is an observation about the shape of the rules, not
something proved here, and it does not survive [Weakening], which may raise
`δ̂` arbitrarily before the rule applies. If `alloc_a` merges instruction sites
(a coarser strategy, which §5.1 permits and which real analyses use to bound
`L̂oc` further), the reset can lose dependencies and the analysis becomes
unsound for taint. Under such an allocator the alternative fix is the right
one: drop I13.1 from the proof and leave `δ̂` untouched, which is sound
unconditionally, because by Def. B8.3.a the concrete `δ'.dep(l) = ∅` imposes
no obligation and `δ' ∼α' δ̂` follows from `δ ∼α δ̂` alone. Replacing
`δ.setDep l ∅` by `δ` in the rule above recovers that variant.

**4. Def. B3** states `ĥ.val(l_v) = v`; it should read `v ∈ ĥ.val(l̂_v)` — a
concrete location and an equality where a set membership is meant.

**6. `alloc_a` does not need the heap.** §5.1 describes the strategy as
"mapping every instruction identifier `κ` to a fixed abstract location", which
is what bounds `L̂oc` and hence guarantees that the fixed points exist. The
signature `alloc_a(ĥ, κ)` suggests otherwise; `AbstractSpec.allocA_site`
records the property the analysis actually relies on.

**8. Recursion: the summary environment and its proof obligation.**
`[Call-Fix]` / `[Call-Assume]` replace the model builder's depth cutoff
(`resolve_function`, which routes a *known* function into the unknown-call
path once it occurs twice on the call stack). That cutoff cannot be proved
sound: a concrete execution recursing deeper than the bound emits nested
`Call`/`Ret` pairs with no counterpart in the abstract trace, so Def. B8.6 
fails. The assume/guarantee rules above cover every depth instead.

The price is a new obligation for Theorem B15. `[Call-Assume]` consumes a
summary *without* re-deriving it, so soundness holds only if every summary in
`Σ` is itself sound with respect to the concrete semantics. The theorem
therefore needs a hypothesis "`Σ` is valid" — every `Σ(f) = s` over-approximates
every concrete execution of `f` — which `[Call-Fix]` must be shown to preserve
when it extends `Σ`. This is the standard assume/guarantee argument, and it is
the one genuinely new piece of proof work recursion adds; it does not arise
anywhere in the paper's Appendix B.

**7. Traces are not widened.** `t̂*` is exact regular closure, so the abstract
trace of a program grows with the program but never loses precision; only the
value and location domains are widened. Worth saying explicitly, since it is
what makes the query-checking step of §6 decidable but also what makes the
abstract trace, rather than the state, the source of blow-up on large
packages.
-/

end CoreJS
