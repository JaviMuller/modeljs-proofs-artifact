/-
  # Core JavaScript — Automaton Semantics

  This file is *not* a transcription of any figure in the paper. It is this
  branch's own contribution: the automaton-based replacement for the
  μ-trace/summary machinery of `CoreJsAbstractSemantics.lean`
  (`ATrc`/`AOut`/`ASummary`/`ASigma`/`ACallBranch`/`ABigStep`'s control-flow
  rules), described in `DESIGN_AND_PLAN.md` §4.3–4.4.

  **Independent of the old abstract-semantics files.** `CoreJsAbstractSyntax
  .lean`/`CoreJsAbstractSemantics.lean`/`CoreJsAbstractionRelation.lean`/
  `CoreJsAbstractionSoundness.lean` are kept in the repository only as
  reference material for this rewrite (their per-statement value-update math
  is where the atomic effect functions below come from) and are slated for
  removal once the automaton development is complete. This file therefore
  does **not** import any of them — it re-declares the abstract domains
  (`ALoc`, `ALocSet`, `VSet`, `AHeap`, `ASto`, `AReg`) it needs from scratch,
  rather than reusing theirs, so that the automaton development has no
  dependency left to sever later.

  See `PROBLEMS.md` for the implementation decisions made while turning
  `DESIGN_AND_PLAN.md`'s §4 into Lean, several of which concern this file
  specifically (Decisions 1, 2, 3, 4, 5).

  Plain Lean 4 — no Mathlib required.
-/

import CoreJsAutomatonSyntax
import CoreJsSemantics

namespace CoreJS

/-! ## Abstract locations and location sets

Reproduced from `CoreJsAbstractSyntax.lean` (Fig. B1) rather than imported —
see the file header. Nothing below depends on the representation. -/

def ALoc := Nat

instance : DecidableEq ALoc := inferInstanceAs (DecidableEq Nat)
instance : Inhabited ALoc   := inferInstanceAs (Inhabited Nat)

/-- `P(L̂oc)`, represented as a predicate. -/
def ALocSet := ALoc → Prop

instance : EmptyCollection ALocSet  := ⟨fun _ => False⟩
instance : Singleton ALoc ALocSet   := ⟨fun l l' => l' = l⟩
instance : Insert ALoc ALocSet      := ⟨fun l A l' => l' = l ∨ A l'⟩
instance : Union ALocSet            := ⟨fun A B l => A l ∨ B l⟩
instance : HasSubset ALocSet        := ⟨fun A B => ∀ l, A l → B l⟩

/-- `V ∈ P(Val)^⊤`: value sets extended with a distinguished `⊤`, produced by
    the widening of `⊕̂`. -/
inductive VSet where
  | vals (V : Val → Prop)
  | top

def VSet.Mem : VSet → Val → Prop
  | .vals V, v => V v
  | .top,    _ => True

def VSet.Subset (V₁ V₂ : VSet) : Prop := ∀ v, V₁.Mem v → V₂.Mem v

def VSet.join : VSet → VSet → VSet
  | .top,     _        => .top
  | .vals _,  .top     => .top
  | .vals V₁, .vals V₂ => .vals (fun v => V₁ v ∨ V₂ v)

instance : EmptyCollection VSet := ⟨.vals fun _ => False⟩
instance : Membership Val VSet  := ⟨VSet.Mem⟩
instance : HasSubset VSet       := ⟨VSet.Subset⟩
instance : Union VSet           := ⟨VSet.join⟩

/-! ## Abstract heap, store and taint register (Fig. B1) -/

/-- Abstract stores `ρ̂ ∈ Ŝto : Var ⇀ P(L̂oc)`, modelled total into `∅`. -/
def ASto := Var → ALocSet

structure AHeap where
  obj : ALoc → PropName → ALocSet
  val : ALoc → VSet

structure AReg where
  dep : ALoc → ALocSet
  ac  : ALocSet
  sk  : ALocSet

def ASto.bot : ASto := fun _ => ∅
def AHeap.bot : AHeap := { obj := fun _ _ => ∅, val := fun _ => ∅ }
def AReg.bot : AReg := { dep := fun _ => ∅, ac := ∅, sk := ∅ }

/-! ### Order (Def. B4) and join (Def. B5), restricted to the domains still
    needed (no `AAct`/`ATrc`/`AOut` here — decision 2 of `PROBLEMS.md`). -/

def AHeap.Le (h₁ h₂ : AHeap) : Prop :=
  (∀ l p, h₁.obj l p ⊆ h₂.obj l p) ∧ (∀ l, (h₁.val l) ⊆ (h₂.val l))

def ASto.Le (ρ₁ ρ₂ : ASto) : Prop := ∀ x, ρ₁ x ⊆ ρ₂ x

def AReg.Le (δ₁ δ₂ : AReg) : Prop :=
  (∀ l, δ₁.dep l ⊆ δ₂.dep l) ∧ δ₁.ac ⊆ δ₂.ac ∧ δ₁.sk ⊆ δ₂.sk

instance : LE VSet  := ⟨VSet.Subset⟩
instance : LE ASto  := ⟨ASto.Le⟩
instance : LE AHeap := ⟨AHeap.Le⟩
instance : LE AReg  := ⟨AReg.Le⟩

scoped infix:50 " ⊑ " => LE.le

class Join (α : Type) where
  join : α → α → α

scoped infixl:65 " ⊔ " => Join.join

def AHeap.join (h₁ h₂ : AHeap) : AHeap :=
  { obj := fun l p => h₁.obj l p ∪ h₂.obj l p
    val := fun l => (h₁.val l) ∪ (h₂.val l) }

def ASto.join (ρ₁ ρ₂ : ASto) : ASto := fun x => ρ₁ x ∪ ρ₂ x

def AReg.join (δ₁ δ₂ : AReg) : AReg :=
  { dep := fun l => δ₁.dep l ∪ δ₂.dep l
    ac  := δ₁.ac ∪ δ₂.ac
    sk  := δ₁.sk ∪ δ₂.sk }

instance : Join VSet    := ⟨VSet.join⟩
instance : Join ALocSet := ⟨fun A B => A ∪ B⟩
instance : Join AHeap   := ⟨AHeap.join⟩
instance : Join ASto    := ⟨ASto.join⟩
instance : Join AReg    := ⟨AReg.join⟩

/-! ## Lifting the heap/register to sets of locations (Fig. B6) -/

def AHeap.valOf (h : AHeap) (L : ALocSet) : VSet :=
  .vals (fun v => ∃ l, L l ∧ (h.val l).Mem v)

def AHeap.objOf (h : AHeap) (L : ALocSet) (p : PropName) : ALocSet :=
  fun l' => ∃ l, L l ∧ h.obj l p l'

def AHeap.objOfV (h : AHeap) (L : ALocSet) (V : VSet) : ALocSet :=
  fun l' => ∃ l p, L l ∧ V.Mem (.str p) ∧ h.obj l p l'

def AReg.depOf (δ : AReg) (L : ALocSet) : ALocSet :=
  fun l' => ∃ l, L l ∧ δ.dep l l'

/-! ## Abstract updates (Fig. B6). All heap/register updates are weak (§5.1),
    except `AReg.setDep`, used only by object initialisation. -/

def AHeap.weakSetVal (h : AHeap) (l : ALoc) (V : VSet) : AHeap :=
  { h with val := fun l' => if l' = l then VSet.join V (h.val l') else h.val l' }

def AHeap.weakSetObj (h : AHeap) (L : ALocSet) (p : PropName) (L' : ALocSet) :
    AHeap :=
  { h with obj := fun l q l' => h.obj l q l' ∨ (L l ∧ q = p ∧ L' l') }

def AHeap.weakSetObjV (h : AHeap) (L : ALocSet) (V : VSet) (L' : ALocSet) :
    AHeap :=
  { h with obj := fun l q l' => h.obj l q l' ∨ (L l ∧ V.Mem (.str q) ∧ L' l') }

def AHeap.weakSetObjs (h : AHeap) (l : ALoc) :
    List (PropName × ALocSet) → AHeap
  | []           => h
  | (p, L) :: ps => (h.weakSetObj {l} p L).weakSetObjs l ps

def AReg.weakSetDep (δ : AReg) (l : ALoc) (d : ALocSet) : AReg :=
  { δ with dep := fun l' => if l' = l then d ∪ δ.dep l' else δ.dep l' }

def AReg.setDep (δ : AReg) (l : ALoc) (d : ALocSet) : AReg :=
  { δ with dep := fun l' => if l' = l then d else δ.dep l' }

def ASto.upd (ρ : ASto) (x : Var) (L : ALocSet) : ASto :=
  fun y => if y = x then L else ρ y

def ASto.ofParams : List Var → List ALocSet → ASto
  | x :: xs, L :: Ls => (ASto.ofParams xs Ls).upd x L
  | _,       _       => ASto.bot

/-! ## Parameters of the analysis -/

class Abstract where
  litLocA : Val → ALoc
  allocA  : AHeap → Idx → ALoc
  opSemA  : BinOp → VSet → VSet → VSet

open Abstract

structure AbstractSpec [Abstract] : Prop where
  opSemA_mono : ∀ op V₁ V₁' V₂ V₂', V₁ ⊑ V₁' → V₂ ⊑ V₂' →
    (opSemA op V₁ V₂) ⊑ (opSemA op V₁' V₂')
  allocA_site : ∀ h h' κ, allocA h κ = allocA h' κ

/-- `⟦e⟧ρ̂` (Fig. B2). Total: an unbound variable evaluates to `∅`. -/
def aevalE [Abstract] (ρ : ASto) : Expr → ALocSet
  | .val v => {litLocA v}
  | .var x => ρ x

def aevalEs [Abstract] (ρ : ASto) : List Expr → List ALocSet
  | []      => []
  | e :: es => aevalE ρ e :: aevalEs ρ es

/-! ## Call candidates (§5.1, `IsCandidate`) -/

def Env.params (Γ : Env) (f : Fid) : List Var :=
  ((Γ f).map Prod.fst).getD []

def Env.body (Γ : Env) (f : Fid) : Stmt :=
  ((Γ f).map Prod.snd).getD .skip

/-- `f` is a candidate callee at a site whose callee expression abstracts to
    `L_f` and which passes `n` arguments. -/
def IsCandidate [Abstract] (Γ : Env) (h : AHeap) (L_f : ALocSet) (n : Nat)
    (f : Fid) : Prop :=
  ((h.valOf L_f).Mem (.fid f)) ∧ (Γ f).isSome ∧ (Γ.params f).length = n

structure EnvSpec (Γ : Env) : Prop where
  fin : ∃ fs : List Fid, ∀ f, (Γ f).isSome → f ∈ fs

/-! ## Abstract configurations -/

/-- `⟨ĥ, ρ̂, δ̂⟩`: what a labeling assigns to every automaton state. -/
structure AConf where
  heap : AHeap
  sto  : ASto
  reg  : AReg

def AConf.bot : AConf := ⟨AHeap.bot, ASto.bot, AReg.bot⟩

def AConf.Le (c₁ c₂ : AConf) : Prop :=
  c₁.heap ⊑ c₂.heap ∧ c₁.sto ⊑ c₂.sto ∧ c₁.reg ⊑ c₂.reg

instance : LE AConf := ⟨AConf.Le⟩

/-! ## Atomic per-statement effects (Fig. B6)

Every statement shape that allocates no automaton state of its own
(`skip`/`assign`/`binOp`/`objLit`/`setTaint`/`setSink`) or exactly one
`action` state consumed by a single edge (`lookupS`/`lookupD`/`updateS`/
`updateD`) contributes a *deterministic* transformation of the running
`AConf`. These are transcribed unchanged from the old `ABigStep`'s
corresponding rules (`CoreJsAbstractSemantics.lean`) — decision 2 of
`PROBLEMS.md`: the value-update math does not change, only how it is
attached, here directly as an edge's contribution function. -/

def AConf.doAssign [Abstract] (x : Var) (e : Expr) (c : AConf) : AConf :=
  { c with sto := c.sto.upd x (aevalE c.sto e) }

def AConf.doBinOp [Abstract] (x : Var) (κ : Idx) (op : BinOp) (e₁ e₂ : Expr)
    (c : AConf) : AConf :=
  let L₁ := aevalE c.sto e₁
  let L₂ := aevalE c.sto e₂
  let l   := allocA c.heap κ
  let V   := opSemA op (c.heap.valOf L₁) (c.heap.valOf L₂)
  { heap := c.heap.weakSetVal l V
    sto  := c.sto.upd x {l}
    reg  := c.reg.weakSetDep l (c.reg.depOf L₁ ∪ c.reg.depOf L₂ ∪ L₁ ∪ L₂) }

def AConf.doObjLit [Abstract] (x : Var) (κ : Idx) (fs : List (PropName × Expr))
    (c : AConf) : AConf :=
  let Ls := aevalEs c.sto (fs.map Prod.snd)
  let l   := allocA c.heap κ
  { heap := c.heap.weakSetObjs l ((fs.map Prod.fst).zip Ls)
    sto  := c.sto.upd x {l}
    reg  := c.reg.setDep l ∅ }

def AConf.doLookupS [Abstract] (x : Var) (e : Expr) (p : PropName) (c : AConf) :
    AConf :=
  { c with sto := c.sto.upd x (c.heap.objOf (aevalE c.sto e) p) }

def AConf.doLookupD [Abstract] (x : Var) (e₁ e₂ : Expr) (c : AConf) : AConf :=
  { c with sto :=
      c.sto.upd x (c.heap.objOfV (aevalE c.sto e₁) (c.heap.valOf (aevalE c.sto e₂))) }

def AConf.doUpdateS [Abstract] (e₁ : Expr) (p : PropName) (e₂ : Expr)
    (c : AConf) : AConf :=
  { c with heap := c.heap.weakSetObj (aevalE c.sto e₁) p (aevalE c.sto e₂) }

def AConf.doUpdateD [Abstract] (e₁ e₂ e₃ : Expr) (c : AConf) : AConf :=
  { c with heap :=
      c.heap.weakSetObjV (aevalE c.sto e₁) (c.heap.valOf (aevalE c.sto e₂)) (aevalE c.sto e₃) }

def AConf.doSetTaint [Abstract] (e : Expr) (c : AConf) : AConf :=
  { c with reg := { c.reg with ac := aevalE c.sto e ∪ c.reg.ac } }

def AConf.doSetSink [Abstract] (e : Expr) (c : AConf) : AConf :=
  { c with reg := { c.reg with sk := aevalE c.sto e ∪ c.reg.sk } }

/-! ## The automaton's edges (§4.3)

Three mutually recursive relations, parameterised by the function
environment `Γ` and indexed by the call string `cs` and the "processing
position" `(entry, pending)` — `entry` the automaton state processing resumed
from, `pending : AConf → AConf` the net effect of every flat statement
(`skip`/`assign`/.../`setSink`) since the last real edge, composed onto
whatever arrives at `entry`:

* `AExit Γ cs entry pending s x xpending` — processing `s` leaves `x` as one
  of the (possibly several) dangling *continuing* exits, itself to be resumed
  with transform `xpending`. `ret` contributes no `AExit` fact at all — a
  `ret` never continues (Decision 3 of `DESIGN_AND_PLAN.md`, decisions 3/8).
* `AEdge Γ cs entry pending s a b C` — processing `s` produces the graph edge
  `a → b` with contribution `C`.
* `ARet Γ cs entry pending s r rpending e` — processing `s` reaches a
  `ret e` at state `r`, with `rpending` the transform up to (but not
  including) evaluating `e`. Used only by `call`'s own processing to wire
  every reachable `ret` inside a candidate callee to that call's own
  continuation (`PROBLEMS.md` decision 4) — `ret` itself never emits an edge.

These are ordinary inductive `Prop`s, not a terminating computation: `call`'s
cases recurse into `Γ.body f` for whichever `f` is a candidate, exactly as
`ABigStep`'s old `callRet`/`callCont` did, which is well-formed for a
strictly positive inductive `Prop` without needing any termination measure
(`PROBLEMS.md` decision 1). -/

-- `IsCandidate` is an arbitrary `Prop` (it quantifies through `VSet.Mem`),
-- not decidable in general; the `if IsCandidate ... then ... else ...` in
-- `callEntry` below is only ever used to state a value, never executed, so a
-- classical instance is exactly right here.
attribute [local instance] Classical.propDecidable

mutual

inductive AExit [Abstract] (Γ : Env) :
    CallString → AState → (AConf → AConf) → Stmt → AState → (AConf → AConf) → Prop where
  | skip {cs entry pending} :
      AExit Γ cs entry pending .skip entry pending
  | assign {cs entry pending x e} :
      AExit Γ cs entry pending (.assign x e) entry (AConf.doAssign x e ∘ pending)
  | binOp {cs entry pending x κ op e₁ e₂} :
      AExit Γ cs entry pending (.binOp x κ op e₁ e₂) entry
        (AConf.doBinOp x κ op e₁ e₂ ∘ pending)
  | objLit {cs entry pending x κ fs} :
      AExit Γ cs entry pending (.objLit x κ fs) entry (AConf.doObjLit x κ fs ∘ pending)
  | setTaint {cs entry pending e} :
      AExit Γ cs entry pending (.setTaint e) entry (AConf.doSetTaint e ∘ pending)
  | setSink {cs entry pending e} :
      AExit Γ cs entry pending (.setSink e) entry (AConf.doSetSink e ∘ pending)
  | lookupS {cs entry pending x κ e p} :
      AExit Γ cs entry pending (.lookupS x κ e p) (.action cs κ) id
  | lookupD {cs entry pending x κ e₁ e₂} :
      AExit Γ cs entry pending (.lookupD x κ e₁ e₂) (.action cs κ) id
  | updateS {cs entry pending κ e₁ p e₂} :
      AExit Γ cs entry pending (.updateS κ e₁ p e₂) (.action cs κ) id
  | updateD {cs entry pending κ e₁ e₂ e₃} :
      AExit Γ cs entry pending (.updateD κ e₁ e₂ e₃) (.action cs κ) id
  | seq {cs entry pending s₁ s₂ x xpending y ypending} :
      AExit Γ cs entry pending s₁ x xpending →
      AExit Γ cs x xpending s₂ y ypending →
      AExit Γ cs entry pending (.seq s₁ s₂) y ypending
  | ifElse {cs entry pending κ e s₁ s₂} :
      AExit Γ cs entry pending (.ifElse κ e s₁ s₂) (.ifEnd cs κ) id
  | whileDo {cs entry pending κ e s} :
      AExit Γ cs entry pending (.whileDo κ e s) (.whileOut cs κ) id
  | call {cs entry pending x κ e es} :
      AExit Γ cs entry pending (.call x κ e es) (.cont cs κ) id

inductive AEdge [Abstract] (Γ : Env) :
    CallString → AState → (AConf → AConf) → Stmt → AState → AState → (AConf → AConf) → Prop where
  | lookupS {cs entry pending x κ e p} :
      AEdge Γ cs entry pending (.lookupS x κ e p) entry (.action cs κ)
        (AConf.doLookupS x e p ∘ pending)
  | lookupD {cs entry pending x κ e₁ e₂} :
      AEdge Γ cs entry pending (.lookupD x κ e₁ e₂) entry (.action cs κ)
        (AConf.doLookupD x e₁ e₂ ∘ pending)
  | updateS {cs entry pending κ e₁ p e₂} :
      AEdge Γ cs entry pending (.updateS κ e₁ p e₂) entry (.action cs κ)
        (AConf.doUpdateS e₁ p e₂ ∘ pending)
  | updateD {cs entry pending κ e₁ e₂ e₃} :
      AEdge Γ cs entry pending (.updateD κ e₁ e₂ e₃) entry (.action cs κ)
        (AConf.doUpdateD e₁ e₂ e₃ ∘ pending)
  | seqLeft {cs entry pending s₁ s₂ a b C} :
      AEdge Γ cs entry pending s₁ a b C →
      AEdge Γ cs entry pending (.seq s₁ s₂) a b C
  | seqRight {cs entry pending s₁ s₂ x xpending a b C} :
      AExit Γ cs entry pending s₁ x xpending →
      AEdge Γ cs x xpending s₂ a b C →
      AEdge Γ cs entry pending (.seq s₁ s₂) a b C
  | ifThen {cs entry pending κ e s₁ s₂} :
      AEdge Γ cs entry pending (.ifElse κ e s₁ s₂) entry (.ifThen cs κ) pending
  | ifElseB {cs entry pending κ e s₁ s₂} :
      AEdge Γ cs entry pending (.ifElse κ e s₁ s₂) entry (.ifElseB cs κ) pending
  | ifThenBody {cs entry pending κ e s₁ s₂ a b C} :
      AEdge Γ cs (.ifThen cs κ) id s₁ a b C →
      AEdge Γ cs entry pending (.ifElse κ e s₁ s₂) a b C
  | ifElseBBody {cs entry pending κ e s₁ s₂ a b C} :
      AEdge Γ cs (.ifElseB cs κ) id s₂ a b C →
      AEdge Γ cs entry pending (.ifElse κ e s₁ s₂) a b C
  | ifThenJoin {cs entry pending κ e s₁ s₂ x xpending} :
      AExit Γ cs (.ifThen cs κ) id s₁ x xpending →
      AEdge Γ cs entry pending (.ifElse κ e s₁ s₂) x (.ifEnd cs κ) xpending
  | ifElseBJoin {cs entry pending κ e s₁ s₂ x xpending} :
      AExit Γ cs (.ifElseB cs κ) id s₂ x xpending →
      AEdge Γ cs entry pending (.ifElse κ e s₁ s₂) x (.ifEnd cs κ) xpending
  | whileHeaderIn {cs entry pending κ e s} :
      AEdge Γ cs entry pending (.whileDo κ e s) entry (.whileIn cs κ) pending
  | whileHeaderOut {cs entry pending κ e s} :
      AEdge Γ cs entry pending (.whileDo κ e s) entry (.whileOut cs κ) pending
  | whileBody {cs entry pending κ e s a b C} :
      AEdge Γ cs (.whileIn cs κ) id s a b C →
      AEdge Γ cs entry pending (.whileDo κ e s) a b C
  | whileBack {cs entry pending κ e s x xpending} :
      AExit Γ cs (.whileIn cs κ) id s x xpending →
      AEdge Γ cs entry pending (.whileDo κ e s) x entry xpending
  /-- The call's own continuation state also always gets a pass-through edge
      directly from the call, binding `x` to `∅` and leaving everything else
      unchanged — `PROBLEMS.md` decision 3: without this, every caller-local
      variable but `x` would be lost at `cont`, and a call site with no live
      candidate would starve everything sequenced after it. -/
  | callPassThrough {cs entry pending x κ e es} :
      AEdge Γ cs entry pending (.call x κ e es) entry (.cont cs κ)
        (fun c => let v := pending c; { v with sto := v.sto.upd x ∅ })
  /-- Structural edge into every arity-matching candidate's entry, gated
      entirely on `IsCandidate` (`PROBLEMS.md` decision 5: the *whole*
      contribution collapses to `AConf.bot`, not just the argument binding,
      when this call site could not have resolved to `f` at this label). -/
  | callEntry {cs entry pending x κ e es f params body}
      (hf : Γ f = some (params, body)) (harity : params.length = es.length) :
      AEdge Γ cs entry pending (.call x κ e es) entry
        (.entry (targetCallString cs κ f))
        (fun c =>
          let v := pending c
          if IsCandidate Γ v.heap (aevalE v.sto e) es.length f then
            { heap := v.heap, sto := ASto.ofParams params (aevalEs v.sto es), reg := v.reg }
          else AConf.bot)
  /-- One edge per `ret` reachable inside a candidate callee's body, wired
      directly to this call's own continuation (`PROBLEMS.md` decision 4).
      No `IsCandidate` gating here (`DESIGN_AND_PLAN.md` decision 7): once
      inside a body producing a return, every continuation the call-string
      mechanism connects to is one that could have called it. The callee's
      local store never leaks into the caller's: only `x` is set, using
      `ASto.bot` everywhere else, so joining this into `cont` only ever
      touches the `x` slot. -/
  | callRet {cs entry pending x κ e es f params body r rpending e'}
      (hf : Γ f = some (params, body)) (harity : params.length = es.length) :
      ARet Γ (targetCallString cs κ f) (.entry (targetCallString cs κ f)) id
        body r rpending e' →
      AEdge Γ cs entry pending (.call x κ e es) r (.cont cs κ)
        (fun c =>
          let v := rpending c
          { heap := v.heap, sto := ASto.bot.upd x (aevalE v.sto e'), reg := v.reg })

inductive ARet [Abstract] (Γ : Env) :
    CallString → AState → (AConf → AConf) → Stmt → AState → (AConf → AConf) → Expr → Prop where
  | ret {cs entry pending e} :
      ARet Γ cs entry pending (.ret e) entry pending e
  | seqLeft {cs entry pending s₁ s₂ r rpending e} :
      ARet Γ cs entry pending s₁ r rpending e →
      ARet Γ cs entry pending (.seq s₁ s₂) r rpending e
  | seqRight {cs entry pending s₁ s₂ x xpending r rpending e} :
      AExit Γ cs entry pending s₁ x xpending →
      ARet Γ cs x xpending s₂ r rpending e →
      ARet Γ cs entry pending (.seq s₁ s₂) r rpending e
  | ifThen {cs entry pending κ e s₁ s₂ r rpending e'} :
      ARet Γ cs (.ifThen cs κ) id s₁ r rpending e' →
      ARet Γ cs entry pending (.ifElse κ e s₁ s₂) r rpending e'
  | ifElseB {cs entry pending κ e s₁ s₂ r rpending e'} :
      ARet Γ cs (.ifElseB cs κ) id s₂ r rpending e' →
      ARet Γ cs entry pending (.ifElse κ e s₁ s₂) r rpending e'
  | whileDo {cs entry pending κ e s r rpending e'} :
      ARet Γ cs (.whileIn cs κ) id s r rpending e' →
      ARet Γ cs entry pending (.whileDo κ e s) r rpending e'

end

/-! ## Labeling and validity (§4.4)

A labeling assigns an `AConf` to every automaton state. It is valid when
every edge's contribution, computed from its own source state's label, is
dominated by the target state's label — a direct generalisation of the old
per-statement weak/strong update rules and of the post-fixed-point condition
`[While]`/`[Call-Fix]` used to check, stated once over the whole reachable
state graph instead of function-by-function.

The graph is closed over every function reachable from the top-level program
`s₀`: not just `s₀`'s own edges (call string `[]`, entry state `entry []`),
but, for every function `f` and *every* well-formed call string `cs` (not
only the ones actually reachable — over-approximating here is harmless and
keeps this definition simple; a real execution only ever needs the reachable
ones, all of which are among these), the edges of `Γ.body f` processed from
`(entry cs, id)`. -/

def Labeling [Abstract] := AState → AConf

def Labeling.Valid [Abstract] (Γ : Env) (s₀ : Stmt) (L : Labeling) : Prop :=
  (∀ a b C, AEdge Γ [] (.entry []) id s₀ a b C → C (L a) ⊑ L b) ∧
  (∀ f params body cs, Γ f = some (params, body) → CallString.WF cs →
     ∀ a b C, AEdge Γ cs (.entry cs) id body a b C → C (L a) ⊑ L b)

/-- The top-level analysis result: `L` is a valid labeling for the program
    `(Γ, s₀)` starting from the default initial abstract state at the top
    level's own entry. This is the automaton counterpart of `SA`. -/
def AnalysisResult [Abstract] (Γ : Env) (s₀ : Stmt) (L : Labeling) : Prop :=
  Labeling.Valid Γ s₀ L ∧ L (.entry []) = AConf.bot

end CoreJS
