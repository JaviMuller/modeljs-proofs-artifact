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

/-- Abstract trace actions: the labels of the automaton's edges. They mirror
    the concrete `Act`, with every location widened to a set of abstract
    locations — except the callee position of `call`/`ret`, which is the
    single canonical location `litLocA (.fid f)` of the function called (the
    edge carrying the label is specific to one candidate `f`). `epsilon`
    labels structurally silent edges, which contribute nothing to a walk's
    trace. -/
inductive AAct where
  | lookup  (L₁ L₂ L₃ : ALocSet)
  | update  (L₁ L₂ L₃ : ALocSet)
  | call    (lf : ALoc) (Ls : List ALocSet)
  | ret     (lf : ALoc) (L : ALocSet)
  | epsilon

/-- The actions an edge label contributes to a walk's trace: none for
    `epsilon`, the action itself otherwise. -/
def AAct.visible : AAct → List AAct
  | .epsilon => []
  | a        => [a]

/-! ### Order (Def. B4) and join (Def. B5), restricted to the domains still
    needed. -/

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
  /-- A function's canonical location is reserved for it: no other literal
      (in particular no other function) shares it. This makes `f ↦ litLocA
      (.fid f)` one-to-one, which is what lets `AAct.call`/`.ret` name the
      callee by a single location. -/
  litLocA_fid : ∀ f v, litLocA (.fid f) = litLocA v → v = .fid f
  /-- No allocation site is abstracted to a function's canonical location, so
      nothing an allocation writes can reach it. -/
  allocA_fid : ∀ h κ f, allocA h κ ≠ litLocA (.fid f)

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

/-! ## Action labels of the heap-accessing statements

The abstract counterpart of the action each of `lookupS`/`lookupD`/
`updateS`/`updateD` emits concretely, computed from the configuration the
statement runs in, position by position as in the concrete rule (for
instance `[Static Property Lookup]` emits `lookup l₂ l₁ l_p` with `l₁` the
object, `l₂` the property's location). -/

def AConf.actLookupS [Abstract] (e : Expr) (p : PropName) (c : AConf) : AAct :=
  .lookup (c.heap.objOf (aevalE c.sto e) p) (aevalE c.sto e) {litLocA (.str p)}

def AConf.actLookupD [Abstract] (e₁ e₂ : Expr) (c : AConf) : AAct :=
  .lookup (c.heap.objOfV (aevalE c.sto e₁) (c.heap.valOf (aevalE c.sto e₂)))
    (aevalE c.sto e₁) (aevalE c.sto e₂)

def AConf.actUpdateS [Abstract] (e₁ : Expr) (p : PropName) (e₂ : Expr) (c : AConf) : AAct :=
  .update (aevalE c.sto e₁) {litLocA (.str p)} (aevalE c.sto e₂)

def AConf.actUpdateD [Abstract] (e₁ e₂ e₃ : Expr) (c : AConf) : AAct :=
  .update (aevalE c.sto e₁) (aevalE c.sto e₂) (aevalE c.sto e₃)

/-- `f` is a candidate callee of `e(es)` at configuration `c`. -/
def AConf.Calls [Abstract] (Γ : Env) (e : Expr) (n : Nat) (f : Fid) (c : AConf) : Prop :=
  IsCandidate Γ c.heap (aevalE c.sto e) n f

/-- A labeling assigns an `AConf` to every automaton state. -/
def Labeling := AState → AConf

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
* `AEdge Γ cs entry pending s a b C ℓ` — processing `s` produces the graph
  edge `a → b` with contribution `C` and action label `ℓ`. Both are read off
  a labeling `L`: `C L` is what the edge contributes to `L b`, and `ℓ L` is
  the action the edge performs — `some .epsilon` for a silent edge, `none`
  when the edge cannot be taken under `L` (a call edge whose candidate check
  fails). They take the whole labeling rather than only the source's label
  because a call's return edges start inside the callee but are gated on the
  *caller's* configuration at the call site.
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
    CallString → AState → (AConf → AConf) → Stmt → AState → AState →
      (Labeling → AConf) → (Labeling → Option AAct) → Prop where
  | lookupS {cs entry pending x κ e p} :
      AEdge Γ cs entry pending (.lookupS x κ e p) entry (.action cs κ)
        (fun L => AConf.doLookupS x e p (pending (L entry)))
        (fun L => some (AConf.actLookupS e p (pending (L entry))))
  | lookupD {cs entry pending x κ e₁ e₂} :
      AEdge Γ cs entry pending (.lookupD x κ e₁ e₂) entry (.action cs κ)
        (fun L => AConf.doLookupD x e₁ e₂ (pending (L entry)))
        (fun L => some (AConf.actLookupD e₁ e₂ (pending (L entry))))
  | updateS {cs entry pending κ e₁ p e₂} :
      AEdge Γ cs entry pending (.updateS κ e₁ p e₂) entry (.action cs κ)
        (fun L => AConf.doUpdateS e₁ p e₂ (pending (L entry)))
        (fun L => some (AConf.actUpdateS e₁ p e₂ (pending (L entry))))
  | updateD {cs entry pending κ e₁ e₂ e₃} :
      AEdge Γ cs entry pending (.updateD κ e₁ e₂ e₃) entry (.action cs κ)
        (fun L => AConf.doUpdateD e₁ e₂ e₃ (pending (L entry)))
        (fun L => some (AConf.actUpdateD e₁ e₂ e₃ (pending (L entry))))
  | seqLeft {cs entry pending s₁ s₂ a b C ℓ} :
      AEdge Γ cs entry pending s₁ a b C ℓ →
      AEdge Γ cs entry pending (.seq s₁ s₂) a b C ℓ
  | seqRight {cs entry pending s₁ s₂ x xpending a b C ℓ} :
      AExit Γ cs entry pending s₁ x xpending →
      AEdge Γ cs x xpending s₂ a b C ℓ →
      AEdge Γ cs entry pending (.seq s₁ s₂) a b C ℓ
  | ifThen {cs entry pending κ e s₁ s₂} :
      AEdge Γ cs entry pending (.ifElse κ e s₁ s₂) entry (.ifThen cs κ)
        (fun L => pending (L entry)) (fun _ => some .epsilon)
  | ifElseB {cs entry pending κ e s₁ s₂} :
      AEdge Γ cs entry pending (.ifElse κ e s₁ s₂) entry (.ifElseB cs κ)
        (fun L => pending (L entry)) (fun _ => some .epsilon)
  | ifThenBody {cs entry pending κ e s₁ s₂ a b C ℓ} :
      AEdge Γ cs (.ifThen cs κ) id s₁ a b C ℓ →
      AEdge Γ cs entry pending (.ifElse κ e s₁ s₂) a b C ℓ
  | ifElseBBody {cs entry pending κ e s₁ s₂ a b C ℓ} :
      AEdge Γ cs (.ifElseB cs κ) id s₂ a b C ℓ →
      AEdge Γ cs entry pending (.ifElse κ e s₁ s₂) a b C ℓ
  | ifThenJoin {cs entry pending κ e s₁ s₂ x xpending} :
      AExit Γ cs (.ifThen cs κ) id s₁ x xpending →
      AEdge Γ cs entry pending (.ifElse κ e s₁ s₂) x (.ifEnd cs κ)
        (fun L => xpending (L x)) (fun _ => some .epsilon)
  | ifElseBJoin {cs entry pending κ e s₁ s₂ x xpending} :
      AExit Γ cs (.ifElseB cs κ) id s₂ x xpending →
      AEdge Γ cs entry pending (.ifElse κ e s₁ s₂) x (.ifEnd cs κ)
        (fun L => xpending (L x)) (fun _ => some .epsilon)
  | whileHeaderIn {cs entry pending κ e s} :
      AEdge Γ cs entry pending (.whileDo κ e s) entry (.whileIn cs κ)
        (fun L => pending (L entry)) (fun _ => some .epsilon)
  | whileHeaderOut {cs entry pending κ e s} :
      AEdge Γ cs entry pending (.whileDo κ e s) entry (.whileOut cs κ)
        (fun L => pending (L entry)) (fun _ => some .epsilon)
  | whileBody {cs entry pending κ e s a b C ℓ} :
      AEdge Γ cs (.whileIn cs κ) id s a b C ℓ →
      AEdge Γ cs entry pending (.whileDo κ e s) a b C ℓ
  /-- Every subsequent iteration re-checks the guard exactly the same way
      the first one did — fanning out again into `whileIn`/`whileOut`, this
      time from the previous iteration's own exit `x` with its own
      accumulated `xpending`, rather than looping back through `entry`'s
      *original* `pending` a second time. `PROBLEMS.md` decision 8: routing
      the back-edge through `entry` (matching `DESIGN_AND_PLAN.md`'s literal
      table, "epsilon back to the header") turned out to need `L entry ⊑
      pending (L entry)` for soundness — a fact nothing guarantees — so the
      back-edge fans out directly instead, exactly mirroring `entry`'s own
      first-arrival fan-out (`whileHeaderIn`/`.whileHeaderOut` above) but
      sourced at `x` with `xpending` in place of `entry` with `pending`. -/
  | whileBackIn {cs entry pending κ e s x xpending} :
      AExit Γ cs (.whileIn cs κ) id s x xpending →
      AEdge Γ cs entry pending (.whileDo κ e s) x (.whileIn cs κ)
        (fun L => xpending (L x)) (fun _ => some .epsilon)
  | whileBackOut {cs entry pending κ e s x xpending} :
      AExit Γ cs (.whileIn cs κ) id s x xpending →
      AEdge Γ cs entry pending (.whileDo κ e s) x (.whileOut cs κ)
        (fun L => xpending (L x)) (fun _ => some .epsilon)
  /-- The call's own continuation state also always gets a pass-through edge
      directly from the call, binding `x` to `∅` and leaving everything else
      unchanged — `PROBLEMS.md` decision 3: without this, every caller-local
      variable but `x` would be lost at `cont`, and a call site with no live
      candidate would starve everything sequenced after it. -/
  | callPassThrough {cs entry pending x κ e es} :
      AEdge Γ cs entry pending (.call x κ e es) entry (.cont cs κ)
        (fun L => let v := pending (L entry); { v with sto := v.sto.upd x ∅ })
        (fun _ => some .epsilon)
  /-- Structural edge into every arity-matching candidate's entry, gated
      entirely on `IsCandidate` (`PROBLEMS.md` decision 5: the *whole*
      contribution collapses to `AConf.bot`, not just the argument binding,
      when this call site could not have resolved to `f` at this label; the
      label is then `none`, so no walk can take the edge either). -/
  | callEntry {cs entry pending x κ e es f params body}
      (hf : Γ f = some (params, body)) (harity : params.length = es.length) :
      AEdge Γ cs entry pending (.call x κ e es) entry
        (.entry (targetCallString cs κ f))
        (fun L =>
          let v := pending (L entry)
          if v.Calls Γ e es.length f then
            { heap := v.heap, sto := ASto.ofParams params (aevalEs v.sto es), reg := v.reg }
          else AConf.bot)
        (fun L =>
          let v := pending (L entry)
          if v.Calls Γ e es.length f then
            some (.call (litLocA (.fid f)) (aevalEs v.sto es))
          else none)
  /-- One edge per `ret` reachable inside a candidate callee's body, wired
      directly to this call's own continuation (`PROBLEMS.md` decision 4).
      Gated on the same candidate check as `callEntry`, evaluated at the
      *caller's* configuration at the call site: a call site that cannot
      have called `f` receives nothing from `f`'s returns, even though it
      shares `f`'s entry with call sites that can. The callee's local store
      never leaks into the caller's: only `x` is set, using `ASto.bot`
      everywhere else, so joining this into `cont` only ever touches the `x`
      slot. -/
  | callRet {cs entry pending x κ e es f params body r rpending e'}
      (hf : Γ f = some (params, body)) (harity : params.length = es.length) :
      ARet Γ (targetCallString cs κ f) (.entry (targetCallString cs κ f)) id
        body r rpending e' →
      AEdge Γ cs entry pending (.call x κ e es) r (.cont cs κ)
        (fun L =>
          if (pending (L entry)).Calls Γ e es.length f then
            let w := rpending (L r)
            { heap := w.heap, sto := ASto.bot.upd x (aevalE w.sto e'), reg := w.reg }
          else AConf.bot)
        (fun L =>
          if (pending (L entry)).Calls Γ e es.length f then
            some (.ret (litLocA (.fid f)) (aevalE (rpending (L r)).sto e'))
          else none)
  /-- A candidate callee whose body can *fall through* (reach any
      `.cont`-outcome exit, structurally: any `AExit` fact of its body)
      implicitly returns `undefined` (matching the concrete `[Function Call],
      implicit return` rule, `CoreJsSemantics.lean`'s `callCont`) — this is a
      genuine second source of contribution to `cont`, independent of
      `callRet`, surfaced only once the soundness proof was attempted (see
      `PROBLEMS.md` decision 7): without it the model is unsound for any
      program where a callee can fall through, since `cont`'s label would
      then omit `undefined` from `x`'s bindings whenever a live candidate's
      body has no explicit `return` on some path. Gated like `callRet`. -/
  | callImplicitRet {cs entry pending x κ e es f params body y ypending}
      (hf : Γ f = some (params, body)) (harity : params.length = es.length) :
      AExit Γ (targetCallString cs κ f) (.entry (targetCallString cs κ f)) id
        body y ypending →
      AEdge Γ cs entry pending (.call x κ e es) y (.cont cs κ)
        (fun L =>
          if (pending (L entry)).Calls Γ e es.length f then
            let w := ypending (L y)
            { heap := w.heap, sto := ASto.bot.upd x {litLocA .undef}, reg := w.reg }
          else AConf.bot)
        (fun L =>
          if (pending (L entry)).Calls Γ e es.length f then
            some (.ret (litLocA (.fid f)) {litLocA .undef})
          else none)

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

/-! ## The automaton's graph, labeling validity

The graph is closed over every function reachable from the top-level program
`s₀`: not just `s₀`'s own edges (call string `[]`, entry state `entry []`),
but, for every function `f` and *every* well-formed call string `cs` (not
only the ones actually reachable — over-approximating here is harmless and
keeps this definition simple; a real execution only ever needs the reachable
ones, all of which are among these), the edges of `Γ.body f` processed from
`(entry cs, id)`.

A labeling is valid when every edge's contribution is dominated by its
target state's label: stated once over the whole graph, this is the
post-fixed-point condition a loop or a recursive function would otherwise
need separately. -/

inductive AGraph [Abstract] (Γ : Env) (s₀ : Stmt) :
    AState → AState → (Labeling → AConf) → (Labeling → Option AAct) → Prop where
  | top {a b C ℓ} :
      AEdge Γ [] (.entry []) id s₀ a b C ℓ → AGraph Γ s₀ a b C ℓ
  | body {f params body cs a b C ℓ} :
      Γ f = some (params, body) → CallString.WF cs →
      AEdge Γ cs (.entry cs) id body a b C ℓ → AGraph Γ s₀ a b C ℓ

def Labeling.Valid [Abstract] (Γ : Env) (s₀ : Stmt) (L : Labeling) : Prop :=
  ∀ a b C ℓ, AGraph Γ s₀ a b C ℓ → C L ⊑ L b

/-- The top-level analysis result: `L` is a valid labeling for the program
    `(Γ, s₀)` starting from the default initial abstract state at the top
    level's own entry. -/
def AnalysisResult [Abstract] (Γ : Env) (s₀ : Stmt) (L : Labeling) : Prop :=
  Labeling.Valid Γ s₀ L ∧ L (.entry []) = AConf.bot

/-! ## Properties of the accumulated transforms

`pending`/`xpending`/`rpending` are only ever built from `id` by
post-composing atomic effects, so any property of transforms closed under
those operations holds of every one of them. -/

/-- `Q` holds of `id` and survives post-composition with every atomic effect
    of a statement that allocates no automaton state. -/
structure PendingClosed [Abstract] (Q : (AConf → AConf) → Prop) : Prop where
  id       : Q id
  assign   : ∀ {f} x e, Q f → Q (AConf.doAssign x e ∘ f)
  binOp    : ∀ {f} x κ op e₁ e₂, Q f → Q (AConf.doBinOp x κ op e₁ e₂ ∘ f)
  objLit   : ∀ {f} x κ fs, Q f → Q (AConf.doObjLit x κ fs ∘ f)
  setTaint : ∀ {f} e, Q f → Q (AConf.doSetTaint e ∘ f)
  setSink  : ∀ {f} e, Q f → Q (AConf.doSetSink e ∘ f)

mutual

theorem AExit.closed [Abstract] {Γ : Env} {Q : (AConf → AConf) → Prop}
    (hQ : PendingClosed Q) : ∀ {cs entry pending s x xpending},
    AExit Γ cs entry pending s x xpending → Q pending → Q xpending
  | _, _, _, _, _, _, .skip, h => h
  | _, _, _, _, _, _, .assign, h => hQ.assign _ _ h
  | _, _, _, _, _, _, .binOp, h => hQ.binOp _ _ _ _ _ h
  | _, _, _, _, _, _, .objLit, h => hQ.objLit _ _ _ h
  | _, _, _, _, _, _, .setTaint, h => hQ.setTaint _ h
  | _, _, _, _, _, _, .setSink, h => hQ.setSink _ h
  | _, _, _, _, _, _, .lookupS, _ => hQ.id
  | _, _, _, _, _, _, .lookupD, _ => hQ.id
  | _, _, _, _, _, _, .updateS, _ => hQ.id
  | _, _, _, _, _, _, .updateD, _ => hQ.id
  | _, _, _, _, _, _, .seq h₁ h₂, h => AExit.closed hQ h₂ (AExit.closed hQ h₁ h)
  | _, _, _, _, _, _, .ifElse, _ => hQ.id
  | _, _, _, _, _, _, .whileDo, _ => hQ.id
  | _, _, _, _, _, _, .call, _ => hQ.id

theorem ARet.closed [Abstract] {Γ : Env} {Q : (AConf → AConf) → Prop}
    (hQ : PendingClosed Q) : ∀ {cs entry pending s r rpending e},
    ARet Γ cs entry pending s r rpending e → Q pending → Q rpending
  | _, _, _, _, _, _, _, .ret, h => h
  | _, _, _, _, _, _, _, .seqLeft h₁, h => ARet.closed hQ h₁ h
  | _, _, _, _, _, _, _, .seqRight h₁ h₂, h => ARet.closed hQ h₂ (AExit.closed hQ h₁ h)
  | _, _, _, _, _, _, _, .ifThen h₁, _ => ARet.closed hQ h₁ hQ.id
  | _, _, _, _, _, _, _, .ifElseB h₁, _ => ARet.closed hQ h₁ hQ.id
  | _, _, _, _, _, _, _, .whileDo h₁, _ => ARet.closed hQ h₁ hQ.id

end

/-! ## Functions' canonical locations hold only themselves

The abstract counterpart of "a function's location holds that function": no
edge ever writes anything but `.fid f` into `litLocA (.fid f)`. Stated as a
preservation property of every edge (`AGraph.fidReserved`) rather than as a
further conjunct of `Labeling.Valid`, so that validity stays the plain
post-fixed-point condition over the edges; the least analysis result
(`CoreJsAutomatonTotality.lean`) is shown to satisfy it. -/

/-- The value set at each function's canonical location contains at most that
    function. -/
def AConf.FidReserved [Abstract] (c : AConf) : Prop :=
  ∀ f v, (c.heap.val (litLocA (.fid f))).Mem v → v = .fid f

theorem AConf.FidReserved.bot [Abstract] : AConf.bot.FidReserved :=
  fun _ _ h => h.elim

theorem AHeap.weakSetObjs_val (h : AHeap) (l : ALoc) :
    ∀ ps, (h.weakSetObjs l ps).val = h.val
  | []          => rfl
  | (_, _) :: ps => AHeap.weakSetObjs_val _ l ps

theorem AConf.FidReserved.pendingClosed [Abstract] (aspec : AbstractSpec) :
    PendingClosed (fun g => ∀ c, AConf.FidReserved c → AConf.FidReserved (g c)) where
  id := fun _ h => h
  assign := fun _ _ hf c hc => hf c hc
  binOp := fun {g} x κ op e₁ e₂ hf c hc f v hv => by
    have hne : litLocA (.fid f) ≠ allocA (g c).heap κ := fun h => aspec.allocA_fid _ _ _ h.symm
    simp only [Function.comp, AConf.doBinOp, AHeap.weakSetVal] at hv
    rw [if_neg hne] at hv
    exact hf c hc f v hv
  objLit := fun x κ fs hf c hc f v hv => by
    simp only [Function.comp, AConf.doObjLit, AHeap.weakSetObjs_val] at hv
    exact hf c hc f v hv
  setTaint := fun _ hf c hc => hf c hc
  setSink := fun _ hf c hc => hf c hc

/-- Every edge's contribution, computed from a labeling all of whose labels
    reserve functions' locations, reserves them too. -/
theorem AEdge.fidReserved [Abstract] (aspec : AbstractSpec) {Γ : Env} {L : Labeling}
    (hL : ∀ st, (L st).FidReserved) :
    ∀ {cs entry pending s a b C ℓ}, AEdge Γ cs entry pending s a b C ℓ →
      (∀ c, AConf.FidReserved c → AConf.FidReserved (pending c)) → (C L).FidReserved
  | _, _, _, _, _, _, _, _, .lookupS, hp => hp _ (hL _)
  | _, _, _, _, _, _, _, _, .lookupD, hp => hp _ (hL _)
  | _, _, _, _, _, _, _, _, .updateS, hp => hp _ (hL _)
  | _, _, _, _, _, _, _, _, .updateD, hp => hp _ (hL _)
  | _, _, _, _, _, _, _, _, .seqLeft h₁, hp => AEdge.fidReserved aspec hL h₁ hp
  | _, _, _, _, _, _, _, _, .seqRight hx h₂, hp =>
      AEdge.fidReserved aspec hL h₂ (AExit.closed (AConf.FidReserved.pendingClosed aspec) hx hp)
  | _, _, _, _, _, _, _, _, .ifThen, hp => hp _ (hL _)
  | _, _, _, _, _, _, _, _, .ifElseB, hp => hp _ (hL _)
  | _, _, _, _, _, _, _, _, .ifThenBody h₁, _ => AEdge.fidReserved aspec hL h₁ (fun _ h => h)
  | _, _, _, _, _, _, _, _, .ifElseBBody h₁, _ => AEdge.fidReserved aspec hL h₁ (fun _ h => h)
  | _, _, _, _, _, _, _, _, .ifThenJoin hx, _ =>
      AExit.closed (AConf.FidReserved.pendingClosed aspec) hx (fun _ h => h) _ (hL _)
  | _, _, _, _, _, _, _, _, .ifElseBJoin hx, _ =>
      AExit.closed (AConf.FidReserved.pendingClosed aspec) hx (fun _ h => h) _ (hL _)
  | _, _, _, _, _, _, _, _, .whileHeaderIn, hp => hp _ (hL _)
  | _, _, _, _, _, _, _, _, .whileHeaderOut, hp => hp _ (hL _)
  | _, _, _, _, _, _, _, _, .whileBody h₁, _ => AEdge.fidReserved aspec hL h₁ (fun _ h => h)
  | _, _, _, _, _, _, _, _, .whileBackIn hx, _ =>
      AExit.closed (AConf.FidReserved.pendingClosed aspec) hx (fun _ h => h) _ (hL _)
  | _, _, _, _, _, _, _, _, .whileBackOut hx, _ =>
      AExit.closed (AConf.FidReserved.pendingClosed aspec) hx (fun _ h => h) _ (hL _)
  | _, _, _, _, _, _, _, _, .callPassThrough, hp => hp _ (hL _)
  | _, _, _, _, _, _, _, _, .callEntry _ _, hp => by
      dsimp only
      split
      · exact hp _ (hL _)
      · exact AConf.FidReserved.bot
  | _, _, _, _, _, _, _, _, .callRet _ _ hr, _ => by
      dsimp only
      split
      · exact ARet.closed (AConf.FidReserved.pendingClosed aspec) hr (fun _ h => h) _ (hL _)
      · exact AConf.FidReserved.bot
  | _, _, _, _, _, _, _, _, .callImplicitRet _ _ hy, _ => by
      dsimp only
      split
      · exact AExit.closed (AConf.FidReserved.pendingClosed aspec) hy (fun _ h => h) _ (hL _)
      · exact AConf.FidReserved.bot

theorem AGraph.fidReserved [Abstract] (aspec : AbstractSpec) {Γ : Env} {s₀ : Stmt}
    {L : Labeling} (hL : ∀ st, (L st).FidReserved) {a b C ℓ}
    (he : AGraph Γ s₀ a b C ℓ) : (C L).FidReserved := by
  cases he with
  | top h => exact AEdge.fidReserved aspec hL h (fun _ h => h)
  | body _ _ h => exact AEdge.fidReserved aspec hL h (fun _ h => h)

end CoreJS
