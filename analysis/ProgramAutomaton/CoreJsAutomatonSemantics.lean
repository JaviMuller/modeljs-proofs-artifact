/-
  # Core JavaScript — Automaton Semantics

  The abstract domains of the analysis, the automaton's edges over the states
  of `CoreJsAutomatonSyntax.lean`, and what it means for a labeling (an
  abstract configuration at every state) to be valid:

  * abstract locations, value sets, heaps, stores and taint registers, their
    order and join, and the parameters of the analysis (`Abstract`,
    `AbstractSpec`);
  * abstract trace actions (`AAct`), the labels of the edges;
  * the per-statement effects on abstract configurations;
  * the edge relations `AExit`/`AEdge`/`ARet`, the whole graph `AGraph`,
    labelings and their validity, analysis results, and walks (`AWalk`);
  * the invariant that functions' canonical locations hold only those
    functions, preserved by every edge.

  Control flow is purely structural: whether a statement returned or
  continued is a matter of which states and edges exist, never a value
  carried on a result. A branch that returns simply has no edge into what
  follows it.

  Plain Lean 4 — no Mathlib required.
-/

import ProgramAutomaton.CoreJsAutomatonSyntax
import CoreJS.CoreJsSemantics

namespace CoreJS

/-! ## Abstract locations and location sets

Nothing below depends on the representation of abstract locations. -/

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

/-! ## Abstract heap, store and taint register -/

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

/-! ### Order and join -/

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

/-! ## Lifting the heap/register to sets of locations -/

def AHeap.valOf (h : AHeap) (L : ALocSet) : VSet :=
  .vals (fun v => ∃ l, L l ∧ (h.val l).Mem v)

def AHeap.objOf (h : AHeap) (L : ALocSet) (p : PropName) : ALocSet :=
  fun l' => ∃ l, L l ∧ h.obj l p l'

/-- `V` contains a value that may denote the property name `q` as a key
    (`Val.KeyOf`). -/
def VSet.HasKey (V : VSet) (q : PropName) : Prop := ∃ v, V.Mem v ∧ v.KeyOf q

def AHeap.objOfV (h : AHeap) (L : ALocSet) (V : VSet) : ALocSet :=
  fun l' => ∃ l p, L l ∧ V.HasKey p ∧ h.obj l p l'

def AReg.depOf (δ : AReg) (L : ALocSet) : ALocSet :=
  fun l' => ∃ l, L l ∧ δ.dep l l'

/-! ## Abstract updates

All heap/register updates are weak (they join into what is there): one
abstract location stands for every concrete location allocated at the sites
it abstracts, so an update of one of them must not erase the others. -/

/-- Some object reference: the value set an object literal stores at its
    abstract location. -/
def VSet.refs : VSet := .vals fun v => ∃ l, v = .loc l

def AHeap.weakSetVal (h : AHeap) (l : ALoc) (V : VSet) : AHeap :=
  { h with val := fun l' => if l' = l then VSet.join V (h.val l') else h.val l' }

def AHeap.weakSetObj (h : AHeap) (L : ALocSet) (p : PropName) (L' : ALocSet) :
    AHeap :=
  { h with obj := fun l q l' => h.obj l q l' ∨ (L l ∧ q = p ∧ L' l') }

def AHeap.weakSetObjV (h : AHeap) (L : ALocSet) (V : VSet) (L' : ALocSet) :
    AHeap :=
  { h with obj := fun l q l' => h.obj l q l' ∨ (L l ∧ V.HasKey q ∧ L' l') }

def AHeap.weakSetObjs (h : AHeap) (l : ALoc) :
    List (PropName × ALocSet) → AHeap
  | []           => h
  | (p, L) :: ps => (h.weakSetObj {l} p L).weakSetObjs l ps

def AReg.weakSetDep (δ : AReg) (l : ALoc) (d : ALocSet) : AReg :=
  { δ with dep := fun l' => if l' = l then d ∪ δ.dep l' else δ.dep l' }

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

/-- `⟦e⟧ρ̂`. Total: an unbound variable evaluates to `∅`. -/
def aevalE [Abstract] (ρ : ASto) : Expr → ALocSet
  | .val v => {litLocA v}
  | .var x => ρ x

def aevalEs [Abstract] (ρ : ASto) : List Expr → List ALocSet
  | []      => []
  | e :: es => aevalE ρ e :: aevalEs ρ es

/-! ## Call candidates -/

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

/-! ## Atomic per-statement effects

Every statement shape that allocates no automaton state of its own
(`skip`/`assign`/`binOp`/`objLit`/`setTaint`/`setSink`) or exactly one
`action` state consumed by a single edge (`lookupS`/`lookupD`/`updateS`/
`updateD`) contributes a *deterministic* transformation of the running
`AConf`, attached to the edges as (part of) their contribution. -/

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

/-- Object initialisation. Concretely the new object's dependencies are reset
    to `∅`; abstractly this is a weak update, i.e. no change. A strong update
    `setDep l ∅` would erase the dependencies of every *other* concrete
    location the abstract location `l` stands for — in particular of one a
    `binOp` allocated, whenever the two sites share an abstract location. -/
def AConf.doObjLit [Abstract] (x : Var) (κ : Idx) (fs : List (PropName × Expr))
    (c : AConf) : AConf :=
  let Ls := aevalEs c.sto (fs.map Prod.snd)
  let l   := allocA c.heap κ
  { heap := (c.heap.weakSetObjs l (("__proto__", {litLocA .proto}) :: (fs.map Prod.fst).zip Ls)).weakSetVal
      l VSet.refs
    sto  := c.sto.upd x {l}
    reg  := c.reg }

/-- What a static lookup of `p` on objects `L` may return: an own property, or,
    when the own property is missing, `Object.prototype`'s (`litLocA .proto`),
    or, when that is missing too, `undefined`. The abstract heap only records
    which properties an object *may* have, never which it must, so a lookup
    can never be known to hit, and all three are always included. -/
def AHeap.lookupS [Abstract] (h : AHeap) (L : ALocSet) (p : PropName) : ALocSet :=
  h.objOf L p ∪ h.objOf {litLocA .proto} p ∪ {litLocA .undef}

/-- The same for a dynamic lookup with keys `V`. -/
def AHeap.lookupD [Abstract] (h : AHeap) (L : ALocSet) (V : VSet) : ALocSet :=
  h.objOfV L V ∪ h.objOfV {litLocA .proto} V ∪ {litLocA .undef}

def AConf.doLookupS [Abstract] (x : Var) (e : Expr) (p : PropName) (c : AConf) :
    AConf :=
  { c with sto := c.sto.upd x (c.heap.lookupS (aevalE c.sto e) p) }

def AConf.doLookupD [Abstract] (x : Var) (e₁ e₂ : Expr) (c : AConf) : AConf :=
  { c with sto :=
      c.sto.upd x (c.heap.lookupD (aevalE c.sto e₁) (c.heap.valOf (aevalE c.sto e₂))) }

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
  .lookup (c.heap.lookupS (aevalE c.sto e) p) (aevalE c.sto e) {litLocA (.str p)}

def AConf.actLookupD [Abstract] (e₁ e₂ : Expr) (c : AConf) : AAct :=
  .lookup (c.heap.lookupD (aevalE c.sto e₁) (c.heap.valOf (aevalE c.sto e₂)))
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

/-! ## The automaton's edges

Three relations, parameterised by the function environment `Γ` and indexed
by the call string `cs` and the "processing position" `(entry, pending)` —
`entry` the automaton state processing resumed from, `pending : AConf → AConf`
the net effect of every flat statement (`skip`/`assign`/.../`setSink`) since
the last real edge, composed onto whatever arrives at `entry`. They are
layered, not mutually recursive: `AExit` refers only to itself, `ARet` to
itself and `AExit`, `AEdge` to all three.

* `AExit Γ cs entry pending s x xpending` — when processing `s` finishes
  normally, processing resumes at state `x` with transform `xpending`. It
  produces no edges. Every statement shape has at most one case, so there is
  at most one exit: a structured statement exits at its join state (`ifEnd`,
  `whileOut`, `cont`) whether or not anything reaches it. `ret` contributes
  no `AExit` fact at all — a `ret` never continues.
* `ARet Γ cs entry pending s r rpending e` — processing `s` reaches a
  `ret e` at state `r`, with `rpending` the transform up to (but not
  including) evaluating `e`. Used only by `call`'s own processing to wire
  every reachable `ret` inside a candidate callee to that call's own
  continuation: the call knows the variable to bind and the callee's call
  string, whereas a `ret` does not know which call sites reach it. `ret`
  itself never emits an edge.
* `AEdge Γ cs entry pending s a b C ℓ` — processing `s` produces the graph
  edge `a → b` with contribution `C` and action label `ℓ`. Both are read off
  a labeling `L`: `C L` is what the edge contributes to `L b`, and `ℓ L` is
  the action the edge performs — `some .epsilon` for a silent edge, `none`
  when the edge cannot be taken under `L` (a call edge whose candidate check
  fails). They take the whole labeling rather than only the source's label
  because a call's return edges start inside the callee but are gated on the
  *caller's* configuration at the call site.

All three are structurally recursive over the statement: `AEdge` never
produces the edges *inside* a callee's body. A call's return edges only
locate the callee's `ret`s and exits, through `ARet`/`AExit` premises over
that body; the body's own edges come from `AGraph.body` below. They are
stated as inductive `Prop`s for readability; nothing needs the edge set to
be computable, only to be well defined. -/

-- `AConf.Calls` is an arbitrary `Prop` (it quantifies through `VSet.Mem`),
-- not decidable in general; the `if … then … else …` in the call edges below
-- is only ever used to state a value, never executed, so a classical
-- instance is exactly right here.
attribute [local instance] Classical.propDecidable

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
      accumulated `xpending`, mirroring `entry`'s first-arrival fan-out
      (`whileHeaderIn`/`.whileHeaderOut`). Looping back to `entry` instead
      would send every later iteration through `entry`'s *original*
      `pending` again, which is sound only if `L entry ⊑ pending (L entry)`
      — nothing guarantees that when flat statements precede the loop. -/
  | whileBackIn {cs entry pending κ e s x xpending} :
      AExit Γ cs (.whileIn cs κ) id s x xpending →
      AEdge Γ cs entry pending (.whileDo κ e s) x (.whileIn cs κ)
        (fun L => xpending (L x)) (fun _ => some .epsilon)
  | whileBackOut {cs entry pending κ e s x xpending} :
      AExit Γ cs (.whileIn cs κ) id s x xpending →
      AEdge Γ cs entry pending (.whileDo κ e s) x (.whileOut cs κ)
        (fun L => xpending (L x)) (fun _ => some .epsilon)
  /-- The call's own continuation state also always gets a pass-through
      contribution directly from the call, binding `x` to `∅` and leaving
      everything else unchanged. Without it, every caller-local variable but
      `x` would be lost at `cont` (the return edges carry only `x`), and a
      call site with no live candidate would starve the labels of everything
      sequenced after it.

      It only feeds the labeling: its label is `none`, so no walk takes it.
      As a silent edge it would let a walk skip a call altogether — no `call`
      action, no callee actions — while reaching a `cont` whose label
      includes the callee's return value, e.g. a trace in which a sanitizer
      was never called. A walk through a call goes `callEntry` → the callee's
      body → `callRet`/`callImplicitRet`, as every concrete run does. -/
  | callPassThrough {cs entry pending x κ e es} :
      AEdge Γ cs entry pending (.call x κ e es) entry (.cont cs κ)
        (fun L => let v := pending (L entry); { v with sto := v.sto.upd x ∅ })
        (fun _ => none)
  /-- Structural edge into every arity-matching candidate's entry, gated
      entirely on the candidate check: the *whole* contribution collapses to
      `AConf.bot`, not just the argument binding, when this call site could
      not have resolved to `f`, since nothing about such a call should reach
      `f`'s entry. The label is then `none`, so no walk can take the edge
      either. -/
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
      directly to this call's own continuation. Gated on the same candidate check as `callEntry`, evaluated at the
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
      implicit return` rule, `CoreJsSemantics.lean`'s `callCont`) — a second
      source of contribution to `cont`, independent of `callRet`. Without it
      `cont`'s label would omit `undefined` from `x`'s bindings whenever a
      live candidate's body has no explicit `return` on some path. Gated like
      `callRet`. -/
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


/-! ## The automaton's graph, labeling validity

The graph has two kinds of roots. `top`: `s₀`'s own edges, processed under
call string `[]` from `(entry [], id)`. `body`: the edges of a function `f`'s
body, processed under an *instance* `cs` of `f` from `(entry cs, id)`. An
instance is a call string that ends with an occurrence of `f` — every target
of a call to `f` does (`targetCallString_ends`) — and that some edge of the
graph enters. So instances grow outwards from `s₀`'s call sites, and the
graph is the part of the automaton syntactically reachable from `entry []`.
It does not depend on any labeling: an instance at a call site that cannot
actually call `f` is still in, its entry and return edges gated shut.

Without the two conditions, `f`'s body would also hang off `entry []` (a walk
from the top-level entry could run it with no call), off other functions'
entries, and off call strings for every site index, making the graph
infinite.

A labeling is valid when every edge's contribution is dominated by its
target state's label: stated once over the whole graph, this is the
post-fixed-point condition a loop or a recursive function would otherwise
need separately. -/

inductive AGraph [Abstract] (Γ : Env) (s₀ : Stmt) :
    AState → AState → (Labeling → AConf) → (Labeling → Option AAct) → Prop where
  | top {a b C ℓ} :
      AEdge Γ [] (.entry []) id s₀ a b C ℓ → AGraph Γ s₀ a b C ℓ
  | body {f params body cs a' C' ℓ' a b C ℓ} :
      Γ f = some (params, body) → CallString.WF cs →
      (∃ cs' site, cs = cs' ++ [(site, f)]) →
      AGraph Γ s₀ a' (.entry cs) C' ℓ' →
      AEdge Γ cs (.entry cs) id body a b C ℓ → AGraph Γ s₀ a b C ℓ

def Labeling.Valid [Abstract] (Γ : Env) (s₀ : Stmt) (L : Labeling) : Prop :=
  ∀ a b C ℓ, AGraph Γ s₀ a b C ℓ → C L ⊑ L b

/-- A literal a run of `s` may start with: `undefined`, a literal of `s`, or a
    literal of the body of a function defined in `Γ`. -/
def InitLit (Γ : Env) (s : Stmt) (v : Val) : Prop :=
  v ∈ Val.undef :: s.lits ∨ ∃ f params body, Γ f = some (params, body) ∧ v ∈ body.lits

/-- The abstract counterpart of `Heap.init Γ fs s`: each literal `v` of `s`,
    of every function body of `Γ`, and `undefined`, at `litLocA v`; no object
    has any property. Stated as a predicate, it covers every function of `Γ`
    without needing them listed, so it covers `Heap.init Γ fs s` for every
    `fs`. -/
def AHeap.init [Abstract] (Γ : Env) (s : Stmt) : AHeap where
  obj := fun _ _ => ∅
  val := fun a => .vals (fun v => InitLit Γ s v ∧ litLocA v = a)

/-- The abstract counterpart of `Conf.init Γ fs s`. -/
def AConf.init [Abstract] (Γ : Env) (s : Stmt) : AConf := ⟨AHeap.init Γ s, ASto.bot, AReg.bot⟩

/-- The top-level analysis result: `L` is a valid labeling for the program
    `(Γ, s₀)` whose top-level entry covers the initial configuration. -/
def AnalysisResult [Abstract] (Γ : Env) (s₀ : Stmt) (L : Labeling) : Prop :=
  Labeling.Valid Γ s₀ L ∧ AConf.init Γ s₀ ⊑ L (.entry [])

/-! ## Walks

A walk follows edges of the graph from state to state, taking an edge only
if its label under `L` is defined. Its trace is the sequence of the labels'
actions, `epsilon`s omitted. The labels are those of the fixed labeling `L`
— the finite labeled automaton a model checker explores — not of any
particular run. -/

inductive AWalk [Abstract] (Γ : Env) (s₀ : Stmt) (L : Labeling) :
    AState → AState → List AAct → Prop where
  | nil {a} : AWalk Γ s₀ L a a []
  | step {a b c C ℓ act acts} :
      AGraph Γ s₀ a b C ℓ → ℓ L = some act → AWalk Γ s₀ L b c acts →
      AWalk Γ s₀ L a c (act.visible ++ acts)

theorem AWalk.append [Abstract] {Γ : Env} {s₀ : Stmt} {L : Labeling} {a b c : AState}
    {t₁ t₂ : List AAct} (w₁ : AWalk Γ s₀ L a b t₁) (w₂ : AWalk Γ s₀ L b c t₂) :
    AWalk Γ s₀ L a c (t₁ ++ t₂) := by
  induction w₁ with
  | nil => exact w₂
  | step he hℓ _ ih => rw [List.append_assoc]; exact .step he hℓ (ih w₂)

/-- A silent edge at the end of a walk leaves its trace unchanged. -/
theorem AWalk.snoc_eps [Abstract] {Γ : Env} {s₀ : Stmt} {L : Labeling} {a b c : AState}
    {acts : List AAct} {C ℓ} (w : AWalk Γ s₀ L a b acts) (he : AGraph Γ s₀ b c C ℓ)
    (hℓ : ℓ L = some .epsilon) : AWalk Γ s₀ L a c acts := by
  simpa [AAct.visible] using w.append (AWalk.step he hℓ .nil)

theorem AWalk.single [Abstract] {Γ : Env} {s₀ : Stmt} {L : Labeling} {a b : AState}
    {C ℓ act} (he : AGraph Γ s₀ a b C ℓ) (hℓ : ℓ L = some act) :
    AWalk Γ s₀ L a b act.visible := by
  simpa using AWalk.step he hℓ .nil

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

theorem AExit.closed [Abstract] {Γ : Env} {Q : (AConf → AConf) → Prop}
    (hQ : PendingClosed Q) {cs entry pending s x xpending}
    (h : AExit Γ cs entry pending s x xpending) : Q pending → Q xpending := by
  induction h with
  | skip => exact id
  | assign => exact hQ.assign _ _
  | binOp => exact hQ.binOp _ _ _ _ _
  | objLit => exact hQ.objLit _ _ _
  | setTaint => exact hQ.setTaint _
  | setSink => exact hQ.setSink _
  | lookupS | lookupD | updateS | updateD | ifElse | whileDo | call => exact fun _ => hQ.id
  | seq _ _ ih₁ ih₂ => exact ih₂ ∘ ih₁

theorem ARet.closed [Abstract] {Γ : Env} {Q : (AConf → AConf) → Prop}
    (hQ : PendingClosed Q) {cs entry pending s r rpending e}
    (h : ARet Γ cs entry pending s r rpending e) : Q pending → Q rpending := by
  induction h with
  | ret => exact id
  | seqLeft _ ih => exact ih
  | seqRight hx _ ih => exact ih ∘ AExit.closed hQ hx
  | ifThen _ ih | ifElseB _ ih | whileDo _ ih => exact fun _ => ih hQ.id

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
  objLit := fun {g} x κ fs hf c hc f v hv => by
    have hne : litLocA (.fid f) ≠ allocA (g c).heap κ := fun h => aspec.allocA_fid _ _ _ h.symm
    simp only [Function.comp, AConf.doObjLit, AHeap.weakSetVal] at hv
    rw [if_neg hne, AHeap.weakSetObjs_val] at hv
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
  | body _ _ _ _ h => exact AEdge.fidReserved aspec hL h (fun _ h => h)

theorem AConf.FidReserved.init [Abstract] (aspec : AbstractSpec) (Γ : Env) (s : Stmt) :
    (AConf.init Γ s).FidReserved := by
  intro f v hv
  exact aspec.litLocA_fid f v hv.2.symm

end CoreJS
