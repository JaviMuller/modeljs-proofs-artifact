/-
  # Core JavaScript — Concrete Semantics

  * semantic domains (stores, heaps, taint registers, traces, outcomes) and
    execution records;
  * the parameters of the semantics (`Concrete`) and their assumptions
    (`ConcreteSpec`);
  * expression evaluation `⟦e⟧ρ`;
  * well-formedness of taint registers w.r.t. a statement, and the minimal
    initial configuration of a run;
  * the big-step judgement `Γ ⊢ ⟨h, ρ, δ, s⟩ ⇓c ⟨h', ρ', δ', t, o⟩`, a
    height-indexed copy of it, and the invariants every run preserves;
  * the execution record of a concrete run, and the theorem that its
    observation is well formed (`BigStep.obs_wf`).

  Plain Lean 4 — no Mathlib required.
-/

import CoreJS.CoreJsSyntax

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

/-! ## Semantic domains -/

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

def Env.params (Γ : Env) (f : Fid) : List Var :=
  ((Γ f).map Prod.fst).getD []

def Env.body (Γ : Env) (f : Fid) : Stmt :=
  ((Γ f).map Prod.snd).getD .skip

/-- The literals occurring in the bodies of the functions `fs`. -/
def Env.lits (Γ : Env) (fs : List Fid) : List Val :=
  fs.flatMap fun f => (Γ.body f).lits

/-- A literal of `Γ.lits fs` occurs in the body of a function defined in `Γ`. -/
theorem Env.mem_lits {Γ : Env} {fs : List Fid} {v : Val} (h : v ∈ Γ.lits fs) :
    ∃ f params body, Γ f = some (params, body) ∧ v ∈ body.lits := by
  obtain ⟨f, _, hv⟩ := List.mem_flatMap.1 h
  cases hf : Γ f with
  | none => simp [Env.body, hf, Stmt.lits] at hv
  | some pb => exact ⟨f, pb.1, pb.2, by rw [hf], by simpa [Env.body, hf] using hv⟩

/-- Memory heaps `h ∈ H`: `obj : Loc × Str ⇀ Loc` maps object properties to
    locations.

    The values stored at locations are not part of the heap: they live in the
    taint register (`Reg.val`), next to the taint facts about them, so that a
    register has exactly the fields of the observation of a run (`Obs`). The
    memory of a configuration is the pair `⟨h, δ⟩`, and the notions of a free,
    used or finitely supported location below read both. -/
structure Heap where
  obj : Loc → PropName → Option Loc

/-- `h[obj ↦ h.obj[(l, p) ↦ l']]`. -/
def Heap.setObj (h : Heap) (l : Loc) (p : PropName) (l' : Loc) : Heap :=
  { h with obj := fun l₁ p₁ => if l₁ = l ∧ p₁ = p then some l' else h.obj l₁ p₁ }

/-- `h[obj ↦ h.obj[(l, pᵢ) ↦ lᵢ | ⁿᵢ₌₁]]`, performed left to right, so a later
    binding of the same property wins.  This is the simultaneous update
    whenever the `pᵢ` are pairwise distinct, as they are required to be in
    an object literal. -/
def Heap.setObjs (h : Heap) (l : Loc) : List (PropName × Loc) → Heap
  | []            => h
  | (p, l') :: ps => (h.setObj l p l').setObjs l ps

/-- Taint registers `δ ∈ Reg`:
    * `val` — the value stored at each location;
    * `dep` — dependencies between values (`l₂ ∈ δ.dep l₁`: the value in `l₁`
      was computed from the one in `l₂`);
    * `ac`  — directly attacker-controlled locations;
    * `sk`  — locations holding sensitive sinks.

    `dep` is total, with `∅` for a location that depends on nothing.

    An object's location holds the object's reference value `.loc l` (set by
    [Object Initialization]). Besides making object references values, as in
    JS (`sv` compares them, binary operators accept them, a key can be one),
    this keeps an object with no properties visible: its location is in use,
    so no later allocation returns it again and two distinct objects never
    alias. -/
structure Reg where
  val : Loc → Option Val
  dep : Loc → LocSet
  ac  : LocSet
  sk  : LocSet

/-- `δ[val ↦ δ.val[l ↦ v]]`. -/
def Reg.setVal (δ : Reg) (l : Loc) (v : Val) : Reg :=
  { δ with val := fun l' => if l' = l then some v else δ.val l' }

/-- `δ[dep ↦ δ.dep[l ↦ d]]`. -/
def Reg.setDep (δ : Reg) (l : Loc) (d : LocSet) : Reg :=
  { δ with dep := fun l' => if l' = l then d else δ.dep l' }

theorem Reg.setVal_defined {δ : Reg} {l x : Loc} {v : Val} (hx : δ.val x ≠ none) :
    (δ.setVal l v).val x ≠ none := by
  by_cases e : x = l
  · simp [Reg.setVal, e]
  · simpa [Reg.setVal, e] using hx

/-- `l` is free in the memory `⟨h, δ⟩`: it holds no value and no object
    property. -/
def Heap.Free (h : Heap) (δ : Reg) (l : Loc) : Prop :=
  δ.val l = none ∧ ∀ p, h.obj l p = none

/-- Finite support: from some location on, every location is free.  Every
    memory reachable from a finite one by the semantics is finite
    (`BigStep.finite`), and only finite memories are guaranteed to have a free
    location for the allocator to return (`ConcreteSpec`). -/
def Heap.Finite (h : Heap) (δ : Reg) : Prop :=
  ∃ n, ∀ l, n ≤ l → h.Free δ l

/-- Finiteness only reads the register's values. -/
theorem Heap.Finite.congr {h : Heap} {δ δ' : Reg} (hf : h.Finite δ) (hv : δ'.val = δ.val) :
    h.Finite δ' := by
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, fun l hl => ⟨by rw [hv]; exact (hn l hl).1, (hn l hl).2⟩⟩

theorem Heap.Finite.setVal {h : Heap} {δ : Reg} (hf : h.Finite δ) (l : Loc) (v : Val) :
    h.Finite (δ.setVal l v) := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨max n (l + 1), fun l' hl' => ?_⟩
  have h₁ : n ≤ l' := Nat.le_trans (Nat.le_max_left _ _) hl'
  have hne : l' ≠ l := Nat.ne_of_gt (Nat.le_trans (Nat.le_max_right _ _) hl')
  refine ⟨?_, (hn l' h₁).2⟩
  simpa [Reg.setVal, hne] using (hn l' h₁).1

theorem Heap.Finite.setObj {h : Heap} {δ : Reg} (hf : h.Finite δ) (l : Loc) (p : PropName)
    (l' : Loc) : (h.setObj l p l').Finite δ := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨max n (l + 1), fun l₁ hl₁ => ?_⟩
  have h₁ : n ≤ l₁ := Nat.le_trans (Nat.le_max_left _ _) hl₁
  have hne : l₁ ≠ l := Nat.ne_of_gt (Nat.le_trans (Nat.le_max_right _ _) hl₁)
  refine ⟨(hn l₁ h₁).1, fun p₁ => ?_⟩
  simpa [Heap.setObj, hne] using (hn l₁ h₁).2 p₁

theorem Heap.Finite.setObjs {h : Heap} {δ : Reg} (hf : h.Finite δ) (l : Loc)
    (ps : List (PropName × Loc)) : (h.setObjs l ps).Finite δ := by
  induction ps generalizing h with
  | nil => exact hf
  | cons q ps ih => exact ih (hf.setObj l q.1 q.2)

/-- A finite memory has a free location. -/
theorem Heap.Finite.exists_fresh {h : Heap} {δ : Reg} (hf : h.Finite δ) : ∃ l, h.Free δ l := by
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, hn n (Nat.le_refl n)⟩

/-- `l` is in use in the memory `⟨h, δ⟩`: it holds a value, or an object
    property. -/
def Heap.Defined (h : Heap) (δ : Reg) (l : Loc) : Prop :=
  δ.val l ≠ none ∨ ∃ p, h.obj l p ≠ none

/-- Being in use only reads the register's values. -/
theorem Heap.Defined.congr {h : Heap} {δ δ' : Reg} {x : Loc} (hx : h.Defined δ x)
    (hv : δ'.val = δ.val) : h.Defined δ' x := by
  rw [Heap.Defined, hv]; exact hx

theorem Heap.Defined.setVal {h : Heap} {δ : Reg} {x : Loc} (hx : h.Defined δ x) (l : Loc)
    (v : Val) : h.Defined (δ.setVal l v) x := by
  rcases hx with hx | hx
  · exact Or.inl (Reg.setVal_defined hx)
  · exact Or.inr hx

theorem Heap.Defined.setObj {h : Heap} {δ : Reg} {x : Loc} (hx : h.Defined δ x) (l : Loc)
    (p : PropName) (l' : Loc) : (h.setObj l p l').Defined δ x := by
  rcases hx with hx | ⟨q, hq⟩
  · exact Or.inl hx
  · refine Or.inr ⟨q, ?_⟩
    by_cases e : x = l ∧ q = p
    · simp [Heap.setObj, e]
    · simpa [Heap.setObj, e] using hq

theorem Heap.Defined.setObjs {h : Heap} {δ : Reg} {x : Loc} (hx : h.Defined δ x) (l : Loc) :
    ∀ ps : List (PropName × Loc), (h.setObjs l ps).Defined δ x
  | []           => hx
  | (p, l') :: ps => (hx.setObj l p l').setObjs l ps

theorem Heap.defined_setVal_self (h : Heap) (δ : Reg) (l : Loc) (v : Val) :
    h.Defined (δ.setVal l v) l :=
  Or.inl (by simp [Reg.setVal])

/-- A free location (`ConcreteSpec.allocC_fresh`) is not in use. -/
theorem Heap.not_defined_of_free {h : Heap} {δ : Reg} {l : Loc} (hf : h.Free δ l) :
    ¬ h.Defined δ l := by
  rintro (hv | ⟨p, hp⟩)
  · exact hv hf.1
  · exact hp (hf.2 p)

/-- Membership in the dependency set built by `[Binary Operation]`. -/
theorem mem_binOpDep {δ : Reg} {l₁ l₂ l' : Loc} :
    (δ.dep l₁ ∪ δ.dep l₂ ∪ {l₁, l₂}) l' ↔
      δ.dep l₁ l' ∨ δ.dep l₂ l' ∨ l' = l₁ ∨ l' = l₂ := by
  show (δ.dep l₁ l' ∨ δ.dep l₂ l') ∨ (l' = l₁ ∨ l' = l₂) ↔ _
  constructor
  · rintro ((h | h) | h | h) <;> simp [h]
  · rintro (h | h | h | h) <;> simp [h]

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

/-- Flatten a trace into the list of its actions, in order. -/
def Trc.toList : Trc → List Act
  | .emp       => []
  | .act a     => [a]
  | .seq t₁ t₂ => t₁.toList ++ t₂.toList

/-! ## Execution records

An *execution record* `⟨t, δ⟩` pairs a trace with an *observation* `δ` of it:
the value stored at each location and the taint facts (`dep`/`ac`/`sk`) in
force by the end of the run — the fields of the final taint register. Defined
here, rather than alongside the query language that consumes them
(`CoreJsQuerySemantics.lean`), because they are built entirely from concepts
already in this file (`Trc`, `Reg`) and
are meant to be shared: the query semantics and the FO-LTL translation both
sit on top of them, and a future model-checking algorithm over the automaton
of `CoreJsAutomatonSemantics.lean` may need them too. -/

/-- Observations `δ` of an execution: the value stored at each location
    (`val`), the locations each location was computed from (`dep`), the
    attacker-controlled locations (`ac`) and the sink locations (`sk`). -/
structure Obs where
  val : Loc → Option Val
  dep : Loc → LocSet
  ac  : LocSet
  sk  : LocSet

/-- Execution records `⟨t, δ⟩`. -/
structure Exec where
  trc : Trc
  obs : Obs

/-- The observation of a concrete run with final taint register `δ`, field
    by field: `val = δ.val`, `dep = δ.dep`, `sk = δ.sk`, and `ac` is `δ.ac`
    together with every location that depends on a location of `δ.ac`. -/
def Obs.ofRun (δ : Reg) : Obs where
  val := δ.val
  dep := δ.dep
  ac  := fun l => δ.ac l ∨ ∃ l', δ.ac l' ∧ δ.dep l l'
  sk  := δ.sk

/-- Well-formedness of an observation (not assumed by any semantics that
    consumes one): `dep` is transitive (`δ.dep l₁ l₂` reads "`l₂ ∈ δ.dep l₁`",
    i.e. `l₁` depends on `l₂`), and `ac` is closed under reverse dependency: a
    location depending on an attacker-controlled one is attacker-controlled. -/
structure Obs.WF (δ : Obs) : Prop where
  dep_trans : ∀ l₁ l₂ l₃, δ.dep l₁ l₂ → δ.dep l₂ l₃ → δ.dep l₁ l₃
  ac_closed : ∀ l₁ l₂, δ.dep l₂ l₁ → δ.ac l₁ → δ.ac l₂

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

Three ingredients are left as parameters: the injection `v ↦ l_v` of literals
into locations, the concrete allocator `alloc_c`, and the interpretation of
binary operators. -/

/-- Parameters of the concrete semantics. -/
class Concrete where
  /-- `l_v`: the fixed location at which the literal value `v` is stored. -/
  litLoc : Val → Loc
  /-- `alloc_c(h, δ, κ)`: allocation of a fresh location of the memory
      `⟨h, δ⟩`. -/
  allocC : Heap → Reg → Idx → Loc
  /-- `⊕(v₁, v₂)`: interpretation of binary operators. -/
  opSem  : BinOp → Val → Val → Val

open Concrete

/-- Assumptions about the parameters above: what a sensible concrete instance
    looks like. The semantics itself does not depend on these; the theorems
    about runs do.

    Freshness is only demanded of *finite* memories (`Heap.Finite`): a memory
    that holds a value at every location has no free location to return, so
    requiring freshness of all heaps would make the specification
    unsatisfiable (and every theorem assuming it vacuous). -/
structure ConcreteSpec [Concrete] : Prop where
  /-- Literal locations are pairwise distinct. -/
  litLoc_inj   : ∀ v w, litLoc v = litLoc w → v = w
  /-- Allocation (on a finite memory) returns a free location. -/
  allocC_fresh : ∀ (h : Heap) (δ : Reg) (κ : Idx), h.Finite δ → h.Free δ (allocC h δ κ)
  /-- Allocation never returns a literal location: the literal locations are a
      reserved region. Every literal a run can evaluate is set up in the
      initial register (`Reg.init`), so its location is not free anyway; this
      also reserves the locations of literals occurring nowhere in the
      program. Concretely that is invisible, but the analysis's abstraction
      commits every literal location to its abstract counterpart up front
      (`AlphaFn.Lits`), so an allocation must never land on one. -/
  allocC_lit   : ∀ h δ κ v, h.Finite δ → allocC h δ κ ≠ litLoc v
  /-- Binary operators never produce a function value, so a function value
      lives only at its own literal location (`Reg.FidCanon`), as JS's
      reference semantics demands: passing or storing a function never copies
      it. In JS the only operators that can yield a function are those that
      return one of their operands — `&&`, `||`, `??` and the comma operator
      `(a, b)` — and they are expressed by statements, not as `BinOp`s:
      `x := a || b` as `c := ToBoolean(a); if c then x := a else x := b`
      (`ToBoolean` any boolean-valued operator; the assignments copy the
      operand's *location*, creating no new function value), and similarly
      `&&`/`??`; `x := (a, b)` as evaluating `a`, then `x := b`. Every other
      binary operator computes a new, non-function value. -/
  opSem_fid    : ∀ op v₁ v₂ f, opSem op v₁ v₂ ≠ .fid f

/-- The allocation half of `ConcreteSpec` is satisfiable. -/
theorem exists_allocator :
    ∃ alloc : Heap → Reg → Idx → Loc,
      ∀ (h : Heap) (δ : Reg) (κ : Idx), h.Finite δ → h.Free δ (alloc h δ κ) := by
  classical
  refine ⟨fun h δ _ => if hf : h.Finite δ then Classical.choose hf.exists_fresh else 0, ?_⟩
  intro h δ κ hf
  simp only [hf, dif_pos]
  exact Classical.choose_spec hf.exists_fresh

/-- Every location holding a function value is that function's own literal
    location. Holds initially (`Reg.init_fidCanon`) and along every run whose
    binary operators never produce a function value (`BigStep.fidCanon`), since
    no other rule writes a value. -/
def Reg.FidCanon [Concrete] (δ : Reg) : Prop :=
  ∀ l f, δ.val l = some (.fid f) → l = litLoc (.fid f)

/-! ## Expression evaluation

`⟦e⟧ρ ≜ l`, with `⟦v⟧ρ ≜ l_v` and `⟦x⟧ρ ≜ ρ(x)`.  Partial, as `ρ` is. -/

/-- `⟦e⟧ρ`. -/
def evalE [Concrete] (ρ : Sto) : Expr → Option Loc
  | .val v => some (litLoc v)
  | .var x => ρ x

/-- `⟦e⟧ρ`, as in the paper. -/
scoped notation:max (name := evalENotation) "⟦" e "⟧" ρ:max => evalE ρ e

/-- `⟦e₁⟧ρ, ..., ⟦eₙ⟧ρ`, pointwise. -/
def evalEs [Concrete] (ρ : Sto) : List Expr → Option (List Loc)
  | []      => some []
  | e :: es => do
      let l  ← ⟦e⟧ρ
      let ls ← evalEs ρ es
      return l :: ls

/-- `⟦es⟧ρ`, the paper's `⟦eᵢ⟧ρ = lᵢ |ⁿᵢ₌₁` as one list (the same notation as
    `⟦e⟧ρ`; the type of the argument, `Expr` or `List Expr`, selects the
    evaluation, so binders of statements using it carry their types). -/
scoped notation:max (name := evalEsNotation) "⟦" es "⟧" ρ:max => evalEs ρ es


/-! ## Well-formedness -/

/-- A taint register `δ` is well formed w.r.t. a statement `s` iff every
    literal value `v` occurring in `s` satisfies `δ.val(l_v) = v`, and the
    global `undefined` cell holds `undefined`.

    The second conjunct is unconditional rather than gated on `s.lits`: no
    source statement need mention `undefined` syntactically, yet the
    [Function Call] rule below reads `l_undef` whenever a callee body falls
    through without an explicit `return`. -/
def Reg.WF [Concrete] (δ : Reg) (s : Stmt) : Prop :=
  (∀ v ∈ s.lits, δ.val (litLoc v) = some v) ∧
  δ.val (litLoc .undef) = some .undef

/-! ## Initial configurations

The configuration a program starts from: the empty heap (no object has any
property), the empty store, and the *minimal* well-formed taint register (only
the literals of the statement, plus `undefined`, hold values; no dependencies,
nothing attacker-controlled, no sinks). -/

/-- The empty heap: no object has any property. -/
def Heap.empty : Heap := ⟨fun _ _ => none⟩

/-- The literals a run of `s` starts with, given the functions `fs` whose
    bodies it may run: `undefined`, those of `s`, and those of the bodies. -/
def initLits (Γ : Env) (fs : List Fid) (s : Stmt) : List Val :=
  Val.undef :: (s.lits ++ Γ.lits fs)

/-- The minimal taint register a run of `s` starts from: `l_v ↦ v` for every
    literal `v` of `initLits Γ fs s` and no other value; no dependencies,
    nothing attacker-controlled, no sinks.

    The bodies' literals are needed because evaluating a literal reads its
    location: without them, a statement in a function body that uses a
    literal (`y := x + 1`, `if true …`, calling another function by name)
    would have no derivation. `fs` lists the functions whose literals are
    set up; normally every function of `Γ` (a list, rather than `Γ`'s
    domain, so that the register stays computable). -/
def Reg.init [Concrete] (Γ : Env) (fs : List Fid) (s : Stmt) : Reg where
  val := fun l => (initLits Γ fs s).find? (fun v => litLoc v == l)
  dep := fun _ => ∅
  ac  := ∅
  sk  := ∅

/-- The initial configuration `⟨∅, ∅, Reg.init Γ fs s⟩` of a run of `s`. -/
def Conf.init [Concrete] (Γ : Env) (fs : List Fid) (s : Stmt) : Conf :=
  ⟨Heap.empty, Sto.empty, Reg.init Γ fs s⟩

/-- `Reg.init Γ fs s` is well formed for `s`. -/
theorem Reg.init_WF [Concrete] (hs : ConcreteSpec) (Γ : Env) (fs : List Fid) (s : Stmt) :
    (Reg.init Γ fs s).WF s := by
  have key : ∀ v ∈ initLits Γ fs s, (Reg.init Γ fs s).val (litLoc v) = some v := by
    intro v hv
    show (initLits Γ fs s).find? (fun w => litLoc w == litLoc v) = some v
    cases hf : (initLits Γ fs s).find? (fun w => litLoc w == litLoc v) with
    | none =>
      have := List.find?_eq_none.1 hf v hv
      simp at this
    | some w =>
      have hw := List.find?_some hf
      simp only [beq_iff_eq] at hw
      rw [hs.litLoc_inj _ _ hw]
  exact ⟨fun v hv => key v (List.mem_cons_of_mem _ (List.mem_append_left _ hv)),
    key _ (List.mem_cons_self ..)⟩

/-- The initial memory `⟨∅, Reg.init Γ fs s⟩` is finite: no literal location
    exceeds the largest one used. -/
theorem Reg.init_finite [Concrete] (Γ : Env) (fs : List Fid) (s : Stmt) :
    Heap.empty.Finite (Reg.init Γ fs s) := by
  obtain ⟨n, hn⟩ : ∃ n, ∀ v ∈ initLits Γ fs s, litLoc v < n := by
    generalize initLits Γ fs s = xs
    induction xs with
    | nil => exact ⟨0, by simp⟩
    | cons a xs ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨max (litLoc a + 1) n, ?_⟩
      intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (hn v hv) (Nat.le_max_right _ _)
  refine ⟨n, fun l hl => ⟨?_, fun _ => rfl⟩⟩
  show (initLits Γ fs s).find? (fun v => litLoc v == l) = none
  rw [List.find?_eq_none]
  intro x hx
  have := hn x hx
  simpa using Nat.ne_of_lt (Nat.lt_of_lt_of_le this hl)

/-! ## Big-step semantics

`Γ ⊢ ⟨h, ρ, δ, s⟩ ⇓c ⟨h', ρ', δ', t, o⟩`, written as in the paper (scoped
notation for `BigStep Γ ⟨h, ρ, δ⟩ s ⟨h', ρ', δ', t, o⟩`; the paper's subscript
`⇓_c` is `⇓c`). The result is any term of type `Res`, usually the anonymous
constructor `⟨h', ρ', δ', t, o⟩`. When the initial configuration is a single
term `c : Conf` rather than its three components, the judgement is written
`Γ ⊢ ⟨c, s⟩ ⇓c r`.

Each rule introduces the components of the resulting configuration as
variables and defines them by equational premises, so a derivation can be
built by applying the rule and discharging each equation on its own (as the
test suite's `bigstep` tactic does), and the abstract semantics can mirror
the rules premise by premise.

Since this is an *inductive* definition, only terminating executions are
derivable, and every trace is finite. -/

-- Declared before `BigStep` so that its rules can use them; without hygiene,
-- `BigStep` is resolved where the notation is used.
set_option hygiene false in
/-- `Γ ⊢ ⟨h, ρ, δ, s⟩ ⇓c r`: the paper's concrete big-step judgement. -/
scoped notation:50 (name := bigStepNotation)
  Γ:51 " ⊢ " "⟨" h ", " ρ ", " δ ", " s "⟩" " ⇓c " r:51 => BigStep Γ ⟨h, ρ, δ⟩ s r

set_option hygiene false in
/-- `Γ ⊢ ⟨c, s⟩ ⇓c r`: the big-step judgement from a configuration `c : Conf`. -/
scoped notation:50 (name := bigStepConfNotation)
  Γ:51 " ⊢ " "⟨" c ", " s "⟩" " ⇓c " r:51 => BigStep Γ c s r

inductive BigStep [Concrete] (Γ : Env) : Conf → Stmt → Res → Prop where

  /-- [Skip] -/
  | skip {h ρ δ} :
      Γ ⊢ ⟨h, ρ, δ, .skip⟩ ⇓c ⟨h, ρ, δ, .emp, .cont⟩

  /-- [Assignment] -/
  | assign {h ρ ρ' δ x} {e : Expr} {l} :
      ⟦e⟧ρ = some l →
      ρ' = ρ.upd x l →
      Γ ⊢ ⟨h, ρ, δ, .assign x e⟩ ⇓c ⟨h, ρ', δ, .emp, .cont⟩

  /-- [Binary Operation] -/
  | binOp {h ρ ρ' δ δ' x κ op} {e₁ e₂ : Expr} {l₁ l₂ v₁ v₂ l v d} :
      ⟦e₁⟧ρ = some l₁ →
      ⟦e₂⟧ρ = some l₂ →
      δ.val l₁ = some v₁ →
      δ.val l₂ = some v₂ →
      l = allocC h δ κ →
      v = opSem op v₁ v₂ →
      ρ' = ρ.upd x l →
      d = δ.dep l₁ ∪ δ.dep l₂ ∪ {l₁, l₂} →
      δ' = (δ.setVal l v).setDep l d →
      Γ ⊢ ⟨h, ρ, δ, .binOp x κ op e₁ e₂⟩ ⇓c ⟨h, ρ', δ', .emp, .cont⟩

  /-- [Object Initialization] -/
  | objLit {h h' ρ ρ' δ δ' x κ} {fs : List (PropName × Expr)} {ls l} :
      ⟦fs.map Prod.snd⟧ρ = some ls →
      l = allocC h δ κ →
      h' = h.setObjs l (("__proto__", litLoc .proto) :: (fs.map Prod.fst).zip ls) →
      ρ' = ρ.upd x l →
      δ' = (δ.setVal l (.loc l)).setDep l ∅ →
      Γ ⊢ ⟨h, ρ, δ, .objLit x κ fs⟩ ⇓c ⟨h', ρ', δ', .emp, .cont⟩

  /-- [Static Property Lookup] -/
  | lookupS {h ρ ρ' δ x κ} {e : Expr} {p l₁ l₂} :
      ⟦e⟧ρ = some l₁ →
      h.obj l₁ p = some l₂ →
      ρ' = ρ.upd x l₂ →
      Γ ⊢ ⟨h, ρ, δ, .lookupS x κ e p⟩ ⇓c
        ⟨h, ρ', δ, .act (.lookup l₂ l₁ (litLoc (.str p))), .cont⟩

  /-- [Dynamic Property Lookup] -/
  | lookupD {h ρ ρ' δ x κ} {e₁ e₂ : Expr} {l₁ l₂ l₃ p v} :
      ⟦e₁⟧ρ = some l₁ →
      ⟦e₂⟧ρ = some l₂ →
      δ.val l₂ = some v →
      v.KeyOf p →
      h.obj l₁ p = some l₃ →
      ρ' = ρ.upd x l₃ →
      Γ ⊢ ⟨h, ρ, δ, .lookupD x κ e₁ e₂⟩ ⇓c
        ⟨h, ρ', δ, .act (.lookup l₃ l₁ l₂), .cont⟩

  /-- [Static Property Lookup], missing own property: as in JS, it is read
      from the prototype, here the one shared `Object.prototype` at
      `litLoc .proto` (object literals point to it through `__proto__`; full
      prototype chains are not modelled). Reading a property of `undefined`
      itself throws in JS, so it has no rule. -/
  | lookupSProto {h ρ ρ' δ x κ} {e : Expr} {p l₁ l₂} :
      ⟦e⟧ρ = some l₁ →
      δ.val l₁ ≠ some .undef →
      h.obj l₁ p = none →
      h.obj (litLoc .proto) p = some l₂ →
      ρ' = ρ.upd x l₂ →
      Γ ⊢ ⟨h, ρ, δ, .lookupS x κ e p⟩ ⇓c
        ⟨h, ρ', δ, .act (.lookup l₂ l₁ (litLoc (.str p))), .cont⟩

  /-- [Static Property Lookup], missing on the object and on
      `Object.prototype`. -/
  | lookupSMissing {h ρ ρ' δ x κ} {e : Expr} {p l₁} :
      ⟦e⟧ρ = some l₁ →
      δ.val l₁ ≠ some .undef →
      h.obj l₁ p = none →
      h.obj (litLoc .proto) p = none →
      ρ' = ρ.upd x (litLoc .undef) →
      Γ ⊢ ⟨h, ρ, δ, .lookupS x κ e p⟩ ⇓c
        ⟨h, ρ', δ, .act (.lookup (litLoc .undef) l₁ (litLoc (.str p))), .cont⟩

  /-- [Dynamic Property Lookup], missing own property: read from
      `Object.prototype`, as above. -/
  | lookupDProto {h ρ ρ' δ x κ} {e₁ e₂ : Expr} {l₁ l₂ l₃ p v} :
      ⟦e₁⟧ρ = some l₁ →
      ⟦e₂⟧ρ = some l₂ →
      δ.val l₁ ≠ some .undef →
      δ.val l₂ = some v →
      v.KeyOf p →
      h.obj l₁ p = none →
      h.obj (litLoc .proto) p = some l₃ →
      ρ' = ρ.upd x l₃ →
      Γ ⊢ ⟨h, ρ, δ, .lookupD x κ e₁ e₂⟩ ⇓c
        ⟨h, ρ', δ, .act (.lookup l₃ l₁ l₂), .cont⟩

  /-- [Dynamic Property Lookup], missing on the object and on
      `Object.prototype`. -/
  | lookupDMissing {h ρ ρ' δ x κ} {e₁ e₂ : Expr} {l₁ l₂ p v} :
      ⟦e₁⟧ρ = some l₁ →
      ⟦e₂⟧ρ = some l₂ →
      δ.val l₁ ≠ some .undef →
      δ.val l₂ = some v →
      v.KeyOf p →
      h.obj l₁ p = none →
      h.obj (litLoc .proto) p = none →
      ρ' = ρ.upd x (litLoc .undef) →
      Γ ⊢ ⟨h, ρ, δ, .lookupD x κ e₁ e₂⟩ ⇓c
        ⟨h, ρ', δ, .act (.lookup (litLoc .undef) l₁ l₂), .cont⟩

  /-- [Static Property Update] -/
  | updateS {h h' ρ δ κ} {e₁ : Expr} {p} {e₂ : Expr} {l₁ l₂} :
      ⟦e₁⟧ρ = some l₁ →
      ⟦e₂⟧ρ = some l₂ →
      h' = h.setObj l₁ p l₂ →
      Γ ⊢ ⟨h, ρ, δ, .updateS κ e₁ p e₂⟩ ⇓c
        ⟨h', ρ, δ, .act (.update l₁ (litLoc (.str p)) l₂), .cont⟩

  /-- [Dynamic Property Update] -/
  | updateD {h h' ρ δ κ} {e₁ e₂ e₃ : Expr} {l₁ l₂ l₃ p v} :
      ⟦e₁⟧ρ = some l₁ →
      ⟦e₂⟧ρ = some l₂ →
      ⟦e₃⟧ρ = some l₃ →
      δ.val l₂ = some v →
      v.KeyOf p →
      h' = h.setObj l₁ p l₃ →
      Γ ⊢ ⟨h, ρ, δ, .updateD κ e₁ e₂ e₃⟩ ⇓c
        ⟨h', ρ, δ, .act (.update l₁ l₂ l₃), .cont⟩

  /-- [Sequence Ret] -/
  | seqRet {h h' ρ ρ' δ δ' s₁ s₂ t l} :
      Γ ⊢ ⟨h, ρ, δ, s₁⟩ ⇓c ⟨h', ρ', δ', t, .ret l⟩ →
      Γ ⊢ ⟨h, ρ, δ, .seq s₁ s₂⟩ ⇓c ⟨h', ρ', δ', t, .ret l⟩

  /-- [Sequence Cont] -/
  | seqCont {h h' h'' ρ ρ' ρ'' δ δ' δ'' s₁ s₂ t₁ t₂ o} :
      Γ ⊢ ⟨h, ρ, δ, s₁⟩ ⇓c ⟨h', ρ', δ', t₁, .cont⟩ →
      Γ ⊢ ⟨h', ρ', δ', s₂⟩ ⇓c ⟨h'', ρ'', δ'', t₂, o⟩ →
      Γ ⊢ ⟨h, ρ, δ, .seq s₁ s₂⟩ ⇓c ⟨h'', ρ'', δ'', .seq t₁ t₂, o⟩

  /-- [Function Call], explicit return: the callee body terminates with
      `r⟨l⟩` and `l` is what the call evaluates to. -/
  | callRet {h h' ρ ρ' ρf' δ δ' x κ} {e : Expr} {es : List Expr} {lf f params body ls l t} :
      ⟦e⟧ρ = some lf →
      δ.val lf = some (.fid f) →
      Γ f = some (params, body) →
      ⟦es⟧ρ = some ls →
      params.length = ls.length →
      Γ ⊢ ⟨h, Sto.ofParams params ls, δ, body⟩ ⇓c ⟨h', ρf', δ', t, .ret l⟩ →
      ρ' = ρ.upd x l →
      Γ ⊢ ⟨h, ρ, δ, .call x κ e es⟩ ⇓c
        ⟨h', ρ', δ',
         .seq (.act (.call lf ls)) (.seq t (.act (.ret lf l))), .cont⟩

  /-- [Function Call], implicit return: the callee body falls through with
      outcome `·`, and the call evaluates to `undefined` (JavaScript's
      behaviour for a function that returns no value).  The emitted `Ret`
      action mentions `l_undef`, so the trace records a return either way. -/
  | callCont {h h' ρ ρ' ρf' δ δ' x κ} {e : Expr} {es : List Expr} {lf f params body ls t} :
      ⟦e⟧ρ = some lf →
      δ.val lf = some (.fid f) →
      Γ f = some (params, body) →
      ⟦es⟧ρ = some ls →
      params.length = ls.length →
      Γ ⊢ ⟨h, Sto.ofParams params ls, δ, body⟩ ⇓c ⟨h', ρf', δ', t, .cont⟩ →
      ρ' = ρ.upd x (litLoc .undef) →
      Γ ⊢ ⟨h, ρ, δ, .call x κ e es⟩ ⇓c
        ⟨h', ρ', δ',
         .seq (.act (.call lf ls))
              (.seq t (.act (.ret lf (litLoc .undef)))), .cont⟩

  /-- [If True] -/
  | ifTrue {h ρ δ κ} {e : Expr} {s₁ s₂ l r} :
      ⟦e⟧ρ = some l →
      δ.val l = some (.bool true) →
      Γ ⊢ ⟨h, ρ, δ, s₁⟩ ⇓c r →
      Γ ⊢ ⟨h, ρ, δ, .ifElse κ e s₁ s₂⟩ ⇓c r

  /-- [If False] -/
  | ifFalse {h ρ δ κ} {e : Expr} {s₁ s₂ l r} :
      ⟦e⟧ρ = some l →
      δ.val l = some (.bool false) →
      Γ ⊢ ⟨h, ρ, δ, s₂⟩ ⇓c r →
      Γ ⊢ ⟨h, ρ, δ, .ifElse κ e s₁ s₂⟩ ⇓c r

  /-- [While], by unfolding into a conditional. -/
  | whileDo {h ρ δ κ} {e : Expr} {s r} :
      Γ ⊢ ⟨h, ρ, δ, .ifElse κ e (.seq s (.whileDo κ e s)) .skip⟩ ⇓c r →
      Γ ⊢ ⟨h, ρ, δ, .whileDo κ e s⟩ ⇓c r

  /-- [Return] -/
  | ret {h ρ δ} {e : Expr} {l} :
      ⟦e⟧ρ = some l →
      Γ ⊢ ⟨h, ρ, δ, .ret e⟩ ⇓c ⟨h, ρ, δ, .emp, .ret l⟩

  /-- [SetTaint] -/
  | setTaint {h ρ δ δ'} {e : Expr} {l} :
      ⟦e⟧ρ = some l →
      δ' = { δ with ac := {l} ∪ δ.ac } →
      Γ ⊢ ⟨h, ρ, δ, .setTaint e⟩ ⇓c ⟨h, ρ, δ', .emp, .cont⟩

  /-- [SetSink] -/
  | setSink {h ρ δ δ'} {e : Expr} {l} :
      ⟦e⟧ρ = some l →
      δ' = { δ with sk := {l} ∪ δ.sk } →
      Γ ⊢ ⟨h, ρ, δ, .setSink e⟩ ⇓c ⟨h, ρ, δ', .emp, .cont⟩


/- `notation` generates no unexpander for a constant that does not exist yet, so
   goals would show `BigStep Γ c s r`; these restore the notation, printing an
   explicit configuration as `⟨h, ρ, δ, s⟩` and an explicit result as
   `⟨h', ρ', δ', t, o⟩` (rather than as structure instances). -/
/-- An explicit result `{ heap := h', … }` printed as `⟨h', ρ', δ', t, o⟩`. -/
def unexpandRes : Lean.Term → Lean.PrettyPrinter.UnexpandM Lean.Term
  | `({ heap := $h, sto := $ρ, reg := $δ, trc := $t, out := $o }) => `(⟨$h, $ρ, $δ, $t, $o⟩)
  | r => pure r

@[scoped app_unexpander BigStep] def unexpandBigStep : Lean.PrettyPrinter.Unexpander
  | `($_ $Γ { heap := $h, sto := $ρ, reg := $δ } $s $r) => do
      `($Γ ⊢ ⟨$h, $ρ, $δ, $s⟩ ⇓c $(← unexpandRes r))
  | `($_ $Γ $c $s $r) => do `($Γ ⊢ ⟨$c, $s⟩ ⇓c $(← unexpandRes r))
  | _ => throw ()

/-! ## Height-indexed derivations

`BigStep` lives in `Prop`, so Lean generates no `sizeOf` for it and its
recursor eliminates only into `Prop`: there is no derivation height available
to recurse on.  The automaton soundness proof needs one: its `[While]` case
applies the induction hypothesis to derivations several levels below the one
being inducted on (the loop body's derivation, and the next iteration's,
inside the unfolded conditional and sequence), which structural induction,
giving hypotheses only for immediate premises, does not provide.

`BigStepN Γ n` is the same relation with an explicit bound on derivation
height, written `Γ ⊢ ⟨h, ρ, δ, s⟩ ⇓c[n] r` (not in the paper): every rule
concludes at `n+1` with its recursive premises at `n`.
`BigStep.toN` and `BigStepN.toBigStep` establish that the two agree, so
soundness may be proved by strong induction on `n` and then transported back. -/

set_option hygiene false in
/-- `Γ ⊢ ⟨h, ρ, δ, s⟩ ⇓c[n] r`: a big-step derivation of height at most `n`. -/
scoped notation:50 (name := bigStepNNotation)
  Γ:51 " ⊢ " "⟨" h ", " ρ ", " δ ", " s "⟩" " ⇓c[" n "] " r:51 => BigStepN Γ n ⟨h, ρ, δ⟩ s r

set_option hygiene false in
/-- `Γ ⊢ ⟨c, s⟩ ⇓c[n] r`, from a configuration `c : Conf`. -/
scoped notation:50 (name := bigStepNConfNotation)
  Γ:51 " ⊢ " "⟨" c ", " s "⟩" " ⇓c[" n "] " r:51 => BigStepN Γ n c s r

inductive BigStepN [Concrete] (Γ : Env) : Nat → Conf → Stmt → Res → Prop where

  /-- [Skip] -/
  | skip {n h ρ δ} :
      Γ ⊢ ⟨h, ρ, δ, .skip⟩ ⇓c[n+1] ⟨h, ρ, δ, .emp, .cont⟩

  /-- [Assignment] -/
  | assign {n h ρ ρ' δ x} {e : Expr} {l} :
      ⟦e⟧ρ = some l →
      ρ' = ρ.upd x l →
      Γ ⊢ ⟨h, ρ, δ, .assign x e⟩ ⇓c[n+1] ⟨h, ρ', δ, .emp, .cont⟩

  /-- [Binary Operation] -/
  | binOp {n h ρ ρ' δ δ' x κ op} {e₁ e₂ : Expr} {l₁ l₂ v₁ v₂ l v d} :
      ⟦e₁⟧ρ = some l₁ →
      ⟦e₂⟧ρ = some l₂ →
      δ.val l₁ = some v₁ →
      δ.val l₂ = some v₂ →
      l = allocC h δ κ →
      v = opSem op v₁ v₂ →
      ρ' = ρ.upd x l →
      d = δ.dep l₁ ∪ δ.dep l₂ ∪ {l₁, l₂} →
      δ' = (δ.setVal l v).setDep l d →
      Γ ⊢ ⟨h, ρ, δ, .binOp x κ op e₁ e₂⟩ ⇓c[n+1] ⟨h, ρ', δ', .emp, .cont⟩

  /-- [Object Initialization] -/
  | objLit {n h h' ρ ρ' δ δ' x κ} {fs : List (PropName × Expr)} {ls l} :
      ⟦fs.map Prod.snd⟧ρ = some ls →
      l = allocC h δ κ →
      h' = h.setObjs l (("__proto__", litLoc .proto) :: (fs.map Prod.fst).zip ls) →
      ρ' = ρ.upd x l →
      δ' = (δ.setVal l (.loc l)).setDep l ∅ →
      Γ ⊢ ⟨h, ρ, δ, .objLit x κ fs⟩ ⇓c[n+1] ⟨h', ρ', δ', .emp, .cont⟩

  /-- [Static Property Lookup] -/
  | lookupS {n h ρ ρ' δ x κ} {e : Expr} {p l₁ l₂} :
      ⟦e⟧ρ = some l₁ →
      h.obj l₁ p = some l₂ →
      ρ' = ρ.upd x l₂ →
      Γ ⊢ ⟨h, ρ, δ, .lookupS x κ e p⟩ ⇓c[n+1]
        ⟨h, ρ', δ, .act (.lookup l₂ l₁ (litLoc (.str p))), .cont⟩

  /-- [Dynamic Property Lookup] -/
  | lookupD {n h ρ ρ' δ x κ} {e₁ e₂ : Expr} {l₁ l₂ l₃ p v} :
      ⟦e₁⟧ρ = some l₁ →
      ⟦e₂⟧ρ = some l₂ →
      δ.val l₂ = some v →
      v.KeyOf p →
      h.obj l₁ p = some l₃ →
      ρ' = ρ.upd x l₃ →
      Γ ⊢ ⟨h, ρ, δ, .lookupD x κ e₁ e₂⟩ ⇓c[n+1]
        ⟨h, ρ', δ, .act (.lookup l₃ l₁ l₂), .cont⟩

  /-- [Static Property Lookup], missing own property. -/
  | lookupSProto {n h ρ ρ' δ x κ} {e : Expr} {p l₁ l₂} :
      ⟦e⟧ρ = some l₁ →
      δ.val l₁ ≠ some .undef →
      h.obj l₁ p = none →
      h.obj (litLoc .proto) p = some l₂ →
      ρ' = ρ.upd x l₂ →
      Γ ⊢ ⟨h, ρ, δ, .lookupS x κ e p⟩ ⇓c[n+1]
        ⟨h, ρ', δ, .act (.lookup l₂ l₁ (litLoc (.str p))), .cont⟩

  /-- [Static Property Lookup], missing on the object and on
      `Object.prototype`. -/
  | lookupSMissing {n h ρ ρ' δ x κ} {e : Expr} {p l₁} :
      ⟦e⟧ρ = some l₁ →
      δ.val l₁ ≠ some .undef →
      h.obj l₁ p = none →
      h.obj (litLoc .proto) p = none →
      ρ' = ρ.upd x (litLoc .undef) →
      Γ ⊢ ⟨h, ρ, δ, .lookupS x κ e p⟩ ⇓c[n+1]
        ⟨h, ρ', δ, .act (.lookup (litLoc .undef) l₁ (litLoc (.str p))), .cont⟩

  /-- [Dynamic Property Lookup], missing own property. -/
  | lookupDProto {n h ρ ρ' δ x κ} {e₁ e₂ : Expr} {l₁ l₂ l₃ p v} :
      ⟦e₁⟧ρ = some l₁ →
      ⟦e₂⟧ρ = some l₂ →
      δ.val l₁ ≠ some .undef →
      δ.val l₂ = some v →
      v.KeyOf p →
      h.obj l₁ p = none →
      h.obj (litLoc .proto) p = some l₃ →
      ρ' = ρ.upd x l₃ →
      Γ ⊢ ⟨h, ρ, δ, .lookupD x κ e₁ e₂⟩ ⇓c[n+1]
        ⟨h, ρ', δ, .act (.lookup l₃ l₁ l₂), .cont⟩

  /-- [Dynamic Property Lookup], missing on the object and on
      `Object.prototype`. -/
  | lookupDMissing {n h ρ ρ' δ x κ} {e₁ e₂ : Expr} {l₁ l₂ p v} :
      ⟦e₁⟧ρ = some l₁ →
      ⟦e₂⟧ρ = some l₂ →
      δ.val l₁ ≠ some .undef →
      δ.val l₂ = some v →
      v.KeyOf p →
      h.obj l₁ p = none →
      h.obj (litLoc .proto) p = none →
      ρ' = ρ.upd x (litLoc .undef) →
      Γ ⊢ ⟨h, ρ, δ, .lookupD x κ e₁ e₂⟩ ⇓c[n+1]
        ⟨h, ρ', δ, .act (.lookup (litLoc .undef) l₁ l₂), .cont⟩

  /-- [Static Property Update] -/
  | updateS {n h h' ρ δ κ} {e₁ : Expr} {p} {e₂ : Expr} {l₁ l₂} :
      ⟦e₁⟧ρ = some l₁ →
      ⟦e₂⟧ρ = some l₂ →
      h' = h.setObj l₁ p l₂ →
      Γ ⊢ ⟨h, ρ, δ, .updateS κ e₁ p e₂⟩ ⇓c[n+1]
        ⟨h', ρ, δ, .act (.update l₁ (litLoc (.str p)) l₂), .cont⟩

  /-- [Dynamic Property Update] -/
  | updateD {n h h' ρ δ κ} {e₁ e₂ e₃ : Expr} {l₁ l₂ l₃ p v} :
      ⟦e₁⟧ρ = some l₁ →
      ⟦e₂⟧ρ = some l₂ →
      ⟦e₃⟧ρ = some l₃ →
      δ.val l₂ = some v →
      v.KeyOf p →
      h' = h.setObj l₁ p l₃ →
      Γ ⊢ ⟨h, ρ, δ, .updateD κ e₁ e₂ e₃⟩ ⇓c[n+1]
        ⟨h', ρ, δ, .act (.update l₁ l₂ l₃), .cont⟩

  /-- [Sequence Ret] -/
  | seqRet {n h h' ρ ρ' δ δ' s₁ s₂ t l} :
      Γ ⊢ ⟨h, ρ, δ, s₁⟩ ⇓c[n] ⟨h', ρ', δ', t, .ret l⟩ →
      Γ ⊢ ⟨h, ρ, δ, .seq s₁ s₂⟩ ⇓c[n+1] ⟨h', ρ', δ', t, .ret l⟩

  /-- [Sequence Cont] -/
  | seqCont {n h h' h'' ρ ρ' ρ'' δ δ' δ'' s₁ s₂ t₁ t₂ o} :
      Γ ⊢ ⟨h, ρ, δ, s₁⟩ ⇓c[n] ⟨h', ρ', δ', t₁, .cont⟩ →
      Γ ⊢ ⟨h', ρ', δ', s₂⟩ ⇓c[n] ⟨h'', ρ'', δ'', t₂, o⟩ →
      Γ ⊢ ⟨h, ρ, δ, .seq s₁ s₂⟩ ⇓c[n+1] ⟨h'', ρ'', δ'', .seq t₁ t₂, o⟩

  /-- [Function Call], explicit return: the callee body terminates with
      `r⟨l⟩` and `l` is what the call evaluates to. -/
  | callRet {n h h' ρ ρ' ρf' δ δ' x κ} {e : Expr} {es : List Expr} {lf f params body ls l t} :
      ⟦e⟧ρ = some lf →
      δ.val lf = some (.fid f) →
      Γ f = some (params, body) →
      ⟦es⟧ρ = some ls →
      params.length = ls.length →
      Γ ⊢ ⟨h, Sto.ofParams params ls, δ, body⟩ ⇓c[n] ⟨h', ρf', δ', t, .ret l⟩ →
      ρ' = ρ.upd x l →
      Γ ⊢ ⟨h, ρ, δ, .call x κ e es⟩ ⇓c[n+1]
        ⟨h', ρ', δ',
         .seq (.act (.call lf ls)) (.seq t (.act (.ret lf l))), .cont⟩

  /-- [Function Call], implicit return: the callee body falls through with
      outcome `·`, and the call evaluates to `undefined` (JavaScript's
      behaviour for a function that returns no value).  The emitted `Ret`
      action mentions `l_undef`, so the trace records a return either way. -/
  | callCont {n h h' ρ ρ' ρf' δ δ' x κ} {e : Expr} {es : List Expr} {lf f params body ls t} :
      ⟦e⟧ρ = some lf →
      δ.val lf = some (.fid f) →
      Γ f = some (params, body) →
      ⟦es⟧ρ = some ls →
      params.length = ls.length →
      Γ ⊢ ⟨h, Sto.ofParams params ls, δ, body⟩ ⇓c[n] ⟨h', ρf', δ', t, .cont⟩ →
      ρ' = ρ.upd x (litLoc .undef) →
      Γ ⊢ ⟨h, ρ, δ, .call x κ e es⟩ ⇓c[n+1]
        ⟨h', ρ', δ',
         .seq (.act (.call lf ls))
              (.seq t (.act (.ret lf (litLoc .undef)))), .cont⟩

  /-- [If True] -/
  | ifTrue {n h ρ δ κ} {e : Expr} {s₁ s₂ l r} :
      ⟦e⟧ρ = some l →
      δ.val l = some (.bool true) →
      Γ ⊢ ⟨h, ρ, δ, s₁⟩ ⇓c[n] r →
      Γ ⊢ ⟨h, ρ, δ, .ifElse κ e s₁ s₂⟩ ⇓c[n+1] r

  /-- [If False] -/
  | ifFalse {n h ρ δ κ} {e : Expr} {s₁ s₂ l r} :
      ⟦e⟧ρ = some l →
      δ.val l = some (.bool false) →
      Γ ⊢ ⟨h, ρ, δ, s₂⟩ ⇓c[n] r →
      Γ ⊢ ⟨h, ρ, δ, .ifElse κ e s₁ s₂⟩ ⇓c[n+1] r

  /-- [While], by unfolding into a conditional. -/
  | whileDo {n h ρ δ κ} {e : Expr} {s r} :
      Γ ⊢ ⟨h, ρ, δ, .ifElse κ e (.seq s (.whileDo κ e s)) .skip⟩ ⇓c[n] r →
      Γ ⊢ ⟨h, ρ, δ, .whileDo κ e s⟩ ⇓c[n+1] r

  /-- [Return] -/
  | ret {n h ρ δ} {e : Expr} {l} :
      ⟦e⟧ρ = some l →
      Γ ⊢ ⟨h, ρ, δ, .ret e⟩ ⇓c[n+1] ⟨h, ρ, δ, .emp, .ret l⟩

  /-- [SetTaint] -/
  | setTaint {n h ρ δ δ'} {e : Expr} {l} :
      ⟦e⟧ρ = some l →
      δ' = { δ with ac := {l} ∪ δ.ac } →
      Γ ⊢ ⟨h, ρ, δ, .setTaint e⟩ ⇓c[n+1] ⟨h, ρ, δ', .emp, .cont⟩

  /-- [SetSink] -/
  | setSink {n h ρ δ δ'} {e : Expr} {l} :
      ⟦e⟧ρ = some l →
      δ' = { δ with sk := {l} ∪ δ.sk } →
      Γ ⊢ ⟨h, ρ, δ, .setSink e⟩ ⇓c[n+1] ⟨h, ρ, δ', .emp, .cont⟩



@[scoped app_unexpander BigStepN] def unexpandBigStepN : Lean.PrettyPrinter.Unexpander
  | `($_ $Γ $n { heap := $h, sto := $ρ, reg := $δ } $s $r) => do
      `($Γ ⊢ ⟨$h, $ρ, $δ, $s⟩ ⇓c[$n] $(← unexpandRes r))
  | `($_ $Γ $n $c $s $r) => do `($Γ ⊢ ⟨$c, $s⟩ ⇓c[$n] $(← unexpandRes r))
  | _ => throw ()

/-- Raising the height bound preserves derivability. -/
theorem BigStepN.mono [Concrete] {Γ : Env} :
    ∀ {n c s r}, Γ ⊢ ⟨c, s⟩ ⇓c[n] r → Γ ⊢ ⟨c, s⟩ ⇓c[n+1] r := by
  intro n c s r H
  induction H with
  | skip => exact .skip
  | assign h1 h2 => exact .assign h1 h2
  | binOp h1 h2 h3 h4 h5 h6 h7 h8 h9 => exact .binOp h1 h2 h3 h4 h5 h6 h7 h8 h9
  | objLit h1 h2 h3 h4 h5 => exact .objLit h1 h2 h3 h4 h5
  | lookupS h1 h2 h3 => exact .lookupS h1 h2 h3
  | lookupD h1 h2 h3 h4 h5 h6 => exact .lookupD h1 h2 h3 h4 h5 h6
  | lookupSProto h1 h2 h3 h4 h5 => exact .lookupSProto h1 h2 h3 h4 h5
  | lookupSMissing h1 h2 h3 h4 h5 => exact .lookupSMissing h1 h2 h3 h4 h5
  | lookupDProto h1 h2 h3 h4 h5 h6 h7 h8 => exact .lookupDProto h1 h2 h3 h4 h5 h6 h7 h8
  | lookupDMissing h1 h2 h3 h4 h5 h6 h7 h8 => exact .lookupDMissing h1 h2 h3 h4 h5 h6 h7 h8
  | updateS h1 h2 h3 => exact .updateS h1 h2 h3
  | updateD h1 h2 h3 h4 h5 h6 => exact .updateD h1 h2 h3 h4 h5 h6
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

theorem BigStepN.mono_le [Concrete] {Γ : Env} {n c s r} (H : Γ ⊢ ⟨c, s⟩ ⇓c[n] r) :
    ∀ {m}, n ≤ m → Γ ⊢ ⟨c, s⟩ ⇓c[m] r := by
  intro m
  induction m with
  | zero => intro hnm; exact (Nat.le_zero.mp hnm) ▸ H
  | succ k ih =>
      intro hnm
      rcases Nat.lt_or_ge n (k+1) with hlt | hge
      · exact BigStepN.mono (ih (Nat.lt_succ_iff.mp hlt))
      · exact (Nat.le_antisymm hnm hge) ▸ H

/-- Every plain derivation has a height. -/
theorem BigStep.toN [Concrete] {Γ : Env} {c s r} (H : Γ ⊢ ⟨c, s⟩ ⇓c r) :
    ∃ n, Γ ⊢ ⟨c, s⟩ ⇓c[n] r := by
  induction H with
  | skip => exact ⟨1, .skip⟩
  | assign h1 h2 => exact ⟨1, .assign h1 h2⟩
  | binOp h1 h2 h3 h4 h5 h6 h7 h8 h9 => exact ⟨1, .binOp h1 h2 h3 h4 h5 h6 h7 h8 h9⟩
  | objLit h1 h2 h3 h4 h5 => exact ⟨1, .objLit h1 h2 h3 h4 h5⟩
  | lookupS h1 h2 h3 => exact ⟨1, .lookupS h1 h2 h3⟩
  | lookupD h1 h2 h3 h4 h5 h6 => exact ⟨1, .lookupD h1 h2 h3 h4 h5 h6⟩
  | lookupSProto h1 h2 h3 h4 h5 => exact ⟨1, .lookupSProto h1 h2 h3 h4 h5⟩
  | lookupSMissing h1 h2 h3 h4 h5 => exact ⟨1, .lookupSMissing h1 h2 h3 h4 h5⟩
  | lookupDProto h1 h2 h3 h4 h5 h6 h7 h8 => exact ⟨1, .lookupDProto h1 h2 h3 h4 h5 h6 h7 h8⟩
  | lookupDMissing h1 h2 h3 h4 h5 h6 h7 h8 => exact ⟨1, .lookupDMissing h1 h2 h3 h4 h5 h6 h7 h8⟩
  | updateS h1 h2 h3 => exact ⟨1, .updateS h1 h2 h3⟩
  | updateD h1 h2 h3 h4 h5 h6 => exact ⟨1, .updateD h1 h2 h3 h4 h5 h6⟩
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
    ∀ {n c s r}, Γ ⊢ ⟨c, s⟩ ⇓c[n] r → Γ ⊢ ⟨c, s⟩ ⇓c r := by
  intro n c s r H
  induction H with
  | skip => exact .skip
  | assign h1 h2 => exact .assign h1 h2
  | binOp h1 h2 h3 h4 h5 h6 h7 h8 h9 => exact .binOp h1 h2 h3 h4 h5 h6 h7 h8 h9
  | objLit h1 h2 h3 h4 h5 => exact .objLit h1 h2 h3 h4 h5
  | lookupS h1 h2 h3 => exact .lookupS h1 h2 h3
  | lookupD h1 h2 h3 h4 h5 h6 => exact .lookupD h1 h2 h3 h4 h5 h6
  | lookupSProto h1 h2 h3 h4 h5 => exact .lookupSProto h1 h2 h3 h4 h5
  | lookupSMissing h1 h2 h3 h4 h5 => exact .lookupSMissing h1 h2 h3 h4 h5
  | lookupDProto h1 h2 h3 h4 h5 h6 h7 h8 => exact .lookupDProto h1 h2 h3 h4 h5 h6 h7 h8
  | lookupDMissing h1 h2 h3 h4 h5 h6 h7 h8 => exact .lookupDMissing h1 h2 h3 h4 h5 h6 h7 h8
  | updateS h1 h2 h3 => exact .updateS h1 h2 h3
  | updateD h1 h2 h3 h4 h5 h6 => exact .updateD h1 h2 h3 h4 h5 h6
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

/-- Every rule of the concrete semantics preserves the finiteness of the
    memory (whatever location `allocC` returns). -/
theorem BigStep.finite [Concrete] {Γ : Env} {c : Conf} {s : Stmt} {r : Res}
    (hb : Γ ⊢ ⟨c, s⟩ ⇓c r) : c.heap.Finite c.reg → r.heap.Finite r.reg := by
  induction hb with
  | skip => exact id
  | assign _ _ => exact id
  | binOp _ _ _ _ _ _ _ _ hδ' => intro hf; subst hδ'; exact (hf.setVal _ _).congr rfl
  | objLit _ _ hh' _ hδ' =>
      intro hf; subst hh' hδ'; exact ((hf.setObjs _ _).setVal _ _).congr rfl
  | lookupS _ _ _ => exact id
  | lookupD _ _ _ _ _ _ => exact id
  | lookupSProto _ _ _ _ _ => exact id
  | lookupSMissing _ _ _ _ _ => exact id
  | lookupDProto _ _ _ _ _ _ _ _ => exact id
  | lookupDMissing _ _ _ _ _ _ _ _ => exact id
  | updateS _ _ hh' => intro hf; subst hh'; exact hf.setObj _ _ _
  | updateD _ _ _ _ _ hh' => intro hf; subst hh'; exact hf.setObj _ _ _
  | seqRet _ ih => exact ih
  | seqCont _ _ ih₁ ih₂ => exact fun hf => ih₂ (ih₁ hf)
  | callRet _ _ _ _ _ _ _ ih => exact ih
  | callCont _ _ _ _ _ _ _ ih => exact ih
  | ifTrue _ _ _ ih => exact ih
  | ifFalse _ _ _ ih => exact ih
  | whileDo _ ih => exact ih
  | ret _ => exact id
  | setTaint _ hδ' => intro hf; subst hδ'; exact hf.congr rfl
  | setSink _ hδ' => intro hf; subst hδ'; exact hf.congr rfl

/-- Every rule of the concrete semantics preserves `Reg.FidCanon`, provided
    binary operators never produce a function value. -/
theorem BigStep.fidCanon [Concrete] (hop : ∀ op v₁ v₂ f, opSem op v₁ v₂ ≠ .fid f)
    {Γ : Env} {c : Conf} {s : Stmt} {r : Res}
    (hb : Γ ⊢ ⟨c, s⟩ ⇓c r) : c.reg.FidCanon → r.reg.FidCanon := by
  induction hb with
  | skip => exact id
  | assign _ _ => exact id
  | @binOp h ρ ρ' δ δ' x κ op e₁ e₂ l₁ l₂ v₁ v₂ l v d _ _ _ _ _ hv _ _ hδ' =>
      intro hc l' f hl'
      subst hδ'
      change (δ.setVal l v).val l' = some (.fid f) at hl'
      by_cases e : l' = l
      · simp only [Reg.setVal, e, if_pos] at hl'
        exact absurd (hv.symm.trans (Option.some.inj hl')) (hop _ _ _ _)
      · exact hc l' f (by simpa [Reg.setVal, e] using hl')
  | @objLit h h' ρ ρ' δ δ' x κ fs ls l _ _ _ _ hδ' =>
      intro hc l' f hl'
      subst hδ'
      change (δ.setVal l (.loc l)).val l' = some (.fid f) at hl'
      by_cases e : l' = l
      · simp [Reg.setVal, e] at hl'
      · exact hc l' f (by simpa [Reg.setVal, e] using hl')
  | lookupS _ _ _ => exact id
  | lookupD _ _ _ _ _ _ => exact id
  | lookupSProto _ _ _ _ _ => exact id
  | lookupSMissing _ _ _ _ _ => exact id
  | lookupDProto _ _ _ _ _ _ _ _ => exact id
  | lookupDMissing _ _ _ _ _ _ _ _ => exact id
  | updateS _ _ _ => exact id
  | updateD _ _ _ _ _ _ => exact id
  | seqRet _ ih => exact ih
  | seqCont _ _ ih₁ ih₂ => exact fun hf => ih₂ (ih₁ hf)
  | callRet _ _ _ _ _ _ _ ih => exact ih
  | callCont _ _ _ _ _ _ _ ih => exact ih
  | ifTrue _ _ _ ih => exact ih
  | ifFalse _ _ _ ih => exact ih
  | whileDo _ ih => exact ih
  | ret _ => exact id
  | setTaint _ hδ' => intro hc; subst hδ'; exact hc
  | setSink _ hδ' => intro hc; subst hδ'; exact hc

/-- `Reg.init Γ fs s` holds a function value only at that function's literal
    location. -/
theorem Reg.init_fidCanon [Concrete] (Γ : Env) (fs : List Fid) (s : Stmt) :
    (Reg.init Γ fs s).FidCanon := by
  intro l f hl
  have hp := List.find?_some hl
  simp only [beq_iff_eq] at hp
  exact hp.symm

/-! ## Execution records of concrete runs

The final configuration of a `BigStep` run yields an execution record
(`Exec.ofRes`), and that record's observation is well formed (`Obs.WF`) —
provided the initial configuration satisfies the dependency invariant
`Reg.DepInv` (which holds, e.g., when the initial `dep` is empty).

The proof rests on one invariant of taint registers:

* `dep` is transitive, and
* every location that some location depends on holds a value.

The second conjunct is what makes `[Binary Operation]` preserve the first:
the freshly allocated location holds no value (`allocC_fresh`, which needs
the current memory to be finite, `Heap.Finite`; finiteness is itself
preserved by every rule, `BigStep.finite`), so it occurs in no dependency
set, and giving it a dependency set cannot break the transitivity of
another location's. -/

/-- The observation of a concrete run is well formed as soon as `dep` is
    transitive: `ac` is closed under reverse dependency by construction. -/
theorem Obs.WF.ofRun_of_trans {δ : Reg}
    (htrans : ∀ l₁ l₂ l₃, δ.dep l₁ l₂ → δ.dep l₂ l₃ → δ.dep l₁ l₃) :
    (Obs.ofRun δ).WF where
  dep_trans := htrans
  ac_closed := by
    intro l₁ l₂ h₂₁ hac
    rcases hac with hac | ⟨l', hl', h₁'⟩
    · exact Or.inr ⟨l₁, hac, h₂₁⟩
    · exact Or.inr ⟨l', hl', htrans _ _ _ h₂₁ h₁'⟩

/-- The execution record of a concrete run. -/
def Exec.ofRes (r : Res) : Exec :=
  ⟨r.trc, Obs.ofRun r.reg⟩

/-! ### The dependency invariant -/

/-- `dep` is transitive, and every location depended upon holds a value. -/
structure Reg.DepInv (δ : Reg) : Prop where
  trans   : ∀ l₁ l₂ l₃, δ.dep l₁ l₂ → δ.dep l₂ l₃ → δ.dep l₁ l₃
  defined : ∀ l₁ l₂, δ.dep l₁ l₂ → δ.val l₂ ≠ none

/-- An empty `dep` satisfies the invariant. -/
theorem Reg.DepInv.of_empty {δ : Reg} (hd : ∀ l₁ l₂, ¬ δ.dep l₁ l₂) : Reg.DepInv δ where
  trans   := fun l₁ l₂ _ h₁₂ _ => absurd h₁₂ (hd l₁ l₂)
  defined := fun l₁ l₂ h₁₂ => absurd h₁₂ (hd l₁ l₂)

/-- The invariant only depends on the register's `val` and `dep`. -/
theorem Reg.DepInv.congr {δ δ' : Reg} (hI : Reg.DepInv δ)
    (hv : δ'.val = δ.val) (hd : δ'.dep = δ.dep) : Reg.DepInv δ' where
  trans   := by rw [hd]; exact hI.trans
  defined := by rw [hd, hv]; exact hI.defined

theorem Reg.setDep_self (δ : Reg) (l : Loc) (d : LocSet) : (δ.setDep l d).dep l = d := by
  simp [Reg.setDep]

theorem Reg.setDep_ne (δ : Reg) {a l : Loc} (d : LocSet) (h : a ≠ l) :
    (δ.setDep l d).dep a = δ.dep a := by
  simp [Reg.setDep, h]

/-- `[Binary Operation]` preserves the invariant. -/
theorem Reg.DepInv.binOp {δ : Reg} {l l₁ l₂ : Loc} {v : Val}
    (hI : Reg.DepInv δ) (hl : δ.val l = none)
    (hl₁ : δ.val l₁ ≠ none) (hl₂ : δ.val l₂ ≠ none) :
    Reg.DepInv ((δ.setVal l v).setDep l (δ.dep l₁ ∪ δ.dep l₂ ∪ {l₁, l₂})) := by
  -- every member of the new dependency set holds a value, so is not `l`
  have hdef : ∀ x, (δ.dep l₁ ∪ δ.dep l₂ ∪ {l₁, l₂}) x → δ.val x ≠ none := by
    intro x hx
    rcases mem_binOpDep.1 hx with hx | hx | rfl | rfl
    · exact hI.defined _ _ hx
    · exact hI.defined _ _ hx
    · exact hl₁
    · exact hl₂
  have hne : ∀ x, (δ.dep l₁ ∪ δ.dep l₂ ∪ {l₁, l₂}) x → x ≠ l := by
    intro x hx e
    exact hdef x hx (e ▸ hl)
  have hne' : ∀ a b, δ.dep a b → b ≠ l := by
    intro a b hab e
    exact hI.defined a b hab (e ▸ hl)
  constructor
  · intro a b c hab hbc
    by_cases ea : a = l
    · subst ea
      rw [Reg.setDep_self] at hab ⊢
      rw [Reg.setDep_ne _ _ (hne _ hab)] at hbc
      rcases mem_binOpDep.1 hab with h₁ | h₁ | rfl | rfl
      · exact mem_binOpDep.2 (Or.inl (hI.trans _ _ _ h₁ hbc))
      · exact mem_binOpDep.2 (Or.inr (Or.inl (hI.trans _ _ _ h₁ hbc)))
      · exact mem_binOpDep.2 (Or.inl hbc)
      · exact mem_binOpDep.2 (Or.inr (Or.inl hbc))
    · rw [Reg.setDep_ne _ _ ea] at hab ⊢
      rw [Reg.setDep_ne _ _ (hne' _ _ hab)] at hbc
      exact hI.trans _ _ _ hab hbc
  · intro a b hab
    show (δ.setVal l v).val b ≠ none
    by_cases ea : a = l
    · subst ea
      rw [Reg.setDep_self] at hab
      exact Reg.setVal_defined (hdef _ hab)
    · rw [Reg.setDep_ne _ _ ea] at hab
      exact Reg.setVal_defined (hI.defined _ _ hab)

/-- `[Object Initialization]` preserves the invariant. -/
theorem Reg.DepInv.objLit {δ : Reg} {l : Loc} (hI : Reg.DepInv δ) (hl : δ.val l = none)
    (v : Val) : Reg.DepInv ((δ.setVal l v).setDep l ∅) := by
  have hne' : ∀ a b, δ.dep a b → b ≠ l := by
    intro a b hab e
    exact hI.defined a b hab (e ▸ hl)
  constructor
  · intro a b c hab hbc
    by_cases ea : a = l
    · subst ea
      rw [Reg.setDep_self] at hab
      exact absurd hab id
    · rw [Reg.setDep_ne _ _ ea] at hab ⊢
      rw [Reg.setDep_ne _ _ (hne' _ _ hab)] at hbc
      exact hI.trans _ _ _ hab hbc
  · intro a b hab
    show (δ.setVal l v).val b ≠ none
    by_cases ea : a = l
    · subst ea
      rw [Reg.setDep_self] at hab
      exact absurd hab id
    · rw [Reg.setDep_ne _ _ ea] at hab
      exact Reg.setVal_defined (hI.defined _ _ hab)

/-- Every rule of the concrete semantics preserves the invariant, on finite
    memories. -/
theorem BigStep.depInv [Concrete] (hs : ConcreteSpec) {Γ : Env} {c : Conf} {s : Stmt}
    {r : Res} (hb : Γ ⊢ ⟨c, s⟩ ⇓c r) :
    c.heap.Finite c.reg → Reg.DepInv c.reg → Reg.DepInv r.reg := by
  induction hb with
  | skip => exact fun _ => id
  | assign _ _ => exact fun _ => id
  | @binOp h ρ ρ' δ δ' x κ op e₁ e₂ l₁ l₂ v₁ v₂ l v d _ _ hv₁ hv₂ hl _ _ hd hδ' =>
    intro hF hI
    subst hd hδ'
    have hfr : δ.val l = none := hl ▸ (hs.allocC_fresh h δ κ hF).1
    exact hI.binOp hfr (by simp [hv₁]) (by simp [hv₂])
  | @objLit h h' ρ ρ' δ δ' x κ fs ls l _ hl _ _ hδ' =>
    intro hF hI
    subst hδ'
    have hfr : δ.val l = none := hl ▸ (hs.allocC_fresh h δ κ hF).1
    exact hI.objLit hfr _
  | lookupS _ _ _ => exact fun _ => id
  | lookupD _ _ _ _ _ _ => exact fun _ => id
  | lookupSProto _ _ _ _ _ => exact fun _ => id
  | lookupSMissing _ _ _ _ _ => exact fun _ => id
  | lookupDProto _ _ _ _ _ _ _ _ => exact fun _ => id
  | lookupDMissing _ _ _ _ _ _ _ _ => exact fun _ => id
  | updateS _ _ _ => exact fun _ => id
  | updateD _ _ _ _ _ _ => exact fun _ => id
  | seqRet _ ih => exact ih
  | seqCont hb₁ _ ih₁ ih₂ => exact fun hF hI => ih₂ (hb₁.finite hF) (ih₁ hF hI)
  | callRet _ _ _ _ _ _ _ ih => exact ih
  | callCont _ _ _ _ _ _ _ ih => exact ih
  | ifTrue _ _ _ ih => exact ih
  | ifFalse _ _ _ ih => exact ih
  | whileDo _ ih => exact ih
  | ret _ => exact fun _ => id
  | setTaint _ hδ' => intro _ hI; subst hδ'; exact hI.congr rfl rfl
  | setSink _ hδ' => intro _ hI; subst hδ'; exact hI.congr rfl rfl

/-- **Runs yield well-formed records.**  The execution record of a concrete run has a well-formed
    observation, provided the initial configuration satisfies the invariant
    (for instance, an empty initial `dep`). -/
theorem BigStep.obs_wf [Concrete] (hs : ConcreteSpec) {Γ : Env} {c : Conf} {s : Stmt}
    {r : Res} (hb : Γ ⊢ ⟨c, s⟩ ⇓c r) (hF : c.heap.Finite c.reg) (hI : Reg.DepInv c.reg) :
    (Exec.ofRes r).obs.WF :=
  Obs.WF.ofRun_of_trans (hb.depInv hs hF hI).trans

/-! ### Runs from the initial configuration -/

/-- A run that starts with no dependencies — over *any* finite memory and
    store — has a well-formed observation.  (The register need not be well
    formed in the sense of `Reg.WF`: `dep` starts empty, and freshness of
    allocation is a property of `allocC` on finite memories.) -/
theorem BigStep.obs_wf_empty [Concrete] (hs : ConcreteSpec) {Γ : Env} {h : Heap} {ρ : Sto}
    {δ : Reg} {s : Stmt} {r : Res} (hb : Γ ⊢ ⟨h, ρ, δ, s⟩ ⇓c r) (hF : h.Finite δ)
    (hd : ∀ l₁ l₂, ¬ δ.dep l₁ l₂) : (Exec.ofRes r).obs.WF :=
  hb.obs_wf hs hF (Reg.DepInv.of_empty hd)

/-- **From the initial configuration.**  Starting from the empty heap, the
    empty store and the minimal well-formed register, a concrete run yields a
    well-formed observation. -/
theorem BigStep.obs_wf_init [Concrete] (hs : ConcreteSpec) {Γ : Env} {fs : List Fid}
    {s : Stmt} {r : Res}
    (hb : Γ ⊢ ⟨Conf.init Γ fs s, s⟩ ⇓c r) : (Exec.ofRes r).obs.WF :=
  hb.obs_wf_empty hs (Reg.init_finite Γ fs s) (fun _ _ hd => hd)

end CoreJS
