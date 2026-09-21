/-
  # Core JavaScript — First-Order LTL over Finite Traces

  Syntax and semantics of first-order linear temporal logic (FO-LTL) over
  *finite* traces, with CoreJS actions and taint/value predicates as atoms,
  and the materialisation of an execution record `⟨t, σ⟩`
  (`CoreJsQuerySemantics.lean`) as a model of it.

  ## Conventions

  * **Positions are boundaries** `0 … n`, where `n` is the number of states.
    State `p < n` says which action happens at `p`; boundary `n` is a
    *sentinel* at which no action holds.  This is exactly how the query
    semantics indexes a trace (`a : i ⇝ j` when the event `t[j-1]` is `a`),
    so `F(a ∧ X ⊤)` reads "`a` occurs", `ε` and the empty trace need no
    special case, and `A₁ ; A₂ ≡ F(A₁ ∧ X F A₂)` holds verbatim.
  * `X` is *strong*: `X φ` holds at `i` iff `i < n` and `φ` holds at `i + 1`.
  * `U` is the usual until, over `[i, n]`.  `F φ := ⊤ U φ`, `G φ := ¬F¬φ`.
  * **Action atoms** are predicates of the state: `lookup(x₁,x₂,x₃)` holds at
    `p` iff the action at `p` is the lookup of the locations the variables
    denote.  **State atoms** (`sk`, `ac`, `dep`, `sv`, `hv`, `=`) read only the
    static part `σ` of the model, so they hold at every boundary or at none:
    `G p ≡ p ≡ F p` (`sat_G_state`).
  * First-order variables are *rigid* and range over `Loc`.
  * Multiple actions cannot happen at the same time: `Model.Excl`, and its
    first-order axiomatisation over a finite set of action shapes
    (`Ltl.excl`), which every execution record satisfies
    (`Exec.toModel_excl`, `Exec.toModel_sat_excl`).

  Formulas and atoms are parametric in the type `ν` of variables, so that
  translations can rename variables (e.g. to keep inlined queries apart).

  Plain Lean 4 — no Mathlib required.
-/

import CoreJsQuerySemantics

namespace CoreJS

/-! ## Syntax -/

/-- Atomic predicates over variables of type `ν`: the four kinds of action,
    the taint/value predicates of the query language, and equality. -/
inductive Atom (ν : Type) where
  /-- `x₁ := x₂[x₃]` happens now. -/
  | lookup (x₁ x₂ x₃ : ν)
  /-- `x₁[x₂] := x₃` happens now. -/
  | update (x₁ x₂ x₃ : ν)
  /-- `Call(x_f, [x₁, …, xₙ])` happens now. -/
  | call   (xf : ν) (xs : List ν)
  /-- `Retn(x_f, x)` happens now. -/
  | retn   (xf x : ν)
  | sk (x : ν)
  | ac (x : ν)
  | dep (x₁ x₂ : ν)
  | sv (x₁ x₂ : ν)
  | hv (x : ν) (c : Val)
  /-- `x₁ = x₂`. -/
  | eq (x₁ x₂ : ν)

/-- First-order LTL formulas. -/
inductive Ltl (ν : Type) where
  | atom  (a : Atom ν)
  | tt
  | ff
  | not   (φ : Ltl ν)
  | and   (φ ψ : Ltl ν)
  | or    (φ ψ : Ltl ν)
  /-- `X φ`, strong next. -/
  | next  (φ : Ltl ν)
  /-- `φ U ψ`. -/
  | until (φ ψ : Ltl ν)
  /-- `∃x. φ`. -/
  | ex    (x : ν) (φ : Ltl ν)
  /-- `∀x. φ`. -/
  | all   (x : ν) (φ : Ltl ν)

namespace Ltl

variable {ν : Type}

/-- `F φ := ⊤ U φ`. -/
def F (φ : Ltl ν) : Ltl ν := .until .tt φ

/-- `G φ := ¬F¬φ`. -/
def G (φ : Ltl ν) : Ltl ν := .not (F (.not φ))

/-- `φ → ψ`. -/
def imp (φ ψ : Ltl ν) : Ltl ν := .or (.not φ) ψ

/-- Finite conjunction. -/
def conj : List (Ltl ν) → Ltl ν
  | []     => .tt
  | φ :: l => .and φ (conj l)

/-- Finite disjunction. -/
def disj : List (Ltl ν) → Ltl ν
  | []     => .ff
  | φ :: l => .or φ (disj l)

/-- `∀x₁ … ∀xₙ. φ`. -/
def allN (vs : List ν) (φ : Ltl ν) : Ltl ν := vs.foldr .all φ

/-- `∃x₁ … ∃xₙ. φ`. -/
def exN (vs : List ν) (φ : Ltl ν) : Ltl ν := vs.foldr .ex φ

end Ltl

/-! ## Models -/

/-- A finite FO-LTL model: the actions that hold in each of the `n` states, and
    the static part `σ` interpreting the state predicates. -/
structure Model where
  states : List (Act → Prop)
  obs    : Obs

/-- The number of states `n`; the boundaries are `0 … n`. -/
def Model.len (m : Model) : Nat := m.states.length

/-- The action `a` holds at boundary `i` (never at the sentinel `n`). -/
def Model.holds (m : Model) (i : Nat) (a : Act) : Prop :=
  ∃ s, m.states[i]? = some s ∧ s a

/-- Multiple actions cannot happen at the same time. -/
def Model.Excl (m : Model) : Prop :=
  ∀ i a₁ a₂, m.holds i a₁ → m.holds i a₂ → a₁ = a₂

/-- Valuations `ξ : ν → Loc`, and `ξ[x ↦ l]`. -/
def upd {ν : Type} [DecidableEq ν] (ξ : ν → Loc) (x : ν) (l : Loc) : ν → Loc :=
  fun y => if y = x then l else ξ y

/-! ## Semantics -/

/-- Atoms: `m, ξ, i ⊨ a`. -/
def Atom.Sat {ν : Type} (m : Model) (ξ : ν → Loc) (i : Nat) : Atom ν → Prop
  | .lookup x₁ x₂ x₃ => m.holds i (.lookup (ξ x₁) (ξ x₂) (ξ x₃))
  | .update x₁ x₂ x₃ => m.holds i (.update (ξ x₁) (ξ x₂) (ξ x₃))
  | .call xf xs      => m.holds i (.call (ξ xf) (xs.map ξ))
  | .retn xf x       => m.holds i (.ret (ξ xf) (ξ x))
  | .sk x            => m.obs.sk (ξ x)
  | .ac x            => m.obs.ac (ξ x)
  | .dep x₁ x₂       => m.obs.dep (ξ x₁) (ξ x₂)
  | .sv x₁ x₂        => ∃ v, m.obs.val (ξ x₁) = some v ∧ m.obs.val (ξ x₂) = some v
  | .hv x c          => m.obs.val (ξ x) = some c
  | .eq x₁ x₂        => ξ x₁ = ξ x₂

/-- `m, ξ, i ⊨ φ`, for `i` a boundary `0 … n`. -/
def Ltl.Sat {ν : Type} [DecidableEq ν] (m : Model) : (ν → Loc) → Ltl ν → Nat → Prop
  | ξ, .atom a,    i => a.Sat m ξ i
  | _, .tt,        _ => True
  | _, .ff,        _ => False
  | ξ, .not φ,     i => ¬ φ.Sat m ξ i
  | ξ, .and φ ψ,   i => φ.Sat m ξ i ∧ ψ.Sat m ξ i
  | ξ, .or φ ψ,    i => φ.Sat m ξ i ∨ ψ.Sat m ξ i
  | ξ, .next φ,    i => i < m.len ∧ φ.Sat m ξ (i + 1)
  | ξ, .until φ ψ, i =>
      ∃ k, i ≤ k ∧ k ≤ m.len ∧ ψ.Sat m ξ k ∧ ∀ p, i ≤ p → p < k → φ.Sat m ξ p
  | ξ, .ex x φ,    i => ∃ l, φ.Sat m (upd ξ x l) i
  | ξ, .all x φ,   i => ∀ l, φ.Sat m (upd ξ x l) i

/-- A formula holds in a model iff it holds at the first boundary. -/
def Ltl.Holds {ν : Type} [DecidableEq ν] (m : Model) (ξ : ν → Loc) (φ : Ltl ν) : Prop :=
  φ.Sat m ξ 0

/-! ## Basic facts -/

section facts

variable {ν : Type} [DecidableEq ν] {m : Model} {ξ : ν → Loc} {i : Nat}

theorem Ltl.sat_F {φ : Ltl ν} :
    φ.F.Sat m ξ i ↔ ∃ k, i ≤ k ∧ k ≤ m.len ∧ φ.Sat m ξ k := by
  simp [Ltl.F, Ltl.Sat]

theorem Ltl.sat_G {φ : Ltl ν} :
    φ.G.Sat m ξ i ↔ ∀ k, i ≤ k → k ≤ m.len → φ.Sat m ξ k := by
  simp only [Ltl.G, Ltl.Sat, Ltl.sat_F]
  constructor
  · intro h k hik hk
    exact Classical.byContradiction fun hφ => h ⟨k, hik, hk, hφ⟩
  · rintro h ⟨k, hik, hk, hφ⟩
    exact hφ (h k hik hk)

theorem Ltl.sat_imp {φ ψ : Ltl ν} :
    (φ.imp ψ).Sat m ξ i ↔ (φ.Sat m ξ i → ψ.Sat m ξ i) := by
  simp only [Ltl.imp, Ltl.Sat]
  constructor
  · rintro (h | h) hφ
    · exact absurd hφ h
    · exact h
  · intro h
    by_cases hφ : φ.Sat m ξ i
    · exact Or.inr (h hφ)
    · exact Or.inl hφ

theorem Ltl.sat_conj {l : List (Ltl ν)} :
    (Ltl.conj l).Sat m ξ i ↔ ∀ φ ∈ l, φ.Sat m ξ i := by
  induction l with
  | nil => simp [Ltl.conj, Ltl.Sat]
  | cons φ l ih => simp [Ltl.conj, Ltl.Sat, ih]

theorem Ltl.sat_disj {l : List (Ltl ν)} :
    (Ltl.disj l).Sat m ξ i ↔ ∃ φ ∈ l, φ.Sat m ξ i := by
  induction l with
  | nil => simp [Ltl.disj, Ltl.Sat]
  | cons φ l ih => simp [Ltl.disj, Ltl.Sat, ih]

theorem Ltl.sat_allN_of {vs : List ν} {φ : Ltl ν}
    (h : ∀ ξ', φ.Sat m ξ' i) : (Ltl.allN vs φ).Sat m ξ i := by
  induction vs generalizing ξ with
  | nil => exact h ξ
  | cons v vs ih => intro l; exact ih

/-- `X ⊤` holds exactly before the sentinel. -/
theorem Ltl.sat_next_tt : (Ltl.next (Ltl.tt : Ltl ν)).Sat m ξ i ↔ i < m.len := by
  simp [Ltl.Sat]

/-- Action atoms never hold at the sentinel: they hold only at a state. -/
def Atom.IsAction {ν : Type} : Atom ν → Prop
  | .lookup .. | .update .. | .call .. | .retn .. => True
  | _ => False

omit [DecidableEq ν] in
theorem Atom.sat_action_lt {a : Atom ν} (ha : a.IsAction) (h : a.Sat m ξ i) : i < m.len := by
  have hh : ∀ act, m.holds i act → i < m.len := by
    rintro act ⟨s, hs, _⟩
    exact (List.getElem?_eq_some_iff.1 hs).1
  cases a <;> simp [Atom.IsAction] at ha <;> exact hh _ h

omit [DecidableEq ν] in
/-- State atoms read only the static part of the model, hence hold at every boundary
    or at none. -/
theorem Atom.sat_state_indep {a : Atom ν} (ha : ¬ a.IsAction) {i i' : Nat} :
    a.Sat m ξ i ↔ a.Sat m ξ i' := by
  cases a <;> simp [Atom.IsAction] at ha <;> simp [Atom.Sat]

/-- `G p ≡ p` for a state atom `p`, at any boundary of the model. -/
theorem Ltl.sat_G_state {a : Atom ν} (ha : ¬ a.IsAction) (hi : i ≤ m.len) :
    (Ltl.G (.atom a)).Sat m ξ i ↔ a.Sat m ξ i := by
  rw [Ltl.sat_G]
  constructor
  · intro h; exact h i (Nat.le_refl _) hi
  · intro h k _ _
    exact (Atom.sat_state_indep ha).1 h

/-- `F p ≡ p` for a state atom `p`, at any boundary of the model. -/
theorem Ltl.sat_F_state {a : Atom ν} (ha : ¬ a.IsAction) (hi : i ≤ m.len) :
    (Ltl.F (.atom a)).Sat m ξ i ↔ a.Sat m ξ i := by
  rw [Ltl.sat_F]
  constructor
  · rintro ⟨k, _, _, h⟩; exact (Atom.sat_state_indep ha).1 h
  · intro h; exact ⟨i, Nat.le_refl _, hi, h⟩

/-- For an action atom, `F(a ∧ X ⊤)` is just `F a`: an action at `p` implies `p + 1` exists. -/
theorem Ltl.sat_F_action_next {a : Atom ν} (ha : a.IsAction) :
    (Ltl.F (.and (.atom a) (.next .tt))).Sat m ξ i ↔ (Ltl.F (.atom a)).Sat m ξ i := by
  simp only [Ltl.sat_F, Ltl.Sat]
  constructor
  · rintro ⟨k, h₁, h₂, h₃, _⟩; exact ⟨k, h₁, h₂, h₃⟩
  · rintro ⟨k, h₁, h₂, h₃⟩
    exact ⟨k, h₁, h₂, h₃, Atom.sat_action_lt ha h₃, trivial⟩

end facts

/-! ## Execution records as models -/

/-- Materialise an execution record: the trace becomes a list of states, each
    holding exactly the one action performed there, and the observation
    becomes the static part. -/
def Exec.toModel (e : Exec) : Model where
  states := e.trc.toList.map fun a => fun a' => a' = a
  obs    := e.obs

theorem Exec.toModel_len (e : Exec) : e.toModel.len = e.trc.toList.length := by
  simp [Exec.toModel, Model.len]

theorem Exec.holds_toModel (e : Exec) (i : Nat) (a : Act) :
    e.toModel.holds i a ↔ e.trc.toList[i]? = some a := by
  simp only [Model.holds, Exec.toModel, List.getElem?_map]
  constructor
  · rintro ⟨s, hs, ha⟩
    cases h : e.trc.toList[i]? with
    | none => simp [h] at hs
    | some b =>
      simp [h] at hs
      subst hs
      rw [ha]
  · intro h
    exact ⟨fun a' => a' = a, by simp [h], rfl⟩

/-- Multiple actions cannot happen at the same time: an execution record's model is exclusive. -/
theorem Exec.toModel_excl (e : Exec) : e.toModel.Excl := by
  intro i a₁ a₂ h₁ h₂
  rw [Exec.holds_toModel] at h₁ h₂
  rw [h₁] at h₂
  exact (Option.some.inj h₂)

/-! ## Exclusivity as a formula

`Shape`s are the actions up to their arguments (calls are told apart by arity),
so that exclusivity can be axiomatised by a *finite* first-order formula over
the shapes that occur in a query. -/

/-- The shape of an action: its kind, and for calls its arity. -/
inductive Shape where
  | lookup
  | update
  | call (n : Nat)
  | retn
  deriving DecidableEq, Repr

/-- Number of arguments of an action of this shape. -/
def Shape.arity : Shape → Nat
  | .lookup => 3
  | .update => 3
  | .call n => n + 1
  | .retn   => 2

/-- The atom of this shape over the variables `x 0, x 1, …`. -/
def Shape.atom {ν : Type} : Shape → (Nat → ν) → Atom ν
  | .lookup, x => .lookup (x 0) (x 1) (x 2)
  | .update, x => .update (x 0) (x 1) (x 2)
  | .call n, x => .call (x 0) ((List.range n).map fun k => x (k + 1))
  | .retn,   x => .retn (x 0) (x 1)

/-- The action of this shape with arguments `l 0, l 1, …`. -/
def Shape.act : Shape → (Nat → Loc) → Act
  | .lookup, l => .lookup (l 0) (l 1) (l 2)
  | .update, l => .update (l 0) (l 1) (l 2)
  | .call n, l => .call (l 0) ((List.range n).map fun k => l (k + 1))
  | .retn,   l => .ret (l 0) (l 1)

theorem Atom.sat_shape {ν : Type} (m : Model) (ξ : ν → Loc) (i : Nat) (s : Shape) (x : Nat → ν) :
    (s.atom x).Sat m ξ i ↔ m.holds i (s.act fun k => ξ (x k)) := by
  cases s <;> simp [Shape.atom, Shape.act, Atom.Sat, List.map_map, Function.comp_def]

theorem map_range_eq {f g : Nat → Loc} {n : Nat}
    (h : (List.range n).map f = (List.range n).map g) : ∀ k, k < n → f k = g k := by
  intro k hk
  have := congrArg (fun l => l[k]?) h
  simpa [List.getElem?_map, List.getElem?_range, hk] using this

/-- Actions of the same shape with equal arguments... and conversely: equal actions have
    equal shapes and equal arguments (below the arity). -/
theorem Shape.act_eq {s s' : Shape} {l l' : Nat → Loc} (h : s.act l = s'.act l') :
    s = s' ∧ ∀ k, k < s.arity → l k = l' k := by
  cases s <;> cases s' <;> simp [Shape.act, Shape.arity] at h ⊢
  · obtain ⟨h0, h1, h2⟩ := h
    intro k hk
    match k, hk with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
  · obtain ⟨h0, h1, h2⟩ := h
    intro k hk
    match k, hk with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
  · obtain ⟨h0, h1⟩ := h
    have hlen := congrArg List.length h1
    simp only [List.length_map, List.length_range] at hlen
    refine ⟨hlen, ?_⟩
    subst hlen
    intro k hk
    cases k with
    | zero => exact h0
    | succ k => exact map_range_eq h1 k (by omega)
  · obtain ⟨h0, h1⟩ := h
    intro k hk
    match k, hk with
    | 0, _ => exact h0
    | 1, _ => exact h1

/-- For two shapes: the corresponding atoms, over the disjoint variable families
    `v 0, v 2, …` and `v 1, v 3, …`, do not hold together at one state unless the shapes
    are equal and all arguments coincide.  Universally quantified over the arguments. -/
def Shape.pairExcl {ν : Type} (v : Nat → ν) (s s' : Shape) : Ltl ν :=
  let x := fun k => v (2 * k)
  let y := fun k => v (2 * k + 1)
  Ltl.allN (((List.range s.arity).map x) ++ ((List.range s'.arity).map y))
    (.not (.and (.atom (s.atom x)) (.and (.atom (s'.atom y))
      (if s = s' then
        .not (Ltl.conj ((List.range s.arity).map fun k => .atom (.eq (x k) (y k))))
       else .tt))))

/-- *Multiple actions cannot happen at the same time*, over the given shapes: at every
    boundary, no two different actions of these shapes hold together.  `v` supplies the
    (distinct) names of the bound variables. -/
def Ltl.excl {ν : Type} (v : Nat → ν) (shapes : List Shape) : Ltl ν :=
  Ltl.G (Ltl.conj (shapes.flatMap fun s => shapes.map fun s' => Shape.pairExcl v s s'))

theorem Shape.sat_pairExcl {ν : Type} [DecidableEq ν] {m : Model} (hm : m.Excl) (v : Nat → ν)
    (s s' : Shape) (ξ : ν → Loc) (i : Nat) : (Shape.pairExcl v s s').Sat m ξ i := by
  apply Ltl.sat_allN_of
  intro ξ'
  rintro ⟨hA, hB, hC⟩
  have hA' := (Atom.sat_shape m ξ' i s _).1 hA
  have hB' := (Atom.sat_shape m ξ' i s' _).1 hB
  obtain ⟨rfl, hargs⟩ := Shape.act_eq (hm i _ _ hA' hB')
  rw [if_pos rfl] at hC
  refine hC (Ltl.sat_conj.2 ?_)
  intro φ hφ
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hφ
  exact hargs k (List.mem_range.1 hk)

/-- Every exclusive model satisfies the exclusivity formula, for any set of shapes. -/
theorem Model.Excl.sat_excl {ν : Type} [DecidableEq ν] {m : Model} (hm : m.Excl) (v : Nat → ν)
    (shapes : List Shape) (ξ : ν → Loc) (i : Nat) : (Ltl.excl v shapes).Sat m ξ i := by
  rw [Ltl.excl, Ltl.sat_G]
  intro k _ _
  rw [Ltl.sat_conj]
  intro φ hφ
  obtain ⟨s, _, hφ⟩ := List.mem_flatMap.1 hφ
  obtain ⟨s', _, rfl⟩ := List.mem_map.1 hφ
  exact Shape.sat_pairExcl hm v s s' ξ k

/-- The model of an execution record satisfies the exclusivity formula. -/
theorem Exec.toModel_sat_excl {ν : Type} [DecidableEq ν] (e : Exec) (v : Nat → ν)
    (shapes : List Shape) (ξ : ν → Loc) : (Ltl.excl v shapes).Holds e.toModel ξ :=
  (Exec.toModel_excl e).sat_excl v shapes ξ 0

end CoreJS
