/-
  # Core JavaScript — Model checking: the abstraction interface

  What model checking a query model (`Queries/QueryModel/`) needs from an
  abstraction of a program, stated independently of any particular
  abstraction, and the *abstract semantics* of query models that model
  checking decides.

  * **Trace systems** (`TSys`): states, an initial state, final states, and
    edges labeled by abstract actions `A` or silent (`none`).  A walk from the
    initial to a final state yields an *abstract execution record*: its
    visible labels, together with the abstract facts `φ : Φ` about the final
    observation.
  * **Abstractions** (`Abs`): how concrete actions and observations relate to
    abstract ones (`act`, `facts`, through a map `α : Loc → V` of locations to
    abstract values `V`), and the abstract judgements a model checker
    evaluates: matching a query action against an abstract action, in two
    polarities (`matchA`: possibly; `mustA`: certainly, for every action and
    every assignment the abstract ones stand for), predicates likewise —
    `may` (possibly true) and `must` (certainly true) — and `inhab`: an
    abstract value certainly denotes some location.  `Abs.Sound` is the specification relating them:
    abstract judgements over-approximate (`may`, `matchA`) or
    under-approximate (`must`, `mustA`) the concrete ones.
  * **Coverage** (`Covers`): every concrete record of interest (e.g. every
    run of a program) is abstracted by the record of some walk.  This is the
    shape of the program automaton's soundness theorem (`sound_top`).
  * Invariants are evaluated by polarity (`Abs.inv`): a negation flips it, so
    a negative literal in positive position is only false when its predicate
    *must* hold.

  The abstract semantics of a query model (`QModel.ASat`) asks for a walk and
  an abstract assignment under which `main` accepts the walk's record in
  *may* polarity, while no `except` component of the final state reached
  accepts the *same* record in *must* polarity (`QComp.AMust`), with its own
  variables re-chosen.  The polarity flip is forced by completeness: an
  `except` may only exclude a candidate when the excluded pattern certainly
  occurs.  `QModel.asat_of_matches`: a concrete record matching the query,
  and covered by the abstraction, makes it hold — model checking against the
  abstraction is complete.

  Plain Lean 4 — no Mathlib required.
-/

import Queries.QueryModel.CoreJsQueryToQModel

namespace CoreJS

/-! ## Trace systems -/

/-- A trace system over abstract actions `A`. -/
structure TSys (A : Type) where
  St    : Type
  init  : St
  final : St → Prop
  /-- `edge s none s'` is a silent edge; `edge s (some a) s'` reads `a`. -/
  edge  : St → Option A → St → Prop

/-- `S.Walk s T s'`: a walk from `s` to `s'` whose visible labels are `T`. -/
inductive TSys.Walk {A : Type} (S : TSys A) : S.St → List A → S.St → Prop where
  | nil {s} : S.Walk s [] s
  | silent {s s' s'' T} : S.edge s none s' → S.Walk s' T s'' → S.Walk s T s''
  | vis {s s' s'' a T} : S.edge s (some a) s' → S.Walk s' T s'' → S.Walk s (a :: T) s''

/-! ## Abstractions -/

/-- Two lists related position by position. -/
def Pointwise {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [],      []      => True
  | a :: as, b :: bs => R a b ∧ Pointwise R as bs
  | _,       _       => False

theorem Pointwise.length {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Pointwise R as bs → as.length = bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [Pointwise.length h.2]

theorem Pointwise.drop {α β : Type} {R : α → β → Prop} :
    ∀ (i : Nat) {as : List α} {bs : List β}, Pointwise R as bs →
      Pointwise R (as.drop i) (bs.drop i)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | i + 1, _ :: _, _ :: _, h => Pointwise.drop i h.2

/-- An abstraction of concrete records by abstract ones, over abstract
    actions `A`, abstract values `V` and abstract facts `Φ`. -/
structure Abs (A V Φ : Type) where
  /-- The concrete action is abstracted by the abstract one, under `α`. -/
  act    : (Loc → V) → Act → A → Prop
  /-- The concrete observation is abstracted by the facts, under `α`. -/
  facts  : (Loc → V) → Obs → Φ → Prop
  /-- The query action may denote an action abstracted by `A`. -/
  matchA : (MVar → V) → QAct MVar → A → Bool
  /-- The predicate may hold. -/
  may    : Φ → (MVar → V) → Pred MVar → Bool
  /-- The predicate must hold. -/
  must   : Φ → (MVar → V) → Pred MVar → Bool
  /-- Every action abstracted by `A` is the query action, under every
      assignment of locations abstracted by the abstract assignment (and
      there is one). -/
  mustA  : (MVar → V) → QAct MVar → A → Bool
  /-- The abstract value certainly abstracts some location. -/
  inhab  : Φ → V → Bool

variable {A V Φ : Type}

/-- The specification of an abstraction. -/
structure Abs.Sound (𝔄 : Abs A V Φ) : Prop where
  matchA : ∀ (α : Loc → V) (ξ : MEnv) (a : QAct MVar) (c : Act) (B : A),
    𝔄.act α c B → c = a.inst ξ → 𝔄.matchA (α ∘ ξ) a B = true
  may : ∀ (α : Loc → V) σ φ (ξ : MEnv) (p : Pred MVar),
    𝔄.facts α σ φ → Pred.Sat σ ξ p → 𝔄.may φ (α ∘ ξ) p = true
  must : ∀ (α : Loc → V) σ φ (ξ : MEnv) (p : Pred MVar),
    𝔄.facts α σ φ → 𝔄.must φ (α ∘ ξ) p = true → Pred.Sat σ ξ p
  may_congr : ∀ φ (ξ ξ' : MVar → V) (p : Pred MVar),
    (∀ x ∈ p.vars, ξ x = ξ' x) → 𝔄.may φ ξ p = 𝔄.may φ ξ' p
  must_congr : ∀ φ (ξ ξ' : MVar → V) (p : Pred MVar),
    (∀ x ∈ p.vars, ξ x = ξ' x) → 𝔄.must φ ξ p = 𝔄.must φ ξ' p
  mustA : ∀ (α : Loc → V) (ξ : MVar → V) (b : QAct MVar) (c : Act) (B : A),
    𝔄.act α c B → 𝔄.mustA ξ b B = true →
      (∀ x ∈ b.vars, ∃ l, α l = ξ x) ∧
      ∀ ξc : MEnv, (∀ x ∈ b.vars, α (ξc x) = ξ x) → c = b.inst ξc
  mustA_congr : ∀ (ξ ξ' : MVar → V) (b : QAct MVar) (B : A),
    (∀ x ∈ b.vars, ξ x = ξ' x) → 𝔄.mustA ξ b B = 𝔄.mustA ξ' b B
  inhab : ∀ (α : Loc → V) σ φ v, 𝔄.facts α σ φ → 𝔄.inhab φ v = true → ∃ l, α l = v

/-- Invariants in polarity `pol`: `true` = may hold, `false` = must hold. -/
def Abs.inv (𝔄 : Abs A V Φ) (φ : Φ) (ξ : MVar → V) : Bool → Inv MVar → Bool
  | pol,   .pred p    => if pol then 𝔄.may φ ξ p else 𝔄.must φ ξ p
  | pol,   .not I     => !(𝔄.inv φ ξ (!pol) I)
  | pol,   .or I₁ I₂  => 𝔄.inv φ ξ pol I₁ || 𝔄.inv φ ξ pol I₂
  | pol,   .and I₁ I₂ => 𝔄.inv φ ξ pol I₁ && 𝔄.inv φ ξ pol I₂
  | _,     .tt        => true
  | _,     .ff        => false

/-- Concrete truth implies *may*; *must* implies concrete truth. -/
theorem Abs.inv_sound {𝔄 : Abs A V Φ} (h𝔄 : 𝔄.Sound) {α : Loc → V} {σ : Obs} {φ : Φ}
    (hf : 𝔄.facts α σ φ) (ξ : MEnv) :
    ∀ I : Inv MVar, (Inv.Sat σ ξ I → 𝔄.inv φ (α ∘ ξ) true I = true) ∧
      (𝔄.inv φ (α ∘ ξ) false I = true → Inv.Sat σ ξ I)
  | .pred p => ⟨fun h => by simpa [Abs.inv] using h𝔄.may α σ φ ξ p hf h,
      fun h => h𝔄.must α σ φ ξ p hf (by simpa [Abs.inv] using h)⟩
  | .not I => by
      obtain ⟨h₁, h₂⟩ := Abs.inv_sound h𝔄 hf ξ I
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp only [Abs.inv, Bool.not_true, Bool.not_eq_eq_eq_not]
        cases hI : 𝔄.inv φ (α ∘ ξ) false I
        · rfl
        · exact absurd (h₂ hI) h
      · simp only [Abs.inv, Bool.not_false, Bool.not_eq_eq_eq_not, Bool.not_true] at h
        intro hs; rw [h₁ hs] at h; cases h
  | .or I₁ I₂ => by
      obtain ⟨a₁, b₁⟩ := Abs.inv_sound h𝔄 hf ξ I₁
      obtain ⟨a₂, b₂⟩ := Abs.inv_sound h𝔄 hf ξ I₂
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases h with h | h <;> simp [Abs.inv, a₁, a₂, h]
      · simp only [Abs.inv, Bool.or_eq_true] at h
        exact h.elim (fun h => Or.inl (b₁ h)) (fun h => Or.inr (b₂ h))
  | .and I₁ I₂ => by
      obtain ⟨a₁, b₁⟩ := Abs.inv_sound h𝔄 hf ξ I₁
      obtain ⟨a₂, b₂⟩ := Abs.inv_sound h𝔄 hf ξ I₂
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp [Abs.inv, a₁ h.1, a₂ h.2]
      · simp only [Abs.inv, Bool.and_eq_true] at h
        exact ⟨b₁ h.1, b₂ h.2⟩
  | .tt => ⟨fun _ => rfl, fun _ => trivial⟩
  | .ff => ⟨fun h => h.elim, fun h => by simp [Abs.inv] at h⟩

/-- Invariants only read their own variables. -/
theorem Abs.inv_congr {𝔄 : Abs A V Φ} (h𝔄 : 𝔄.Sound) (φ : Φ) {ξ ξ' : MVar → V} :
    ∀ (pol : Bool) (I : Inv MVar), (∀ x ∈ I.vars, ξ x = ξ' x) →
      𝔄.inv φ ξ pol I = 𝔄.inv φ ξ' pol I
  | pol, .pred p, h => by
      cases pol <;> simp [Abs.inv, h𝔄.may_congr φ ξ ξ' p h, h𝔄.must_congr φ ξ ξ' p h]
  | pol, .not I, h => by simp [Abs.inv, Abs.inv_congr h𝔄 φ (!pol) I h]
  | pol, .or I₁ I₂, h => by
      simp only [Abs.inv]
      rw [Abs.inv_congr h𝔄 φ pol I₁ (fun x hx => h x (by simp [Inv.vars, hx])),
        Abs.inv_congr h𝔄 φ pol I₂ (fun x hx => h x (by simp [Inv.vars, hx]))]
  | pol, .and I₁ I₂, h => by
      simp only [Abs.inv]
      rw [Abs.inv_congr h𝔄 φ pol I₁ (fun x hx => h x (by simp [Inv.vars, hx])),
        Abs.inv_congr h𝔄 φ pol I₂ (fun x hx => h x (by simp [Inv.vars, hx]))]
  | _, .tt, _ => rfl
  | _, .ff, _ => rfl

/-- The record `e` is abstracted by the visible labels `T` and the facts `φ`. -/
def RecAbs (𝔄 : Abs A V Φ) (α : Loc → V) (e : Exec) (T : List A) (φ : Φ) : Prop :=
  Pointwise (𝔄.act α) e.trc.toList T ∧ 𝔄.facts α e.obs φ

/-- Every record satisfying `R` is abstracted by the record of a walk from the
    initial to a final state, with the facts `φ`. -/
def Covers (S : TSys A) (𝔄 : Abs A V Φ) (φ : Φ) (R : Exec → Prop) : Prop :=
  ∀ e, R e → ∃ (T : List A) (s : S.St) (α : Loc → V),
    S.Walk S.init T s ∧ S.final s ∧ RecAbs 𝔄 α e T φ

/-! ## Runs of a component over a list of labels

`Run` (`CoreJsQModelSemantics.lean`) reads a concrete trace by position;
model checking reads lists of abstract actions, front to back.  `LRun` is the
same notion over any alphabet, with the firing of an action edge given as a
parameter. -/

/-- `LRun es F s w s'`: the edges `es` lead from `s` to `s'` reading `w`, an
    edge `act as` reading `a` when `F as a`. -/
inductive LRun {α : Type} (es : List QEdge) (F : List (QAct MVar) → α → Prop) :
    QSt → List α → QSt → Prop where
  | nil {s} : LRun es F s [] s
  | eps {s s' s'' w} : (s, .eps, s') ∈ es → LRun es F s' w s'' → LRun es F s w s''
  | act {s s' s'' as a w} :
      (s, .act as, s') ∈ es → F as a → LRun es F s' w s'' → LRun es F s (a :: w) s''

/-- A concrete run, read through a position-by-position abstraction of the
    trace. -/
theorem Run.toLRun {es : List QEdge} {t : List Act} {ξ : MEnv} {R : Act → A → Prop}
    {F : List (QAct MVar) → A → Prop}
    (hF : ∀ as c B, (∀ b ∈ as, c = b.inst ξ) → R c B → F as B) {T : List A}
    (hT : Pointwise R t T) {s s' : QSt} {i j : Nat} (h : Run es t ξ s i s' j) :
    j = t.length → LRun es F s (T.drop i) s' := by
  induction h with
  | @refl s i =>
    intro hj; subst hj
    have : T.drop t.length = [] := by simp [← hT.length]
    rw [this]; exact .nil
  | eps he _ ih => exact fun hj => .eps he (ih hj)
  | @act s₀ s₁ s₂ as i j he hi hb _ ih =>
    intro hj
    have hiT : i < T.length := hT.length ▸ hi
    rw [List.drop_eq_getElem_cons hiT]
    have hpw := hT.drop i
    rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hiT] at hpw
    refine .act he (hF as _ _ (fun b hb' => ?_) hpw.1) (ih hj)
    have := hb b hb'
    rw [List.getElem?_eq_getElem hi] at this
    exact Option.some.inj this

/-- A run over abstract labels, read through a position-by-position
    abstraction of a concrete trace, is a concrete run, provided every action
    abstracted by a label fired must be the edge's actions under `ξ`. -/
theorem LRun.toRun {es : List QEdge} {t : List Act} {ξ : MEnv} {R : Act → A → Prop}
    {F : List (QAct MVar) → A → Prop}
    (hF : ∀ as c B, F as B → R c B → ∀ b ∈ as, c = b.inst ξ) {T : List A}
    (hT : Pointwise R t T) {s s' : QSt} {w : List A} (h : LRun es F s w s') :
    ∀ i, T.drop i = w → i ≤ t.length → Run es t ξ s i s' t.length := by
  induction h with
  | nil =>
    intro i hi hle
    have : T.length ≤ i := List.drop_eq_nil_iff.1 hi
    have : i = t.length := by have := hT.length; omega
    subst this; exact .refl
  | eps he _ ih => exact fun i hi hle => .eps he (ih i hi hle)
  | @act s₀ s₁ s₂ as a w he hf _ ih =>
    intro i hi hle
    have hiT : i < T.length := by
      rcases Nat.lt_or_ge i T.length with h | h
      · exact h
      · rw [List.drop_eq_nil_of_le h] at hi; cases hi
    have hit : i < t.length := hT.length ▸ hiT
    rw [List.drop_eq_getElem_cons hiT] at hi
    simp only [List.cons.injEq] at hi
    obtain ⟨rfl, hw⟩ := hi
    have hpw := hT.drop i
    rw [List.drop_eq_getElem_cons hit, List.drop_eq_getElem_cons hiT] at hpw
    refine .act he hit (fun b hb => ?_) (ih (i + 1) (by rw [← List.drop_drop]; simp [List.drop_eq_getElem_cons hiT, hw]) hit)
    rw [List.getElem?_eq_getElem hit, hF as _ _ hf hpw.1 b hb]

/-- A run of `es`, whose invariants grow along edges, ends with more invariants
    than it started with. -/
theorem LRun.inv_mono {α : Type} {c : QComp} (hm : c.Mono) {F : List (QAct MVar) → α → Prop}
    {s s' : QSt} {w : List α} (h : LRun c.edges F s w s') : c.inv s ⊆ c.inv s' := by
  induction h with
  | nil => exact List.Subset.refl _
  | eps he _ ih => exact fun _ hx => ih ((hm _ _ _ he).1 hx)
  | act he _ _ ih => exact fun _ hx => ih ((hm _ _ _ he).1 hx)

/-- Runs only depend on how the action edges of `es` fire. -/
theorem LRun.mono_fires {α : Type} {es : List QEdge} {F G : List (QAct MVar) → α → Prop}
    (hFG : ∀ s as s' a, (s, .act as, s') ∈ es → F as a → G as a) {s s' : QSt} {w : List α}
    (h : LRun es F s w s') : LRun es G s w s' := by
  induction h with
  | nil => exact .nil
  | eps he _ ih => exact .eps he ih
  | act he hf _ ih => exact .act he (hFG _ _ _ _ he hf) ih

/-! ## Abstract semantics -/

/-- The firing of an action edge on an abstract action, under `ξ`: each
    action *may* match. -/
def Abs.Fires (𝔄 : Abs A V Φ) (ξ : MVar → V) (as : List (QAct MVar)) (B : A) : Prop :=
  ∀ b ∈ as, 𝔄.matchA ξ b B = true

/-- Each action *must* match. -/
def Abs.MustFires (𝔄 : Abs A V Φ) (ξ : MVar → V) (as : List (QAct MVar)) (B : A) : Prop :=
  ∀ b ∈ as, 𝔄.mustA ξ b B = true

/-- The component `c` *must* accept the labels `T` under `ξ`: for some final
    state `f` and new values of `f`'s scope, `c` reads `T` to `f` with every
    action edge must-firing, the invariants of `f` must hold, and the new
    values of the variables they read certainly denote locations.  A final
    state with `except`s of its own is never used (it would need trackers of
    trackers, the polarity flipping again): this only ever accepts less. -/
def QComp.AMust (c : QComp) (𝔄 : Abs A V Φ) (φ : Φ) (T : List A) (ξ : MVar → V) : Prop :=
  ∃ f ∈ c.finals, c.exc f = [] ∧ ∃ ξ' : MVar → V, (∀ v, v ∉ c.scope f → ξ' v = ξ v) ∧
    LRun c.edges (𝔄.MustFires ξ') c.start T f ∧ (∀ J ∈ c.inv f, 𝔄.inv φ ξ' false J = true) ∧
    ∀ x ∈ c.scope f, x ∈ (c.inv f).flatMap Inv.vars → 𝔄.inhab φ (ξ' x) = true

/-- `except` component `k` of `M` must accept `T` under `ξ` (at depth `0`,
    like `compSat`, no component is ever satisfied). -/
def QModel.AExcl (M : QModel) (𝔄 : Abs A V Φ) (φ : Φ) (T : List A) (k : Nat)
    (ξ : MVar → V) : Prop :=
  M.depth ≠ 0 ∧ ∃ c, M.comps[k]? = some c ∧ c.AMust 𝔄 φ T ξ

/-- The abstract semantics of `M`: for the record of some walk of `S` and some
    abstract assignment, `main` reads the walk's labels to a final state whose
    invariants may hold, and no `except` component of that state must accept
    the same labels.  Polarity flips at the `except`: a candidate is excluded
    only when the excluded pattern certainly occurs. -/
def QModel.ASat (M : QModel) (S : TSys A) (𝔄 : Abs A V Φ) (φ : Φ) : Prop :=
  ∃ (T : List A) (s : S.St), S.Walk S.init T s ∧ S.final s ∧
    ∃ f ∈ M.main.finals, ∃ ξ : MVar → V,
      LRun M.main.edges (𝔄.Fires ξ) M.main.start T f ∧
      (∀ J ∈ M.main.inv f, 𝔄.inv φ ξ true J = true) ∧ ∀ k ∈ M.main.exc f, ¬ M.AExcl 𝔄 φ T k ξ

/-- A component must-accepting the abstraction of a record accepts the record
    itself, under any assignment abstracted by the abstract one. -/
theorem QComp.AMust.acc {𝔄 : Abs A V Φ} (h𝔄 : 𝔄.Sound) {α : Loc → V} {e : Exec} {T : List A}
    {φ : Φ} (hrec : RecAbs 𝔄 α e T φ) {c : QComp} {ξ : MEnv} (h : c.AMust 𝔄 φ T (α ∘ ξ))
    (X : Nat → MEnv → Prop) :
    c.Acc e.trc.toList e.obs X ξ 0 e.trc.toList.length := by
  classical
  obtain ⟨f, hf, hexc, ξa, hout, hrun, hinv, hinh⟩ := h
  -- New concrete values: a location abstracted by the new abstract value,
  -- where there is one.
  let ξ' : MEnv := fun x =>
    if x ∈ c.scope f then (if h : ∃ l, α l = ξa x then Classical.choose h else ξ x) else ξ x
  have hα : ∀ x, (x ∈ c.scope f → ∃ l, α l = ξa x) → α (ξ' x) = ξa x := by
    intro x hx
    by_cases hs : x ∈ c.scope f
    · have hex := hx hs
      simp only [ξ', hs, if_true, dif_pos hex]
      exact Classical.choose_spec hex
    · simp only [ξ', hs, if_false]; exact (hout x hs).symm
  refine ⟨f, hf, ξ', fun v hv => by simp [ξ', hv], ?_, fun J hJ => ?_, by simp [hexc]⟩
  · refine LRun.toRun (R := 𝔄.act α) (fun as cA B hF hR b hb => ?_) hrec.1 hrun 0 rfl (Nat.zero_le _)
    obtain ⟨hex, huniq⟩ := h𝔄.mustA α ξa b cA B hR (hF b hb)
    exact huniq ξ' fun x hx => hα x fun _ => hex x hx
  · refine (Abs.inv_sound h𝔄 hrec.2 ξ' J).2 ?_
    rw [Abs.inv_congr h𝔄 φ false J (ξ := α ∘ ξ') (ξ' := ξa) (fun x hx => hα x fun hs =>
      h𝔄.inhab α _ φ _ hrec.2 (hinh x hs (List.mem_flatMap.2 ⟨J, hJ, hx⟩)))]
    exact hinv J hJ

/-- **Completeness of the abstraction.** A record matching the query, and
    covered by the abstraction, makes the abstract semantics of its model
    hold. -/
theorem QModel.asat_of_matches {𝔄 : Abs A V Φ} (h𝔄 : 𝔄.Sound) {S : TSys A} {φ : Φ}
    {R : Exec → Prop} (hcov : Covers S 𝔄 φ R) {Δ : QProg} {q : Query} (hwf : QProg.WF (q :: Δ))
    {e : Exec} (he : R e) {ls : List Loc} (hlen : ls.length = q.params.length)
    (hm : Exec.Matches (q :: Δ) e q.name ls) : (q.toQModel Δ).ASat S 𝔄 φ := by
  obtain ⟨f, hf, ξ, _, hrun, hinv, hexc⟩ := (Query.toQModel_correct hwf e hlen).2 hm
  obtain ⟨T, s, α, hw, hs, hrec⟩ := hcov e he
  refine ⟨T, s, hw, hs, f, hf, α ∘ ξ, ?_, fun J hJ => (Abs.inv_sound h𝔄 hrec.2 ξ J).1 (hinv J hJ),
    fun k hk ⟨hd, c, hc, hmust⟩ => hexc k hk ?_⟩
  · have := Run.toLRun (F := 𝔄.Fires (α ∘ ξ))
      (fun as c B hc hB b hb => h𝔄.matchA α ξ b c B hB (hc b hb)) hrec.1 hrun rfl
    simpa using this
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hd
    rw [hn]
    exact ⟨c, hc, hmust.acc h𝔄 hrec _⟩

end CoreJS
