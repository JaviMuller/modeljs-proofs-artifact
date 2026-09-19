/-
  # Core JavaScript — Query Semantics over Execution Records

  Satisfaction of queries (`CoreJsQuerySyntax.lean`) over *execution records*
  `⟨t, σ⟩`: a concrete trace `t` together with an observation `σ` of it.  The
  semantics is defined for any record, whether or not it was produced by the
  concrete semantics (`CoreJsSemantics.lean`); `Obs.ofRun` shows how a
  concrete run's final heap and taint register yield an observation.

  The relations follow Fig. 5 of the paper:

  * `Inv.Sat σ ξ I`                       — `σ, ξ ⊨ I`
  * `Pat.Sat Θ t σ ξ F i j`               — `t, σ, ξ ⊨ F : i ⇝ j`
  * `Guarded.Sat Θ t σ ξ P i j`           — the same for guarded patterns
  * `Δ ⊢ t, σ, ξ ⊨ F : i ⇝ j`             — `Pat.Sat` with query invocations
                                            resolved in the program `Δ`

  `t, σ, ξ ⊨ F : i ⇝ j` reads: starting after position `i` of the trace,
  `F` is performed, and the last action it uses is `t[j-1]` (so `j` is one
  past it; `j = i` if `F` uses no action).

  Differences from the figure as printed (all deliberate):

  * `F₁ & F₂ : i ⇝ j` requires *both* patterns to match from `i`, ending at
    `j₁` and `j₂`, and `j = max j₁ j₂`.  A single trace action may serve both
    sides, so `a & a` is matched whenever `a` is.
  * `except F'` is checked from `i` (not from `0`) but for *every* end point
    `k`, not just `k ≤ j`: `F'` must not occur anywhere in `t[i..]`.
  * The figure quantifies over extensions `ξ'' ⊇ ξ'` of the valuation; here
    valuations are total and (by `Query.Declared`) every variable of the
    query is already assigned, so the quantifier is vacuous and is dropped.
  * Invocation `Q(z⃗)` runs the body of `Q` under the valuation
    `[xᵢ ↦ ξ(zᵢ)]` — equivalent to `P_Q[z⃗/x⃗]` with the locals of `Q` private —
    rather than substituting syntactically, so no capture-avoidance is needed.
  * Invocations are resolved in a *list* of queries (`QProg`) by structural
    recursion (`QProg.interp`), instead of inside the same inductive
    definition.  That is forced by Lean's strict positivity: the `except`
    clause negates `Pat.Sat`, which cannot happen inside the (mutual)
    inductive that defines `Pat.Sat` itself.  Pattern satisfaction is
    therefore parametric in an *interpretation* `Θ` of invocations, and
    `QProg.interp` builds `Θ` from the program.

  Plain Lean 4 — no Mathlib required.
-/

import CoreJsSemantics
import CoreJsQuerySyntax

namespace CoreJS

/-! ## Execution records -/

/-- Observations `σ` of an execution: the value stored at each location
    (`val`), the locations each location was computed from (`dep`), the
    attacker-controlled locations (`ac`) and the sink locations (`sk`). -/
structure Obs where
  val : Loc → Option Val
  dep : Loc → LocSet
  ac  : LocSet
  sk  : LocSet

/-- Execution records `⟨t, σ⟩`. -/
structure Exec where
  trc : Trc
  obs : Obs

/-- Flatten a trace into the list of its actions, in order. -/
def Trc.toList : Trc → List Act
  | .emp       => []
  | .act a     => [a]
  | .seq t₁ t₂ => t₁.toList ++ t₂.toList

/-- The observation of a concrete run with final heap `h` and taint register
    `δ`: `val = h.val`, `dep = δ.dep`, `sk = δ.sk`, and `ac` is `δ.ac`
    together with every location that depends on a location of `δ.ac`. -/
def Obs.ofRun (h : Heap) (δ : Reg) : Obs where
  val := h.val
  dep := δ.dep
  ac  := fun l => δ.ac l ∨ ∃ l', δ.ac l' ∧ δ.dep l l'
  sk  := δ.sk

/-- Well-formedness of an observation (not assumed by the semantics):
    `dep` is transitive (`σ.dep l₁ l₂` reads "`l₂ ∈ σ.dep l₁`", i.e. `l₁`
    depends on `l₂`), and `ac` is closed under reverse dependency: a location
    depending on an attacker-controlled one is attacker-controlled. -/
structure Obs.WF (σ : Obs) : Prop where
  dep_trans : ∀ l₁ l₂ l₃, σ.dep l₁ l₂ → σ.dep l₂ l₃ → σ.dep l₁ l₃
  ac_closed : ∀ l₁ l₂, σ.dep l₂ l₁ → σ.ac l₁ → σ.ac l₂

/-! ## Logical environments -/

/-- Logical environments `ξ`: the location each query variable denotes. -/
abbrev LEnv := Var → Loc

/-- The default environment, used only to seed environments whose relevant
    variables are all overwritten (see `Query.Declared`). -/
def LEnv.empty : LEnv := fun _ => 0

/-- `ξ[y₁ ↦ l₁, ..., yₙ ↦ lₙ]`; surplus variables or locations are ignored. -/
def LEnv.bind (ξ : LEnv) : List Var → List Loc → LEnv
  | y :: ys, l :: ls => fun x => if x = y then l else LEnv.bind ξ ys ls x
  | _,       _       => ξ

/-- The trace action a query action denotes under `ξ`. -/
def QAct.inst (ξ : LEnv) : QAct → Act
  | .lookup x₁ x₂ x₃ => .lookup (ξ x₁) (ξ x₂) (ξ x₃)
  | .update x₁ x₂ x₃ => .update (ξ x₁) (ξ x₂) (ξ x₃)
  | .call xf xs      => .call (ξ xf) (xs.map ξ)
  | .retn xf x       => .ret (ξ xf) (ξ x)

/-! ## Invariants -/

/-- `σ, ξ ⊨ p`.  `sv` requires both locations to hold a value: two locations
    with no value do not "hold the same value" (and this is distinct from
    both holding `.undef`, which is a value). -/
def Pred.Sat (σ : Obs) (ξ : LEnv) : Pred → Prop
  | .sk x      => σ.sk (ξ x)
  | .ac x      => σ.ac (ξ x)
  | .dep x₁ x₂ => σ.dep (ξ x₁) (ξ x₂)
  | .sv x₁ x₂  => ∃ v, σ.val (ξ x₁) = some v ∧ σ.val (ξ x₂) = some v
  | .hv x c    => σ.val (ξ x) = some c

/-- `σ, ξ ⊨ I`. -/
def Inv.Sat (σ : Obs) (ξ : LEnv) : Inv → Prop
  | .pred p    => p.Sat σ ξ
  | .not I     => ¬ I.Sat σ ξ
  | .or I₁ I₂  => I₁.Sat σ ξ ∨ I₂.Sat σ ξ
  | .and I₁ I₂ => I₁.Sat σ ξ ∧ I₂.Sat σ ξ
  | .tt        => True
  | .ff        => False

/-! ## Action patterns and guarded patterns

`Θ Q l⃗ i j` says that the query `Q`, applied to the locations `l⃗`, matches
`t` from `i` to `j`.  It is a parameter of the two relations below (with `t`
and `σ` fixed) and is instantiated by `QProg.interp`. -/

/-- Interpretations of query invocations. -/
abbrev Interp := QName → List Loc → Nat → Nat → Prop

/-- `t, σ, ξ ⊨ F : i ⇝ j`, relative to the interpretation `Θ` of invocations. -/
inductive Pat.Sat (Θ : Interp) (t : List Act) (σ : Obs) (ξ : LEnv) :
    Pat → Nat → Nat → Prop where

  /-- `ε` -/
  | eps {i} : Pat.Sat Θ t σ ξ .eps i i

  /-- `a` -/
  | act {a i j} :
      i < j →
      j ≤ t.length →
      t[j - 1]? = some (a.inst ξ) →
      Pat.Sat Θ t σ ξ (.act a) i j

  /-- `Q(z⃗)` -/
  | query {Q zs i j} :
      Θ Q (zs.map ξ) i j →
      Pat.Sat Θ t σ ξ (.query Q zs) i j

  /-- `F₁ ; F₂` -/
  | seq {F₁ F₂ i k j} :
      Pat.Sat Θ t σ ξ F₁ i k →
      Pat.Sat Θ t σ ξ F₂ k j →
      Pat.Sat Θ t σ ξ (.seq F₁ F₂) i j

  /-- `F₁ ‖ F₂`, left -/
  | altL {F₁ F₂ i j} :
      Pat.Sat Θ t σ ξ F₁ i j →
      Pat.Sat Θ t σ ξ (.alt F₁ F₂) i j

  /-- `F₁ ‖ F₂`, right -/
  | altR {F₁ F₂ i j} :
      Pat.Sat Θ t σ ξ F₂ i j →
      Pat.Sat Θ t σ ξ (.alt F₁ F₂) i j

  /-- `F₁ & F₂`: both matched from `i`, ending at the later of the two. -/
  | both {F₁ F₂ i j₁ j₂ j} :
      Pat.Sat Θ t σ ξ F₁ i j₁ →
      Pat.Sat Θ t σ ξ F₂ i j₂ →
      j = max j₁ j₂ →
      Pat.Sat Θ t σ ξ (.both F₁ F₂) i j

/-- `t, σ, ξ ⊨ (exists y⃗: F when I except F') : i ⇝ j`. -/
inductive Guarded.Sat (Θ : Interp) (t : List Act) (σ : Obs) :
    LEnv → Guarded → Nat → Nat → Prop where
  | mk {ξ ξ' g ls i j} :
      ls.length = g.locals.length →
      ξ' = ξ.bind g.locals ls →
      Pat.Sat Θ t σ ξ' g.body i j →
      Inv.Sat σ ξ' g.when →
      (∀ F', g.except = some F' → ∀ k, ¬ Pat.Sat Θ t σ ξ' F' i k) →
      Guarded.Sat Θ t σ ξ g i j

/-! ## Query programs -/

/-- The interpretation of invocations determined by a query program on the
    record `⟨t, σ⟩`.  A query is applied to as many locations as it has
    parameters, and its guarded pattern is run under `[xᵢ ↦ lᵢ]`; it can only
    invoke the queries after it in the list. -/
def QProg.interp (t : List Act) (σ : Obs) : QProg → Interp
  | []     => fun _ _ _ _ => False
  | q :: Δ => fun Q ls i j =>
      if Q = q.name then
        ls.length = q.params.length ∧
        Guarded.Sat (QProg.interp t σ Δ) t σ (LEnv.empty.bind q.params ls) q.body i j
      else QProg.interp t σ Δ Q ls i j

/-- `Δ ⊢ t, σ, ξ ⊨ F : i ⇝ j`. -/
def QProg.Sat (Δ : QProg) (t : List Act) (σ : Obs) (ξ : LEnv) (F : Pat) (i j : Nat) : Prop :=
  Pat.Sat (Δ.interp t σ) t σ ξ F i j

@[inherit_doc] scoped notation:50 Δ " ⊢ " t ", " σ ", " ξ " ⊨ " F " : " i " ⇝ " j =>
  QProg.Sat Δ t σ ξ F i j

/-- The execution record `e` matches the query `Q` applied to `l⃗`:
    `t, σ, [x⃗ ↦ l⃗] ⊨ P_Q : 0 ⇝ j` for some `j`. -/
def Exec.Matches (Δ : QProg) (e : Exec) (Q : QName) (ls : List Loc) : Prop :=
  ∃ j, Δ.interp e.trc.toList e.obs Q ls 0 j

/-! ## Sanity lemmas

Facts about the position bounds and the algebra of the combinators.  The
position bounds hold of `Pat.Sat` for any interpretation `Θ` that respects
them, and `QProg.interp` does. -/

/-- An interpretation only relates `i` to `j ≥ i`, and stays within the trace. -/
structure Interp.Ok (Θ : Interp) (t : List Act) : Prop where
  le    : ∀ Q ls i j, Θ Q ls i j → i ≤ j
  bound : ∀ Q ls i j, Θ Q ls i j → i ≤ t.length → j ≤ t.length

theorem Pat.Sat.le {Θ t σ ξ F i j} (hΘ : Θ.Ok t) : Pat.Sat Θ t σ ξ F i j → i ≤ j := by
  intro h
  induction h with
  | eps => exact Nat.le_refl _
  | act hij => exact Nat.le_of_lt hij
  | query h => exact hΘ.le _ _ _ _ h
  | seq _ _ ih₁ ih₂ => exact Nat.le_trans ih₁ ih₂
  | altL _ ih => exact ih
  | altR _ ih => exact ih
  | both _ _ hj ih₁ _ => omega

theorem Pat.Sat.bound {Θ t σ ξ F i j} (hΘ : Θ.Ok t) :
    Pat.Sat Θ t σ ξ F i j → i ≤ t.length → j ≤ t.length := by
  intro h
  induction h with
  | eps => exact id
  | act _ hj => intro _; exact hj
  | query h => exact hΘ.bound _ _ _ _ h
  | seq _ h₂ ih₁ ih₂ => intro hi; exact ih₂ (ih₁ hi)
  | altL _ ih => exact ih
  | altR _ ih => exact ih
  | both _ _ hj ih₁ ih₂ => intro hi; have := ih₁ hi; have := ih₂ hi; omega

theorem Guarded.Sat.le {Θ t σ ξ g i j} (hΘ : Θ.Ok t) : Guarded.Sat Θ t σ ξ g i j → i ≤ j := by
  intro h
  cases h with
  | mk _ _ hb _ _ => exact hb.le hΘ

theorem Guarded.Sat.bound {Θ t σ ξ g i j} (hΘ : Θ.Ok t) :
    Guarded.Sat Θ t σ ξ g i j → i ≤ t.length → j ≤ t.length := by
  intro h
  cases h with
  | mk _ _ hb _ _ => exact hb.bound hΘ

theorem QProg.interp_ok (Δ : QProg) (t : List Act) (σ : Obs) : (Δ.interp t σ).Ok t := by
  induction Δ with
  | nil => exact ⟨fun _ _ _ _ h => h.elim, fun _ _ _ _ h => h.elim⟩
  | cons q Δ ih =>
    constructor
    · intro Q ls i j h
      simp only [QProg.interp] at h
      split at h
      · exact h.2.le ih
      · exact ih.le _ _ _ _ h
    · intro Q ls i j h
      simp only [QProg.interp] at h
      split at h
      · exact h.2.bound ih
      · exact ih.bound _ _ _ _ h

/-- `ε` is a unit for `;` on the left. -/
theorem Pat.Sat.seq_eps_left {Θ t σ ξ F i j} :
    Pat.Sat Θ t σ ξ (.seq .eps F) i j ↔ Pat.Sat Θ t σ ξ F i j := by
  constructor
  · intro h
    cases h with
    | seq h₁ h₂ => cases h₁; exact h₂
  · intro h; exact .seq .eps h

/-- `ε` is a unit for `;` on the right. -/
theorem Pat.Sat.seq_eps_right {Θ t σ ξ F i j} :
    Pat.Sat Θ t σ ξ (.seq F .eps) i j ↔ Pat.Sat Θ t σ ξ F i j := by
  constructor
  · intro h
    cases h with
    | seq h₁ h₂ => cases h₂; exact h₁
  · intro h; exact .seq h .eps

/-- `;` is associative. -/
theorem Pat.Sat.seq_assoc {Θ t σ ξ F G H i j} :
    Pat.Sat Θ t σ ξ (.seq (.seq F G) H) i j ↔ Pat.Sat Θ t σ ξ (.seq F (.seq G H)) i j := by
  constructor
  · intro h
    cases h with
    | seq h₁ h₂ =>
      cases h₁ with
      | seq h₁ h₃ => exact .seq h₁ (.seq h₃ h₂)
  · intro h
    cases h with
    | seq h₁ h₂ =>
      cases h₂ with
      | seq h₂ h₃ => exact .seq (.seq h₁ h₂) h₃

/-- `‖` is commutative. -/
theorem Pat.Sat.alt_comm {Θ t σ ξ F G i j} :
    Pat.Sat Θ t σ ξ (.alt F G) i j ↔ Pat.Sat Θ t σ ξ (.alt G F) i j := by
  constructor
  · intro h
    cases h with
    | altL h => exact .altR h
    | altR h => exact .altL h
  · intro h
    cases h with
    | altL h => exact .altR h
    | altR h => exact .altL h

/-- `‖` is idempotent. -/
theorem Pat.Sat.alt_idem {Θ t σ ξ F i j} :
    Pat.Sat Θ t σ ξ (.alt F F) i j ↔ Pat.Sat Θ t σ ξ F i j := by
  constructor
  · intro h
    cases h with
    | altL h => exact h
    | altR h => exact h
  · intro h; exact .altL h

/-- `&` is commutative. -/
theorem Pat.Sat.both_comm {Θ t σ ξ F G i j} :
    Pat.Sat Θ t σ ξ (.both F G) i j ↔ Pat.Sat Θ t σ ξ (.both G F) i j := by
  constructor
  · intro h
    cases h with
    | both h₁ h₂ hj => exact .both h₂ h₁ (by omega)
  · intro h
    cases h with
    | both h₁ h₂ hj => exact .both h₂ h₁ (by omega)

/-- `&` is idempotent; in particular `a & a` is matched whenever `a` is. -/
theorem Pat.Sat.both_idem {Θ t σ ξ F i j} :
    Pat.Sat Θ t σ ξ (.both F F) i j ↔ Pat.Sat Θ t σ ξ F i j := by
  constructor
  · intro h
    cases h with
    | @both _ _ _ a b _ h₁ h₂ hj =>
      rcases Nat.le_total a b with hle | hle
      · have : j = b := by omega
        subst this; exact h₂
      · have : j = a := by omega
        subst this; exact h₁
  · intro h; exact .both h h (by omega)

/-- `&` is associative. -/
theorem Pat.Sat.both_assoc {Θ t σ ξ F G H i j} :
    Pat.Sat Θ t σ ξ (.both (.both F G) H) i j ↔ Pat.Sat Θ t σ ξ (.both F (.both G H)) i j := by
  constructor
  · intro h
    cases h with
    | both h₁ h₂ hj =>
      cases h₁ with
      | both h₁ h₃ hk => exact .both h₁ (.both h₃ h₂ rfl) (by omega)
  · intro h
    cases h with
    | both h₁ h₂ hj =>
      cases h₂ with
      | both h₂ h₃ hk => exact .both (.both h₁ h₂ rfl) h₃ (by omega)

/-- `ε` is a unit for `&`, for interpretations that respect positions. -/
theorem Pat.Sat.both_eps {Θ t σ ξ F i j} (hΘ : Θ.Ok t) :
    Pat.Sat Θ t σ ξ (.both F .eps) i j ↔ Pat.Sat Θ t σ ξ F i j := by
  constructor
  · intro h
    cases h with
    | @both _ _ _ a _ _ h₁ h₂ hj =>
      cases h₂
      have := h₁.le hΘ
      have : j = a := by omega
      subst this; exact h₁
  · intro h
    have := h.le hΘ
    exact .both h .eps (by omega)

/-- Unfolding of `QProg.interp` at the head query of the program (any start `i`). -/
theorem QProg.interp_head (q : Query) (Δ : QProg) (t : List Act) (σ : Obs) (ls : List Loc)
    (i j : Nat) :
    (QProg.interp t σ (q :: Δ)) q.name ls i j ↔
      ls.length = q.params.length ∧
      Guarded.Sat (QProg.interp t σ Δ) t σ (LEnv.empty.bind q.params ls) q.body i j := by
  simp [QProg.interp]

/-- Unfolding of `QProg.interp` at a query other than the head. -/
theorem QProg.interp_tail (q : Query) (Δ : QProg) (t : List Act) (σ : Obs) {Q : QName}
    (h : Q ≠ q.name) (ls : List Loc) (i j : Nat) :
    (QProg.interp t σ (q :: Δ)) Q ls i j ↔ QProg.interp t σ Δ Q ls i j := by
  simp [QProg.interp, h]

/-- Unfolding of `Exec.Matches` for a query in the program. -/
theorem Exec.Matches.iff_head (q : Query) (Δ : QProg) (e : Exec) (ls : List Loc) :
    Exec.Matches (q :: Δ) e q.name ls ↔
      ls.length = q.params.length ∧
      ∃ j, Guarded.Sat (Δ.interp e.trc.toList e.obs) e.trc.toList e.obs
        (LEnv.empty.bind q.params ls) q.body 0 j := by
  simp only [Exec.Matches, QProg.interp, if_true]
  constructor
  · rintro ⟨j, h₁, h₂⟩; exact ⟨h₁, j, h₂⟩
  · rintro ⟨h₁, j, h₂⟩; exact ⟨j, h₁, h₂⟩

end CoreJS
