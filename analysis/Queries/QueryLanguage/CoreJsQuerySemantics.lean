/-
  # Core JavaScript — Query Semantics over Execution Records

  Satisfaction of queries (`CoreJsQuerySyntax.lean`) over *execution records*
  `⟨t, δ⟩` (`Exec`/`Obs`, defined in `CoreJsSemantics.lean`, since they need
  nothing from the query syntax and are shared with `CoreJsFoLtl.lean`): a
  concrete trace `t` together with an observation `δ` of it, which has the
  fields of a taint register (the paper's record `(t, δ)`).  The semantics
  is defined for any record, whether or not it was produced by the concrete
  semantics; `Obs.ofRun` (also in `CoreJsSemantics.lean`) shows how a concrete
  run's final taint register yields an observation.

  The relations, in the paper's notation and as written here (Lean notation,
  `scoped` in `CoreJS`):

  | Paper                     | Lean                        | Definition                |
  |---------------------------|-----------------------------|---------------------------|
  | `δ, ξ ⊨ p`                | `δ ⬝ ξ ⊨ p`                 | `Pred.Sat δ ξ p`          |
  | `δ, ξ ⊨ I`                | `δ ⬝ ξ ⊨ I`                 | `Inv.Sat δ ξ I`           |
  | `t, δ, ξ ⊨ F : i ⇝ j`     | `Δ ⬝ t ⬝ δ ⬝ ξ ⊨ F : i ⇝ j` | `QProg.Sat Δ t δ ξ F i j` |
  |                           | `Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F : i ⇝ j` | `Pat.Sat Θ t δ ξ F i j`   |
  | `t, δ, ξ ⊨ P : i ⇝ j`     | `Θ ⬝ t ⬝ δ ⬝ ξ ⊨ P : i ⇝ j` | `QBody.Sat Θ t δ ξ P i j` |

  Two systematic changes from the paper. Arguments are separated by `⬝`
  instead of `,` (in Lean, a term followed by `,` clashes with tuples and
  `⟨…, …⟩`). And the queries an invocation may refer to, implicit in the
  paper, are an explicit first argument: the program `Δ`, or the
  interpretation `Θ` it induces.  The proofs mostly use the `Θ` form: `Θ` is the interpretation
  of query invocations that the program `Δ` determines on `t` and `δ`
  (`QProg.interp`, below), and stands in `Δ`'s place in the list — it is
  what the inductive definition can be parametrised by (see the note on
  strict positivity below).  One notation covers the last three rows: the
  types of `Θ`/`Δ` (`Interp` or `QProg`) and of `F`/`P` (`Pat` or `QBody`)
  select the relation, so binders in statements carry their types.

  `t, δ, ξ ⊨ F : i ⇝ j` reads: starting after position `i` of the trace,
  `F` is performed, and the last action it uses is `t[j-1]` (so `j` is one
  past it; `j = i` if `F` uses no action).

  Choices worth knowing about:

  * `F₁ & F₂ : i ⇝ j` requires *both* patterns to match from `i`, ending at
    `j₁` and `j₂`, and `j = max j₁ j₂`.  A single trace action may serve both
    sides, so `a & a` is matched whenever `a` is.
  * `except F'` is checked over the *whole trace*, as in the paper's Fig. 6:
    `F'`, matched from `0` with any end point `k ≤ |t|`, must not occur
    anywhere in `t` — not just after
    the start `i` of the query it belongs to, and not just before `j`.  A
    guard thereby does not depend on where its query starts, which is what
    lets the FO-LTL translation (`CoreJsQueryToLtl.lean`) place a guard's
    translation exactly where the query occurs.  It only constrains the
    query body it belongs to, so under `Q ‖ F` a failing `except` inside
    `Q` merely rules out the left alternative.
  * Valuations are total and (by `Query.Declared`) every variable of a
    well-formed query is already assigned, so there is no quantification
    over extensions of the valuation: the paper's "for all `ξ'' ⊇ ξ'`" in
    `except` is `ξ''` = `ξ'` here (a total valuation has no proper
    extension), which agrees with the paper on well-formed queries, whose
    excluded patterns mention only declared variables.  The bound
    `k ≤ |t|` is redundant for the interpretations that arise
    (`Pat.not_sat_zero_iff`), but kept so the rule reads as the paper's.
  * Invocation `Q(zs)` runs the body of `Q` under the valuation
    `[xᵢ ↦ ξ(zᵢ)]` — equivalent to `P_Q[zs/xs]` with the locals of `Q` private —
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

import CoreJS.CoreJsSemantics
import Queries.QueryLanguage.CoreJsQuerySyntax

namespace CoreJS

/-! ## Logical environments

`Obs`/`Exec`/`Trc.toList`/`Obs.ofRun`/`Obs.WF` live in `CoreJsSemantics.lean`
(they need nothing from the query syntax); only the query-specific notion of
a valuation follows here. -/

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
def QAct.inst {ν} (ξ : ν → Loc) : QAct ν → Act
  | .lookup x₁ x₂ x₃ => .lookup (ξ x₁) (ξ x₂) (ξ x₃)
  | .update x₁ x₂ x₃ => .update (ξ x₁) (ξ x₂) (ξ x₃)
  | .call xf xs      => .call (ξ xf) (xs.map ξ)
  | .retn xf x       => .ret (ξ xf) (ξ x)

/-! ## Invariants -/

/-- `δ ⬝ ξ ⊨ p`.  `sv` requires both locations to hold a value: two locations
    with no value do not "hold the same value" (and this is distinct from
    both holding `.undef`, which is a value). -/
def Pred.Sat {ν} (δ : Obs) (ξ : ν → Loc) : Pred ν → Prop
  | .sk x      => δ.sk (ξ x)
  | .ac x      => δ.ac (ξ x)
  | .dep x₁ x₂ => δ.dep (ξ x₁) (ξ x₂)
  | .sv x₁ x₂  => ∃ v, δ.val (ξ x₁) = some v ∧ δ.val (ξ x₂) = some v
  | .hv x c    => δ.val (ξ x) = some c

@[inherit_doc] scoped notation:50 δ:51 " ⬝ " ξ:51 " ⊨ " p:51 => Pred.Sat δ ξ p

-- Declared before `Inv.Sat` so that its defining equations can use it; without
-- hygiene, `Inv.Sat` is resolved where the notation is used.
set_option hygiene false in
/-- `δ ⬝ ξ ⊨ I` (the paper's `δ, ξ ⊨ I`). -/
scoped notation:50 (name := invSatNotation) δ:51 " ⬝ " ξ:51 " ⊨ " I:51 => Inv.Sat δ ξ I

/-- `δ ⬝ ξ ⊨ I`. -/
def Inv.Sat {ν} (δ : Obs) (ξ : ν → Loc) : Inv ν → Prop
  | .pred p    => δ ⬝ ξ ⊨ p
  | .not I     => ¬ δ ⬝ ξ ⊨ I
  | .or I₁ I₂  => δ ⬝ ξ ⊨ I₁ ∨ δ ⬝ ξ ⊨ I₂
  | .and I₁ I₂ => δ ⬝ ξ ⊨ I₁ ∧ δ ⬝ ξ ⊨ I₂
  | .tt        => True
  | .ff        => False

/- `notation` generates no unexpander for a constant that does not exist yet, so
   goals would show `Inv.Sat δ ξ I`; this one restores the notation.  (A quotation
   `` `($δ ⬝ $ξ ⊨ $I) `` would be ambiguous with `Pred.Sat`'s, hence the explicit
   node of the right kind.) -/
@[scoped app_unexpander Inv.Sat] def unexpandInvSat : Lean.PrettyPrinter.Unexpander
  | `($_ $δ $ξ $I) => pure <| Lean.mkNode ``invSatNotation
      #[δ, Lean.mkAtom "⬝", ξ, Lean.mkAtom "⊨", I]
  | _ => throw ()

/-! ## Action patterns and query bodies

`Θ Q ls i j` says that the query `Q`, applied to the locations `ls`, matches
`t` from `i` to `j`.  It is a parameter of the two relations below (with `t`
and `δ` fixed) and is instantiated by `QProg.interp`. -/

/-- Interpretations of query invocations. -/
abbrev Interp := QName → List Loc → Nat → Nat → Prop

-- As for `Inv.Sat`: declared before the inductives so that their rules can use it.
-- The same notation stands for `Pat.Sat`, `QBody.Sat` and (below) `QProg.Sat`;
-- the types of `Θ`/`Δ` and of `F`/`P` select the one meant.
set_option hygiene false in
/-- `Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F : i ⇝ j`: the paper's `Δ, t, δ, ξ ⊨ F : i ⇝ j`, with the
    interpretation `Θ` of invocations in place of the program `Δ`. -/
scoped notation:50 (name := patSatNotation)
  Θ:51 " ⬝ " t:51 " ⬝ " δ:51 " ⬝ " ξ:51 " ⊨ " F " : " i " ⇝ " j:51 => Pat.Sat Θ t δ ξ F i j

set_option hygiene false in
/-- `Θ ⬝ t ⬝ δ ⬝ ξ ⊨ P : i ⇝ j` for a query body `P`. -/
scoped notation:50 (name := qbodySatNotation)
  Θ:51 " ⬝ " t:51 " ⬝ " δ:51 " ⬝ " ξ:51 " ⊨ " P " : " i " ⇝ " j:51 => QBody.Sat Θ t δ ξ P i j

/-- `Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F : i ⇝ j`, relative to the interpretation `Θ` of invocations. -/
inductive Pat.Sat (Θ : Interp) (t : List Act) (δ : Obs) (ξ : LEnv) :
    Pat → Nat → Nat → Prop where

  /-- `ε` -/
  | eps {i} : Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .eps : i ⇝ i

  /-- `a` -/
  | act {a i j} :
      i < j →
      j ≤ t.length →
      t[j - 1]? = some (a.inst ξ) →
      Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .act a : i ⇝ j

  /-- `Q(zs)` -/
  | query {Q zs i j} :
      Θ Q (zs.map ξ) i j →
      Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .query Q zs : i ⇝ j

  /-- `F₁ ; F₂` -/
  | seq {F₁ F₂ i k j} :
      Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F₁ : i ⇝ k →
      Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F₂ : k ⇝ j →
      Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .seq F₁ F₂ : i ⇝ j

  /-- `F₁ ‖ F₂`, left -/
  | altL {F₁ F₂ i j} :
      Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F₁ : i ⇝ j →
      Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .alt F₁ F₂ : i ⇝ j

  /-- `F₁ ‖ F₂`, right -/
  | altR {F₁ F₂ i j} :
      Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F₂ : i ⇝ j →
      Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .alt F₁ F₂ : i ⇝ j

  /-- `F₁ & F₂`: both matched from `i`, ending at the later of the two. -/
  | both {F₁ F₂ i j₁ j₂ j} :
      Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F₁ : i ⇝ j₁ →
      Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F₂ : i ⇝ j₂ →
      j = max j₁ j₂ →
      Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .both F₁ F₂ : i ⇝ j

/-- `Θ ⬝ t ⬝ δ ⬝ ξ ⊨ (exists ys: F when I except F') : i ⇝ j`.  The positive part
    `F` is matched from `i`; the excluded pattern `F'` is checked from the
    start of the trace, for every end point `k ≤ |t|`, so that the guard does
    not depend on `i` (Fig. 6, condition (3)). -/
inductive QBody.Sat (Θ : Interp) (t : List Act) (δ : Obs) :
    LEnv → QBody → Nat → Nat → Prop where
  | mk {ξ ξ' : LEnv} {P : QBody} {ls : List Loc} {i j : Nat} :
      ls.length = P.locals.length →
      ξ' = ξ.bind P.locals ls →
      Θ ⬝ t ⬝ δ ⬝ ξ' ⊨ P.pattern : i ⇝ j →
      δ ⬝ ξ' ⊨ P.when →
      (∀ F', P.except = some F' → ∀ k ≤ t.length, ¬ Θ ⬝ t ⬝ δ ⬝ ξ' ⊨ F' : 0 ⇝ k) →
      Θ ⬝ t ⬝ δ ⬝ ξ ⊨ P : i ⇝ j

-- Unexpanders, as for `Inv.Sat`.
@[scoped app_unexpander Pat.Sat] def unexpandPatSat : Lean.PrettyPrinter.Unexpander
  | `($_ $Θ $t $δ $ξ $F $i $j) => pure <| Lean.mkNode ``patSatNotation
      #[Θ, Lean.mkAtom "⬝", t, Lean.mkAtom "⬝", δ, Lean.mkAtom "⬝", ξ, Lean.mkAtom "⊨", F,
        Lean.mkAtom ":", i, Lean.mkAtom "⇝", j]
  | _ => throw ()

@[scoped app_unexpander QBody.Sat] def unexpandQBodySat : Lean.PrettyPrinter.Unexpander
  | `($_ $Θ $t $δ $ξ $P $i $j) => pure <| Lean.mkNode ``qbodySatNotation
      #[Θ, Lean.mkAtom "⬝", t, Lean.mkAtom "⬝", δ, Lean.mkAtom "⬝", ξ, Lean.mkAtom "⊨", P,
        Lean.mkAtom ":", i, Lean.mkAtom "⇝", j]
  | _ => throw ()

/-! ## Query programs -/

/-- The interpretation of invocations determined by a query program on the
    record `⟨t, δ⟩`.  A query is applied to as many locations as it has
    parameters, and its body is run under `[xᵢ ↦ lᵢ]`; it can only
    invoke the queries after it in the list. -/
def QProg.interp (t : List Act) (δ : Obs) : QProg → Interp
  | []     => fun _ _ _ _ => False
  | q :: Δ => fun Q ls i j =>
      if Q = q.name then
        ls.length = q.params.length ∧
        QProg.interp t δ Δ ⬝ t ⬝ δ ⬝ LEnv.empty.bind q.params ls ⊨ q.body : i ⇝ j
      else QProg.interp t δ Δ Q ls i j

/-- `Δ ⬝ t ⬝ δ ⬝ ξ ⊨ F : i ⇝ j`: the paper's `Δ, t, δ, ξ ⊨ F : i ⇝ j`. -/
def QProg.Sat (Δ : QProg) (t : List Act) (δ : Obs) (ξ : LEnv) (F : Pat) (i j : Nat) : Prop :=
  Δ.interp t δ ⬝ t ⬝ δ ⬝ ξ ⊨ F : i ⇝ j

@[inherit_doc] scoped notation:50
  Δ:51 " ⬝ " t:51 " ⬝ " δ:51 " ⬝ " ξ:51 " ⊨ " F " : " i " ⇝ " j:51 => QProg.Sat Δ t δ ξ F i j

/-- The execution record `e` matches the query `Q` applied to `ls`:
    `t, δ, [xs ↦ ls] ⊨ P_Q : 0 ⇝ j` for some `j`.  Starting at `0` loses no
    generality: a match from any `i` yields one from `0`
    (`Exec.Matches.of_interp`). -/
def Exec.Matches (Δ : QProg) (e : Exec) (Q : QName) (ls : List Loc) : Prop :=
  ∃ j, Δ.interp e.trc.toList e.obs Q ls 0 j

/-! ## Sanity lemmas

Facts about the position bounds and the algebra of the combinators.  The
position bounds hold of `Pat.Sat` for any interpretation `Θ` that respects
them, and `QProg.interp` does. -/

section sanity

variable {Θ : Interp} {t : List Act} {δ : Obs} {ξ : LEnv} {F G H : Pat} {P : QBody} {i j : Nat}

/-- An interpretation only relates `i` to `j ≥ i`, and stays within the trace. -/
structure Interp.Ok (Θ : Interp) (t : List Act) : Prop where
  le    : ∀ Q ls i j, Θ Q ls i j → i ≤ j
  bound : ∀ Q ls i j, Θ Q ls i j → i ≤ t.length → j ≤ t.length

theorem Pat.Sat.le (hΘ : Θ.Ok t) : Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F : i ⇝ j → i ≤ j := by
  intro h
  induction h with
  | eps => exact Nat.le_refl _
  | act hij => exact Nat.le_of_lt hij
  | query h => exact hΘ.le _ _ _ _ h
  | seq _ _ ih₁ ih₂ => exact Nat.le_trans ih₁ ih₂
  | altL _ ih => exact ih
  | altR _ ih => exact ih
  | both _ _ hj ih₁ _ => omega

theorem Pat.Sat.bound (hΘ : Θ.Ok t) :
    Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F : i ⇝ j → i ≤ t.length → j ≤ t.length := by
  intro h
  induction h with
  | eps => exact id
  | act _ hj => intro _; exact hj
  | query h => exact hΘ.bound _ _ _ _ h
  | seq _ h₂ ih₁ ih₂ => intro hi; exact ih₂ (ih₁ hi)
  | altL _ ih => exact ih
  | altR _ ih => exact ih
  | both _ _ hj ih₁ ih₂ => intro hi; have := ih₁ hi; have := ih₂ hi; omega

theorem QBody.Sat.le (hΘ : Θ.Ok t) : Θ ⬝ t ⬝ δ ⬝ ξ ⊨ P : i ⇝ j → i ≤ j := by
  intro h
  cases h with
  | mk _ _ hb _ _ => exact hb.le hΘ

theorem QBody.Sat.bound (hΘ : Θ.Ok t) :
    Θ ⬝ t ⬝ δ ⬝ ξ ⊨ P : i ⇝ j → i ≤ t.length → j ≤ t.length := by
  intro h
  cases h with
  | mk _ _ hb _ _ => exact hb.bound hΘ

theorem QProg.interp_ok (Δ : QProg) (t : List Act) (δ : Obs) : (Δ.interp t δ).Ok t := by
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

/-- The bound `k ≤ |t|` of an `except` clause (as in the paper) loses nothing
    under an interpretation that stays within the trace: a match from `0`
    never ends past it. -/
theorem Pat.not_sat_zero_iff (hΘ : Θ.Ok t) :
    (∀ k ≤ t.length, ¬ Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F : 0 ⇝ k) ↔ ∀ k, ¬ Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F : 0 ⇝ k :=
  ⟨fun h k hm => h k (hm.bound hΘ (Nat.zero_le _)) hm, fun h k _ => h k⟩

/-! ### Starting a match earlier

Starting a match earlier never forces it to finish later.  The weaker
"`F : i ⇝ j` implies `F : 0 ⇝ j'` for some `j'`" is not inductive: lowering
the start of `ε` also lowers its end, so in `ε ; F₂` the second pattern must
be restarted earlier too.  The `query` case needs the same property of the
interpretation (`Interp.LowerStart`); `QProg.interp` has it because a guard's
`except` is checked over the whole trace, independently of the start.  The
upshot, `Exec.Matches.of_interp`: `Exec.Matches` starting at boundary `0`
loses no generality. -/

/-- An interpretation may always restart a match earlier, finishing no later. -/
def Interp.LowerStart (Θ : Interp) : Prop :=
  ∀ Q ls i j i', Θ Q ls i j → i' ≤ i → ∃ j', j' ≤ j ∧ Θ Q ls i' j'

theorem Pat.Sat.lower_start (hΘ : Θ.LowerStart) (h : Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F : i ⇝ j) :
    ∀ i', i' ≤ i → ∃ j', j' ≤ j ∧ Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F : i' ⇝ j' := by
  induction h with
  | eps => intro i' hi; exact ⟨i', hi, .eps⟩
  | act hij hj ht => intro i' hi; exact ⟨_, Nat.le_refl _, .act (by omega) hj ht⟩
  | query h =>
    intro i' hi
    obtain ⟨j', hj', h'⟩ := hΘ _ _ _ _ _ h hi
    exact ⟨j', hj', .query h'⟩
  | seq _ _ ih₁ ih₂ =>
    intro i' hi
    obtain ⟨k', hk', h₁⟩ := ih₁ i' hi
    obtain ⟨j', hj', h₂⟩ := ih₂ k' hk'
    exact ⟨j', hj', .seq h₁ h₂⟩
  | altL _ ih =>
    intro i' hi
    obtain ⟨j', hj', h'⟩ := ih i' hi
    exact ⟨j', hj', .altL h'⟩
  | altR _ ih =>
    intro i' hi
    obtain ⟨j', hj', h'⟩ := ih i' hi
    exact ⟨j', hj', .altR h'⟩
  | both _ _ hj ih₁ ih₂ =>
    intro i' hi
    obtain ⟨j₁', hj₁', h₁⟩ := ih₁ i' hi
    obtain ⟨j₂', hj₂', h₂⟩ := ih₂ i' hi
    exact ⟨max j₁' j₂', by omega, .both h₁ h₂ rfl⟩

theorem QBody.Sat.lower_start (hΘ : Θ.LowerStart) (h : Θ ⬝ t ⬝ δ ⬝ ξ ⊨ P : i ⇝ j) :
    ∀ i', i' ≤ i → ∃ j', j' ≤ j ∧ Θ ⬝ t ⬝ δ ⬝ ξ ⊨ P : i' ⇝ j' := by
  intro i' hi
  cases h with
  | mk hlen hξ' hpat hwhen hexcept =>
    obtain ⟨j', hj', hpat'⟩ := hpat.lower_start hΘ i' hi
    exact ⟨j', hj', .mk hlen hξ' hpat' hwhen hexcept⟩

theorem QProg.interp_lowerStart (Δ : QProg) (t : List Act) (δ : Obs) :
    (Δ.interp t δ).LowerStart := by
  induction Δ with
  | nil => intro _ _ _ _ _ h; exact h.elim
  | cons q Δ ih =>
    intro Q ls i j i' h hi
    simp only [QProg.interp] at h ⊢
    split at h
    · rename_i hQ
      obtain ⟨j', hj', h'⟩ := h.2.lower_start ih i' hi
      exact ⟨j', hj', by rw [if_pos hQ]; exact ⟨h.1, h'⟩⟩
    · rename_i hQ
      obtain ⟨j', hj', h'⟩ := ih _ _ _ _ _ h hi
      exact ⟨j', hj', by rw [if_neg hQ]; exact h'⟩

/-- A match of `Q` starting anywhere in the trace yields one starting at `0`:
    defining `Exec.Matches` from boundary `0` loses no generality. -/
theorem Exec.Matches.of_interp {Δ : QProg} {e : Exec} {Q : QName} {ls : List Loc} {i j : Nat}
    (h : Δ.interp e.trc.toList e.obs Q ls i j) : Exec.Matches Δ e Q ls :=
  let ⟨j', _, h'⟩ := QProg.interp_lowerStart Δ _ _ _ _ _ _ 0 h (Nat.zero_le _)
  ⟨j', h'⟩

/-- `ε` is a unit for `;` on the left. -/
theorem Pat.Sat.seq_eps_left :
    Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .seq .eps F : i ⇝ j ↔ Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F : i ⇝ j := by
  constructor
  · intro h
    cases h with
    | seq h₁ h₂ => cases h₁; exact h₂
  · intro h; exact .seq .eps h

/-- `ε` is a unit for `;` on the right. -/
theorem Pat.Sat.seq_eps_right :
    Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .seq F .eps : i ⇝ j ↔ Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F : i ⇝ j := by
  constructor
  · intro h
    cases h with
    | seq h₁ h₂ => cases h₂; exact h₁
  · intro h; exact .seq h .eps

/-- `;` is associative. -/
theorem Pat.Sat.seq_assoc :
    Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .seq (.seq F G) H : i ⇝ j ↔ Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .seq F (.seq G H) : i ⇝ j := by
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
theorem Pat.Sat.alt_comm :
    Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .alt F G : i ⇝ j ↔ Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .alt G F : i ⇝ j := by
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
theorem Pat.Sat.alt_idem :
    Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .alt F F : i ⇝ j ↔ Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F : i ⇝ j := by
  constructor
  · intro h
    cases h with
    | altL h => exact h
    | altR h => exact h
  · intro h; exact .altL h

/-- `&` is commutative. -/
theorem Pat.Sat.both_comm :
    Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .both F G : i ⇝ j ↔ Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .both G F : i ⇝ j := by
  constructor
  · intro h
    cases h with
    | both h₁ h₂ hj => exact .both h₂ h₁ (by omega)
  · intro h
    cases h with
    | both h₁ h₂ hj => exact .both h₂ h₁ (by omega)

/-- `&` is idempotent; in particular `a & a` is matched whenever `a` is. -/
theorem Pat.Sat.both_idem :
    Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .both F F : i ⇝ j ↔ Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F : i ⇝ j := by
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
theorem Pat.Sat.both_assoc :
    Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .both (.both F G) H : i ⇝ j ↔ Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .both F (.both G H) : i ⇝ j := by
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
theorem Pat.Sat.both_eps (hΘ : Θ.Ok t) :
    Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .both F .eps : i ⇝ j ↔ Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F : i ⇝ j := by
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

/-! ### Inversion lemmas for `Pat.Sat` -/

theorem Pat.sat_eps : Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .eps : i ⇝ j ↔ j = i := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .eps

theorem Pat.sat_act {a : QAct} :
    Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .act a : i ⇝ j ↔ i < j ∧ j ≤ t.length ∧ t[j - 1]? = some (a.inst ξ) := by
  constructor
  · intro h; cases h with | act h₁ h₂ h₃ => exact ⟨h₁, h₂, h₃⟩
  · rintro ⟨h₁, h₂, h₃⟩; exact .act h₁ h₂ h₃

theorem Pat.sat_seq {F₁ F₂ : Pat} :
    Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .seq F₁ F₂ : i ⇝ j ↔
      ∃ k, Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F₁ : i ⇝ k ∧ Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F₂ : k ⇝ j := by
  constructor
  · intro h; cases h with | seq h₁ h₂ => exact ⟨_, h₁, h₂⟩
  · rintro ⟨k, h₁, h₂⟩; exact .seq h₁ h₂

theorem Pat.sat_alt {F₁ F₂ : Pat} :
    Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .alt F₁ F₂ : i ⇝ j ↔
      Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F₁ : i ⇝ j ∨ Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F₂ : i ⇝ j := by
  constructor
  · intro h
    cases h with
    | altL h => exact Or.inl h
    | altR h => exact Or.inr h
  · rintro (h | h)
    · exact .altL h
    · exact .altR h

theorem Pat.sat_both {F₁ F₂ : Pat} :
    Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .both F₁ F₂ : i ⇝ j ↔
      ∃ j₁ j₂, Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F₁ : i ⇝ j₁ ∧ Θ ⬝ t ⬝ δ ⬝ ξ ⊨ F₂ : i ⇝ j₂ ∧ j = max j₁ j₂ := by
  constructor
  · intro h; cases h with | both h₁ h₂ h₃ => exact ⟨_, _, h₁, h₂, h₃⟩
  · rintro ⟨j₁, j₂, h₁, h₂, h₃⟩; exact .both h₁ h₂ h₃

theorem Pat.sat_query {Q : QName} {zs : List Var} :
    Θ ⬝ t ⬝ δ ⬝ ξ ⊨ .query Q zs : i ⇝ j ↔ Θ Q (zs.map ξ) i j := by
  constructor
  · intro h; cases h with | query h => exact h
  · intro h; exact .query h

end sanity

/-! ### Coincidence (locality in the free variables)

`Pat.Sat`/`Inv.Sat`/`QBody.Sat` depend on a valuation only through its values
on the term's own variables — standard for any substitution-based semantics,
and needed to relate an invoked query's *fresh* base valuation to the
semantics' own `LEnv.empty.bind` (they agree only on the query's declared
parameters; `QBody.sat_coincide` is what lets that suffice). -/

/-- A variable not among the ones bound falls through to the base valuation. -/
theorem LEnv.bind_eq_of_not_mem (ξ : LEnv) :
    ∀ (locals : List Var) (ls : List Loc) (x : Var), x ∉ locals → LEnv.bind ξ locals ls x = ξ x
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | y :: ys, l :: ls, x, hx => by
      simp only [LEnv.bind]
      have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self ..)
      rw [if_neg hxy]
      exact LEnv.bind_eq_of_not_mem ξ ys ls x (fun h => hx (List.mem_cons_of_mem _ h))

/-- A bound variable's value depends only on the binder list `ls`, not on the base
    valuation. -/
theorem LEnv.bind_indep (ξ₁ ξ₂ : LEnv) :
    ∀ (locals : List Var) (ls : List Loc), ls.length = locals.length → ∀ x ∈ locals,
      LEnv.bind ξ₁ locals ls x = LEnv.bind ξ₂ locals ls x
  | [], _, _, x, hx => by simp at hx
  | y :: ys, ls, hlen, x, hx => by
      match ls, hlen with
      | l :: ls', hlen =>
        simp only [LEnv.bind]
        by_cases hxy : x = y
        · simp [hxy]
        · rw [if_neg hxy, if_neg hxy]
          exact LEnv.bind_indep ξ₁ ξ₂ ys ls' (by simpa using hlen) x
            ((List.mem_cons.1 hx).resolve_left hxy)

theorem Pat.sat_coincide {Θ : Interp} {t : List Act} {δ : Obs} {i j : Nat} :
    ∀ {F : Pat} {ξ₁ ξ₂ : LEnv}, (∀ x ∈ F.vars, ξ₁ x = ξ₂ x) →
      (Θ ⬝ t ⬝ δ ⬝ ξ₁ ⊨ F : i ⇝ j ↔ Θ ⬝ t ⬝ δ ⬝ ξ₂ ⊨ F : i ⇝ j)
  | .eps, _, _, _ => by rw [Pat.sat_eps, Pat.sat_eps]
  | .act a, ξ₁, ξ₂, h => by
      have hinst : a.inst ξ₁ = a.inst ξ₂ := by
        simp only [Pat.vars] at h
        cases a with
        | lookup x₁ x₂ x₃ =>
          simp only [QAct.vars, List.mem_cons, List.not_mem_nil, or_false] at h
          simp only [QAct.inst, h x₁ (Or.inl rfl), h x₂ (Or.inr (Or.inl rfl)),
            h x₃ (Or.inr (Or.inr rfl))]
        | update x₁ x₂ x₃ =>
          simp only [QAct.vars, List.mem_cons, List.not_mem_nil, or_false] at h
          simp only [QAct.inst, h x₁ (Or.inl rfl), h x₂ (Or.inr (Or.inl rfl)),
            h x₃ (Or.inr (Or.inr rfl))]
        | call xf xs =>
          simp only [QAct.vars, List.mem_cons] at h
          have hxf : ξ₁ xf = ξ₂ xf := h xf (Or.inl rfl)
          have hxs : xs.map ξ₁ = xs.map ξ₂ := List.map_congr_left (fun x hx => h x (Or.inr hx))
          simp only [QAct.inst, hxf, hxs]
        | retn xf x =>
          simp only [QAct.vars, List.mem_cons, List.not_mem_nil, or_false] at h
          simp only [QAct.inst, h xf (Or.inl rfl), h x (Or.inr rfl)]
      simp only [Pat.sat_act, hinst]
  | .query Q zs, ξ₁, ξ₂, h => by
      have : zs.map ξ₁ = zs.map ξ₂ := List.map_congr_left (fun x hx => h x hx)
      simp only [Pat.sat_query, this]
  | .seq F₁ F₂, ξ₁, ξ₂, h => by
      simp only [Pat.sat_seq]
      constructor
      · rintro ⟨k, h₁, h₂⟩
        exact ⟨k, (Pat.sat_coincide (fun x hx => h x (by simp [Pat.vars]; left; exact hx))).1 h₁,
          (Pat.sat_coincide (fun x hx => h x (by simp [Pat.vars]; right; exact hx))).1 h₂⟩
      · rintro ⟨k, h₁, h₂⟩
        exact ⟨k, (Pat.sat_coincide (fun x hx => h x (by simp [Pat.vars]; left; exact hx))).2 h₁,
          (Pat.sat_coincide (fun x hx => h x (by simp [Pat.vars]; right; exact hx))).2 h₂⟩
  | .alt F₁ F₂, ξ₁, ξ₂, h => by
      simp only [Pat.sat_alt]
      constructor
      · rintro (h₁ | h₂)
        · exact Or.inl ((Pat.sat_coincide (fun x hx => h x (by simp [Pat.vars]; left; exact hx))).1 h₁)
        · exact Or.inr ((Pat.sat_coincide (fun x hx => h x (by simp [Pat.vars]; right; exact hx))).1 h₂)
      · rintro (h₁ | h₂)
        · exact Or.inl ((Pat.sat_coincide (fun x hx => h x (by simp [Pat.vars]; left; exact hx))).2 h₁)
        · exact Or.inr ((Pat.sat_coincide (fun x hx => h x (by simp [Pat.vars]; right; exact hx))).2 h₂)
  | .both F₁ F₂, ξ₁, ξ₂, h => by
      simp only [Pat.sat_both]
      constructor
      · rintro ⟨j₁, j₂, h₁, h₂, h₃⟩
        exact ⟨j₁, j₂, (Pat.sat_coincide (fun x hx => h x (by simp [Pat.vars]; left; exact hx))).1 h₁,
          (Pat.sat_coincide (fun x hx => h x (by simp [Pat.vars]; right; exact hx))).1 h₂, h₃⟩
      · rintro ⟨j₁, j₂, h₁, h₂, h₃⟩
        exact ⟨j₁, j₂, (Pat.sat_coincide (fun x hx => h x (by simp [Pat.vars]; left; exact hx))).2 h₁,
          (Pat.sat_coincide (fun x hx => h x (by simp [Pat.vars]; right; exact hx))).2 h₂, h₃⟩

theorem Pred.sat_coincide {ν} {δ : Obs} :
    ∀ {p : Pred ν} {ξ₁ ξ₂ : ν → Loc}, (∀ x ∈ p.vars, ξ₁ x = ξ₂ x) → (δ ⬝ ξ₁ ⊨ p ↔ δ ⬝ ξ₂ ⊨ p)
  | .sk x, ξ₁, ξ₂, h => by simp [Pred.Sat, Pred.vars] at h ⊢; rw [h]
  | .ac x, ξ₁, ξ₂, h => by simp [Pred.Sat, Pred.vars] at h ⊢; rw [h]
  | .dep x₁ x₂, ξ₁, ξ₂, h => by simp [Pred.Sat, Pred.vars] at h ⊢; rw [h.1, h.2]
  | .sv x₁ x₂, ξ₁, ξ₂, h => by simp [Pred.Sat, Pred.vars] at h ⊢; rw [h.1, h.2]
  | .hv x c, ξ₁, ξ₂, h => by simp [Pred.Sat, Pred.vars] at h ⊢; rw [h]

theorem Inv.sat_coincide {ν} {δ : Obs} :
    ∀ {I : Inv ν} {ξ₁ ξ₂ : ν → Loc}, (∀ x ∈ I.vars, ξ₁ x = ξ₂ x) → (δ ⬝ ξ₁ ⊨ I ↔ δ ⬝ ξ₂ ⊨ I)
  | .pred p, ξ₁, ξ₂, h => Pred.sat_coincide h
  | .not I, ξ₁, ξ₂, h => by simp only [Inv.Sat, Inv.sat_coincide (I := I) h]
  | .or I₁ I₂, ξ₁, ξ₂, h => by
      simp only [Inv.Sat]
      rw [Inv.sat_coincide (I := I₁) (fun x hx => h x (by simp [Inv.vars]; left; exact hx)),
        Inv.sat_coincide (I := I₂) (fun x hx => h x (by simp [Inv.vars]; right; exact hx))]
  | .and I₁ I₂, ξ₁, ξ₂, h => by
      simp only [Inv.Sat]
      rw [Inv.sat_coincide (I := I₁) (fun x hx => h x (by simp [Inv.vars]; left; exact hx)),
        Inv.sat_coincide (I := I₂) (fun x hx => h x (by simp [Inv.vars]; right; exact hx))]
  | .tt, _, _, _ => Iff.rfl
  | .ff, _, _, _ => Iff.rfl

/-- `QBody.Sat` depends on the outer valuation only through its values outside the
    guard's own locals (which get rebound internally regardless). -/
theorem QBody.sat_coincide {Θ : Interp} {t : List Act} {δ : Obs} {P : QBody} {i j : Nat}
    {ξ₁ ξ₂ : LEnv} (h : ∀ x ∈ P.vars, x ∉ P.locals → ξ₁ x = ξ₂ x) :
    Θ ⬝ t ⬝ δ ⬝ ξ₁ ⊨ P : i ⇝ j ↔ Θ ⬝ t ⬝ δ ⬝ ξ₂ ⊨ P : i ⇝ j := by
  have mp : ∀ {ξ₁ ξ₂ : LEnv}, (∀ x ∈ P.vars, x ∉ P.locals → ξ₁ x = ξ₂ x) →
      Θ ⬝ t ⬝ δ ⬝ ξ₁ ⊨ P : i ⇝ j → Θ ⬝ t ⬝ δ ⬝ ξ₂ ⊨ P : i ⇝ j := by
    intro ξ₁ ξ₂ h hs
    cases hs with
    | mk hlen hξ' hpat hwhen hexcept =>
      rename_i ξ' ls
      have key : ∀ x ∈ P.vars, LEnv.bind ξ₁ P.locals ls x = LEnv.bind ξ₂ P.locals ls x := by
        intro x hxg
        by_cases hxl : x ∈ P.locals
        · exact LEnv.bind_indep ξ₁ ξ₂ P.locals ls hlen x hxl
        · rw [LEnv.bind_eq_of_not_mem ξ₁ P.locals ls x hxl,
            LEnv.bind_eq_of_not_mem ξ₂ P.locals ls x hxl]
          exact h x hxg hxl
      subst hξ'
      refine .mk hlen rfl ?_ ?_ ?_
      · exact (Pat.sat_coincide
          (fun x hx => key x (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hx)))))).1 hpat
      · exact (Inv.sat_coincide
          (fun x hx => key x (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hx)))))).1 hwhen
      · intro F' hF' k hk hm
        exact hexcept F' hF' k hk
          ((Pat.sat_coincide (F := F') (fun x hx => key x
            (List.mem_append.2 (Or.inr (by rw [hF']; exact hx))))).2 hm)
  exact ⟨mp h, mp (fun x hx hxl => (h x hx hxl).symm)⟩

/-- Unfolding of `QProg.interp` at the head query of the program (any start `i`). -/
theorem QProg.interp_head (q : Query) (Δ : QProg) (t : List Act) (δ : Obs) (ls : List Loc)
    (i j : Nat) :
    (QProg.interp t δ (q :: Δ)) q.name ls i j ↔
      ls.length = q.params.length ∧
      QProg.interp t δ Δ ⬝ t ⬝ δ ⬝ LEnv.empty.bind q.params ls ⊨ q.body : i ⇝ j := by
  simp [QProg.interp]

/-- Unfolding of `QProg.interp` at a query other than the head. -/
theorem QProg.interp_tail (q : Query) (Δ : QProg) (t : List Act) (δ : Obs) {Q : QName}
    (h : Q ≠ q.name) (ls : List Loc) (i j : Nat) :
    (QProg.interp t δ (q :: Δ)) Q ls i j ↔ QProg.interp t δ Δ Q ls i j := by
  simp [QProg.interp, h]

/-- Unfolding of `Exec.Matches` for a query in the program. -/
theorem Exec.Matches.iff_head (q : Query) (Δ : QProg) (e : Exec) (ls : List Loc) :
    Exec.Matches (q :: Δ) e q.name ls ↔
      ls.length = q.params.length ∧
      ∃ j, Δ.interp e.trc.toList e.obs ⬝
        e.trc.toList ⬝ e.obs ⬝ LEnv.empty.bind q.params ls ⊨ q.body : 0 ⇝ j := by
  simp only [Exec.Matches, QProg.interp, if_true]
  constructor
  · rintro ⟨j, h₁, h₂⟩; exact ⟨h₁, j, h₂⟩
  · rintro ⟨h₁, j, h₂⟩; exact ⟨j, h₁, h₂⟩

end CoreJS
