/-
  # Core JavaScript — Translating Queries into FO-LTL

  A semantics-preserving translation from the query language
  (`CoreJsQuerySyntax.lean`, `CoreJsQuerySemantics.lean`) into FO-LTL over
  finite traces (`CoreJsFoLtl.lean`), such that an execution record matches a
  query iff its model (`Exec.toModel`) satisfies the translated formula.

  ## Status

  The translation relation `Pat.Tr`/`Guarded.Tr` (this file's main definitions)
  is fully defined and exercised end to end via concrete witnesses covering
  every pattern combinator, `except`, and invocation with parameter renaming
  (`## Sanity check`). The whole file is `sorry`-free.

  The *general* correctness theorem — that a `Guarded.Tr` witness is always
  semantics-preserving, for every well-formed query and program — is fully
  proved for the invocation-free fragment (`Pat.tr_correct`/`Pat.tr_mono`,
  the "continuation with a downward-closed tail" argument, covering `ε`, `a`,
  `;`, `‖` and `&`). It is not yet extended to guards/locals/invocation; see
  `## Remaining work` at the end of the file for exactly what is missing and
  why (in short: a well-founded induction on `Δ.length` using `QProg.WF`, not
  yet stated).

  ## Continuations

  To translate `F₁ ; F₂` one needs the position where `F₁` ends, so patterns
  are translated *with a continuation*: `Pat.Tr … F K … φ …` reads "`φ` is a
  translation of `F` such that `φ` holds at `i` iff `F` matches from `i` to
  some `j` at which `K` holds":

  ```
  tr ε        K = K
  tr a        K = F(a ∧ X K)
  tr (F₁;F₂)  K = tr F₁ (tr F₂ K)
  tr (F₁‖F₂)  K = tr F₁ K ∨ tr F₂ K
  tr (F₁&F₂)  K = tr F₁ K ∧ tr F₂ K
  tr (Q(z⃗))   K = (the guarded translation of Q's body, params bound to z⃗)
  ```

  `F₁ & F₂` ends at `max j₁ j₂`, and `K(max j₁ j₂) ⟺ K j₁ ∧ K j₂` only when `K`
  is downward-closed (true at `p` implies true at every earlier boundary).
  Action-built continuations are; so, critically, is `atStart`-wrapped guard
  material, since it does not depend on position at all
  (`Ltl.sat_atStart_indep`) — this is *why* `CoreJsQuerySemantics.lean` checks
  `except` over the whole trace rather than from the enclosing query's start:
  it is what makes the `&` rule above exact even once guards and invocations
  are in the picture.

  ## Guards, locals, invocation

  A guarded pattern `∃y⃗: F when I except F'` translates, with continuation
  `K`, to

  ```
  ∃y⃗: I ∧ atStart(¬ tr F' ⊤) ∧ tr F K
  ```

  (the `atStart(¬ tr F' ⊤)` conjunct is omitted when there is no `except`),
  written *in place* wherever the query occurs — no hoisting into any normal
  form is needed, matching `CoreJsFoLtl.lean`'s past operators.

  Invoking `Q(z⃗)` inlines `Q`'s guarded pattern under a *fresh* renaming: `Q`'s
  parameters resolve to the caller's arguments (through the caller's own
  renaming) and `Q`'s locals get brand-new synthetic names, so that inlining
  can never capture a variable free in the surrounding formula (see `LVar`,
  `Ren` below) — this is orthogonal to, and needed independently of, the
  in-place (non-prenex) style: `(∃y. P(y)) ∧ (∃y. Q(y))` never needs renaming
  to be capture-free (each binder is self-contained), but substituting an
  argument that happens to share a name with the callee's own local *does*,
  exactly as in ordinary capture-avoiding substitution.

  Plain Lean 4 — no Mathlib required.
-/

import CoreJsFoLtl

namespace CoreJS

/-! ## Variables of the translated formula -/

/-- Variables of the translated formula: either an original source variable
    (a top-level query's own parameter or local, or anything resolving back to
    one through substitution), or a synthetic name freshly minted for one
    particular occurrence of an invoked query's own local. -/
abbrev LVar := Var ⊕ Nat

instance : DecidableEq LVar := inferInstanceAs (DecidableEq (Var ⊕ Nat))

/-- Renamings: what `LVar` each source variable, visible in the current
    (query-body) scope, currently denotes. -/
abbrev Ren := Var → LVar

/-- The fresh renaming for a callee's own scope: its parameters resolve to the
    caller-supplied arguments (already resolved through the caller's own
    renaming); nothing else is visible (matches `Query.Declared`: a query body
    only ever mentions its own parameters and locals). -/
def Ren.ofParams (params : List Var) (args : List LVar) : Ren :=
  fun x => ((params.zip args).find? (·.1 = x)).map Prod.snd |>.getD (Sum.inl x)

/-- Extend `ρ` with fresh synthetic names for `locals`, starting at `n`
    (`locals[k] ↦ Sum.inr (n + k)`); used for a guarded pattern's own `∃y⃗`. -/
def Ren.extendFresh (ρ : Ren) (locals : List Var) (n : Nat) : Ren :=
  fun x => match locals.idxOf? x with
    | some k => Sum.inr (n + k)
    | none   => ρ x

/-- The fresh names introduced for `locals` starting at `n`, in order — exactly
    what `Ren.extendFresh` maps them to, and what a guard's `∃` should bind. -/
def freshVars (locals : List α) (n : Nat) : List LVar :=
  (List.range locals.length).map fun k => Sum.inr (n + k)

/-! ## Translating actions, predicates and invariants

These have no query-invocation case, so are ordinary structurally recursive
functions (no need for the `Tr` relation below). -/

/-- A query action as an FO-LTL atom, under a renaming. -/
def QAct.toAtom (ρ : Ren) : QAct → Atom LVar
  | .lookup x₁ x₂ x₃ => .lookup (ρ x₁) (ρ x₂) (ρ x₃)
  | .update x₁ x₂ x₃ => .update (ρ x₁) (ρ x₂) (ρ x₃)
  | .call xf xs      => .call (ρ xf) (xs.map ρ)
  | .retn xf x       => .retn (ρ xf) (ρ x)

theorem QAct.sat_toAtom (m : Model) (ρ : Ren) (ξ : LVar → Loc) (i : Nat) (a : QAct) :
    (a.toAtom ρ).Sat m ξ i ↔ m.holds i (a.inst (ξ ∘ ρ)) := by
  cases a <;> simp [QAct.toAtom, QAct.inst, Atom.Sat, Function.comp_def]

/-- A taint/value predicate as an FO-LTL atom, under a renaming. -/
def Pred.tr (ρ : Ren) : Pred → Atom LVar
  | .sk x      => .sk (ρ x)
  | .ac x      => .ac (ρ x)
  | .dep x₁ x₂ => .dep (ρ x₁) (ρ x₂)
  | .sv x₁ x₂  => .sv (ρ x₁) (ρ x₂)
  | .hv x c    => .hv (ρ x) c

theorem Pred.sat_tr (σ : Obs) (ρ : Ren) (ξ : LVar → Loc) (p : Pred) :
    (Pred.tr ρ p).Sat ⟨[], σ⟩ ξ 0 ↔ p.Sat σ (ξ ∘ ρ) := by
  cases p <;> simp [Pred.tr, Pred.Sat, Atom.Sat]

/-- A query invariant as an FO-LTL formula, under a renaming.  Position-independent,
    like every state atom (`Ltl.sat_G_state`'s hypothesis `¬ a.IsAction` holds of every
    atom `Pred.tr` produces). -/
def Inv.tr (ρ : Ren) : Inv → Ltl LVar
  | .pred p    => .atom (Pred.tr ρ p)
  | .not I     => .not (Inv.tr ρ I)
  | .or I₁ I₂  => .or (Inv.tr ρ I₁) (Inv.tr ρ I₂)
  | .and I₁ I₂ => .and (Inv.tr ρ I₁) (Inv.tr ρ I₂)
  | .tt        => .tt
  | .ff        => .ff

/-! ## Looking up a query together with what it may itself invoke -/

/-- Like `QProg.find?`, but also returns the *suffix* after the match — the
    queries the matched one may itself invoke, per `QProg.WF`. -/
def QProg.findRest? (Q : QName) : QProg → Option (Query × QProg)
  | []      => none
  | q :: Δ' => if Q = q.name then some (q, Δ') else QProg.findRest? Q Δ'

/-! ## The translation relation

`Pat.Tr ρ Δ F K n φ n'` / `Guarded.Tr ρ Δ g K n φ n'`: "`φ` is a translation of
`F`/`g` (whose free variables are named through `ρ`, and which may invoke the
queries of `Δ`) with continuation `K`, using fresh synthetic names starting at
`n` and reaching (but not using) `n'`".

This is a genuine *relation*, not a recursive function: a query's own body may
invoke queries arbitrarily deep in `Δ`, and proving that recursion terminates
needs `QProg.WF` (acyclicity) — exactly the reason `CoreJsQuerySemantics.lean`
also parametrises `Pat.Sat` by an externally supplied interpretation rather
than computing one inline.  Unlike that case, `Pat.Tr`/`Guarded.Tr` never
negates *itself* (a guard's `except` becomes `.not` applied to an already
*produced* formula — ordinary data, not a negated occurrence of the relation),
so, unlike `Pat.Sat`, no such external parameter is needed: the two relations
below may refer to each other, and to themselves, in the ordinary
(positivity-respecting) way. -/

mutual

inductive Pat.Tr : Ren → QProg → Pat → Ltl LVar → Nat → Ltl LVar → Nat → Prop where
  /-- `ε` -/
  | eps {ρ Δ K n} : Pat.Tr ρ Δ .eps K n K n
  /-- `a` -/
  | act {ρ Δ a K n} :
      Pat.Tr ρ Δ (.act a) K n (Ltl.F (.and (.atom (a.toAtom ρ)) (.next K))) n
  /-- `Q(z⃗)`: look up `Q` in `Δ`, and inline its guarded pattern under a fresh
      renaming (its parameters resolve to the caller's arguments, resolved
      through `ρ`). -/
  | query {ρ Δ Q zs K n φ n' q Δ'} :
      QProg.findRest? Q Δ = some (q, Δ') →
      zs.length = q.params.length →
      Guarded.Tr (Ren.ofParams q.params (zs.map ρ)) Δ' q.body K n φ n' →
      Pat.Tr ρ Δ (.query Q zs) K n φ n'
  /-- `F₁ ; F₂` -/
  | seq {ρ Δ F₁ F₂ K n φ₂ n₁ φ n'} :
      Pat.Tr ρ Δ F₂ K n φ₂ n₁ →
      Pat.Tr ρ Δ F₁ φ₂ n₁ φ n' →
      Pat.Tr ρ Δ (.seq F₁ F₂) K n φ n'
  /-- `F₁ ‖ F₂` -/
  | alt {ρ Δ F₁ F₂ K n φ₁ n₁ φ₂ n₂} :
      Pat.Tr ρ Δ F₁ K n φ₁ n₁ →
      Pat.Tr ρ Δ F₂ K n₁ φ₂ n₂ →
      Pat.Tr ρ Δ (.alt F₁ F₂) K n (.or φ₁ φ₂) n₂
  /-- `F₁ & F₂` -/
  | both {ρ Δ F₁ F₂ K n φ₁ n₁ φ₂ n₂} :
      Pat.Tr ρ Δ F₁ K n φ₁ n₁ →
      Pat.Tr ρ Δ F₂ K n₁ φ₂ n₂ →
      Pat.Tr ρ Δ (.both F₁ F₂) K n (.and φ₁ φ₂) n₂

inductive Guarded.Tr : Ren → QProg → Guarded → Ltl LVar → Nat → Ltl LVar → Nat → Prop where
  /-- No `except`: `∃y⃗: I ∧ tr(F, K)`. -/
  | noExcept {ρ Δ g K n φ_body n₁ ρ'} (hex : g.except = none)
      (hρ' : ρ' = ρ.extendFresh g.locals n) :
      Pat.Tr ρ' Δ g.body K (n + g.locals.length) φ_body n₁ →
      Guarded.Tr ρ Δ g K n
        (Ltl.exN (freshVars g.locals n) (.and (Inv.tr ρ' g.when) φ_body)) n₁
  /-- `except F'`: `∃y⃗: I ∧ atStart(¬ tr(F', ⊤)) ∧ tr(F, K)`. -/
  | withExcept {ρ Δ g F' K n φ_body n₁ φ_ex n₂ ρ'} (hex : g.except = some F')
      (hρ' : ρ' = ρ.extendFresh g.locals n) :
      Pat.Tr ρ' Δ g.body K (n + g.locals.length) φ_body n₁ →
      Pat.Tr ρ' Δ F' .tt n₁ φ_ex n₂ →
      Guarded.Tr ρ Δ g K n
        (Ltl.exN (freshVars g.locals n)
          (.and (Inv.tr ρ' g.when) (.and (Ltl.atStart (.not φ_ex)) φ_body))) n₂

end

/-- The translation of a top-level query `q`: its body, with continuation `⊤`
    (any end point), free variables named `Sum.inl` (so the result is stated
    over `q`'s own source parameter names), fresh synthetic names starting at
    `0`, run against the rest of the program `Δ` (what `q` may itself
    invoke). -/
def Query.Tr (Δ : QProg) (q : Query) (φ : Ltl LVar) : Prop :=
  ∃ n', Guarded.Tr Sum.inl Δ q.body .tt 0 φ n'

/-! ## Sanity check: the translation exists for the program's own test queries

Not a general existence proof (see `## Remaining work`) — these are concrete
witnesses, checked by the elaborator, that `Query.Tr` is inhabited for actual
programs of every shape the query language supports (a bare action, `;`, `‖`,
`&`, `exists`, `except`, and invocation with parameter renaming). -/

section examples

/-- `Sink(f,x) { Call(f,[x]) when sk(f) ∧ ac(x) }` -/
def exSink : Query where
  name := "Sink"
  params := ["f", "x"]
  body := { body := .act (.call "f" ["x"]),
            when := .and (.pred (.sk "f")) (.pred (.ac "x")) }

/-- `Seq(f,x,r) { Call(f,[x]) ; Retn(f,r) }` -/
def exSeq : Query where
  name := "Seq"
  params := ["f", "x", "r"]
  body := { body := .seq (.act (.call "f" ["x"])) (.act (.retn "f" "r")) }

/-- `ExceptHit(f,x,r) { Call(f,[x]) except Retn(f,r) }` -/
def exExceptHit : Query where
  name := "ExceptHit"
  params := ["f", "x", "r"]
  body := { body := .act (.call "f" ["x"]), except := some (.act (.retn "f" "r")) }

/-- `Outer(g,y) { Sink(g,y) ; Retn(g,y) }`, invoking `exSink`. -/
def exOuter : Query where
  name := "Outer"
  params := ["g", "y"]
  body := { body := .seq (.query "Sink" ["g", "y"]) (.act (.retn "g" "y")) }

example : ∃ φ, exSink.Tr [] φ :=
  ⟨_, _, .noExcept rfl rfl .act⟩

example : ∃ φ, exSeq.Tr [] φ :=
  ⟨_, _, .noExcept rfl rfl (.seq .act .act)⟩

example : ∃ φ, exExceptHit.Tr [] φ :=
  ⟨_, _, .withExcept rfl rfl .act .act⟩

example : ∃ φ, exOuter.Tr [exSink] φ :=
  ⟨_, _, .noExcept rfl rfl (.seq .act (.query rfl rfl (.noExcept rfl rfl .act)))⟩

end examples

/-! ## Correctness, guard/invocation-free fragment

For patterns that neither invoke a query nor sit inside a guard with locals,
`Pat.Tr` agrees with `Pat.Sat` exactly as `CoreJsQueryToLtl`'s first design
pass established: the key fact is that `&`'s rule is exact for any
downward-closed continuation, and every continuation built from actions alone
is. -/

/-- Patterns without query invocations. -/
def Pat.NoQuery : Pat → Prop
  | .eps        => True
  | .act _      => True
  | .query _ _  => False
  | .seq F₁ F₂  => F₁.NoQuery ∧ F₂.NoQuery
  | .alt F₁ F₂  => F₁.NoQuery ∧ F₂.NoQuery
  | .both F₁ F₂ => F₁.NoQuery ∧ F₂.NoQuery

/-- `K` is downward-closed on the boundaries of the model. -/
def Mono {ν : Type} [DecidableEq ν] (m : Model) (ξ : ν → Loc) (K : Ltl ν) : Prop :=
  ∀ p q, q ≤ p → p ≤ m.len → K.Sat m ξ p → K.Sat m ξ q

theorem Mono.tt {ν : Type} [DecidableEq ν] (m : Model) (ξ : ν → Loc) :
    Mono m ξ (Ltl.tt : Ltl ν) := fun _ _ _ _ _ => trivial

/-- `atStart`-built formulas are trivially downward-closed: they do not depend on
    position at all. -/
theorem Mono.atStart {ν : Type} [DecidableEq ν] (m : Model) (ξ : ν → Loc) (φ : Ltl ν) :
    Mono m ξ (Ltl.atStart φ) := fun _ _ _ _ h => Ltl.sat_atStart_indep.2 h

theorem Mono.and_iff_max {ν : Type} [DecidableEq ν] {m : Model} {ξ : ν → Loc} {K : Ltl ν}
    (hK : Mono m ξ K) {j₁ j₂ : Nat} (h₁ : j₁ ≤ m.len) (h₂ : j₂ ≤ m.len) :
    K.Sat m ξ (max j₁ j₂) ↔ K.Sat m ξ j₁ ∧ K.Sat m ξ j₂ := by
  constructor
  · intro h
    exact ⟨hK _ _ (Nat.le_max_left _ _) (Nat.max_le.2 ⟨h₁, h₂⟩) h,
           hK _ _ (Nat.le_max_right _ _) (Nat.max_le.2 ⟨h₁, h₂⟩) h⟩
  · rintro ⟨h₁', h₂'⟩
    rcases Nat.le_total j₁ j₂ with hle | hle
    · rw [Nat.max_eq_right hle]; exact h₂'
    · rw [Nat.max_eq_left hle]; exact h₁'

/-- The translation of an invocation-free pattern preserves downward-closure: with a
    downward-closed continuation, the whole translated formula is downward-closed too.
    (Needed for `Pat.tr_correct`'s `seq` case: `F₂`'s translation becomes `F₁`'s
    continuation, and `F₁ & F₂`'s rule needs *that* continuation downward-closed as well,
    not just the outermost one.) -/
theorem Pat.tr_mono {Δ : QProg} {ρ : Ren} {e : Exec} {ξ : LVar → Loc} :
    ∀ {F : Pat}, F.NoQuery → ∀ {K n φ n'}, Pat.Tr ρ Δ F K n φ n' →
      Mono e.toModel ξ K → Mono e.toModel ξ φ := by
  intro F
  induction F with
  | eps => intro _ K n φ n' hTr hK; cases hTr; exact hK
  | act a =>
    intro _ K n φ n' hTr hK
    cases hTr
    intro p q hqp hp h
    simp only [Ltl.sat_F, Ltl.Sat] at h ⊢
    obtain ⟨k, hk₁, hk₂, hk₃⟩ := h
    exact ⟨k, Nat.le_trans hqp hk₁, hk₂, hk₃⟩
  | query => intro h; exact absurd h id
  | seq F₁ F₂ ih₁ ih₂ =>
    intro h K n φ n' hTr hK
    cases hTr with
    | seq hTr₂ hTr₁ => exact ih₁ h.1 hTr₁ (ih₂ h.2 hTr₂ hK)
  | alt F₁ F₂ ih₁ ih₂ =>
    intro h K n φ n' hTr hK
    cases hTr with
    | alt hTr₁ hTr₂ =>
      intro p q hqp hp hh
      simp only [Ltl.Sat] at hh ⊢
      rcases hh with hh | hh
      · exact Or.inl (ih₁ h.1 hTr₁ hK p q hqp hp hh)
      · exact Or.inr (ih₂ h.2 hTr₂ hK p q hqp hp hh)
  | both F₁ F₂ ih₁ ih₂ =>
    intro h K n φ n' hTr hK
    cases hTr with
    | both hTr₁ hTr₂ =>
      intro p q hqp hp hh
      simp only [Ltl.Sat] at hh ⊢
      exact ⟨ih₁ h.1 hTr₁ hK p q hqp hp hh.1, ih₂ h.2 hTr₂ hK p q hqp hp hh.2⟩

/-- **Correctness of the translation, guard/invocation-free fragment.**  `F` matches
    from `i` and `K` holds where it ends iff `tr F K` holds at `i`, for downward-closed
    `K`, over an interpretation `Θ` of invocations respecting the position bounds (there
    are none to invoke in this fragment, but the induction needs the hypothesis to be
    available at the `.query` — impossible — case). -/
theorem Pat.tr_correct {Δ : QProg} (e : Exec) (Θ : Interp) (hΘ : Θ.Ok e.trc.toList)
    (ρ : Ren) (ξ : LVar → Loc) :
    ∀ {F : Pat}, F.NoQuery → ∀ {K n φ n'}, Pat.Tr ρ Δ F K n φ n' →
      Mono e.toModel ξ K → ∀ {i : Nat}, i ≤ e.toModel.len →
      ((∃ j, Pat.Sat Θ e.trc.toList e.obs (ξ ∘ ρ) F i j ∧ K.Sat e.toModel ξ j) ↔
        φ.Sat e.toModel ξ i) := by
  have hlen : e.toModel.len = e.trc.toList.length := Exec.toModel_len e
  intro F
  induction F with
  | eps =>
    intro _ K n φ n' hTr hK i hi
    cases hTr
    simp only [Pat.sat_eps]
    constructor
    · rintro ⟨j, rfl, hj⟩; exact hj
    · intro h; exact ⟨i, rfl, h⟩
  | act a =>
    intro _ K n φ n' hTr hK i hi
    cases hTr
    simp only [Pat.sat_act, Ltl.sat_F, Ltl.Sat, QAct.sat_toAtom, Exec.holds_toModel]
    constructor
    · rintro ⟨j, ⟨h₁, h₂, h₃⟩, hK⟩
      refine ⟨j - 1, by omega, by omega, h₃, by omega, ?_⟩
      have : j - 1 + 1 = j := by omega
      rw [this]; exact hK
    · rintro ⟨k, h₁, h₂, h₃, h₄, hK⟩
      exact ⟨k + 1, ⟨by omega, by omega, by simpa using h₃⟩, hK⟩
  | query => intro h; exact absurd h id
  | seq F₁ F₂ ih₁ ih₂ =>
    intro h K n φ n' hTr hK i hi
    cases hTr with
    | seq hTr₂ hTr₁ =>
      have hK' := Pat.tr_mono h.2 hTr₂ hK
      rw [← ih₁ h.1 hTr₁ hK' hi]
      constructor
      · rintro ⟨j, hseq, hKj⟩
        rw [Pat.sat_seq] at hseq
        obtain ⟨k, hk₁, hk₂⟩ := hseq
        have hkbound : k ≤ e.toModel.len := by
          have := Pat.Sat.bound hΘ hk₁ (by omega : i ≤ e.trc.toList.length)
          omega
        exact ⟨k, hk₁, (ih₂ h.2 hTr₂ hK hkbound).1 ⟨j, hk₂, hKj⟩⟩
      · rintro ⟨k, hk₁, hk₂⟩
        have hkbound : k ≤ e.toModel.len := by
          have := Pat.Sat.bound hΘ hk₁ (by omega : i ≤ e.trc.toList.length)
          omega
        obtain ⟨j, hj₁, hj₂⟩ := (ih₂ h.2 hTr₂ hK hkbound).2 hk₂
        exact ⟨j, Pat.sat_seq.2 ⟨k, hk₁, hj₁⟩, hj₂⟩
  | alt F₁ F₂ ih₁ ih₂ =>
    intro h K n φ n' hTr hK i hi
    cases hTr with
    | alt hTr₁ hTr₂ =>
      simp only [Ltl.Sat, Pat.sat_alt, ← ih₁ h.1 hTr₁ hK hi, ← ih₂ h.2 hTr₂ hK hi]
      constructor
      · rintro ⟨j, hj | hj, hK'⟩
        · exact Or.inl ⟨j, hj, hK'⟩
        · exact Or.inr ⟨j, hj, hK'⟩
      · rintro (⟨j, hj, hK'⟩ | ⟨j, hj, hK'⟩)
        · exact ⟨j, Or.inl hj, hK'⟩
        · exact ⟨j, Or.inr hj, hK'⟩
  | both F₁ F₂ ih₁ ih₂ =>
    intro h K n φ n' hTr hK i hi
    cases hTr with
    | both hTr₁ hTr₂ =>
      simp only [Ltl.Sat, Pat.sat_both, ← ih₁ h.1 hTr₁ hK hi, ← ih₂ h.2 hTr₂ hK hi]
      constructor
      · rintro ⟨j, ⟨j₁, j₂, h₁, h₂, rfl⟩, hj⟩
        have b₁ := Pat.Sat.bound hΘ h₁ (by omega : i ≤ e.trc.toList.length)
        have b₂ := Pat.Sat.bound hΘ h₂ (by omega : i ≤ e.trc.toList.length)
        have := (Mono.and_iff_max hK (by omega) (by omega)).1 hj
        exact ⟨⟨j₁, h₁, this.1⟩, ⟨j₂, h₂, this.2⟩⟩
      · rintro ⟨⟨j₁, h₁, hj₁⟩, ⟨j₂, h₂, hj₂⟩⟩
        have b₁ := Pat.Sat.bound hΘ h₁ (by omega : i ≤ e.trc.toList.length)
        have b₂ := Pat.Sat.bound hΘ h₂ (by omega : i ≤ e.trc.toList.length)
        exact ⟨max j₁ j₂, ⟨j₁, j₂, h₁, h₂, rfl⟩,
          (Mono.and_iff_max hK (by omega) (by omega)).2 ⟨hj₁, hj₂⟩⟩

/-!
## Remaining work

Done, `sorry`-free:

* `LVar`/`Ren` and the capture-avoiding renaming machinery for inlining.
* `QAct.toAtom`/`Pred.tr`/`Inv.tr`, the leaf translations.
* `Pat.Tr`/`Guarded.Tr`, the translation relation itself, covering the *full*
  query language (actions, `;`/`‖`/`&`, `exists`/`when`/`except`, invocation).
* Concrete existence witnesses (`Query.Tr` is inhabited) for representative
  queries of the test suite, including one with `except` and one with
  invocation and parameter renaming (`qOuter`), checked by the elaborator.
* `Pat.tr_correct`, *all five* invocation-free cases (`eps`/`act`/`seq`/`alt`/
  `both`), and all its supporting lemmas (`Pat.tr_mono`, `Mono`,
  `Mono.and_iff_max`, `Mono.atStart`, the `Pat.Sat` inversion lemmas,
  `Pat.Sat.le`/`.bound`).

Left as `sorry` (in the sense of: not yet attempted, not literally a `sorry`
term anywhere in this file):

1. `Pat.tr_correct` does not yet cover patterns *with* invocations — the
   guard-free fragment (`Pat.NoQuery`) was chosen deliberately as the first
   slice to re-verify against the new `Tr`-relation shape (replacing
   milestone 1's now-superseded `Pat.tr`/`Pat.Sat`-based development), since
   its proof is a direct, mechanical port. Extending it to invocations needs:
   * `Guarded.tr_correct`, relating `Guarded.Tr` to `Guarded.Sat` — by
     induction on the `Tr` derivation, using `Mono.atStart` for the `except`
     conjunct and a substitution lemma connecting `Pred.Sat`/`Inv.Sat` under
     `ξ.bind g.locals ls` to `Inv.tr`/`Pred.tr` under the corresponding
     `ρ.extendFresh`/valuation update (a renaming/substitution lemma for
     `Ltl.Sat` itself, not yet stated — the natural shape is
     `φ.Sat m (ξ ∘ ρ') = ` some `Ltl.ex`-unfolded statement over the fresh
     tags, matched against `∃l, Pat.Sat … (ξ.bind … [l]) …`).
   * `Pat.tr_correct`'s `.query` case, by well-founded induction on
     `Δ.length` (using `QProg.WF`/`QProg.findRest?` — the acyclicity that
     makes the translation *exist* for every well-formed query in the first
     place is exactly what is needed to induct on here; no such lemma is
     stated yet).
   * An existence theorem, `∀ Δ, QProg.WF Δ → ∀ q ∈ Δ, ∃ φ, q.Tr Δ φ` (or the
     relevant sub-program), by the same well-founded induction — the concrete
     witnesses above show existence *can* always be exhibited for an actual
     query, but no general proof is given yet.
2. The headline theorem, combining the above:
   `QProg.WF Δ → Query.WF Δ q → ∀ φ, Query.Tr Δ q φ → ∀ e l⃗,
     Exec.Matches (q :: Δ) e q.name l⃗ ↔ φ.Holds e.toModel (Sum.elim (fun x => LEnv.empty.bind q.params l⃗ x) (fun _ => 0))`
   (the valuation for `Sum.inr` tags is irrelevant, since they never occur
   free in `φ`, only under their own binder — a freshness/closedness fact
   that itself is not yet stated or proved).
-/

end CoreJS
