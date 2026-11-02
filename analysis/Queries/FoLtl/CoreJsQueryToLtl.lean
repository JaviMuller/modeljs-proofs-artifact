/-
  # Core JavaScript — Translating Queries into FO-LTL

  A semantics-preserving translation from the query language
  (`CoreJsQuerySyntax.lean`, `CoreJsQuerySemantics.lean`) into FO-LTL over
  finite traces (`CoreJsFoLtl.lean`), such that an execution record matches a
  query iff its model (`Exec.toModel`) satisfies the translated formula.

  ## Results

  The translation relation `Pat.Tr`/`QBody.Tr` (this file's main definitions)
  is exercised end to end via concrete witnesses covering every pattern
  combinator, `except`, and invocation with parameter renaming
  (`## Sanity check`).

  The *general* correctness theorem holds for the *entire* query
  language including guards, locals and invocation, not just the
  invocation-free fragment: `correct_all` (`PatCorrect`/`QBodyCorrect`, by
  strong induction on the remaining program's length) shows every `Pat.Tr`/
  `QBody.Tr` witness is semantics-preserving for every well-formed program.
  `exists_all` (`PatExists`/`QBodyExists`) shows a translation witness
  always exists. Together these give the headline result,
  `Query.tr_correct`/`Query.exists_tr_correct`: for a well-formed query `q`
  at the head of a well-formed program, matching `q` on an execution record
  is equivalent to that record's model satisfying the (constructively
  produced) translated formula, evaluated at `q`'s own topmost environment
  (`Query.topEnv`). `## Proof structure` at the end of the file summarises
  the supporting machinery this needs.

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
  tr (Q(zs))  K = (the translation of Q's body, params bound to zs)
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

  A query body `∃ ys: F when I except F'` translates, with continuation
  `K`, to

  ```
  ∃ ys: I ∧ atStart(¬ tr F' ⊤) ∧ tr F K
  ```

  (the `atStart(¬ tr F' ⊤)` conjunct is omitted when there is no `except`),
  written *in place* wherever the query occurs — no hoisting into any normal
  form is needed, matching `CoreJsFoLtl.lean`'s past operators.

  Invoking `Q(zs)` inlines `Q`'s body under a *fresh* renaming: `Q`'s
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

import Queries.QueryLanguage.CoreJsQuerySemantics
import Queries.FoLtl.CoreJsFoLtl

namespace CoreJS

/-! ## Variables of the translated formula -/

/-- Variables of the translated formula: either an original source variable
    (a top-level query's own parameter), or a synthetic name freshly minted
    for one particular occurrence of a query body's local — the
    top-level query's own locals included (`QBody.Tr` always renames them). -/
abbrev LVar := Var ⊕ Nat

instance : DecidableEq LVar := inferInstanceAs (DecidableEq (Var ⊕ Nat))

/-- Renamings: what `LVar` each source variable, visible in the current
    (query-body) scope, currently denotes. -/
abbrev Ren := Var → LVar

/-- The fresh renaming for a callee's own scope: its parameters resolve to the
    caller-supplied arguments (already resolved through the caller's own
    renaming), by first-match exactly as `LEnv.bind`; nothing else is visible
    (matches `Query.Declared`: a query body only ever mentions its own
    parameters and locals — `Ren.sat_ofParams` below only claims agreement
    with the semantics' own `LEnv.bind` on `x ∈ params`, which is all a
    declared body ever evaluates `ρ` at). -/
def Ren.ofParams : List Var → List LVar → Ren
  | y :: ys, l :: ls => fun x => if x = y then l else Ren.ofParams ys ls x
  | _,       _        => fun x => Sum.inl x

/-- Extend `ρ` with fresh synthetic names for `locals`, starting at `n`
    (`locals[k] ↦ Sum.inr (n + k)`, by first-match exactly as `LEnv.bind`); used for a
    query body's own `∃ ys`. -/
def Ren.extendFresh (ρ : Ren) : List Var → Nat → Ren
  | [],       _ => ρ
  | y :: ys,  n => fun x => if x = y then Sum.inr n else Ren.extendFresh ρ ys (n + 1) x

/-- The fresh names introduced for `locals` starting at `n`, in order — exactly
    what `Ren.extendFresh` maps them to, and what a guard's `∃` should bind. -/
def freshVars : List α → Nat → List LVar
  | [],      _ => []
  | _ :: ys, n => Sum.inr n :: freshVars ys (n + 1)

theorem freshVars_length (locals : List α) (n : Nat) : (freshVars locals n).length = locals.length := by
  induction locals generalizing n with
  | nil => rfl
  | cons _ ys ih => simp [freshVars, ih]

/-! ### Freshness

The invariant that makes inlining capture-free: at the point a renaming `ρ` is
used with fresh-counter `n`, every synthetic tag `ρ` already produces is below
`n` — so allocating new tags at `n, n+1, …` can never collide with one `ρ`
already uses. `Pat.Tr ρ Δ F K n φ n'`/`QBody.Tr ρ Δ P K n φ n'` preserve it
(`Pat.Tr.fresh`/`QBody.Tr.fresh` below): `φ`'s own tags stay confined to
`[n, n')`, and this is exactly what makes the valuation-update lemmas
(`Ltl.sat_exN`, `Ren.updateFresh_comp_extendFresh`) go through. -/

/-- Every synthetic tag `ρ` produces is below `n`. -/
def Ren.Fresh (ρ : Ren) (n : Nat) : Prop := ∀ x m, ρ x = Sum.inr m → m < n

theorem Ren.Fresh.mono {ρ : Ren} {n n' : Nat} (h : ρ.Fresh n) (hle : n ≤ n') : ρ.Fresh n' :=
  fun x m hx => Nat.lt_of_lt_of_le (h x m hx) hle

theorem Ren.Fresh.ofParams {n : Nat} :
    ∀ {params : List Var} {args : List LVar}, (∀ l ∈ args, ∀ m, l = Sum.inr m → m < n) →
      (Ren.ofParams params args).Fresh n
  | [], _, _ => fun x m hx => by simp only [Ren.ofParams] at hx; nomatch hx
  | _ :: _, [], _ => fun x m hx => by simp only [Ren.ofParams] at hx; nomatch hx
  | y :: ys, l :: ls, hargs => by
      intro x m hx
      simp only [Ren.ofParams] at hx
      split at hx
      · exact hargs l (List.mem_cons_self ..) m hx
      · exact Ren.Fresh.ofParams (fun l' hl' => hargs l' (List.mem_cons_of_mem _ hl')) x m hx

theorem Ren.Fresh.map {ρ : Ren} {n : Nat} (h : ρ.Fresh n) (zs : List Var) :
    ∀ l ∈ zs.map ρ, ∀ m, l = Sum.inr m → m < n := by
  rintro l hl m hm
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hl
  exact h x m hm

theorem Ren.Fresh.extendFresh :
    ∀ (locals : List Var) {ρ : Ren} {n : Nat}, ρ.Fresh n →
      (ρ.extendFresh locals n).Fresh (n + locals.length)
  | [], ρ, n, h => by simp only [Ren.extendFresh, List.length_nil, Nat.add_zero]; exact h
  | y :: ys, ρ, n, h => by
      intro x m hx
      simp only [Ren.extendFresh] at hx
      simp only [List.length_cons]
      split at hx
      · simp only [Sum.inr.injEq] at hx; omega
      · have := Ren.Fresh.extendFresh ys (h.mono (Nat.le_succ n)) x m hx
        omega

/-! ### Simultaneously updating the fresh tags of one occurrence's locals -/

/-- `ξ`, updated at the fresh tags `n, n+1, …, n+ls.length-1` to `ls[0], ls[1], …`;
    everything else (including `Sum.inl` names and out-of-range tags) is untouched. -/
def updateFresh (ξ : LVar → Loc) (n : Nat) (ls : List Loc) : LVar → Loc
  | .inl x => ξ (.inl x)
  | .inr m => if n ≤ m then (ls[m - n]?).getD (ξ (.inr m)) else ξ (.inr m)

theorem updateFresh_nil (ξ : LVar → Loc) (n : Nat) : updateFresh ξ n [] = ξ := by
  funext v; cases v <;> simp [updateFresh]

/-- Overriding tag `n` and updating the tags `n+1, …` from `ls` (in either order) agree. -/
theorem updateFresh_cons (ξ : LVar → Loc) (n : Nat) (l : Loc) (ls : List Loc) :
    updateFresh ξ n (l :: ls) = updateFresh (upd ξ (.inr n) l) (n + 1) ls := by
  funext v
  cases v with
  | inl x => simp [updateFresh, upd]
  | inr m =>
    simp only [updateFresh, upd, Sum.inr.injEq]
    by_cases h1 : n ≤ m
    · by_cases h2 : n + 1 ≤ m
      · have h3 : ¬ m = n := by omega
        rw [if_pos h1, if_pos h2, if_neg h3, show m - n = (m - (n + 1)) + 1 from by omega,
          List.getElem?_cons_succ]
      · have hmn : m = n := by omega
        rw [if_pos h1, if_neg h2, if_pos hmn, show m - n = 0 from by omega,
          List.getElem?_cons_zero, Option.getD_some]
    · have h2 : ¬ n + 1 ≤ m := by omega
      have h3 : ¬ m = n := by omega
      rw [if_neg h1, if_neg h2, if_neg h3]

/-- Unfolding `∃` over the fresh tags of `locals` into an existential over a list of
    locations of matching length. -/
theorem Ltl.sat_exN_fresh (m : Model) (ξ : LVar → Loc) (φ : Ltl LVar) (i n : Nat) :
    ∀ locals : List Var, m ⬝ ξ ⬝ i ⊨ Ltl.exN (freshVars locals n) φ ↔
      ∃ ls : List Loc, ls.length = locals.length ∧ m ⬝ updateFresh ξ n ls ⬝ i ⊨ φ := by
  intro locals
  induction locals generalizing n ξ with
  | nil =>
    simp only [freshVars, Ltl.exN, List.length_nil]
    constructor
    · intro h; exact ⟨[], rfl, by rwa [updateFresh_nil]⟩
    · rintro ⟨ls, hlen, hφ⟩
      have : ls = [] := List.length_eq_zero_iff.1 hlen
      subst this; rwa [updateFresh_nil] at hφ
  | cons y ys ih =>
    have hfold : Ltl.exN (freshVars (y :: ys) n) φ = .ex (Sum.inr n) (Ltl.exN (freshVars ys (n + 1)) φ) := by
      simp [freshVars, Ltl.exN]
    rw [hfold]
    simp only [Ltl.Sat]
    constructor
    · rintro ⟨l, hl⟩
      rw [ih (upd ξ (.inr n) l) (n + 1)] at hl
      obtain ⟨ls, hlen, hφ⟩ := hl
      exact ⟨l :: ls, by simp [hlen], by rwa [updateFresh_cons]⟩
    · rintro ⟨ls, hlen, hφ⟩
      match ls, hlen with
      | l :: ls', hlen =>
        refine ⟨l, (ih (upd ξ (.inr n) l) (n + 1)).2 ⟨ls', by simpa using hlen, ?_⟩⟩
        rwa [← updateFresh_cons]

/-- `upd`'s override at a fresh tag `n` never affects `ξ ∘ ρ` when `ρ.Fresh n`, since `ρ`
    can never itself produce exactly `n`. -/
theorem Ren.Fresh.upd_comp {ρ : Ren} {n : Nat} (h : ρ.Fresh n) (ξ : LVar → Loc) (l : Loc) :
    upd ξ (Sum.inr n) l ∘ ρ = ξ ∘ ρ := by
  funext x
  simp only [Function.comp_apply, upd]
  by_cases hc : ρ x = Sum.inr n
  · exact absurd (h x n hc) (Nat.lt_irrefl n)
  · simp [hc]

/-- Connects the translation's fresh tags to the semantics' `LEnv.bind`: instantiating the
    tags `Ren.extendFresh` introduced for `locals` with `ls` (via `updateFresh`) agrees,
    composed with the caller's own `ρ`, with binding `locals` to `ls` directly in the
    semantics' valuation `ξ ∘ ρ`. -/
theorem Ren.sat_updateFresh_extendFresh :
    ∀ (locals : List Var) {ρ : Ren} {n : Nat}, ρ.Fresh n → ∀ {ls : List Loc},
      ls.length = locals.length → ∀ (ξ : LVar → Loc) (x : Var),
        updateFresh ξ n ls (ρ.extendFresh locals n x) = LEnv.bind (ξ ∘ ρ) locals ls x
  | [], ρ, n, _, ls, hlen, ξ, x => by
      have : ls = [] := List.length_eq_zero_iff.1 hlen
      subst this
      simp [Ren.extendFresh, updateFresh_nil, LEnv.bind]
  | y :: ys, ρ, n, hfresh, ls, hlen, ξ, x => by
      match ls, hlen with
      | l :: ls', hlen =>
        simp only [Ren.extendFresh, LEnv.bind]
        by_cases hxy : x = y
        · subst hxy
          rw [if_pos rfl, if_pos rfl]
          simp [updateFresh]
        · rw [if_neg hxy, if_neg hxy]
          rw [updateFresh_cons,
            Ren.sat_updateFresh_extendFresh ys (hfresh.mono (Nat.le_succ n))
              (by simpa using hlen) (upd ξ (.inr n) l) x,
            hfresh.upd_comp ξ l]

/-- Connects an invoked query's fresh base renaming to the semantics' own valuation for
    its call, `LEnv.empty.bind q.params ls` — but only for `x ∈ params`: `Ren.ofParams`'s
    "not found" fallback (`Sum.inl x`) and `LEnv.empty`'s (`0`) have no reason to agree
    under an arbitrary `ξ`, which is exactly why this is *not* claimed for every `x` (a
    declared query body never evaluates `ρ` outside its own parameters/locals, so this is
    all `QBody.sat_coincide` ever needs it for). -/
theorem Ren.sat_ofParams (ξ : LVar → Loc) :
    ∀ (params : List Var) (args : List LVar), params.length = args.length → ∀ x ∈ params,
      ξ (Ren.ofParams params args x) = LEnv.bind LEnv.empty params (args.map ξ) x
  | [], _, _, x, hx => by simp at hx
  | y :: ys, args, hlen, x, hx => by
      match args, hlen with
      | l :: args', hlen =>
        simp only [Ren.ofParams, LEnv.bind, List.map_cons]
        by_cases hxy : x = y
        · simp [hxy]
        · rw [if_neg hxy, if_neg hxy]
          exact Ren.sat_ofParams ξ ys args' (by simpa using hlen) x
            ((List.mem_cons.1 hx).resolve_left hxy)

/-! ### Insensitivity of a formula to updates at fresh tags it does not itself use

A *continuation* `K` threaded into a translation step is built *before* the
current query body's own fresh tags exist, so its truth must not depend
on what they are eventually set to — otherwise wrapping it under a further
`∃ ys` (as `QBody.Tr` does) could silently change its meaning. `Ltl.Indep φ n`
captures this: `φ` cannot tell `ξ` apart from any `updateFresh ξ m ls` with
`m ≥ n`. It grows monotonically as more fresh tags are consumed
(`Ltl.Indep.mono`), and — critically for `Ltl.ex`/`Ltl.all` — binding one of
`φ`'s *own* (already-below-`n`) tags preserves `Indep n` at the *same* `n`,
not a smaller one: the update ranges this predicate ever has to withstand
never reach back down to an already-bound tag. -/

/-- `φ` cannot distinguish `ξ` from `updateFresh ξ m ls` for any `m ≥ n`. -/
def Ltl.Indep (φ : Ltl LVar) (n : Nat) : Prop :=
  ∀ (m : Model) (ξ : LVar → Loc) (k : Nat) (ls : List Loc), n ≤ k →
    ∀ i, m ⬝ ξ ⬝ i ⊨ φ ↔ m ⬝ updateFresh ξ k ls ⬝ i ⊨ φ

theorem Ltl.Indep.mono {φ : Ltl LVar} {n n' : Nat} (h : φ.Indep n) (hn : n ≤ n') : φ.Indep n' :=
  fun m ξ k ls hk i => h m ξ k ls (Nat.le_trans hn hk) i

theorem Ltl.Indep.tt (n : Nat) : (Ltl.tt : Ltl LVar).Indep n := fun _ _ _ _ _ _ => Iff.rfl
theorem Ltl.Indep.ff (n : Nat) : (Ltl.ff : Ltl LVar).Indep n := fun _ _ _ _ _ _ => Iff.rfl

theorem Ltl.Indep.not {φ : Ltl LVar} {n : Nat} (h : φ.Indep n) : (Ltl.not φ).Indep n :=
  fun m ξ k ls hk i => by simp only [Ltl.Sat, h m ξ k ls hk i]

theorem Ltl.Indep.and {φ ψ : Ltl LVar} {n : Nat} (h1 : φ.Indep n) (h2 : ψ.Indep n) :
    (Ltl.and φ ψ).Indep n :=
  fun m ξ k ls hk i => by simp only [Ltl.Sat, h1 m ξ k ls hk i, h2 m ξ k ls hk i]

theorem Ltl.Indep.or {φ ψ : Ltl LVar} {n : Nat} (h1 : φ.Indep n) (h2 : ψ.Indep n) :
    (Ltl.or φ ψ).Indep n :=
  fun m ξ k ls hk i => by simp only [Ltl.Sat, h1 m ξ k ls hk i, h2 m ξ k ls hk i]

theorem Ltl.Indep.next {φ : Ltl LVar} {n : Nat} (h : φ.Indep n) : (Ltl.next φ).Indep n :=
  fun m ξ k ls hk i => by simp only [Ltl.Sat, h m ξ k ls hk (i + 1)]

theorem Ltl.Indep.yesterday {φ : Ltl LVar} {n : Nat} (h : φ.Indep n) :
    (Ltl.yesterday φ).Indep n :=
  fun m ξ k ls hk i => by simp only [Ltl.Sat, h m ξ k ls hk (i - 1)]

theorem Ltl.Indep.until {φ ψ : Ltl LVar} {n : Nat} (h1 : φ.Indep n) (h2 : ψ.Indep n) :
    (Ltl.until φ ψ).Indep n := by
  intro m ξ k ls hk i
  simp only [Ltl.Sat]
  constructor
  · rintro ⟨p, hp1, hp2, hp3, hp4⟩
    exact ⟨p, hp1, hp2, (h2 m ξ k ls hk p).1 hp3,
      fun q hq1 hq2 => (h1 m ξ k ls hk q).1 (hp4 q hq1 hq2)⟩
  · rintro ⟨p, hp1, hp2, hp3, hp4⟩
    exact ⟨p, hp1, hp2, (h2 m ξ k ls hk p).2 hp3,
      fun q hq1 hq2 => (h1 m ξ k ls hk q).2 (hp4 q hq1 hq2)⟩

theorem Ltl.Indep.since {φ ψ : Ltl LVar} {n : Nat} (h1 : φ.Indep n) (h2 : ψ.Indep n) :
    (Ltl.since φ ψ).Indep n := by
  intro m ξ k ls hk i
  simp only [Ltl.Sat]
  constructor
  · rintro ⟨p, hp1, hp2, hp3⟩
    exact ⟨p, hp1, (h2 m ξ k ls hk p).1 hp2, fun q hq1 hq2 => (h1 m ξ k ls hk q).1 (hp3 q hq1 hq2)⟩
  · rintro ⟨p, hp1, hp2, hp3⟩
    exact ⟨p, hp1, (h2 m ξ k ls hk p).2 hp2, fun q hq1 hq2 => (h1 m ξ k ls hk q).2 (hp3 q hq1 hq2)⟩

/-- Binding one of `φ`'s own already-consumed tags (`< n`) preserves `Indep n` — the
    update ranges it has to withstand start at `≥ n > x`, so they never reach `x`. -/
theorem Ltl.Indep.ex {x : LVar} {φ : Ltl LVar} {n : Nat}
    (hx : ∀ m, x = Sum.inr m → m < n) (h : φ.Indep n) : (Ltl.ex x φ).Indep n := by
  intro m ξ k ls hk i
  have hxk : ∀ m', x = Sum.inr m' → m' < k := fun m' hm' => Nat.lt_of_lt_of_le (hx m' hm') hk
  have hcomm : ∀ l : Loc, upd (updateFresh ξ k ls) x l = updateFresh (upd ξ x l) k ls := by
    intro l
    funext v
    cases v with
    | inl y => simp [upd, updateFresh]
    | inr m' =>
      simp only [upd, updateFresh]
      by_cases hv : (Sum.inr m' : LVar) = x
      · have hlt := hxk m' hv.symm
        have hnk : ¬ k ≤ m' := by omega
        simp [hv, hnk]
      · simp [hv]
  simp only [Ltl.Sat]
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨l, ?_⟩
    rw [hcomm l]
    exact (h m (upd ξ x l) k ls hk i).1 hl
  · rintro ⟨l, hl⟩
    rw [hcomm l] at hl
    exact ⟨l, (h m (upd ξ x l) k ls hk i).2 hl⟩

theorem Ltl.Indep.all {x : LVar} {φ : Ltl LVar} {n : Nat}
    (hx : ∀ m, x = Sum.inr m → m < n) (h : φ.Indep n) : (Ltl.all x φ).Indep n := by
  intro m ξ k ls hk i
  have hxk : ∀ m', x = Sum.inr m' → m' < k := fun m' hm' => Nat.lt_of_lt_of_le (hx m' hm') hk
  have hcomm : ∀ l, upd (updateFresh ξ k ls) x l = updateFresh (upd ξ x l) k ls := by
    intro l
    funext v
    cases v with
    | inl y => simp [upd, updateFresh]
    | inr m' =>
      simp only [upd, updateFresh]
      by_cases hv : (Sum.inr m' : LVar) = x
      · have := hxk m' hv.symm
        have hnk : ¬ k ≤ m' := by omega
        simp [hv, hnk]
      · simp [hv]
  simp only [Ltl.Sat]
  constructor
  · intro hl l
    rw [hcomm l]
    exact (h m (upd ξ x l) k ls hk i).1 (hl l)
  · intro hl l
    have := hl l
    rw [hcomm l] at this
    exact (h m (upd ξ x l) k ls hk i).2 this

/-- Every value `ρ` produces for a query variable is untouched by an update ranging over
    `≥ n`, given `ρ.Fresh n`. -/
theorem Ren.Fresh.updateFresh_ren {ρ : Ren} {n k : Nat} (hfresh : ρ.Fresh n) (hk : n ≤ k)
    (ξ : LVar → Loc) (ls : List Loc) (v : Var) : updateFresh ξ k ls (ρ v) = ξ (ρ v) := by
  cases hc : ρ v with
  | inl x => rfl
  | inr m => simp [updateFresh, Nat.not_le.2 (Nat.lt_of_lt_of_le (hfresh v m hc) hk)]

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
    m ⬝ ξ ⬝ i ⊨ a.toAtom ρ ↔ m.holds i (a.inst (ξ ∘ ρ)) := by
  cases a <;> simp [QAct.toAtom, QAct.inst, Atom.Sat, Function.comp_def]

/-- A taint/value predicate as an FO-LTL atom, under a renaming. -/
def Pred.tr (ρ : Ren) : Pred → Atom LVar
  | .sk x      => .sk (ρ x)
  | .ac x      => .ac (ρ x)
  | .dep x₁ x₂ => .dep (ρ x₁) (ρ x₂)
  | .sv x₁ x₂  => .sv (ρ x₁) (ρ x₂)
  | .hv x c    => .hv (ρ x) c

theorem Pred.sat_tr (m : Model) (ρ : Ren) (ξ : LVar → Loc) (i : Nat) (p : Pred) :
    m ⬝ ξ ⬝ i ⊨ Pred.tr ρ p ↔ m.obs ⬝ (ξ ∘ ρ) ⊨ p := by
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

theorem Inv.sat_tr (m : Model) (ρ : Ren) (ξ : LVar → Loc) (i : Nat) :
    ∀ I : Inv, m ⬝ ξ ⬝ i ⊨ Inv.tr ρ I ↔ m.obs ⬝ (ξ ∘ ρ) ⊨ I
  | .pred p    => Pred.sat_tr m ρ ξ i p
  | .not I     => by simp [Inv.tr, Ltl.Sat, Inv.Sat, Inv.sat_tr m ρ ξ i I]
  | .or I₁ I₂  => by simp [Inv.tr, Ltl.Sat, Inv.Sat, Inv.sat_tr m ρ ξ i I₁, Inv.sat_tr m ρ ξ i I₂]
  | .and I₁ I₂ => by simp [Inv.tr, Ltl.Sat, Inv.Sat, Inv.sat_tr m ρ ξ i I₁, Inv.sat_tr m ρ ξ i I₂]
  | .tt        => by simp [Inv.tr, Ltl.Sat, Inv.Sat]
  | .ff        => by simp [Inv.tr, Ltl.Sat, Inv.Sat]

/-- A translated action atom is independent of any update at or beyond `ρ`'s own range. -/
theorem Ltl.Indep.qact {ρ : Ren} {n : Nat} (hfresh : ρ.Fresh n) (a : QAct) :
    (Ltl.atom (a.toAtom ρ) : Ltl LVar).Indep n := by
  intro m ξ k ls hk i
  have hveq : ∀ v : Var, updateFresh ξ k ls (ρ v) = ξ (ρ v) := hfresh.updateFresh_ren hk ξ ls
  have hveqs : ∀ vs : List Var, (vs.map ρ).map (updateFresh ξ k ls) = (vs.map ρ).map ξ :=
    fun vs => List.map_congr_left (fun w hw => by
      obtain ⟨v, _, rfl⟩ := List.mem_map.1 hw; exact hveq v)
  cases a <;> simp [Ltl.Sat, Atom.Sat, QAct.toAtom, hveq, List.map_map, Function.comp_def, hveqs]

/-- A translated taint/value atom is likewise independent. -/
theorem Ltl.Indep.pred {ρ : Ren} {n : Nat} (hfresh : ρ.Fresh n) (p : Pred) :
    (Ltl.atom (Pred.tr ρ p) : Ltl LVar).Indep n := by
  intro m ξ k ls hk i
  have hveq : ∀ v : Var, updateFresh ξ k ls (ρ v) = ξ (ρ v) := hfresh.updateFresh_ren hk ξ ls
  cases p <;> simp [Ltl.Sat, Atom.Sat, Pred.tr, hveq]

/-- A translated invariant is independent, for the same reason, by structural induction. -/
theorem Ltl.Indep.inv {ρ : Ren} {n : Nat} (hfresh : ρ.Fresh n) : ∀ I : Inv, (Inv.tr ρ I).Indep n
  | .pred p    => Ltl.Indep.pred hfresh p
  | .not I     => (Ltl.Indep.inv hfresh I).not
  | .or I₁ I₂  => (Ltl.Indep.inv hfresh I₁).or (Ltl.Indep.inv hfresh I₂)
  | .and I₁ I₂ => (Ltl.Indep.inv hfresh I₁).and (Ltl.Indep.inv hfresh I₂)
  | .tt        => Ltl.Indep.tt n
  | .ff        => Ltl.Indep.ff n

/-- `first` mentions no query variable at all, so it is independent at every range. -/
theorem Ltl.Indep.first (n : Nat) : (Ltl.first : Ltl LVar).Indep n :=
  ((Ltl.Indep.tt n).yesterday).not

/-- `atStart` preserves independence. -/
theorem Ltl.Indep.atStart {φ : Ltl LVar} {n : Nat} (h : φ.Indep n) : (Ltl.atStart φ).Indep n :=
  (Ltl.Indep.tt n).since (h.and (Ltl.Indep.first n))

/-- Binding a *list* of already-consumed tags preserves `Indep`, one `Ltl.Indep.ex` per
    element (`Ltl.exN`'s own shape: outermost binder first). -/
theorem Ltl.Indep.exN {φ : Ltl LVar} {n : Nat} :
    ∀ {vs : List LVar}, (∀ v ∈ vs, ∀ m, v = Sum.inr m → m < n) → φ.Indep n →
      (Ltl.exN vs φ).Indep n
  | [],      _,   h => h
  | v :: _, hvs, h =>
      Ltl.Indep.ex (hvs v (List.mem_cons_self ..))
        (Ltl.Indep.exN (fun v' hv' => hvs v' (List.mem_cons_of_mem _ hv')) h)

/-- Every fresh tag `freshVars locals n` introduces is below `n + locals.length`. -/
theorem freshVars_lt {α : Type} (locals : List α) (n : Nat) :
    ∀ v ∈ freshVars locals n, ∀ m, v = Sum.inr m → m < n + locals.length := by
  induction locals generalizing n with
  | nil => simp [freshVars]
  | cons _ ys ih =>
    intro v hv m hm
    simp only [freshVars, List.mem_cons] at hv
    simp only [List.length_cons]
    rcases hv with hv | hv
    · subst hv
      simp only [Sum.inr.injEq] at hm
      omega
    · have := ih (n + 1) v hv m hm
      omega

/-! ## Looking up a query together with what it may itself invoke -/

/-- Like `QProg.find?`, but also returns the *suffix* after the match — the
    queries the matched one may itself invoke, per `QProg.WF`. -/
def QProg.findRest? (Q : QName) : QProg → Option (Query × QProg)
  | []      => none
  | q :: Δ' => if Q = q.name then some (q, Δ') else QProg.findRest? Q Δ'

/-- `QProg.findRest?` gives a strictly shorter program: what the matched query may itself
    invoke. This is the well-founded measure the correctness/existence proofs induct on. -/
theorem QProg.findRest?_length_lt {Q : QName} :
    ∀ {Δ : QProg} {q : Query} {Δ' : QProg}, QProg.findRest? Q Δ = some (q, Δ') →
      Δ'.length < Δ.length
  | [], q, Δ', h => by simp [QProg.findRest?] at h
  | q₀ :: Δ₀, q, Δ', h => by
      simp only [QProg.findRest?] at h
      by_cases hQ : Q = q₀.name
      · rw [if_pos hQ] at h
        injection Option.some.inj h with h1 h2
        subst h2
        simp
      · rw [if_neg hQ] at h
        exact Nat.lt_succ_of_lt (QProg.findRest?_length_lt h)

/-- `QProg.interp`'s definition unfolded at a query found via `findRest?`: exactly
    `QProg.interp`'s own traversal, since both recurse identically on `Q = q.name`. -/
theorem QProg.interp_findRest (t : List Act) (δ : Obs) (Q : QName) (ls : List Loc) (i j : Nat) :
    ∀ {Δ : QProg} {q : Query} {Δ' : QProg}, QProg.findRest? Q Δ = some (q, Δ') →
      (QProg.interp t δ Δ Q ls i j ↔
        ls.length = q.params.length ∧
        QProg.interp t δ Δ' ⬝ t ⬝ δ ⬝ LEnv.empty.bind q.params ls ⊨ q.body : i ⇝ j)
  | [], q, Δ', h => by simp [QProg.findRest?] at h
  | q₀ :: Δ₀, q, Δ', h => by
      simp only [QProg.findRest?] at h
      by_cases hQ : Q = q₀.name
      · rw [if_pos hQ] at h
        injection Option.some.inj h with h1 h2
        subst h1; subst h2
        simp only [QProg.interp, if_pos hQ]
      · rw [if_neg hQ] at h
        simp only [QProg.interp, if_neg hQ]
        exact QProg.interp_findRest t δ Q ls i j h

/-- The query found via `findRest?` is declared, and what it may itself invoke is
    well formed — what the correctness theorem's `query` case needs from `QProg.WF Δ`
    (nothing about arity/target-existence, since `Pat.Tr.query`'s own premises already
    require those). -/
theorem QProg.WF.findRest :
    ∀ {Δ : QProg} {Q : QName} {q : Query} {Δ' : QProg}, QProg.WF Δ →
      QProg.findRest? Q Δ = some (q, Δ') → q.WF Δ' ∧ QProg.WF Δ'
  | [], _, _, _, _, h => by simp [QProg.findRest?] at h
  | q₀ :: Δ₀, Q, q, Δ', hwf, h => by
      simp only [QProg.findRest?] at h
      by_cases hQ : Q = q₀.name
      · rw [if_pos hQ] at h
        injection Option.some.inj h with h1 h2
        subst h1; subst h2
        exact ⟨hwf.1, hwf.2.2⟩
      · rw [if_neg hQ] at h
        exact QProg.WF.findRest hwf.2.2 h

/-- `QProg.find?` and `QProg.findRest?` traverse `Δ` identically, so agree on whether a
    query is found (`QProg.findRest?` additionally reports the rest of the program). -/
theorem QProg.find?_eq_some_iff_findRest? {Q : QName} :
    ∀ {Δ : QProg} {q : Query}, QProg.find? Δ Q = some q ↔ ∃ Δ', QProg.findRest? Q Δ = some (q, Δ')
  | [], q => by simp [QProg.find?, QProg.findRest?]
  | q₀ :: Δ₀, q => by
      by_cases hQ : Q = q₀.name
      · simp [QProg.find?, QProg.findRest?, hQ, BEq.beq]
      · have hQ' : ¬ (q₀.name == Q) = true := by simp [BEq.beq]; exact fun h => hQ h.symm
        simp only [QProg.find?, List.find?, hQ']
        rw [QProg.findRest?, if_neg hQ]
        exact QProg.find?_eq_some_iff_findRest? (Δ := Δ₀)

/-- Every invocation in `F` names a query of `Δ` (with the *rest* it may itself invoke)
    and passes as many arguments as that query has parameters — the fact needed to
    *construct* a `Pat.Tr` witness (mirrors `Query.CallsOK`, phrased via `findRest?` so
    the recursive query case has what it needs). -/
def Pat.CallsOK (Δ : QProg) (F : Pat) : Prop :=
  ∀ c ∈ F.calls, ∃ q Δ', QProg.findRest? c.1 Δ = some (q, Δ') ∧ q.params.length = c.2.length

/-- The same, for a query body's pattern and excluded pattern. -/
def QBody.CallsOK (Δ : QProg) (P : QBody) : Prop :=
  ∀ c ∈ P.calls, ∃ q Δ', QProg.findRest? c.1 Δ = some (q, Δ') ∧ q.params.length = c.2.length

theorem Pat.CallsOK.seq {Δ : QProg} {F₁ F₂ : Pat} (h : Pat.CallsOK Δ (.seq F₁ F₂)) :
    Pat.CallsOK Δ F₁ ∧ Pat.CallsOK Δ F₂ :=
  ⟨fun c hc => h c (List.mem_append.2 (Or.inl hc)), fun c hc => h c (List.mem_append.2 (Or.inr hc))⟩

theorem Pat.CallsOK.alt {Δ : QProg} {F₁ F₂ : Pat} (h : Pat.CallsOK Δ (.alt F₁ F₂)) :
    Pat.CallsOK Δ F₁ ∧ Pat.CallsOK Δ F₂ :=
  ⟨fun c hc => h c (List.mem_append.2 (Or.inl hc)), fun c hc => h c (List.mem_append.2 (Or.inr hc))⟩

theorem Pat.CallsOK.both {Δ : QProg} {F₁ F₂ : Pat} (h : Pat.CallsOK Δ (.both F₁ F₂)) :
    Pat.CallsOK Δ F₁ ∧ Pat.CallsOK Δ F₂ :=
  ⟨fun c hc => h c (List.mem_append.2 (Or.inl hc)), fun c hc => h c (List.mem_append.2 (Or.inr hc))⟩

theorem QBody.CallsOK.pattern {Δ : QProg} {P : QBody} (h : QBody.CallsOK Δ P) :
    Pat.CallsOK Δ P.pattern :=
  fun c hc => h c (List.mem_append.2 (Or.inl hc))

theorem QBody.CallsOK.except {Δ : QProg} {P : QBody} {F' : Pat} (h : QBody.CallsOK Δ P)
    (he : P.except = some F') : Pat.CallsOK Δ F' :=
  fun c hc => h c (List.mem_append.2 (Or.inr (by rw [he]; exact hc)))

/-- A query found via `findRest?`'s own invocations are answerable in the rest of the
    program it may itself invoke — `Query.CallsOK` restated via `findRest?`. -/
theorem Query.CallsOK.body {Δ : QProg} {q : Query} (h : q.CallsOK Δ) :
    QBody.CallsOK Δ q.body :=
  fun c hc => by
    obtain ⟨q', hfind, harity⟩ := h c hc
    obtain ⟨Δ', hfind'⟩ := QProg.find?_eq_some_iff_findRest?.1 hfind
    exact ⟨q', Δ', hfind', harity⟩

/-! ## The translation relation

`Pat.Tr ρ Δ F K n φ n'` / `QBody.Tr ρ Δ P K n φ n'`: "`φ` is a translation of
`F`/`P` (whose free variables are named through `ρ`, and which may invoke the
queries of `Δ`) with continuation `K`, using fresh synthetic names starting at
`n` and reaching (but not using) `n'`".

This is a genuine *relation*, not a recursive function: a query's own body may
invoke queries arbitrarily deep in `Δ`, and proving that recursion terminates
needs `QProg.WF` (acyclicity) — exactly the reason `CoreJsQuerySemantics.lean`
also parametrises `Pat.Sat` by an externally supplied interpretation rather
than computing one inline.  Unlike that case, `Pat.Tr`/`QBody.Tr` never
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
  /-- `Q(zs)`: look up `Q` in `Δ`, and inline its body under a fresh
      renaming (its parameters resolve to the caller's arguments, resolved
      through `ρ`). -/
  | query {ρ Δ Q zs K n φ n' q Δ'} :
      QProg.findRest? Q Δ = some (q, Δ') →
      zs.length = q.params.length →
      QBody.Tr (Ren.ofParams q.params (zs.map ρ)) Δ' q.body K n φ n' →
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

inductive QBody.Tr : Ren → QProg → QBody → Ltl LVar → Nat → Ltl LVar → Nat → Prop where
  /-- No `except`: `∃ ys: I ∧ tr(F, K)`. -/
  | noExcept {ρ Δ P K n φ_pat n₁ ρ'} (hex : P.except = none)
      (hρ' : ρ' = ρ.extendFresh P.locals n) :
      Pat.Tr ρ' Δ P.pattern K (n + P.locals.length) φ_pat n₁ →
      QBody.Tr ρ Δ P K n
        (Ltl.exN (freshVars P.locals n) (.and (Inv.tr ρ' P.when) φ_pat)) n₁
  /-- `except F'`: `∃ ys: I ∧ atStart(¬ tr(F', ⊤)) ∧ tr(F, K)`. -/
  | withExcept {ρ Δ P F' K n φ_pat n₁ φ_ex n₂ ρ'} (hex : P.except = some F')
      (hρ' : ρ' = ρ.extendFresh P.locals n) :
      Pat.Tr ρ' Δ P.pattern K (n + P.locals.length) φ_pat n₁ →
      Pat.Tr ρ' Δ F' .tt n₁ φ_ex n₂ →
      QBody.Tr ρ Δ P K n
        (Ltl.exN (freshVars P.locals n)
          (.and (Inv.tr ρ' P.when) (.and (Ltl.atStart (.not φ_ex)) φ_pat))) n₂

end

/-- The translation of a top-level query `q`: its body, with continuation `⊤`
    (any end point), free variables named `Sum.inl` (so the result is stated
    over `q`'s own source parameter names), fresh synthetic names starting at
    `0`, run against the rest of the program `Δ` (what `q` may itself
    invoke). -/
def Query.Tr (Δ : QProg) (q : Query) (φ : Ltl LVar) : Prop :=
  ∃ n', QBody.Tr Sum.inl Δ q.body .tt 0 φ n'

/-! ## Sanity check: the translation exists for the program's own test queries

Superseded as a existence *proof* by `exists_all` below (which covers every
well-formed program, not just these), but kept as concrete witnesses, checked
by the elaborator, that `Query.Tr` is inhabited for actual programs of every
shape the query language supports (a bare action, `;`, `‖`, `&`, `exists`,
`except`, and invocation with parameter renaming) — useful when debugging a
change to the translation relation itself. -/

section examples

/-- `Sink(f,x) { Call(f,[x]) when sk(f) ∧ ac(x) }` -/
def exSink : Query where
  name := "Sink"
  params := ["f", "x"]
  body := { pattern := .act (.call "f" ["x"]),
            when := .and (.pred (.sk "f")) (.pred (.ac "x")) }

/-- `Seq(f,x,r) { Call(f,[x]) ; Retn(f,r) }` -/
def exSeq : Query where
  name := "Seq"
  params := ["f", "x", "r"]
  body := { pattern := .seq (.act (.call "f" ["x"])) (.act (.retn "f" "r")) }

/-- `ExceptHit(f,x,r) { Call(f,[x]) except Retn(f,r) }` -/
def exExceptHit : Query where
  name := "ExceptHit"
  params := ["f", "x", "r"]
  body := { pattern := .act (.call "f" ["x"]), except := some (.act (.retn "f" "r")) }

/-- `Outer(g,y) { Sink(g,y) ; Retn(g,y) }`, invoking `exSink`. -/
def exOuter : Query where
  name := "Outer"
  params := ["g", "y"]
  body := { pattern := .seq (.query "Sink" ["g", "y"]) (.act (.retn "g" "y")) }

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
  ∀ p q, q ≤ p → p ≤ m.len → m ⬝ ξ ⬝ p ⊨ K → m ⬝ ξ ⬝ q ⊨ K

theorem Mono.tt {ν : Type} [DecidableEq ν] (m : Model) (ξ : ν → Loc) :
    Mono m ξ (Ltl.tt : Ltl ν) := fun _ _ _ _ _ => trivial

/-- `atStart`-built formulas are trivially downward-closed: they do not depend on
    position at all. -/
theorem Mono.atStart {ν : Type} [DecidableEq ν] (m : Model) (ξ : ν → Loc) (φ : Ltl ν) :
    Mono m ξ (Ltl.atStart φ) := fun _ _ _ _ h => Ltl.sat_atStart_indep.2 h

/-- `F ψ` is downward-closed for *any* `ψ`: the same later witness for "eventually"
    still lies past an earlier boundary. -/
theorem Mono.F {ν : Type} [DecidableEq ν] (m : Model) (ξ : ν → Loc) (ψ : Ltl ν) :
    Mono m ξ (Ltl.F ψ) := by
  intro p q hqp hp h
  rw [Ltl.sat_F] at h ⊢
  obtain ⟨k, hk1, hk2, hk3⟩ := h
  exact ⟨k, Nat.le_trans hqp hk1, hk2, hk3⟩

theorem Mono.or {ν : Type} [DecidableEq ν] {m : Model} {ξ : ν → Loc} {φ ψ : Ltl ν}
    (h1 : Mono m ξ φ) (h2 : Mono m ξ ψ) : Mono m ξ (Ltl.or φ ψ) := by
  intro p q hqp hp h
  simp only [Ltl.Sat] at h ⊢
  rcases h with h | h
  · exact Or.inl (h1 p q hqp hp h)
  · exact Or.inr (h2 p q hqp hp h)

theorem Mono.and {ν : Type} [DecidableEq ν] {m : Model} {ξ : ν → Loc} {φ ψ : Ltl ν}
    (h1 : Mono m ξ φ) (h2 : Mono m ξ ψ) : Mono m ξ (Ltl.and φ ψ) := by
  intro p q hqp hp h
  simp only [Ltl.Sat] at h ⊢
  exact ⟨h1 p q hqp hp h.1, h2 p q hqp hp h.2⟩

/-- An `n`-insensitive `K` is Mono at `ξ` iff it is Mono at any `updateFresh`-modified
    valuation, for any range at or above `n` — used when the recursive correctness fact
    for a query body's pattern is applied at `updateFresh ξ n ls` rather than `ξ`
    itself. -/
theorem Ltl.Indep.mono_iff {K : Ltl LVar} {n : Nat} (hKI : K.Indep n) {m : Model}
    {ξ : LVar → Loc} {k : Nat} (hk : n ≤ k) (ls : List Loc) :
    Mono m ξ K ↔ Mono m (updateFresh ξ k ls) K := by
  constructor
  · intro hM p q hqp hp h
    rw [← hKI m ξ k ls hk q]
    exact hM p q hqp hp ((hKI m ξ k ls hk p).2 h)
  · intro hM p q hqp hp h
    rw [hKI m ξ k ls hk q]
    exact hM p q hqp hp ((hKI m ξ k ls hk p).1 h)

theorem Mono.and_iff_max {ν : Type} [DecidableEq ν] {m : Model} {ξ : ν → Loc} {K : Ltl ν}
    (hK : Mono m ξ K) {j₁ j₂ : Nat} (h₁ : j₁ ≤ m.len) (h₂ : j₂ ≤ m.len) :
    m ⬝ ξ ⬝ max j₁ j₂ ⊨ K ↔ m ⬝ ξ ⬝ j₁ ⊨ K ∧ m ⬝ ξ ⬝ j₂ ⊨ K := by
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
      ((∃ j, Θ ⬝ e.trc.toList ⬝ e.obs ⬝ ξ ∘ ρ ⊨ F : i ⇝ j ∧ e.toModel ⬝ ξ ⬝ j ⊨ K) ↔
        e.toModel ⬝ ξ ⬝ i ⊨ φ) := by
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

/-! ## The general correctness theorem

`Pat.Tr`/`QBody.Tr` are mutually inductive `Prop`s, and this Lean version's
`induction` tactic does not support inducting on a mutual-family hypothesis
directly (confirmed experimentally). The two correctness facts are therefore
proved together by *explicit* strong induction on `Δ.length`, with an
ordinary structural induction on the (non-mutual) `Pat` syntax nested inside
each step: a query invocation strictly shortens `Δ` (`QProg.findRest?_length_lt`)
and defers to `QBody.Tr`'s correctness at that smaller level; every other
case keeps `Δ` fixed and recurses on `Pat`/`QBody`'s own structure.

Each fact carries *four* conjuncts, not just the expected correctness `iff`:
the fresh counter only grows (`n ≤ n'`), the produced formula is `Indep n'`,
the produced formula is `Mono`-preserving for *any* valuation whenever the
continuation is (needed because a query body's `∃ ys` re-derives its
pattern's correctness at `updateFresh ξ n ls`, a valuation different from the
one the outer goal is stated at), and the correctness `iff` itself. -/

/-- An invariant's translation is position-independent (`Inv.sat_tr`'s right-hand side
    does not mention a position at all), hence trivially `Mono` for any valuation. -/
theorem Mono.inv (ρ : Ren) (I : Inv) (m : Model) (ξ : LVar → Loc) : Mono m ξ (Inv.tr ρ I) := by
  intro p q _ _ h
  rw [Inv.sat_tr] at h ⊢
  exact h

/-- For every program of length `≤ N`, a `Pat.Tr` derivation is exactly right: it
    consumes fresh tags starting no lower than it says, produces a formula insensitive
    to anything from its own output counter on, preserves `Mono`-ness of the
    continuation at any valuation, and agrees with `Pat.Sat` for any downward-closed,
    `n`-insensitive continuation. -/
def PatCorrect (N : Nat) : Prop :=
  ∀ (e : Exec) (Δ : QProg) (ρ : Ren), Δ.length ≤ N → QProg.WF Δ →
  ∀ (F : Pat) (n : Nat) (K φ : Ltl LVar) (n' : Nat),
    ρ.Fresh n → K.Indep n → Pat.Tr ρ Δ F K n φ n' →
    n ≤ n' ∧ φ.Indep n' ∧
    (∀ ξ, Mono e.toModel ξ K → Mono e.toModel ξ φ) ∧
    ∀ (ξ : LVar → Loc), Mono e.toModel ξ K → ∀ i, i ≤ e.toModel.len →
      ((∃ j, QProg.interp e.trc.toList e.obs Δ ⬝ e.trc.toList ⬝ e.obs ⬝ ξ ∘ ρ ⊨ F : i ⇝ j ∧
             e.toModel ⬝ ξ ⬝ j ⊨ K) ↔ e.toModel ⬝ ξ ⬝ i ⊨ φ)

/-- The same, for `QBody.Tr`/`QBody.Sat`. -/
def QBodyCorrect (N : Nat) : Prop :=
  ∀ (e : Exec) (Δ : QProg) (ρ : Ren), Δ.length ≤ N → QProg.WF Δ →
  ∀ (P : QBody) (n : Nat) (K φ : Ltl LVar) (n' : Nat),
    ρ.Fresh n → K.Indep n → QBody.Tr ρ Δ P K n φ n' →
    n ≤ n' ∧ φ.Indep n' ∧
    (∀ ξ, Mono e.toModel ξ K → Mono e.toModel ξ φ) ∧
    ∀ (ξ : LVar → Loc), Mono e.toModel ξ K → ∀ i, i ≤ e.toModel.len →
      ((∃ j, QProg.interp e.trc.toList e.obs Δ ⬝ e.trc.toList ⬝ e.obs ⬝ ξ ∘ ρ ⊨ P : i ⇝ j ∧
             e.toModel ⬝ ξ ⬝ j ⊨ K) ↔ e.toModel ⬝ ξ ⬝ i ⊨ φ)

theorem correct_all : ∀ N, PatCorrect N ∧ QBodyCorrect N := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    have ihQBody : ∀ M, M < N → QBodyCorrect M := fun M hM => (ih M hM).2
    have hP : PatCorrect N := by
      intro e Δ ρ hΔlen hΔwf F
      have hΘ : (QProg.interp e.trc.toList e.obs Δ).Ok e.trc.toList := QProg.interp_ok Δ _ _
      have hlen : e.toModel.len = e.trc.toList.length := Exec.toModel_len e
      induction F with
      | eps =>
        intro n K φ n' hfresh hKI hTr
        cases hTr
        refine ⟨Nat.le_refl _, hKI, fun ξ hK => hK, fun ξ hK i hi => ?_⟩
        simp only [Pat.sat_eps]
        constructor
        · rintro ⟨j, rfl, hj⟩; exact hj
        · intro h; exact ⟨i, rfl, h⟩
      | act a =>
        intro n K φ n' hfresh hKI hTr
        cases hTr
        refine ⟨Nat.le_refl _,
          Ltl.Indep.until (Ltl.Indep.tt n) ((Ltl.Indep.qact hfresh a).and hKI.next),
          fun ξ _ => Mono.F e.toModel ξ _, fun ξ hK i hi => ?_⟩
        simp only [Pat.sat_act, Ltl.sat_F, Ltl.Sat, QAct.sat_toAtom, Exec.holds_toModel]
        constructor
        · rintro ⟨j, ⟨h1, h2, h3⟩, hKj⟩
          refine ⟨j - 1, by omega, by omega, h3, by omega, ?_⟩
          have : j - 1 + 1 = j := by omega
          rw [this]; exact hKj
        · rintro ⟨k, h1, h2, h3, h4, hKj⟩
          exact ⟨k + 1, ⟨by omega, by omega, by simpa using h3⟩, hKj⟩
      | query Q zs =>
        intro n K φ n' hfresh hKI hTr
        cases hTr with
        | query hFind hLen hQBTr =>
          rename_i q Δ'
          have hlt : Δ'.length < Δ.length := QProg.findRest?_length_lt hFind
          have hltN : Δ'.length < N := Nat.lt_of_lt_of_le hlt hΔlen
          have hdw := hΔwf.findRest hFind
          have hdecl : q.Declared := hdw.1.1
          have hΔ'wf : QProg.WF Δ' := hdw.2
          have hfresh' : (Ren.ofParams q.params (zs.map ρ)).Fresh n :=
            Ren.Fresh.ofParams (Ren.Fresh.map hfresh zs)
          obtain ⟨hnn', hφIndep, hφMono, hcorr⟩ :=
            ihQBody Δ'.length hltN e Δ' (Ren.ofParams q.params (zs.map ρ))
              (Nat.le_refl _) hΔ'wf q.body n K φ n' hfresh' hKI hQBTr
          refine ⟨hnn', hφIndep, hφMono, fun ξ hK i hi => ?_⟩
          rw [← hcorr ξ hK i hi]
          have hzslen : q.params.length = (zs.map ρ).length := by simp [hLen]
          have hmapeq : zs.map (ξ ∘ ρ) = (zs.map ρ).map ξ := by
            simp [List.map_map, Function.comp_def]
          constructor
          · rintro ⟨j, hsq, hKj⟩
            rw [Pat.sat_query,
              QProg.interp_findRest e.trc.toList e.obs Q (zs.map (ξ ∘ ρ)) i j hFind] at hsq
            obtain ⟨_, hPs⟩ := hsq
            refine ⟨j, ?_, hKj⟩
            refine (QBody.sat_coincide (ξ₁ := LEnv.empty.bind q.params (zs.map (ξ ∘ ρ)))
              (ξ₂ := ξ ∘ Ren.ofParams q.params (zs.map ρ)) ?_).1 hPs
            intro x hx hxl
            rcases hdecl.2 x hx with hxp | hxl'
            · rw [Function.comp_apply, hmapeq, ← Ren.sat_ofParams ξ q.params (zs.map ρ) hzslen x hxp]
            · exact absurd hxl' hxl
          · rintro ⟨j, hPs, hKj⟩
            refine ⟨j, ?_, hKj⟩
            rw [Pat.sat_query,
              QProg.interp_findRest e.trc.toList e.obs Q (zs.map (ξ ∘ ρ)) i j hFind]
            refine ⟨by simp [hLen], ?_⟩
            refine (QBody.sat_coincide (ξ₁ := ξ ∘ Ren.ofParams q.params (zs.map ρ))
              (ξ₂ := LEnv.empty.bind q.params (zs.map (ξ ∘ ρ))) ?_).1 hPs
            intro x hx hxl
            rcases hdecl.2 x hx with hxp | hxl'
            · rw [Function.comp_apply, hmapeq, ← Ren.sat_ofParams ξ q.params (zs.map ρ) hzslen x hxp]
            · exact absurd hxl' hxl
      | seq F₁ F₂ ih₁ ih₂ =>
        intro n K φ n' hfresh hKI hTr
        cases hTr with
        | seq hTr₂ hTr₁ =>
          rename_i φ₂ n₁
          obtain ⟨hn_n₁, hφ₂I, hφ₂Mono, hcorr₂⟩ := ih₂ n K φ₂ n₁ hfresh hKI hTr₂
          have hfresh₁ : ρ.Fresh n₁ := hfresh.mono hn_n₁
          obtain ⟨hn₁_n', hφI, hφMono, hcorr₁⟩ := ih₁ n₁ φ₂ φ n' hfresh₁ hφ₂I hTr₁
          refine ⟨Nat.le_trans hn_n₁ hn₁_n', hφI, fun ξ hK => hφMono ξ (hφ₂Mono ξ hK),
            fun ξ hK i hi => ?_⟩
          have hMonoφ₂ := hφ₂Mono ξ hK
          rw [← hcorr₁ ξ hMonoφ₂ i hi]
          constructor
          · rintro ⟨j, hseq, hKj⟩
            rw [Pat.sat_seq] at hseq
            obtain ⟨k, hk1, hk2⟩ := hseq
            have hkbound : k ≤ e.toModel.len := by
              have := Pat.Sat.bound hΘ hk1 (by omega : i ≤ e.trc.toList.length)
              omega
            exact ⟨k, hk1, (hcorr₂ ξ hK k hkbound).1 ⟨j, hk2, hKj⟩⟩
          · rintro ⟨k, hk1, hk2⟩
            have hkbound : k ≤ e.toModel.len := by
              have := Pat.Sat.bound hΘ hk1 (by omega : i ≤ e.trc.toList.length)
              omega
            obtain ⟨j, hj1, hj2⟩ := (hcorr₂ ξ hK k hkbound).2 hk2
            exact ⟨j, Pat.sat_seq.2 ⟨k, hk1, hj1⟩, hj2⟩
      | alt F₁ F₂ ih₁ ih₂ =>
        intro n K φ n' hfresh hKI hTr
        cases hTr with
        | @alt _ _ _ _ _ _ φ₁ n₁ φ₂ _ hTr₁ hTr₂ =>
          obtain ⟨hn_n₁, hφ₁I, hφ₁Mono, hcorr₁⟩ := ih₁ n K φ₁ n₁ hfresh hKI hTr₁
          obtain ⟨hn₁_n', hφ₂I, hφ₂Mono, hcorr₂⟩ :=
            ih₂ n₁ K φ₂ n' (hfresh.mono hn_n₁) (hKI.mono hn_n₁) hTr₂
          refine ⟨Nat.le_trans hn_n₁ hn₁_n', (hφ₁I.mono hn₁_n').or hφ₂I,
            fun ξ hK => (hφ₁Mono ξ hK).or (hφ₂Mono ξ hK), fun ξ hK i hi => ?_⟩
          simp only [Ltl.Sat, Pat.sat_alt, ← hcorr₁ ξ hK i hi, ← hcorr₂ ξ hK i hi]
          constructor
          · rintro ⟨j, hj | hj, hK'⟩
            · exact Or.inl ⟨j, hj, hK'⟩
            · exact Or.inr ⟨j, hj, hK'⟩
          · rintro (⟨j, hj, hK'⟩ | ⟨j, hj, hK'⟩)
            · exact ⟨j, Or.inl hj, hK'⟩
            · exact ⟨j, Or.inr hj, hK'⟩
      | both F₁ F₂ ih₁ ih₂ =>
        intro n K φ n' hfresh hKI hTr
        cases hTr with
        | @both _ _ _ _ _ _ φ₁ n₁ φ₂ _ hTr₁ hTr₂ =>
          obtain ⟨hn_n₁, hφ₁I, hφ₁Mono, hcorr₁⟩ := ih₁ n K φ₁ n₁ hfresh hKI hTr₁
          obtain ⟨hn₁_n', hφ₂I, hφ₂Mono, hcorr₂⟩ :=
            ih₂ n₁ K φ₂ n' (hfresh.mono hn_n₁) (hKI.mono hn_n₁) hTr₂
          refine ⟨Nat.le_trans hn_n₁ hn₁_n', (hφ₁I.mono hn₁_n').and hφ₂I,
            fun ξ hK => (hφ₁Mono ξ hK).and (hφ₂Mono ξ hK), fun ξ hK i hi => ?_⟩
          simp only [Ltl.Sat, Pat.sat_both, ← hcorr₁ ξ hK i hi, ← hcorr₂ ξ hK i hi]
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
    have hB : QBodyCorrect N := by
      intro e Δ ρ hΔlen hΔwf P n K φ n' hfresh hKI hTr
      cases hTr with
      | @noExcept _ _ _ _ _ φ_pat _ ρ' hex hρ' hPatTr =>
        have hfresh' : ρ'.Fresh (n + P.locals.length) := hρ' ▸ hfresh.extendFresh P.locals
        have hKI' : K.Indep (n + P.locals.length) := hKI.mono (Nat.le_add_right _ _)
        obtain ⟨hn_n', hφpI, hφpMono, hcorrPat⟩ :=
          hP e Δ ρ' hΔlen hΔwf P.pattern (n + P.locals.length) K φ_pat n' hfresh' hKI' hPatTr
        have hnn' : n ≤ n' := Nat.le_trans (Nat.le_add_right _ _) hn_n'
        refine ⟨hnn',
          Ltl.Indep.exN (fun v hv m hm => Nat.lt_of_lt_of_le (freshVars_lt P.locals n v hv m hm) hn_n')
            ((Ltl.Indep.inv hfresh' P.when).mono hn_n' |>.and hφpI),
          fun ξ hK => ?_, fun ξ hK i hi => ?_⟩
        · intro p q hqp hp h
          rw [Ltl.sat_exN_fresh] at h ⊢
          obtain ⟨ls, hlen, hψ⟩ := h
          refine ⟨ls, hlen, ?_⟩
          have hKls : Mono e.toModel (updateFresh ξ n ls) K := (hKI.mono_iff (Nat.le_refl n) ls).1 hK
          exact (Mono.inv ρ' P.when e.toModel (updateFresh ξ n ls) |>.and
            (hφpMono (updateFresh ξ n ls) hKls)) p q hqp hp hψ
        · rw [Ltl.sat_exN_fresh]
          constructor
          · rintro ⟨j, hPs, hKj⟩
            cases hPs with
            | @mk _ ξ'' ls' _ _ hlen' hξ'' hpat hwhen _ =>
              have hcomp : updateFresh ξ n ls' ∘ ρ' = LEnv.bind (ξ ∘ ρ) P.locals ls' := by
                rw [hρ']; exact funext (Ren.sat_updateFresh_extendFresh P.locals hfresh hlen' ξ)
              have hKls' : Mono e.toModel (updateFresh ξ n ls') K :=
                (hKI.mono_iff (Nat.le_refl n) ls').1 hK
              have hKj' : e.toModel ⬝ updateFresh ξ n ls' ⬝ j ⊨ K :=
                (hKI e.toModel ξ n ls' (Nat.le_refl n) j).1 hKj
              refine ⟨ls', hlen', ?_⟩
              simp only [Ltl.Sat]
              refine ⟨?_, (hcorrPat (updateFresh ξ n ls') hKls' i hi).1 ⟨j, ?_, hKj'⟩⟩
              · rw [Inv.sat_tr, hcomp]; rw [hξ''] at hwhen; exact hwhen
              · rw [hcomp]; rw [hξ''] at hpat; exact hpat
          · rintro ⟨ls, hlen, hψ⟩
            simp only [Ltl.Sat] at hψ
            obtain ⟨hwhen, hpat⟩ := hψ
            have hcomp : updateFresh ξ n ls ∘ ρ' = LEnv.bind (ξ ∘ ρ) P.locals ls := by
              rw [hρ']; exact funext (Ren.sat_updateFresh_extendFresh P.locals hfresh hlen ξ)
            have hKls' : Mono e.toModel (updateFresh ξ n ls) K :=
              (hKI.mono_iff (Nat.le_refl n) ls).1 hK
            obtain ⟨j, hpat', hKj'⟩ := (hcorrPat (updateFresh ξ n ls) hKls' i hi).2 hpat
            refine ⟨j, QBody.Sat.mk hlen rfl ?_ ?_ (by simp [hex]),
              (hKI e.toModel ξ n ls (Nat.le_refl n) j).2 hKj'⟩
            · rw [hcomp] at hpat'; exact hpat'
            · rw [Inv.sat_tr] at hwhen; rw [hcomp] at hwhen; exact hwhen
      | @withExcept _ _ _ F' _ _ φ_pat n₁ φ_ex _ ρ' hex hρ' hPatTr hExTr =>
        have hfresh' : ρ'.Fresh (n + P.locals.length) := hρ' ▸ hfresh.extendFresh P.locals
        have hKI' : K.Indep (n + P.locals.length) := hKI.mono (Nat.le_add_right _ _)
        obtain ⟨hn_n₁, hφpI, hφpMono, hcorrPat⟩ :=
          hP e Δ ρ' hΔlen hΔwf P.pattern (n + P.locals.length) K φ_pat n₁ hfresh' hKI' hPatTr
        have hfresh₁ : ρ'.Fresh n₁ := hfresh'.mono hn_n₁
        obtain ⟨hn₁_n', hφexI, hφexMono, hcorrEx⟩ :=
          hP e Δ ρ' hΔlen hΔwf F' n₁ Ltl.tt φ_ex n' hfresh₁ (Ltl.Indep.tt n₁) hExTr
        have hnn₁ : n ≤ n₁ := Nat.le_trans (Nat.le_add_right _ _) hn_n₁
        have hnn' : n ≤ n' := Nat.le_trans hnn₁ hn₁_n'
        have hnpat_n' : n + P.locals.length ≤ n' := Nat.le_trans hn_n₁ hn₁_n'
        have hExIff : ∀ ξ' : LVar → Loc,
            (∃ j, QProg.interp e.trc.toList e.obs Δ ⬝ e.trc.toList ⬝ e.obs ⬝ ξ' ∘ ρ' ⊨ F' : 0 ⇝ j) ↔
              e.toModel ⬝ ξ' ⬝ 0 ⊨ φ_ex := by
          intro ξ'
          simpa [Ltl.Sat] using hcorrEx ξ' (Mono.tt _ _) 0 (Nat.zero_le _)
        refine ⟨hnn',
          Ltl.Indep.exN
            (fun v hv m hm => Nat.lt_of_lt_of_le (freshVars_lt P.locals n v hv m hm) hnpat_n')
            (((Ltl.Indep.inv hfresh' P.when).mono hnpat_n').and
              ((Ltl.Indep.atStart hφexI.not).and (hφpI.mono hn₁_n'))),
          fun ξ hK => ?_, fun ξ hK i hi => ?_⟩
        · intro p q hqp hp h
          rw [Ltl.sat_exN_fresh] at h ⊢
          obtain ⟨ls, hlen, hψ⟩ := h
          refine ⟨ls, hlen, ?_⟩
          have hKls : Mono e.toModel (updateFresh ξ n ls) K :=
            (hKI.mono_iff (Nat.le_refl n) ls).1 hK
          exact ((Mono.inv ρ' P.when e.toModel (updateFresh ξ n ls)).and
            ((Mono.atStart e.toModel (updateFresh ξ n ls) _).and
              (hφpMono (updateFresh ξ n ls) hKls))) p q hqp hp hψ
        · rw [Ltl.sat_exN_fresh]
          constructor
          · rintro ⟨j, hPs, hKj⟩
            cases hPs with
            | @mk _ ξ'' ls' _ _ hlen' hξ'' hpat hwhen hexcept =>
              have hcomp : updateFresh ξ n ls' ∘ ρ' = LEnv.bind (ξ ∘ ρ) P.locals ls' := by
                rw [hρ']; exact funext (Ren.sat_updateFresh_extendFresh P.locals hfresh hlen' ξ)
              have hKls' : Mono e.toModel (updateFresh ξ n ls') K :=
                (hKI.mono_iff (Nat.le_refl n) ls').1 hK
              have hKj' : e.toModel ⬝ updateFresh ξ n ls' ⬝ j ⊨ K :=
                (hKI e.toModel ξ n ls' (Nat.le_refl n) j).1 hKj
              refine ⟨ls', hlen', ?_⟩
              simp only [Ltl.Sat]
              refine ⟨?_, ?_, (hcorrPat (updateFresh ξ n ls') hKls' i hi).1 ⟨j, ?_, hKj'⟩⟩
              · rw [Inv.sat_tr, hcomp]; rw [hξ''] at hwhen; exact hwhen
              · rw [Ltl.sat_atStart, Ltl.Sat, ← hExIff (updateFresh ξ n ls'), hcomp]
                exact fun ⟨k, hk⟩ => hexcept F' hex k
                  (hk.bound (QProg.interp_ok _ _ _) (Nat.zero_le _)) (hξ'' ▸ hk)
              · rw [hcomp]; rw [hξ''] at hpat; exact hpat
          · rintro ⟨ls, hlen, hψ⟩
            simp only [Ltl.Sat] at hψ
            obtain ⟨hwhen, hnotex, hpat⟩ := hψ
            have hcomp : updateFresh ξ n ls ∘ ρ' = LEnv.bind (ξ ∘ ρ) P.locals ls := by
              rw [hρ']; exact funext (Ren.sat_updateFresh_extendFresh P.locals hfresh hlen ξ)
            have hKls : Mono e.toModel (updateFresh ξ n ls) K :=
              (hKI.mono_iff (Nat.le_refl n) ls).1 hK
            obtain ⟨j, hpat', hKj'⟩ := (hcorrPat (updateFresh ξ n ls) hKls i hi).2 hpat
            refine ⟨j, QBody.Sat.mk hlen rfl ?_ ?_ ?_,
              (hKI e.toModel ξ n ls (Nat.le_refl n) j).2 hKj'⟩
            · rw [hcomp] at hpat'; exact hpat'
            · rw [Inv.sat_tr] at hwhen; rw [hcomp] at hwhen; exact hwhen
            · intro F'' hF'' k _ hk
              have hFeq : F'' = F' := by rw [hex] at hF''; exact (Option.some.inj hF'').symm
              subst hFeq
              rw [Ltl.sat_atStart, Ltl.Sat, ← hExIff (updateFresh ξ n ls), hcomp] at hnotex
              exact hnotex ⟨k, hk⟩
    exact ⟨hP, hB⟩

/-! ## Existence

Every well-formed query program has a `QBody.Tr` witness: the same strong induction as
`correct_all`, but *constructing* a derivation instead of consuming one — mechanically
simpler, since existence needs no `Mono`/`Indep` bookkeeping (`correct_all` supplies those
for free once a witness exists). -/

/-- Every invocation `F` makes is answerable in `Δ`, for every pattern of `≤ N` queries. -/
def PatExists (N : Nat) : Prop :=
  ∀ (Δ : QProg), Δ.length ≤ N → QProg.WF Δ →
  ∀ (F : Pat), Pat.CallsOK Δ F →
  ∀ (ρ : Ren) (K : Ltl LVar) (n : Nat), ∃ φ n', Pat.Tr ρ Δ F K n φ n'

/-- The same, for `QBody.Tr`. -/
def QBodyExists (N : Nat) : Prop :=
  ∀ (Δ : QProg), Δ.length ≤ N → QProg.WF Δ →
  ∀ (P : QBody), QBody.CallsOK Δ P →
  ∀ (ρ : Ren) (K : Ltl LVar) (n : Nat), ∃ φ n', QBody.Tr ρ Δ P K n φ n'

theorem exists_all : ∀ N, PatExists N ∧ QBodyExists N := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    have ihQBody : ∀ M, M < N → QBodyExists M := fun M hM => (ih M hM).2
    have hP : PatExists N := by
      intro Δ hΔlen hΔwf F
      induction F with
      | eps => intro _ ρ K n; exact ⟨K, n, .eps⟩
      | act a => intro _ ρ K n; exact ⟨_, n, .act⟩
      | query Q zs =>
        intro hcalls ρ K n
        obtain ⟨q, Δ', hfind, harity⟩ := hcalls (Q, zs) (by simp [Pat.calls])
        have hlt : Δ'.length < Δ.length := QProg.findRest?_length_lt hfind
        have hltN : Δ'.length < N := Nat.lt_of_lt_of_le hlt hΔlen
        have hdw := hΔwf.findRest hfind
        obtain ⟨φ, n', hTr⟩ :=
          ihQBody Δ'.length hltN Δ' (Nat.le_refl _) hdw.2 q.body
            hdw.1.2.body (Ren.ofParams q.params (zs.map ρ)) K n
        exact ⟨φ, n', .query hfind harity.symm hTr⟩
      | seq F₁ F₂ ih₁ ih₂ =>
        intro hcalls ρ K n
        obtain ⟨h1, h2⟩ := hcalls.seq
        obtain ⟨φ₂, n₁, hTr₂⟩ := ih₂ h2 ρ K n
        obtain ⟨φ, n', hTr₁⟩ := ih₁ h1 ρ φ₂ n₁
        exact ⟨φ, n', .seq hTr₂ hTr₁⟩
      | alt F₁ F₂ ih₁ ih₂ =>
        intro hcalls ρ K n
        obtain ⟨h1, h2⟩ := hcalls.alt
        obtain ⟨φ₁, n₁, hTr₁⟩ := ih₁ h1 ρ K n
        obtain ⟨φ₂, n₂, hTr₂⟩ := ih₂ h2 ρ K n₁
        exact ⟨_, n₂, .alt hTr₁ hTr₂⟩
      | both F₁ F₂ ih₁ ih₂ =>
        intro hcalls ρ K n
        obtain ⟨h1, h2⟩ := hcalls.both
        obtain ⟨φ₁, n₁, hTr₁⟩ := ih₁ h1 ρ K n
        obtain ⟨φ₂, n₂, hTr₂⟩ := ih₂ h2 ρ K n₁
        exact ⟨_, n₂, .both hTr₁ hTr₂⟩
    have hB : QBodyExists N := by
      intro Δ hΔlen hΔwf P hcalls ρ K n
      cases he : P.except with
      | none =>
        obtain ⟨φ_pat, n₁, hTr⟩ :=
          hP Δ hΔlen hΔwf P.pattern hcalls.pattern (ρ.extendFresh P.locals n) K (n + P.locals.length)
        exact ⟨_, n₁, .noExcept he rfl hTr⟩
      | some F' =>
        obtain ⟨φ_pat, n₁, hTr1⟩ :=
          hP Δ hΔlen hΔwf P.pattern hcalls.pattern (ρ.extendFresh P.locals n) K (n + P.locals.length)
        obtain ⟨φ_ex, n₂, hTr2⟩ :=
          hP Δ hΔlen hΔwf F' (hcalls.except he) (ρ.extendFresh P.locals n) Ltl.tt n₁
        exact ⟨_, n₂, .withExcept he rfl hTr1 hTr2⟩
    exact ⟨hP, hB⟩

/-! ## The headline theorem

Putting `correct_all` and `exists_all` together: every well-formed query has a
translation into `Ltl LVar`, and it is semantics-preserving over *any* execution
record — materializing the translation, as asked for at the outset. -/

/-- `Sum.inl` never produces a synthetic tag, so it is (trivially) fresh below any `n`,
    in particular `0`. -/
theorem Ren.Fresh.inl (n : Nat) : Ren.Fresh Sum.inl n := by
  intro x m hx; nomatch hx

/-- The valuation a top-level query's arguments determine: its own parameters get their
    given locations, and (since they occur in `φ` only under their own `∃`, by
    `Ltl.Indep`) the synthetic tags' values are irrelevant. -/
def Query.topEnv (q : Query) (ls : List Loc) : LVar → Loc :=
  Sum.elim (LEnv.empty.bind q.params ls) (fun _ => 0)

theorem Query.topEnv_comp_inl (q : Query) (ls : List Loc) :
    Query.topEnv q ls ∘ (Sum.inl : Var → LVar) = LEnv.empty.bind q.params ls := rfl

/-- **Semantics-preservation.** Given a translation witness for `q`'s body, matching is
    exactly satisfaction of the translated formula, for any execution record and any
    arguments of the right arity. -/
theorem Query.tr_correct {Δ : QProg} {q : Query} (hwf : QProg.WF (q :: Δ))
    {φ : Ltl LVar} {n' : Nat} (hTr : QBody.Tr Sum.inl Δ q.body Ltl.tt 0 φ n')
    (e : Exec) (ls : List Loc) (hlen : ls.length = q.params.length) :
    Exec.Matches (q :: Δ) e q.name ls ↔ φ.Holds e.toModel (q.topEnv ls) := by
  have hΔwf : QProg.WF Δ := hwf.2.2
  obtain ⟨-, -, -, hcorr⟩ :=
    (correct_all Δ.length).2 e Δ Sum.inl (Nat.le_refl _) hΔwf q.body 0 Ltl.tt φ n'
      (Ren.Fresh.inl 0) (Ltl.Indep.tt 0) hTr
  have := (hcorr (q.topEnv ls) (Mono.tt _ _) 0 (Nat.zero_le _))
  simp only [Ltl.Sat, and_true, Query.topEnv_comp_inl] at this
  simp only [Exec.Matches, QProg.interp, Ltl.Holds]
  rw [← this]
  constructor
  · rintro ⟨j, hlen', hPs⟩; exact ⟨j, hPs⟩
  · rintro ⟨j, hPs⟩; exact ⟨j, hlen, hPs⟩

/-- **The general theorem.** For every well-formed query, a semantics-preserving
    translation into `Ltl LVar` exists: it agrees with `Pat.Sat`/`QBody.Sat` for every
    execution record, not just ones produced by the concrete semantics of
    `CoreJsSemantics.lean`.  `Query.tr` computes it (`Query.tr_computed_correct`). -/
theorem Query.exists_tr_correct {Δ : QProg} {q : Query} (hwf : QProg.WF (q :: Δ)) :
    ∃ (φ : Ltl LVar) (n' : Nat), QBody.Tr Sum.inl Δ q.body Ltl.tt 0 φ n' ∧
      ∀ (e : Exec) (ls : List Loc), ls.length = q.params.length →
        (Exec.Matches (q :: Δ) e q.name ls ↔ φ.Holds e.toModel (q.topEnv ls)) := by
  have hΔwf : QProg.WF Δ := hwf.2.2
  obtain ⟨φ, n', hTr⟩ :=
    (exists_all Δ.length).2 Δ (Nat.le_refl _) hΔwf q.body hwf.1.2.body
      Sum.inl Ltl.tt 0
  exact ⟨φ, n', hTr, fun e ls hlen => Query.tr_correct hwf hTr e ls hlen⟩

/-! ### A worked example

`exSink` (`Sink(f,x) { Call(f,[x]) when sk(f) ∧ ac(x) }`) is well formed on its own,
so the headline theorem applies to it directly, over *any* execution record — not just
`exSink.Tr`'s own witness (already exhibited above), but the full statement that
matching and satisfying the translated formula agree. -/

theorem exSink_WF : QProg.WF [exSink] := by
  refine ⟨⟨?_, ?_⟩, ?_, trivial⟩
  · constructor
    · decide
    · intro v hv
      simp [QBody.vars, exSink, Pat.vars, QAct.vars, Inv.vars, Pred.vars] at hv
      rcases hv with h | h | h | h <;> simp [h, exSink]
  · intro c hc
    simp [QBody.calls, exSink, Pat.calls] at hc
  · decide

/-- The call, on a sink, of an attacker-controlled value. -/
def eSinkHit : Exec where
  trc := .act (.call 204 [1100])
  obs := ⟨fun _ => none, fun _ => ∅, fun l => l = 1100, fun l => l = 204⟩

/-- The same call, but neither a sink nor attacker-controlled. -/
def eSinkMiss : Exec where
  trc := .act (.call 205 [1101])
  obs := ⟨fun _ => none, fun _ => ∅, fun _ => False, fun _ => False⟩

/-- The headline theorem, materialized for `exSink`: matching agrees with satisfying
    the translated formula, on both a hit and a miss. -/
example :
    ∃ φ : Ltl LVar, (∀ e ls, ls.length = 2 →
      (Exec.Matches [exSink] e "Sink" ls ↔ φ.Holds e.toModel (exSink.topEnv ls))) ∧
      φ.Holds eSinkHit.toModel (exSink.topEnv [204, 1100]) ∧
      ¬ φ.Holds eSinkMiss.toModel (exSink.topEnv [205, 1101]) := by
  obtain ⟨φ, n', hTr, hcorr⟩ := Query.exists_tr_correct exSink_WF
  refine ⟨φ, hcorr, (hcorr eSinkHit [204, 1100] rfl).1 ⟨1, ?_⟩, ?_⟩
  · exact (QProg.interp_head exSink [] eSinkHit.trc.toList eSinkHit.obs [204, 1100] 0 1).2
      ⟨rfl, .mk (ls := []) rfl rfl (.act (by decide) (by decide) (by decide)) ⟨rfl, rfl⟩
        (fun F' h => nomatch h)⟩
  · rw [← hcorr eSinkMiss [205, 1101] rfl]
    rintro ⟨j, hlen, hPs⟩
    cases hPs with
    | mk _ hξ' _ hwhen _ =>
      simp only [hξ', exSink, Inv.Sat, Pred.Sat, eSinkMiss, LEnv.bind, LEnv.empty] at hwhen
      exact hwhen.1

/-! ## Computing the translation

`Pat.Tr`/`QBody.Tr` are the specification; `Pat.tr`/`QBody.tr` compute it.
Recursion is well founded on `(Δ.length, sizeOf F)`: an invocation continues
with the strictly shorter rest of the program (`QProg.findRest?_length_lt`),
every other case with a sub-term.  The result is `none` exactly when an
invocation names no query of `Δ` or passes the wrong number of arguments,
which `QProg.WF` rules out.

The function and the relation agree: whatever `Pat.tr` returns is a
derivation (`Pat.tr_sound`), and every derivation is what `Pat.tr` returns
(`Pat.Tr.tr_eq`, so the relation is functional).  With `exists_all`, the
latter makes `Pat.tr` total on well-formed programs, and
`Query.tr_computed_correct` restates the headline theorem for the computed
formula. -/

mutual

/-- Compute `tr(F, K)` with renaming `ρ` and fresh tags from `n`: the formula and
    the next unused tag. -/
def Pat.tr (ρ : Ren) (Δ : QProg) : Pat → Ltl LVar → Nat → Option (Ltl LVar × Nat)
  | .eps, K, n => some (K, n)
  | .act a, K, n => some (Ltl.F (.and (.atom (a.toAtom ρ)) (.next K)), n)
  | .query Q zs, K, n =>
      match _hfind : QProg.findRest? Q Δ with
      | some (q, Δ') =>
          if zs.length = q.params.length then
            QBody.tr (Ren.ofParams q.params (zs.map ρ)) Δ' q.body K n
          else none
      | none => none
  | .seq F₁ F₂, K, n =>
      match Pat.tr ρ Δ F₂ K n with
      | some (φ₂, n₁) => Pat.tr ρ Δ F₁ φ₂ n₁
      | none => none
  | .alt F₁ F₂, K, n =>
      match Pat.tr ρ Δ F₁ K n with
      | some (φ₁, n₁) =>
          match Pat.tr ρ Δ F₂ K n₁ with
          | some (φ₂, n₂) => some (.or φ₁ φ₂, n₂)
          | none => none
      | none => none
  | .both F₁ F₂, K, n =>
      match Pat.tr ρ Δ F₁ K n with
      | some (φ₁, n₁) =>
          match Pat.tr ρ Δ F₂ K n₁ with
          | some (φ₂, n₂) => some (.and φ₁ φ₂, n₂)
          | none => none
      | none => none
termination_by F => (Δ.length, sizeOf F)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ (QProg.findRest?_length_lt _hfind)
    | (apply Prod.Lex.right; simp_wf; omega)

/-- Compute the translation of a query body `∃ ys: F when I except F'`. -/
def QBody.tr (ρ : Ren) (Δ : QProg) : QBody → Ltl LVar → Nat → Option (Ltl LVar × Nat)
  | ⟨locals, pattern, when, except⟩, K, n =>
      match except with
      | none =>
          match Pat.tr (ρ.extendFresh locals n) Δ pattern K (n + locals.length) with
          | some (φ_pat, n₁) =>
              some (Ltl.exN (freshVars locals n)
                (.and (Inv.tr (ρ.extendFresh locals n) when) φ_pat), n₁)
          | none => none
      | some F' =>
          match Pat.tr (ρ.extendFresh locals n) Δ pattern K (n + locals.length) with
          | some (φ_pat, n₁) =>
              match Pat.tr (ρ.extendFresh locals n) Δ F' .tt n₁ with
              | some (φ_ex, n₂) =>
                  some (Ltl.exN (freshVars locals n)
                    (.and (Inv.tr (ρ.extendFresh locals n) when)
                      (.and (Ltl.atStart (.not φ_ex)) φ_pat)), n₂)
              | none => none
          | none => none
termination_by P => (Δ.length, sizeOf P)
decreasing_by all_goals (apply Prod.Lex.right; simp_wf; omega)

end

/-- Compute the translation of a top-level query, as `Query.Tr` specifies it. -/
def Query.tr (Δ : QProg) (q : Query) : Option (Ltl LVar) :=
  (QBody.tr Sum.inl Δ q.body .tt 0).map Prod.fst

/-- A formula variable as text: a source name as itself, a fresh tag `k` as `#k`. -/
def LVar.toStr : LVar → String
  | .inl x => x
  | .inr k => s!"#{k}"

/-- The translation of a top-level query as text (for `#eval`). -/
def Query.trStr (Δ : QProg) (q : Query) : String :=
  match Query.tr Δ q with
  | some φ => φ.toStr LVar.toStr
  | none   => "(no translation: an invocation is unresolved or has the wrong arity)"

/-- Every derivation is what `Pat.tr`/`QBody.tr` compute, for programs of length `≤ N`;
    in particular `Pat.Tr`/`QBody.Tr` are functional. -/
theorem tr_complete_all : ∀ N,
    (∀ (Δ : QProg), Δ.length ≤ N → ∀ (ρ : Ren) (F : Pat) (K : Ltl LVar) (n : Nat) φ n',
      Pat.Tr ρ Δ F K n φ n' → Pat.tr ρ Δ F K n = some (φ, n')) ∧
    (∀ (Δ : QProg), Δ.length ≤ N → ∀ (ρ : Ren) (P : QBody) (K : Ltl LVar) (n : Nat) φ n',
      QBody.Tr ρ Δ P K n φ n' → QBody.tr ρ Δ P K n = some (φ, n')) := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    have hP : ∀ (Δ : QProg), Δ.length ≤ N → ∀ (ρ : Ren) (F : Pat) (K : Ltl LVar) (n : Nat) φ n',
        Pat.Tr ρ Δ F K n φ n' → Pat.tr ρ Δ F K n = some (φ, n') := by
      intro Δ hΔlen ρ F
      induction F with
      | eps => intro K n φ n' hTr; cases hTr; rw [Pat.tr]
      | act a => intro K n φ n' hTr; cases hTr; rw [Pat.tr]
      | query Q zs =>
        intro K n φ n' hTr
        cases hTr with
        | query hfind hlen hQBTr =>
          rename_i q Δ'
          have hlt : Δ'.length < N :=
            Nat.lt_of_lt_of_le (QProg.findRest?_length_lt hfind) hΔlen
          rw [Pat.tr]
          split
          · rename_i q' Δ'' h
            rw [hfind] at h
            injection h with h
            injection h with h1 h2
            subst h1; subst h2
            rw [if_pos hlen]
            exact (ih Δ'.length hlt).2 Δ' (Nat.le_refl _) _ _ _ _ _ _ hQBTr
          · rename_i h
            rw [hfind] at h
            nomatch h
      | seq F₁ F₂ ih₁ ih₂ =>
        intro K n φ n' hTr
        cases hTr with
        | seq hTr₂ hTr₁ =>
          rw [Pat.tr, ih₂ _ _ _ _ hTr₂]
          exact ih₁ _ _ _ _ hTr₁
      | alt F₁ F₂ ih₁ ih₂ =>
        intro K n φ n' hTr
        cases hTr with
        | alt hTr₁ hTr₂ =>
          rw [Pat.tr, ih₁ _ _ _ _ hTr₁]
          simp only
          rw [ih₂ _ _ _ _ hTr₂]
      | both F₁ F₂ ih₁ ih₂ =>
        intro K n φ n' hTr
        cases hTr with
        | both hTr₁ hTr₂ =>
          rw [Pat.tr, ih₁ _ _ _ _ hTr₁]
          simp only
          rw [ih₂ _ _ _ _ hTr₂]
    refine ⟨hP, ?_⟩
    intro Δ hΔlen ρ P K n φ n' hTr
    obtain ⟨locals, pattern, when, except⟩ := P
    cases hTr with
    | noExcept hex hρ' hpat =>
      simp only at hex
      subst hex; subst hρ'
      rw [QBody.tr.eq_def]
      simp only
      rw [hP Δ hΔlen _ _ _ _ _ _ hpat]
    | withExcept hex hρ' hpat hex' =>
      simp only at hex
      subst hex; subst hρ'
      rw [QBody.tr.eq_def]
      simp only
      rw [hP Δ hΔlen _ _ _ _ _ _ hpat]
      simp only
      rw [hP Δ hΔlen _ _ _ _ _ _ hex']

theorem Pat.Tr.tr_eq {ρ : Ren} {Δ : QProg} {F : Pat} {K : Ltl LVar} {n : Nat} {φ : Ltl LVar}
    {n' : Nat} (h : Pat.Tr ρ Δ F K n φ n') : Pat.tr ρ Δ F K n = some (φ, n') :=
  (tr_complete_all Δ.length).1 Δ (Nat.le_refl _) ρ F K n φ n' h

theorem QBody.Tr.tr_eq {ρ : Ren} {Δ : QProg} {P : QBody} {K : Ltl LVar} {n : Nat} {φ : Ltl LVar}
    {n' : Nat} (h : QBody.Tr ρ Δ P K n φ n') : QBody.tr ρ Δ P K n = some (φ, n') :=
  (tr_complete_all Δ.length).2 Δ (Nat.le_refl _) ρ P K n φ n' h

/-- Whatever `Pat.tr`/`QBody.tr` return is a derivation, for programs of length `≤ N`
    (the same strong induction on program length as `correct_all`). -/
theorem tr_sound_all : ∀ N,
    (∀ (Δ : QProg), Δ.length ≤ N → ∀ (ρ : Ren) (F : Pat) (K : Ltl LVar) (n : Nat) φ n',
      Pat.tr ρ Δ F K n = some (φ, n') → Pat.Tr ρ Δ F K n φ n') ∧
    (∀ (Δ : QProg), Δ.length ≤ N → ∀ (ρ : Ren) (P : QBody) (K : Ltl LVar) (n : Nat) φ n',
      QBody.tr ρ Δ P K n = some (φ, n') → QBody.Tr ρ Δ P K n φ n') := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    have hP : ∀ (Δ : QProg), Δ.length ≤ N → ∀ (ρ : Ren) (F : Pat) (K : Ltl LVar) (n : Nat) φ n',
        Pat.tr ρ Δ F K n = some (φ, n') → Pat.Tr ρ Δ F K n φ n' := by
      intro Δ hΔlen ρ F
      induction F with
      | eps =>
        intro K n φ n' h
        rw [Pat.tr] at h
        injection h with h
        injection h with h1 h2
        subst h1; subst h2
        exact .eps
      | act a =>
        intro K n φ n' h
        rw [Pat.tr] at h
        injection h with h
        injection h with h1 h2
        subst h1; subst h2
        exact .act
      | query Q zs =>
        intro K n φ n' h
        rw [Pat.tr] at h
        split at h
        · rename_i q Δ' hfind
          split at h
          · rename_i hlen
            have hlt : Δ'.length < N :=
              Nat.lt_of_lt_of_le (QProg.findRest?_length_lt hfind) hΔlen
            exact .query hfind hlen ((ih Δ'.length hlt).2 Δ' (Nat.le_refl _) _ _ _ _ _ _ h)
          · nomatch h
        · nomatch h
      | seq F₁ F₂ ih₁ ih₂ =>
        intro K n φ n' h
        rw [Pat.tr] at h
        split at h
        · rename_i φ₂ n₁ h₂
          exact .seq (ih₂ K n φ₂ n₁ h₂) (ih₁ φ₂ n₁ φ n' h)
        · nomatch h
      | alt F₁ F₂ ih₁ ih₂ =>
        intro K n φ n' h
        rw [Pat.tr] at h
        split at h
        · rename_i φ₁ n₁ h₁
          split at h
          · rename_i φ₂ n₂ h₂
            injection h with h
            injection h with h1 h2
            subst h1; subst h2
            exact .alt (ih₁ K n φ₁ n₁ h₁) (ih₂ K n₁ φ₂ n₂ h₂)
          · nomatch h
        · nomatch h
      | both F₁ F₂ ih₁ ih₂ =>
        intro K n φ n' h
        rw [Pat.tr] at h
        split at h
        · rename_i φ₁ n₁ h₁
          split at h
          · rename_i φ₂ n₂ h₂
            injection h with h
            injection h with h1 h2
            subst h1; subst h2
            exact .both (ih₁ K n φ₁ n₁ h₁) (ih₂ K n₁ φ₂ n₂ h₂)
          · nomatch h
        · nomatch h
    refine ⟨hP, ?_⟩
    intro Δ hΔlen ρ P K n φ n' h
    obtain ⟨locals, pattern, when, except⟩ := P
    rw [QBody.tr.eq_def] at h
    cases except with
    | none =>
      simp only at h
      split at h
      · rename_i φ_pat n₁ hpat
        injection h with h
        injection h with h1 h2
        subst h1; subst h2
        exact .noExcept rfl rfl (hP Δ hΔlen _ _ _ _ _ _ hpat)
      · nomatch h
    | some F' =>
      simp only at h
      split at h
      · rename_i φ_pat n₁ hpat
        split at h
        · rename_i φ_ex n₂ hex
          injection h with h
          injection h with h1 h2
          subst h1; subst h2
          exact .withExcept rfl rfl (hP Δ hΔlen _ _ _ _ _ _ hpat) (hP Δ hΔlen _ _ _ _ _ _ hex)
        · nomatch h
      · nomatch h

theorem Pat.tr_sound {ρ : Ren} {Δ : QProg} {F : Pat} {K : Ltl LVar} {n : Nat} {φ : Ltl LVar}
    {n' : Nat} (h : Pat.tr ρ Δ F K n = some (φ, n')) : Pat.Tr ρ Δ F K n φ n' :=
  (tr_sound_all Δ.length).1 Δ (Nat.le_refl _) ρ F K n φ n' h

theorem QBody.tr_sound {ρ : Ren} {Δ : QProg} {P : QBody} {K : Ltl LVar} {n : Nat} {φ : Ltl LVar}
    {n' : Nat} (h : QBody.tr ρ Δ P K n = some (φ, n')) : QBody.Tr ρ Δ P K n φ n' :=
  (tr_sound_all Δ.length).2 Δ (Nat.le_refl _) ρ P K n φ n' h

/-- `Query.tr` computes exactly the translations `Query.Tr` specifies. -/
theorem Query.tr_eq_some_iff {Δ : QProg} {q : Query} {φ : Ltl LVar} :
    Query.tr Δ q = some φ ↔ Query.Tr Δ q φ := by
  constructor
  · intro h
    simp only [Query.tr, Option.map_eq_some_iff] at h
    obtain ⟨⟨φ', n'⟩, h, rfl⟩ := h
    exact ⟨n', QBody.tr_sound h⟩
  · rintro ⟨n', hTr⟩
    simp [Query.tr, QBody.Tr.tr_eq hTr]

/-- **The headline theorem, computed.** For a well-formed query, `Query.tr` succeeds,
    and the formula it returns is semantics-preserving over every execution record. -/
theorem Query.tr_computed_correct {Δ : QProg} {q : Query} (hwf : QProg.WF (q :: Δ)) :
    ∃ φ, Query.tr Δ q = some φ ∧
      ∀ (e : Exec) (ls : List Loc), ls.length = q.params.length →
        (Exec.Matches (q :: Δ) e q.name ls ↔ φ.Holds e.toModel (q.topEnv ls)) := by
  obtain ⟨φ, n', hTr, hcorr⟩ := Query.exists_tr_correct hwf
  exact ⟨φ, Query.tr_eq_some_iff.2 ⟨n', hTr⟩, hcorr⟩

/-! ### Computed translations

What `Query.tr` produces for the example queries above and for three more, as
compile-time checks (`#guard`): a change to the translation that alters any of
these formulas fails the build.  The empty `when` shows up as `⊤ ∧ …`, and
`F (a ∧ X ⊤)` is the translation of an action with nothing after it. -/

section computed

-- `Sink(f,x) { Call(f,[x]) when sk(f) ∧ ac(x) }`: no locals, so no `∃`.
#guard Query.trStr [] exSink ==
  "((sk(f) ∧ ac(x)) ∧ F (call(f, [x]) ∧ X ⊤))"

-- `;` nests the second action inside the first one's continuation.
#guard Query.trStr [] exSeq ==
  "(⊤ ∧ F (call(f, [x]) ∧ X F (retn(f, r) ∧ X ⊤)))"

-- `except` becomes `atStart(¬ …)`: checked from boundary `0`, wherever it sits.
#guard Query.trStr [] exExceptHit ==
  "(⊤ ∧ (atStart(¬F (retn(f, r) ∧ X ⊤)) ∧ F (call(f, [x]) ∧ X ⊤)))"

-- Invocation inlines `Sink`'s body with its parameters `f, x` renamed to the
-- caller's `g, y`.
#guard Query.trStr [exSink] exOuter ==
  "(⊤ ∧ ((sk(g) ∧ ac(y)) ∧ F (call(g, [y]) ∧ X F (retn(g, y) ∧ X ⊤))))"

-- Without `Sink` in the program, the invocation is unresolved: no translation.
#guard (Query.tr [] exOuter).isNone

/-- `SanCalled() { ∃s, z: Call(s, [z]) when hv(s, fid san) }`: `san` is called with
    some argument. -/
def exSanCalled : Query where
  name := "SanCalled"
  params := []
  body := { locals := ["s", "z"], pattern := .act (.call "s" ["z"]),
            when := .pred (.hv "s" (.fid "san")) }

/-- `Unsanitized() { ∃g, y: Call(g, [y]) when hv(g, fid f) except SanCalled() }`:
    `f` is called, and `san` is never called with *any* argument. -/
def exUnsanitized : Query where
  name := "Unsanitized"
  params := []
  body := { locals := ["g", "y"], pattern := .act (.call "g" ["y"]),
            when := .pred (.hv "g" (.fid "f")), except := some (.query "SanCalled" []) }

-- `SanCalled`'s locals become the fresh tags `#2`, `#3`, quantified *inside* the
-- `¬`: "no `z` at all", which a local of `Unsanitized` itself could not express.
#guard Query.trStr [exSanCalled] exUnsanitized ==
  "(∃#0. (∃#1. (hv(#0, fid f) ∧ (atStart(¬(∃#2. (∃#3. (hv(#2, fid san) ∧ " ++
    "F (call(#2, [#3]) ∧ X ⊤))))) ∧ F (call(#0, [#1]) ∧ X ⊤)))))"

/-- `Ret(a) { ∃y: Retn(y, a) }`: some function returns `a`. -/
def exRet : Query where
  name := "Ret"
  params := ["a"]
  body := { locals := ["y"], pattern := .act (.retn "y" "a") }

/-- `RetThenCall(x, y) { Ret(x) ; Call(y, [x]) }`: `x` is returned by some function,
    then the caller's `y` is called with it. -/
def exRetThenCall : Query where
  name := "RetThenCall"
  params := ["x", "y"]
  body := { pattern := .seq (.query "Ret" ["x"]) (.act (.call "y" ["x"])) }

-- `Ret`'s local is the fresh tag `#0`, so the continuation's `y` (the caller's
-- parameter) is not captured by it.
#guard Query.trStr [exRet] exRetThenCall ==
  "(⊤ ∧ (∃#0. (⊤ ∧ F (retn(#0, x) ∧ X F (call(y, [x]) ∧ X ⊤)))))"

end computed

/-!
## Proof structure

The pieces the general theorem is built from (`#print axioms` on each of the theorems named below shows
only the standard Lean core axioms `propext`, `Classical.choice`,
`Quot.sound` — `exists_all` needs only `propext`/`Quot.sound`, no choice):

* `LVar`/`Ren` and the capture-avoiding renaming machinery for inlining
  (`Ren.ofParams`, `Ren.extendFresh`, both defined by the *same* first-match
  recursion `LEnv.bind` uses, so the connecting lemmas are direct structural
  inductions rather than index arithmetic).
* `QAct.toAtom`/`Pred.tr`/`Inv.tr`, the leaf translations, and `Inv.sat_tr`/
  `Pred.sat_tr`/`QAct.sat_toAtom` relating them to `Inv.Sat`/`Pred.Sat`/
  `Act.inst` under `ξ ∘ ρ`.
* `Pat.Tr`/`QBody.Tr`, the translation relation itself, covering the *full*
  query language (actions, `;`/`‖`/`&`, `exists`/`when`/`except`, invocation).
* The freshness invariant `Ren.Fresh` and its preservation across
  `Ren.ofParams`/`Ren.extendFresh` (`Ren.Fresh.ofParams`/`.extendFresh`/
  `.map`/`.mono`), and `updateFresh` (simultaneous valuation update at a
  fresh range) with `updateFresh_nil`/`_cons`, `Ltl.sat_exN_fresh`,
  `Ren.Fresh.upd_comp` and `Ren.sat_updateFresh_extendFresh` — together,
  these connect the *translation's* fresh-tag `∃` to the *semantics'*
  `LEnv.bind` for a query body's own locals.
* `QProg.findRest?_length_lt` (the well-founded measure: invoking a query
  strictly shortens the remaining program), `QProg.interp_findRest`
  (unfolding `QProg.interp` at a query found this way), and
  `QProg.WF.findRest` (a query found via `findRest?` in a well-formed
  program is itself well-formed, against the *shorter* remaining program) —
  together these are what the `query`/`QBody.Tr` case needs to relate
  `Pat.Sat`'s `Θ`-call to `QBody.Sat` on the shorter `Δ'`.
* A **coincidence/locality package** (`Pat.sat_coincide`/`Pred.sat_coincide`/
  `Inv.sat_coincide`/`QBody.sat_coincide`): satisfaction depends on a
  valuation only through its values on the pattern's own free variables
  outside a guard's own locals. This is what makes `Ren.ofParams`'s
  "not found" fallback harmless: composed with `Query.Declared q` (a query's
  body only mentions its own parameters and locals, already defined in
  `CoreJsQuerySyntax.lean`), the `x ∉ q.params` case of `Ren.ofParams` never
  actually gets evaluated by `q.body`.
* `Ltl.Indep φ n` (`φ` cannot distinguish a valuation from any
  `updateFresh`-update at range `≥ n`) and its closure lemmas across every
  connective, including `.ex`/`.all` (binding an already-consumed tag
  preserves `Indep`) — needed because the guard case re-derives the body's
  correctness at a transformed valuation `updateFresh ξ n ls` rather than the
  original `ξ`, and without `Indep` there is no way to relate `Mono ξ K` to
  `Mono (updateFresh ξ n ls) K`. `Mono.F`/`Mono.or`/`Mono.and` and
  `Ltl.Indep.mono_iff` package this transfer.
* `correct_all` (`PatCorrect N ∧ QBodyCorrect N`, proved for every `N` by
  `Nat.strongRecOn` on `N`, with `Pat` handled by ordinary structural
  induction inside each step, since `Pat.Tr`/`QBody.Tr` are mutually
  inductive `Prop`s and this Lean version's `induction` tactic does not
  support inducting on a mutual-family hypothesis directly — confirmed
  experimentally): every `Pat.Tr`/`QBody.Tr` witness, for a program of any
  length, is semantics-preserving.
* `exists_all` (`PatExists N ∧ QBodyExists N`, same induction skeleton,
  no `Mono`/`Indep`/freshness bookkeeping needed): a translation witness
  exists for every well-formed pattern/query body over every
  well-formed program.
* The headline theorems, combining both: `Query.tr_correct` (given a
  witness, matching a well-formed top-level query agrees with the witness
  formula evaluated at `Query.topEnv`) and `Query.exists_tr_correct`
  (dropping the "given a witness" hypothesis, by `exists_all`).
* A worked example (`exSink`/`eSinkHit`/`eSinkMiss`) instantiating the
  headline theorem concretely, confirming it holds on both a hit and a miss.
-/

end CoreJS
