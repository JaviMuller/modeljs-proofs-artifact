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
  `;`, `‖` and `&`), together with all of the substantial supporting
  machinery the full (guards/locals/invocation) case needs: the freshness
  invariant and its preservation, the fresh-tag valuation update and its
  connection to the semantics' `LEnv.bind`, and unfolding `QProg.interp` at
  an invoked query. What remains is now a concrete, scoped plan rather than
  an open-ended gap — see `## Remaining work` at the end of the file.

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
    guarded pattern's own `∃y⃗`. -/
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
already uses. `Pat.Tr ρ Δ F K n φ n'`/`Guarded.Tr ρ Δ g K n φ n'` preserve it
(`Pat.Tr.fresh`/`Guarded.Tr.fresh` below): `φ`'s own tags stay confined to
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
    ∀ locals : List Var, (Ltl.exN (freshVars locals n) φ).Sat m ξ i ↔
      ∃ ls : List Loc, ls.length = locals.length ∧ φ.Sat m (updateFresh ξ n ls) i := by
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
    all `Guarded.sat_coincide` ever needs it for). -/
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
current guarded pattern's own fresh tags exist, so its truth must not depend
on what they are eventually set to — otherwise wrapping it under a further
`∃y⃗` (as `Guarded.Tr` does) could silently change its meaning. `Ltl.Indep φ n`
captures this: `φ` cannot tell `ξ` apart from any `updateFresh ξ m ls` with
`m ≥ n`. It grows monotonically as more fresh tags are consumed
(`Ltl.Indep.mono`), and — critically for `Ltl.ex`/`Ltl.all` — binding one of
`φ`'s *own* (already-below-`n`) tags preserves `Indep n` at the *same* `n`,
not a smaller one: the update ranges this predicate ever has to withstand
never reach back down to an already-bound tag. -/

/-- `φ` cannot distinguish `ξ` from `updateFresh ξ m ls` for any `m ≥ n`. -/
def Ltl.Indep (φ : Ltl LVar) (n : Nat) : Prop :=
  ∀ (m : Model) (ξ : LVar → Loc) (k : Nat) (ls : List Loc), n ≤ k →
    ∀ i, φ.Sat m ξ i ↔ φ.Sat m (updateFresh ξ k ls) i

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
    (a.toAtom ρ).Sat m ξ i ↔ m.holds i (a.inst (ξ ∘ ρ)) := by
  cases a <;> simp [QAct.toAtom, QAct.inst, Atom.Sat, Function.comp_def]

/-- A taint/value predicate as an FO-LTL atom, under a renaming. -/
def Pred.tr (ρ : Ren) : Pred → Atom LVar
  | .sk x      => .sk (ρ x)
  | .ac x      => .ac (ρ x)
  | .dep x₁ x₂ => .dep (ρ x₁) (ρ x₂)
  | .sv x₁ x₂  => .sv (ρ x₁) (ρ x₂)
  | .hv x c    => .hv (ρ x) c

theorem Pred.sat_tr (m : Model) (ρ : Ren) (ξ : LVar → Loc) (i : Nat) (p : Pred) :
    (Pred.tr ρ p).Sat m ξ i ↔ p.Sat m.obs (ξ ∘ ρ) := by
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
    ∀ I : Inv, (Inv.tr ρ I).Sat m ξ i ↔ I.Sat m.obs (ξ ∘ ρ)
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
theorem QProg.interp_findRest (t : List Act) (σ : Obs) (Q : QName) (ls : List Loc) (i j : Nat) :
    ∀ {Δ : QProg} {q : Query} {Δ' : QProg}, QProg.findRest? Q Δ = some (q, Δ') →
      (QProg.interp t σ Δ Q ls i j ↔
        ls.length = q.params.length ∧
        Guarded.Sat (QProg.interp t σ Δ') t σ (LEnv.empty.bind q.params ls) q.body i j)
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
        exact QProg.interp_findRest t σ Q ls i j h

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

* `LVar`/`Ren` and the capture-avoiding renaming machinery for inlining
  (`Ren.ofParams`, `Ren.extendFresh`, both defined by the *same* first-match
  recursion `LEnv.bind` uses, so the connecting lemmas below are direct
  structural inductions rather than index arithmetic).
* `QAct.toAtom`/`Pred.tr`/`Inv.tr`, the leaf translations, and `Inv.sat_tr`/
  `Pred.sat_tr`/`QAct.sat_toAtom` relating them to `Inv.Sat`/`Pred.Sat`/
  `Act.inst` under `ξ ∘ ρ`.
* `Pat.Tr`/`Guarded.Tr`, the translation relation itself, covering the *full*
  query language (actions, `;`/`‖`/`&`, `exists`/`when`/`except`, invocation).
* Concrete existence witnesses (`Query.Tr` is inhabited) for representative
  queries, including `except` and invocation with parameter renaming.
* `Pat.tr_correct`/`Pat.tr_mono`, full correctness for the invocation-free
  fragment (`ε`/`a`/`;`/`‖`/`&`).
* The freshness invariant `Ren.Fresh` and its preservation across
  `Ren.ofParams`/`Ren.extendFresh` (`Ren.Fresh.ofParams`/`.extendFresh`/
  `.map`/`.mono`).
* `updateFresh` (simultaneous valuation update at a fresh range) with
  `updateFresh_nil`/`_cons`, `Ltl.sat_exN_fresh` (unfolding the guard's `∃y⃗`
  into an existential over a list of locations), `Ren.Fresh.upd_comp` and
  `Ren.sat_updateFresh_extendFresh` — together, these connect the
  *translation's* fresh-tag `∃` to the *semantics'* `LEnv.bind` for a guarded
  pattern's own locals.
* `QProg.findRest?_length_lt` (the well-founded measure: invoking a query
  strictly shortens the remaining program) and `QProg.interp_findRest`
  (unfolding `QProg.interp` at a query found this way) — together these are
  what a `.query`/`Guarded.Tr` case needs to relate `Pat.Sat`'s `Θ`-call to
  `Guarded.Sat` on the shorter `Δ'`.

**What is left, precisely** (this is now a concrete plan, not a placeholder):

The combined correctness statement is two mutually-referring facts (`Pat.Tr`/
`Guarded.Tr` are mutually inductive `Prop`s, and this Lean version's
`induction` tactic does not support inducting on a mutual-family hypothesis
directly — confirmed experimentally — so the two must be proved together by
*explicit* strong induction on `Δ.length`, not Lean's auto-generated mutual
recursor):

```
PatCorrect N     := ∀ e Δ ρ, Δ.length ≤ N → ∀ F n K φ n', ρ.Fresh n → Pat.Tr ρ Δ F K n φ n' →
                       n ≤ n' ∧ ∀ ξ, Mono … K → ∀ i, i ≤ len → (∃j, Pat.Sat (QProg.interp … Δ) … F i j ∧ K.Sat … j) ↔ φ.Sat … i
GuardedCorrect N := (the same, for Guarded.Tr/Guarded.Sat)
```

proved as `∀ N, PatCorrect N ∧ GuardedCorrect N` by `Nat.strong_induction_on`
on `N`: within one step (`ih : ∀ M < N, …`), first prove `PatCorrect N` by
ordinary structural induction on `F` (`Pat` alone is *not* mutual, so this
part *is* directly inductable) — `eps`/`act` as in `Pat.tr_correct`; `seq`/
`alt`/`both` are a mechanical port of `Pat.tr_correct`'s own cases, now
carrying the `n`/`Fresh` bookkeeping; `query` uses `QProg.findRest?_length_lt`
to get `Δ'.length < N` and calls `ih`'s `GuardedCorrect` at that smaller
level. Then prove `GuardedCorrect N` using the just-proved `PatCorrect N`
(same `Δ`, so *not* from `ih` — `Guarded.Tr`'s premises translate `g.body`
over the *same* `Δ`) for both its constructors.

**The one genuinely new obstacle found while planning this** (worth flagging
explicitly, since it changes the theorem's hypotheses): relating
`Ren.ofParams q.params (zs.map ρ)` (the fresh base renaming for an invoked
query's scope, composed with `ξ`) to the semantics' `LEnv.empty.bind
q.params ls` is only true for variables `x ∈ q.params` — `Ren.ofParams`'s
"not found" fallback and `LEnv.empty`'s fallback (`0`, a fixed `Loc`) have no
reason to agree under an arbitrary `ξ`, unlike `Ren.extendFresh`'s fallback
(which recurses to the *caller's* `ρ`, matching `LEnv.bind`'s own fallback
`ξ ∘ ρ` exactly — that symmetry is why `Ren.sat_updateFresh_extendFresh`
above holds unconditionally). Closing this needs two more pieces, neither
started:

1. A **coincidence/locality lemma**: `Pat.Sat`/`Ltl.Sat`/`Inv.Sat` depend on a
   valuation only through its values on the term's own free variables (an
   ordinary induction on `Pat`/`Ltl`/`Inv`, independent of everything above).
2. Threading `Query.Declared q` (already defined in
   `CoreJsQuerySyntax.lean`: a query's body only mentions its own parameters
   and locals) at the `query` case, so (1) applies and the `x ∉ q.params`
   case of `Ren.ofParams` never actually gets evaluated by `q.body`.

Once these two land, `PatCorrect`/`GuardedCorrect` need a `Query.WF Δ`-style
hypothesis (for the query actually found via `findRest?`, not the whole `Δ`),
and the headline theorem is

```
Query.WF Δ q → Guarded.Tr Sum.inl Δ q.body ⊤ 0 φ n' →
  ∀ e l⃗, l⃗.length = q.params.length →
    Exec.Matches (q :: Δ) e q.name l⃗ ↔ φ.Holds e.toModel (Sum.elim (LEnv.empty.bind q.params l⃗) (fun _ => 0))
```

(the valuation at `Sum.inr` tags is irrelevant — they occur in `φ` only under
their own `∃`, a closedness fact not yet stated either, though it should
follow from `Ren.Fresh` plus a "formula only depends on `ξ` at its own free
variables" instance of the coincidence lemma above), plus a matching
existence theorem obtained by the same strong induction, constructively
building a `Guarded.Tr` witness instead of consuming one.
-/

end CoreJS
