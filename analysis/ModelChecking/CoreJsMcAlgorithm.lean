/-
  # Core JavaScript — Model checking: the algorithm

  Model checking a query model against a finite trace system (`FinTSys`),
  for any abstraction, assignment domain and tracker meeting their
  specifications.

  A search state `(p, q, d, τ)` pairs a program state `p`, a state `q` of the
  model's `main` component, the set `d` of abstract assignments still
  possible, and a tracker `τ` summarising the labels read so far for the
  `except` check (`CoreJsMcTracker.lean`).  The search starts from the initial states with every variable
  unconstrained (refined by the invariants of `main`'s start), and steps by

  * a silent program edge alone;
  * an `ε`-edge of `main` alone, refining `d` by the invariants of its target;
  * an action edge `act as` of `main` together with a visible program edge `B`,
    constraining `d` by `as` matching `B`, refining by the target's
    invariants, discarding the step if `d` becomes empty, and stepping the
    tracker by `B`.

  Refining by the invariants of the *current* state loses nothing, since
  invariants only grow along edges (`QComp.Mono`): a value excluded now could
  never satisfy the invariants of a final state.  The search is the generic
  exploration of `CoreJsMcExplore.lean` (*progress*: a visited set), so it
  terminates: trackers are deterministic in the labels, so two walks reaching
  the same search state are interchangeable for every continuation.  A
  witness is a reachable state with a final program state and a final state
  of `main`, together with an assignment of `d` satisfying the final state's
  invariants and excluded by none of its `except` components, according to
  the tracker (`ADom.solve` with the test `excOk`).

  Results:
  * `witnesses_ne_nil_iff`: there is a witness iff the abstract semantics
    `QModel.ASat` holds — the search decides it exactly;
  * `mem_witnesses`: every witness is an accepting walk and assignment;
  * `model_check_complete`: with `QModel.asat_of_matches`, every record
    covered by the abstraction and matching the query yields a witness;
    `model_check_complete_enum` instantiates the domain with `nonrel` and the
    tracker with `enumTracker`.

  Plain Lean 4 — no Mathlib required.
-/

import ModelChecking.CoreJsMcTracker

namespace CoreJS

variable {A V Φ : Type}

/-! ## Finite trace systems -/

/-- A trace system given by successor lists, whose reachable states lie in a
    finite list. -/
structure FinTSys (A : Type) where
  St     : Type
  deq    : DecidableEq St
  init   : St
  final  : St → Bool
  succ   : St → List (Option A × St)
  finite : ∃ U : List St, init ∈ U ∧ ∀ s ∈ U, ∀ e ∈ succ s, e.2 ∈ U

/-- The trace system it presents. -/
def FinTSys.toTSys (P : FinTSys A) : TSys A where
  St    := P.St
  init  := P.init
  final s := P.final s = true
  edge s l s' := (l, s') ∈ P.succ s

theorem TSys.Walk.snoc_silent {S : TSys A} {s s' s'' : S.St} {T : List A}
    (h : S.Walk s T s') (he : S.edge s' none s'') : S.Walk s T s'' := by
  induction h with
  | nil => exact .silent he .nil
  | silent h₁ _ ih => exact .silent h₁ (ih he)
  | vis h₁ _ ih => exact .vis h₁ (ih he)

theorem TSys.Walk.snoc_vis {S : TSys A} {s s' s'' : S.St} {T : List A} {a : A}
    (h : S.Walk s T s') (he : S.edge s' (some a) s'') : S.Walk s (T ++ [a]) s'' := by
  induction h with
  | nil => exact .vis he .nil
  | silent h₁ _ ih => exact .silent h₁ (ih he)
  | vis h₁ _ ih => exact .vis h₁ (ih he)

theorem LRun.snoc_eps {α : Type} {es : List QEdge} {F : List (QAct MVar) → α → Prop}
    {s s' s'' : QSt} {w : List α} (h : LRun es F s w s') (he : (s', .eps, s'') ∈ es) :
    LRun es F s w s'' := by
  induction h with
  | nil => exact .eps he .nil
  | eps h₁ _ ih => exact .eps h₁ (ih he)
  | act h₁ hf _ ih => exact .act h₁ hf (ih he)

theorem LRun.snoc_act {α : Type} {es : List QEdge} {F : List (QAct MVar) → α → Prop}
    {s s' s'' : QSt} {w : List α} {as : List (QAct MVar)} {a : α} (h : LRun es F s w s')
    (he : (s', .act as, s'') ∈ es) (hf : F as a) : LRun es F s (w ++ [a]) s'' := by
  induction h with
  | nil => exact .act he hf .nil
  | eps h₁ _ ih => exact .eps h₁ (ih he)
  | act h₁ hf' _ ih => exact .act h₁ hf' (ih he)

/-! ## The search -/

section search

variable (P : FinTSys A) (c : QComp) (dom : ADom A V Φ) (tr : Tracker A V)

/-- Search states: program state, state of the component, assignments,
    tracker. -/
abbrev MSt := P.St × QSt × dom.D × tr.T

instance : DecidableEq (MSt P dom tr) :=
  @instDecidableEqProd _ _ P.deq
    (@instDecidableEqProd _ _ inferInstance (@instDecidableEqProd _ _ dom.deq tr.deq))

/-- The initial search state. -/
def mcInit : MSt P dom tr := (P.init, c.start, dom.refine dom.top (c.inv c.start), tr.init)

/-- The successors of a search state. -/
def mcSucc (st : MSt P dom tr) : List (MSt P dom tr) :=
  ((P.succ st.1).filter (fun e => e.1.isNone)).map (fun e => (e.2, st.2.1, st.2.2.1, st.2.2.2)) ++
  (((epsEdges c.edges).filter (fun e => decide (e.1 = st.2.1))).map
    fun e => (st.1, e.2, dom.refine st.2.2.1 (c.inv e.2), st.2.2.2)) ++
  ((P.succ st.1).filterMap (fun e => e.1.map (fun B => (B, e.2)))).flatMap fun e =>
    ((actEdges c.edges).filter (fun e' => decide (e'.1 = st.2.1))).filterMap fun e' =>
      if dom.empty (dom.refine (dom.constrain st.2.2.1 e'.2.1 e.1) (c.inv e'.2.2)) then none
      else some (e.2, e'.2.2, dom.refine (dom.constrain st.2.2.1 e'.2.1 e.1) (c.inv e'.2.2),
        tr.step st.2.2.2 e.1)

theorem mem_mcSucc {p : P.St} {q : QSt} {d : dom.D} {τ : tr.T} {y : MSt P dom tr} :
    y ∈ mcSucc P c dom tr (p, q, d, τ) ↔
      (∃ p', (none, p') ∈ P.succ p ∧ y = (p', q, d, τ)) ∨
      (∃ q', (q, .eps, q') ∈ c.edges ∧ y = (p, q', dom.refine d (c.inv q'), τ)) ∨
      (∃ B p' as q', (some B, p') ∈ P.succ p ∧ (q, .act as, q') ∈ c.edges ∧
        dom.empty (dom.refine (dom.constrain d as B) (c.inv q')) = false ∧
        y = (p', q', dom.refine (dom.constrain d as B) (c.inv q'), tr.step τ B)) := by
  simp only [mcSucc, List.mem_append, List.mem_map, List.mem_filter, List.mem_flatMap,
    List.mem_filterMap, Option.map_eq_some_iff, decide_eq_true_eq]
  constructor
  · rintro ((⟨⟨l, p'⟩, ⟨hp, hl⟩, rfl⟩ | ⟨⟨q₀, q'⟩, ⟨he, rfl⟩, rfl⟩) |
      ⟨⟨B, p'⟩, ⟨⟨l, p''⟩, hp, B', hl, hB⟩, ⟨q₀, as, q'⟩, ⟨he, rfl⟩, hy⟩)
    · simp at hl; subst hl; exact Or.inl ⟨p', hp, rfl⟩
    · exact Or.inr (Or.inl ⟨q', mem_epsEdges.1 he, rfl⟩)
    · simp only [Prod.mk.injEq] at hB
      obtain ⟨rfl, rfl⟩ := hB
      subst hl
      split at hy
      · cases hy
      · rename_i hne
        cases hy
        exact Or.inr (Or.inr ⟨B', p'', as, q', hp, mem_actEdges.1 he,
          Bool.eq_false_iff.2 hne, rfl⟩)
  · rintro (⟨p', hp, rfl⟩ | ⟨q', he, rfl⟩ | ⟨B, p', as, q', hp, he, hne, rfl⟩)
    · exact Or.inl (Or.inl ⟨(none, p'), ⟨hp, rfl⟩, rfl⟩)
    · exact Or.inl (Or.inr ⟨(q, q'), ⟨mem_epsEdges.2 he, rfl⟩, rfl⟩)
    · refine Or.inr ⟨(B, p'), ⟨(some B, p'), hp, B, rfl, rfl⟩, (q, as, q'),
        ⟨mem_actEdges.2 he, rfl⟩, ?_⟩
      simp [hne]

variable {P c dom tr}

/-- Reachable search states stay within a finite list. -/
theorem mcSucc_finite (hc : c.Closed)
    (hD : ∃ UD : List dom.D, dom.top ∈ UD ∧
      ∀ d ∈ UD, (∀ I, dom.refine d I ∈ UD) ∧ ∀ as B, dom.constrain d as B ∈ UD)
    (hT : ∃ UT : List tr.T, tr.init ∈ UT ∧ ∀ τ ∈ UT, ∀ B, tr.step τ B ∈ UT) :
    ∃ U : List (MSt P dom tr), mcInit P c dom tr ∈ U ∧ SuccClosed (mcSucc P c dom tr) U := by
  obtain ⟨UP, hUP, hUPc⟩ := P.finite
  obtain ⟨UD, hUD, hUDc⟩ := hD
  obtain ⟨UT, hUT, hUTc⟩ := hT
  let U : List (MSt P dom tr) := UP.flatMap fun p => c.states.flatMap fun q =>
    UD.flatMap fun d => UT.map fun τ => (p, q, d, τ)
  have memU : ∀ p q d τ, p ∈ UP → q ∈ c.states → d ∈ UD → τ ∈ UT → (p, q, d, τ) ∈ U := by
    intro p q d τ hp hq hd hτ
    simp only [U, List.mem_flatMap, List.mem_map]
    exact ⟨p, hp, q, hq, d, hd, τ, hτ, rfl⟩
  refine ⟨U, memU _ _ _ _ hUP hc.start ((hUDc _ hUD).1 _) hUT, ?_⟩
  intro x hx y hy
  simp only [U, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨p, hp, q, hq, d, hd, τ, hτ, rfl⟩ := hx
  rcases (mem_mcSucc P c dom tr).1 hy with ⟨p', hp', rfl⟩ | ⟨q', he, rfl⟩ |
    ⟨B, p', as, q', hp', he, _, rfl⟩
  · exact memU _ _ _ _ (hUPc p hp _ hp') hq hd hτ
  · exact memU _ _ _ _ hp (hc.edges _ _ _ he).2 ((hUDc d hd).1 _) hτ
  · exact memU _ _ _ _ (hUPc p hp _ hp') (hc.edges _ _ _ he).2
      ((hUDc _ ((hUDc d hd).2 as B)).1 _) (hUTc τ hτ B)

variable (P c dom tr)

/-- The `except` check at a final state `q` with tracker `τ`: no component of
    `exc q` must accept. -/
def excOk (q : QSt) (τ : tr.T) (ξ : MVar → V) : Bool :=
  (c.exc q).all fun k => !tr.excl τ k ξ

/-- The witnesses found: program final state, final state of the component,
    and an assignment satisfying its invariants and passing its `except`
    check. -/
def witnesses (hc : c.Closed)
    (hD : ∃ UD : List dom.D, dom.top ∈ UD ∧
      ∀ d ∈ UD, (∀ I, dom.refine d I ∈ UD) ∧ ∀ as B, dom.constrain d as B ∈ UD)
    (hT : ∃ UT : List tr.T, tr.init ∈ UT ∧ ∀ τ ∈ UT, ∀ B, tr.step τ B ∈ UT) :
    List (P.St × QSt × (MVar → V)) :=
  (explore (mcSucc P c dom tr) (mcInit P c dom tr) (mcSucc_finite hc hD hT)).filterMap fun st =>
    if P.final st.1 && decide (st.2.1 ∈ c.finals) then
      (dom.solve st.2.2.1 (c.inv st.2.1) tr.reads (excOk c tr st.2.1 st.2.2.2)).map
        fun ξ => (st.1, st.2.1, ξ)
    else none

end search

/-! ## Correctness -/

section correct

variable {P : FinTSys A} {c : QComp} {dom : ADom A V Φ} {tr : Tracker A V} {𝔄 : Abs A V Φ}
  {φ : Φ} {good : List (QAct MVar) → Prop}

/-- Every reachable search state is reached along a walk, read by `c` under
    every assignment it still allows, and its tracker summarises the walk. -/
theorem reach_sound (hdom : dom.Spec 𝔄 φ good)
    (hgood : ∀ s as s', (s, .act as, s') ∈ c.edges → good as) {st : MSt P dom tr}
    (h : Reach (mcSucc P c dom tr) (mcInit P c dom tr) st) :
    ∃ T, P.toTSys.Walk P.init T st.1 ∧
      (∀ ξ, dom.mem st.2.2.1 ξ → LRun c.edges (𝔄.Fires ξ) c.start T st.2.1) ∧
      st.2.2.2 = tr.run T := by
  induction h with
  | refl => exact ⟨[], .nil, fun _ _ => .nil, rfl⟩
  | @step y z _ hy ih =>
    obtain ⟨T, hw, hrun, hτ⟩ := ih
    obtain ⟨p₀, q₀, d₀, τ₀⟩ := y
    rcases (mem_mcSucc P c dom tr).1 hy with ⟨p', hp', rfl⟩ | ⟨q', he, rfl⟩ |
      ⟨B, p', as, q', hp', he, _, rfl⟩
    · exact ⟨T, hw.snoc_silent hp', hrun, hτ⟩
    · exact ⟨T, hw, fun ξ hξ => (hrun ξ (hdom.refine_sub _ _ _ hξ)).snoc_eps he, hτ⟩
    · refine ⟨T ++ [B], hw.snoc_vis hp', fun ξ hξ => ?_, by
        simp only [Tracker.run_snoc]; exact congrArg (tr.step · B) hτ⟩
      obtain ⟨h₁, h₂⟩ := (hdom.constrain _ _ _ _ (hgood _ _ _ he)).1 (hdom.refine_sub _ _ _ hξ)
      exact (hrun ξ h₁).snoc_act he h₂

/-- Conversely, a walk read by `c` under `ξ`, ending in a state whose
    invariants `ξ` may satisfy, is followed by the search keeping `ξ`, the
    tracker summarising the whole walk. -/
theorem reach_complete (hdom : dom.Spec 𝔄 φ good)
    (hgood : ∀ s as s', (s, .act as, s') ∈ c.edges → good as) (hm : c.Mono) (ξ : MVar → V) :
    ∀ {p : P.toTSys.St} {T : List A} {p' : P.toTSys.St}, P.toTSys.Walk p T p' →
      ∀ {q q' : QSt} {d : dom.D} {T₀ : List A},
        Reach (mcSucc P c dom tr) (mcInit P c dom tr) (p, q, d, tr.run T₀) →
        dom.mem d ξ → LRun c.edges (𝔄.Fires ξ) q T q' →
        (∀ J ∈ c.inv q', 𝔄.inv φ ξ true J = true) →
        ∃ d', Reach (mcSucc P c dom tr) (mcInit P c dom tr) (p', q', d', tr.run (T₀ ++ T)) ∧
          dom.mem d' ξ := by
  -- `ε`-steps of the component, the program staying put.
  have epsOnly : ∀ {p : P.St} {q q' : QSt} {d : dom.D} {τ : tr.T} {w : List A},
      Reach (mcSucc P c dom tr) (mcInit P c dom tr) (p, q, d, τ) → dom.mem d ξ →
      LRun c.edges (𝔄.Fires ξ) q w q' → w = [] →
      (∀ J ∈ c.inv q', 𝔄.inv φ ξ true J = true) →
      ∃ d', Reach (mcSucc P c dom tr) (mcInit P c dom tr) (p, q', d', τ) ∧ dom.mem d' ξ := by
    intro p q q' d τ w hr hd hrun hw hinv
    induction hrun generalizing d with
    | nil => exact ⟨d, hr, hd⟩
    | @eps q₁ q₂ _ _ he hrest ih =>
      refine ih (.step hr ((mem_mcSucc P c dom tr).2 (Or.inr (Or.inl ⟨q₂, he, rfl⟩))))
        (hdom.refine_keep _ _ _ hd fun J hJ => hinv J (hrest.inv_mono hm hJ)) hw hinv
    | act => cases hw
  -- Steps of the component up to and including the one reading `a`.
  have one : ∀ {p p₁ : P.St} {a : A} {q q' : QSt} {d : dom.D} {τ : tr.T} {w : List A}
      {T : List A},
      Reach (mcSucc P c dom tr) (mcInit P c dom tr) (p, q, d, τ) → dom.mem d ξ →
      (some a, p₁) ∈ P.succ p → LRun c.edges (𝔄.Fires ξ) q w q' → w = a :: T →
      (∀ J ∈ c.inv q', 𝔄.inv φ ξ true J = true) →
      ∃ q₁ d₁, Reach (mcSucc P c dom tr) (mcInit P c dom tr) (p₁, q₁, d₁, tr.step τ a) ∧
        dom.mem d₁ ξ ∧ LRun c.edges (𝔄.Fires ξ) q₁ T q' := by
    intro p p₁ a q q' d τ w T hr hd hp hrun hw hinv
    induction hrun generalizing d with
    | nil => cases hw
    | @eps q₁ q₂ _ _ he hrest ih =>
      exact ih (.step hr ((mem_mcSucc P c dom tr).2 (Or.inr (Or.inl ⟨q₂, he, rfl⟩))))
        (hdom.refine_keep _ _ _ hd fun J hJ => hinv J (hrest.inv_mono hm hJ)) hw hinv
    | @act q₁ q₂ _ as a' w' he hf hrest =>
      simp only [List.cons.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hd' : dom.mem (dom.refine (dom.constrain d as a') (c.inv q₂)) ξ :=
        hdom.refine_keep _ _ _ ((hdom.constrain _ _ _ _ (hgood _ _ _ he)).2 ⟨hd, hf⟩)
          fun J hJ => hinv J (hrest.inv_mono hm hJ)
      exact ⟨q₂, _, .step hr ((mem_mcSucc P c dom tr).2 (Or.inr (Or.inr ⟨a', p₁, as, q₂, hp,
        he, hdom.empty _ _ hd', rfl⟩))), hd', hrest⟩
  intro p T p' hw
  induction hw with
  | nil =>
    intro q q' d T₀ hr hd hrun hinv
    simpa using epsOnly hr hd hrun rfl hinv
  | silent he _ ih =>
    intro q q' d T₀ hr hd hrun hinv
    exact ih (.step hr ((mem_mcSucc P c dom tr).2 (Or.inl ⟨_, he, rfl⟩))) hd hrun hinv
  | @vis _ _ _ a T he _ ih =>
    intro q q' d T₀ hr hd hrun hinv
    obtain ⟨q₁, d₁, hr₁, hd₁, hrun₁⟩ := one hr hd he hrun rfl hinv
    rw [← Tracker.run_snoc] at hr₁
    simpa using ih hr₁ hd₁ hrun₁ hinv

/-- The `except` check passes iff no component of `exc q` must accept. -/
theorem excOk_iff {M : QModel} (htr : tr.Spec 𝔄 φ M) {q : QSt} {T : List A} {ξ : MVar → V} :
    excOk M.main tr q (tr.run T) ξ = true ↔ ∀ k ∈ M.main.exc q, ¬ M.AExcl 𝔄 φ T k ξ := by
  simp only [excOk, List.all_eq_true, Bool.not_eq_true', ← htr.excl]
  exact forall₂_congr fun _ _ => by simp

/-- Every witness is an accepting walk and assignment. -/
theorem mem_witnesses {M : QModel} (hdom : dom.Spec 𝔄 φ good) (htr : tr.Spec 𝔄 φ M)
    (hgood : ∀ s as s', (s, .act as, s') ∈ M.main.edges → good as) (hc : M.main.Closed) (hD hT)
    {s : P.St} {f : QSt} {ξ : MVar → V} (h : (s, f, ξ) ∈ witnesses P M.main dom tr hc hD hT) :
    ∃ T, P.toTSys.Walk P.init T s ∧ P.final s = true ∧ f ∈ M.main.finals ∧
      LRun M.main.edges (𝔄.Fires ξ) M.main.start T f ∧
      (∀ J ∈ M.main.inv f, 𝔄.inv φ ξ true J = true) ∧ ∀ k ∈ M.main.exc f, ¬ M.AExcl 𝔄 φ T k ξ := by
  simp only [witnesses, List.mem_filterMap] at h
  obtain ⟨⟨p, q, d, τ⟩, hst, hw⟩ := h
  split at hw
  · rename_i hacc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
    obtain ⟨ξ', hsol, he⟩ := Option.map_eq_some_iff.1 hw
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨hmem, hinv, hexc⟩ := hdom.solve_sound _ _ _ _ _ hsol
    obtain ⟨T, hw', hrun, hτ⟩ := reach_sound hdom hgood ((mem_explore _ _ _ _).1 hst)
    simp only at hτ; subst hτ
    exact ⟨T, hw', hacc.1, hacc.2, hrun ξ' hmem, hinv, (excOk_iff htr).1 hexc⟩
  · cases hw

/-- **Exactness.** The search finds a witness iff the abstract semantics
    holds. -/
theorem witnesses_ne_nil_iff {M : QModel} (hdom : dom.Spec 𝔄 φ good) (htr : tr.Spec 𝔄 φ M)
    (hgood : ∀ s as s', (s, .act as, s') ∈ M.main.edges → good as) (hc : M.main.Closed)
    (hm : M.main.Mono) (hD hT) :
    witnesses P M.main dom tr hc hD hT ≠ [] ↔ M.ASat P.toTSys 𝔄 φ := by
  constructor
  · intro h
    obtain ⟨⟨s, f, ξ⟩, hx⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨T, hw, hs, hf, hrun, hinv, hexc⟩ := mem_witnesses hdom htr hgood hc hD hT hx
    exact ⟨T, s, hw, hs, f, hf, ξ, hrun, hinv, hexc⟩
  · rintro ⟨T, s, hw, hs, f, hf, ξ, hrun, hinv, hexc⟩
    have hd₀ : dom.mem (mcInit P M.main dom tr).2.2.1 ξ :=
      hdom.refine_keep _ _ _ (hdom.top ξ) fun J hJ => hinv J (hrun.inv_mono hm hJ)
    obtain ⟨d, hr, hd⟩ := reach_complete hdom hgood hm ξ hw (T₀ := []) .refl hd₀ hrun hinv
    simp only [List.nil_append] at hr
    have hsol := hdom.solve_complete _ _ tr.reads _ _ (fun ξ₁ ξ₂ h => by
      simp only [excOk]; congr 1; funext k; rw [htr.reads _ k ξ₁ ξ₂ h]) hd hinv
      ((excOk_iff htr).2 hexc)
    obtain ⟨ξ', hξ'⟩ := Option.isSome_iff_exists.1 hsol
    refine List.ne_nil_of_mem (a := (s, f, ξ')) (List.mem_filterMap.2
      ⟨(s, f, d, tr.run T), (mem_explore _ _ _ _).2 hr, ?_⟩)
    have hacc : (P.final s && decide (f ∈ M.main.finals)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hs, hf⟩
    simp only [hacc, hξ', if_true, Option.map_some]
    rfl

/-- **Completeness of model checking.** For a well-formed query program, every
    record covered by the abstraction and matching the query yields a witness. -/
theorem model_check_complete (h𝔄 : 𝔄.Sound) {Δ : QProg} {q : Query} (hwf : QProg.WF (q :: Δ))
    (hdom : dom.Spec 𝔄 φ good) (htr : tr.Spec 𝔄 φ (q.toQModel Δ))
    (hgood : ∀ s as s', (s, .act as, s') ∈ (q.toQModel Δ).main.edges → good as) (hD hT)
    {R : Exec → Prop} (hcov : Covers P.toTSys 𝔄 φ R) {e : Exec} (he : R e) {ls : List Loc}
    (hlen : ls.length = q.params.length) (hmatch : Exec.Matches (q :: Δ) e q.name ls) :
    witnesses P (q.toQModel Δ).main dom tr (Query.toQModel_wf hwf).1 hD hT ≠ [] :=
  (witnesses_ne_nil_iff hdom htr hgood _ (Query.toQModel_wf hwf).2.1 hD hT).2
    (QModel.asat_of_matches h𝔄 hcov hwf he hlen hmatch)

end correct

/-! ## With the non-relational domain and the enumerating tracker -/

/-- **Completeness of model checking**, with one set of values per variable of
    the model's labels, and trackers enumerating the `except` components'
    variables. -/
theorem model_check_complete_enum [DecidableEq V] [Inhabited V] {P : FinTSys A}
    {𝔄 : Abs A V Φ} (h𝔄 : 𝔄.Sound) (S : 𝔄.Sep) {φ : Φ} {vals : List V}
    (hvals : ∀ v, v ∈ vals) {Δ : QProg} {q : Query} (hwf : QProg.WF (q :: Δ))
    {R : Exec → Prop} (hcov : Covers P.toTSys 𝔄 φ R) {e : Exec} (he : R e) {ls : List Loc}
    (hlen : ls.length = q.params.length) (hmatch : Exec.Matches (q :: Δ) e q.name ls) :
    witnesses P (q.toQModel Δ).main (nonrel vals (q.toQModel Δ).main.labelVars 𝔄 φ S)
      (enumTracker 𝔄 φ (q.toQModel Δ) vals (q.toQModel Δ).compVars)
      (Query.toQModel_wf hwf).1 (nonrel_spec vals _ 𝔄 φ S h𝔄 hvals).finite
      (enumTracker_spec h𝔄 hvals (fun c hc => ((Query.toQModel_wf hwf).2.2 c hc).1)
        QModel.compVars_labels QModel.compVars_inv).finite ≠ [] :=
  model_check_complete h𝔄 hwf (nonrel_spec vals _ 𝔄 φ S h𝔄 hvals)
    (enumTracker_spec h𝔄 hvals (fun c hc => ((Query.toQModel_wf hwf).2.2 c hc).1)
      QModel.compVars_labels QModel.compVars_inv)
    (QComp.labelVars_good _) _ _ hcov he hlen hmatch

end CoreJS
