/-
  # Core JavaScript — Soundness of the Automaton-Based Static Analysis

  The automaton counterpart of Theorem B15: every concrete execution is
  `α`-related, at whatever automaton state it structurally lands on, to a
  valid labeling's value there.

  ## Status

  **Incomplete**, in the sense the project's `sorry` policy describes (see
  `CLAUDE.md`): the statement, the supporting infrastructure, and most cases
  are proved (`skip`/`assign`/`setTaint`/`setSink`/`lookupS`/`lookupD`/
  `updateS`/`updateD`/`ret`/`seqRet`/`seqCont`/`ifTrue`/`ifFalse`); the
  harder cases (`binOp`/`objLit`, which need a new cross-spec relating `⊕`
  to `⊕̂` introduced below *and* an `α`-freshness invariant this proof does
  not track yet; `whileDo`, which needs induction on iteration count; `call`,
  which needs the candidate-search/recursion assembly) are `sorry`,
  documented at each site with what remains. No `axiom`s are used.

  ## Why this proof is *simpler* than the old `soundnessN`, in one respect

  The old proof needed `SigmaValid`/`[Weakening]`-absorbing generation lemmas
  because recursion was handled by *assuming* a not-yet-derived summary
  (`[Call-Fix]`/`[Call-Assume]`) and `[Weakening]` could interpose anywhere.
  Neither exists in the automaton model: a `Labeling` is a single, flat,
  non-recursive predicate over the *whole* graph at once (`Labeling.Valid`),
  so a recursive call is handled by simply *looking up* the labeling at the
  callee's entry state — no assume/guarantee invariant, no per-rule
  `[Weakening]` absorption, needed at all. What the old proof spent on those
  two mechanisms, this one spends on threading the "which edges of *this*
  substatement does `Valid` actually vouch for" hypothesis through the
  induction (see `hvalidS` in `step_sound` below) — mechanical, but new.

  See `PROBLEMS.md` for the decisions made while writing this file.
-/

import CoreJsAutomatonRelation

namespace CoreJS

/-! ## A cross-spec relating the concrete and abstract binary operators

Needed for `binOp`'s soundness; has no counterpart in `ConcreteSpec`/
`AbstractSpec` (both purely one-sided) or anywhere in the old development —
the old proof's own "Remaining work" list flagged `[Binary Operation]` as
unstarted, so this obligation was never previously written down either. -/

/-- `⊕̂` soundly over-approximates `⊕`: if both operands are related, so is
    the result. -/
structure OpSemSound [Concrete] [Abstract] : Prop where
  opSem_sound : ∀ op v₁ v₂ (V₁ V₂ : VSet), V₁.Mem v₁ → V₂.Mem v₂ →
    (Abstract.opSemA op V₁ V₂).Mem (Concrete.opSem op v₁ v₂)

/-! ## Small helper facts -/

theorem evalEs_length [Concrete] :
    ∀ {ρ : Sto} {es : List Expr} {ls : List Loc}, evalEs ρ es = some ls →
      ls.length = es.length
  | _, [], _, he => by simp only [evalEs, Option.some.injEq] at he; subst he; rfl
  | ρ, e :: es, ls, he => by
      rw [evalEs] at he
      cases hE : evalE ρ e with
      | none => rw [hE] at he; simp at he
      | some l =>
          cases hEs : evalEs ρ es with
          | none => rw [hE, hEs] at he; simp at he
          | some ls' =>
              rw [hE, hEs] at he
              have hx : l :: ls' = ls := by injection he
              subst hx
              simp only [List.length_cons, evalEs_length hEs]

theorem aevalEs_length [Abstract] : ∀ (ρ : ASto) (es : List Expr),
    (aevalEs ρ es).length = es.length
  | _, []      => rfl
  | ρ, e :: es => by simp [aevalEs, aevalEs_length ρ es]

/-- Lemma B11, lifted to whole parameter lists: the callee's freshly built
    store relates to the abstract store built the same way, given the
    argument lists are related componentwise. -/
theorem sto_ofParams_alpha {α : AlphaFn} :
    ∀ {ls : List Loc} {Ls : List ALocSet}, LocsAlpha α ls Ls →
      ∀ params : List Var, Sto.Alpha α (Sto.ofParams params ls) (ASto.ofParams params Ls)
  | [], [], _, params => by
      cases params <;> (intro y l hy; exact absurd hy (by simp [Sto.ofParams, Sto.empty]))
  | l :: ls, L :: Ls, h, params => by
      cases params with
      | nil => intro y l' hy; exact absurd hy (by simp [Sto.ofParams, Sto.empty])
      | cons x xs =>
          show Sto.Alpha α ((Sto.ofParams xs ls).upd x l) ((ASto.ofParams xs Ls).upd x L)
          exact sto_upd_alpha (sto_ofParams_alpha h.2 xs) h.1
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

/-! ## Main soundness lemma

`step_sound` inducts on the height of the *concrete* derivation (strong
induction, exactly as the old `soundnessN` did — needed because `call`'s
case recurses into a shorter derivation of a *different* statement). At every
statement shape it takes, as an explicit hypothesis, exactly the slice of
`Labeling.Valid` that concerns the substatement currently being processed
(`hvalidS`); recursing into a substatement re-derives the narrower hypothesis
needed for it by wrapping the relevant `AEdge` constructor around a fact
about the substatement (turning it into a fact about the whole statement,
which `hvalidS` already covers) — see the file header. Recursing across a
function call instead gets a *fresh* `hvalidS` directly from `Labeling.Valid`
`.2` (the closure over every function body at every well-formed call
string), which is exactly why `Labeling.Valid` has two conjuncts rather than
one. -/

theorem step_sound [Concrete] [Abstract] (cspec : ConcreteSpec) (aspec : AbstractSpec)
    (opspec : OpSemSound) {Γ : Env} {L : Labeling} (hΓ : EnvSpec Γ) :
    ∀ (n : Nat) {cs : CallString} {entry : AState} {pending : AConf → AConf}
      {s : Stmt} {c : Conf} {r : Res} {α : AlphaFn},
      CallString.WF cs →
      α.Lits →
      (∀ a b C, AEdge Γ cs entry pending s a b C → C (L a) ⊑ L b) →
      BigStepN Γ n c s r →
      AConf.Alpha α c (pending (L entry)) →
      ( (∃ x xpending, AExit Γ cs entry pending s x xpending ∧ r.out = .cont ∧
           ∃ α', α' ≥α α ∧ α'.Lits ∧
             AConf.Alpha α' ⟨r.heap, r.sto, r.reg⟩ (xpending (L x)))
      ∨ (∃ rst rpending e' l, ARet Γ cs entry pending s rst rpending e' ∧ r.out = .ret l ∧
           ∃ α', α' ≥α α ∧ α'.Lits ∧
             AConf.Alpha α' ⟨r.heap, r.sto, r.reg⟩ (rpending (L rst)) ∧
             α'.MapsInto l (aevalE (rpending (L rst)).sto e')) ) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
    intro cs entry pending s c r α hcs hlit hvalidS H hα
    cases H with
    | skip =>
        exact Or.inl ⟨entry, pending, .skip, rfl, α, .refl α, hlit, hα⟩
    | @assign _ h ρ ρ' δ x e l he hρ' =>
        subst hρ'
        refine Or.inl ⟨entry, AConf.doAssign x e ∘ pending, .assign, rfl, α, .refl α, hlit, ?_⟩
        have hval := eval_alpha hlit hα.2.1 he
        exact ⟨hα.1, sto_upd_alpha hα.2.1 hval, hα.2.2⟩
    | @setTaint _ h ρ δ δ' e l he hδ' =>
        subst hδ'
        refine Or.inl ⟨entry, AConf.doSetTaint e ∘ pending, .setTaint, rfl, α, .refl α, hlit, ?_⟩
        have hval := eval_alpha hlit hα.2.1 he
        refine ⟨hα.1, hα.2.1, ?_, ?_, ?_⟩
        · exact hα.2.2.1
        · intro y hy
          rcases hy with hy | hy
          · subst hy; exact hval.subset (fun _ h => Or.inl h)
          · exact (hα.2.2.2.1 y hy).subset (fun _ h => Or.inr h)
        · exact hα.2.2.2.2
    | @setSink _ h ρ δ δ' e l he hδ' =>
        subst hδ'
        refine Or.inl ⟨entry, AConf.doSetSink e ∘ pending, .setSink, rfl, α, .refl α, hlit, ?_⟩
        have hval := eval_alpha hlit hα.2.1 he
        refine ⟨hα.1, hα.2.1, hα.2.2.1, ?_, ?_⟩
        · exact hα.2.2.2.1
        · intro y hy
          rcases hy with hy | hy
          · subst hy; exact hval.subset (fun _ h => Or.inl h)
          · exact (hα.2.2.2.2 y hy).subset (fun _ h => Or.inr h)
    | @lookupS _ h ρ ρ' δ x κ e p l₁ l₂ he hobj hρ' =>
        subst hρ'
        have hval := eval_alpha hlit hα.2.1 he
        have hmaps := hα.1.objOf hval hobj
        have hcα : AConf.Alpha α ⟨h, ρ.upd x l₂, δ⟩ (AConf.doLookupS x e p (pending (L entry))) :=
          ⟨hα.1, sto_upd_alpha hα.2.1 hmaps, hα.2.2⟩
        have hedge : (AConf.doLookupS x e p ∘ pending) (L entry) ⊑ L (.action cs κ) :=
          hvalidS _ _ _ AEdge.lookupS
        exact Or.inl ⟨.action cs κ, id, .lookupS, rfl, α, .refl α, hlit, hcα.le hedge⟩
    | @lookupD _ h ρ ρ' δ x κ e₁ e₂ l₁ l₂ l₃ p he1 he2 hstr hobj hρ' =>
        subst hρ'
        have hval1 := eval_alpha hlit hα.2.1 he1
        have hval2 := eval_alpha hlit hα.2.1 he2
        have hVmem := hα.1.valOf hval2 hstr
        have hmaps := hα.1.objOfV hval1 hVmem hobj
        have hcα : AConf.Alpha α ⟨h, ρ.upd x l₃, δ⟩ (AConf.doLookupD x e₁ e₂ (pending (L entry))) :=
          ⟨hα.1, sto_upd_alpha hα.2.1 hmaps, hα.2.2⟩
        have hedge : (AConf.doLookupD x e₁ e₂ ∘ pending) (L entry) ⊑ L (.action cs κ) :=
          hvalidS _ _ _ AEdge.lookupD
        exact Or.inl ⟨.action cs κ, id, .lookupD, rfl, α, .refl α, hlit, hcα.le hedge⟩
    | @ret _ h ρ δ e l he =>
        exact Or.inr ⟨entry, pending, e, l, .ret, rfl, α, .refl α, hlit, hα,
          eval_alpha hlit hα.2.1 he⟩
    | @seqRet nred h h' ρ ρ' δ δ' s1 s2 t l Hstep1 =>
        have hvalidS1 : ∀ a b C, AEdge Γ cs entry pending s1 a b C → C (L a) ⊑ L b :=
          fun a b C he => hvalidS a b C (.seqLeft he)
        rcases IH nred (Nat.lt_succ_self _) hcs hlit hvalidS1 Hstep1 hα with
          ⟨_, _, _, hcont, _⟩ | ⟨rst, rpending, e', l', hARet1, hout, α', hext, hlit', hαres, hmaps⟩
        · exact absurd hcont (by simp)
        · exact Or.inr ⟨rst, rpending, e', l', .seqLeft hARet1, hout, α', hext, hlit', hαres, hmaps⟩
    | @seqCont nred h h' h'' ρ ρ' ρ'' δ δ' δ'' s1 s2 t1 t2 o Hstep1 Hstep2 =>
        have hvalidS1 : ∀ a b C, AEdge Γ cs entry pending s1 a b C → C (L a) ⊑ L b :=
          fun a b C he => hvalidS a b C (.seqLeft he)
        rcases IH nred (Nat.lt_succ_self _) hcs hlit hvalidS1 Hstep1 hα with
          ⟨x, xpending, hAExit1, _, α1, hext1, hlit1, hα1⟩
          | ⟨_, _, _, _, hARet1, hout, _⟩
        · have hvalidS2 : ∀ a b C, AEdge Γ cs x xpending s2 a b C → C (L a) ⊑ L b :=
            fun a b C he => hvalidS a b C (.seqRight hAExit1 he)
          rcases IH nred (Nat.lt_succ_self _) hcs hlit1 hvalidS2 Hstep2 hα1 with
              ⟨y, ypending, hAExit2, hout2, α2, hext2, hlit2, hαres⟩
            | ⟨rst, rpending, e', l, hARet2, hout2, α2, hext2, hlit2, hαres, hmaps⟩
          · exact Or.inl ⟨y, ypending, .seq hAExit1 hAExit2, hout2, α2,
              hext1.trans hext2, hlit2, hαres⟩
          · exact Or.inr ⟨rst, rpending, e', l, .seqRight hAExit1 hARet2, hout2, α2,
              hext1.trans hext2, hlit2, hαres, hmaps⟩
        · exact absurd hout (by simp)
    | binOp _ _ _ _ _ _ _ _ _ _ =>
        -- Needs `OpSemSound` (introduced above) plus extending `α` at the
        -- fresh allocation site `allocC h κ ↦ allocA (AConf.doBinOp ...).heap
        -- κ` (justified by `ConcreteSpec.allocC_fresh`/`AbstractSpec.
        -- allocA_site`, exactly as the old file's "Remaining work" item 3
        -- describes) — not yet done.
        sorry
    | objLit _ _ _ _ _ =>
        -- Same shape as `binOp`: needs the `α`-extension at a fresh
        -- allocation site. Not yet done.
        sorry
    | @updateS _ h h' ρ δ κ e1 p e2 l1 l2 he1 he2 hh' =>
        subst hh'
        have hval1 := eval_alpha hlit hα.2.1 he1
        have hval2 := eval_alpha hlit hα.2.1 he2
        have hcα : AConf.Alpha α ⟨h.setObj l1 p l2, ρ, δ⟩
            (AConf.doUpdateS e1 p e2 (pending (L entry))) :=
          ⟨hα.1.setObj hval1 hval2, hα.2.1, hα.2.2⟩
        have hedge : (AConf.doUpdateS e1 p e2 ∘ pending) (L entry) ⊑ L (.action cs κ) :=
          hvalidS _ _ _ AEdge.updateS
        exact Or.inl ⟨.action cs κ, id, .updateS, rfl, α, .refl α, hlit, hcα.le hedge⟩
    | @updateD _ h h' ρ δ κ e1 e2 e3 l1 l2 l3 p he1 he2 he3 hstr hh' =>
        subst hh'
        have hval1 := eval_alpha hlit hα.2.1 he1
        have hval2 := eval_alpha hlit hα.2.1 he2
        have hval3 := eval_alpha hlit hα.2.1 he3
        have hVmem := hα.1.valOf hval2 hstr
        have hcα : AConf.Alpha α ⟨h.setObj l1 p l3, ρ, δ⟩
            (AConf.doUpdateD e1 e2 e3 (pending (L entry))) :=
          ⟨hα.1.setObjV hval1 hVmem hval3, hα.2.1, hα.2.2⟩
        have hedge : (AConf.doUpdateD e1 e2 e3 ∘ pending) (L entry) ⊑ L (.action cs κ) :=
          hvalidS _ _ _ AEdge.updateD
        exact Or.inl ⟨.action cs κ, id, .updateD, rfl, α, .refl α, hlit, hcα.le hedge⟩
    | @ifTrue nred _ ρ δ κ e s1 s2 l r' he hval Hstep1 =>
        have hedge_in : pending (L entry) ⊑ L (.ifThen cs κ) := hvalidS _ _ _ .ifThen
        have hα' : AConf.Alpha α _ (L (.ifThen cs κ)) := hα.le hedge_in
        have hvalidS1 : ∀ a b C, AEdge Γ cs (.ifThen cs κ) id s1 a b C → C (L a) ⊑ L b :=
          fun a b C he => hvalidS a b C (.ifThenBody he)
        rcases IH nred (Nat.lt_succ_self _) hcs hlit hvalidS1 Hstep1 hα' with
            ⟨x, xpending, hAExit1, hout, α', hext, hlit', hαres⟩
          | ⟨rst, rpending, e', l', hARet1, hout, α', hext, hlit', hαres, hmaps⟩
        · have hedge_out : xpending (L x) ⊑ L (.ifEnd cs κ) :=
            hvalidS _ _ _ (.ifThenJoin hAExit1)
          exact Or.inl ⟨.ifEnd cs κ, id, .ifElse, hout, α', hext, hlit', hαres.le hedge_out⟩
        · exact Or.inr ⟨rst, rpending, e', l', .ifThen hARet1, hout, α', hext, hlit', hαres, hmaps⟩
    | @ifFalse nred _ ρ δ κ e s1 s2 l r' he hval Hstep2 =>
        have hedge_in : pending (L entry) ⊑ L (.ifElseB cs κ) := hvalidS _ _ _ .ifElseB
        have hα' : AConf.Alpha α _ (L (.ifElseB cs κ)) := hα.le hedge_in
        have hvalidS2 : ∀ a b C, AEdge Γ cs (.ifElseB cs κ) id s2 a b C → C (L a) ⊑ L b :=
          fun a b C he => hvalidS a b C (.ifElseBBody he)
        rcases IH nred (Nat.lt_succ_self _) hcs hlit hvalidS2 Hstep2 hα' with
            ⟨x, xpending, hAExit2, hout, α', hext, hlit', hαres⟩
          | ⟨rst, rpending, e', l', hARet2, hout, α', hext, hlit', hαres, hmaps⟩
        · have hedge_out : xpending (L x) ⊑ L (.ifEnd cs κ) :=
            hvalidS _ _ _ (.ifElseBJoin hAExit2)
          exact Or.inl ⟨.ifEnd cs κ, id, .ifElse, hout, α', hext, hlit', hαres.le hedge_out⟩
        · exact Or.inr ⟨rst, rpending, e', l', .ifElseB hARet2, hout, α', hext, hlit', hαres, hmaps⟩
    | whileDo _ =>
        -- Unfolds to `ifElse e (seq s (whileDo e s)) skip` concretely
        -- (`BigStepN.whileDo`), but the *automaton* does not unfold — it has
        -- a genuine back-edge (`AEdge.whileBack`) and a single pair of
        -- `whileIn`/`whileOut` states shared across every iteration. Relating
        -- these needs an argument by induction on the number of concrete
        -- loop iterations taken (each iteration re-uses the *same*
        -- `whileIn`/`AEdge.whileBody` facts, validated once), not a direct
        -- structural mirroring the way every other case here is. Not yet
        -- done.
        sorry
    | callRet _ _ _ _ _ _ _ =>
        -- The main argument sketched in the file header: (1) build the
        -- `AEdge.callEntry` fact and use `hvalidS`/`IsCandidate` (established
        -- from `hα` via `Heap.Alpha.valOf`) to relate the callee's initial
        -- store (`sto_ofParams_alpha` above) up to `L (entry cs_f)`;
        -- (2) invoke `IH` on the callee body at `cs_f` — using
        -- `Labeling.Valid`'s *second* conjunct (via `hΓ`/`EnvSpec` to know
        -- `Γ f` and `targetCallString_wf` for `CallString.WF cs_f`) as the
        -- fresh `hvalidS`, not a wrapped one; (3) build `AEdge.callRet` from
        -- the resulting `ARet` fact and use `hvalidS` again to relate the
        -- return value, bound via `ASto.bot.upd x`, up to `L (cont cs κ)`.
        -- Not yet done — every ingredient above is in place, this is
        -- "only" assembly, but nontrivial assembly.
        sorry
    | callCont _ _ _ _ _ _ _ =>
        -- Symmetric to `callRet`, using the newly-added
        -- `AEdge.callImplicitRet` (`PROBLEMS.md` decision 7, added to
        -- `CoreJsAutomatonSemantics.lean` once this case exposed the gap):
        -- the callee falls through with `.cont`, so its own `AExit` fact
        -- (from `IH`'s `.cont` disjunct) plays the role `ARet`'s fact played
        -- in `callRet`, and the contribution binds `x` to `{litLocA .undef}`
        -- instead of an evaluated return expression. Same assembly work as
        -- `callRet`, not yet done.
        sorry

/-- Corollary form, height existentially quantified away — the automaton
    counterpart of the old `soundness`/`soundness_top`. Immediate from
    `step_sound` via `BigStep.toN`, exactly as before. -/
theorem sound [Concrete] [Abstract] (cspec : ConcreteSpec) (aspec : AbstractSpec)
    (opspec : OpSemSound) {Γ : Env} {L : Labeling} (hΓ : EnvSpec Γ)
    {cs : CallString} {entry : AState} {pending : AConf → AConf} {s : Stmt}
    {c : Conf} {r : Res} {α : AlphaFn}
    (hcs : CallString.WF cs) (hlit : α.Lits)
    (hvalidS : ∀ a b C, AEdge Γ cs entry pending s a b C → C (L a) ⊑ L b)
    (H : BigStep Γ c s r) (hα : AConf.Alpha α c (pending (L entry))) :
    ( (∃ x xpending, AExit Γ cs entry pending s x xpending ∧ r.out = .cont ∧
         ∃ α', α' ≥α α ∧ α'.Lits ∧
           AConf.Alpha α' ⟨r.heap, r.sto, r.reg⟩ (xpending (L x)))
    ∨ (∃ rst rpending e' l, ARet Γ cs entry pending s rst rpending e' ∧ r.out = .ret l ∧
         ∃ α', α' ≥α α ∧ α'.Lits ∧
           AConf.Alpha α' ⟨r.heap, r.sto, r.reg⟩ (rpending (L rst)) ∧
           α'.MapsInto l (aevalE (rpending (L rst)).sto e')) ) := by
  obtain ⟨n, HN⟩ := H.toN
  exact step_sound cspec aspec opspec hΓ n hcs hlit hvalidS HN hα

/-- The top-level instance: soundness of the whole program `s₀` against any
    valid labeling, starting from the bottom state (matching `SA`'s old
    convention that the top-level analysis begins at `AHeap.bot`/`ASto.bot`/
    `AReg.bot`, and the concrete side begins from any concrete configuration
    at all — `α`-relatedness to `⊥` says nothing, so `Heap.Alpha`/`Sto.Alpha`/
    `Reg.Alpha` against the empty heap/store/register are the "no constraint
    yet" starting point, exactly as `AlphaFn.Lits` alone was sufficient to
    start the old `soundness_top`). -/
theorem sound_top [Concrete] [Abstract] (cspec : ConcreteSpec) (aspec : AbstractSpec)
    (opspec : OpSemSound) {Γ : Env} {s₀ : Stmt} {L : Labeling}
    (hΓ : EnvSpec Γ) (hvalid : Labeling.Valid Γ s₀ L)
    {c : Conf} {r : Res} {α : AlphaFn} (hlit : α.Lits)
    (H : BigStep Γ c s₀ r) (hα : AConf.Alpha α c (L (.entry []))) :
    ( (∃ x xpending, AExit Γ [] (.entry []) id s₀ x xpending ∧ r.out = .cont ∧
         ∃ α', α' ≥α α ∧ α'.Lits ∧
           AConf.Alpha α' ⟨r.heap, r.sto, r.reg⟩ (xpending (L x)))
    ∨ (∃ rst rpending e' l, ARet Γ [] (.entry []) id s₀ rst rpending e' ∧ r.out = .ret l ∧
         ∃ α', α' ≥α α ∧ α'.Lits ∧
           AConf.Alpha α' ⟨r.heap, r.sto, r.reg⟩ (rpending (L rst)) ∧
           α'.MapsInto l (aevalE (rpending (L rst)).sto e')) ) :=
  sound cspec aspec opspec hΓ CallString.WF.nil hlit hvalid.1 H (by simpa using hα)

/-!
## Totality (deferred, `sorry`)

`DESIGN_AND_PLAN.md` decision 12: aim for a Kleene-iteration witness
(`F(⊥), F(F(⊥)), ...` stabilising by the ascending chain condition), not
`main`'s `⊤`-shortcut. Stating the *goal* here so it is on record; the
construction itself is substantial additional work not attempted yet:

1. Restrict to the finite subtype of `AState` actually used by `(Γ, s₀)`
   (`AState.WF` in `CoreJsAutomatonSyntax.lean`, together with
   `CallString.length_le` and `EnvSpec.fin`) — needed before "iterate a
   whole-graph transformer" is even a well-founded notion, since `AState`
   itself is not finite without this restriction (`Idx`/`Fid` are `Nat`/
   `String`).
2. Define the whole-graph transformer `F : Labeling → Labeling`,
   `F L s = ⊔` over every edge landing at `s` of that edge's contribution
   computed from its own source's label under `L` — this needs `AEdge`
   turned into an enumerable (not just decidable-in-principle) fact per
   state, which `AEdge` as an inductive `Prop` does not provide for free.
3. Show `F` is monotone (routine, given every atomic effect and every
   `AHeap`/`ASto`/`AReg` operation used already is) and invoke the ascending
   chain condition (the finite-domain groundwork the old
   `CoreJsAbstractionSoundness.lean` already sketched — `AFinite`,
   `AscendingHeap` — ports over essentially unchanged) to get `n` with
   `F (F^n ⊥) ⊑ F^n ⊥`, i.e. a post-fixed point, i.e. (by construction of
   `F`) a valid labeling.
-/

theorem exists_valid_labeling [Concrete] [Abstract] (Γ : Env) (s₀ : Stmt)
    (hΓ : EnvSpec Γ) : ∃ L : Labeling, Labeling.Valid Γ s₀ L := by
  sorry

/-!
## Remaining work

Done: the statement of both soundness (`step_sound`/`sound`/`sound_top`) and
totality (`exists_valid_labeling`); the supporting relation infrastructure
(`CoreJsAutomatonRelation.lean`, including the heap-update lemmas
`Heap.Alpha.setObj`/`.setObjV`); `skip`, `assign`, `setTaint`, `setSink`,
`lookupS`, `lookupD`, `updateS`, `updateD`, `ret`, `seqRet`, `seqCont`,
`ifTrue`, `ifFalse` proved end to end.

Left, in the order a future session should attack them (each `sorry` above
has a comment sketching what it specifically needs):

1. `binOp`/`objLit` — need the `α`-extension step at a fresh allocation site
   (`ConcreteSpec.allocC_fresh`/`AbstractSpec.allocA_site`) and, for `binOp`
   only, the new `OpSemSound` cross-spec introduced at the top of this file.
   Genuinely harder than it looks: extending `α` safely requires knowing the
   fresh concrete location is *not already in `α`'s domain*, which needs an
   invariant this proof does not currently track (see the `binOp` `sorry`'s
   comment) — the old, pre-automaton proof hit exactly the same wall and
   also left it unstarted.
2. `whileDo` — needs induction on the number of concrete loop iterations
   (each iteration reuses the *same* `whileIn`/`AEdge.whileBody` fact,
   validated once by `Labeling.Valid`), not a direct structural mirroring —
   the one remaining case that is not just "assemble the pieces already
   built".
3. `callRet`/`callCont` — assembly of every piece already in place (see each
   `sorry`'s comment); the last case needed before `sound_top` is a complete,
   `sorry`-free soundness proof.
4. `exists_valid_labeling` — real additional construction (see the section
   above), independent of 1–3.
-/

end CoreJS
