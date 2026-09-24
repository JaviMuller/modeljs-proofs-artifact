/-
  # Core JavaScript — Soundness of the Automaton-Based Static Analysis

  The automaton counterpart of Theorem B15: every concrete execution is
  `α`-related, at whatever automaton state it structurally lands on, to a
  valid labeling's value there.

  ## Status

  **Incomplete**, in the sense the project's `sorry` policy describes (see
  `CLAUDE.md`): the statement, the supporting infrastructure, and 18 of 19
  statement-shape cases are proved (`skip`/`assign`/`setTaint`/`setSink`/
  `lookupS`/`lookupD`/`updateS`/`updateD`/`ret`/`seqRet`/`seqCont`/`ifTrue`/
  `ifFalse`/`callRet`/`callCont`/`whileDo`). Left as `sorry`: `binOp`/
  `objLit`, which need a new cross-spec relating `⊕` to `⊕̂` (introduced
  below) *and* an `α`-freshness invariant this proof does not track yet.
  `whileDo` needed a real design fix along the way, not just proof
  engineering — `PROBLEMS.md` decision 8 — since `Labeling.Valid` as first
  stated was not strong enough to make this theorem true for a `while` loop
  preceded by a non-trivial `pending`. No `axiom`s are used.

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
    (opspec : OpSemSound) {Γ : Env} {s₀ : Stmt} {L : Labeling} (hΓ : EnvSpec Γ)
    (hvalid : Labeling.Valid Γ s₀ L) :
    ∀ (n : Nat) {cs : CallString} {entry : AState} {pending : AConf → AConf}
      {s : Stmt} {c : Conf} {r : Res} {α : AlphaFn},
      CallString.WF cs →
      α.Lits →
      (∀ a b C ℓ, AEdge Γ cs entry pending s a b C ℓ → C L ⊑ L b) →
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
          hvalidS _ _ _ _ AEdge.lookupS
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
          hvalidS _ _ _ _ AEdge.lookupD
        exact Or.inl ⟨.action cs κ, id, .lookupD, rfl, α, .refl α, hlit, hcα.le hedge⟩
    | @ret _ h ρ δ e l he =>
        exact Or.inr ⟨entry, pending, e, l, .ret, rfl, α, .refl α, hlit, hα,
          eval_alpha hlit hα.2.1 he⟩
    | @seqRet nred h h' ρ ρ' δ δ' s1 s2 t l Hstep1 =>
        have hvalidS1 : ∀ a b C ℓ, AEdge Γ cs entry pending s1 a b C ℓ → C L ⊑ L b :=
          fun a b C ℓ he => hvalidS a b C ℓ (.seqLeft he)
        rcases IH nred (Nat.lt_succ_self _) hcs hlit hvalidS1 Hstep1 hα with
          ⟨_, _, _, hcont, _⟩ | ⟨rst, rpending, e', l', hARet1, hout, α', hext, hlit', hαres, hmaps⟩
        · exact absurd hcont (by simp)
        · exact Or.inr ⟨rst, rpending, e', l', .seqLeft hARet1, hout, α', hext, hlit', hαres, hmaps⟩
    | @seqCont nred h h' h'' ρ ρ' ρ'' δ δ' δ'' s1 s2 t1 t2 o Hstep1 Hstep2 =>
        have hvalidS1 : ∀ a b C ℓ, AEdge Γ cs entry pending s1 a b C ℓ → C L ⊑ L b :=
          fun a b C ℓ he => hvalidS a b C ℓ (.seqLeft he)
        rcases IH nred (Nat.lt_succ_self _) hcs hlit hvalidS1 Hstep1 hα with
          ⟨x, xpending, hAExit1, _, α1, hext1, hlit1, hα1⟩
          | ⟨_, _, _, _, hARet1, hout, _⟩
        · have hvalidS2 : ∀ a b C ℓ, AEdge Γ cs x xpending s2 a b C ℓ → C L ⊑ L b :=
            fun a b C ℓ he => hvalidS a b C ℓ (.seqRight hAExit1 he)
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
          hvalidS _ _ _ _ AEdge.updateS
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
          hvalidS _ _ _ _ AEdge.updateD
        exact Or.inl ⟨.action cs κ, id, .updateD, rfl, α, .refl α, hlit, hcα.le hedge⟩
    | @ifTrue nred _ ρ δ κ e s1 s2 l r' he hval Hstep1 =>
        have hedge_in : pending (L entry) ⊑ L (.ifThen cs κ) := hvalidS _ _ _ _ .ifThen
        have hα' : AConf.Alpha α _ (L (.ifThen cs κ)) := hα.le hedge_in
        have hvalidS1 : ∀ a b C ℓ, AEdge Γ cs (.ifThen cs κ) id s1 a b C ℓ → C L ⊑ L b :=
          fun a b C ℓ he => hvalidS a b C ℓ (.ifThenBody he)
        rcases IH nred (Nat.lt_succ_self _) hcs hlit hvalidS1 Hstep1 hα' with
            ⟨x, xpending, hAExit1, hout, α', hext, hlit', hαres⟩
          | ⟨rst, rpending, e', l', hARet1, hout, α', hext, hlit', hαres, hmaps⟩
        · have hedge_out : xpending (L x) ⊑ L (.ifEnd cs κ) :=
            hvalidS _ _ _ _ (.ifThenJoin hAExit1)
          exact Or.inl ⟨.ifEnd cs κ, id, .ifElse, hout, α', hext, hlit', hαres.le hedge_out⟩
        · exact Or.inr ⟨rst, rpending, e', l', .ifThen hARet1, hout, α', hext, hlit', hαres, hmaps⟩
    | @ifFalse nred _ ρ δ κ e s1 s2 l r' he hval Hstep2 =>
        have hedge_in : pending (L entry) ⊑ L (.ifElseB cs κ) := hvalidS _ _ _ _ .ifElseB
        have hα' : AConf.Alpha α _ (L (.ifElseB cs κ)) := hα.le hedge_in
        have hvalidS2 : ∀ a b C ℓ, AEdge Γ cs (.ifElseB cs κ) id s2 a b C ℓ → C L ⊑ L b :=
          fun a b C ℓ he => hvalidS a b C ℓ (.ifElseBBody he)
        rcases IH nred (Nat.lt_succ_self _) hcs hlit hvalidS2 Hstep2 hα' with
            ⟨x, xpending, hAExit2, hout, α', hext, hlit', hαres⟩
          | ⟨rst, rpending, e', l', hARet2, hout, α', hext, hlit', hαres, hmaps⟩
        · have hedge_out : xpending (L x) ⊑ L (.ifEnd cs κ) :=
            hvalidS _ _ _ _ (.ifElseBJoin hAExit2)
          exact Or.inl ⟨.ifEnd cs κ, id, .ifElse, hout, α', hext, hlit', hαres.le hedge_out⟩
        · exact Or.inr ⟨rst, rpending, e', l', .ifElseB hARet2, hout, α', hext, hlit', hαres, hmaps⟩
    | @whileDo nred h ρ δ κ e s r' Hstep =>
        -- `PROBLEMS.md` decision 8: this needed `AEdge.whileBack` replaced by
        -- `.whileBackIn`/`.whileBackOut` (fanning out again from an
        -- iteration's own exit, instead of looping back through `entry`'s
        -- possibly-stale `pending`). With that fix, every iteration is
        -- handled uniformly by a nested induction taking, as an explicit
        -- parameter, *which* fan-out edges apply at the current position —
        -- `AEdge.whileHeaderIn`/`.whileHeaderOut` for the first arrival at
        -- `entry`, `.whileBackIn`/`.whileBackOut` for every subsequent one at
        -- whatever `x` the previous iteration exited to.
        suffices hloop : ∀ (m : Nat), m ≤ nred → ∀ {pos : AState} {posPending : AConf → AConf}
            {c' : Conf} {r'' : Res} {αc : AlphaFn},
            AEdge Γ cs entry pending (.whileDo κ e s) pos (.whileIn cs κ)
              (fun L => posPending (L pos)) (fun _ => some .epsilon) →
            AEdge Γ cs entry pending (.whileDo κ e s) pos (.whileOut cs κ)
              (fun L => posPending (L pos)) (fun _ => some .epsilon) →
            BigStepN Γ m c' (.ifElse κ e (.seq s (.whileDo κ e s)) .skip) r'' →
            αc.Lits →
            AConf.Alpha αc c' (posPending (L pos)) →
            ( (∃ x xpending, AExit Γ cs entry pending (.whileDo κ e s) x xpending ∧
                 r''.out = .cont ∧ ∃ α', α' ≥α αc ∧ α'.Lits ∧
                   AConf.Alpha α' ⟨r''.heap, r''.sto, r''.reg⟩ (xpending (L x)))
            ∨ (∃ rst rpending e'' l, ARet Γ cs entry pending (.whileDo κ e s) rst rpending e'' ∧
                 r''.out = .ret l ∧ ∃ α', α' ≥α αc ∧ α'.Lits ∧
                   AConf.Alpha α' ⟨r''.heap, r''.sto, r''.reg⟩ (rpending (L rst)) ∧
                   α'.MapsInto l (aevalE (rpending (L rst)).sto e'')) ) by
          exact hloop nred (Nat.le_refl nred) AEdge.whileHeaderIn AEdge.whileHeaderOut Hstep
            hlit hα
        clear Hstep hα hlit
        intro m
        induction m using Nat.strongRecOn with
        | _ m IHloop =>
          intro hmn pos posPending c' r'' αc hedgeIn hedgeOut Hstep' hlit hα'
          cases Hstep' with
          | @ifFalse _ _ _ _ _ _ _ _ _ _ _ hval Hskip =>
              cases Hskip
              have hineq : posPending (L pos) ⊑ L (.whileOut cs κ) := hvalidS _ _ _ _ hedgeOut
              exact Or.inl ⟨.whileOut cs κ, id, .whileDo, rfl, αc, .refl αc, hlit, hα'.le hineq⟩
          | @ifTrue mm h1 ρ1 δ1 _ _ _ _ _ _ _ hval Hbody =>
              have hineqIn : posPending (L pos) ⊑ L (.whileIn cs κ) := hvalidS _ _ _ _ hedgeIn
              have hαIn : AConf.Alpha αc ⟨h1, ρ1, δ1⟩ (L (.whileIn cs κ)) := hα'.le hineqIn
              have hvalidBody : ∀ a b C ℓ, AEdge Γ cs (.whileIn cs κ) id s a b C ℓ → C L ⊑ L b :=
                fun a b C ℓ he => hvalidS a b C ℓ (.whileBody he)
              cases Hbody with
              | @seqRet m1 _ _ _ _ _ _ _ _ _ _ Hs1 =>
                  rcases IH m1 (by omega) hcs hlit hvalidBody Hs1 hαIn with
                      ⟨_, _, _, hcont, _⟩
                    | ⟨rst, rpending, e'', l, hARet_s, hout, α1, hext1, hlit1, hα1, hmaps1⟩
                  · exact absurd hcont (by simp)
                  · exact Or.inr ⟨rst, rpending, e'', l, .whileDo hARet_s, hout, α1, hext1,
                      hlit1, hα1, hmaps1⟩
              | @seqCont m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hs1 Hs2 =>
                  rcases IH m1 (by omega) hcs hlit hvalidBody Hs1 hαIn with
                      ⟨x, xpending, hAExit_s, hcont, α1, hext1, hlit1, hα1⟩
                    | ⟨_, _, _, _, _, hout, _⟩
                  · cases Hs2 with
                    | @whileDo m2 _ _ _ _ _ _ _ Hstep2 =>
                        rcases IHloop m2 (by omega) (by omega) (pos := x) (posPending := xpending)
                            (αc := α1) (.whileBackIn hAExit_s) (.whileBackOut hAExit_s) Hstep2
                            hlit1 hα1 with
                            ⟨y, ypending, hAExit_y, hout2, α2, hext2, hlit2, hα2⟩
                          | ⟨rst, rpending, e'', l, hARet_y, hout2, α2, hext2, hlit2, hα2, hmaps2⟩
                        · exact Or.inl ⟨y, ypending, hAExit_y, hout2, α2, hext1.trans hext2,
                            hlit2, hα2⟩
                        · exact Or.inr ⟨rst, rpending, e'', l, hARet_y, hout2, α2,
                            hext1.trans hext2, hlit2, hα2, hmaps2⟩
                  · exact absurd hout (by simp)
    | @callRet nred h h' ρ ρ' ρf' δ δ' x κ e es lf f params body ls l t he hlf hΓf hes
        harity Hstep hρ' =>
        subst hρ'
        -- (1) the call resolves to `f`: build `IsCandidate` from `hα`.
        have hval_e := eval_alpha hlit hα.2.1 he
        have hVmem := hα.1.valOf hval_e hlf
        have hargs := evals_alpha hlit hα.2.1 es hes
        have harity' : params.length = es.length := harity.trans (evalEs_length hes)
        have hΓparams : Γ.params f = params := by simp [Env.params, hΓf]
        have hcand : (pending (L entry)).Calls Γ e es.length f :=
          ⟨hVmem, by simp [hΓf], by rw [hΓparams, harity']⟩
        -- (2) relate the callee's initial store, and lift it to `L (entry cs_f)`.
        have hedge_entry := hvalidS _ _ _ _ (AEdge.callEntry hΓf harity')
        simp only [hcand, if_pos] at hedge_entry
        have hcα0 : AConf.Alpha α ⟨h, Sto.ofParams params ls, δ⟩
            { heap := (pending (L entry)).heap
              sto := ASto.ofParams params (aevalEs (pending (L entry)).sto es)
              reg := (pending (L entry)).reg } :=
          ⟨hα.1, sto_ofParams_alpha hargs params, hα.2.2⟩
        have hα_entry_f := hcα0.le hedge_entry
        -- (3) descend into the callee body, at a *fresh* `hvalidS` from `Valid`.
        have hcsf : CallString.WF (targetCallString cs κ f) := targetCallString_wf hcs κ f
        have hvalidBody : ∀ a b C ℓ, AEdge Γ (targetCallString cs κ f)
            (.entry (targetCallString cs κ f)) id body a b C ℓ → C L ⊑ L b :=
          fun a b C ℓ he => hvalid a b C ℓ (.body hΓf hcsf he)
        rcases IH nred (Nat.lt_succ_self _) hcsf hlit hvalidBody Hstep hα_entry_f with
            ⟨_, _, _, hcont, _⟩
          | ⟨rst, rpending, e', l', hARet, hout, α', hext, hlit', hαres, hmaps⟩
        · exact absurd hcont (by simp)
        · -- (4) build the `ret`-to-`cont` edge and the pass-through edge, and
          -- combine them componentwise: heap/register come from the callee
          -- (already transitively includes the caller's, since the callee's
          -- own initial heap/register *were* the caller's), the returned
          -- variable `x` from the `ret` edge, every other variable from the
          -- pass-through edge (decision 3 of `PROBLEMS.md`).
          have heql : l = l' := by injection hout
          subst heql
          have hedge_ret := hvalidS _ _ _ _ (AEdge.callRet hΓf harity' hARet)
          simp only [hcand, if_pos] at hedge_ret
          have hedge_pass := hvalidS _ _ _ _ (AEdge.callPassThrough (x := x) (κ := κ) (e := e) (es := es))
          refine Or.inl ⟨.cont cs κ, id, .call, rfl, α', hext, hlit', ?_, ?_, ?_⟩
          · exact hαres.1.le hedge_ret.1
          · intro y ly hy
            by_cases hxy : y = x
            · have hlyl : ly = l := by rw [hxy] at hy; simpa [Sto.upd] using hy.symm
              rw [hxy, hlyl]
              have hxineq : (aevalE (rpending (L rst)).sto e') ⊆ (L (.cont cs κ)).sto x := by
                simpa [ASto.upd] using hedge_ret.2.1 x
              exact hmaps.subset hxineq
            · have hy' : ρ y = some ly := by simpa [Sto.upd, hxy] using hy
              have hcaller := hα.2.1 y ly hy'
              have hpass : (pending (L entry)).sto y ⊆ (L (.cont cs κ)).sto y := by
                have := hedge_pass.2.1 y
                simpa [ASto.upd, hxy] using this
              exact (hcaller.subset hpass).mono hext
          · exact hαres.2.2.le hedge_ret.2.2
    | @callCont nred h h' ρ ρ' ρf' δ δ' x κ e es lf f params body ls t he hlf hΓf hes
        harity Hstep hρ' =>
        subst hρ'
        have hval_e := eval_alpha hlit hα.2.1 he
        have hVmem := hα.1.valOf hval_e hlf
        have hargs := evals_alpha hlit hα.2.1 es hes
        have harity' : params.length = es.length := harity.trans (evalEs_length hes)
        have hΓparams : Γ.params f = params := by simp [Env.params, hΓf]
        have hcand : (pending (L entry)).Calls Γ e es.length f :=
          ⟨hVmem, by simp [hΓf], by rw [hΓparams, harity']⟩
        have hedge_entry := hvalidS _ _ _ _ (AEdge.callEntry hΓf harity')
        simp only [hcand, if_pos] at hedge_entry
        have hcα0 : AConf.Alpha α ⟨h, Sto.ofParams params ls, δ⟩
            { heap := (pending (L entry)).heap
              sto := ASto.ofParams params (aevalEs (pending (L entry)).sto es)
              reg := (pending (L entry)).reg } :=
          ⟨hα.1, sto_ofParams_alpha hargs params, hα.2.2⟩
        have hα_entry_f := hcα0.le hedge_entry
        have hcsf : CallString.WF (targetCallString cs κ f) := targetCallString_wf hcs κ f
        have hvalidBody : ∀ a b C ℓ, AEdge Γ (targetCallString cs κ f)
            (.entry (targetCallString cs κ f)) id body a b C ℓ → C L ⊑ L b :=
          fun a b C ℓ he => hvalid a b C ℓ (.body hΓf hcsf he)
        rcases IH nred (Nat.lt_succ_self _) hcsf hlit hvalidBody Hstep hα_entry_f with
            ⟨y, ypending, hAExit, hout, α', hext, hlit', hαres⟩
          | ⟨_, _, _, _, _, hout, _⟩
        · have hedge_ret := hvalidS _ _ _ _ (AEdge.callImplicitRet hΓf harity' hAExit)
          simp only [hcand, if_pos] at hedge_ret
          have hedge_pass := hvalidS _ _ _ _ (AEdge.callPassThrough (x := x) (κ := κ) (e := e) (es := es))
          refine Or.inl ⟨.cont cs κ, id, .call, rfl, α', hext, hlit', ?_, ?_, ?_⟩
          · exact hαres.1.le hedge_ret.1
          · intro z lz hz
            by_cases hxz : z = x
            · have hlzl : lz = Concrete.litLoc .undef := by
                rw [hxz] at hz; simpa [Sto.upd] using hz.symm
              rw [hxz, hlzl]
              have hxineq : ({Abstract.litLocA .undef} : ALocSet) ⊆ (L (.cont cs κ)).sto x := by
                simpa [ASto.upd] using hedge_ret.2.1 x
              have : α.MapsInto (Concrete.litLoc .undef) ({Abstract.litLocA .undef} : ALocSet) :=
                ⟨Abstract.litLocA .undef, hlit .undef, rfl⟩
              exact (this.subset hxineq).mono hext
            · have hz' : ρ z = some lz := by simpa [Sto.upd, hxz] using hz
              have hcaller := hα.2.1 z lz hz'
              have hpass : (pending (L entry)).sto z ⊆ (L (.cont cs κ)).sto z := by
                have := hedge_pass.2.1 z
                simpa [ASto.upd, hxz] using this
              exact (hcaller.subset hpass).mono hext
          · exact hαres.2.2.le hedge_ret.2.2
        · exact absurd hout (by simp)

/-- Corollary form, height existentially quantified away — the automaton
    counterpart of the old `soundness`/`soundness_top`. Immediate from
    `step_sound` via `BigStep.toN`, exactly as before. -/
theorem sound [Concrete] [Abstract] (cspec : ConcreteSpec) (aspec : AbstractSpec)
    (opspec : OpSemSound) {Γ : Env} {s₀ : Stmt} {L : Labeling} (hΓ : EnvSpec Γ)
    (hvalid : Labeling.Valid Γ s₀ L)
    {cs : CallString} {entry : AState} {pending : AConf → AConf} {s : Stmt}
    {c : Conf} {r : Res} {α : AlphaFn}
    (hcs : CallString.WF cs) (hlit : α.Lits)
    (hvalidS : ∀ a b C ℓ, AEdge Γ cs entry pending s a b C ℓ → C L ⊑ L b)
    (H : BigStep Γ c s r) (hα : AConf.Alpha α c (pending (L entry))) :
    ( (∃ x xpending, AExit Γ cs entry pending s x xpending ∧ r.out = .cont ∧
         ∃ α', α' ≥α α ∧ α'.Lits ∧
           AConf.Alpha α' ⟨r.heap, r.sto, r.reg⟩ (xpending (L x)))
    ∨ (∃ rst rpending e' l, ARet Γ cs entry pending s rst rpending e' ∧ r.out = .ret l ∧
         ∃ α', α' ≥α α ∧ α'.Lits ∧
           AConf.Alpha α' ⟨r.heap, r.sto, r.reg⟩ (rpending (L rst)) ∧
           α'.MapsInto l (aevalE (rpending (L rst)).sto e')) ) := by
  obtain ⟨n, HN⟩ := H.toN
  exact step_sound cspec aspec opspec hΓ hvalid n hcs hlit hvalidS HN hα

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
  sound cspec aspec opspec hΓ hvalid CallString.WF.nil hlit (fun a b C ℓ he => hvalid a b C ℓ (.top he)) H (by simpa using hα)

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
`ifTrue`, `ifFalse`, `callRet`, `callCont`, `whileDo` proved end to end —
**18 of the 19** statement-shape cases.

`whileDo` needed `PROBLEMS.md` decision 8 (`AEdge.whileBack` replaced by
`.whileBackIn`/`.whileBackOut`, fanning out again from an iteration's own
exit instead of looping back through `entry`'s possibly-stale `pending`) and
a nested strong induction (`hloop`/`IHloop`, local to that case) over the
number of concrete loop iterations, taking as an explicit parameter which
pair of fan-out edges applies at the current position — the first
iteration's from `entry`, every subsequent one's from the previous
iteration's own exit.

Left:

1. `binOp`/`objLit` — need the `α`-extension step at a fresh allocation site
   (`ConcreteSpec.allocC_fresh`/`AbstractSpec.allocA_site`) and, for `binOp`
   only, the new `OpSemSound` cross-spec introduced at the top of this file.
   Genuinely harder than it looks: extending `α` safely requires knowing the
   fresh concrete location is *not already in `α`'s domain*, which needs an
   invariant this proof does not currently track (see the `binOp` `sorry`'s
   comment) — the old, pre-automaton proof hit exactly the same wall and
   also left it unstarted.
2. `exists_valid_labeling` — real additional construction (see the section
   above), independent of 1. The one thing worth double-checking once it is
   attempted: that a labeling built via Kleene iteration from `⊥` actually
   satisfies the *new* `whileBackIn`/`.whileBackOut` edges' inequalities
   (there is no reason to expect it wouldn't — they are ordinary edges into
   `whileIn`/`whileOut` like any other, just sourced at whatever state a
   loop body's own exit turned out to be — but it was decision 8's fix, so
   worth confirming explicitly rather than assuming).
-/

end CoreJS
