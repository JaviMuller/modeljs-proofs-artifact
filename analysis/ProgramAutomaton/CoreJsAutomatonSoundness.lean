/-
  # Core JavaScript — Soundness of the Automaton-Based Static Analysis

  Every concrete run is matched by the automaton, relative to any valid
  labeling `L`:

  * its final heap, store and register are `α`-related to `L`'s label at the
    automaton state the run structurally ends at (an exit of the statement if
    it continued, a `ret` if it returned);
  * its trace is `α`-related, action by action and in order, to the trace of
    a walk (`AWalk`) through the labeled automaton, from the state the
    statement was entered at to that final state.

  `step_sound` proves this for a run of any statement processed at any
  position of the graph, by strong induction on the height of the concrete
  derivation: a `while` loop's case needs the hypothesis for the body's and
  the next iteration's derivations, which sit several levels below the
  loop's own. `sound` drops the height, and
  `sound_top` specialises to a whole program run from its initial
  configuration against an `AnalysisResult`, and `sound_least` to the least
  one, which always exists (`CoreJsAutomatonTotality.lean`).

  The labeling is a single flat predicate over the whole graph
  (`Labeling.Valid`), so a recursive call needs no assume/guarantee argument:
  its callee's entry label is simply looked up. What the proof threads
  instead is `hsub`, "every edge of the statement being processed is an edge
  of the graph": recursing into a substatement wraps the relevant `AEdge`
  constructor around the substatement's edges, and recursing into a callee
  starts afresh from `AGraph.body`.

  Besides `α`-relatedness, three facts about the current memory (heap and
  register values) are carried along the run: it is finite (so allocation
  returns a fresh location), `α` is allocation-safe for it (so `α` can be
  extended at that location), and function values sit only at their literal
  locations (so a call's callee location is the one the abstract
  `call`/`ret` labels name).
-/

import ProgramAutomaton.CoreJsAutomatonRelation
import ProgramAutomaton.CoreJsAutomatonTotality

namespace CoreJS

/-! ## Small helper facts -/

theorem evalEs_length [Concrete] :
    ∀ {ρ : Sto} {es : List Expr} {ls : List Loc}, ⟦es⟧ρ = some ls →
      ls.length = es.length
  | _, [], _, he => by simp only [evalEs, Option.some.injEq] at he; subst he; rfl
  | ρ, e :: es, ls, he => by
      rw [evalEs] at he
      cases hE : ⟦e⟧ρ with
      | none => rw [hE] at he; simp at he
      | some l =>
          cases hEs : ⟦es⟧ρ with
          | none => rw [hE, hEs] at he; simp at he
          | some ls' =>
              rw [hE, hEs] at he
              have hx : l :: ls' = ls := by injection he
              subst hx
              simp only [List.length_cons, evalEs_length hEs]

theorem aevalEs_length [Abstract] : ∀ (ρ : ASto) (es : List Expr),
    (⟦es⟧ρ).length = es.length
  | _, []      => rfl
  | ρ, e :: es => by simp [aevalEs, aevalEs_length ρ es]

/-- Store update (`sto_upd_alpha`), lifted to whole parameter lists: the
    callee's freshly built store relates to the abstract store built the same way, given the
    argument lists are related componentwise. -/
theorem sto_ofParams_alpha {α : AlphaFn} :
    ∀ {ls : List Loc} {Ls : List ALocSet}, ls ∼α Ls →
      ∀ params : List Var, Sto.ofParams params ls ∼α ASto.ofParams params Ls
  | [], [], _, params => by
      cases params <;> (intro y l hy; exact absurd hy (by simp [Sto.ofParams, Sto.empty]))
  | l :: ls, L :: Ls, h, params => by
      cases params with
      | nil => intro y l' hy; exact absurd hy (by simp [Sto.ofParams, Sto.empty])
      | cons x xs =>
          show (Sto.ofParams xs ls).upd x l ∼α (ASto.ofParams xs Ls).upd x L
          exact sto_upd_alpha (sto_ofParams_alpha h.2 xs) h.1
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

/-! ## Main soundness lemma -/

-- The call edges' contributions and labels branch on `AConf.Calls` with the
-- classical decidability instance `CoreJsAutomatonSemantics.lean` uses; the
-- same instance is needed here to state their unfolded forms.
attribute [local instance] Classical.propDecidable

/-- What `step_sound` concludes about a run of `s`, processed from
    `(cs, entry, pending)`, that started `α`-related to `pending (L entry)` and
    ended in `r`: either `s` continued, to one of its exits `x`, or it
    returned, at one of its `ret`s `rst`. Either way `α` extends to an `α'`,
    still allocation-safe for the final memory, relating the final configuration
    to that state's label, and a walk from `start` reaches that state with a
    trace `α'`-related to the run's. -/
def SoundRun [Concrete] [Abstract] (Γ : Env) (s₀ : Stmt) (L : Labeling) (cs : CallString)
    (entry : AState) (pending : AConf → AConf) (s : Stmt) (start : AState) (α : AlphaFn)
    (r : Res) : Prop :=
  (∃ x xpending, AExit Γ cs entry pending s x xpending ∧ r.out = .cont ∧
     ∃ α', α' ≥α α ∧ α'.AllocSafe r.heap r.reg ∧
       ⟨r.heap, r.sto, r.reg⟩ ∼α' xpending (L x) ∧
       ∃ tₐ, AWalk Γ s₀ L start x tₐ ∧ r.trc ∼α' tₐ) ∨
  (∃ rst rpending e l, ARet Γ cs entry pending s rst rpending e ∧ r.out = .ret l ∧
     ∃ α', α' ≥α α ∧ α'.AllocSafe r.heap r.reg ∧
       ⟨r.heap, r.sto, r.reg⟩ ∼α' rpending (L rst) ∧
       l ∼α' ⟦e⟧(rpending (L rst)).sto ∧
       ∃ tₐ, AWalk Γ s₀ L start rst tₐ ∧ r.trc ∼α' tₐ)

theorem step_sound [Concrete] [Abstract] (cspec : ConcreteSpec) (xspec : CrossSpec)
    {Γ : Env} {s₀ : Stmt} {L : Labeling} (hvalid : Labeling.Valid Γ s₀ L) :
    ∀ (n : Nat) {cs : CallString} {entry : AState} {pending : AConf → AConf}
      {s : Stmt} {c : Conf} {r : Res} {α : AlphaFn},
      CallString.WF cs → α.Lits → α.AllocSafe c.heap c.reg → c.heap.Finite c.reg →
        c.reg.FidCanon →
      (∀ a b C ℓ, AEdge Γ cs entry pending s a b C ℓ → AGraph Γ s₀ a b C ℓ) →
      Γ ⊢ ⟨c, s⟩ ⇓c[n] r →
      c ∼α pending (L entry) →
      SoundRun Γ s₀ L cs entry pending s entry α r := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
    intro cs entry pending s c r α hcs hlit hsafe hfin hfid hsub H hα
    have hle : ∀ {a b C ℓ}, AEdge Γ cs entry pending s a b C ℓ → C L ⊑ L b :=
      fun he => hvalid _ _ _ _ (hsub _ _ _ _ he)
    -- The two call edges' labels, once the candidate check is known to hold.
    have hℓ : ∀ {P : Prop} (A : AAct) (B : Option AAct), P →
        (if P then some A else B) = some A := fun _ _ hP => if_pos hP
    cases H with
    | skip =>
        exact Or.inl ⟨entry, pending, .skip, rfl, α, .refl α, hsafe, hα, [], .nil, trivial⟩
    | @assign _ h ρ ρ' δ x e l he hρ' =>
        subst hρ'
        refine Or.inl ⟨entry, AConf.doAssign x e ∘ pending, .assign, rfl, α, .refl α, hsafe, ?_,
          [], .nil, trivial⟩
        exact ⟨hα.1, sto_upd_alpha hα.2.1 (eval_alpha hlit hα.2.1 he), hα.2.2⟩
    | @setTaint _ h ρ δ δ' e l he hδ' =>
        subst hδ'
        refine Or.inl ⟨entry, AConf.doSetTaint e ∘ pending, .setTaint, rfl, α, .refl α, hsafe, ?_,
          [], .nil, trivial⟩
        have hval := eval_alpha hlit hα.2.1 he
        refine ⟨hα.1, hα.2.1, hα.2.2.1, hα.2.2.2.1, ?_, hα.2.2.2.2.2⟩
        intro y hy
        rcases hy with hy | hy
        · subst hy; exact hval.subset (fun _ h => Or.inl h)
        · exact (hα.2.2.2.2.1 y hy).subset (fun _ h => Or.inr h)
    | @setSink _ h ρ δ δ' e l he hδ' =>
        subst hδ'
        refine Or.inl ⟨entry, AConf.doSetSink e ∘ pending, .setSink, rfl, α, .refl α, hsafe, ?_,
          [], .nil, trivial⟩
        have hval := eval_alpha hlit hα.2.1 he
        refine ⟨hα.1, hα.2.1, hα.2.2.1, hα.2.2.2.1, hα.2.2.2.2.1, ?_⟩
        intro y hy
        rcases hy with hy | hy
        · subst hy; exact hval.subset (fun _ h => Or.inl h)
        · exact (hα.2.2.2.2.2 y hy).subset (fun _ h => Or.inr h)
    | @lookupS _ h ρ ρ' δ x κ e p l₁ l₂ he hobj hρ' =>
        subst hρ'
        have hval := eval_alpha hlit hα.2.1 he
        have hmaps : α.MapsInto l₂
            ((pending (L entry)).heap.lookupS (⟦e⟧(pending (L entry)).sto) p) :=
          (hα.1.objOf hval hobj).subset (fun _ h => Or.inl (Or.inl h))
        have hcα : ⟨h, ρ.upd x l₂, δ⟩ ∼α AConf.doLookupS x e p (pending (L entry)) :=
          ⟨hα.1, sto_upd_alpha hα.2.1 hmaps, hα.2.2⟩
        exact Or.inl ⟨.action cs κ, id, .lookupS, rfl, α, .refl α, hsafe, hcα.le (hle .lookupS),
          _, AWalk.single (hsub _ _ _ _ .lookupS) rfl,
          ⟨⟨hmaps, hval, _, hlit _, rfl⟩, trivial⟩⟩
    | @lookupSProto _ h ρ ρ' δ x κ e p l₁ l₂ he _ _ hobj hρ' =>
        -- the own property is missing: read `Object.prototype`'s
        subst hρ'
        have hval := eval_alpha hlit hα.2.1 he
        have hmaps : α.MapsInto l₂
            ((pending (L entry)).heap.lookupS (⟦e⟧(pending (L entry)).sto) p) :=
          (hα.1.objOf (L := {Abstract.litLocA .proto}) ⟨_, hlit .proto, rfl⟩ hobj).subset
            (fun _ h => Or.inl (Or.inr h))
        have hcα : ⟨h, ρ.upd x l₂, δ⟩ ∼α AConf.doLookupS x e p (pending (L entry)) :=
          ⟨hα.1, sto_upd_alpha hα.2.1 hmaps, hα.2.2⟩
        exact Or.inl ⟨.action cs κ, id, .lookupS, rfl, α, .refl α, hsafe, hcα.le (hle .lookupS),
          _, AWalk.single (hsub _ _ _ _ .lookupS) rfl,
          ⟨⟨hmaps, hval, _, hlit _, rfl⟩, trivial⟩⟩
    | @lookupSMissing _ h ρ ρ' δ x κ e p l₁ he _ _ _ hρ' =>
        -- missing on the object and on `Object.prototype`: `undefined`
        subst hρ'
        have hval := eval_alpha hlit hα.2.1 he
        have hmaps : α.MapsInto (Concrete.litLoc .undef)
            ((pending (L entry)).heap.lookupS (⟦e⟧(pending (L entry)).sto) p) :=
          ⟨_, hlit .undef, Or.inr rfl⟩
        have hcα : ⟨h, ρ.upd x (Concrete.litLoc .undef), δ⟩ ∼α
            AConf.doLookupS x e p (pending (L entry)) :=
          ⟨hα.1, sto_upd_alpha hα.2.1 hmaps, hα.2.2⟩
        exact Or.inl ⟨.action cs κ, id, .lookupS, rfl, α, .refl α, hsafe, hcα.le (hle .lookupS),
          _, AWalk.single (hsub _ _ _ _ .lookupS) rfl,
          ⟨⟨hmaps, hval, _, hlit _, rfl⟩, trivial⟩⟩
    | @lookupD _ h ρ ρ' δ x κ e₁ e₂ l₁ l₂ l₃ p v he1 he2 hstr hkey hobj hρ' =>
        subst hρ'
        have hval1 := eval_alpha hlit hα.2.1 he1
        have hval2 := eval_alpha hlit hα.2.1 he2
        have hmaps : α.MapsInto l₃
            ((pending (L entry)).heap.lookupD (⟦e₁⟧(pending (L entry)).sto)
              ((pending (L entry)).reg.valOf (⟦e₂⟧(pending (L entry)).sto))) :=
          (hα.1.objOfV hval1 ⟨v, hα.2.2.valOf hval2 hstr, hkey⟩ hobj).subset
            (fun _ h => Or.inl (Or.inl h))
        have hcα : ⟨h, ρ.upd x l₃, δ⟩ ∼α AConf.doLookupD x e₁ e₂ (pending (L entry)) :=
          ⟨hα.1, sto_upd_alpha hα.2.1 hmaps, hα.2.2⟩
        exact Or.inl ⟨.action cs κ, id, .lookupD, rfl, α, .refl α, hsafe, hcα.le (hle .lookupD),
          _, AWalk.single (hsub _ _ _ _ .lookupD) rfl, ⟨⟨hmaps, hval1, hval2⟩, trivial⟩⟩
    | @lookupDProto _ h ρ ρ' δ x κ e₁ e₂ l₁ l₂ l₃ p v he1 he2 _ hstr hkey _ hobj hρ' =>
        subst hρ'
        have hval1 := eval_alpha hlit hα.2.1 he1
        have hval2 := eval_alpha hlit hα.2.1 he2
        have hmaps : α.MapsInto l₃
            ((pending (L entry)).heap.lookupD (⟦e₁⟧(pending (L entry)).sto)
              ((pending (L entry)).reg.valOf (⟦e₂⟧(pending (L entry)).sto))) :=
          (hα.1.objOfV (L := {Abstract.litLocA .proto}) ⟨_, hlit .proto, rfl⟩
              ⟨v, hα.2.2.valOf hval2 hstr, hkey⟩ hobj).subset
            (fun _ h => Or.inl (Or.inr h))
        have hcα : ⟨h, ρ.upd x l₃, δ⟩ ∼α AConf.doLookupD x e₁ e₂ (pending (L entry)) :=
          ⟨hα.1, sto_upd_alpha hα.2.1 hmaps, hα.2.2⟩
        exact Or.inl ⟨.action cs κ, id, .lookupD, rfl, α, .refl α, hsafe, hcα.le (hle .lookupD),
          _, AWalk.single (hsub _ _ _ _ .lookupD) rfl, ⟨⟨hmaps, hval1, hval2⟩, trivial⟩⟩
    | @lookupDMissing _ h ρ ρ' δ x κ e₁ e₂ l₁ l₂ p v he1 he2 _ _ _ _ _ hρ' =>
        subst hρ'
        have hval1 := eval_alpha hlit hα.2.1 he1
        have hval2 := eval_alpha hlit hα.2.1 he2
        have hmaps : α.MapsInto (Concrete.litLoc .undef)
            ((pending (L entry)).heap.lookupD (⟦e₁⟧(pending (L entry)).sto)
              ((pending (L entry)).reg.valOf (⟦e₂⟧(pending (L entry)).sto))) :=
          ⟨_, hlit .undef, Or.inr rfl⟩
        have hcα : ⟨h, ρ.upd x (Concrete.litLoc .undef), δ⟩ ∼α
            AConf.doLookupD x e₁ e₂ (pending (L entry)) :=
          ⟨hα.1, sto_upd_alpha hα.2.1 hmaps, hα.2.2⟩
        exact Or.inl ⟨.action cs κ, id, .lookupD, rfl, α, .refl α, hsafe, hcα.le (hle .lookupD),
          _, AWalk.single (hsub _ _ _ _ .lookupD) rfl, ⟨⟨hmaps, hval1, hval2⟩, trivial⟩⟩
    | @updateS _ h h' ρ δ κ e1 p e2 l1 l2 he1 he2 hh' =>
        subst hh'
        have hval1 := eval_alpha hlit hα.2.1 he1
        have hval2 := eval_alpha hlit hα.2.1 he2
        have hcα : AConf.Alpha α ⟨h.setObj l1 p l2, ρ, δ⟩
            (AConf.doUpdateS e1 p e2 (pending (L entry))) :=
          ⟨hα.1.setObj hval1 hval2, hα.2.1, hα.2.2⟩
        exact Or.inl ⟨.action cs κ, id, .updateS, rfl, α, .refl α,
          hsafe.mono_heap (fun _ hd => hd.setObj _ _ _), hcα.le (hle .updateS),
          _, AWalk.single (hsub _ _ _ _ .updateS) rfl,
          ⟨⟨hval1, ⟨_, hlit _, rfl⟩, hval2⟩, trivial⟩⟩
    | @updateD _ h h' ρ δ κ e1 e2 e3 l1 l2 l3 p v he1 he2 he3 hstr hkey hh' =>
        subst hh'
        have hval1 := eval_alpha hlit hα.2.1 he1
        have hval2 := eval_alpha hlit hα.2.1 he2
        have hval3 := eval_alpha hlit hα.2.1 he3
        have hVmem : VSet.HasKey _ p := ⟨v, hα.2.2.valOf hval2 hstr, hkey⟩
        have hcα : AConf.Alpha α ⟨h.setObj l1 p l3, ρ, δ⟩
            (AConf.doUpdateD e1 e2 e3 (pending (L entry))) :=
          ⟨hα.1.setObjV hval1 hVmem hval3, hα.2.1, hα.2.2⟩
        exact Or.inl ⟨.action cs κ, id, .updateD, rfl, α, .refl α,
          hsafe.mono_heap (fun _ hd => hd.setObj _ _ _), hcα.le (hle .updateD),
          _, AWalk.single (hsub _ _ _ _ .updateD) rfl, ⟨⟨hval1, hval2, hval3⟩, trivial⟩⟩
    | @binOp _ h ρ ρ' δ δ' x κ op e₁ e₂ l₁ l₂ v₁ v₂ l v d he1 he2 hv1 hv2 hl hv hρ' hd hδ' =>
        subst hl hv hρ' hd hδ'
        -- `α` is extended at the fresh location, to the abstract location the
        -- abstract `binOp` writes at.
        obtain ⟨α', hext, hαl, hsafe'⟩ :=
          hsafe.extend cspec hfin κ (pending (L entry)).heap (pending (L entry)).reg
        have hval1 := eval_alpha hlit hα.2.1 he1
        have hval2 := eval_alpha hlit hα.2.1 he2
        have hV := xspec.opSem_sound op v₁ v₂ _ _ (hα.2.2.valOf hval1 hv1) (hα.2.2.valOf hval2 hv2)
        refine Or.inl ⟨entry, AConf.doBinOp x κ op e₁ e₂ ∘ pending, .binOp, rfl, α', hext,
          hsafe' _ _ (fun _ hd => (hd.setVal _ _).congr rfl)
            ((Heap.defined_setVal_self _ _ _ _).congr rfl),
          ⟨?_, ?_, ?_⟩, [], .nil, trivial⟩
        · exact hα.1.mono hext
        · exact sto_upd_alpha (hα.2.1.mono hext) ⟨_, hαl, rfl⟩
        · exact ((hα.2.2.mono hext).setVal hαl hV).binOp hαl (hval1.mono hext) (hval2.mono hext)
    | @objLit _ h h' ρ ρ' δ δ' x κ fs ls l hes hl hh' hρ' hδ' =>
        subst hl hh' hρ' hδ'
        obtain ⟨α', hext, hαl, hsafe'⟩ :=
          hsafe.extend cspec hfin κ (pending (L entry)).heap (pending (L entry)).reg
        have hargs := (evals_alpha hlit hα.2.1 _ hes).mono hext
        refine Or.inl ⟨entry, AConf.doObjLit x κ fs ∘ pending, .objLit, rfl, α', hext,
          hsafe' _ _ (fun _ hd => ((hd.setObjs _ _).setVal _ _).congr rfl)
            ((Heap.defined_setVal_self _ _ _ _).congr rfl), ⟨?_, ?_, ?_⟩, [], .nil, trivial⟩
        · -- the object's `__proto__`, then its own fields
          exact Heap.Alpha.setObjs hαl (fs.map Prod.fst)
            (Heap.Alpha.setObj (p := "__proto__")
              (L1 := {Abstract.allocA (pending (L entry)).heap (pending (L entry)).reg κ})
              (L2 := {Abstract.litLocA .proto}) (hα.1.mono hext) ⟨_, hαl, rfl⟩
              ⟨_, hlit.mono hext .proto, rfl⟩) hargs
        · exact sto_upd_alpha (hα.2.1.mono hext) ⟨_, hαl, rfl⟩
        · -- the object's own reference value at its location
          exact ((hα.2.2.mono hext).setVal (V := VSet.refs) hαl
            ⟨Concrete.allocC h δ κ, rfl⟩).setDep_empty
    | @ret _ h ρ δ e l he =>
        exact Or.inr ⟨entry, pending, e, l, .ret, rfl, α, .refl α, hsafe, hα,
          eval_alpha hlit hα.2.1 he, [], .nil, trivial⟩
    | @seqRet nred h h' ρ ρ' δ δ' s1 s2 t l Hstep1 =>
        rcases IH nred (Nat.lt_succ_self _) hcs hlit hsafe hfin hfid
            (fun a b C ℓ he => hsub a b C ℓ (.seqLeft he)) Hstep1 hα with
          ⟨_, _, _, hcont, _⟩ | ⟨rst, rpending, e', l', hARet1, hout, rest⟩
        · exact absurd hcont (by simp)
        · exact Or.inr ⟨rst, rpending, e', l', .seqLeft hARet1, hout, rest⟩
    | @seqCont nred h h' h'' ρ ρ' ρ'' δ δ' δ'' s1 s2 t1 t2 o Hstep1 Hstep2 =>
        have hfin' := BigStep.finite Hstep1.toBigStep hfin
        have hfid' := BigStep.fidCanon cspec.opSem_fid Hstep1.toBigStep hfid
        rcases IH nred (Nat.lt_succ_self _) hcs hlit hsafe hfin hfid
            (fun a b C ℓ he => hsub a b C ℓ (.seqLeft he)) Hstep1 hα with
          ⟨x, xpending, hAExit1, _, α1, hext1, hsafe1, hα1, tₐ₁, w1, tr1⟩
          | ⟨_, _, _, _, _, hout, _⟩
        · rcases IH nred (Nat.lt_succ_self _) hcs (hlit.mono hext1) hsafe1 hfin' hfid'
              (fun a b C ℓ he => hsub a b C ℓ (.seqRight hAExit1 he)) Hstep2 hα1 with
            ⟨y, ypending, hAExit2, hout2, α2, hext2, hsafe2, hα2, tₐ₂, w2, tr2⟩
            | ⟨rst, rpending, e', l, hARet2, hout2, α2, hext2, hsafe2, hα2, hmaps, tₐ₂, w2, tr2⟩
          · exact Or.inl ⟨y, ypending, .seq hAExit1 hAExit2, hout2, α2, hext1.trans hext2,
              hsafe2, hα2, tₐ₁ ++ tₐ₂, w1.append w2, (tr1.mono hext2).seq tr2⟩
          · exact Or.inr ⟨rst, rpending, e', l, .seqRight hAExit1 hARet2, hout2, α2,
              hext1.trans hext2, hsafe2, hα2, hmaps, tₐ₁ ++ tₐ₂, w1.append w2,
              (tr1.mono hext2).seq tr2⟩
        · exact absurd hout (by simp)
    | @ifTrue nred _ ρ δ κ e s1 s2 l r' he hval Hstep1 =>
        rcases IH nred (Nat.lt_succ_self _) hcs hlit hsafe hfin hfid
            (fun a b C ℓ he => hsub a b C ℓ (.ifThenBody he)) Hstep1 (hα.le (hle .ifThen)) with
          ⟨x, xpending, hAExit1, hout, α', hext, hsafe', hαres, tₐ, w, tr⟩
          | ⟨rst, rpending, e', l', hARet1, hout, α', hext, hsafe', hαres, hmaps, tₐ, w, tr⟩
        · exact Or.inl ⟨.ifEnd cs κ, id, .ifElse, hout, α', hext, hsafe',
            hαres.le (hle (.ifThenJoin hAExit1)), tₐ,
            (AWalk.step (hsub _ _ _ _ .ifThen) rfl w).snoc_eps
              (hsub _ _ _ _ (.ifThenJoin hAExit1)) rfl, tr⟩
        · exact Or.inr ⟨rst, rpending, e', l', .ifThen hARet1, hout, α', hext, hsafe', hαres,
            hmaps, tₐ, AWalk.step (hsub _ _ _ _ .ifThen) rfl w, tr⟩
    | @ifFalse nred _ ρ δ κ e s1 s2 l r' he hval Hstep2 =>
        rcases IH nred (Nat.lt_succ_self _) hcs hlit hsafe hfin hfid
            (fun a b C ℓ he => hsub a b C ℓ (.ifElseBBody he)) Hstep2 (hα.le (hle .ifElseB)) with
          ⟨x, xpending, hAExit2, hout, α', hext, hsafe', hαres, tₐ, w, tr⟩
          | ⟨rst, rpending, e', l', hARet2, hout, α', hext, hsafe', hαres, hmaps, tₐ, w, tr⟩
        · exact Or.inl ⟨.ifEnd cs κ, id, .ifElse, hout, α', hext, hsafe',
            hαres.le (hle (.ifElseBJoin hAExit2)), tₐ,
            (AWalk.step (hsub _ _ _ _ .ifElseB) rfl w).snoc_eps
              (hsub _ _ _ _ (.ifElseBJoin hAExit2)) rfl, tr⟩
        · exact Or.inr ⟨rst, rpending, e', l', .ifElseB hARet2, hout, α', hext, hsafe', hαres,
            hmaps, tₐ, AWalk.step (hsub _ _ _ _ .ifElseB) rfl w, tr⟩
    | @whileDo nred h ρ δ κ e s r' Hstep =>
        -- A nested induction over the iterations, taking as a parameter the
        -- position `pos` the current iteration's guard is checked from and
        -- the pair of fan-out edges leaving it: `whileHeaderIn`/`Out` from
        -- `entry` for the first iteration, `whileBackIn`/`Out` from the
        -- previous iteration's exit for every later one.
        suffices hloop : ∀ (m : Nat), m ≤ nred → ∀ {pos : AState} {posPending : AConf → AConf}
            {c' : Conf} {r'' : Res} {αc : AlphaFn},
            AEdge Γ cs entry pending (.whileDo κ e s) pos (.whileIn cs κ)
              (fun L => posPending (L pos)) (fun _ => some .epsilon) →
            AEdge Γ cs entry pending (.whileDo κ e s) pos (.whileOut cs κ)
              (fun L => posPending (L pos)) (fun _ => some .epsilon) →
            Γ ⊢ ⟨c', .ifElse κ e (.seq s (.whileDo κ e s)) .skip⟩ ⇓c[m] r'' →
            αc.Lits → αc.AllocSafe c'.heap c'.reg → c'.heap.Finite c'.reg → c'.reg.FidCanon →
            c' ∼αc posPending (L pos) →
            SoundRun Γ s₀ L cs entry pending (.whileDo κ e s) pos αc r'' by
          exact hloop nred (Nat.le_refl nred) AEdge.whileHeaderIn AEdge.whileHeaderOut Hstep
            hlit hsafe hfin hfid hα
        clear Hstep hα hlit hsafe hfin hfid
        intro m
        induction m using Nat.strongRecOn with
        | _ m IHloop =>
          intro hmn pos posPending c' r'' αc hedgeIn hedgeOut Hstep' hlit hsafe hfin hfid hα'
          have hsubBody : ∀ a b C ℓ, AEdge Γ cs (.whileIn cs κ) id s a b C ℓ →
              AGraph Γ s₀ a b C ℓ :=
            fun a b C ℓ he => hsub a b C ℓ (.whileBody he)
          cases Hstep' with
          | @ifFalse _ _ _ _ _ _ _ _ _ _ _ hval Hskip =>
              cases Hskip
              exact Or.inl ⟨.whileOut cs κ, id, .whileDo, rfl, αc, .refl αc, hsafe,
                hα'.le (hle hedgeOut), [], AWalk.single (hsub _ _ _ _ hedgeOut) rfl, trivial⟩
          | @ifTrue mm h1 ρ1 δ1 _ _ _ _ _ _ _ hval Hbody =>
              have hαIn : ⟨h1, ρ1, δ1⟩ ∼αc L (.whileIn cs κ) :=
                hα'.le (hle hedgeIn)
              cases Hbody with
              | @seqRet m1 _ _ _ _ _ _ _ _ _ _ Hs1 =>
                  rcases IH m1 (by omega) hcs hlit hsafe hfin hfid hsubBody Hs1 hαIn with
                      ⟨_, _, _, hcont, _⟩
                    | ⟨rst, rpending, e'', l, hARet_s, hout, α1, hext1, hsafe1, hα1, hmaps1,
                        tₐ, w, tr⟩
                  · exact absurd hcont (by simp)
                  · exact Or.inr ⟨rst, rpending, e'', l, .whileDo hARet_s, hout, α1, hext1,
                      hsafe1, hα1, hmaps1, tₐ, AWalk.step (hsub _ _ _ _ hedgeIn) rfl w, tr⟩
              | @seqCont m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hs1 Hs2 =>
                  rcases IH m1 (by omega) hcs hlit hsafe hfin hfid hsubBody Hs1 hαIn with
                      ⟨x, xpending, hAExit_s, hcont, α1, hext1, hsafe1, hα1, tₐ₁, w1, tr1⟩
                    | ⟨_, _, _, _, _, hout, _⟩
                  · cases Hs2 with
                    | @whileDo m2 _ _ _ _ _ _ _ Hstep2 =>
                        rcases IHloop m2 (by omega) (by omega) (pos := x) (posPending := xpending)
                            (αc := α1) (.whileBackIn hAExit_s) (.whileBackOut hAExit_s) Hstep2
                            (hlit.mono hext1) hsafe1 (BigStep.finite Hs1.toBigStep hfin)
                            (BigStep.fidCanon cspec.opSem_fid Hs1.toBigStep hfid) hα1 with
                            ⟨y, ypending, hAExit_y, hout2, α2, hext2, hsafe2, hα2, tₐ₂, w2, tr2⟩
                          | ⟨rst, rpending, e'', l, hARet_y, hout2, α2, hext2, hsafe2, hα2, hmaps2,
                              tₐ₂, w2, tr2⟩
                        · exact Or.inl ⟨y, ypending, hAExit_y, hout2, α2, hext1.trans hext2,
                            hsafe2, hα2, tₐ₁ ++ tₐ₂,
                            AWalk.step (hsub _ _ _ _ hedgeIn) rfl (w1.append w2),
                            (tr1.mono hext2).seq tr2⟩
                        · exact Or.inr ⟨rst, rpending, e'', l, hARet_y, hout2, α2,
                            hext1.trans hext2, hsafe2, hα2, hmaps2, tₐ₁ ++ tₐ₂,
                            AWalk.step (hsub _ _ _ _ hedgeIn) rfl (w1.append w2),
                            (tr1.mono hext2).seq tr2⟩
                  · exact absurd hout (by simp)
    | @callRet nred h h' ρ ρ' ρf' δ δ' x κ e es lf f params body ls l t he hlf hΓf hes
        harity Hstep hρ' =>
        subst hρ'
        -- (1) the call resolves to `f`: build the candidate check from `hα`.
        have hval_e := eval_alpha hlit hα.2.1 he
        have hVmem := hα.2.2.valOf hval_e hlf
        have hargs := evals_alpha hlit hα.2.1 es hes
        have harity' : params.length = es.length := harity.trans (evalEs_length hes)
        have hΓparams : Γ.params f = params := by simp [Env.params, hΓf]
        have hcand : (pending (L entry)).Calls Γ e es.length f :=
          ⟨hVmem, by simp [hΓf], by rw [hΓparams, harity']⟩
        -- (2) relate the callee's initial store, and lift it to `L (entry cs_f)`.
        have hEntry := AEdge.callEntry (cs := cs) (entry := entry) (pending := pending) (x := x)
          (κ := κ) (e := e) hΓf harity'
        have hedge_entry := hle hEntry
        simp only [hcand, if_pos] at hedge_entry
        have hcα0 : AConf.Alpha α ⟨h, Sto.ofParams params ls, δ⟩
            { heap := (pending (L entry)).heap
              sto := ASto.ofParams params (⟦es⟧(pending (L entry)).sto)
              reg := (pending (L entry)).reg } :=
          ⟨hα.1, sto_ofParams_alpha hargs params, hα.2.2⟩
        -- (3) descend into the callee body, whose edges are the graph's by
        -- `AGraph.body`.
        have hcsf : CallString.WF (targetCallString cs κ f) := targetCallString_wf hcs κ f
        rcases IH nred (Nat.lt_succ_self _) (c := ⟨h, Sto.ofParams params ls, δ⟩) hcsf hlit
            hsafe hfin hfid
            (fun a b C ℓ he => .body hΓf hcsf (targetCallString_ends cs κ f)
              (hsub _ _ _ _ hEntry) he) Hstep (hcα0.le hedge_entry) with
            ⟨_, _, _, hcont, _⟩
          | ⟨rst, rpending, e', l', hARet, hout, α', hext, hsafe', hαres, hmaps, tₐ, w, tr⟩
        · exact absurd hcont (by simp)
        · -- (4) combine the `ret`-to-`cont` edge and the pass-through edge
          -- componentwise: heap/register from the callee (which started from
          -- the caller's), the returned variable `x` from the `ret` edge,
          -- every other variable from the pass-through edge.
          have heql : l = l' := by injection hout
          subst heql
          have hRet := AEdge.callRet (x := x) (κ := κ) (e := e) (es := es) (cs := cs)
            (entry := entry) (pending := pending) hΓf harity' hARet
          have hedge_ret := hle hRet
          simp only [hcand, if_pos] at hedge_ret
          have hedge_pass := hle (AEdge.callPassThrough (x := x) (κ := κ) (e := e) (es := es))
          -- The callee location is `f`'s literal location.
          have hlf' : α' lf = some (Abstract.litLocA (.fid f)) := by
            rw [hfid lf f hlf]; exact hlit.mono hext _
          refine Or.inl ⟨.cont cs κ, id, .call, rfl, α', hext, hsafe', ⟨?_, ?_, ?_⟩, _,
            AWalk.step (hsub _ _ _ _ hEntry) (hℓ _ _ hcand)
              (w.append (AWalk.single (hsub _ _ _ _ hRet) (hℓ _ _ hcand))),
            ActsAlpha.append (t₁ := [_]) ⟨⟨hlf', hargs.mono hext⟩, trivial⟩
              (ActsAlpha.append tr ⟨⟨hlf', hmaps⟩, trivial⟩)⟩
          · exact hαres.1.le hedge_ret.1
          · intro y ly hy
            by_cases hxy : y = x
            · have hlyl : ly = l := by rw [hxy] at hy; simpa [Sto.upd] using hy.symm
              rw [hxy, hlyl]
              have hxineq : (⟦e'⟧(rpending (L rst)).sto) ⊆ (L (.cont cs κ)).sto x := by
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
        have hVmem := hα.2.2.valOf hval_e hlf
        have hargs := evals_alpha hlit hα.2.1 es hes
        have harity' : params.length = es.length := harity.trans (evalEs_length hes)
        have hΓparams : Γ.params f = params := by simp [Env.params, hΓf]
        have hcand : (pending (L entry)).Calls Γ e es.length f :=
          ⟨hVmem, by simp [hΓf], by rw [hΓparams, harity']⟩
        have hEntry := AEdge.callEntry (cs := cs) (entry := entry) (pending := pending) (x := x)
          (κ := κ) (e := e) hΓf harity'
        have hedge_entry := hle hEntry
        simp only [hcand, if_pos] at hedge_entry
        have hcα0 : AConf.Alpha α ⟨h, Sto.ofParams params ls, δ⟩
            { heap := (pending (L entry)).heap
              sto := ASto.ofParams params (⟦es⟧(pending (L entry)).sto)
              reg := (pending (L entry)).reg } :=
          ⟨hα.1, sto_ofParams_alpha hargs params, hα.2.2⟩
        have hcsf : CallString.WF (targetCallString cs κ f) := targetCallString_wf hcs κ f
        rcases IH nred (Nat.lt_succ_self _) (c := ⟨h, Sto.ofParams params ls, δ⟩) hcsf hlit
            hsafe hfin hfid
            (fun a b C ℓ he => .body hΓf hcsf (targetCallString_ends cs κ f)
              (hsub _ _ _ _ hEntry) he) Hstep (hcα0.le hedge_entry) with
            ⟨y, ypending, hAExit, hout, α', hext, hsafe', hαres, tₐ, w, tr⟩
          | ⟨_, _, _, _, _, hout, _⟩
        · have hRet := AEdge.callImplicitRet (x := x) (κ := κ) (e := e) (es := es) (cs := cs)
            (entry := entry) (pending := pending) hΓf harity' hAExit
          have hedge_ret := hle hRet
          simp only [hcand, if_pos] at hedge_ret
          have hedge_pass := hle (AEdge.callPassThrough (x := x) (κ := κ) (e := e) (es := es))
          have hlf' : α' lf = some (Abstract.litLocA (.fid f)) := by
            rw [hfid lf f hlf]; exact hlit.mono hext _
          have hundef : α'.MapsInto (Concrete.litLoc .undef)
              ({Abstract.litLocA .undef} : ALocSet) :=
            ⟨Abstract.litLocA .undef, hlit.mono hext .undef, rfl⟩
          refine Or.inl ⟨.cont cs κ, id, .call, rfl, α', hext, hsafe', ⟨?_, ?_, ?_⟩, _,
            AWalk.step (hsub _ _ _ _ hEntry) (hℓ _ _ hcand)
              (w.append (AWalk.single (hsub _ _ _ _ hRet) (hℓ _ _ hcand))),
            ActsAlpha.append (t₁ := [_]) ⟨⟨hlf', hargs.mono hext⟩, trivial⟩
              (ActsAlpha.append tr ⟨⟨hlf', hundef⟩, trivial⟩)⟩
          · exact hαres.1.le hedge_ret.1
          · intro z lz hz
            by_cases hxz : z = x
            · have hlzl : lz = Concrete.litLoc .undef := by
                rw [hxz] at hz; simpa [Sto.upd] using hz.symm
              rw [hxz, hlzl]
              have hxineq : ({Abstract.litLocA .undef} : ALocSet) ⊆ (L (.cont cs κ)).sto x := by
                simpa [ASto.upd] using hedge_ret.2.1 x
              exact hundef.subset hxineq
            · have hz' : ρ z = some lz := by simpa [Sto.upd, hxz] using hz
              have hcaller := hα.2.1 z lz hz'
              have hpass : (pending (L entry)).sto z ⊆ (L (.cont cs κ)).sto z := by
                have := hedge_pass.2.1 z
                simpa [ASto.upd, hxz] using this
              exact (hcaller.subset hpass).mono hext
          · exact hαres.2.2.le hedge_ret.2.2
        · exact absurd hout (by simp)

/-- `step_sound` with the derivation height existentially quantified away. -/
theorem sound [Concrete] [Abstract] (cspec : ConcreteSpec) (xspec : CrossSpec)
    {Γ : Env} {s₀ : Stmt} {L : Labeling} (hvalid : Labeling.Valid Γ s₀ L)
    {cs : CallString} {entry : AState} {pending : AConf → AConf} {s : Stmt}
    {c : Conf} {r : Res} {α : AlphaFn}
    (hcs : CallString.WF cs) (hlit : α.Lits) (hsafe : α.AllocSafe c.heap c.reg)
    (hfin : c.heap.Finite c.reg) (hfid : c.reg.FidCanon)
    (hsub : ∀ a b C ℓ, AEdge Γ cs entry pending s a b C ℓ → AGraph Γ s₀ a b C ℓ)
    (H : Γ ⊢ ⟨c, s⟩ ⇓c r) (hα : c ∼α pending (L entry)) :
    SoundRun Γ s₀ L cs entry pending s entry α r := by
  obtain ⟨n, HN⟩ := H.toN
  exact step_sound cspec xspec hvalid n hcs hlit hsafe hfin hfid hsub HN hα

/-- Soundness of a whole program: every run of `s₀` from its initial
    configuration is matched, against any analysis result `L`, by a walk of
    the labeled automaton from the top-level entry, with the run's trace and
    final configuration related to the walk's trace and final label.

    Scope: only runs with a `BigStep` derivation are covered. `Γ` holds every
    function definition, and a call to a function not in `Γ` (for example an
    unavailable external dependency) has no rule, so a run making one has no
    derivation and lies outside this theorem.

    `fs` lists the functions whose literals the initial register sets up
    (normally all of `Γ`'s); the analysis covers every function of `Γ`
    (`AConf.init Γ s₀`), so the theorem holds whatever `fs` is. -/
theorem sound_top [Concrete] [Abstract] (cspec : ConcreteSpec) (xspec : CrossSpec)
    {Γ : Env} {fs : List Fid} {s₀ : Stmt} {L : Labeling} (hres : AnalysisResult Γ s₀ L)
    {r : Res} (H : Γ ⊢ ⟨Conf.init Γ fs s₀, s₀⟩ ⇓c r) :
    SoundRun Γ s₀ L [] (.entry []) id s₀ (.entry []) AlphaFn.lits r :=
  sound cspec xspec hres.1 CallString.WF.nil (AlphaFn.lits_lits cspec)
    (AlphaFn.lits_allocSafe _ _) (Reg.init_finite Γ fs s₀) (Reg.init_fidCanon Γ fs s₀)
    (fun _ _ _ _ he => .top he) H ((AConf.Alpha.init cspec Γ fs s₀).le hres.2)

/-- The headline result: every run of a program from its initial
    configuration is matched by a walk through the automaton labeled with the
    program's least analysis result (`CoreJsAutomatonTotality.lean`), which
    always exists. -/
theorem sound_least [Concrete] [Abstract] (cspec : ConcreteSpec) (aspec : AbstractSpec)
    (xspec : CrossSpec) {Γ : Env} {fs : List Fid} {s₀ : Stmt} {r : Res}
    (H : Γ ⊢ ⟨Conf.init Γ fs s₀, s₀⟩ ⇓c r) :
    SoundRun Γ s₀ (Labeling.least Γ s₀) [] (.entry []) id s₀ (.entry []) AlphaFn.lits r :=
  sound_top cspec xspec (Labeling.least_result aspec Γ s₀) H

/-! ## The assumptions are jointly satisfiable

`ConcreteSpec`, `AbstractSpec` and `CrossSpec` together hold of at least one
pair of instances, so the theorems above do not hold vacuously. The witness is
deliberately crude: literals at even locations (through an injective
encoding of values), allocation at the first odd location past a finite
memory's support, a single abstract location for every allocation site, every
function at its own even abstract location, and `opSemA` always `⊤`. -/

namespace SpecModel

private def B : Nat := 2 ^ 32 + 1

private def encChars : List Char → Nat
  | []      => 0
  | c :: cs => (c.toNat + 1) + B * encChars cs

private theorem digit_lt (c : Char) : c.toNat + 1 < B := by
  have : c.toNat < 2 ^ 32 := c.val.toNat_lt
  unfold B; omega

private theorem encChars_inj : ∀ {a b : List Char}, encChars a = encChars b → a = b
  | [],      [],      _ => rfl
  | [],      _ :: _,  h => by simp only [encChars] at h; omega
  | _ :: _,  [],      h => by simp only [encChars] at h; omega
  | c :: cs, d :: ds, h => by
      have hB : 0 < B := by unfold B; omega
      have h1 := congrArg (· % B) h
      have h2 := congrArg (· / B) h
      simp only [encChars, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (digit_lt _)] at h1
      simp only [encChars, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (digit_lt _)] at h2
      have hc : c = d := Char.toNat_inj.mp (by omega)
      rw [hc, encChars_inj (by omega : encChars cs = encChars ds)]

private def encStr (s : String) : Nat := encChars s.toList

private theorem encStr_inj {s t : String} (h : encStr s = encStr t) : s = t :=
  String.ext (encChars_inj h)

private def encInt : Int → Nat
  | .ofNat n   => 2 * n
  | .negSucc n => 2 * n + 1

private theorem encInt_inj : ∀ {i j : Int}, encInt i = encInt j → i = j
  | .ofNat _,   .ofNat _,   h => by simp only [encInt] at h; congr 1; omega
  | .ofNat _,   .negSucc _, h => by simp only [encInt] at h; omega
  | .negSucc _, .ofNat _,   h => by simp only [encInt] at h; omega
  | .negSucc _, .negSucc _, h => by simp only [encInt] at h; congr 1; omega

private def encVal : Val → Nat
  | .num i  => 6 * encInt i
  | .str s  => 6 * encStr s + 1
  | .bool b => 6 * (if b then 1 else 0) + 2
  | .fid f  => 6 * encStr f + 3
  | .loc l  => 6 * l + 4
  | .undef  => 5
  | .proto  => 11

private theorem encVal_inj : ∀ {v w : Val}, encVal v = encVal w → v = w := by
  intro v w h
  cases v <;> cases w <;> simp only [encVal] at h <;>
    first
    | omega
    | (congr 1; exact encInt_inj (by omega))
    | (congr 1; exact encStr_inj (by omega))
    | (congr 1; exact Nat.eq_of_mul_eq_mul_left (by decide) (Nat.add_right_cancel h))
    | rfl
    | (rename_i b c; cases b <;> cases c <;> simp at h ⊢)

@[reducible] private noncomputable def concrete : Concrete where
  litLoc v := 2 * encVal v
  allocC h δ _ := by
    classical
    exact if hf : h.Finite δ then 2 * Classical.choose hf + 1 else 1
  opSem _ _ _ := .undef

@[reducible] private def abstract : Abstract where
  litLocA
    | .fid f => 2 * encStr f + 2
    | _      => (1 : Nat)
  allocA _ _ _ := (0 : Nat)
  opSemA _ _ _ := .top

attribute [local instance] concrete abstract

private theorem allocC_eq {h : Heap} {δ : Reg} (hf : h.Finite δ) (κ : Idx) :
    Concrete.allocC h δ κ = 2 * Classical.choose hf + 1 := by
  show (if hf : h.Finite δ then _ else _) = _
  rw [dif_pos hf]

private theorem cspec : ConcreteSpec where
  litLoc_inj v w h := encVal_inj (Nat.eq_of_mul_eq_mul_left (by decide) h)
  allocC_fresh h δ κ hf := by
    rw [allocC_eq hf]
    exact Classical.choose_spec hf _
      (Nat.le_succ_of_le (Nat.le_mul_of_pos_left _ (by decide)))
  allocC_lit h δ κ v hf := by
    rw [allocC_eq hf]
    intro heq
    have : (2 * Classical.choose hf + 1 : Nat) = 2 * encVal v := heq
    omega
  opSem_fid _ _ _ _ h := by cases h

private theorem aspec : AbstractSpec where
  opSemA_mono _ _ _ _ _ _ _ _ hv := hv
  allocA_site _ _ _ _ _ := rfl
  litLocA_fid f v h := by
    cases v
    case fid g =>
      have h' : (2 * encStr f + 2 : Nat) = 2 * encStr g + 2 := h
      exact congrArg Val.fid (encStr_inj (by omega))
    all_goals (have h' : (2 * encStr f + 2 : Nat) = 1 := h; omega)
  allocA_fid _ _ _ f h := by
    have h' : (0 : Nat) = 2 * encStr f + 2 := h
    omega

private theorem xspec : CrossSpec where
  opSem_sound _ _ _ _ _ _ _ := trivial

theorem satisfiable :
    ∃ (C : Concrete) (A : Abstract), @ConcreteSpec C ∧ @AbstractSpec A ∧ @CrossSpec C A :=
  ⟨concrete, abstract, cspec, aspec, xspec⟩

end SpecModel

end CoreJS
