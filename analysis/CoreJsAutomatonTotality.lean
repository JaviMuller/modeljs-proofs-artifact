/-
  # Core JavaScript — Existence of a Least Analysis Result

  Every program has an analysis result (`AnalysisResult`), and in fact a
  *least* one: `Labeling.least Γ s₀`, below every other. It is the most precise
  labeling the automaton admits, so the existence proof does not settle for a
  trivial witness (the labeling that is `⊤` everywhere is also valid, but
  carries no information).

  The abstract domains are sets represented as predicates, so a labeling
  lattice has arbitrary meets and joins: `Labeling.least` is the meet of all
  analysis results. It is itself one because every edge's contribution is
  monotone in the labeling (`AGraph.lmono`): the meet lies below each result,
  so each edge's contribution from it lies below that result's target label,
  hence below their meet.

  The same fact gives the fixpoint reading. `Labeling.step L` is the join of
  every edge's contribution into each state (plus the initial configuration
  at the top-level entry); a labeling is an analysis result exactly when
  `step L ≤ L`, and `least` is a fixed point of `step`. Iterating `step` from
  `⊥` (`Labeling.kleene`) gives an ascending chain below `least`, and an
  iterate that is itself a post-fixed point *is* `least`. Whether the chain
  reaches such an iterate after finitely many steps depends on `opSemA`
  (value sets over an infinite domain, widened or not) and is not assumed.

  Finally, the least result keeps functions' locations reserved to them
  (`least_fidReserved`, invariant `AConf.FidReserved`).
-/

import CoreJsAutomatonSemantics

namespace CoreJS

open Abstract

/-! ## The order on configurations is a preorder with a least element -/

theorem AConf.le_refl (c : AConf) : c ⊑ c :=
  ⟨⟨fun _ _ _ h => h, fun _ _ h => h⟩, fun _ _ h => h, fun _ _ h => h, fun _ h => h,
    fun _ h => h⟩

theorem AConf.le_trans {c₁ c₂ c₃ : AConf} (h₁ : c₁ ⊑ c₂) (h₂ : c₂ ⊑ c₃) : c₁ ⊑ c₃ :=
  ⟨⟨fun l p a h => h₂.1.1 l p a (h₁.1.1 l p a h), fun l v h => h₂.1.2 l v (h₁.1.2 l v h)⟩,
    fun x a h => h₂.2.1 x a (h₁.2.1 x a h),
    fun l a h => h₂.2.2.1 l a (h₁.2.2.1 l a h),
    fun a h => h₂.2.2.2.1 a (h₁.2.2.2.1 a h),
    fun a h => h₂.2.2.2.2 a (h₁.2.2.2.2 a h)⟩

theorem AConf.bot_le (c : AConf) : AConf.bot ⊑ c :=
  ⟨⟨fun _ _ _ h => h.elim, fun _ _ h => h.elim⟩, fun _ _ h => h.elim, fun _ _ h => h.elim,
    fun _ h => h.elim, fun _ h => h.elim⟩

/-! ## Monotonicity of the abstract operations -/

theorem VSet.mem_join {V₁ V₂ : VSet} {v : Val} :
    (VSet.join V₁ V₂).Mem v ↔ V₁.Mem v ∨ V₂.Mem v := by
  cases V₁ <;> cases V₂ <;> simp [VSet.join, VSet.Mem]

theorem aevalE_mono [Abstract] {ρ ρ' : ASto} (hρ : ρ ⊑ ρ') (e : Expr) :
    aevalE ρ e ⊆ aevalE ρ' e := by
  cases e with
  | val v => exact fun _ h => h
  | var x => exact hρ x

/-- Componentwise inclusion of two lists of location sets. -/
def ListLe : List ALocSet → List ALocSet → Prop
  | [],      []        => True
  | L :: Ls, L' :: Ls' => L ⊆ L' ∧ ListLe Ls Ls'
  | _,       _         => False

theorem aevalEs_mono [Abstract] {ρ ρ' : ASto} (hρ : ρ ⊑ ρ') :
    ∀ es : List Expr, ListLe (aevalEs ρ es) (aevalEs ρ' es)
  | []      => trivial
  | e :: es => ⟨aevalE_mono hρ e, aevalEs_mono hρ es⟩

theorem ASto.upd_mono {ρ ρ' : ASto} (hρ : ρ ⊑ ρ') (x : Var) {L L' : ALocSet} (hL : L ⊆ L') :
    ρ.upd x L ⊑ ρ'.upd x L' := by
  intro y
  by_cases e : y = x
  · simp only [ASto.upd, e, if_pos]; exact hL
  · simp only [ASto.upd, e, if_neg, not_false_eq_true]; exact hρ y

theorem ASto.ofParams_mono :
    ∀ (ps : List Var) {Ls Ls' : List ALocSet}, ListLe Ls Ls' →
      ASto.ofParams ps Ls ⊑ ASto.ofParams ps Ls'
  | [],      _,       _,        _ => fun _ _ h => h
  | _ :: _,  [],      [],       _ => fun _ _ h => h
  | x :: xs, _ :: _,  _ :: _,   h => ASto.upd_mono (ASto.ofParams_mono xs h.2) x h.1
  | _ :: _,  [],      _ :: _,   h => h.elim
  | _ :: _,  _ :: _,  [],       h => h.elim

theorem AHeap.valOf_mono {h h' : AHeap} (hh : h ⊑ h') {L L' : ALocSet} (hL : L ⊆ L') :
    h.valOf L ⊑ h'.valOf L' := by
  rintro v ⟨l, hl, hv⟩
  exact ⟨l, hL l hl, hh.2 l v hv⟩

theorem AHeap.objOf_mono {h h' : AHeap} (hh : h ⊑ h') {L L' : ALocSet} (hL : L ⊆ L')
    (p : PropName) : h.objOf L p ⊆ h'.objOf L' p := by
  rintro a ⟨l, hl, ha⟩
  exact ⟨l, hL l hl, hh.1 l p a ha⟩

theorem AHeap.objOfV_mono {h h' : AHeap} (hh : h ⊑ h') {L L' : ALocSet} (hL : L ⊆ L')
    {V V' : VSet} (hV : V ⊑ V') : h.objOfV L V ⊆ h'.objOfV L' V' := by
  rintro a ⟨l, p, hl, hp, ha⟩
  exact ⟨l, p, hL l hl, hV _ hp, hh.1 l p a ha⟩

theorem AReg.depOf_mono {δ δ' : AReg} (hδ : δ ⊑ δ') {L L' : ALocSet} (hL : L ⊆ L') :
    δ.depOf L ⊆ δ'.depOf L' := by
  rintro a ⟨l, hl, ha⟩
  exact ⟨l, hL l hl, hδ.1 l a ha⟩

theorem AHeap.weakSetVal_mono {h h' : AHeap} (hh : h ⊑ h') (l : ALoc) {V V' : VSet}
    (hV : V ⊑ V') : h.weakSetVal l V ⊑ h'.weakSetVal l V' := by
  refine ⟨hh.1, fun a v hv => ?_⟩
  by_cases e : a = l
  · simp only [AHeap.weakSetVal, e, if_pos] at hv ⊢
    rcases VSet.mem_join.1 hv with hv | hv
    · exact VSet.mem_join.2 (Or.inl (hV v hv))
    · exact VSet.mem_join.2 (Or.inr (hh.2 _ v hv))
  · simp only [AHeap.weakSetVal, e, if_neg, not_false_eq_true] at hv ⊢
    exact hh.2 a v hv

theorem AHeap.weakSetObj_mono {h h' : AHeap} (hh : h ⊑ h') {L L' : ALocSet} (hL : L ⊆ L')
    (p : PropName) {L₂ L₂' : ALocSet} (hL₂ : L₂ ⊆ L₂') :
    h.weakSetObj L p L₂ ⊑ h'.weakSetObj L' p L₂' := by
  refine ⟨fun a q b hab => ?_, hh.2⟩
  rcases hab with hab | ⟨ha, hq, hb⟩
  · exact Or.inl (hh.1 a q b hab)
  · exact Or.inr ⟨hL a ha, hq, hL₂ b hb⟩

theorem AHeap.weakSetObjV_mono {h h' : AHeap} (hh : h ⊑ h') {L L' : ALocSet} (hL : L ⊆ L')
    {V V' : VSet} (hV : V ⊑ V') {L₂ L₂' : ALocSet} (hL₂ : L₂ ⊆ L₂') :
    h.weakSetObjV L V L₂ ⊑ h'.weakSetObjV L' V' L₂' := by
  refine ⟨fun a q b hab => ?_, hh.2⟩
  rcases hab with hab | ⟨ha, hq, hb⟩
  · exact Or.inl (hh.1 a q b hab)
  · exact Or.inr ⟨hL a ha, hV _ hq, hL₂ b hb⟩

theorem AHeap.weakSetObjs_mono (l : ALoc) :
    ∀ (ps : List PropName) {h h' : AHeap} {Ls Ls' : List ALocSet}, h ⊑ h' → ListLe Ls Ls' →
      h.weakSetObjs l (ps.zip Ls) ⊑ h'.weakSetObjs l (ps.zip Ls')
  | [],      _, _, _,      _,       hh, _ => hh
  | _ :: _,  _, _, [],     [],      hh, _ => hh
  | p :: ps, _, _, _ :: _, _ :: _,  hh, hL =>
      AHeap.weakSetObjs_mono l ps (AHeap.weakSetObj_mono hh (fun _ h => h) p hL.1) hL.2
  | _ :: _,  _, _, [],     _ :: _,  _,  hL => hL.elim
  | _ :: _,  _, _, _ :: _, [],      _,  hL => hL.elim

theorem AReg.weakSetDep_mono {δ δ' : AReg} (hδ : δ ⊑ δ') (l : ALoc) {d d' : ALocSet}
    (hd : d ⊆ d') : δ.weakSetDep l d ⊑ δ'.weakSetDep l d' := by
  refine ⟨fun a b hab => ?_, hδ.2.1, hδ.2.2⟩
  by_cases e : a = l
  · simp only [AReg.weakSetDep, e, if_pos] at hab ⊢
    rcases hab with hab | hab
    · exact Or.inl (hd b hab)
    · exact Or.inr (hδ.1 _ b hab)
  · simp only [AReg.weakSetDep, e, if_neg, not_false_eq_true] at hab ⊢
    exact hδ.1 a b hab

theorem ALocSet.union_mono {A A' B B' : ALocSet} (hA : A ⊆ A') (hB : B ⊆ B') :
    A ∪ B ⊆ A' ∪ B' := by
  rintro l (h | h)
  · exact Or.inl (hA l h)
  · exact Or.inr (hB l h)

theorem AConf.Calls_mono [Abstract] {Γ : Env} {e : Expr} {n : Nat} {f : Fid} {c c' : AConf}
    (hc : c ⊑ c') (h : c.Calls Γ e n f) : c'.Calls Γ e n f :=
  ⟨AHeap.valOf_mono hc.1 (aevalE_mono hc.2.1 e) _ h.1, h.2.1, h.2.2⟩

/-! ## Monotonicity of the per-statement effects -/

/-- `f` preserves the order. -/
def AMono (f : AConf → AConf) : Prop := ∀ c c', c ⊑ c' → f c ⊑ f c'

theorem AConf.doAssign_mono [Abstract] (x : Var) (e : Expr) : AMono (AConf.doAssign x e) :=
  fun _ _ h => ⟨h.1, ASto.upd_mono h.2.1 x (aevalE_mono h.2.1 e), h.2.2⟩

theorem AConf.doBinOp_mono [Abstract] (aspec : AbstractSpec) (x : Var) (κ : Idx) (op : BinOp)
    (e₁ e₂ : Expr) : AMono (AConf.doBinOp x κ op e₁ e₂) := by
  intro c c' h
  have hl : allocA c.heap κ = allocA c'.heap κ := aspec.allocA_site _ _ κ
  have hL₁ := aevalE_mono h.2.1 e₁
  have hL₂ := aevalE_mono h.2.1 e₂
  simp only [AConf.doBinOp, hl]
  refine ⟨AHeap.weakSetVal_mono h.1 _ (aspec.opSemA_mono _ _ _ _ _
      (AHeap.valOf_mono h.1 hL₁) (AHeap.valOf_mono h.1 hL₂)),
    ASto.upd_mono h.2.1 x (fun _ h => h), AReg.weakSetDep_mono h.2.2 _ ?_⟩
  exact ALocSet.union_mono (ALocSet.union_mono (ALocSet.union_mono
    (AReg.depOf_mono h.2.2 hL₁) (AReg.depOf_mono h.2.2 hL₂)) hL₁) hL₂

theorem AConf.doObjLit_mono [Abstract] (aspec : AbstractSpec) (x : Var) (κ : Idx)
    (fs : List (PropName × Expr)) : AMono (AConf.doObjLit x κ fs) := by
  intro c c' h
  have hl : allocA c.heap κ = allocA c'.heap κ := aspec.allocA_site _ _ κ
  simp only [AConf.doObjLit, hl]
  exact ⟨AHeap.weakSetObjs_mono _ _ h.1 (aevalEs_mono h.2.1 _),
    ASto.upd_mono h.2.1 x (fun _ h => h), h.2.2⟩

theorem AConf.doSetTaint_mono [Abstract] (e : Expr) : AMono (AConf.doSetTaint e) :=
  fun _ _ h => ⟨h.1, h.2.1, h.2.2.1, ALocSet.union_mono (aevalE_mono h.2.1 e) h.2.2.2.1,
    h.2.2.2.2⟩

theorem AConf.doSetSink_mono [Abstract] (e : Expr) : AMono (AConf.doSetSink e) :=
  fun _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    ALocSet.union_mono (aevalE_mono h.2.1 e) h.2.2.2.2⟩

theorem AConf.doLookupS_mono [Abstract] (x : Var) (e : Expr) (p : PropName) :
    AMono (AConf.doLookupS x e p) :=
  fun _ _ h => ⟨h.1, ASto.upd_mono h.2.1 x (AHeap.objOf_mono h.1 (aevalE_mono h.2.1 e) p),
    h.2.2⟩

theorem AConf.doLookupD_mono [Abstract] (x : Var) (e₁ e₂ : Expr) :
    AMono (AConf.doLookupD x e₁ e₂) :=
  fun _ _ h => ⟨h.1, ASto.upd_mono h.2.1 x (AHeap.objOfV_mono h.1 (aevalE_mono h.2.1 e₁)
    (AHeap.valOf_mono h.1 (aevalE_mono h.2.1 e₂))), h.2.2⟩

theorem AConf.doUpdateS_mono [Abstract] (e₁ : Expr) (p : PropName) (e₂ : Expr) :
    AMono (AConf.doUpdateS e₁ p e₂) :=
  fun _ _ h => ⟨AHeap.weakSetObj_mono h.1 (aevalE_mono h.2.1 e₁) p (aevalE_mono h.2.1 e₂),
    h.2.1, h.2.2⟩

theorem AConf.doUpdateD_mono [Abstract] (e₁ e₂ e₃ : Expr) : AMono (AConf.doUpdateD e₁ e₂ e₃) :=
  fun _ _ h => ⟨AHeap.weakSetObjV_mono h.1 (aevalE_mono h.2.1 e₁)
    (AHeap.valOf_mono h.1 (aevalE_mono h.2.1 e₂)) (aevalE_mono h.2.1 e₃), h.2.1, h.2.2⟩

theorem AMono.pendingClosed [Abstract] (aspec : AbstractSpec) : PendingClosed AMono where
  id := fun _ _ h => h
  assign := fun x e hf c c' h => AConf.doAssign_mono x e _ _ (hf c c' h)
  binOp := fun x κ op e₁ e₂ hf c c' h => AConf.doBinOp_mono aspec x κ op e₁ e₂ _ _ (hf c c' h)
  objLit := fun x κ fs hf c c' h => AConf.doObjLit_mono aspec x κ fs _ _ (hf c c' h)
  setTaint := fun e hf c c' h => AConf.doSetTaint_mono e _ _ (hf c c' h)
  setSink := fun e hf c c' h => AConf.doSetSink_mono e _ _ (hf c c' h)

/-! ## Every edge's contribution is monotone in the labeling -/

/-- Pointwise order on labelings. -/
def Labeling.Le (L L' : Labeling) : Prop := ∀ st, L st ⊑ L' st

theorem Labeling.Le.refl (L : Labeling) : L.Le L := fun st => AConf.le_refl (L st)

theorem Labeling.Le.trans {L₁ L₂ L₃ : Labeling} (h₁ : L₁.Le L₂) (h₂ : L₂.Le L₃) : L₁.Le L₃ :=
  fun st => AConf.le_trans (h₁ st) (h₂ st)

/-- A contribution preserves the order on labelings. -/
def LMono (C : Labeling → AConf) : Prop := ∀ L L', L.Le L' → C L ⊑ C L'

theorem AEdge.lmono [Abstract] (aspec : AbstractSpec) {Γ : Env} :
    ∀ {cs entry pending s a b C ℓ}, AEdge Γ cs entry pending s a b C ℓ →
      AMono pending → LMono C
  | _, _, _, _, _, _, _, _, .lookupS, hp => fun _ _ hL =>
      AConf.doLookupS_mono _ _ _ _ _ (hp _ _ (hL _))
  | _, _, _, _, _, _, _, _, .lookupD, hp => fun _ _ hL =>
      AConf.doLookupD_mono _ _ _ _ _ (hp _ _ (hL _))
  | _, _, _, _, _, _, _, _, .updateS, hp => fun _ _ hL =>
      AConf.doUpdateS_mono _ _ _ _ _ (hp _ _ (hL _))
  | _, _, _, _, _, _, _, _, .updateD, hp => fun _ _ hL =>
      AConf.doUpdateD_mono _ _ _ _ _ (hp _ _ (hL _))
  | _, _, _, _, _, _, _, _, .seqLeft h₁, hp => AEdge.lmono aspec h₁ hp
  | _, _, _, _, _, _, _, _, .seqRight hx h₂, hp =>
      AEdge.lmono aspec h₂ (AExit.closed (AMono.pendingClosed aspec) hx hp)
  | _, _, _, _, _, _, _, _, .ifThen, hp => fun _ _ hL => hp _ _ (hL _)
  | _, _, _, _, _, _, _, _, .ifElseB, hp => fun _ _ hL => hp _ _ (hL _)
  | _, _, _, _, _, _, _, _, .ifThenBody h₁, _ => AEdge.lmono aspec h₁ (fun _ _ h => h)
  | _, _, _, _, _, _, _, _, .ifElseBBody h₁, _ => AEdge.lmono aspec h₁ (fun _ _ h => h)
  | _, _, _, _, _, _, _, _, .ifThenJoin hx, _ => fun _ _ hL =>
      AExit.closed (AMono.pendingClosed aspec) hx (fun _ _ h => h) _ _ (hL _)
  | _, _, _, _, _, _, _, _, .ifElseBJoin hx, _ => fun _ _ hL =>
      AExit.closed (AMono.pendingClosed aspec) hx (fun _ _ h => h) _ _ (hL _)
  | _, _, _, _, _, _, _, _, .whileHeaderIn, hp => fun _ _ hL => hp _ _ (hL _)
  | _, _, _, _, _, _, _, _, .whileHeaderOut, hp => fun _ _ hL => hp _ _ (hL _)
  | _, _, _, _, _, _, _, _, .whileBody h₁, _ => AEdge.lmono aspec h₁ (fun _ _ h => h)
  | _, _, _, _, _, _, _, _, .whileBackIn hx, _ => fun _ _ hL =>
      AExit.closed (AMono.pendingClosed aspec) hx (fun _ _ h => h) _ _ (hL _)
  | _, _, _, _, _, _, _, _, .whileBackOut hx, _ => fun _ _ hL =>
      AExit.closed (AMono.pendingClosed aspec) hx (fun _ _ h => h) _ _ (hL _)
  | _, entry, _, _, _, _, _, _, .callPassThrough, hp => fun _ _ hL => by
      have hv := hp _ _ (hL entry)
      exact ⟨hv.1, ASto.upd_mono hv.2.1 _ (fun _ h => h), hv.2.2⟩
  | _, entry, _, _, _, _, _, _, .callEntry _ _, hp => fun L L' hL => by
      have hv := hp _ _ (hL entry)
      dsimp only
      split
      · rename_i hc
        rw [if_pos (AConf.Calls_mono hv hc)]
        exact ⟨hv.1, ASto.ofParams_mono _ (aevalEs_mono hv.2.1 _), hv.2.2⟩
      · exact AConf.bot_le _
  | _, entry, _, _, r, _, _, _, .callRet _ _ hr, hp => fun L L' hL => by
      have hv := hp _ _ (hL entry)
      have hw := ARet.closed (AMono.pendingClosed aspec) hr (fun _ _ h => h) _ _ (hL r)
      dsimp only
      split
      · rename_i hc
        rw [if_pos (AConf.Calls_mono hv hc)]
        exact ⟨hw.1, ASto.upd_mono (fun _ _ h => h) _ (aevalE_mono hw.2.1 _), hw.2.2⟩
      · exact AConf.bot_le _
  | _, entry, _, _, y, _, _, _, .callImplicitRet _ _ hy, hp => fun L L' hL => by
      have hv := hp _ _ (hL entry)
      have hw := AExit.closed (AMono.pendingClosed aspec) hy (fun _ _ h => h) _ _ (hL y)
      dsimp only
      split
      · rename_i hc
        rw [if_pos (AConf.Calls_mono hv hc)]
        exact ⟨hw.1, fun _ _ h => h, hw.2.2⟩
      · exact AConf.bot_le _

theorem AGraph.lmono [Abstract] (aspec : AbstractSpec) {Γ : Env} {s₀ : Stmt} {a b C ℓ}
    (he : AGraph Γ s₀ a b C ℓ) : LMono C := by
  cases he with
  | top h => exact AEdge.lmono aspec h (fun _ _ h => h)
  | body _ _ h => exact AEdge.lmono aspec h (fun _ _ h => h)

/-! ## Meets and joins of arbitrary sets of configurations -/

/-- The greatest lower bound of a set of configurations. -/
def AConf.inf (P : AConf → Prop) : AConf where
  heap := { obj := fun a p b => ∀ c, P c → c.heap.obj a p b
            val := fun a => .vals (fun v => ∀ c, P c → (c.heap.val a).Mem v) }
  sto  := fun x a => ∀ c, P c → c.sto x a
  reg  := { dep := fun a b => ∀ c, P c → c.reg.dep a b
            ac  := fun a => ∀ c, P c → c.reg.ac a
            sk  := fun a => ∀ c, P c → c.reg.sk a }

theorem AConf.inf_le {P : AConf → Prop} {c : AConf} (hc : P c) : AConf.inf P ⊑ c :=
  ⟨⟨fun _ _ _ h => h c hc, fun _ _ h => h c hc⟩, fun _ _ h => h c hc, fun _ _ h => h c hc,
    fun _ h => h c hc, fun _ h => h c hc⟩

theorem AConf.le_inf {P : AConf → Prop} {d : AConf} (h : ∀ c, P c → d ⊑ c) :
    d ⊑ AConf.inf P :=
  ⟨⟨fun a p b hd c hc => (h c hc).1.1 a p b hd, fun a v hd c hc => (h c hc).1.2 a v hd⟩,
    fun x a hd c hc => (h c hc).2.1 x a hd,
    fun a b hd c hc => (h c hc).2.2.1 a b hd,
    fun a hd c hc => (h c hc).2.2.2.1 a hd,
    fun a hd c hc => (h c hc).2.2.2.2 a hd⟩

/-- The least upper bound of a set of configurations. -/
def AConf.sup (P : AConf → Prop) : AConf where
  heap := { obj := fun a p b => ∃ c, P c ∧ c.heap.obj a p b
            val := fun a => .vals (fun v => ∃ c, P c ∧ (c.heap.val a).Mem v) }
  sto  := fun x a => ∃ c, P c ∧ c.sto x a
  reg  := { dep := fun a b => ∃ c, P c ∧ c.reg.dep a b
            ac  := fun a => ∃ c, P c ∧ c.reg.ac a
            sk  := fun a => ∃ c, P c ∧ c.reg.sk a }

theorem AConf.le_sup {P : AConf → Prop} {c : AConf} (hc : P c) : c ⊑ AConf.sup P :=
  ⟨⟨fun _ _ _ h => ⟨c, hc, h⟩, fun _ _ h => ⟨c, hc, h⟩⟩, fun _ _ h => ⟨c, hc, h⟩,
    fun _ _ h => ⟨c, hc, h⟩, fun _ h => ⟨c, hc, h⟩, fun _ h => ⟨c, hc, h⟩⟩

theorem AConf.sup_le {P : AConf → Prop} {d : AConf} (h : ∀ c, P c → c ⊑ d) :
    AConf.sup P ⊑ d := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rintro a p b ⟨c, hc, hb⟩; exact (h c hc).1.1 a p b hb
  · rintro a v ⟨c, hc, hv⟩; exact (h c hc).1.2 a v hv
  · rintro x a ⟨c, hc, ha⟩; exact (h c hc).2.1 x a ha
  · rintro a b ⟨c, hc, hb⟩; exact (h c hc).2.2.1 a b hb
  · rintro a ⟨c, hc, ha⟩; exact (h c hc).2.2.2.1 a ha
  · rintro a ⟨c, hc, ha⟩; exact (h c hc).2.2.2.2 a ha

/-! ## The least analysis result -/

/-- The meet of every analysis result of `(Γ, s₀)`. -/
def Labeling.least [Abstract] (Γ : Env) (s₀ : Stmt) : Labeling := fun st =>
  AConf.inf (fun c => ∃ L, AnalysisResult Γ s₀ L ∧ c = L st)

/-- `least` lies below every analysis result. -/
theorem Labeling.least_le [Abstract] {Γ : Env} {s₀ : Stmt} {L : Labeling}
    (hL : AnalysisResult Γ s₀ L) : (Labeling.least Γ s₀).Le L :=
  fun _ => AConf.inf_le ⟨L, hL, rfl⟩

/-- A labeling below every analysis result lies below `least`. -/
theorem Labeling.le_least [Abstract] {Γ : Env} {s₀ : Stmt} {M : Labeling}
    (h : ∀ L, AnalysisResult Γ s₀ L → M.Le L) : M.Le (Labeling.least Γ s₀) := by
  intro st
  apply AConf.le_inf
  rintro c ⟨L, hL, rfl⟩
  exact h L hL st

/-- `least` is itself an analysis result. -/
theorem Labeling.least_result [Abstract] (aspec : AbstractSpec) (Γ : Env) (s₀ : Stmt) :
    AnalysisResult Γ s₀ (Labeling.least Γ s₀) := by
  refine ⟨fun a b C ℓ he => ?_, ?_⟩
  · apply AConf.le_inf
    rintro c ⟨L, hL, rfl⟩
    exact AConf.le_trans (he.lmono aspec _ _ (Labeling.least_le hL)) (hL.1 a b C ℓ he)
  · apply AConf.le_inf
    rintro c ⟨L, hL, rfl⟩
    exact hL.2

/-- Every program has a least analysis result. -/
theorem exists_least_analysisResult [Abstract] (aspec : AbstractSpec) (Γ : Env) (s₀ : Stmt) :
    ∃ L, AnalysisResult Γ s₀ L ∧ ∀ L', AnalysisResult Γ s₀ L' → L.Le L' :=
  ⟨_, Labeling.least_result aspec Γ s₀, fun _ hL => Labeling.least_le hL⟩

/-- Every program has a valid labeling — witnessed by its least analysis
    result, not by the trivial `⊤` labeling. -/
theorem exists_valid_labeling [Abstract] (aspec : AbstractSpec) (Γ : Env) (s₀ : Stmt) :
    ∃ L : Labeling, Labeling.Valid Γ s₀ L :=
  ⟨_, (Labeling.least_result aspec Γ s₀).1⟩

/-! ## The fixpoint reading, and Kleene iteration -/

/-- One round of propagation: each state receives the join of every incoming
    edge's contribution, and the top-level entry also the initial
    configuration. -/
def Labeling.step [Abstract] (Γ : Env) (s₀ : Stmt) (L : Labeling) : Labeling := fun b =>
  AConf.sup (fun c => (∃ a C ℓ, AGraph Γ s₀ a b C ℓ ∧ c = C L) ∨
    (b = .entry [] ∧ c = AConf.init s₀))

theorem Labeling.step_mono [Abstract] (aspec : AbstractSpec) {Γ : Env} {s₀ : Stmt}
    {L L' : Labeling} (h : L.Le L') : (Labeling.step Γ s₀ L).Le (Labeling.step Γ s₀ L') := by
  intro b
  apply AConf.sup_le
  rintro c (⟨a, C, ℓ, he, rfl⟩ | ⟨hb, rfl⟩)
  · exact AConf.le_trans (he.lmono aspec _ _ h) (AConf.le_sup (Or.inl ⟨a, C, ℓ, he, rfl⟩))
  · exact AConf.le_sup (Or.inr ⟨hb, rfl⟩)

/-- Analysis results are exactly the post-fixed points of `step`. -/
theorem Labeling.result_iff [Abstract] {Γ : Env} {s₀ : Stmt} {L : Labeling} :
    AnalysisResult Γ s₀ L ↔ (Labeling.step Γ s₀ L).Le L := by
  constructor
  · rintro ⟨hv, hinit⟩ b
    apply AConf.sup_le
    rintro c (⟨a, C, ℓ, he, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hv a b C ℓ he
    · exact hinit
  · intro h
    refine ⟨fun a b C ℓ he => AConf.le_trans (AConf.le_sup (Or.inl ⟨a, C, ℓ, he, rfl⟩)) (h b),
      AConf.le_trans (AConf.le_sup (Or.inr ⟨rfl, rfl⟩)) (h _)⟩

/-- `least` is a fixed point of `step` (the least one, by `least_le` and
    `result_iff`). -/
theorem Labeling.least_fixed [Abstract] (aspec : AbstractSpec) (Γ : Env) (s₀ : Stmt) :
    (Labeling.step Γ s₀ (Labeling.least Γ s₀)).Le (Labeling.least Γ s₀) ∧
      (Labeling.least Γ s₀).Le (Labeling.step Γ s₀ (Labeling.least Γ s₀)) := by
  have hpost := Labeling.result_iff.1 (Labeling.least_result aspec Γ s₀)
  refine ⟨hpost, Labeling.least_le (Labeling.result_iff.2 ?_)⟩
  exact Labeling.step_mono aspec hpost

/-- The Kleene iterates of `step` from the bottom labeling. -/
def Labeling.kleene [Abstract] (Γ : Env) (s₀ : Stmt) : Nat → Labeling
  | 0     => fun _ => AConf.bot
  | n + 1 => Labeling.step Γ s₀ (Labeling.kleene Γ s₀ n)

/-- The iterates form an ascending chain. -/
theorem Labeling.kleene_ascending [Abstract] (aspec : AbstractSpec) (Γ : Env) (s₀ : Stmt) :
    ∀ n, (Labeling.kleene Γ s₀ n).Le (Labeling.kleene Γ s₀ (n + 1))
  | 0     => fun _ => AConf.bot_le _
  | n + 1 => Labeling.step_mono aspec (Labeling.kleene_ascending aspec Γ s₀ n)

/-- Every iterate lies below the least analysis result. -/
theorem Labeling.kleene_le_least [Abstract] (aspec : AbstractSpec) (Γ : Env) (s₀ : Stmt) :
    ∀ n, (Labeling.kleene Γ s₀ n).Le (Labeling.least Γ s₀)
  | 0     => fun _ => AConf.bot_le _
  | n + 1 => (Labeling.step_mono aspec (Labeling.kleene_le_least aspec Γ s₀ n)).trans
      (Labeling.least_fixed aspec Γ s₀).1

/-- An iterate that is a post-fixed point is an analysis result, and is
    `least` itself (up to the order in both directions). -/
theorem Labeling.kleene_stable [Abstract] (aspec : AbstractSpec) {Γ : Env} {s₀ : Stmt}
    {n : Nat} (h : (Labeling.step Γ s₀ (Labeling.kleene Γ s₀ n)).Le (Labeling.kleene Γ s₀ n)) :
    AnalysisResult Γ s₀ (Labeling.kleene Γ s₀ n) ∧
      (Labeling.kleene Γ s₀ n).Le (Labeling.least Γ s₀) ∧
      (Labeling.least Γ s₀).Le (Labeling.kleene Γ s₀ n) :=
  ⟨Labeling.result_iff.2 h, Labeling.kleene_le_least aspec Γ s₀ n,
    Labeling.least_le (Labeling.result_iff.2 h)⟩

/-! ## The least result keeps functions' locations reserved -/

/-- `c` with every value that would break `AConf.FidReserved` removed. -/
def AConf.restrictFid [Abstract] (c : AConf) : AConf where
  heap :=
    { obj := c.heap.obj
      val := fun a =>
        .vals (fun v => (c.heap.val a).Mem v ∧ ∀ f, a = litLocA (.fid f) → v = .fid f) }
  sto := c.sto
  reg := c.reg

theorem AConf.restrictFid_le [Abstract] (c : AConf) : c.restrictFid ⊑ c :=
  ⟨⟨fun _ _ _ h => h, fun _ _ h => h.1⟩, fun _ _ h => h, fun _ _ h => h, fun _ h => h,
    fun _ h => h⟩

theorem AConf.le_restrictFid [Abstract] {c d : AConf} (h : c ⊑ d) (hc : c.FidReserved) :
    c ⊑ d.restrictFid :=
  ⟨⟨h.1.1, fun a v hv => ⟨h.1.2 a v hv, fun f ha => hc f v (ha ▸ hv)⟩⟩, h.2.1, h.2.2⟩

theorem AConf.restrictFid_fidReserved [Abstract] (c : AConf) : c.restrictFid.FidReserved :=
  fun f _ hv => hv.2 f rfl

/-- Every label of the least analysis result keeps each function's canonical
    location holding at most that function. -/
theorem Labeling.least_fidReserved [Abstract] (aspec : AbstractSpec) (Γ : Env) (s₀ : Stmt)
    (st : AState) : (Labeling.least Γ s₀ st).FidReserved := by
  let L' : Labeling := fun st' => (Labeling.least Γ s₀ st').restrictFid
  have hL'le : L'.Le (Labeling.least Γ s₀) := fun st => AConf.restrictFid_le _
  have hL'res : ∀ st, (L' st).FidReserved := fun st => AConf.restrictFid_fidReserved _
  have hres : AnalysisResult Γ s₀ L' := by
    have hleast := Labeling.least_result aspec Γ s₀
    refine ⟨fun a b C ℓ he => ?_, ?_⟩
    · exact AConf.le_restrictFid
        (AConf.le_trans (he.lmono aspec _ _ hL'le) (hleast.1 a b C ℓ he))
        (he.fidReserved aspec hL'res)
    · exact AConf.le_restrictFid hleast.2 (AConf.FidReserved.init aspec s₀)
  intro f v hv
  exact (hL'res st) f v ((Labeling.least_le hres st).1.2 _ v hv)

end CoreJS
