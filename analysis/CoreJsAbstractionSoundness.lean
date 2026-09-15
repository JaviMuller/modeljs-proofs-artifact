/-
  # Core JavaScript — Soundness of the Static Analysis

  Theorem B15: every concrete execution is `α`-related to the abstract
  analysis of the same statement, provided the initial states are related.

  ## Status

  This file is **incomplete**.  What is proved here is the infrastructure that
  the paper's proof leaves implicit, plus the base cases; the remaining cases
  are marked `sorry` and listed under "Remaining work" at the end.  Nothing
  below is assumed: there are no `axiom`s, so every `sorry` is visible.

  ## The two things the paper's proof does not address

  1. **`[Weakening]`.**  The printed proof of Theorem B15 (Appendix B.2.2)
     never mentions the rule.  Each case reads "from H2 and the definitions in
     B7, it follows that ...", which is only valid if `H2`'s outermost rule is
     the one matching the shape of `s`.  It need not be: `[Weakening]` applies
     at every statement.  The generation lemmas below (`abs_gen_*`) absorb any
     number of outer weakenings, which is what makes that step legitimate.

  2. **Summary validity.**  `[Call-Assume]` consumes a summary from `Σ`
     without re-deriving it.  Soundness therefore holds only relative to `Σ`
     being sound, and `[Call-Fix]` must be shown to preserve that when it
     extends `Σ`.  This is the assume/guarantee obligation; it has no
     counterpart in the paper, which has no recursion rule.
-/

import CoreJsAbstractionRelation

namespace CoreJS

/-! ## Supporting order, monotonicity and finiteness results

Properties that are not needed for the soundness statement itself but that its
proof leans on (or that are worth having on record):

* `⊑` is a preorder on the domains introduced for the multi-target call and
  for recursion — actions, outcomes and traces.  The corresponding results
  for heaps, stores and registers are already in `CoreJsAbstractSyntax`.
* Substitution and unfolding laws for `μ`-traces.
* Monotonicity of abstract evaluation, needed because `[Weakening]` runs the
  underlying rule in a *larger* state than its conclusion mentions.
* The ascending chain condition, which is what guarantees that a fixpoint
  search for `[Call-Fix]` terminates.
-/

/-! ### Componentwise order on argument lists -/

theorem ALocSets.Le.refl : ∀ Ls : List ALocSet, ALocSets.Le Ls Ls
  | []      => trivial
  | L :: Ls => ⟨ALocSet.subset_refl L, ALocSets.Le.refl Ls⟩

theorem ALocSets.Le.trans :
    ∀ {Ls Ms Ns : List ALocSet}, ALocSets.Le Ls Ms → ALocSets.Le Ms Ns → ALocSets.Le Ls Ns
  | [],      [],      [],      _,  _  => trivial
  | [],      [],      _ :: _,  _,  h₂ => h₂.elim
  | [],      _ :: _,  _,       h₁, _  => h₁.elim
  | _ :: _,  [],      _,       h₁, _  => h₁.elim
  | _ :: _,  _ :: _,  [],      _,  h₂ => h₂.elim
  | _ :: _, _ :: _, _ :: _, h₁, h₂ =>
      ⟨ALocSet.subset_trans _ _ _ h₁.1 h₂.1, ALocSets.Le.trans h₁.2 h₂.2⟩

/-! ### `⊑` is a preorder on actions -/

theorem AAct.le_refl (a : AAct) : a ⊑ a := by
  cases a with
  | lookup L₁ L₂ L₃ =>
      exact ⟨ALocSet.subset_refl L₁, ALocSet.subset_refl L₂, ALocSet.subset_refl L₃⟩
  | update L₁ L₂ L₃ =>
      exact ⟨ALocSet.subset_refl L₁, ALocSet.subset_refl L₂, ALocSet.subset_refl L₃⟩
  | call al_f Ls => exact ⟨rfl, ALocSets.Le.refl Ls⟩
  | ret al_f L   => exact ⟨rfl, ALocSet.subset_refl L⟩

theorem AAct.le_trans : ∀ {a b c : AAct}, a ⊑ b → b ⊑ c → a ⊑ c := by
  intro a b c h₁ h₂
  cases a <;> cases b <;> cases c <;>
    simp only [LE.le, AAct.Le] at h₁ h₂ ⊢ <;>
    first
      | exact h₁.elim
      | exact h₂.elim
      | exact ⟨ALocSet.subset_trans _ _ _ h₁.1 h₂.1,
               ALocSet.subset_trans _ _ _ h₁.2.1 h₂.2.1,
               ALocSet.subset_trans _ _ _ h₁.2.2 h₂.2.2⟩
      | exact ⟨h₁.1.trans h₂.1, ALocSets.Le.trans h₁.2 h₂.2⟩
      | exact ⟨h₁.1.trans h₂.1, ALocSet.subset_trans _ _ _ h₁.2 h₂.2⟩

/-! ### `⊑` is a preorder on outcomes

Recall the asymmetry introduced by the return-collecting fix: `r ⊑ ·` holds
(an analysis that says "returns" is refined by one that says "may continue,
and these are the return locations"), while `· ⊑ r` does not. -/

theorem AOut.le_refl (o : AOut) : o ⊑ o := by
  cases o with
  | mk kind locs =>
      cases kind <;> simp only [LE.le, AOut.Le] <;> exact ALocSet.subset_refl _

theorem AOut.le_trans : ∀ {o₁ o₂ o₃ : AOut}, o₁ ⊑ o₂ → o₂ ⊑ o₃ → o₁ ⊑ o₃ := by
  intro o₁ o₂ o₃ h₁ h₂
  cases o₁ with
  | mk k₁ L₁ => cases o₂ with
    | mk k₂ L₂ => cases o₃ with
      | mk k₃ L₃ =>
          cases k₁ <;> cases k₂ <;> cases k₃ <;>
            simp only [LE.le, AOut.Le] at h₁ h₂ ⊢ <;>
            first
              | exact h₁.elim
              | exact h₂.elim
              | exact ALocSet.subset_trans _ _ _ h₁ h₂

/-- `⊑` on `AOut` reduces to inclusion of `locs` whenever the `kind`s agree
    (it can only fail to when a `.cont` on the left meets a `.ret` on the
    right).  Needed by `[Sequence]`: joining `s₁`'s collected return locations
    into `s₂`'s result only grows `s₂`'s own `locs` at a fixed `kind`. -/
theorem AOut.le_of_locs_subset {o o' : AOut} (hk : o.kind = o'.kind)
    (hL : o.locs ⊆ o'.locs) : o ⊑ o' := by
  cases o with
  | mk k L => cases o' with
    | mk k' L' => cases k <;> cases k' <;> first | exact hL | (exfalso; injection hk)

/-- The reverse extraction: `⊑` on `AOut` always gives inclusion of `locs`,
    regardless of `kind` (the `(.cont, .ret)` mismatch makes the hypothesis
    `False`, from which anything follows). -/
theorem AOut.Le.locs_subset {o o' : AOut} (h : o ⊑ o') : o.locs ⊆ o'.locs := by
  cases o with
  | mk k L => cases o' with
    | mk k' L' => cases k <;> cases k' <;> first | exact h | exact h.elim

/-! ### `⊑` is a preorder on traces -/

theorem ATrc.le_refl (t : ATrc) : t ⊑ t := by
  induction t with
  | emp => exact trivial
  | act a => exact AAct.le_refl a
  | seq t₁ t₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | alt t₁ t₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | star t₁ ih => exact ih
  | tvar => exact trivial
  | mu t₁ ih => exact ih

theorem ATrc.le_trans : ∀ {t u v : ATrc}, t ⊑ u → u ⊑ v → t ⊑ v := by
  intro t
  induction t with
  | emp =>
      intro u v h₁ h₂
      cases u <;> cases v <;>
        first | exact trivial | exact h₁.elim | exact h₂.elim
  | act a =>
      intro u v h₁ h₂
      cases u <;> cases v <;>
        first | exact AAct.le_trans h₁ h₂ | exact h₁.elim | exact h₂.elim
  | seq t₁ t₂ ih₁ ih₂ =>
      intro u v h₁ h₂
      cases u <;> cases v <;>
        first | exact ⟨ih₁ h₁.1 h₂.1, ih₂ h₁.2 h₂.2⟩ | exact h₁.elim | exact h₂.elim
  | alt t₁ t₂ ih₁ ih₂ =>
      intro u v h₁ h₂
      cases u <;> cases v <;>
        first | exact ⟨ih₁ h₁.1 h₂.1, ih₂ h₁.2 h₂.2⟩ | exact h₁.elim | exact h₂.elim
  | star t₁ ih =>
      intro u v h₁ h₂
      cases u <;> cases v <;>
        first | exact ih h₁ h₂ | exact h₁.elim | exact h₂.elim
  | tvar =>
      intro u v h₁ h₂
      cases u <;> cases v <;>
        first | exact trivial | exact h₁.elim | exact h₂.elim
  | mu t₁ ih =>
      intro u v h₁ h₂
      cases u <;> cases v <;>
        first | exact ih h₁ h₂ | exact h₁.elim | exact h₂.elim

/-! ### Substitution laws for `μ`-traces -/

/-- Substituting the recursion variable in a trace that does not contain one
    changes nothing. -/
def ATrc.Closed : ATrc → Prop
  | .emp       => True
  | .act _     => True
  | .seq t₁ t₂ => t₁.Closed ∧ t₂.Closed
  | .alt t₁ t₂ => t₁.Closed ∧ t₂.Closed
  | .star t    => t.Closed
  | .tvar      => False
  | .mu _      => True

theorem ATrc.subst_closed : ∀ {t : ATrc}, t.Closed → ∀ u, t.subst u = t
  | .emp,       _, _ => rfl
  | .act _,     _, _ => rfl
  | .seq t₁ t₂, h, u => by
      simp [ATrc.subst, ATrc.subst_closed h.1 u, ATrc.subst_closed h.2 u]
  | .alt t₁ t₂, h, u => by
      simp [ATrc.subst, ATrc.subst_closed h.1 u, ATrc.subst_closed h.2 u]
  | .star t,    h, u => by
      show ATrc.star (t.subst u) = ATrc.star t
      rw [ATrc.subst_closed (t := t) h u]
  | .tvar,      h, _ => h.elim
  | .mu _,      _, _ => rfl

/-! ### Monotonicity of abstract evaluation

Needed by every generation lemma whose rule reads the store: `[Weakening]`
runs the underlying rule in a *larger* state, so the value it computes must
dominate the one computed in the smaller state. -/

theorem aevalE_mono [Abstract] {ρ ρ' : ASto} (h : ρ ⊑ ρ') (e : Expr) :
    aevalE ρ e ⊆ aevalE ρ' e := by
  cases e with
  | val v => exact ALocSet.subset_refl _
  | var x => exact h x

theorem aevalEs_mono [Abstract] {ρ ρ' : ASto} (h : ρ ⊑ ρ') :
    ∀ es : List Expr, ALocSets.Le (aevalEs ρ es) (aevalEs ρ' es)
  | []      => trivial
  | e :: es => ⟨aevalE_mono h e, aevalEs_mono h es⟩

theorem ASto.upd_mono [Abstract] {ρ ρ' : ASto} {L L' : ALocSet} (hρ : ρ ⊑ ρ')
    (hL : L ⊆ L') (x : Var) : ρ.upd x L ⊑ ρ'.upd x L' := by
  intro y
  show (if y = x then L else ρ y) ⊆ (if y = x then L' else ρ' y)
  by_cases hy : y = x
  · rw [if_pos hy, if_pos hy]; exact hL
  · rw [if_neg hy, if_neg hy]; exact hρ y

/-- Needed by the `[Lookup]`/`[Update]` generation lemmas: `[Weakening]` grows
    the heap too, so the property read out of it must grow along with it. -/
theorem AHeap.objOf_mono [Abstract] {h h' : AHeap} {L L' : ALocSet} {p : PropName}
    (hh : h ⊑ h') (hL : L ⊆ L') : h.objOf L p ⊆ h'.objOf L' p := by
  rintro l' ⟨l, hLl, hobj⟩
  exact ⟨l, hL l hLl, hh.1 l p l' hobj⟩

theorem AHeap.valOf_mono [Abstract] {h h' : AHeap} {L L' : ALocSet}
    (hh : h ⊑ h') (hL : L ⊆ L') : h.valOf L ⊑ h'.valOf L' := by
  rintro v ⟨l, hLl, hmem⟩
  exact ⟨l, hL l hLl, hh.2 l v hmem⟩

theorem AHeap.objOfV_mono [Abstract] {h h' : AHeap} {L L' : ALocSet} {V V' : VSet}
    (hh : h ⊑ h') (hL : L ⊆ L') (hV : V ⊑ V') : h.objOfV L V ⊆ h'.objOfV L' V' := by
  rintro l' ⟨l, p, hLl, hVp, hobj⟩
  exact ⟨l, p, hL l hLl, hV _ hVp, hh.1 l p l' hobj⟩

/-! ### Termination of the fixpoint search

REMARK.  There is no *algorithm* in this development to prove terminating:
`ABigStep` is a relation, and `[Call-Fix]` requires only that *some* valid
post-fixed point exist.  A non-terminating search would therefore fail to find
a derivation rather than produce an unsound one, so soundness does not depend
on any of this.

What does bear on termination of a fixpoint *search* is the ascending chain
condition on the abstract domains, which holds because the abstract location
space is finite (one location per allocation site — `AbstractSpec.allocA_site`)
and the value domain has finite height (`⊤` absorbs once the widening
threshold is exceeded).  Stated with the finiteness made explicit: -/

/-- The abstract location space is finite: some list enumerates it. -/
class AFinite (ALoc : Type) where
  enum : List ALoc
  complete : ∀ l, l ∈ enum

/-- An ascending chain of abstract heaps. -/
def AscendingHeap (c : Nat → AHeap) : Prop := ∀ n, c n ⊑ c (n + 1)

/-- Chains are monotone at every distance, not just adjacent indices — the
    part of the ACC argument that holds with no finiteness assumption at all. -/
theorem AscendingHeap.le_of_le {c : Nat → AHeap} (hc : AscendingHeap c) :
    ∀ {m n : Nat}, m ≤ n → c m ⊑ c n := by
  intro m n hmn
  induction n with
  | zero =>
      have : m = 0 := Nat.le_zero.mp hmn
      subst this
      exact AHeap.le_refl _
  | succ k ih =>
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · exact AHeap.le_trans _ _ _ (ih (Nat.lt_succ_iff.mp hlt)) (hc k)
      · have : m = k + 1 := Nat.le_antisymm hmn hge
        subst this
        exact AHeap.le_refl _

/-! ## Summary validity (the assume/guarantee invariant) -/

/-- `Σ` is *valid* when every summary it assumes really does over-approximate
    every concrete execution of that function: starting from any concrete state
    related to the summary's input, the function's result is related to the
    summary's output.

    `[Call-Assume]` is sound exactly under this hypothesis, and `[Call-Fix]`
    must re-establish it for `Σ[f ↦ s]` from its post-fixed-point premises. -/
def SigmaValid [Concrete] [Abstract] (Γ : Env) (Sg : ASigma) (n : Nat) : Prop :=
  ∀ f sm, Sg f = some sm →
    ∀ (α : AlphaFn) m h ρf δ h' ρf' δ' t l,
      m ≤ n →
      α.Lits →
      BigStepN Γ m ⟨h, ρf, δ⟩ (Γ.body f) ⟨h', ρf', δ', t, .ret l⟩ →
      Heap.Alpha α h sm.heap →
      Reg.Alpha α δ sm.reg →
      ∃ α' : AlphaFn, α' ≥α α ∧ α'.Lits ∧
        Heap.Alpha α' h' sm.heap ∧ Reg.Alpha α' δ' sm.reg ∧
        α'.MapsInto l sm.ret

/-- Validity at a smaller height is implied by validity at a larger one. -/
theorem SigmaValid.le [Concrete] [Abstract] {Γ Sg n m} (hnm : m ≤ n)
    (h : SigmaValid Γ Sg n) : SigmaValid Γ Sg m := by
  intro f sm hf α k hh ρf δ h' ρf' δ' t l hk
  exact h f sm hf α k hh ρf δ h' ρf' δ' t l (Nat.le_trans hk hnm)

theorem SigmaValid.empty [Concrete] [Abstract] (Γ : Env) (n : Nat) :
    SigmaValid Γ ASigma.empty n := by
  intro f sm hf
  exact absurd hf (by simp [ASigma.empty])

/-! ## Generation lemmas

Each of these inverts an abstract derivation for one statement shape, absorbing
any outer `[Weakening]`s into the order relations of its conclusion.  They are
proved by induction on the derivation: in the `weaken` case the inductive
hypothesis supplies the inner conclusion and transitivity of `⊑` extends it
through the surrounding weakening. -/

/-- `[Skip]`, inverted.  Any derivation for `skip` — however many weakenings
    surround it — leaves the state below its own output, emits a trace above
    `ε̂`, and an outcome above `⟨·, ∅⟩`. -/
theorem abs_gen_skip [Abstract] {Γ : Env} {Sg : ASigma} {c : AConf} {r : ARes}
    (H : ABigStep Γ Sg c .skip r) :
    c.heap ⊑ r.heap ∧ c.sto ⊑ r.sto ∧ c.reg ⊑ r.reg ∧
      (ATrc.emp ⊑ r.trc) ∧ (AOut.mk .cont ∅ ⊑ r.out) := by
  generalize hs : (Stmt.skip) = st at H
  induction H using ABigStep.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ => True)
  case skip =>
      exact ⟨AHeap.le_refl _, ASto.le_refl _, AReg.le_refl _,
             ATrc.le_refl _, AOut.le_refl _⟩
  case weaken hh hρ hδ _ hh' hρ' hδ' ht ho ih =>
      obtain ⟨k1, k2, k3, k4, k5⟩ := ih hs
      exact ⟨AHeap.le_trans _ _ _ hh (AHeap.le_trans _ _ _ k1 hh'),
             ASto.le_trans _ _ _ hρ (ASto.le_trans _ _ _ k2 hρ'),
             AReg.le_trans _ _ _ hδ (AReg.le_trans _ _ _ k3 hδ'),
             ATrc.le_trans k4 ht,
             AOut.le_trans k5 ho⟩
  all_goals first | trivial | exact absurd hs (by simp)

/-- `[Assignment]`, inverted. Absorbs any outer weakenings. -/
theorem abs_gen_assign [Abstract] {Γ : Env} {Sg : ASigma} {c : AConf} {r : ARes}
    {x : Var} {e : Expr}
    (H : ABigStep Γ Sg c (.assign x e) r) :
    c.heap ⊑ r.heap ∧
    (c.sto.upd x (aevalE c.sto e)) ⊑ r.sto ∧
    c.reg ⊑ r.reg ∧
    (ATrc.emp ⊑ r.trc) ∧ (AOut.mk .cont ∅ ⊑ r.out) := by
  generalize hs : (Stmt.assign x e) = st at H
  induction H using ABigStep.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ => True)
  case assign h ρ ρ' δ y e' L he hρ' =>
      cases hs
      subst he hρ'
      exact ⟨AHeap.le_refl _, ASto.le_refl _, AReg.le_refl _,
             ATrc.le_refl _, AOut.le_refl _⟩
  case weaken hh hρ hδ _ hh' hρ' hδ' ht ho ih =>
      obtain ⟨k1, k2, k3, k4, k5⟩ := ih hs
      have hupd : (ASto.upd _ x (aevalE _ e)) ⊑ (ASto.upd _ x (aevalE _ e)) :=
        ASto.upd_mono hρ (aevalE_mono hρ e) x
      exact ⟨AHeap.le_trans _ _ _ hh (AHeap.le_trans _ _ _ k1 hh'),
             ASto.le_trans _ _ _ hupd (ASto.le_trans _ _ _ k2 hρ'),
             AReg.le_trans _ _ _ hδ (AReg.le_trans _ _ _ k3 hδ'),
             ATrc.le_trans k4 ht,
             AOut.le_trans k5 ho⟩
  all_goals first | trivial | exact absurd hs (by simp)

/-- `[Return]`, inverted. Absorbs any outer weakenings. -/
theorem abs_gen_ret [Abstract] {Γ : Env} {Sg : ASigma} {c : AConf} {r : ARes}
    {e : Expr}
    (H : ABigStep Γ Sg c (.ret e) r) :
    c.heap ⊑ r.heap ∧
    c.sto ⊑ r.sto ∧
    c.reg ⊑ r.reg ∧
    (ATrc.emp ⊑ r.trc) ∧ (AOut.mk .ret (aevalE c.sto e) ⊑ r.out) := by
  generalize hs : (Stmt.ret e) = st at H
  induction H using ABigStep.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ => True)
  case ret h ρ δ e' L he =>
      cases hs
      subst he
      exact ⟨AHeap.le_refl _, ASto.le_refl _, AReg.le_refl _,
             ATrc.le_refl _, AOut.le_refl _⟩
  case weaken hh hρ hδ _ hh' hρ' hδ' ht ho ih =>
      obtain ⟨k1, k2, k3, k4, k5⟩ := ih hs
      have hout : AOut.Le (AOut.mk .ret (aevalE _ e)) (AOut.mk .ret (aevalE _ e)) :=
        aevalE_mono hρ e
      exact ⟨AHeap.le_trans _ _ _ hh (AHeap.le_trans _ _ _ k1 hh'),
             ASto.le_trans _ _ _ hρ (ASto.le_trans _ _ _ k2 hρ'),
             AReg.le_trans _ _ _ hδ (AReg.le_trans _ _ _ k3 hδ'),
             ATrc.le_trans k4 ht,
             AOut.le_trans (AOut.le_trans hout k5) ho⟩
  all_goals first | trivial | exact absurd hs (by simp)

/-- `[SetTaint]`, inverted. Absorbs any outer weakenings.

    `dep` and `sk` are untouched by the rule, so one might expect to relate
    them to `aδ'` by equality; but `[Weakening]`'s input side only gives
    `c.reg ⊑` the state the underlying rule actually ran in, so only the
    inclusion survives once any outer weakenings are absorbed — equality
    would be false whenever `H` is not literally `[SetTaint]` itself. -/
theorem abs_gen_setTaint [Abstract] {Γ : Env} {Sg : ASigma} {c : AConf} {r : ARes}
    {e : Expr}
    (H : ABigStep Γ Sg c (.setTaint e) r) :
    ∃ aδ' : AReg,
      c.heap ⊑ r.heap ∧
      c.sto ⊑ r.sto ∧
      aδ' ⊑ r.reg ∧
      (∀ l, c.reg.dep l ⊆ aδ'.dep l) ∧
      c.reg.sk ⊆ aδ'.sk ∧
      (aevalE c.sto e ∪ c.reg.ac) ⊆ aδ'.ac ∧
      (ATrc.emp ⊑ r.trc) ∧ (AOut.mk .cont ∅ ⊑ r.out) := by
  generalize hs : (Stmt.setTaint e) = st at H
  induction H using ABigStep.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ => True)
  case setTaint h ρ δ δ' e' L he hδ' =>
      cases hs
      subst he hδ'
      refine ⟨{ δ with ac := aevalE ρ e ∪ δ.ac },
              AHeap.le_refl _, ASto.le_refl _, AReg.le_refl _,
              fun l => ALocSet.subset_refl _, ALocSet.subset_refl _, ALocSet.subset_refl _,
              ATrc.le_refl _, AOut.le_refl _⟩
  case weaken hh hρ hδ _ hh' hρ' hδ' ht ho ih =>
      obtain ⟨aδ', k1, k2, k3, kdep, ksk, kac, k4, k5⟩ := ih hs
      refine ⟨aδ',
              AHeap.le_trans _ _ _ hh (AHeap.le_trans _ _ _ k1 hh'),
              ASto.le_trans _ _ _ hρ (ASto.le_trans _ _ _ k2 hρ'),
              AReg.le_trans _ _ _ k3 hδ',
              fun l => ALocSet.subset_trans _ _ _ (hδ.1 l) (kdep l),
              ALocSet.subset_trans _ _ _ hδ.2.2 ksk,
              ALocSet.union_subset _ _ _
                (ALocSet.subset_trans _ _ _ (aevalE_mono hρ e) (ALocSet.subset_trans _ _ _ (ALocSet.subset_union_left _ _) kac))
                (ALocSet.subset_trans _ _ _ hδ.2.1 (ALocSet.subset_trans _ _ _ (ALocSet.subset_union_right _ _) kac)),
              ATrc.le_trans k4 ht,
              AOut.le_trans k5 ho⟩
  all_goals first | trivial | exact absurd hs (by simp)

/-- `[SetSink]`, inverted. Absorbs any outer weakenings.

    Same inclusion-not-equality caveat as `abs_gen_setTaint`, for `dep`/`ac`. -/
theorem abs_gen_setSink [Abstract] {Γ : Env} {Sg : ASigma} {c : AConf} {r : ARes}
    {e : Expr}
    (H : ABigStep Γ Sg c (.setSink e) r) :
    ∃ aδ' : AReg,
      c.heap ⊑ r.heap ∧
      c.sto ⊑ r.sto ∧
      aδ' ⊑ r.reg ∧
      (∀ l, c.reg.dep l ⊆ aδ'.dep l) ∧
      c.reg.ac ⊆ aδ'.ac ∧
      (aevalE c.sto e ∪ c.reg.sk) ⊆ aδ'.sk ∧
      (ATrc.emp ⊑ r.trc) ∧ (AOut.mk .cont ∅ ⊑ r.out) := by
  generalize hs : (Stmt.setSink e) = st at H
  induction H using ABigStep.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ => True)
  case setSink h ρ δ δ' e' L he hδ' =>
      cases hs
      subst he hδ'
      refine ⟨{ δ with sk := aevalE ρ e ∪ δ.sk },
              AHeap.le_refl _, ASto.le_refl _, AReg.le_refl _,
              fun l => ALocSet.subset_refl _, ALocSet.subset_refl _, ALocSet.subset_refl _,
              ATrc.le_refl _, AOut.le_refl _⟩
  case weaken hh hρ hδ _ hh' hρ' hδ' ht ho ih =>
      obtain ⟨aδ', k1, k2, k3, kdep, kac, ksk, k4, k5⟩ := ih hs
      refine ⟨aδ',
              AHeap.le_trans _ _ _ hh (AHeap.le_trans _ _ _ k1 hh'),
              ASto.le_trans _ _ _ hρ (ASto.le_trans _ _ _ k2 hρ'),
              AReg.le_trans _ _ _ k3 hδ',
              fun l => ALocSet.subset_trans _ _ _ (hδ.1 l) (kdep l),
              ALocSet.subset_trans _ _ _ hδ.2.1 kac,
              ALocSet.union_subset _ _ _
                (ALocSet.subset_trans _ _ _ (aevalE_mono hρ e) (ALocSet.subset_trans _ _ _ (ALocSet.subset_union_left _ _) ksk))
                (ALocSet.subset_trans _ _ _ hδ.2.2 (ALocSet.subset_trans _ _ _ (ALocSet.subset_union_right _ _) ksk)),
              ATrc.le_trans k4 ht,
              AOut.le_trans k5 ho⟩
  all_goals first | trivial | exact absurd hs (by simp)

/-- `[Sequence]`, inverted.  Absorbs any outer weakenings.

    `[Sequence Ret]` and `[Sequence Cont]` are two different constructors for
    the same statement shape, so the generation lemma has to invert into a
    disjunction rather than a single tuple: either `s₁` alone already produced
    the whole result (as a `.ret`), or `s₁` continued and `s₂` ran from where
    it left off. -/
theorem abs_gen_seq [Abstract] {Γ : Env} {Sg : ASigma} {c : AConf} {r : ARes}
    {s₁ s₂ : Stmt}
    (H : ABigStep Γ Sg c (.seq s₁ s₂) r) :
    ∃ r₁ : ARes, ABigStep Γ Sg c s₁ r₁ ∧
      ( (r₁.out.kind = .ret ∧
          r₁.heap ⊑ r.heap ∧ r₁.sto ⊑ r.sto ∧ r₁.reg ⊑ r.reg ∧
          r₁.trc ⊑ r.trc ∧ r₁.out ⊑ r.out)
      ∨ (r₁.out.kind = .cont ∧
          ∃ r₂ : ARes, ABigStep Γ Sg ⟨r₁.heap, r₁.sto, r₁.reg⟩ s₂ r₂ ∧
            r₂.heap ⊑ r.heap ∧ r₂.sto ⊑ r.sto ∧ r₂.reg ⊑ r.reg ∧
            (r₁.trc ;; r₂.trc) ⊑ r.trc ∧
            (AOut.mk r₂.out.kind (r₁.out.locs ∪ r₂.out.locs)) ⊑ r.out) ) := by
  generalize hs : (Stmt.seq s₁ s₂) = st at H
  induction H using ABigStep.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ => True)
  case seqRet hstep _ih =>
      cases hs
      exact ⟨_, hstep, Or.inl ⟨rfl,
        AHeap.le_refl _, ASto.le_refl _, AReg.le_refl _, ATrc.le_refl _, AOut.le_refl _⟩⟩
  case seqCont hstep1 hstep2 _ih1 _ih2 =>
      cases hs
      exact ⟨_, hstep1, Or.inr ⟨rfl, _, hstep2,
        AHeap.le_refl _, ASto.le_refl _, AReg.le_refl _, ATrc.le_refl _, AOut.le_refl _⟩⟩
  case weaken hh hρ hδ _ hh' hρ' hδ' ht ho ih =>
      obtain ⟨r1, hstep1, hdisj⟩ := ih hs
      refine ⟨r1,
        ABigStep.weaken hh hρ hδ hstep1
          (AHeap.le_refl _) (ASto.le_refl _) (AReg.le_refl _) (ATrc.le_refl _) (AOut.le_refl _),
        ?_⟩
      rcases hdisj with ⟨hkind, k1, k2, k3, k4, k5⟩ | ⟨hkind, r2, hstep2, k1, k2, k3, k4, k5⟩
      · exact Or.inl ⟨hkind,
          AHeap.le_trans _ _ _ k1 hh', ASto.le_trans _ _ _ k2 hρ', AReg.le_trans _ _ _ k3 hδ',
          ATrc.le_trans k4 ht, AOut.le_trans k5 ho⟩
      · exact Or.inr ⟨hkind, r2, hstep2,
          AHeap.le_trans _ _ _ k1 hh', ASto.le_trans _ _ _ k2 hρ', AReg.le_trans _ _ _ k3 hδ',
          ATrc.le_trans k4 ht, AOut.le_trans k5 ho⟩
  all_goals first | trivial | exact absurd hs (by simp)

/-- `[Static Property Lookup]`, inverted. Absorbs any outer weakenings. -/
theorem abs_gen_lookupS [Abstract] {Γ : Env} {Sg : ASigma} {c : AConf} {r : ARes}
    {x : Var} {e : Expr} {p : PropName}
    (H : ABigStep Γ Sg c (.lookupS x e p) r) :
    c.heap ⊑ r.heap ∧
    (c.sto.upd x (c.heap.objOf (aevalE c.sto e) p)) ⊑ r.sto ∧
    c.reg ⊑ r.reg ∧
    (ATrc.act (.lookup (c.heap.objOf (aevalE c.sto e) p) (aevalE c.sto e)
        {Abstract.litLocA (.str p)})) ⊑ r.trc ∧
    (AOut.mk .cont ∅ ⊑ r.out) := by
  generalize hs : (Stmt.lookupS x e p) = st at H
  induction H using ABigStep.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ => True)
  case lookupS h ρ ρ' δ x' e' p' L1 L2 he hL2 hρ' =>
      cases hs
      subst he hL2 hρ'
      exact ⟨AHeap.le_refl _, ASto.le_refl _, AReg.le_refl _,
             ATrc.le_refl _, AOut.le_refl _⟩
  case weaken hh hρ hδ _ hh' hρ' hδ' ht ho ih =>
      obtain ⟨k1, k2, k3, k4, k5⟩ := ih hs
      have hobj_mono : (AHeap.objOf _ (aevalE _ e) p) ⊆ (AHeap.objOf _ (aevalE _ e) p) :=
        AHeap.objOf_mono hh (aevalE_mono hρ e)
      have hupd_mono : (ASto.upd _ x (AHeap.objOf _ (aevalE _ e) p)) ⊑
          (ASto.upd _ x (AHeap.objOf _ (aevalE _ e) p)) :=
        ASto.upd_mono hρ hobj_mono x
      have htrc_mono : ATrc.Le
          (.act (.lookup (AHeap.objOf _ (aevalE _ e) p) (aevalE _ e) {Abstract.litLocA (.str p)}))
          (.act (.lookup (AHeap.objOf _ (aevalE _ e) p) (aevalE _ e) {Abstract.litLocA (.str p)})) :=
        ⟨hobj_mono, aevalE_mono hρ e, ALocSet.subset_refl _⟩
      exact ⟨AHeap.le_trans _ _ _ hh (AHeap.le_trans _ _ _ k1 hh'),
             ASto.le_trans _ _ _ hupd_mono (ASto.le_trans _ _ _ k2 hρ'),
             AReg.le_trans _ _ _ hδ (AReg.le_trans _ _ _ k3 hδ'),
             ATrc.le_trans htrc_mono (ATrc.le_trans k4 ht),
             AOut.le_trans k5 ho⟩
  all_goals first | trivial | exact absurd hs (by simp)

/-- `[Dynamic Property Lookup]`, inverted. Absorbs any outer weakenings. -/
theorem abs_gen_lookupD [Abstract] {Γ : Env} {Sg : ASigma} {c : AConf} {r : ARes}
    {x : Var} {e₁ e₂ : Expr}
    (H : ABigStep Γ Sg c (.lookupD x e₁ e₂) r) :
    c.heap ⊑ r.heap ∧
    (c.sto.upd x (c.heap.objOfV (aevalE c.sto e₁) (c.heap.valOf (aevalE c.sto e₂)))) ⊑ r.sto ∧
    c.reg ⊑ r.reg ∧
    (ATrc.act (.lookup
        (c.heap.objOfV (aevalE c.sto e₁) (c.heap.valOf (aevalE c.sto e₂)))
        (aevalE c.sto e₁) (aevalE c.sto e₂))) ⊑ r.trc ∧
    (AOut.mk .cont ∅ ⊑ r.out) := by
  generalize hs : (Stmt.lookupD x e₁ e₂) = st at H
  induction H using ABigStep.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ => True)
  case lookupD h ρ ρ' δ x' e₁' e₂' L1 L2 L3 V he1 he2 hV hL3 hρ' =>
      cases hs
      subst he1 he2 hV hL3 hρ'
      exact ⟨AHeap.le_refl _, ASto.le_refl _, AReg.le_refl _,
             ATrc.le_refl _, AOut.le_refl _⟩
  case weaken hh hρ hδ _ hh' hρ' hδ' ht ho ih =>
      obtain ⟨k1, k2, k3, k4, k5⟩ := ih hs
      have hval_mono : (AHeap.valOf _ (aevalE _ e₂)) ⊑ (AHeap.valOf _ (aevalE _ e₂)) :=
        AHeap.valOf_mono hh (aevalE_mono hρ e₂)
      have hobjV_mono : (AHeap.objOfV _ (aevalE _ e₁) (AHeap.valOf _ (aevalE _ e₂))) ⊆
          (AHeap.objOfV _ (aevalE _ e₁) (AHeap.valOf _ (aevalE _ e₂))) :=
        AHeap.objOfV_mono hh (aevalE_mono hρ e₁) hval_mono
      have hupd_mono : (ASto.upd _ x (AHeap.objOfV _ (aevalE _ e₁) (AHeap.valOf _ (aevalE _ e₂)))) ⊑
          (ASto.upd _ x (AHeap.objOfV _ (aevalE _ e₁) (AHeap.valOf _ (aevalE _ e₂)))) :=
        ASto.upd_mono hρ hobjV_mono x
      have htrc_mono : ATrc.Le
          (.act (.lookup (AHeap.objOfV _ (aevalE _ e₁) (AHeap.valOf _ (aevalE _ e₂)))
              (aevalE _ e₁) (aevalE _ e₂)))
          (.act (.lookup (AHeap.objOfV _ (aevalE _ e₁) (AHeap.valOf _ (aevalE _ e₂)))
              (aevalE _ e₁) (aevalE _ e₂))) :=
        ⟨hobjV_mono, aevalE_mono hρ e₁, aevalE_mono hρ e₂⟩
      exact ⟨AHeap.le_trans _ _ _ hh (AHeap.le_trans _ _ _ k1 hh'),
             ASto.le_trans _ _ _ hupd_mono (ASto.le_trans _ _ _ k2 hρ'),
             AReg.le_trans _ _ _ hδ (AReg.le_trans _ _ _ k3 hδ'),
             ATrc.le_trans htrc_mono (ATrc.le_trans k4 ht),
             AOut.le_trans k5 ho⟩
  all_goals first | trivial | exact absurd hs (by simp)

/-! ## Theorem B15 (Soundness of the static analysis) -/

/-- Theorem B15, height-indexed form.  Proved by strong induction on the
    height `n` of the concrete derivation; `soundness` below is the corollary
    with the height existentially quantified away.

    The hypothesis `SigmaValid Γ Sg n` is the assume/guarantee side condition:
    `[Call-Assume]` uses a summary without re-deriving it, so the summaries in
    `Σ` must already over-approximate every concrete execution up to the
    current height. -/
theorem soundnessN [Concrete] [Abstract] (cs : ConcreteSpec) (as : AbstractSpec)
    {Γ : Env} :
    ∀ (n : Nat) {Sg : ASigma} {α : AlphaFn} {s : Stmt}
      {c : Conf} {r : Res} {ac : AConf} {ar : ARes},
      α.Lits →
      SigmaValid Γ Sg n →
      BigStepN Γ n c s r →
      ABigStep Γ Sg ac s ar →
      Heap.Alpha α c.heap ac.heap →
      Sto.Alpha α c.sto ac.sto →
      Reg.Alpha α c.reg ac.reg →
      ∃ α' : AlphaFn, α' ≥α α ∧ α'.Lits ∧
        Heap.Alpha α' r.heap ar.heap ∧ Sto.Alpha α' r.sto ar.sto ∧
        Reg.Alpha α' r.reg ar.reg ∧
        Trc.Alpha α' r.trc ar.trc ∧ Out.Alpha α' r.out ar.out := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
    intro Sg α s c r ac ar hlit hval H1 H2 Hh Hρ Hδ
    cases H1
    case skip h ρ δ =>
        -- [Skip].  The concrete state is unchanged, so `α` itself works.  The
        -- abstract side may have been weakened arbitrarily; `abs_gen_skip`
        -- absorbs that into `⊑` and Lemma B13 transports the relation across.
        obtain ⟨k1, k2, k3, k4, k5⟩ := abs_gen_skip H2
        exact ⟨α, AlphaFn.Extends.refl α, hlit,
               Hh.le k1, Hρ.le k2, Hδ.le k3,
               Trc.Alpha.emp.le k4,
               (show Out.Alpha α .cont (AOut.mk .cont ∅) from trivial).le k5⟩
    case assign h ρ ρ' δ x e l he hρ' =>
        subst hρ'
        obtain ⟨k1, k2, k3, k4, k5⟩ := abs_gen_assign H2
        have hval_e := eval_alpha hlit Hρ he
        have hupd := sto_upd_alpha (x := x) Hρ hval_e
        exact ⟨α, AlphaFn.Extends.refl α, hlit,
               Hh.le k1, hupd.le k2, Hδ.le k3,
               Trc.Alpha.emp.le k4,
               (show Out.Alpha α .cont (AOut.mk .cont ∅) from trivial).le k5⟩
    case ret h ρ δ e l he =>
        obtain ⟨k1, k2, k3, k4, k5⟩ := abs_gen_ret H2
        have hval_e := eval_alpha hlit Hρ he
        have ho : Out.Alpha α (.ret l) (AOut.mk .ret (aevalE ac.sto e)) := hval_e
        exact ⟨α, AlphaFn.Extends.refl α, hlit,
               Hh.le k1, Hρ.le k2, Hδ.le k3,
               Trc.Alpha.emp.le k4,
               ho.le k5⟩
    case setTaint h ρ δ δ' e l he hδ' =>
        subst hδ'
        obtain ⟨aδ', k1, k2, k3, kdep, ksk, kac, k4, k5⟩ := abs_gen_setTaint H2
        have hval_e := eval_alpha hlit Hρ he
        have hReg' : Reg.Alpha α { δ with ac := {l} ∪ δ.ac } aδ' := by
          refine ⟨?_, ?_, ?_⟩
          · intro l₁ l₂ hdep
            obtain ⟨a₁, a₂, ha1, ha2, hd⟩ := Hδ.1 l₁ l₂ hdep
            exact ⟨a₁, a₂, ha1, ha2, kdep a₁ a₂ hd⟩
          · intro x hx
            rcases hx with hx | hx
            · subst hx
              exact hval_e.subset
                (ALocSet.subset_trans _ _ _ (ALocSet.subset_union_left _ _) kac)
            · exact (Hδ.2.1 x hx).subset
                (ALocSet.subset_trans _ _ _ (ALocSet.subset_union_right _ _) kac)
          · intro x hx
            exact (Hδ.2.2 x hx).subset ksk
        exact ⟨α, AlphaFn.Extends.refl α, hlit,
               Hh.le k1, Hρ.le k2, hReg'.le k3,
               Trc.Alpha.emp.le k4,
               (show Out.Alpha α .cont (AOut.mk .cont ∅) from trivial).le k5⟩
    case setSink h ρ δ δ' e l he hδ' =>
        subst hδ'
        obtain ⟨aδ', k1, k2, k3, kdep, kac, ksk, k4, k5⟩ := abs_gen_setSink H2
        have hval_e := eval_alpha hlit Hρ he
        have hReg' : Reg.Alpha α { δ with sk := {l} ∪ δ.sk } aδ' := by
          refine ⟨?_, ?_, ?_⟩
          · intro l₁ l₂ hdep
            obtain ⟨a₁, a₂, ha1, ha2, hd⟩ := Hδ.1 l₁ l₂ hdep
            exact ⟨a₁, a₂, ha1, ha2, kdep a₁ a₂ hd⟩
          · intro x hx
            exact (Hδ.2.1 x hx).subset kac
          · intro x hx
            rcases hx with hx | hx
            · subst hx
              exact hval_e.subset
                (ALocSet.subset_trans _ _ _ (ALocSet.subset_union_left _ _) ksk)
            · exact (Hδ.2.2 x hx).subset
                (ALocSet.subset_trans _ _ _ (ALocSet.subset_union_right _ _) ksk)
        exact ⟨α, AlphaFn.Extends.refl α, hlit,
               Hh.le k1, Hρ.le k2, hReg'.le k3,
               Trc.Alpha.emp.le k4,
               (show Out.Alpha α .cont (AOut.mk .cont ∅) from trivial).le k5⟩
    case seqRet nred h h' ρ ρ' δ δ' s1 s2 t l hstep1 =>
        obtain ⟨r1, hastep1, hdisj⟩ := abs_gen_seq H2
        obtain ⟨α1, hα1, hlit1, hh1, hρ1, hδ1, ht1, ho1⟩ :=
          IH nred (Nat.lt_succ_self _) hlit (hval.le (Nat.le_succ _)) hstep1 hastep1 Hh Hρ Hδ
        rcases hdisj with ⟨hkind, k1, k2, k3, k4, k5⟩ | ⟨hkind, r2, hastep2, k1, k2, k3, k4, k5⟩
        · exact ⟨α1, hα1, hlit1, hh1.le k1, hρ1.le k2, hδ1.le k3, ht1.le k4, ho1.le k5⟩
        · -- `r1.out.kind = .cont`: the abstract analysis conservatively thought
          -- `s1` might continue and explored `s2` too, even though *this*
          -- concrete execution returned from `s1`.  `k1`..`k5` here relate
          -- `r2` (the result of that spurious `s2` exploration) to `ar`, not
          -- `r1` — and since `s2`'s store update is *strong* (`ASto.upd`
          -- overwrites, it does not join), `Sto.Alpha` for `r1`/`ρ'` need not
          -- survive being routed through `r2` at all.  Genuinely unprovable
          -- as Theorem B15 is currently stated; see the design discussion in
          -- the file header.  Left as `sorry` pending that decision.
          sorry
    case seqCont nred h h' h'' ρ ρ' ρ'' δ δ' δ'' s1 s2 t1 t2 o hstep1 hstep2 =>
        obtain ⟨r1, hastep1, hdisj⟩ := abs_gen_seq H2
        obtain ⟨α1, hα1, hlit1, hh1, hρ1, hδ1, ht1, ho1⟩ :=
          IH nred (Nat.lt_succ_self _) hlit (hval.le (Nat.le_succ _)) hstep1 hastep1 Hh Hρ Hδ
        have hcont : r1.out.kind = .cont := ho1.cont_kind
        rcases hdisj with ⟨hkind, _, _, _, _, _⟩ | ⟨_, r2, hastep2, k1, k2, k3, k4, k5⟩
        · exfalso; injection (hcont.symm.trans hkind)
        · obtain ⟨α2, hα2, hlit2, hh2, hρ2, hδ2, ht2, ho2⟩ :=
            IH nred (Nat.lt_succ_self _) hlit1 (hval.le (Nat.le_succ _)) hstep2 hastep2 hh1 hρ1 hδ1
          have hle_r2 : r2.out ⊑ (AOut.mk r2.out.kind (r1.out.locs ∪ r2.out.locs)) :=
            AOut.le_of_locs_subset rfl (ALocSet.subset_union_right _ _)
          exact ⟨α2, AlphaFn.Extends.trans hα1 hα2, hlit2,
                 hh2.le k1, hρ2.le k2, hδ2.le k3,
                 (Trc.Alpha.seq (ht1.mono hα2) ht2).le k4,
                 (ho2.le hle_r2).le k5⟩
    case lookupS h ρ ρ' δ x e p l1 l2 he hobj hρ' =>
        subst hρ'
        obtain ⟨k1, k2, k3, k4, k5⟩ := abs_gen_lookupS H2
        have hval_e := eval_alpha hlit Hρ he
        have hmaps := Hh.objOf hval_e hobj
        have hupd := sto_upd_alpha (x := x) Hρ hmaps
        have hlp : α.MapsInto (Concrete.litLoc (.str p))
            ({Abstract.litLocA (.str p)} : ALocSet) :=
          ⟨Abstract.litLocA (.str p), hlit (.str p), rfl⟩
        have hact : Act.Alpha α (.lookup l2 l1 (Concrete.litLoc (.str p)))
            (.lookup (ac.heap.objOf (aevalE ac.sto e) p) (aevalE ac.sto e)
              {Abstract.litLocA (.str p)}) :=
          ⟨hmaps, hval_e, hlp⟩
        exact ⟨α, AlphaFn.Extends.refl α, hlit,
               Hh.le k1, hupd.le k2, Hδ.le k3,
               (Trc.Alpha.act hact).le k4,
               (show Out.Alpha α .cont (AOut.mk .cont ∅) from trivial).le k5⟩
    case lookupD h ρ ρ' δ x e1 e2 l1 l2 l3 p he1 he2 hstr hobj hρ' =>
        subst hρ'
        obtain ⟨k1, k2, k3, k4, k5⟩ := abs_gen_lookupD H2
        have hval_e1 := eval_alpha hlit Hρ he1
        have hval_e2 := eval_alpha hlit Hρ he2
        have hVmem : (ac.heap.valOf (aevalE ac.sto e2)).Mem (.str p) :=
          Hh.valOf hval_e2 hstr
        have hmaps := Hh.objOfV hval_e1 hVmem hobj
        have hupd := sto_upd_alpha (x := x) Hρ hmaps
        have hact : Act.Alpha α (.lookup l3 l1 l2)
            (.lookup (ac.heap.objOfV (aevalE ac.sto e1) (ac.heap.valOf (aevalE ac.sto e2)))
              (aevalE ac.sto e1) (aevalE ac.sto e2)) :=
          ⟨hmaps, hval_e1, hval_e2⟩
        exact ⟨α, AlphaFn.Extends.refl α, hlit,
               Hh.le k1, hupd.le k2, Hδ.le k3,
               (Trc.Alpha.act hact).le k4,
               (show Out.Alpha α .cont (AOut.mk .cont ∅) from trivial).le k5⟩
    all_goals sorry

/-- Theorem B15.  Every finite concrete execution of `s` is `α`-related to
    every abstract analysis of `s`, for some extension `α'` of the initial
    abstraction.

    `α'` must be allowed to grow: the concrete semantics allocates fresh
    locations (`allocC`) that the initial `α` cannot already account for. -/
theorem soundness [Concrete] [Abstract] (cs : ConcreteSpec) (as : AbstractSpec)
    {Γ : Env} {Sg : ASigma} {α : AlphaFn} {s : Stmt}
    {c : Conf} {r : Res} {ac : AConf} {ar : ARes}
    (hlit : α.Lits)
    (hval : ∀ n, SigmaValid Γ Sg n)
    (H1 : BigStep Γ c s r)
    (H2 : ABigStep Γ Sg ac s ar)
    (Hh : Heap.Alpha α c.heap ac.heap)
    (Hρ : Sto.Alpha α c.sto ac.sto)
    (Hδ : Reg.Alpha α c.reg ac.reg) :
    ∃ α' : AlphaFn, α' ≥α α ∧ α'.Lits ∧
      Heap.Alpha α' r.heap ar.heap ∧ Sto.Alpha α' r.sto ar.sto ∧
      Reg.Alpha α' r.reg ar.reg ∧
      Trc.Alpha α' r.trc ar.trc ∧ Out.Alpha α' r.out ar.out := by
  obtain ⟨n, HN⟩ := H1.toN
  exact soundnessN cs as n hlit (hval n) HN H2 Hh Hρ Hδ

/-- Corollary: the top-level analysis `SA(Γ, s)` is sound, with no side
    condition at all — the summary environment starts empty. -/
theorem soundness_top [Concrete] [Abstract] (cs : ConcreteSpec) (as : AbstractSpec)
    {Γ : Env} {α : AlphaFn} {s : Stmt} {c : Conf} {r : Res} {ac : AConf} {ar : ARes}
    (hlit : α.Lits)
    (H1 : BigStep Γ c s r)
    (H2 : ABigStep Γ ASigma.empty ac s ar)
    (Hh : Heap.Alpha α c.heap ac.heap)
    (Hρ : Sto.Alpha α c.sto ac.sto)
    (Hδ : Reg.Alpha α c.reg ac.reg) :
    ∃ α' : AlphaFn, α' ≥α α ∧ α'.Lits ∧
      Heap.Alpha α' r.heap ar.heap ∧ Sto.Alpha α' r.sto ar.sto ∧
      Reg.Alpha α' r.reg ar.reg ∧
      Trc.Alpha α' r.trc ar.trc ∧ Out.Alpha α' r.out ar.out :=
  soundness cs as hlit (fun n => SigmaValid.empty Γ n) H1 H2 Hh Hρ Hδ

/-!
## Remaining work

The height-indexed scaffolding is complete and `[Skip]`, `[Assignment]`,
`[Return]`, `[SetTaint]` and `[SetSink]` are proved end to end, including the
`[Weakening]` absorption the paper's proof omits.  What remains is the
per-rule work, in dependency order:

1. `abs_gen_*` for the remaining statement shapes.  Each is the same two-case
   induction as `abs_gen_skip` (own rule + `weaken`), and each needs the
   monotonicity lemmas now in `CoreJsExtra` (`aevalE_mono`, `aevalEs_mono`,
   `ASto.upd_mono`), because `[Weakening]` runs the underlying rule in a
   *larger* state than the conclusion mentions.

   NOTE (learned from `abs_gen_setTaint`/`abs_gen_setSink`): a generation
   lemma's `weaken` case only has the induction hypothesis (`ih`) and the
   `weaken` constructor's *named* hypotheses to work with — its implicit
   config variables (the unnamed `h ρ δ h'' ρ'' δ'' ...` etc.) are *not*
   accessible under those names, and the theorem's own outer implicit
   arguments (`c`, `e`, ...) are still in scope but are a completely
   different, disconnected variable from whatever the goal actually
   mentions after `induction ... using` specialises it — referencing them
   inside the `weaken` case type-checks but proves a false goal. Write the
   `weaken` case using only `ih`'s output and the constructor's named
   hypotheses (`hh`, `hρ`, `hδ`, `hh'`, ... — reusing the *same* witness
   `ih` already produced whenever possible, as `abs_gen_setTaint` now does),
   never a freshly-built term that mentions `c` or other outer variables.
   Relatedly, don't state a generation lemma's untouched-field clauses as
   equalities (e.g. `c.reg.dep = aδ'.dep`) — `[Weakening]`'s input side
   only gives `⊑`, not `=`, so absorbing an outer weakening only preserves
   *inclusion* of the untouched fields, not equality; state those clauses
   as `⊆`/pointwise-`⊆` instead (see `abs_gen_setTaint`/`abs_gen_setSink`).

2. `[Sequence]`, `[Lookup]`, `[Update]` — Lemma B9 (`eval_alpha`) and Lemma
   B11 (`sto_upd_alpha`) plus the generation lemma from (1).

3. `[Binary Operation]` and `[Object Literal]`: the cases where `α'` genuinely
   grows.  Extend `α` at `allocC h κ ↦ allocA ĥ κ`; `AlphaFn.Extends` holds by
   `ConcreteSpec.allocC_fresh`, and `AbstractSpec.allocA_site` is what makes
   the extension well defined (one abstract location per site).

4. `[If-Then-Else]` and `[While]`: `Trc.Alpha.altL/altR` and
   `starNil/starCons`.  Neither needs trace-`⊑`, matching the paper.

5. `[Function Call]`, multi-target: `Hh` forces the concrete callee into the
   candidate list (B8.1.b gives `fid f ∈ ĥ.valOf L_f`), then
   `Trc.Alpha.choice` lifts that branch to the whole `ATrc.choice`.  Note the
   candidate set must be shown monotone in the heap, since `IsCandidate` is
   stated against the pre-weakening heap.

6. `[Call-Fix]` / `[Call-Assume]`.  `[Call-Assume]` is discharged directly by
   `hval`.  `[Call-Fix]` must establish `SigmaValid Γ (Sg.upd f sm) m` for the
   `m < n` at which the body is analysed — this is exactly what the strong
   induction hypothesis `IH` is for, and it is the reason the height index had
   to be introduced at all.
-/

end CoreJS
