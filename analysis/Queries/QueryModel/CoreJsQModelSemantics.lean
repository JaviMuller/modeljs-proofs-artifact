/-
  # Core JavaScript — Query Models (semantics)

  Satisfaction of query models (`CoreJsQModelSyntax.lean`) over execution
  records, the automaton counterpart of `Exec.Matches`.

  * A run (`Run`) reads a stretch `t[i..j)` of the trace, one action per
    action edge; `ε`-edges read nothing.
  * A component *accepts* `t[i..j)` under a substitution `ξ` (`QComp.Acc`) if,
    after choosing new values for the variables in the `scope` of some final
    state `f`, a run from the start reaches `f`, every invariant of `inv f`
    holds, and no `except` component of `exc f` is satisfied.  Values are
    chosen for exactly the run's own `scope`, so the tags of invocations a run
    never went through are never bound, and a local that occurs only in an
    `except` is bound *outside* it, as in the query semantics.
  * An `except` component is satisfied (`compSat`) if it accepts the whole
    trace; its own variables are then the ones in its `scope`, bound inside
    the negation.  `compSat` recurses on a *fuel* bounding the nesting of
    components (`QModel.depth`): a component of an `except` invoking a query
    with an `except` of its own refers to a further component, and so on.
  * A model is satisfied by a record and arguments `ls` (`QModel.Sat`) if its
    positive part accepts the whole trace, starting from the substitution
    that binds the parameters to `ls`.

  Substitutions are total (`MEnv`), like the query semantics' `LEnv`; a
  model checker binding variables lazily, as runs mention them, computes the
  same thing, since a run, its labels and its components only read the
  variables bound by the caller and the ones in their scope
  (`QComp.ReadsIn`, `QComp.acc_coincide`).

  Plain Lean 4 — no Mathlib required.
-/

import Queries.QueryLanguage.CoreJsQuerySemantics
import Queries.QueryModel.CoreJsQModelSyntax

namespace CoreJS

/-! ## Renamed actions and invariants -/

theorem QAct.inst_map {ν μ} (ρ : ν → μ) (ξ : μ → Loc) :
    ∀ a : QAct ν, (a.map ρ).inst ξ = a.inst (ξ ∘ ρ)
  | .lookup .. => rfl
  | .update .. => rfl
  | .call xf xs => by simp [QAct.map, QAct.inst, List.map_map]
  | .retn .. => rfl

theorem QAct.vars_map {ν μ} (ρ : ν → μ) : ∀ a : QAct ν, (a.map ρ).vars = a.vars.map ρ
  | .lookup .. => rfl
  | .update .. => rfl
  | .call xf xs => by simp [QAct.map, QAct.vars]
  | .retn .. => rfl

theorem QAct.inst_congr {ν} {ξ₁ ξ₂ : ν → Loc} :
    ∀ {a : QAct ν}, (∀ v ∈ a.vars, ξ₁ v = ξ₂ v) → a.inst ξ₁ = a.inst ξ₂
  | .lookup x₁ x₂ x₃, h => by simp [QAct.vars] at h; simp [QAct.inst, h]
  | .update x₁ x₂ x₃, h => by simp [QAct.vars] at h; simp [QAct.inst, h]
  | .call xf xs, h => by
      simp only [QAct.vars, List.mem_cons] at h
      have hxs : xs.map ξ₁ = xs.map ξ₂ := List.map_congr_left (fun x hx => h x (Or.inr hx))
      simp [QAct.inst, h xf (Or.inl rfl), hxs]
  | .retn xf x, h => by simp [QAct.vars] at h; simp [QAct.inst, h]

theorem Pred.vars_map {ν μ} (ρ : ν → μ) : ∀ p : Pred ν, (p.map ρ).vars = p.vars.map ρ
  | .sk _ | .ac _ | .dep _ _ | .sv _ _ | .hv _ _ => rfl

theorem Inv.vars_map {ν μ} (ρ : ν → μ) : ∀ I : Inv ν, (I.map ρ).vars = I.vars.map ρ
  | .pred p => Pred.vars_map ρ p
  | .not I => Inv.vars_map ρ I
  | .or I₁ I₂ | .and I₁ I₂ => by simp [Inv.map, Inv.vars, Inv.vars_map ρ I₁, Inv.vars_map ρ I₂]
  | .tt | .ff => rfl

theorem Pred.sat_map {ν μ} (ρ : ν → μ) (δ : Obs) (ξ : μ → Loc) :
    ∀ p : Pred ν, Pred.Sat δ ξ (p.map ρ) ↔ Pred.Sat δ (ξ ∘ ρ) p
  | .sk _ | .ac _ | .dep _ _ | .sv _ _ | .hv _ _ => Iff.rfl

theorem Inv.sat_map {ν μ} (ρ : ν → μ) (δ : Obs) (ξ : μ → Loc) :
    ∀ I : Inv ν, Inv.Sat δ ξ (I.map ρ) ↔ Inv.Sat δ (ξ ∘ ρ) I
  | .pred p => Pred.sat_map ρ δ ξ p
  | .not I => by simp only [Inv.map, Inv.Sat, Inv.sat_map ρ δ ξ I]
  | .or I₁ I₂ => by simp only [Inv.map, Inv.Sat, Inv.sat_map ρ δ ξ I₁, Inv.sat_map ρ δ ξ I₂]
  | .and I₁ I₂ => by simp only [Inv.map, Inv.Sat, Inv.sat_map ρ δ ξ I₁, Inv.sat_map ρ δ ξ I₂]
  | .tt | .ff => Iff.rfl

/-! ## Runs -/

/-- Substitutions of the model's variables. -/
abbrev MEnv := MVar → Loc

/-- `Run es t ξ s i s' j`: the edges `es` lead from `s` to `s'` reading
    `t[i..j)` under `ξ`. -/
inductive Run (es : List QEdge) (t : List Act) (ξ : MEnv) : QSt → Nat → QSt → Nat → Prop where
  | refl {s i} : Run es t ξ s i s i
  | eps {s s' s'' i j} :
      (s, .eps, s') ∈ es → Run es t ξ s' i s'' j → Run es t ξ s i s'' j
  | act {s s' s'' as i j} :
      (s, .act as, s') ∈ es →
      i < t.length →
      (∀ b ∈ as, t[i]? = some (b.inst ξ)) →
      Run es t ξ s' (i + 1) s'' j →
      Run es t ξ s i s'' j

section run

variable {es : List QEdge} {t : List Act} {ξ : MEnv}

theorem Run.le {s s' i j} (h : Run es t ξ s i s' j) : i ≤ j := by
  induction h <;> omega

theorem Run.trans {s s' s'' i k j} (h₁ : Run es t ξ s i s' k) (h₂ : Run es t ξ s' k s'' j) :
    Run es t ξ s i s'' j := by
  induction h₁ with
  | refl => exact h₂
  | eps he _ ih => exact .eps he (ih h₂)
  | act he hi hb _ ih => exact .act he hi hb (ih h₂)

/-- A run only uses the edges it is given. -/
theorem Run.mono {es' : List QEdge} (hes : ∀ e ∈ es, e ∈ es') {s s' i j}
    (h : Run es t ξ s i s' j) : Run es' t ξ s i s' j := by
  induction h with
  | refl => exact .refl
  | eps he _ ih => exact .eps (hes _ he) ih
  | act he hi hb _ ih => exact .act (hes _ he) hi hb ih

/-- A run through an `Any` self-loop on `s` stays at `s` for any stretch. -/
theorem Run.loop {s} (hs : (s, MLbl.any, s) ∈ es) :
    ∀ {i j}, i ≤ j → j ≤ t.length → Run es t ξ s i s j := by
  intro i j hij hj
  induction hd : j - i generalizing i with
  | zero => have : i = j := by omega
            subst this; exact .refl
  | succ d ih => exact .act hs (by omega) (by simp) (ih (by omega) (by omega))

/-- Runs only depend on the variables of their edges' labels. -/
theorem Run.coincide {V : MVar → Prop} {ξ₁ ξ₂ : MEnv}
    (hV : ∀ s l s', (s, l, s') ∈ es → ∀ v ∈ l.vars, V v) (hξ : ∀ v, V v → ξ₁ v = ξ₂ v)
    {s s' i j} (h : Run es t ξ₁ s i s' j) : Run es t ξ₂ s i s' j := by
  induction h with
  | refl => exact .refl
  | eps he _ ih => exact .eps he ih
  | @act s₀ s₁ _ as _ _ he hi hb _ ih =>
    refine .act he hi (fun b hb' => ?_) ih
    rw [← QAct.inst_congr (fun v hv => hξ v (hV _ _ _ he v
      (by simp only [MLbl.vars, List.mem_flatMap]; exact ⟨b, hb', hv⟩)))]
    exact hb b hb'

/-- Runs over edges lifted along a map `w` are the lifted runs:
    stated for an edge list `es` whose edges *out of* the image of `w` are
    exactly the lifted edges of `es₀`. -/
theorem Run.embed {es₀ : List QEdge} {w : QSt → QSt}
    (hes : ∀ s l x, (w s, l, x) ∈ es ↔ ∃ s', x = w s' ∧ (s, l, s') ∈ es₀) :
    ∀ {s x i j}, Run es t ξ (w s) i x j ↔ ∃ s', x = w s' ∧ Run es₀ t ξ s i s' j := by
  intro s x i j
  constructor
  · intro h
    generalize hs : w s = ws at h
    induction h generalizing s with
    | refl => exact ⟨s, hs.symm, .refl⟩
    | eps he _ ih =>
      subst hs
      obtain ⟨s', rfl, he'⟩ := (hes _ _ _).1 he
      obtain ⟨s'', rfl, h'⟩ := ih rfl
      exact ⟨s'', rfl, .eps he' h'⟩
    | act he hi hb _ ih =>
      subst hs
      obtain ⟨s', rfl, he'⟩ := (hes _ _ _).1 he
      obtain ⟨s'', rfl, h'⟩ := ih rfl
      exact ⟨s'', rfl, .act he' hi hb h'⟩
  · rintro ⟨s', rfl, h⟩
    induction h with
    | refl => exact .refl
    | eps he _ ih => exact .eps ((hes _ _ _).2 ⟨_, rfl, he⟩) ih
    | act he hi hb _ ih => exact .act ((hes _ _ _).2 ⟨_, rfl, he⟩) hi hb ih

end run

/-! ## Acceptance and satisfaction -/

/-- The labels of the final state `f` hold under `ξ`: its invariants, and none
    of its `except` components (`X k ξ`: component `k` is satisfied). -/
def QComp.Ok (c : QComp) (δ : Obs) (X : Nat → MEnv → Prop) (ξ : MEnv) (f : QSt) : Prop :=
  (∀ I ∈ c.inv f, δ ⬝ ξ ⊨ I) ∧ ∀ k ∈ c.exc f, ¬ X k ξ

/-- `c` accepts `t[i..j)` under `ξ`: for some final state `f` and new values
    of the variables in `f`'s scope, a run reaches `f` and `f`'s labels hold. -/
def QComp.Acc (c : QComp) (t : List Act) (δ : Obs) (X : Nat → MEnv → Prop) (ξ : MEnv)
    (i j : Nat) : Prop :=
  ∃ f ∈ c.finals, ∃ ξ' : MEnv, (∀ v, v ∉ c.scope f → ξ' v = ξ v) ∧
    Run c.edges t ξ' c.start i f j ∧ c.Ok δ X ξ' f

/-- `compSat cs t δ n k ξ`: component `k` of `cs` accepts the whole trace
    under `ξ`, its own components evaluated with fuel `n - 1`. -/
def compSat (cs : List QComp) (t : List Act) (δ : Obs) : Nat → Nat → MEnv → Prop
  | 0,     _, _ => False
  | n + 1, k, ξ => ∃ c, cs[k]? = some c ∧ c.Acc t δ (compSat cs t δ n) ξ 0 t.length

/-- The substitution binding the parameters to `ls` (as `LEnv.bind` does) and
    everything else to `0`, like `LEnv.empty`. -/
def QModel.env (M : QModel) (ls : List Loc) : MEnv
  | .src x   => LEnv.empty.bind M.params ls x
  | .tag _ _ => 0

/-- The record `e` satisfies the model `M` applied to `ls`. -/
def QModel.Sat (M : QModel) (e : Exec) (ls : List Loc) : Prop :=
  M.main.Acc e.trc.toList e.obs (compSat M.comps e.trc.toList e.obs M.depth) (M.env ls)
    0 e.trc.toList.length

/-! ## Coincidence

A component reads only the variables bound by its caller and the ones in its
own scope.  `ReadsIn cs V c` says that everything `c` reads — labels,
invariants, scope, and the components it refers to, recursively — is in `V`. -/

/-- Everything `c` reads, and every component of `cs` it refers to, is in `V`. -/
inductive QComp.ReadsIn (cs : List QComp) (V : MVar → Prop) : QComp → Prop where
  | mk {c : QComp} :
      (∀ s l s', (s, l, s') ∈ c.edges → ∀ v ∈ l.vars, V v) →
      (∀ s, ∀ I ∈ c.inv s, ∀ v ∈ I.vars, V v) →
      (∀ s, ∀ v ∈ c.scope s, V v) →
      (∀ s, ∀ k ∈ c.exc s, k < cs.length) →
      (∀ s, ∀ k ∈ c.exc s, ∀ c', cs[k]? = some c' → QComp.ReadsIn cs V c') →
      QComp.ReadsIn cs V c

theorem QComp.ReadsIn.edges {cs V c} : QComp.ReadsIn cs V c →
    ∀ s l s', (s, l, s') ∈ c.edges → ∀ v ∈ l.vars, V v
  | .mk h _ _ _ _ => h

theorem QComp.ReadsIn.inv {cs V c} : QComp.ReadsIn cs V c →
    ∀ s, ∀ I ∈ c.inv s, ∀ v ∈ I.vars, V v
  | .mk _ h _ _ _ => h

theorem QComp.ReadsIn.scope {cs V c} : QComp.ReadsIn cs V c → ∀ s, ∀ v ∈ c.scope s, V v
  | .mk _ _ h _ _ => h

theorem QComp.ReadsIn.excLt {cs V c} : QComp.ReadsIn cs V c →
    ∀ s, ∀ k ∈ c.exc s, k < cs.length
  | .mk _ _ _ h _ => h

theorem QComp.ReadsIn.exc {cs V c} : QComp.ReadsIn cs V c →
    ∀ s, ∀ k ∈ c.exc s, ∀ c', cs[k]? = some c' → QComp.ReadsIn cs V c'
  | .mk _ _ _ _ h => h

/-- Reading within `V` survives growing the list of components. -/
theorem QComp.ReadsIn.extend {cs cs' : List QComp} (hcs : cs <+: cs') {V} :
    ∀ {c}, QComp.ReadsIn cs V c → QComp.ReadsIn cs' V c := by
  intro c h
  obtain ⟨u, rfl⟩ := hcs
  induction h with
  | mk he hi hs hlt _ ih =>
    refine .mk he hi hs (fun s k hk => by simp; have := hlt s k hk; omega) (fun s k hk c' hc' => ?_)
    rw [List.getElem?_append_left (hlt s k hk)] at hc'
    exact ih s k hk c' hc'

/-- Weakening the set of variables read. -/
theorem QComp.ReadsIn.weaken {cs : List QComp} {V W : MVar → Prop} (hVW : ∀ v, V v → W v) :
    ∀ {c}, QComp.ReadsIn cs V c → QComp.ReadsIn cs W c := by
  intro c h
  induction h with
  | mk he hi hs hlt _ ih =>
    exact .mk (fun s l s' h v hv => hVW v (he s l s' h v hv))
      (fun s I hI v hv => hVW v (hi s I hI v hv)) (fun s v hv => hVW v (hs s v hv)) hlt ih

/-- The labels of a final state only read `V`. -/
theorem QComp.ok_coincide {cs : List QComp} {V : MVar → Prop} {c : QComp} {δ : Obs}
    {X : Nat → MEnv → Prop}
    (hX : ∀ k c', cs[k]? = some c' → QComp.ReadsIn cs V c' →
      ∀ ξ₁ ξ₂ : MEnv, (∀ v, V v → ξ₁ v = ξ₂ v) → (X k ξ₁ ↔ X k ξ₂))
    (hc : QComp.ReadsIn cs V c) {ξ₁ ξ₂ : MEnv} (hξ : ∀ v, V v → ξ₁ v = ξ₂ v) (f : QSt) :
    c.Ok δ X ξ₁ f ↔ c.Ok δ X ξ₂ f := by
  unfold QComp.Ok
  constructor
  · rintro ⟨hi, he⟩
    refine ⟨fun I hI => (Inv.sat_coincide (fun v hv => hξ v (hc.inv f I hI v hv))).1 (hi I hI),
      fun k hk hk' => he k hk ?_⟩
    obtain ⟨c', hc'⟩ : ∃ c', cs[k]? = some c' :=
      ⟨_, List.getElem?_eq_getElem (hc.excLt f k hk)⟩
    exact (hX k c' hc' (hc.exc f k hk c' hc') ξ₁ ξ₂ hξ).2 hk'
  · rintro ⟨hi, he⟩
    refine ⟨fun I hI => (Inv.sat_coincide (fun v hv => hξ v (hc.inv f I hI v hv))).2 (hi I hI),
      fun k hk hk' => he k hk ?_⟩
    obtain ⟨c', hc'⟩ : ∃ c', cs[k]? = some c' :=
      ⟨_, List.getElem?_eq_getElem (hc.excLt f k hk)⟩
    exact (hX k c' hc' (hc.exc f k hk c' hc') ξ₁ ξ₂ hξ).1 hk'

/-- Acceptance only reads `V`, for components referred to whose satisfaction
    only reads `V`. -/
theorem QComp.acc_coincide {cs : List QComp} {V : MVar → Prop} {c : QComp} {t : List Act}
    {δ : Obs} {X : Nat → MEnv → Prop}
    (hX : ∀ k c', cs[k]? = some c' → QComp.ReadsIn cs V c' →
      ∀ ξ₁ ξ₂ : MEnv, (∀ v, V v → ξ₁ v = ξ₂ v) → (X k ξ₁ ↔ X k ξ₂))
    (hc : QComp.ReadsIn cs V c) {ξ₁ ξ₂ : MEnv} (hξ : ∀ v, V v → ξ₁ v = ξ₂ v) {i j : Nat} :
    c.Acc t δ X ξ₁ i j ↔ c.Acc t δ X ξ₂ i j := by
  have mp : ∀ {ξ₁ ξ₂ : MEnv}, (∀ v, V v → ξ₁ v = ξ₂ v) →
      c.Acc t δ X ξ₁ i j → c.Acc t δ X ξ₂ i j := by
    rintro ξ₁ ξ₂ hξ ⟨f, hf, ξ', hξ', hrun, hok⟩
    let ξ'' : MEnv := fun v => if v ∈ c.scope f then ξ' v else ξ₂ v
    have hagree : ∀ v, V v → ξ' v = ξ'' v := by
      intro v hv
      by_cases hs : v ∈ c.scope f
      · simp [ξ'', hs]
      · simp only [ξ'', hs, if_false]; rw [hξ' v hs]; exact hξ v hv
    refine ⟨f, hf, ξ'', fun v hv => by simp [ξ'', hv], hrun.coincide hc.edges hagree,
      (QComp.ok_coincide hX hc hagree f).1 hok⟩
  exact ⟨mp hξ, mp (fun v hv => (hξ v hv).symm)⟩

/-- Satisfaction of a component only reads `V`. -/
theorem compSat_coincide {cs : List QComp} {t : List Act} {δ : Obs} {V : MVar → Prop} :
    ∀ (n k : Nat) (c : QComp), cs[k]? = some c → QComp.ReadsIn cs V c →
      ∀ ξ₁ ξ₂ : MEnv, (∀ v, V v → ξ₁ v = ξ₂ v) → (compSat cs t δ n k ξ₁ ↔ compSat cs t δ n k ξ₂)
  | 0, _, _, _, _, _, _, _ => Iff.rfl
  | n + 1, k, c, hc, hr, ξ₁, ξ₂, hξ => by
      simp only [compSat, hc, Option.some.injEq, exists_eq_left']
      exact QComp.acc_coincide (compSat_coincide n) hr hξ

end CoreJS
