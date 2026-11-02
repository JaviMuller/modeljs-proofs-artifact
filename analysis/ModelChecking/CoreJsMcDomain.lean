/-
  # Core JavaScript — Model checking: assignment domains

  The *successive refinement of the variables' values* that makes model
  checking efficient, stated as an interface: an abstract domain of sets of
  abstract assignments (`ADom`), with

  * `top`: every assignment — every variable starts unconstrained, including
    variables that occur in no action (only in invariants);
  * `constrain d as B`: the assignments of `d` under which the actions `as`
    may match the abstract action `B`;
  * `refine d I`: some subset of `d` keeping every assignment that may satisfy
    the invariants `I` (from no filtering at all to full propagation);
  * `solve d I ys g`: an assignment of `d` that may satisfy `I` and passes the
    test `g` (reading only the variables `ys`), if there is one — the
    `except` check at acceptance is such a test;
  * `empty d`: `d` has certainly no assignment.

  `ADom.Spec` is the specification the model-checking algorithm relies on;
  its proofs never look inside a domain.

  `nonrel` is an instance: one set of values per variable (non-relational),
  with generalised arc consistency as `refine` (a value is kept if, for every
  invariant conjunct mentioning its variable, some assignment of the
  conjunct's variables from the current sets supports it) and enumeration of
  the invariants' variables as `solve`.  It represents action constraints
  exactly, provided matching an action decomposes into constraints on single
  variables (`Abs.Sep`), and it has finitely many elements, as needed for
  termination.

  Plain Lean 4 — no Mathlib required.
-/

import ModelChecking.CoreJsMcExplore

namespace CoreJS

variable {A V Φ : Type}

/-! ## The interface -/

/-- An abstract domain of sets of abstract assignments. -/
structure ADom (A V Φ : Type) where
  D         : Type
  deq       : DecidableEq D
  mem       : D → (MVar → V) → Prop
  top       : D
  constrain : D → List (QAct MVar) → A → D
  refine    : D → List (Inv MVar) → D
  solve     : D → List (Inv MVar) → List MVar → ((MVar → V) → Bool) → Option (MVar → V)
  empty     : D → Bool

/-- The specification of a domain, relative to an abstraction `𝔄`, facts `δₐ`,
    and the action lists `good` it must represent exactly. -/
structure ADom.Spec (dom : ADom A V Φ) (𝔄 : Abs A V Φ) (δₐ : Φ)
    (good : List (QAct MVar) → Prop) : Prop where
  top            : ∀ ξ, dom.mem dom.top ξ
  constrain      : ∀ d as B ξ, good as →
    (dom.mem (dom.constrain d as B) ξ ↔ dom.mem d ξ ∧ 𝔄.Fires ξ as B)
  refine_sub     : ∀ d I ξ, dom.mem (dom.refine d I) ξ → dom.mem d ξ
  refine_keep    : ∀ d I ξ, dom.mem d ξ → (∀ J ∈ I, 𝔄.inv δₐ ξ true J = true) →
    dom.mem (dom.refine d I) ξ
  solve_sound    : ∀ d I ys g ξ, dom.solve d I ys g = some ξ →
    dom.mem d ξ ∧ (∀ J ∈ I, 𝔄.inv δₐ ξ true J = true) ∧ g ξ = true
  solve_complete : ∀ d I ys g ξ, (∀ ξ₁ ξ₂, (∀ x ∈ ys, ξ₁ x = ξ₂ x) → g ξ₁ = g ξ₂) →
    dom.mem d ξ → (∀ J ∈ I, 𝔄.inv δₐ ξ true J = true) → g ξ = true →
    (dom.solve d I ys g).isSome
  empty          : ∀ d ξ, dom.mem d ξ → dom.empty d = false
  /-- Finitely many elements are reachable from `top`. -/
  finite         : ∃ UD : List dom.D, dom.top ∈ UD ∧
    ∀ d ∈ UD, (∀ I, dom.refine d I ∈ UD) ∧ ∀ as B, dom.constrain d as B ∈ UD

/-! ## Separable matching

Matching a query action against an abstract action is a conjunction of
constraints on single variables (one per position); this is what a
non-relational domain can represent exactly. -/

/-- Action matching decomposed into constraints on single variables: `none` if
    the action cannot match at all. -/
structure Abs.Sep (𝔄 : Abs A V Φ) where
  sep  : QAct MVar → A → Option (List (MVar × (V → Bool)))
  spec : ∀ ξ b B, 𝔄.matchA ξ b B = true ↔
    ∃ cs, sep b B = some cs ∧ ∀ c ∈ cs, c.2 (ξ c.1) = true
  vars : ∀ b B cs, sep b B = some cs → ∀ c ∈ cs, c.1 ∈ b.vars

/-- The constraints of a list of actions, all matching the same abstract action. -/
def Abs.Sep.all {𝔄 : Abs A V Φ} (S : 𝔄.Sep) (B : A) : List (QAct MVar) →
    Option (List (MVar × (V → Bool)))
  | []      => some []
  | b :: as => match S.sep b B, S.all B as with
    | some c, some r => some (c ++ r)
    | _,      _      => none

theorem Abs.Sep.all_spec {𝔄 : Abs A V Φ} (S : 𝔄.Sep) (B : A) (ξ : MVar → V) :
    ∀ as : List (QAct MVar), 𝔄.Fires ξ as B ↔
      ∃ cs, S.all B as = some cs ∧ ∀ c ∈ cs, c.2 (ξ c.1) = true
  | [] => by simp [Abs.Fires, Abs.Sep.all]
  | b :: as => by
      have ih := S.all_spec B ξ as
      simp only [Abs.Fires, List.mem_cons, forall_eq_or_imp] at ih ⊢
      rw [S.spec, ih]
      simp only [Abs.Sep.all]
      constructor
      · rintro ⟨⟨c, hc, hc'⟩, r, hr, hr'⟩
        rw [hc, hr]
        exact ⟨_, rfl, fun x hx => (List.mem_append.1 hx).elim (hc' x) (hr' x)⟩
      · rintro ⟨cs, h, hcs⟩
        cases hc : S.sep b B <;> cases hr : S.all B as <;> rw [hc, hr] at h <;> simp at h
        subst h
        exact ⟨⟨_, rfl, fun x hx => hcs x (List.mem_append_left _ hx)⟩,
          ⟨_, rfl, fun x hx => hcs x (List.mem_append_right _ hx)⟩⟩

theorem Abs.Sep.all_vars {𝔄 : Abs A V Φ} (S : 𝔄.Sep) (B : A) :
    ∀ (as : List (QAct MVar)) cs, S.all B as = some cs → ∀ c ∈ cs, ∃ b ∈ as, c.1 ∈ b.vars
  | [], cs, h => by simp [Abs.Sep.all] at h; subst h; simp
  | b :: as, cs, h => by
      simp only [Abs.Sep.all] at h
      cases hc : S.sep b B <;> cases hr : S.all B as <;> rw [hc, hr] at h <;> simp at h
      subst h
      intro c hc'
      rcases List.mem_append.1 hc' with h | h
      · exact ⟨b, List.mem_cons_self .., S.vars b B _ hc c h⟩
      · obtain ⟨b', hb', h'⟩ := S.all_vars B as _ hr c h
        exact ⟨b', List.mem_cons_of_mem _ hb', h'⟩

/-! ## Finite enumerations used by the instance -/

/-- All sublists. -/
def subs {β : Type} : List β → List (List β)
  | []     => [[]]
  | a :: l => (subs l).map (a :: ·) ++ subs l

theorem mem_subs {β : Type} {l' l : List β} (h : l'.Sublist l) : l' ∈ subs l := by
  induction h with
  | slnil => simp [subs]
  | cons a _ ih => simp only [subs, List.mem_append]; exact Or.inr ih
  | cons_cons a _ ih => simp only [subs, List.mem_append, List.mem_map]; exact Or.inl ⟨_, ih, rfl⟩

theorem sublist_of_mem_subs {β : Type} : ∀ {l : List β} {l' : List β}, l' ∈ subs l → l'.Sublist l
  | [], l', h => by simp [subs] at h; subst h; exact List.Sublist.refl _
  | a :: l, l', h => by
      simp only [subs, List.mem_append, List.mem_map] at h
      rcases h with ⟨l'', hl, rfl⟩ | hl
      · exact (sublist_of_mem_subs hl).cons_cons a
      · exact (sublist_of_mem_subs hl).cons a

/-- All lists of length `n` with elements from `B`. -/
def tuples {β : Type} (B : List β) : Nat → List (List β)
  | 0     => [[]]
  | n + 1 => B.flatMap fun b => (tuples B n).map (b :: ·)

theorem of_mem_tuples {β : Type} {B : List β} :
    ∀ {n : Nat} {d : List β}, d ∈ tuples B n → ∀ e ∈ d, e ∈ B
  | 0, d, h => by simp [tuples] at h; subst h; simp
  | n + 1, d, h => by
      simp only [tuples, List.mem_flatMap, List.mem_map] at h
      obtain ⟨b, hb, d', hd', rfl⟩ := h
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hb
      · exact of_mem_tuples hd' e he

theorem mem_tuples {β : Type} {B : List β} :
    ∀ {d : List β}, (∀ e ∈ d, e ∈ B) → d ∈ tuples B d.length
  | [], _ => by simp [tuples]
  | e :: d, h => by
      simp only [tuples, List.length_cons, List.mem_flatMap, List.mem_map]
      exact ⟨e, h e (List.mem_cons_self ..), d,
        mem_tuples (fun x hx => h x (List.mem_cons_of_mem _ hx)), rfl⟩

/-! ## The non-relational instance -/

section nonrel

variable (vals : List V) (xs : List MVar)

/-- The values of `x`: its entry, for a variable of `xs`; every value otherwise. -/
def dget : List MVar → List (List V) → MVar → List V
  | y :: ys, e :: es, x => if x = y then e else dget ys es x
  | _,       _,       _ => vals

theorem dget_map (g : MVar → List V) {x : MVar} :
    ∀ {ys : List MVar}, x ∈ ys → dget vals ys (ys.map g) x = g x
  | [], h => by simp at h
  | y :: ys, h => by
      simp only [List.map_cons, dget]
      by_cases hxy : x = y
      · subst hxy; simp
      · rw [if_neg hxy]; exact dget_map g ((List.mem_cons.1 h).resolve_left hxy)

theorem dget_not_mem {x : MVar} : ∀ {ys : List MVar} (e : List (List V)), x ∉ ys →
    dget vals ys e x = vals
  | [], e, _ => by cases e <;> rfl
  | y :: ys, [], _ => rfl
  | y :: ys, e :: es, h => by
      simp only [dget]
      rw [if_neg (fun hxy : x = y => h (hxy ▸ List.mem_cons_self ..))]
      exact dget_not_mem es (fun h' => h (List.mem_cons_of_mem _ h'))

/-- Entries are sublists of `vals` (or `vals` itself). -/
theorem dget_sublist {e : List (List V)} (he : ∀ c ∈ e, c.Sublist vals) :
    ∀ (ys : List MVar) (x : MVar), (dget vals ys e x).Sublist vals := by
  intro ys x
  induction ys generalizing e with
  | nil => exact List.Sublist.refl _
  | cons y ys ih =>
    cases e with
    | nil => exact List.Sublist.refl _
    | cons c es =>
      simp only [dget]
      split
      · exact he c (List.mem_cons_self ..)
      · exact ih (fun c hc => he c (List.mem_cons_of_mem _ hc))

/-- All assignments taking, on `ys`, values from `get`, and agreeing with `ξ₀`
    elsewhere. -/
def assigns (get : MVar → List V) (ξ₀ : MVar → V) : List MVar → List (MVar → V)
  | []      => [ξ₀]
  | y :: ys => (get y).flatMap fun v =>
      (assigns get ξ₀ ys).map fun ξ => fun z => if z = y then v else ξ z

theorem mem_assigns {get : MVar → List V} {ξ₀ : MVar → V} :
    ∀ {ys : List MVar} {ξ : MVar → V}, ξ ∈ assigns get ξ₀ ys →
      (∀ y ∈ ys, ξ y ∈ get y) ∧ (∀ z, z ∉ ys → ξ z = ξ₀ z)
  | [], ξ, h => by simp [assigns] at h; subst h; simp
  | y :: ys, ξ, h => by
      simp only [assigns, List.mem_flatMap, List.mem_map] at h
      obtain ⟨v, hv, ξ', hξ', rfl⟩ := h
      obtain ⟨h₁, h₂⟩ := mem_assigns hξ'
      refine ⟨fun z hz => ?_, fun z hz => ?_⟩
      · by_cases hzy : z = y
        · simp [hzy, hv]
        · simp only [hzy, if_false]; exact h₁ z ((List.mem_cons.1 hz).resolve_left hzy)
      · have hzy : z ≠ y := fun h => hz (h ▸ List.mem_cons_self ..)
        simp only [hzy, if_false]; exact h₂ z (fun h => hz (List.mem_cons_of_mem _ h))

theorem exists_mem_assigns {get : MVar → List V} {ξ₀ ξ : MVar → V} :
    ∀ {ys : List MVar}, (∀ y ∈ ys, ξ y ∈ get y) →
      ∃ ξ' ∈ assigns get ξ₀ ys, ∀ y ∈ ys, ξ' y = ξ y
  | [], _ => ⟨ξ₀, by simp [assigns], by simp⟩
  | y :: ys, h => by
      obtain ⟨ξ', hξ', h'⟩ := exists_mem_assigns (ys := ys) (fun z hz => h z (List.mem_cons_of_mem _ hz))
      refine ⟨fun z => if z = y then ξ y else ξ' z, ?_, fun z hz => ?_⟩
      · simp only [assigns, List.mem_flatMap, List.mem_map]
        exact ⟨ξ y, h y (List.mem_cons_self ..), ξ', hξ', rfl⟩
      · by_cases hzy : z = y
        · simp [hzy]
        · simp only [hzy, if_false]; exact h' z ((List.mem_cons.1 hz).resolve_left hzy)

variable [DecidableEq V] [Inhabited V]

/-- A default assignment from the entries' first values. -/
def dflt (e : List (List V)) : MVar → V := fun y => (dget vals xs e y).headD default

omit [DecidableEq V] in
theorem dflt_mem {e : List (List V)} {y : MVar} (h : dget vals xs e y ≠ []) :
    dflt vals xs e y ∈ dget vals xs e y := by
  unfold dflt
  cases hd : dget vals xs e y with
  | nil => exact absurd hd h
  | cons a l => simp

variable (𝔄 : Abs A V Φ) (δₐ : Φ) (S : 𝔄.Sep)

/-- Arc consistency of the value `v` of `x` with the conjunct `J`. -/
def supported (e : List (List V)) (x : MVar) (v : V) (J : Inv MVar) : Bool :=
  !(decide (x ∈ J.vars)) ||
    (assigns (fun y => if y = x then [v] else dget vals xs e y) (dflt vals xs e) J.vars).any
      fun ξ => 𝔄.inv δₐ ξ true J

/-- One set of values per variable of `xs` (`none`: certainly empty). -/
def nonrel : ADom A V Φ where
  D := Option (List (List V))
  deq := inferInstance
  mem
    | none,   _ => False
    | some e, ξ => ∀ x ∈ xs, ξ x ∈ dget vals xs e x
  top := some (xs.map fun _ => vals)
  constrain
    | none,   _,  _ => none
    | some e, as, B => match S.all B as with
      | none    => none
      | some cs => some (xs.map fun y => (dget vals xs e y).filter fun v =>
          cs.all fun c => !(decide (c.1 = y)) || c.2 v)
  refine
    | none,   _ => none
    | some e, I => some (xs.map fun x => (dget vals xs e x).filter fun v =>
        I.all (supported vals xs 𝔄 δₐ e x v))
  solve
    | none,   _, _,  _ => none
    | some e, I, ys, g =>
      if xs.all (fun x => !(dget vals xs e x).isEmpty) then
        (assigns (dget vals xs e) (dflt vals xs e) (I.flatMap Inv.vars ++ ys)).find?
          fun ξ => I.all (𝔄.inv δₐ ξ true) && g ξ
      else none
  empty
    | none   => true
    | some e  => xs.any fun x => (dget vals xs e x).isEmpty

theorem nonrel_mem (e : List (List V)) (ξ : MVar → V) :
    (nonrel vals xs 𝔄 δₐ S).mem (some e) ξ ↔ ∀ x ∈ xs, ξ x ∈ dget vals xs e x := Iff.rfl

theorem nonrel_refine (e : List (List V)) (I : List (Inv MVar)) :
    (nonrel vals xs 𝔄 δₐ S).refine (some e) I = some (xs.map fun x =>
      (dget vals xs e x).filter fun v => I.all (supported vals xs 𝔄 δₐ e x v)) := rfl

theorem nonrel_constrain (e : List (List V)) (as : List (QAct MVar)) (B : A) :
    (nonrel vals xs 𝔄 δₐ S).constrain (some e) as B = (match S.all B as with
      | none    => none
      | some cs => some (xs.map fun y => (dget vals xs e y).filter fun v =>
          cs.all fun c => !(decide (c.1 = y)) || c.2 v)) := rfl

/-- Finitely many elements are reachable from `top`: one sublist of `vals`
    per variable of `xs`. -/
theorem nonrel_finite :
    ∃ UD : List (nonrel vals xs 𝔄 δₐ S).D, (nonrel vals xs 𝔄 δₐ S).top ∈ UD ∧
      ∀ d ∈ UD, (∀ I, (nonrel vals xs 𝔄 δₐ S).refine d I ∈ UD) ∧
        ∀ as B, (nonrel vals xs 𝔄 δₐ S).constrain d as B ∈ UD := by
    -- Canonical elements: one sublist of `vals` per variable of `xs`.
    have mk : ∀ g : MVar → List V, (∀ y, (g y).Sublist vals) →
        some (xs.map g) ∈ none :: (tuples (subs vals) xs.length).map some := by
      intro g hg
      refine List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, ?_, rfl⟩)
      have := mem_tuples (B := subs vals) (d := xs.map g)
        (by simp only [List.mem_map]; rintro _ ⟨y, _, rfl⟩; exact mem_subs (hg y))
      simpa using this
    refine ⟨none :: (tuples (subs vals) xs.length).map some, mk _ fun _ => List.Sublist.refl _, ?_⟩
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact ⟨fun _ => List.mem_cons_self .., fun _ _ => List.mem_cons_self ..⟩
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
      have hsub := dget_sublist vals
        (fun c hc => sublist_of_mem_subs (of_mem_tuples he c hc)) xs
      refine ⟨fun I => ?_, fun as B => ?_⟩
      · rw [nonrel_refine]; exact mk _ fun y => (List.filter_sublist).trans (hsub y)
      · rw [nonrel_constrain]
        split
        · exact List.mem_cons_self ..
        · exact mk _ fun y => (List.filter_sublist).trans (hsub y)

/-- The instance meets the specification, for action lists whose variables
    are among `xs`, when `vals` contains every abstract value. -/
theorem nonrel_spec (h𝔄 : 𝔄.Sound) (hvals : ∀ v, v ∈ vals) :
    (nonrel vals xs 𝔄 δₐ S).Spec 𝔄 δₐ (fun as => ∀ b ∈ as, ∀ x ∈ b.vars, x ∈ xs) where
  top ξ := fun x hx => by
    show ξ x ∈ dget vals xs (xs.map fun _ => vals) x
    rw [dget_map _ _ hx]; exact hvals _
  constrain d as B ξ hgood := by
    cases d with
    | none => exact ⟨fun h => h.elim, fun h => h.1.elim⟩
    | some e =>
      rw [nonrel_constrain, S.all_spec B ξ as]
      cases hcs : S.all B as with
      | none => simp; exact fun h => h.elim
      | some cs =>
        simp only [Option.some.injEq, exists_eq_left']
        rw [nonrel_mem, nonrel_mem]
        constructor
        · intro h
          have h' : ∀ x ∈ xs, ξ x ∈ (dget vals xs e x).filter fun v =>
              cs.all fun c => !(decide (c.1 = x)) || c.2 v := by
            intro x hx; have := h x hx; rw [dget_map _ _ hx] at this; exact this
          refine ⟨fun x hx => (List.mem_filter.1 (h' x hx)).1, fun c hc => ?_⟩
          obtain ⟨b, hb, hcb⟩ := S.all_vars B as cs hcs c hc
          have hx := hgood b hb c.1 hcb
          have := List.all_eq_true.1 (List.mem_filter.1 (h' c.1 hx)).2 c hc
          simpa using this
        · rintro ⟨h₁, h₂⟩ x hx
          rw [dget_map _ _ hx]
          refine List.mem_filter.2 ⟨h₁ x hx, List.all_eq_true.2 fun c hc => ?_⟩
          by_cases hcx : c.1 = x
          · subst hcx; simp [h₂ c hc]
          · simp [hcx]
  refine_sub d I ξ h := by
    cases d with
    | none => exact h
    | some e =>
      rw [nonrel_refine, nonrel_mem] at h
      rw [nonrel_mem]
      intro x hx
      have := h x hx
      rw [dget_map _ _ hx] at this
      exact (List.mem_filter.1 this).1
  refine_keep d I ξ hd hI := by
    cases d with
    | none => exact hd
    | some e =>
      rw [nonrel_mem] at hd
      rw [nonrel_refine, nonrel_mem]
      intro x hx
      rw [dget_map _ _ hx]
      refine List.mem_filter.2 ⟨hd x hx, List.all_eq_true.2 fun J hJ => ?_⟩
      unfold supported
      by_cases hxJ : x ∈ J.vars
      · simp only [hxJ, decide_true, Bool.not_true, Bool.false_or]
        obtain ⟨ξ', hξ', hagree⟩ := exists_mem_assigns (ξ₀ := dflt vals xs e) (ξ := ξ)
          (get := fun y => if y = x then [ξ x] else dget vals xs e y) (ys := J.vars) (by
            intro y _
            by_cases hyx : y = x
            · simp [hyx]
            · simp only [hyx, if_false]
              by_cases hy : y ∈ xs
              · exact hd y hy
              · rw [dget_not_mem _ _ hy]; exact hvals _)
        refine List.any_eq_true.2 ⟨ξ', hξ', ?_⟩
        rw [Abs.inv_congr h𝔄 δₐ true J (fun y hy => hagree y hy)]
        exact hI J hJ
      · simp [hxJ]
  solve_sound d I ys g ξ h := by
    cases d with
    | none => simp [nonrel] at h
    | some e =>
      simp only [nonrel] at h
      split at h
      · rename_i hne
        have hξ := List.mem_of_find?_eq_some h
        have hI := List.find?_some h
        obtain ⟨h₁, h₂⟩ := mem_assigns hξ
        simp only [Bool.and_eq_true] at hI
        refine ⟨fun x hx => ?_, fun J hJ => List.all_eq_true.1 hI.1 J hJ, hI.2⟩
        by_cases hxv : x ∈ I.flatMap Inv.vars ++ ys
        · exact h₁ x hxv
        · rw [h₂ x hxv]
          apply dflt_mem
          have := List.all_eq_true.1 hne x hx
          simpa using this
      · simp at h
  solve_complete d I ys g ξ hg hd hI hgξ := by
    cases d with
    | none => exact hd.elim
    | some e =>
      simp only [nonrel]
      have hne : (xs.all fun x => !(dget vals xs e x).isEmpty) = true :=
        List.all_eq_true.2 fun x hx => by
          have := hd x hx
          cases h : dget vals xs e x with
          | nil => rw [h] at this; simp at this
          | cons _ _ => rfl
      rw [if_pos hne]
      obtain ⟨ξ', hξ', hagree⟩ := exists_mem_assigns (ξ₀ := dflt vals xs e) (ξ := ξ)
        (get := dget vals xs e) (ys := I.flatMap Inv.vars ++ ys) (by
          intro y _
          by_cases hy : y ∈ xs
          · exact hd y hy
          · rw [dget_not_mem _ _ hy]; exact hvals _)
      refine List.find?_isSome.2 ⟨ξ', hξ', ?_⟩
      simp only [Bool.and_eq_true]
      refine ⟨List.all_eq_true.2 fun J hJ => ?_, ?_⟩
      · rw [Abs.inv_congr h𝔄 δₐ true J (fun y hy =>
          hagree y (List.mem_append_left _ (List.mem_flatMap.2 ⟨J, hJ, hy⟩)))]
        exact hI J hJ
      · rw [hg ξ' ξ (fun y hy => hagree y (List.mem_append_right _ hy))]
        exact hgξ
  empty d ξ hd := by
    cases d with
    | none => exact hd.elim
    | some e =>
      simp only [nonrel]
      refine Bool.eq_false_iff.2 fun h => ?_
      obtain ⟨x, hx, he⟩ := List.any_eq_true.1 h
      have := hd x hx
      cases h' : dget vals xs e x with
      | nil => rw [h'] at this; simp at this
      | cons _ _ => rw [h'] at he; simp at he
  finite := nonrel_finite vals xs 𝔄 δₐ S

end nonrel

end CoreJS
