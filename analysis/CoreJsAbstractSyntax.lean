/-
  # Core JavaScript — Abstract Domains

  Formalisation of Appendix B.1 of
  "Model Checking Security Properties of Node.js Packages":

  * Fig. B1  — abstract domains of the static analysis
  * Def. B4  — order relation `⊑` of the abstract domains
  * Def. B5  — least upper bound `⊔` of the abstract domains

  Only `CoreJsSyntax.lean` is needed; the file is independent of the concrete
  semantics.  Plain Lean 4 — no Mathlib required.

  Two deliberate deviations from the paper are marked `REMARK` below and
  summarised at the end of the file.
-/

import CoreJsSyntax

namespace CoreJS

/-! ## Abstract locations

`l̂ ∈ L̂oc`.  Nothing below depends on the representation; the only requirement
is decidable equality.  The analysis of §5 uses a *finite* subset of `L̂oc`,
determined by the literal locations `l̂_v` and by the allocation strategy
`alloc_a(·, κ)`, which maps every instruction identifier `κ` to a fixed
abstract location. -/

def ALoc := Nat

instance : DecidableEq ALoc := inferInstanceAs (DecidableEq Nat)
instance : Repr ALoc        := inferInstanceAs (Repr Nat)
instance : Inhabited ALoc   := inferInstanceAs (Inhabited Nat)

/-! ## Sets of abstract locations, `P(L̂oc)` -/

/-- `P(L̂oc)`, represented as a predicate. -/
def ALocSet := ALoc → Prop

instance : EmptyCollection ALocSet  := ⟨fun _ => False⟩
instance : Singleton ALoc ALocSet   := ⟨fun l l' => l' = l⟩
instance : Insert ALoc ALocSet      := ⟨fun l A l' => l' = l ∨ A l'⟩
instance : Union ALocSet            := ⟨fun A B l => A l ∨ B l⟩
instance : HasSubset ALocSet        := ⟨fun A B => ∀ l, A l -> B l⟩

/-- Componentwise inclusion of argument-location lists (used for `Call`). -/
def ALocSets.Le : List ALocSet → List ALocSet → Prop
  | [],      []      => True
  | L :: Ls, M :: Ms => L ⊆ M ∧ ALocSets.Le Ls Ms
  | _,       _       => False

/-! ## Sets of values, `P(Val)^⊤`

Value sets extended with a distinguished element `⊤` denoting the set of all
values, produced by the widening of `⊕̂` (§5.1). -/

/-- `V ∈ P(Val)^⊤`. -/
inductive VSet where
  /-- A set of values, represented as a predicate. -/
  | vals (V : Val → Prop)
  /-- `⊤`: all possible values. -/
  | top

/-- Membership in a (possibly `⊤`) value set. -/
def VSet.Mem : VSet → Val → Prop
  | .vals V, v => V v
  | .top,    _ => True

/-- Inclusion of value sets (Def. B4.1.b), defined through membership so that
    `⊤` is the greatest element. -/
def VSet.Subset (V₁ V₂ : VSet) : Prop := ∀ v, V₁.Mem v → V₂.Mem v
def VSet.Le := VSet.Subset

/-- Union of value sets, absorbing on `⊤` (Def. B5.1.b). -/
def VSet.join : VSet → VSet → VSet
  | .top,     _        => .top
  | .vals _,  .top     => .top
  | .vals V₁, .vals V₂ => .vals (fun v => V₁ v ∨ V₂ v)

instance : EmptyCollection VSet := ⟨.vals fun _ => False⟩
instance : Membership Val VSet  := ⟨VSet.Mem⟩
instance : HasSubset VSet       := ⟨VSet.Subset⟩
instance : Union VSet           := ⟨VSet.join⟩

/-! ## Abstract domains (Fig. B1)

REMARK.  The paper writes the maps of Fig. B1 as *partial* (`⇀`) but always
uses them totally: `ρ̂(x)`, `ĥ.obj(l̂, p)`, `δ̂.dep(l̂)` denote sets, and are read
as `∅` outside the domain (e.g. in the [Object Initialization] rule and in
Def. B4).  We therefore model them as total maps into the corresponding
bottom element, which makes Def. B4 as literally stated equivalent to the
pointwise order below. -/

/-- Abstract stores `ρ̂ ∈ Ŝto : Var ⇀ P(L̂oc)`. -/
def ASto := Var → ALocSet

/-- Abstract heaps `ĥ ∈ Ĥ`:
    * `obj : L̂oc × Str ⇀ P(L̂oc)`
    * `val : L̂oc ⇀ P(Val)^⊤` -/
structure AHeap where
  obj : ALoc → PropName → ALocSet
  val : ALoc → VSet

/-- Abstract taint registers `δ̂ ∈ R̂eg`. -/
structure AReg where
  dep : ALoc → ALocSet
  ac  : ALocSet
  sk  : ALocSet

/-- Abstract trace actions `â ∈ Âct`.

    ```
    â ::= L₁ := L₂[L₃] | L₁[L₂] := L₃ | Call(l̂_f, [L₁, ..., Lₙ]) | Ret(l̂_f, L)
    ```
    Note that, as in Fig. B1, the callee of a call/return action is a single
    abstract location, not a set. -/
inductive AAct where
  | lookup (L₁ L₂ L₃ : ALocSet)
  | update (L₁ L₂ L₃ : ALocSet)
  | call   (al_f : ALoc) (Ls : List ALocSet)
  | ret    (al_f : ALoc) (L : ALocSet)

/-- Abstract traces `t̂ ∈ T̂rc ::= ε̂ | â | t̂₁; t̂₂ | (t̂₁ | t̂₂) | t̂*`:
    regular expressions over `Âct`. -/
inductive ATrc where
  /-- `ε̂`: the empty trace. -/
  | emp
  /-- A single abstract action. -/
  | act  (a : AAct)
  /-- `t̂₁; t̂₂`: concatenation. -/
  | seq  (t₁ t₂ : ATrc)
  /-- `t̂₁ | t̂₂`: alternation. -/
  | alt  (t₁ t₂ : ATrc)
  /-- `t̂*`: Kleene star. -/
  | star (t : ATrc)
  /-- `X`: the recursion variable, standing for the enclosing `μ`-bound body.
      Emitted at a recursive call site whose summary is being assumed. -/
  | tvar
  /-- `μX. t̂`: the trace of a recursive function, with `X` marking the
      recursive occurrences of its own body.

      Semantics is by unfolding (`ATrc.subst`), so this denotes the *exact*
      set of traces at every recursion depth — a context-free language in
      general. The model builder's automaton, which turns the recursive
      occurrence into a back-edge, is a further *regular over-approximation*
      of this: for a body `w | (u; Call; X; Ret; v)` the exact language is
      `{(u·Call)ⁿ; w; (Ret·v)ⁿ}` while the back-edge automaton accepts
      `(u·Call)*; w; (Ret·v)*`, i.e. the same traces plus unbalanced ones.
      Soundness against `μ` therefore implies soundness against the
      automaton, and the proof keeps the sharper statement. -/
  | mu (t : ATrc)

@[inherit_doc] scoped infixr:70 (name := atrcSeq) " ;; " => ATrc.seq
@[inherit_doc] scoped infixr:65 (name := atrcAlt) " || " => ATrc.alt
@[inherit_doc] scoped postfix:80 (name := atrcStar) "*" => ATrc.star

/-- `t̂[X := û]`: substitution for the recursion variable.

    A nested `μ` binds its own `X`, so substitution does not descend into it
    (there is a single recursion variable, which suffices for the one function
    whose summary is currently being assumed). -/
def ATrc.subst : ATrc → ATrc → ATrc
  | .emp,       _ => .emp
  | .act a,     _ => .act a
  | .seq t₁ t₂, u => .seq (t₁.subst u) (t₂.subst u)
  | .alt t₁ t₂, u => .alt (t₁.subst u) (t₂.subst u)
  | .star t,    u => .star (t.subst u)
  | .tvar,      u => u
  | .mu t,      _ => .mu t

/-- One-step unfolding `μX. t̂  ↝  t̂[X := μX. t̂]`. -/
def ATrc.unfold (t : ATrc) : ATrc := t.subst (.mu t)

/-- A list of alternative traces, folded into a choice tree.  This is the
    natural representation of a call site whose callee expression may resolve to
    several abstract locations. -/
def ATrc.choice : List ATrc → ATrc
  | []      => .emp
  | [t]     => t
  | t :: ts => .alt t (ATrc.choice ts)

/-- Abstract outcomes `ô ∈ Ôut ::= { ⟨·|r, L⟩`. -/
inductive AOutKind where
  | cont
  | ret

structure AOut where
  kind : AOutKind
  locs : ALocSet

/-! ### Bottom elements

The initial abstract state `(ĥ₀, ρ̂₀, δ̂₀)` of §5.1. -/

def ASto.bot : ASto := fun _ => ∅

def AHeap.bot : AHeap := { obj := fun _ _ => ∅, val := fun _ => ∅ }

def AReg.bot : AReg := { dep := fun _ => ∅, ac := ∅, sk := ∅ }

/-! ## Order relation (Definition B4) -/

/-- Def. B4.1 (with B4.1.a and B4.1.b). -/
def AHeap.Le (h₁ h₂ : AHeap) : Prop :=
  (∀ l p, h₁.obj l p ⊆ h₂.obj l p) ∧ (∀ l, (h₁.val l) ⊆ (h₂.val l))

/-- Def. B4.2. -/
def ASto.Le (ρ₁ ρ₂ : ASto) : Prop := ∀ x, ρ₁ x ⊆ ρ₂ x

/-- Def. B4.3 (with B4.3.a–c) -/
def AReg.Le (δ₁ δ₂ : AReg) : Prop :=
  (∀ l, δ₁.dep l ⊆ δ₂.dep l) ∧ δ₁.ac ⊆ δ₂.ac ∧ δ₁.sk ⊆ δ₂.sk

/-- Def. B4.4 (with B4.4.a-c) -/
def AOut.Le : AOut → AOut → Prop
  | ⟨.ret, L₁⟩, ⟨.ret, L₂⟩   => L₁ ⊆ L₂
  | ⟨.ret, L₁⟩, ⟨.cont, L₂⟩  => L₁ ⊆ L₂
  | ⟨.cont, L₁⟩, ⟨.cont, L₂⟩ => L₁ ⊆ L₂
  | ⟨.cont, _⟩, ⟨.ret, _⟩ => False

/-- Def. B4.5 (with B4.5.a–d).  Actions of different shapes, or calls/returns
    of different callees or arities, are unrelated. -/
def AAct.Le : AAct → AAct → Prop
  | .lookup L₁ L₂ L₃, .lookup M₁ M₂ M₃ => L₁ ⊆ M₁ ∧ L₂ ⊆ M₂ ∧ L₃ ⊆ M₃
  | .update L₁ L₂ L₃, .update M₁ M₂ M₃ => L₁ ⊆ M₁ ∧ L₂ ⊆ M₂ ∧ L₃ ⊆ M₃
  | .call al_f Ls,    .call al_f' Ms   => al_f = al_f' ∧ ALocSets.Le Ls Ms
  | .ret al_f L,      .ret al_f' L'    => al_f = al_f' ∧ L ⊆ L'
  | _,                _                => False

/-- Def. B4.6 (with B4.6.a-d). -/
def ATrc.Le : ATrc → ATrc → Prop
  | .emp,       .emp       => True
  | .act a,     .act b     => a.Le b
  | .seq t₁ t₂, .seq u₁ u₂ => t₁.Le u₁ ∧ t₂.Le u₂
  | .alt t₁ t₂, .alt u₁ u₂ => t₁.Le u₁ ∧ t₂.Le u₂
  | .star t,    .star u    => t.Le u
  | .tvar,      .tvar      => True
  | .mu t,      .mu u      => t.Le u
  | _,          _          => False

instance : LE VSet  := ⟨VSet.Le⟩
instance : LE ASto  := ⟨ASto.Le⟩
instance : LE AHeap := ⟨AHeap.Le⟩
instance : LE AReg  := ⟨AReg.Le⟩
instance : LE AOut  := ⟨AOut.Le⟩
instance : LE AAct  := ⟨AAct.Le⟩
instance : LE ATrc  := ⟨ATrc.Le⟩

/-- The paper's `⊑`. -/
scoped infix:50 " ⊑ " => LE.le

/-! ## Least upper bound (Definition B5) -/

/-- A total binary join.  (`⊔` is not part of core Lean; we introduce it
    locally rather than depending on Mathlib's order hierarchy.) -/
class Join (α : Type) where
  /-- The least upper bound of two elements of `α`. -/
  join : α → α → α

@[inherit_doc] scoped infixl:65 " ⊔ " => Join.join

/-- Def. B5.1 (with B5.1.a and B5.1.b). -/
def AHeap.join (h₁ h₂ : AHeap) : AHeap :=
  { obj := fun l p => h₁.obj l p ∪ h₂.obj l p
    val := fun l => (h₁.val l) ∪ (h₂.val l) }

/-- Def. B5.2. -/
def ASto.join (ρ₁ ρ₂ : ASto) : ASto := fun x => ρ₁ x ∪ ρ₂ x

/-- Def. B5.3 (with B5.3.a–c). -/
def AReg.join (δ₁ δ₂ : AReg) : AReg :=
  { dep := fun l => δ₁.dep l ∪ δ₂.dep l
    ac  := δ₁.ac ∪ δ₂.ac
    sk  := δ₁.sk ∪ δ₂.sk }

/-- Def. B5.4 (with B5.4.a-c). -/
def AOut.join : AOut → AOut → AOut
  | ⟨.ret, L₁⟩, ⟨.ret, L₂⟩ => ⟨.ret, L₁ ∪ L₂⟩
  | ⟨_, L₁⟩,    ⟨_, L₂⟩    => ⟨.cont, L₁ ∪ L₂⟩


/-- Pointwise join of argument-location lists, defined only for equal
    arities. -/
def ALocSets.join : List ALocSet → List ALocSet → Option (List ALocSet)
  | [],      []      => some []
  | L :: Ls, M :: Ms => (ALocSets.join Ls Ms).map (fun Ns => (L ∪ M) :: Ns)
  | _,       _       => none

instance : Join VSet    := ⟨VSet.join⟩
instance : Join ALocSet := ⟨fun A B => A ∪ B⟩
instance : Join AHeap   := ⟨AHeap.join⟩
instance : Join ASto    := ⟨ASto.join⟩
instance : Join AReg    := ⟨AReg.join⟩
instance : Join AOut    := ⟨AOut.join⟩

/-! ## Lemma B12 for the total domains

"The least upper bound is well defined for all abstract domains given the
defined order relation."  Below, the two halves of that statement — `⊔` is an
upper bound, and it is the least one — for every domain whose join is total.
The corresponding facts for `AAct` require Def. B5.5 to be
made total first (REMARK 1); given that, they follow by case analysis on the
shape of the outcome/action. -/

theorem ALocSet.subset_refl (A : ALocSet) : A ⊆ A := by
  -- `A ⊆ A` unfolds to `∀ l, A l → A l`.
  intro _ h
  exact h

theorem ALocSet.subset_antisymm (A B : ALocSet) (h₁ : A ⊆ B) (h₂ : B ⊆ A) :
    A = B := by
  funext l
  apply propext
  constructor
  · intro hA
    exact h₁ l hA
  · intro hB
    exact h₂ l hB

theorem ALocSet.subset_trans (A B C : ALocSet) (h₁ : A ⊆ B) (h₂ : B ⊆ C) :
    A ⊆ C := by
  intro l h
  exact h₂ l (h₁ l h)

theorem ALocSet.subset_union_left (A B : ALocSet) : A ⊆ A ∪ B := by
  -- membership in `A ∪ B` is the disjunction `A l ∨ B l`.
  intro _ h
  exact Or.inl h

theorem ALocSet.subset_union_right (A B : ALocSet) : B ⊆ A ∪ B := by
  intro _ h
  exact Or.inr h

theorem ALocSet.union_subset (A B C : ALocSet) (h₁ : A ⊆ C) (h₂ : B ⊆ C) :
    A ∪ B ⊆ C := by
  intro l h
  rcases h with hA | hB
  · exact h₁ l hA
  · exact h₂ l hB

theorem VSet.le_refl (V : VSet) : V ⊑ V := by
  intro _ h
  exact h

theorem VSet.le_trans (V₁ V₂ V₃ : VSet) (h₁ : V₁ ⊑ V₂) (h₂ : V₂ ⊑ V₃) :
    V₁.Le V₃ := by
  intro v h
  exact h₂ v (h₁ v h)

theorem VSet.le_join_left (V₁ V₂ : VSet) : V₁ ⊑ (V₁ ⊔ V₂) := by
  cases V₁ with
  | top =>
      -- the join is `⊤`, and everything is `⊤`-membered.
      intro _ _
      exact trivial
  | vals V =>
      cases V₂ with
      | top =>
          intro _ _
          exact trivial
      | vals W =>
          intro _ h
          exact Or.inl h

theorem VSet.le_join_right (V₁ V₂ : VSet) : V₂ ⊑ (V₁ ⊔ V₂) := by
  cases V₁ with
  | top =>
      intro _ _
      exact trivial
  | vals V =>
      cases V₂ with
      | top =>
          intro _ _
          exact trivial
      | vals W =>
          intro _ h
          exact Or.inr h

theorem VSet.join_le (V₁ V₂ W : VSet) (h₁ : V₁ ⊑ W) (h₂ : V₂ ⊑ W) :
    (V₁ ⊔ V₂) ⊑ W := by
  cases V₁ with
  | top =>
      -- the join *is* `V₁` here, so `h₁` already is the goal.
      exact h₁
  | vals V =>
      cases V₂ with
      | top => exact h₂
      | vals U =>
          intro v h
          rcases h with hV | hU
          · exact h₁ v hV
          · exact h₂ v hU

theorem ASto.le_refl (ρ₁ : ASto) : ρ₁ ⊑ ρ₁ := by
  intro _
  exact ALocSet.subset_refl _

theorem ASto.le_antisymm (ρ₁ ρ₂ : ASto) (h₁ : ρ₁ ⊑ ρ₂) (h₂ : ρ₂ ⊑ ρ₁) :
    ρ₁ = ρ₂ := by
  funext x
  exact ALocSet.subset_antisymm (ρ₁ x) (ρ₂ x) (h₁ x) (h₂ x)

theorem ASto.le_trans (ρ₁ ρ₂ ρ₃ : ASto) (h₁ : ρ₁ ⊑ ρ₂) (h₂ : ρ₂ ⊑ ρ₃) :
    ρ₁ ⊑ ρ₃ := by
  intro x
  exact ALocSet.subset_trans (ρ₁ x) (ρ₂ x) (ρ₃ x) (h₁ x) (h₂ x)

theorem ASto.le_join_left (ρ₁ ρ₂ : ASto) : ρ₁ ⊑ (ρ₁ ⊔ ρ₂) := by
  intro _
  exact ALocSet.subset_union_left _ _

theorem ASto.le_join_right (ρ₁ ρ₂ : ASto) : ρ₂ ⊑ (ρ₁ ⊔ ρ₂) := by
  intro _
  exact ALocSet.subset_union_right _ _

theorem ASto.join_le {ρ₁ ρ₂ ρ : ASto} (h₁ : ρ₁ ⊑ ρ) (h₂ : ρ₂ ⊑ ρ) :
    (ρ₁.join ρ₂).Le ρ := by
  intro x
  exact ALocSet.union_subset (ρ₁ x) (ρ₂ x) (ρ x) (h₁ x) (h₂ x)

theorem AHeap.le_refl (h₁ : AHeap) : h₁ ⊑ h₁ := by
  refine ⟨?_, ?_⟩
  · intro _ _
    exact ALocSet.subset_refl _
  · intro l
    exact VSet.le_refl (h₁.val l)

theorem AHeap.le_trans (h₁ h₂ h₃ : AHeap) (hy₁ : h₁ ⊑ h₂) (hy₂ : h₂ ⊑ h₃) :
    h₁ ⊑ h₃ := by
    refine ⟨?_, ?_⟩
    · intro l p
      exact ALocSet.subset_trans (h₁.obj l p) (h₂.obj l p) (h₃.obj l p) (hy₁.1 l p) (hy₂.1 l p)
    · intro l
      exact VSet.le_trans (h₁.val l) (h₂.val l) (h₃.val l) (hy₁.2 l) (hy₂.2 l)

theorem AHeap.le_join_left (h₁ h₂ : AHeap) : h₁ ⊑ (h₁ ⊔ h₂) := by
  -- `AHeap.Le` is a conjunction: one goal for `obj`, one for `val`.
  refine ⟨?_, ?_⟩
  · intro _ _
    exact ALocSet.subset_union_left _ _
  · intro x
    exact VSet.le_join_left (h₁.val x) (h₂.val x)

theorem AHeap.le_join_right (h₁ h₂ : AHeap) : h₂ ⊑ (h₁ ⊔ h₂) := by
  refine ⟨?_, ?_⟩
  · intro _ _
    exact ALocSet.subset_union_right _ _
  · intro l
    exact VSet.le_join_right (h₁.val l) (h₂.val l)

theorem AHeap.join_le {h₁ h₂ h : AHeap} (k₁ : h₁ ⊑ h) (k₂ : h₂ ⊑ h) :
    (h₁ ⊔ h₂) ⊑ h := by
  refine ⟨?_, ?_⟩
  · intro l p
    exact ALocSet.union_subset (h₁.obj l p) (h₂.obj l p) (h.obj l p) (k₁.1 l p) (k₂.1 l p)
  · intro l
    exact VSet.join_le (h₁.val l) (h₂.val l) (h.val l) (k₁.2 l) (k₂.2 l)

theorem AReg.le_refl (δ : AReg) : δ ⊑ δ := by
  refine ⟨?_, ?_, ?_⟩
  · intro _
    exact ALocSet.subset_refl _
  · exact ALocSet.subset_refl _
  · exact ALocSet.subset_refl _

theorem AReg.le_antisymm (δ₁ δ₂ : AReg) (h₁ : δ₁ ⊑ δ₂) (h₂ : δ₂ ⊑ δ₁) :
    δ₁ = δ₂ := by
  cases δ₁ with
  | mk dep₁ ac₁ sk₁ =>
      cases δ₂ with
      | mk dep₂ ac₂ sk₂ =>
          have hdep : dep₁ = dep₂ := by
            funext l
            exact ALocSet.subset_antisymm (dep₁ l) (dep₂ l) (h₁.1 l) (h₂.1 l)
          have hac : ac₁ = ac₂ :=
            ALocSet.subset_antisymm ac₁ ac₂ h₁.2.1 h₂.2.1
          have hsk : sk₁ = sk₂ :=
            ALocSet.subset_antisymm sk₁ sk₂ h₁.2.2 h₂.2.2
          cases hdep
          cases hac
          cases hsk
          rfl

theorem AReg.le_trans (δ₁ δ₂ δ₃ : AReg) (h₁ : δ₁ ⊑ δ₂) (h₂ : δ₂ ⊑ δ₃) :
    δ₁ ⊑ δ₃ := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ALocSet.subset_trans (δ₁.dep x) (δ₂.dep x) (δ₃.dep x) (h₁.1 x) (h₂.1 x)
  · exact ALocSet.subset_trans δ₁.ac δ₂.ac δ₃.ac h₁.2.1 h₂.2.1
  · exact ALocSet.subset_trans δ₁.sk δ₂.sk δ₃.sk h₁.2.2 h₂.2.2

theorem AReg.le_join_left (δ₁ δ₂ : AReg) : δ₁ ⊑ (δ₁ ⊔ δ₂) := by
  -- three goals: `dep`, `ac`, `sk`.
  refine ⟨?_, ?_, ?_⟩
  · intro _
    exact ALocSet.subset_union_left _ _
  · exact ALocSet.subset_union_left _ _
  · exact ALocSet.subset_union_left _ _

theorem AReg.le_join_right (δ₁ δ₂ : AReg) : δ₂ ⊑ (δ₁ ⊔ δ₂) := by
  refine ⟨?_, ?_, ?_⟩
  · intro _
    exact ALocSet.subset_union_right _ _
  · exact ALocSet.subset_union_right _ _
  · exact ALocSet.subset_union_right _ _

theorem AReg.join_le {δ₁ δ₂ δ : AReg} (k₁ : δ₁ ⊑ δ) (k₂ : δ₂ ⊑ δ) :
    (δ₁ ⊔ δ₂) ⊑ δ := by
  refine ⟨?_, ?_, ?_⟩
  · intro l
    exact ALocSet.union_subset (δ₁.dep l) (δ₂.dep l) (δ.dep l) (k₁.1 l) (k₂.1 l)
  · exact ALocSet.union_subset δ₁.ac δ₂.ac δ.ac k₁.2.1 k₂.2.1
  · exact ALocSet.union_subset δ₁.sk δ₂.sk δ.sk k₁.2.2 k₂.2.2

/-! ## Finite folds over branch results (used by [Function Call])

A call site whose callee resolves to several candidate functions produces one
result per candidate.  Those results are combined with the ordinary binary
joins, folded over the (finite) candidate list; `AHeap.bot` / `AReg.bot` / `∅`
are the units of those folds. -/

/-- `⨆ hs`, the join of a finite list of abstract heaps. -/
def AHeap.joinAll (hs : List AHeap) : AHeap := hs.foldr AHeap.join AHeap.bot

/-- `⨆ δs`, the join of a finite list of abstract taint registers. -/
def AReg.joinAll (ds : List AReg) : AReg := ds.foldr AReg.join AReg.bot

/-- `⋃ Ls`, the union of a finite list of abstract location sets. -/
def ALocSet.unionAll (Ls : List ALocSet) : ALocSet := Ls.foldr (· ∪ ·) ∅

theorem AHeap.bot_le (h : AHeap) : AHeap.bot ⊑ h := by
  refine ⟨?_, ?_⟩
  · intro _ _ _ hm
    exact False.elim hm
  · intro _ v hm
    exact False.elim hm

theorem AReg.bot_le (δ : AReg) : AReg.bot ⊑ δ := by
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ hm
    exact False.elim hm
  · intro _ hm
    exact False.elim hm
  · intro _ hm
    exact False.elim hm

/-- Every element of the list is below the fold: the fold is an upper bound. -/
theorem AHeap.le_joinAll {h : AHeap} : ∀ {hs : List AHeap}, h ∈ hs → h ⊑ AHeap.joinAll hs
  | k :: ks, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htl
      · exact AHeap.le_join_left _ _
      · exact AHeap.le_trans _ _ _ (AHeap.le_joinAll htl)
          (AHeap.le_join_right k (AHeap.joinAll ks))

theorem AReg.le_joinAll {δ : AReg} : ∀ {ds : List AReg}, δ ∈ ds → δ ⊑ AReg.joinAll ds
  | k :: ks, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htl
      · exact AReg.le_join_left _ _
      · exact AReg.le_trans _ _ _ (AReg.le_joinAll htl)
          (AReg.le_join_right k (AReg.joinAll ks))

theorem ALocSet.subset_unionAll {L : ALocSet} :
    ∀ {Ls : List ALocSet}, L ∈ Ls → L ⊆ ALocSet.unionAll Ls
  | K :: Ks, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htl
      · exact ALocSet.subset_union_left _ _
      · exact ALocSet.subset_trans _ _ _ (ALocSet.subset_unionAll htl)
          (ALocSet.subset_union_right K (ALocSet.unionAll Ks))

end CoreJS
