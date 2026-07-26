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

/-- Set inclusion on `P(L̂oc)`, the primitive order of Def. B4. -/
protected def ALocSet.Subset (A B : ALocSet) : Prop := ∀ l, A l → B l

instance : EmptyCollection ALocSet  := ⟨fun _ => False⟩
instance : Singleton ALoc ALocSet   := ⟨fun l l' => l' = l⟩
instance : Insert ALoc ALocSet      := ⟨fun l A l' => l' = l ∨ A l'⟩
instance : Union ALocSet            := ⟨fun A B l => A l ∨ B l⟩
instance : HasSubset ALocSet        := ⟨ALocSet.Subset⟩

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
def VSet.Le (V₁ V₂ : VSet) : Prop := ∀ v, V₁.Mem v → V₂.Mem v

/-- Union of value sets, absorbing on `⊤` (Def. B5.1.b). -/
def VSet.join : VSet → VSet → VSet
  | .top,     _        => .top
  | .vals _,  .top     => .top
  | .vals V₁, .vals V₂ => .vals (fun v => V₁ v ∨ V₂ v)

instance : EmptyCollection VSet := ⟨.vals fun _ => False⟩
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
  | call   (lf : ALoc) (Ls : List ALocSet)
  | ret    (lf : ALoc) (L : ALocSet)

/-- Abstract traces `t̂ ∈ T̂rc ::= ε̂ | â | t̂₁; t̂₂ | (t̂₁ | t̂₂) | t̂*`:
    regular expressions over `Âct`. -/
inductive ATrc where
  /-- `ε̂`: the empty trace. -/
  | emp
  /-- A single abstract action. -/
  | act  (a : AAct)
  /-- `t̂₁; t̂₂`: concatenation. -/
  | seq  (t₁ t₂ : ATrc)
  /-- `(t̂₁ | t̂₂)`: alternation. -/
  | alt  (t₁ t₂ : ATrc)
  /-- `t̂*`: Kleene star. -/
  | star (t : ATrc)

@[inherit_doc] scoped infixr:70 " ;; " => ATrc.seq

/-- Abstract outcomes `ô ∈ Ôut ::= · | r⟨L⟩`. -/
inductive AOut where
  | cont
  | ret (L : ALocSet)

/-! ### Bottom elements

The initial abstract state `(ĥ₀, ρ̂₀, δ̂₀)` of §5.1. -/

def ASto.bot : ASto := fun _ => ∅

def AHeap.bot : AHeap := { obj := fun _ _ => ∅, val := fun _ => ∅ }

def AReg.bot : AReg := { dep := fun _ => ∅, ac := ∅, sk := ∅ }

/-! ## Order relation (Definition B4) -/

/-- Def. B4.2. -/
def ASto.Le (ρ₁ ρ₂ : ASto) : Prop := ∀ x, ρ₁ x ⊆ ρ₂ x

/-- Def. B4.1 (with B4.1.a and B4.1.b). -/
def AHeap.Le (h₁ h₂ : AHeap) : Prop :=
  (∀ l p, h₁.obj l p ⊆ h₂.obj l p) ∧ (∀ l, (h₁.val l).Le (h₂.val l))

/-- Def. B4.3 (with B4.3.a–c).  Note the paper writes `δ̂₁ ∼α δ̂₂` in B4.3;
    `⊑` is meant. -/
def AReg.Le (δ₁ δ₂ : AReg) : Prop :=
  (∀ l, δ₁.dep l ⊆ δ₂.dep l) ∧ δ₁.ac ⊆ δ₂.ac ∧ δ₁.sk ⊆ δ₂.sk

/-- Def. B4.4.  Undefined — hence `False` — between a continuation and a
    return outcome (see REMARK 1 at the end of the file). -/
def AOut.Le : AOut → AOut → Prop
  | .cont,   .cont   => True
  | .ret L₁, .ret L₂ => L₁ ⊆ L₂
  | _,       _       => False

/-- Def. B4.5 (with B4.5.a–d).  Actions of different shapes, or calls/returns
    of different callees or arities, are unrelated. -/
def AAct.Le : AAct → AAct → Prop
  | .lookup L₁ L₂ L₃, .lookup M₁ M₂ M₃ => L₁ ⊆ M₁ ∧ L₂ ⊆ M₂ ∧ L₃ ⊆ M₃
  | .update L₁ L₂ L₃, .update M₁ M₂ M₃ => L₁ ⊆ M₁ ∧ L₂ ⊆ M₂ ∧ L₃ ⊆ M₃
  | .call lf Ls,      .call lf' Ms     => lf = lf' ∧ ALocSets.Le Ls Ms
  | .ret lf L,        .ret lf' L'      => lf = lf' ∧ L ⊆ L'
  | _,                _                => False

/-- Structural order on abstract traces.  This is *not* in Def. B4, but the
    [Weakening] rule of Fig. B7 requires `t̂ ⊑ t̂'` (see REMARK 2). -/
def ATrc.Le : ATrc → ATrc → Prop
  | .emp,       .emp       => True
  | .act a,     .act b     => a.Le b
  | .seq t₁ t₂, .seq u₁ u₂ => t₁.Le u₁ ∧ t₂.Le u₂
  | .alt t₁ t₂, .alt u₁ u₂ => t₁.Le u₁ ∧ t₂.Le u₂
  | .star t,    .star u    => t.Le u
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

/-- Def. B5.2. -/
def ASto.join (ρ₁ ρ₂ : ASto) : ASto := fun x => ρ₁ x ∪ ρ₂ x

/-- Def. B5.1 (with B5.1.a and B5.1.b). -/
def AHeap.join (h₁ h₂ : AHeap) : AHeap :=
  { obj := fun l p => h₁.obj l p ∪ h₂.obj l p
    val := fun l => VSet.join (h₁.val l) (h₂.val l) }

/-- Def. B5.3 (with B5.3.a–c). -/
def AReg.join (δ₁ δ₂ : AReg) : AReg :=
  { dep := fun l => δ₁.dep l ∪ δ₂.dep l
    ac  := δ₁.ac ∪ δ₂.ac
    sk  := δ₁.sk ∪ δ₂.sk }

instance : Join ALocSet := ⟨fun A B => A ∪ B⟩
instance : Join VSet    := ⟨VSet.join⟩
instance : Join ASto    := ⟨ASto.join⟩
instance : Join AHeap   := ⟨AHeap.join⟩
instance : Join AReg    := ⟨AReg.join⟩

/-- Def. B5.4.  *Partial*: `None` for a continuation joined with a return
    outcome (see REMARK 1). -/
def AOut.join : AOut → AOut → Option AOut
  | .cont,   .cont   => some .cont
  | .ret L₁, .ret L₂ => some (.ret (L₁ ∪ L₂))
  | _,       _       => none

/-- Pointwise join of argument-location lists, defined only for equal
    arities. -/
def ALocSets.join : List ALocSet → List ALocSet → Option (List ALocSet)
  | [],      []      => some []
  | L :: Ls, M :: Ms => (ALocSets.join Ls Ms).map (fun Ns => (L ∪ M) :: Ns)
  | _,       _       => none

/-- Def. B5.5 (with B5.5.a–d).  *Partial*: defined only for actions of the
    same shape, and, for calls and returns, of the same callee (and arity). -/
def AAct.join : AAct → AAct → Option AAct
  | .lookup L₁ L₂ L₃, .lookup M₁ M₂ M₃ =>
      some (.lookup (L₁ ∪ M₁) (L₂ ∪ M₂) (L₃ ∪ M₃))
  | .update L₁ L₂ L₃, .update M₁ M₂ M₃ =>
      some (.update (L₁ ∪ M₁) (L₂ ∪ M₂) (L₃ ∪ M₃))
  | .call lf Ls, .call lf' Ms =>
      if lf = lf' then (ALocSets.join Ls Ms).map (AAct.call lf) else none
  | .ret lf L, .ret lf' L' =>
      if lf = lf' then some (.ret lf (L ∪ L')) else none
  | _, _ => none

/-- Abstract traces have no join in Def. B5: the [If-Then-Else] rule of
    Fig. B7 combines branch traces with the regular alternation `t̂₁ | t̂₂`,
    which plays the role of the join at the trace level. -/
abbrev ATrc.join : ATrc → ATrc → ATrc := ATrc.alt

/-! ## Lemma B12 for the total domains

"The least upper bound is well defined for all abstract domains given the
defined order relation."  Below, the two halves of that statement — `⊔` is an
upper bound, and it is the least one — for every domain whose join is total.
The corresponding facts for `AOut` and `AAct` require Def. B5.4/B5.5 to be
made total first (REMARK 1); given that, they follow by case analysis on the
shape of the outcome/action. -/

theorem ALocSet.subset_refl (A : ALocSet) : A ⊆ A := fun _ h => h

theorem ALocSet.subset_trans {A B C : ALocSet} (h₁ : A ⊆ B) (h₂ : B ⊆ C) :
    A ⊆ C := fun l h => h₂ l (h₁ l h)

theorem ALocSet.subset_union_left (A B : ALocSet) : A ⊆ A ∪ B :=
  fun _ h => Or.inl h

theorem ALocSet.subset_union_right (A B : ALocSet) : B ⊆ A ∪ B :=
  fun _ h => Or.inr h

theorem ALocSet.union_subset {A B C : ALocSet} (h₁ : A ⊆ C) (h₂ : B ⊆ C) :
    A ∪ B ⊆ C := fun l h => Or.elim h (h₁ l) (h₂ l)

theorem VSet.le_refl (V : VSet) : V.Le V := fun _ h => h

theorem VSet.le_trans (V₁ V₂ V₃ : VSet) (h₁ : V₁.Le V₂) (h₂ : V₂.Le V₃) :
    V₁.Le V₃ := fun v h => h₂ v (h₁ v h)

theorem VSet.le_join_left : ∀ (V₁ V₂ : VSet), V₁.Le (V₁.join V₂)
  | .top,    _       => fun _ _ => trivial
  | .vals _, .top    => fun _ _ => trivial
  | .vals _, .vals _ => fun _ h => Or.inl h

theorem VSet.le_join_right : ∀ (V₁ V₂ : VSet), V₂.Le (V₁.join V₂)
  | .top,    .top    => fun _ _ => trivial
  | .top,    .vals _ => fun _ _ => trivial
  | .vals _, .top    => fun _ _ => trivial
  | .vals _, .vals _ => fun _ h => Or.inr h

theorem VSet.join_le : ∀ (V₁ V₂ W : VSet), V₁.Le W → V₂.Le W →
    (V₁.join V₂).Le W
  | .top,    _,       _, h₁, _  => h₁
  | .vals _, .top,    _, _,  h₂ => h₂
  | .vals _, .vals _, _, h₁, h₂ => fun v h => Or.elim h (h₁ v) (h₂ v)

theorem ASto.le_join_left (ρ₁ ρ₂ : ASto) : ρ₁.Le (ρ₁.join ρ₂) :=
  fun _ => ALocSet.subset_union_left _ _

theorem ASto.le_join_right (ρ₁ ρ₂ : ASto) : ρ₂.Le (ρ₁.join ρ₂) :=
  fun _ => ALocSet.subset_union_right _ _

theorem ASto.join_le {ρ₁ ρ₂ ρ : ASto} (h₁ : ρ₁.Le ρ) (h₂ : ρ₂.Le ρ) :
    (ρ₁.join ρ₂).Le ρ :=
  fun x => ALocSet.union_subset (h₁ x) (h₂ x)

theorem AHeap.le_join_left (h₁ h₂ : AHeap) : h₁.Le (h₁.join h₂) :=
  ⟨fun _ _ => ALocSet.subset_union_left _ _,
   fun l => VSet.le_join_left (h₁.val l) (h₂.val l)⟩

theorem AHeap.le_join_right (h₁ h₂ : AHeap) : h₂.Le (h₁.join h₂) :=
  ⟨fun _ _ => ALocSet.subset_union_right _ _,
   fun l => VSet.le_join_right (h₁.val l) (h₂.val l)⟩

theorem AHeap.join_le {h₁ h₂ h : AHeap} (k₁ : h₁.Le h) (k₂ : h₂.Le h) :
    (h₁.join h₂).Le h :=
  ⟨fun l p => ALocSet.union_subset (k₁.1 l p) (k₂.1 l p),
   fun l => VSet.join_le (h₁.val l) (h₂.val l) (h.val l) (k₁.2 l) (k₂.2 l)⟩

theorem AReg.le_join_left (δ₁ δ₂ : AReg) : δ₁.Le (δ₁.join δ₂) :=
  ⟨fun _ => ALocSet.subset_union_left _ _,
   ALocSet.subset_union_left _ _,
   ALocSet.subset_union_left _ _⟩

theorem AReg.le_join_right (δ₁ δ₂ : AReg) : δ₂.Le (δ₁.join δ₂) :=
  ⟨fun _ => ALocSet.subset_union_right _ _,
   ALocSet.subset_union_right _ _,
   ALocSet.subset_union_right _ _⟩

theorem AReg.join_le {δ₁ δ₂ δ : AReg} (k₁ : δ₁.Le δ) (k₂ : δ₂.Le δ) :
    (δ₁.join δ₂).Le δ :=
  ⟨fun l => ALocSet.union_subset (k₁.1 l) (k₂.1 l),
   ALocSet.union_subset k₁.2.1 k₂.2.1,
   ALocSet.union_subset k₁.2.2 k₂.2.2⟩

/-!
## REMARKS

**1. `⊔` on outcomes and actions is partial, but Fig. B7 uses it totally.**
Def. B5.4 defines `ô₁ ⊔ ô₂` only when both outcomes are continuations or both
are returns, yet the [If-Then-Else] rule of Fig. B7 computes `ô = ô₁ ⊔ ô₂`
for arbitrary branches — and the branches of, e.g.
`if (c) { return x } else { y := 1 }` disagree.  The same holds for the
`h₁ ⊔ h₂` of actions in Def. B5.5 wherever actions of different shapes meet.
A minimal fix for outcomes is to abstract `Out` by a pair rather than by a
sum, i.e.

```
structure AOut' where
  mayCont : Bool        -- the branch may fall through
  retLocs : ALocSet     -- locations it may return
```

ordered and joined componentwise, which is total and has `⟨false, ∅⟩` as
bottom.  The concretisation is then `· ∼α ô'` iff `ô'.mayCont`, and
`r⟨l⟩ ∼α ô'` iff `α(l) ∈ ô'.retLocs`.

**2. No order on abstract traces is given.**  Def. B4 omits `t̂₁ ⊑ t̂₂`, but
the [Weakening] rule of Fig. B7 and the statement of Theorem B15 both compare
traces.  `ATrc.Le` above is the structural reading (same regular skeleton,
componentwise larger location sets).  Note that this is a *different*
relation from the `ξ(t) ⊑ t̂` of §6.1/Theorem D7, which is language
membership: "the word obtained from the query trace `t` under `ξ` is one of
the traces modelled by `t̂`".  Using the same symbol for both is likely to
confuse a reviewer; giving the latter its own notation (say `t ∈ L(t̂)`) and
an explicit inductive definition would help.
-/

end CoreJS
