/-
  # Core JavaScript — Translating Queries into Query Models

  The construction of the query model of a query (`Query.toQModel`), and the
  theorem that it is semantically equivalent to the query
  (`Query.toQModel_correct`): for a well-formed program `q :: Δ`, an execution
  record satisfies the model of `q` applied to `ls` iff it matches `q`
  applied to `ls` (`Exec.Matches`).  This holds for the whole query language,
  `except` and invocation included.

  ## Construction

  Patterns are translated compositionally (`Pat.build`), each combinator
  being an automaton construction (`QComp.eps`, `.act`, `.alt`, `.seq`,
  `.both`):

  * `ε` is a single state with an `Any` loop, start and final;
  * `a` reads `Any*`, then `a`, then `Any*`;
  * `F₁ ‖ F₂` is the disjoint union, with a new start and `ε`-edges into
    both;
  * `F₁ ; F₂` runs `F₁` to one of its final states `f`, then an `ε`-edge
    enters a copy of `F₂` *specific to `f`* (`seqR f s`): the copy keeps
    `f`'s labels, so a state still determines the invocations used to reach
    it;
  * `F₁ & F₂` is the synchronous product: a step moves either side alone on
    an `ε`-edge, or both sides on the same trace action (an action edge of
    one side may be the `Any` loop of the other: that is how one side
    progresses while the other waits; a step where both sides progress uses
    one trace action for both, so `a & a` matches a single `a`);
  * `Q(zs)` inlines the body of `Q` (`QBody.build`): `Q`'s parameters are
    renamed to the arguments, its locals to fresh tags `tag n y`
    (`Query.ren`), its `when` is added to `inv` of all its states and its
    locals to their `scope`; its `except` becomes a new component, added to
    `exc` of its states.  An invocation that cannot be resolved, or has the
    wrong number of arguments, never matches in the query semantics, and
    becomes an automaton with no final state.

  Invocations are resolved as `QProg.interp` resolves them: by a builder for
  invocations (`Builder`), defined by recursion on the program
  (`QProg.build`), so that every function here is structurally recursive.

  ## Proof

  * `Built`: the bookkeeping invariants of a construction — the tags it mints
    are fresh, its scope consists of them, it reads nothing minted later
    (`QComp.ReadsIn`), and it is `Closed` and `Mono`.
  * `Correct`: acceptance of `t[i..j)` agrees with the query semantics
    matching from `i` to some `j' ≤ j` (runs read the whole stretch, the
    query semantics stops at its last action).
  * `PatOK` / `BuilderOK`: every pattern / invocation construction is `Built`
    and `Correct`, for fuel at least the length of the program it resolves
    invocations in.  `patOK` derives the first from the second, by induction
    on the pattern; `bodyOK` handles a query body; `buildOK` proves
    `BuilderOK` of `QProg.build Δ` by induction on `Δ`.

  The interplay of `scope` and the query semantics' nested existentials: a
  pattern's acceptance under `ξ` chooses new values for the tags of the run,
  so it only depends on `ξ` through the pattern's own variables
  (`Correct.transfer`); this is what lets the two halves of `;` and `&` be
  combined under one substitution, together with the fact that each half
  reads none of the other's tags (`Built.reads`).

  Plain Lean 4 — no Mathlib required.
-/

import Queries.QueryModel.CoreJsQModelSemantics

namespace CoreJS

/-! ## Automaton constructions -/

/-- The edge `e` with both endpoints mapped by `w`. -/
def QEdge.lift (w : QSt → QSt) (e : QEdge) : QEdge := (w e.1, e.2.1, w e.2.2)

/-- No final state: the automaton of an unresolvable invocation. -/
def QComp.empty : QComp where
  start  := .s0
  states := [.s0]
  edges  := [(.s0, .any, .s0)]
  finals := []
  inv    := fun _ => []
  scope  := fun _ => []
  exc    := fun _ => []

/-- `ε`. -/
def QComp.eps : QComp := { QComp.empty with finals := [.s0] }

/-- `a`: `Any*`, then `a`, then `Any*`. -/
def QComp.act (a : QAct MVar) : QComp where
  start  := .s0
  states := [.s0, .s1]
  edges  := [(.s0, .any, .s0), (.s0, .act [a], .s1), (.s1, .any, .s1)]
  finals := [.s1]
  inv    := fun _ => []
  scope  := fun _ => []
  exc    := fun _ => []

/-- Labels of `‖`, `;` and `&` from those of the parts. -/
def Lbl.alt {α} (fA fB : QSt → List α) : QSt → List α
  | .altL s => fA s
  | .altR s => fB s
  | _       => []

def Lbl.seq {α} (fA fB : QSt → List α) : QSt → List α
  | .seqL s   => fA s
  | .seqR f s => fA f ++ fB s
  | _         => []

def Lbl.both {α} (fA fB : QSt → List α) : QSt → List α
  | .both a b => fA a ++ fB b
  | _         => []

/-- `F₁ ‖ F₂`. -/
def QComp.alt (A B : QComp) : QComp where
  start  := .altS
  states := .altS :: (A.states.map .altL ++ B.states.map .altR)
  edges  := (.altS, .eps, .altL A.start) :: (.altS, .eps, .altR B.start) ::
              (A.edges.map (QEdge.lift .altL) ++ B.edges.map (QEdge.lift .altR))
  finals := A.finals.map .altL ++ B.finals.map .altR
  inv    := Lbl.alt A.inv B.inv
  scope  := Lbl.alt A.scope B.scope
  exc    := Lbl.alt A.exc B.exc

/-- `F₁ ; F₂`, with one copy of `F₂` per final state of `F₁`. -/
def QComp.seq (A B : QComp) : QComp where
  start  := .seqL A.start
  states := A.states.map .seqL ++ A.finals.flatMap (fun f => B.states.map (.seqR f))
  edges  := A.edges.map (QEdge.lift .seqL) ++
              A.finals.flatMap (fun f =>
                (.seqL f, .eps, .seqR f B.start) :: B.edges.map (QEdge.lift (.seqR f)))
  finals := A.finals.flatMap (fun f => B.finals.map (.seqR f))
  inv    := Lbl.seq A.inv B.inv
  scope  := Lbl.seq A.scope B.scope
  exc    := Lbl.seq A.exc B.exc

/-- The `ε`-edges of an edge list. -/
def epsEdges (es : List QEdge) : List (QSt × QSt) :=
  es.filterMap fun e => match e.2.1 with
    | .eps   => some (e.1, e.2.2)
    | .act _ => none

/-- The action edges of an edge list. -/
def actEdges (es : List QEdge) : List (QSt × List (QAct MVar) × QSt) :=
  es.filterMap fun e => match e.2.1 with
    | .eps    => none
    | .act as => some (e.1, as, e.2.2)

/-- `F₁ & F₂`: the synchronous product. -/
def QComp.both (A B : QComp) : QComp where
  start  := .both A.start B.start
  states := A.states.flatMap (fun a => B.states.map (.both a))
  edges  := (epsEdges A.edges).flatMap (fun e => B.states.map fun b =>
                (.both e.1 b, .eps, .both e.2 b)) ++
            (epsEdges B.edges).flatMap (fun e => A.states.map fun a =>
                (.both a e.1, .eps, .both a e.2)) ++
            (actEdges A.edges).flatMap (fun e => (actEdges B.edges).map fun e' =>
                (.both e.1 e'.1, .act (e.2.1 ++ e'.2.1), .both e.2.2 e'.2.2))
  finals := A.finals.flatMap (fun a => B.finals.map (.both a))
  inv    := Lbl.both A.inv B.inv
  scope  := Lbl.both A.scope B.scope
  exc    := Lbl.both A.exc B.exc

/-- A query body around the automaton of its pattern: its invariant, its
    locals and its `except` components on every state. -/
def QComp.guard (A : QComp) (I : Inv MVar) (locs : List MVar) (ks : List Nat) : QComp :=
  { A with inv := fun s => I :: A.inv s, scope := fun s => locs ++ A.scope s,
           exc := fun s => ks ++ A.exc s }

/-! ## The translation -/

/-- The result of a construction: the automaton, the next fresh tag, and the
    `except` components so far. -/
structure BRes where
  comp  : QComp
  next  : Nat
  comps : List QComp

/-- Constructing the automaton of an invocation `Q(args)`, with fresh tags
    from `n` and the components so far `cs`. -/
abbrev Builder := QName → List MVar → Nat → List QComp → BRes

/-- The automaton of a pattern whose variables are renamed by `ρ`. -/
def Pat.build (Ψ : Builder) (ρ : Var → MVar) : Pat → Nat → List QComp → BRes
  | .eps,        n, cs => ⟨.eps, n, cs⟩
  | .act a,      n, cs => ⟨.act (a.map ρ), n, cs⟩
  | .query Q zs, n, cs => Ψ Q (zs.map ρ) n cs
  | .seq F G,    n, cs =>
      let r₁ := Pat.build Ψ ρ F n cs
      let r₂ := Pat.build Ψ ρ G r₁.next r₁.comps
      ⟨.seq r₁.comp r₂.comp, r₂.next, r₂.comps⟩
  | .alt F G,    n, cs =>
      let r₁ := Pat.build Ψ ρ F n cs
      let r₂ := Pat.build Ψ ρ G r₁.next r₁.comps
      ⟨.alt r₁.comp r₂.comp, r₂.next, r₂.comps⟩
  | .both F G,   n, cs =>
      let r₁ := Pat.build Ψ ρ F n cs
      let r₂ := Pat.build Ψ ρ G r₁.next r₁.comps
      ⟨.both r₁.comp r₂.comp, r₂.next, r₂.comps⟩

/-- The automaton of a query body whose variables are renamed by `ρ`; its
    `except` pattern, if any, becomes the last component. -/
def QBody.build (Ψ : Builder) (ρ : Var → MVar) (P : QBody) (n : Nat) (cs : List QComp) : BRes :=
  let r := Pat.build Ψ ρ P.pattern n cs
  match P.except with
  | none    => ⟨r.comp.guard (P.when.map ρ) (P.locals.map ρ) [], r.next, r.comps⟩
  | some F' =>
      let e := Pat.build Ψ ρ F' r.next r.comps
      ⟨r.comp.guard (P.when.map ρ) (P.locals.map ρ) [e.comps.length], e.next, e.comps ++ [e.comp]⟩

/-- The value bound to `x` by binding `ys` to `as`, first match first, as in
    `LEnv.bind`. -/
def assoc (x : Var) : List Var → List MVar → Option MVar
  | y :: ys, a :: as => if x = y then some a else assoc x ys as
  | _,       _       => none

/-- The renaming of `q`'s variables when it is invoked with `args` as the
    `n`-th invocation: locals become `tag n y`, parameters the arguments. -/
def Query.ren (q : Query) (args : List MVar) (n : Nat) (x : Var) : MVar :=
  if x ∈ q.body.locals then .tag n x else (assoc x q.params args).getD (.tag n x)

/-- Inlining invocations of the queries of `Δ`, resolved as `QProg.interp`
    does. -/
def QProg.build : QProg → Builder
  | []     => fun _ _ n cs => ⟨.empty, n, cs⟩
  | q :: Δ => fun Q args n cs =>
      if Q = q.name then
        if args.length = q.params.length then
          QBody.build (QProg.build Δ) (q.ren args n) q.body (n + 1) cs
        else ⟨.empty, n, cs⟩
      else QProg.build Δ Q args n cs

/-- The query model of `q`, whose invocations are resolved in `Δ`. -/
def Query.toQModel (Δ : QProg) (q : Query) : QModel :=
  let r := QBody.build (QProg.build Δ) .src q.body 0 []
  { params := q.params, main := r.comp, comps := r.comps, depth := Δ.length + 1 }

/-! ## Edges of the constructions -/

section edges

theorem mem_epsEdges {es : List QEdge} {s s' : QSt} :
    (s, s') ∈ epsEdges es ↔ (s, .eps, s') ∈ es := by
  simp only [epsEdges, List.mem_filterMap]
  constructor
  · rintro ⟨⟨a, l, b⟩, he, h⟩
    cases l with
    | eps => simp at h; obtain ⟨rfl, rfl⟩ := h; exact he
    | act => simp at h
  · intro h; exact ⟨_, h, rfl⟩

theorem mem_actEdges {es : List QEdge} {s s' : QSt} {as : List (QAct MVar)} :
    (s, as, s') ∈ actEdges es ↔ (s, .act as, s') ∈ es := by
  simp only [actEdges, List.mem_filterMap]
  constructor
  · rintro ⟨⟨a, l, b⟩, he, h⟩
    cases l with
    | eps => simp at h
    | act => simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact he
  · intro h; exact ⟨_, h, rfl⟩

theorem mem_lift {es : List QEdge} {w : QSt → QSt} {e : QEdge} :
    e ∈ es.map (QEdge.lift w) ↔ ∃ s l s', e = (w s, l, w s') ∧ (s, l, s') ∈ es := by
  simp only [List.mem_map, QEdge.lift]
  constructor
  · rintro ⟨⟨a, l, b⟩, he, rfl⟩; exact ⟨a, l, b, rfl, he⟩
  · rintro ⟨s, l, s', rfl, he⟩; exact ⟨_, he, rfl⟩

theorem alt_edge {A B : QComp} {s : QSt} {l : MLbl} {x : QSt} :
    (s, l, x) ∈ (QComp.alt A B).edges ↔
      (s = .altS ∧ l = .eps ∧ (x = .altL A.start ∨ x = .altR B.start)) ∨
      (∃ a a', s = .altL a ∧ x = .altL a' ∧ (a, l, a') ∈ A.edges) ∨
      (∃ b b', s = .altR b ∧ x = .altR b' ∧ (b, l, b') ∈ B.edges) := by
  simp only [QComp.alt, List.mem_cons, List.mem_append,
    mem_lift (w := .altL), mem_lift (w := .altR),
    Prod.mk.injEq]
  constructor
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨a, l', a', ⟨rfl, rfl, rfl⟩, h⟩ |
      ⟨b, l', b', ⟨rfl, rfl, rfl⟩, h⟩)
    · exact Or.inl ⟨rfl, rfl, Or.inl rfl⟩
    · exact Or.inl ⟨rfl, rfl, Or.inr rfl⟩
    · exact Or.inr (Or.inl ⟨a, a', rfl, rfl, h⟩)
    · exact Or.inr (Or.inr ⟨b, b', rfl, rfl, h⟩)
  · rintro (⟨rfl, rfl, rfl | rfl⟩ | ⟨a, a', rfl, rfl, h⟩ | ⟨b, b', rfl, rfl, h⟩)
    · exact Or.inl ⟨rfl, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨a, l, a', ⟨rfl, rfl, rfl⟩, h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨b, l, b', ⟨rfl, rfl, rfl⟩, h⟩))

theorem seq_edge {A B : QComp} {s : QSt} {l : MLbl} {x : QSt} :
    (s, l, x) ∈ (QComp.seq A B).edges ↔
      (∃ a a', s = .seqL a ∧ x = .seqL a' ∧ (a, l, a') ∈ A.edges) ∨
      (∃ f, f ∈ A.finals ∧ s = .seqL f ∧ l = .eps ∧ x = .seqR f B.start) ∨
      (∃ f b b', f ∈ A.finals ∧ s = .seqR f b ∧ x = .seqR f b' ∧ (b, l, b') ∈ B.edges) := by
  simp only [QComp.seq, List.mem_append, List.mem_flatMap, List.mem_cons,
    mem_lift (w := .seqL), Prod.mk.injEq]
  constructor
  · rintro (⟨a, l', a', ⟨rfl, rfl, rfl⟩, h⟩ | ⟨f, hf, ⟨rfl, rfl, rfl⟩ | h⟩)
    · exact Or.inl ⟨a, a', rfl, rfl, h⟩
    · exact Or.inr (Or.inl ⟨f, hf, rfl, rfl, rfl⟩)
    · rw [mem_lift (w := .seqR _)] at h
      obtain ⟨b, l', b', he, h⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact Or.inr (Or.inr ⟨f, b, b', hf, rfl, rfl, h⟩)
  · rintro (⟨a, a', rfl, rfl, h⟩ | ⟨f, hf, rfl, rfl, rfl⟩ | ⟨f, b, b', hf, rfl, rfl, h⟩)
    · exact Or.inl ⟨a, l, a', ⟨rfl, rfl, rfl⟩, h⟩
    · exact Or.inr ⟨f, hf, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · refine Or.inr ⟨f, hf, Or.inr ?_⟩
      rw [mem_lift (w := .seqR _)]
      exact ⟨b, l, b', rfl, h⟩

theorem both_edge {A B : QComp} {s : QSt} {l : MLbl} {x : QSt} :
    (s, l, x) ∈ (QComp.both A B).edges ↔
      (∃ a a' b, s = .both a b ∧ l = .eps ∧ x = .both a' b ∧
        (a, .eps, a') ∈ A.edges ∧ b ∈ B.states) ∨
      (∃ a b b', s = .both a b ∧ l = .eps ∧ x = .both a b' ∧
        (b, .eps, b') ∈ B.edges ∧ a ∈ A.states) ∨
      (∃ a a' b b' as bs, s = .both a b ∧ l = .act (as ++ bs) ∧ x = .both a' b' ∧
        (a, .act as, a') ∈ A.edges ∧ (b, .act bs, b') ∈ B.edges) := by
  simp only [QComp.both, List.mem_append, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ((⟨⟨a, a'⟩, he, b, hb, rfl, rfl, rfl⟩ | ⟨⟨b, b'⟩, he, a, ha, rfl, rfl, rfl⟩) |
      ⟨⟨a, as, a'⟩, he, ⟨b, bs, b'⟩, he', rfl, rfl, rfl⟩)
    · exact Or.inl ⟨a, a', b, rfl, rfl, rfl, mem_epsEdges.1 he, hb⟩
    · exact Or.inr (Or.inl ⟨a, b, b', rfl, rfl, rfl, mem_epsEdges.1 he, ha⟩)
    · exact Or.inr (Or.inr ⟨a, a', b, b', as, bs, rfl, rfl, rfl, mem_actEdges.1 he,
        mem_actEdges.1 he'⟩)
  · rintro (⟨a, a', b, rfl, rfl, rfl, he, hb⟩ | ⟨a, b, b', rfl, rfl, rfl, he, ha⟩ |
      ⟨a, a', b, b', as, bs, rfl, rfl, rfl, he, he'⟩)
    · exact Or.inl (Or.inl ⟨(a, a'), mem_epsEdges.2 he, b, hb, rfl, rfl, rfl⟩)
    · exact Or.inl (Or.inr ⟨(b, b'), mem_epsEdges.2 he, a, ha, rfl, rfl, rfl⟩)
    · exact Or.inr ⟨(a, as, a'), mem_actEdges.2 he, (b, bs, b'), mem_actEdges.2 he',
        rfl, rfl, rfl⟩

end edges


/-! ## Runs and acceptance of the constructions -/

section runs

variable {t : List Act} {δ : Obs} {X : Nat → MEnv → Prop} {ξ : MEnv}

theorem Run.lift {es es' : List QEdge} {w : QSt → QSt}
    (h : ∀ s l s', (s, l, s') ∈ es → (w s, l, w s') ∈ es') {s s' i j}
    (hr : Run es t ξ s i s' j) : Run es' t ξ (w s) i (w s') j := by
  induction hr with
  | refl => exact .refl
  | eps he _ ih => exact .eps (h _ _ _ he) ih
  | act he hi hb _ ih => exact .act (h _ _ _ he) hi hb ih

/-- The labels of a final state made of two final states. -/
theorem QComp.ok_append {c A B : QComp} {f a b : QSt}
    (hi : c.inv f = A.inv a ++ B.inv b) (he : c.exc f = A.exc a ++ B.exc b) :
    c.Ok δ X ξ f ↔ A.Ok δ X ξ a ∧ B.Ok δ X ξ b := by
  simp only [QComp.Ok, hi, he, List.mem_append]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨fun I h => h₁ I (Or.inl h), fun k h => h₂ k (Or.inl h)⟩,
      ⟨fun I h => h₁ I (Or.inr h), fun k h => h₂ k (Or.inr h)⟩⟩
  · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    exact ⟨fun I h => h.elim (h₁ I) (h₃ I), fun k h => h.elim (h₂ k) (h₄ k)⟩

/-- Acceptance by an automaton without labels is reachability of a final state. -/
theorem QComp.acc_plain {c : QComp} (hi : ∀ s, c.inv s = []) (hs : ∀ s, c.scope s = [])
    (he : ∀ s, c.exc s = []) {i j : Nat} :
    c.Acc t δ X ξ i j ↔ ∃ f ∈ c.finals, Run c.edges t ξ c.start i f j := by
  constructor
  · rintro ⟨f, hf, ξ', hξ', hr, _⟩
    have : ξ' = ξ := funext fun v => hξ' v (by simp [hs])
    subst this; exact ⟨f, hf, hr⟩
  · rintro ⟨f, hf, hr⟩
    exact ⟨f, hf, ξ, fun _ _ => rfl, hr, by simp [QComp.Ok, hi, he]⟩

theorem acc_empty {i j : Nat} : QComp.empty.Acc t δ X ξ i j ↔ False := by
  rw [QComp.acc_plain (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)]
  simp [QComp.empty]

theorem acc_eps {i j : Nat} (hj : j ≤ t.length) : QComp.eps.Acc t δ X ξ i j ↔ i ≤ j := by
  rw [QComp.acc_plain (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)]
  simp only [QComp.eps, QComp.empty, List.mem_singleton, exists_eq_left]
  exact ⟨Run.le, fun h => Run.loop (by simp) h hj⟩

theorem run_act {a : QAct MVar} {i j : Nat} (hj : j ≤ t.length) :
    Run (QComp.act a).edges t ξ .s0 i .s1 j ↔ ∃ p, i ≤ p ∧ p < j ∧ t[p]? = some (a.inst ξ) := by
  constructor
  · have key : ∀ s x i j, Run (QComp.act a).edges t ξ s i x j → x = .s1 → s = .s0 →
        ∃ p, i ≤ p ∧ p < j ∧ t[p]? = some (a.inst ξ) := by
      intro s x i j h
      induction h with
      | refl => intro hx hs; rw [hx] at hs; cases hs
      | eps he => simp [QComp.act] at he
      | act he hi hb hr ih =>
        intro hx hs
        subst hs
        simp [QComp.act] at he
        rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · obtain ⟨p, h₁, h₂, h₃⟩ := ih hx rfl
          exact ⟨p, by omega, h₂, h₃⟩
        · exact ⟨_, Nat.le_refl _, by have := hr.le; omega, hb a (by simp)⟩
    exact fun h => key _ _ _ _ h rfl rfl
  · rintro ⟨p, hip, hpj, hp⟩
    exact (Run.loop (by simp [QComp.act]) hip (by omega)).trans
      (.act (as := [a]) (by simp [QComp.act]) (by omega) (by simpa using hp)
        (Run.loop (by simp [QComp.act]) hpj hj))

theorem acc_act {a : QAct MVar} {i j : Nat} (hj : j ≤ t.length) :
    (QComp.act a).Acc t δ X ξ i j ↔ ∃ p, i ≤ p ∧ p < j ∧ t[p]? = some (a.inst ξ) := by
  rw [QComp.acc_plain (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)]
  simp only [QComp.act, List.mem_singleton, exists_eq_left]
  exact run_act hj

theorem acc_alt {A B : QComp} {i j : Nat} :
    (QComp.alt A B).Acc t δ X ξ i j ↔ A.Acc t δ X ξ i j ∨ B.Acc t δ X ξ i j := by
  have embL : ∀ {s x i j} {ξ : MEnv}, Run (QComp.alt A B).edges t ξ (.altL s) i x j ↔
      ∃ s', x = .altL s' ∧ Run A.edges t ξ s i s' j :=
    Run.embed (fun s l x => by
      rw [alt_edge]
      constructor
      · rintro (⟨h, _⟩ | ⟨a, a', h, rfl, he⟩ | ⟨b, b', h, _⟩)
        · cases h
        · cases h; exact ⟨a', rfl, he⟩
        · cases h
      · rintro ⟨s', rfl, he⟩; exact Or.inr (Or.inl ⟨s, s', rfl, rfl, he⟩))
  have embR : ∀ {s x i j} {ξ : MEnv}, Run (QComp.alt A B).edges t ξ (.altR s) i x j ↔
      ∃ s', x = .altR s' ∧ Run B.edges t ξ s i s' j :=
    Run.embed (fun s l x => by
      rw [alt_edge]
      constructor
      · rintro (⟨h, _⟩ | ⟨a, a', h, _⟩ | ⟨b, b', h, rfl, he⟩)
        · cases h
        · cases h
        · cases h; exact ⟨b', rfl, he⟩
      · rintro ⟨s', rfl, he⟩; exact Or.inr (Or.inr ⟨s, s', rfl, rfl, he⟩))
  -- A run from the start enters one of the two alternatives at once.
  have start : ∀ {x i j} {ξ : MEnv}, Run (QComp.alt A B).edges t ξ .altS i x j → x ≠ .altS →
      Run (QComp.alt A B).edges t ξ (.altL A.start) i x j ∨
      Run (QComp.alt A B).edges t ξ (.altR B.start) i x j := by
    intro x i j ξ h hx
    cases h with
    | refl => exact absurd rfl hx
    | eps he hr =>
      rcases alt_edge.1 he with ⟨_, _, rfl | rfl⟩ | ⟨a, _, h, _⟩ | ⟨b, _, h, _⟩
      · exact Or.inl hr
      · exact Or.inr hr
      · cases h
      · cases h
    | act he =>
      rcases alt_edge.1 he with ⟨_, h, _⟩ | ⟨a, _, h, _⟩ | ⟨b, _, h, _⟩ <;> cases h
  constructor
  · rintro ⟨f, hf, ξ', hξ', hr, hok⟩
    simp only [QComp.alt, List.mem_append, List.mem_map] at hf
    rcases hf with ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩
    · rcases start hr (by simp) with h | h
      · obtain ⟨_, he, h⟩ := embL.1 h
        cases he
        exact Or.inl ⟨f, hf, ξ', hξ', h, hok⟩
      · obtain ⟨_, he, _⟩ := embR.1 h; cases he
    · rcases start hr (by simp) with h | h
      · obtain ⟨_, he, _⟩ := embL.1 h; cases he
      · obtain ⟨_, he, h⟩ := embR.1 h
        cases he
        exact Or.inr ⟨f, hf, ξ', hξ', h, hok⟩
  · rintro (⟨f, hf, ξ', hξ', hr, hok⟩ | ⟨f, hf, ξ', hξ', hr, hok⟩)
    · exact ⟨.altL f, by simp [QComp.alt, hf], ξ', hξ',
        .eps (alt_edge.2 (Or.inl ⟨rfl, rfl, Or.inl rfl⟩)) (embL.2 ⟨f, rfl, hr⟩), hok⟩
    · exact ⟨.altR f, by simp [QComp.alt, hf], ξ', hξ',
        .eps (alt_edge.2 (Or.inl ⟨rfl, rfl, Or.inr rfl⟩)) (embR.2 ⟨f, rfl, hr⟩), hok⟩

theorem run_seq {A B : QComp} {s f g : QSt} {i j : Nat} :
    Run (QComp.seq A B).edges t ξ (.seqL s) i (.seqR f g) j ↔
      f ∈ A.finals ∧ ∃ m, Run A.edges t ξ s i f m ∧ Run B.edges t ξ B.start m g j := by
  have embR : ∀ {f}, f ∈ A.finals → ∀ {s x i j}, Run (QComp.seq A B).edges t ξ (.seqR f s) i x j ↔
      ∃ s', x = .seqR f s' ∧ Run B.edges t ξ s i s' j := by
    intro f hf
    exact Run.embed (fun s l x => by
      rw [seq_edge]
      constructor
      · rintro (⟨a, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨f', b, b', _, h, rfl, he⟩)
        · cases h
        · cases h
        · cases h; exact ⟨b', rfl, he⟩
      · rintro ⟨s', rfl, he⟩; exact Or.inr (Or.inr ⟨f, s, s', hf, rfl, rfl, he⟩))
  constructor
  · intro h
    generalize hs : QSt.seqL s = S at h
    generalize hx : QSt.seqR f g = x at h
    induction h generalizing s with
    | refl => subst hs; cases hx
    | eps he hr ih =>
      subst hs
      rcases seq_edge.1 he with ⟨a, a', h, rfl, he'⟩ | ⟨f', hf', h, _, rfl⟩ | ⟨_, _, _, _, h, _⟩
      · cases h
        obtain ⟨hf, m, h₁, h₂⟩ := ih rfl hx
        exact ⟨hf, m, .eps he' h₁, h₂⟩
      · cases h
        subst hx
        obtain ⟨_, he, h₂⟩ := (embR hf').1 hr
        cases he
        exact ⟨hf', _, .refl, h₂⟩
      · cases h
    | act he hi hb hr ih =>
      subst hs
      rcases seq_edge.1 he with ⟨a, a', h, rfl, he'⟩ | ⟨_, _, _, h, _⟩ | ⟨_, _, _, _, h, _⟩
      · cases h
        obtain ⟨hf, m, h₁, h₂⟩ := ih rfl hx
        exact ⟨hf, m, .act he' hi hb h₁, h₂⟩
      · cases h
      · cases h
  · rintro ⟨hf, m, h₁, h₂⟩
    have h₁' : Run (QComp.seq A B).edges t ξ (.seqL s) i (.seqL f) m :=
      Run.lift (fun a l a' he => seq_edge.2 (Or.inl ⟨a, a', rfl, rfl, he⟩)) h₁
    exact h₁'.trans (.eps (seq_edge.2 (Or.inr (Or.inl ⟨f, hf, rfl, rfl, rfl⟩)))
      ((embR hf).2 ⟨g, rfl, h₂⟩))

theorem acc_seq {A B : QComp} {i j : Nat} :
    (QComp.seq A B).Acc t δ X ξ i j ↔
      ∃ f ∈ A.finals, ∃ g ∈ B.finals, ∃ ξ' : MEnv,
        (∀ v, v ∉ A.scope f → v ∉ B.scope g → ξ' v = ξ v) ∧
        (∃ m, Run A.edges t ξ' A.start i f m ∧ Run B.edges t ξ' B.start m g j) ∧
        A.Ok δ X ξ' f ∧ B.Ok δ X ξ' g := by
  constructor
  · rintro ⟨x, hx, ξ', hξ', hr, hok⟩
    simp only [QComp.seq, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨f, hf, g, hg, rfl⟩ := hx
    obtain ⟨_, m, h₁, h₂⟩ := run_seq.1 hr
    exact ⟨f, hf, g, hg, ξ', fun v h₁ h₂ => hξ' v (by simp [QComp.seq, Lbl.seq, h₁, h₂]),
      ⟨m, h₁, h₂⟩, (QComp.ok_append rfl rfl).1 hok⟩
  · rintro ⟨f, hf, g, hg, ξ', hξ', ⟨m, h₁, h₂⟩, hok₁, hok₂⟩
    refine ⟨.seqR f g, ?_, ξ', fun v hv => ?_, run_seq.2 ⟨hf, m, h₁, h₂⟩,
      (QComp.ok_append rfl rfl).2 ⟨hok₁, hok₂⟩⟩
    · simp only [QComp.seq, List.mem_flatMap, List.mem_map]; exact ⟨f, hf, g, hg, rfl⟩
    · simp only [QComp.seq, Lbl.seq, List.mem_append, not_or] at hv
      exact hξ' v hv.1 hv.2

theorem run_both {A B : QComp} (hA : A.Closed) (hB : B.Closed) {a b a' b' : QSt} {i j : Nat}
    (ha : a ∈ A.states) (hb : b ∈ B.states) :
    Run (QComp.both A B).edges t ξ (.both a b) i (.both a' b') j ↔
      Run A.edges t ξ a i a' j ∧ Run B.edges t ξ b i b' j := by
  constructor
  · intro h
    generalize hs : QSt.both a b = S at h
    generalize hx : QSt.both a' b' = x at h
    induction h generalizing a b with
    | refl => subst hs; cases hx; exact ⟨.refl, .refl⟩
    | eps he hr ih =>
      subst hs
      rcases both_edge.1 he with ⟨a₀, a₁, b₀, h, _, rfl, he', hb'⟩ | ⟨a₀, b₀, b₁, h, _, rfl, he', ha'⟩ |
        ⟨_, _, _, _, _, _, _, h, _⟩
      · cases h
        obtain ⟨h₁, h₂⟩ := ih (hA.edges _ _ _ he').2 hb rfl hx
        exact ⟨.eps he' h₁, h₂⟩
      · cases h
        obtain ⟨h₁, h₂⟩ := ih ha (hB.edges _ _ _ he').2 rfl hx
        exact ⟨h₁, .eps he' h₂⟩
      · cases h
    | act he hi hb' hr ih =>
      subst hs
      rcases both_edge.1 he with ⟨_, _, _, _, h, _⟩ | ⟨_, _, _, _, h, _⟩ |
        ⟨a₀, a₁, b₀, b₁, as, bs, h, hl, rfl, he₁, he₂⟩
      · cases h
      · cases h
      · cases h
        cases hl
        obtain ⟨h₁, h₂⟩ := ih (hA.edges _ _ _ he₁).2 (hB.edges _ _ _ he₂).2 rfl hx
        exact ⟨.act he₁ hi (fun c hc => hb' c (List.mem_append_left _ hc)) h₁,
          .act he₂ hi (fun c hc => hb' c (List.mem_append_right _ hc)) h₂⟩
  · rintro ⟨h₁, h₂⟩
    -- `B` alone, over an empty stretch: only `ε`-steps.
    have onlyB : ∀ {a b b' i j}, a ∈ A.states → Run B.edges t ξ b i b' j → i = j →
        Run (QComp.both A B).edges t ξ (.both a b) i (.both a b') j := by
      intro a b b' i j ha h hij
      induction h with
      | refl => exact .refl
      | eps he _ ih => exact .eps (both_edge.2 (Or.inr (Or.inl ⟨_, _, _, rfl, rfl, rfl, he, ha⟩))) (ih hij)
      | act _ _ _ hr => have := hr.le; omega
    induction h₁ generalizing b with
    | refl => exact onlyB ha h₂ rfl
    | eps he _ ih =>
      exact .eps (both_edge.2 (Or.inl ⟨_, _, _, rfl, rfl, rfl, he, hb⟩))
        (ih (hA.edges _ _ _ he).2 hb h₂)
    | @act a₀ a₁ _ as i _ he hi hfire hr ih =>
      have hr' := hr
      clear hb
      induction h₂ with
      | refl => have := hr'.le; omega
      | eps he' _ ih' =>
        exact .eps (both_edge.2 (Or.inr (Or.inl ⟨_, _, _, rfl, rfl, rfl, he', ha⟩))) (by apply ih' <;> assumption)
      | act he' _ hfire' hr₂ _ =>
        exact .act (both_edge.2 (Or.inr (Or.inr ⟨_, _, _, _, as, _, rfl, rfl, rfl, he, he'⟩))) hi
          (fun c hc => (List.mem_append.1 hc).elim (hfire c) (hfire' c))
          (ih (hA.edges _ _ _ he).2 (hB.edges _ _ _ he').2 hr₂)

theorem acc_both {A B : QComp} (hA : A.Closed) (hB : B.Closed) {i j : Nat} :
    (QComp.both A B).Acc t δ X ξ i j ↔
      ∃ a ∈ A.finals, ∃ b ∈ B.finals, ∃ ξ' : MEnv,
        (∀ v, v ∉ A.scope a → v ∉ B.scope b → ξ' v = ξ v) ∧
        Run A.edges t ξ' A.start i a j ∧ Run B.edges t ξ' B.start i b j ∧
        A.Ok δ X ξ' a ∧ B.Ok δ X ξ' b := by
  constructor
  · rintro ⟨x, hx, ξ', hξ', hr, hok⟩
    simp only [QComp.both, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨h₁, h₂⟩ := (run_both hA hB hA.start hB.start).1 hr
    exact ⟨a, ha, b, hb, ξ', fun v h₁ h₂ => hξ' v (by simp [QComp.both, Lbl.both, h₁, h₂]),
      h₁, h₂, (QComp.ok_append rfl rfl).1 hok⟩
  · rintro ⟨a, ha, b, hb, ξ', hξ', h₁, h₂, hok₁, hok₂⟩
    refine ⟨.both a b, ?_, ξ', fun v hv => ?_, (run_both hA hB hA.start hB.start).2 ⟨h₁, h₂⟩,
      (QComp.ok_append rfl rfl).2 ⟨hok₁, hok₂⟩⟩
    · simp only [QComp.both, List.mem_flatMap, List.mem_map]; exact ⟨a, ha, b, hb, rfl⟩
    · simp only [QComp.both, Lbl.both, List.mem_append, not_or] at hv
      exact hξ' v hv.1 hv.2

end runs

/-! ## Bookkeeping invariants -/

section built

theorem Lbl.mem_alt {α} {fA fB : QSt → List α} {x : α} {s : QSt} (h : x ∈ Lbl.alt fA fB s) :
    (∃ s', x ∈ fA s') ∨ (∃ s', x ∈ fB s') := by
  cases s <;> simp [Lbl.alt] at h
  · exact Or.inl ⟨_, h⟩
  · exact Or.inr ⟨_, h⟩

theorem Lbl.mem_seq {α} {fA fB : QSt → List α} {x : α} {s : QSt} (h : x ∈ Lbl.seq fA fB s) :
    (∃ s', x ∈ fA s') ∨ (∃ s', x ∈ fB s') := by
  cases s <;> simp [Lbl.seq] at h
  · exact Or.inl ⟨_, h⟩
  · rcases h with h | h
    · exact Or.inl ⟨_, h⟩
    · exact Or.inr ⟨_, h⟩

theorem Lbl.mem_both {α} {fA fB : QSt → List α} {x : α} {s : QSt} (h : x ∈ Lbl.both fA fB s) :
    (∃ s', x ∈ fA s') ∨ (∃ s', x ∈ fB s') := by
  cases s <;> simp [Lbl.both] at h
  rcases h with h | h
  · exact Or.inl ⟨_, h⟩
  · exact Or.inr ⟨_, h⟩

theorem MVar.Below.mono {n n' : Nat} (h : n ≤ n') : ∀ {v : MVar}, v.Below n → v.Below n'
  | .src _, _ => trivial
  | .tag _ _, hv => by simp only [MVar.Below] at hv ⊢; omega

theorem MVar.InRange.not_below {n n' : Nat} : ∀ {v : MVar}, v.InRange n n' → ¬ v.Below n
  | .tag _ _, hv, hb => by simp only [MVar.InRange, MVar.Below] at hv hb; omega

theorem MVar.InRange.below {n n' : Nat} : ∀ {v : MVar}, v.InRange n n' → v.Below n'
  | .tag _ _, hv => by simp only [MVar.InRange, MVar.Below] at hv ⊢; omega

theorem MVar.InRange.mono {n n' m m' : Nat} (h₁ : m ≤ n) (h₂ : n' ≤ m') :
    ∀ {v : MVar}, v.InRange n n' → v.InRange m m'
  | .tag _ _, hv => by simp only [MVar.InRange] at hv ⊢; omega

theorem getElem?_of_prefix {cs cs' : List QComp} (h : cs <+: cs') {k : Nat} (hk : k < cs.length) :
    cs'[k]? = cs[k]? := by
  obtain ⟨u, rfl⟩ := h
  exact List.getElem?_append_left hk

/-- The bookkeeping invariants of a construction started with the fresh tag
    `n` and the components `cs`. -/
structure Built (n : Nat) (cs : List QComp) (r : BRes) : Prop where
  le     : n ≤ r.next
  pre    : cs <+: r.comps
  closed : r.comp.Closed
  /-- The scope consists of the tags minted by the construction. -/
  scope  : ∀ s, ∀ v ∈ r.comp.scope s, v.InRange n r.next
  /-- Nothing minted later is read. -/
  reads  : r.comp.ReadsIn r.comps (MVar.Below r.next)
  mono   : r.comp.Mono
  comps  : (∀ c ∈ cs, c.Closed ∧ c.Mono) → ∀ c ∈ r.comps, c.Closed ∧ c.Mono

/-- A construction without labels or components. -/
theorem Built.plain {n : Nat} {cs : List QComp} {c : QComp} (hc : c.Closed)
    (hi : ∀ s, c.inv s = []) (hs : ∀ s, c.scope s = []) (he : ∀ s, c.exc s = [])
    (hl : ∀ s l s', (s, l, s') ∈ c.edges → ∀ v ∈ l.vars, v.Below n) :
    Built n cs ⟨c, n, cs⟩ where
  le := Nat.le_refl _
  pre := List.prefix_refl _
  closed := hc
  scope := by intro s v hv; simp [hs] at hv
  reads := .mk hl (by simp [hi]) (by simp [hs]) (by simp [he]) (by simp [he])
  mono := by intro s l s' _; simp [hi, hs]
  comps := id

/-- Combining two consecutive constructions into one, whose labels come from
    theirs. -/
theorem Built.combine {n : Nat} {cs : List QComp} {r₁ r₂ : BRes} (h₁ : Built n cs r₁)
    (h₂ : Built r₁.next r₁.comps r₂) {C : QComp} (hC : C.Closed) (hM : C.Mono)
    (hE : ∀ s l s', (s, l, s') ∈ C.edges → ∀ v ∈ l.vars,
      (∃ s l s', (s, l, s') ∈ r₁.comp.edges ∧ v ∈ l.vars) ∨
      (∃ s l s', (s, l, s') ∈ r₂.comp.edges ∧ v ∈ l.vars))
    (hI : ∀ s, ∀ I ∈ C.inv s, (∃ s', I ∈ r₁.comp.inv s') ∨ (∃ s', I ∈ r₂.comp.inv s'))
    (hS : ∀ s, ∀ v ∈ C.scope s, (∃ s', v ∈ r₁.comp.scope s') ∨ (∃ s', v ∈ r₂.comp.scope s'))
    (hX : ∀ s, ∀ k ∈ C.exc s, (∃ s', k ∈ r₁.comp.exc s') ∨ (∃ s', k ∈ r₂.comp.exc s')) :
    Built n cs ⟨C, r₂.next, r₂.comps⟩ := by
  have hle := h₂.le
  have hpre := h₂.pre
  have hR₁ := (h₁.reads.extend hpre).weaken (fun _ hv => MVar.Below.mono hle hv)
  have hR₂ := h₂.reads
  refine ⟨Nat.le_trans h₁.le hle, h₁.pre.trans hpre, hC, ?_, ?_, hM,
    fun h c hc => h₂.comps (h₁.comps h) c hc⟩
  · intro s v hv
    rcases hS s v hv with ⟨s', h⟩ | ⟨s', h⟩
    · exact (h₁.scope s' v h).mono (Nat.le_refl _) hle
    · exact (h₂.scope s' v h).mono h₁.le (Nat.le_refl _)
  · refine .mk ?_ ?_ ?_ ?_ ?_
    · intro s l s' he v hv
      rcases hE s l s' he v hv with ⟨a, l', a', he', hv'⟩ | ⟨a, l', a', he', hv'⟩
      · exact hR₁.edges a l' a' he' v hv'
      · exact hR₂.edges a l' a' he' v hv'
    · intro s I hI' v hv
      rcases hI s I hI' with ⟨s', h⟩ | ⟨s', h⟩
      · exact hR₁.inv s' I h v hv
      · exact hR₂.inv s' I h v hv
    · intro s v hv
      rcases hS s v hv with ⟨s', h⟩ | ⟨s', h⟩
      · exact hR₁.scope s' v h
      · exact hR₂.scope s' v h
    · intro s k hk
      rcases hX s k hk with ⟨s', h⟩ | ⟨s', h⟩
      · exact hR₁.excLt s' k h
      · exact hR₂.excLt s' k h
    · intro s k hk c' hc'
      rcases hX s k hk with ⟨s', h⟩ | ⟨s', h⟩
      · exact hR₁.exc s' k h c' hc'
      · exact hR₂.exc s' k h c' hc'

theorem List.subset_append_both {α} {l₁ l₁' l₂ l₂' : List α} (h₁ : l₁ ⊆ l₁') (h₂ : l₂ ⊆ l₂') :
    l₁ ++ l₂ ⊆ l₁' ++ l₂' := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact List.mem_append_left _ (h₁ h)
  · exact List.mem_append_right _ (h₂ h)

section shapes

variable {A B : QComp}

theorem closed_empty : QComp.empty.Closed :=
  ⟨by simp [QComp.empty], by rintro s l s' h; simp [QComp.empty] at h; simp [QComp.empty, h],
    by simp [QComp.empty]⟩

theorem closed_eps : QComp.eps.Closed :=
  ⟨by simp [QComp.eps, QComp.empty],
    by rintro s l s' h; simp [QComp.eps, QComp.empty] at h; simp [QComp.eps, QComp.empty, h],
    by simp [QComp.eps, QComp.empty]⟩

theorem closed_act {a : QAct MVar} : (QComp.act a).Closed :=
  ⟨by simp [QComp.act],
    by rintro s l s' h; simp [QComp.act] at h; rcases h with h | h | h <;> simp [QComp.act, h],
    by simp [QComp.act]⟩

theorem closed_alt (hA : A.Closed) (hB : B.Closed) : (QComp.alt A B).Closed := by
  refine ⟨by simp [QComp.alt], fun s l s' he => ?_, fun f hf => ?_⟩
  · rcases alt_edge.1 he with ⟨rfl, rfl, rfl | rfl⟩ | ⟨a, a', rfl, rfl, h⟩ | ⟨b, b', rfl, rfl, h⟩
    · simp [QComp.alt, hA.start]
    · simp [QComp.alt, hB.start]
    · simp [QComp.alt, (hA.edges _ _ _ h).1, (hA.edges _ _ _ h).2]
    · simp [QComp.alt, (hB.edges _ _ _ h).1, (hB.edges _ _ _ h).2]
  · simp only [QComp.alt, List.mem_append, List.mem_map] at hf
    rcases hf with ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩
    · simp [QComp.alt, hA.finals f hf]
    · simp [QComp.alt, hB.finals f hf]

theorem closed_seq (hA : A.Closed) (hB : B.Closed) : (QComp.seq A B).Closed := by
  refine ⟨by simp [QComp.seq, hA.start], fun s l s' he => ?_, fun f hf => ?_⟩
  · rcases seq_edge.1 he with ⟨a, a', rfl, rfl, h⟩ | ⟨f, hf, rfl, rfl, rfl⟩ |
      ⟨f, b, b', hf, rfl, rfl, h⟩
    · simp [QComp.seq, (hA.edges _ _ _ h).1, (hA.edges _ _ _ h).2]
    · simp only [QComp.seq, List.mem_append, List.mem_map, List.mem_flatMap]
      exact ⟨Or.inl ⟨f, hA.finals f hf, rfl⟩, Or.inr ⟨f, hf, B.start, hB.start, rfl⟩⟩
    · simp only [QComp.seq, List.mem_append, List.mem_map, List.mem_flatMap]
      exact ⟨Or.inr ⟨f, hf, b, (hB.edges _ _ _ h).1, rfl⟩,
        Or.inr ⟨f, hf, b', (hB.edges _ _ _ h).2, rfl⟩⟩
  · simp only [QComp.seq, List.mem_append, List.mem_map, List.mem_flatMap] at hf ⊢
    obtain ⟨f, hf, g, hg, rfl⟩ := hf
    exact Or.inr ⟨f, hf, g, hB.finals g hg, rfl⟩

theorem closed_both (hA : A.Closed) (hB : B.Closed) : (QComp.both A B).Closed := by
  refine ⟨by simp [QComp.both, hA.start, hB.start], fun s l s' he => ?_, fun f hf => ?_⟩
  · simp only [QComp.both, List.mem_flatMap, List.mem_map]
    rcases both_edge.1 he with ⟨a, a', b, rfl, rfl, rfl, h, hb⟩ | ⟨a, b, b', rfl, rfl, rfl, h, ha⟩ |
      ⟨a, a', b, b', as, bs, rfl, rfl, rfl, h, h'⟩
    · exact ⟨⟨a, (hA.edges _ _ _ h).1, b, hb, rfl⟩, ⟨a', (hA.edges _ _ _ h).2, b, hb, rfl⟩⟩
    · exact ⟨⟨a, ha, b, (hB.edges _ _ _ h).1, rfl⟩, ⟨a, ha, b', (hB.edges _ _ _ h).2, rfl⟩⟩
    · exact ⟨⟨a, (hA.edges _ _ _ h).1, b, (hB.edges _ _ _ h').1, rfl⟩,
        ⟨a', (hA.edges _ _ _ h).2, b', (hB.edges _ _ _ h').2, rfl⟩⟩
  · simp only [QComp.both, List.mem_flatMap, List.mem_map] at hf ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := hf
    exact ⟨a, hA.finals a ha, b, hB.finals b hb, rfl⟩

theorem mono_alt (hA : A.Mono) (hB : B.Mono) : (QComp.alt A B).Mono := by
  intro s l s' he
  rcases alt_edge.1 he with ⟨rfl, rfl, _⟩ | ⟨a, a', rfl, rfl, h⟩ | ⟨b, b', rfl, rfl, h⟩
  · simp [QComp.alt, Lbl.alt]
  · exact hA _ _ _ h
  · exact hB _ _ _ h

theorem mono_seq (hA : A.Mono) (hB : B.Mono) : (QComp.seq A B).Mono := by
  intro s l s' he
  rcases seq_edge.1 he with ⟨a, a', rfl, rfl, h⟩ | ⟨f, _, rfl, rfl, rfl⟩ | ⟨f, b, b', _, rfl, rfl, h⟩
  · exact hA _ _ _ h
  · exact ⟨List.subset_append_left _ _, List.subset_append_left _ _⟩
  · exact ⟨List.subset_append_both (List.Subset.refl _) (hB _ _ _ h).1,
      List.subset_append_both (List.Subset.refl _) (hB _ _ _ h).2⟩

theorem mono_both (hA : A.Mono) (hB : B.Mono) : (QComp.both A B).Mono := by
  intro s l s' he
  rcases both_edge.1 he with ⟨a, a', b, rfl, rfl, rfl, h, _⟩ | ⟨a, b, b', rfl, rfl, rfl, h, _⟩ |
    ⟨a, a', b, b', as, bs, rfl, rfl, rfl, h, h'⟩
  · exact ⟨List.subset_append_both (hA _ _ _ h).1 (List.Subset.refl _),
      List.subset_append_both (hA _ _ _ h).2 (List.Subset.refl _)⟩
  · exact ⟨List.subset_append_both (List.Subset.refl _) (hB _ _ _ h).1,
      List.subset_append_both (List.Subset.refl _) (hB _ _ _ h).2⟩
  · exact ⟨List.subset_append_both (hA _ _ _ h).1 (hB _ _ _ h').1,
      List.subset_append_both (hA _ _ _ h).2 (hB _ _ _ h').2⟩

theorem vars_alt {s l s'} (he : (s, l, s') ∈ (QComp.alt A B).edges) {v : MVar} (hv : v ∈ l.vars) :
    (∃ s l s', (s, l, s') ∈ A.edges ∧ v ∈ l.vars) ∨ (∃ s l s', (s, l, s') ∈ B.edges ∧ v ∈ l.vars) := by
  rcases alt_edge.1 he with ⟨_, rfl, _⟩ | ⟨a, a', _, _, h⟩ | ⟨b, b', _, _, h⟩
  · simp [MLbl.vars] at hv
  · exact Or.inl ⟨_, _, _, h, hv⟩
  · exact Or.inr ⟨_, _, _, h, hv⟩

theorem vars_seq {s l s'} (he : (s, l, s') ∈ (QComp.seq A B).edges) {v : MVar} (hv : v ∈ l.vars) :
    (∃ s l s', (s, l, s') ∈ A.edges ∧ v ∈ l.vars) ∨ (∃ s l s', (s, l, s') ∈ B.edges ∧ v ∈ l.vars) := by
  rcases seq_edge.1 he with ⟨a, a', _, _, h⟩ | ⟨_, _, _, rfl, _⟩ | ⟨_, b, b', _, _, _, h⟩
  · exact Or.inl ⟨_, _, _, h, hv⟩
  · simp [MLbl.vars] at hv
  · exact Or.inr ⟨_, _, _, h, hv⟩

theorem vars_both {s l s'} (he : (s, l, s') ∈ (QComp.both A B).edges) {v : MVar} (hv : v ∈ l.vars) :
    (∃ s l s', (s, l, s') ∈ A.edges ∧ v ∈ l.vars) ∨ (∃ s l s', (s, l, s') ∈ B.edges ∧ v ∈ l.vars) := by
  rcases both_edge.1 he with ⟨_, _, _, _, rfl, _⟩ | ⟨_, _, _, _, rfl, _⟩ |
    ⟨a, a', b, b', as, bs, _, rfl, _, h, h'⟩
  · simp [MLbl.vars] at hv
  · simp [MLbl.vars] at hv
  · simp only [MLbl.vars, List.flatMap_append, List.mem_append] at hv
    rcases hv with hv | hv
    · exact Or.inl ⟨_, _, _, h, by simpa [MLbl.vars] using hv⟩
    · exact Or.inr ⟨_, _, _, h', by simpa [MLbl.vars] using hv⟩

end shapes

end built


/-! ## Correctness of patterns -/

section correct

variable {t : List Act} {δ : Obs}

/-- Acceptance of `t[i..j)` by the constructed automaton agrees with `R`
    holding from `i` to some `j' ≤ j`, whatever the components it is
    eventually placed among, for fuel at least `d`. -/
def Correct (t : List Act) (δ : Obs) (d : Nat) (r : BRes) (R : MEnv → Nat → Nat → Prop) : Prop :=
  ∀ M : List QComp, r.comps <+: M → ∀ fuel, d ≤ fuel → ∀ (ξ : MEnv) (i j : Nat), j ≤ t.length →
    (r.comp.Acc t δ (compSat M t δ fuel) ξ i j ↔ ∃ j', j' ≤ j ∧ R ξ i j')

/-- Every pattern construction is `Built` and `Correct`. -/
def PatOK (t : List Act) (δ : Obs) (Ψ : Builder) (Θ : Interp) (d : Nat) : Prop :=
  ∀ (ρ : Var → MVar) (F : Pat) (n : Nat) (cs : List QComp), (∀ x, (ρ x).Below n) →
    Built n cs (F.build Ψ ρ n cs) ∧
    Correct t δ d (F.build Ψ ρ n cs) (fun ξ i j => Θ ⬝ t ⬝ δ ⬝ (ξ ∘ ρ) ⊨ F : i ⇝ j)

/-- Every invocation construction is `Built` and `Correct`. -/
def BuilderOK (t : List Act) (δ : Obs) (Ψ : Builder) (Θ : Interp) (d : Nat) : Prop :=
  ∀ (Q : QName) (args : List MVar) (n : Nat) (cs : List QComp), (∀ v ∈ args, v.Below n) →
    Built n cs (Ψ Q args n cs) ∧
    Correct t δ d (Ψ Q args n cs) (fun ξ i j => Θ Q (args.map ξ) i j)

/-- New values for tags minted from `n` do not change what `ρ`, all of whose
    variables are below `n`, denotes. -/
theorem comp_eq_of_scope {ρ : Var → MVar} {n : Nat} (hρ : ∀ x, (ρ x).Below n)
    {S : MVar → Prop} (hS : ∀ v, S v → ¬ v.Below n) {ξ ξ' : MEnv}
    (h : ∀ v, ¬ S v → ξ' v = ξ v) : ξ' ∘ ρ = ξ ∘ ρ :=
  funext fun x => h (ρ x) (fun hs => hS _ hs (hρ x))

/-- Satisfaction of components reads `V` if the components do. -/
theorem compSat_reads {M : List QComp} {V : MVar → Prop} (fuel : Nat) :
    ∀ k c', M[k]? = some c' → QComp.ReadsIn M V c' →
      ∀ ξ₁ ξ₂ : MEnv, (∀ v, V v → ξ₁ v = ξ₂ v) →
        (compSat M t δ fuel k ξ₁ ↔ compSat M t δ fuel k ξ₂) :=
  fun k c' hc hr ξ₁ ξ₂ h => compSat_coincide fuel k c' hc hr ξ₁ ξ₂ h

/-- A run and the labels of its final state survive changing the
    substitution outside what the automaton reads. -/
theorem run_ok_coincide {A : QComp} {M : List QComp} {V : MVar → Prop} {fuel : Nat}
    (hR : A.ReadsIn M V) {ξa ξb : MEnv} (h : ∀ v, V v → ξa v = ξb v) {f : QSt} {i m : Nat}
    (hr : Run A.edges t ξa A.start i f m) (hok : A.Ok δ (compSat M t δ fuel) ξa f) :
    Run A.edges t ξb A.start i f m ∧ A.Ok δ (compSat M t δ fuel) ξb f :=
  ⟨hr.coincide hR.edges h, (QComp.ok_coincide (compSat_reads fuel) hR h f).1 hok⟩

/-- Two consecutive constructions: the second one's new values do not
    disturb the first one. -/
theorem combine_acc {n : Nat} {cs : List QComp} {r₁ r₂ : BRes} {ρ : Var → MVar}
    (hρ : ∀ x, (ρ x).Below n) (h₁ : Built n cs r₁) (h₂ : Built r₁.next r₁.comps r₂)
    {M : List QComp} (hM : r₂.comps <+: M) {fuel : Nat} {ξ ξa ξb : MEnv} {f g : QSt}
    (hξa : ∀ v, v ∉ r₁.comp.scope f → ξa v = ξ v) (hξb : ∀ v, v ∉ r₂.comp.scope g → ξb v = ξa v)
    {i m : Nat} (hr : Run r₁.comp.edges t ξa r₁.comp.start i f m)
    (hok : r₁.comp.Ok δ (compSat M t δ fuel) ξa f) :
    (∀ v, v ∉ r₁.comp.scope f → v ∉ r₂.comp.scope g → ξb v = ξ v) ∧
    Run r₁.comp.edges t ξb r₁.comp.start i f m ∧ r₁.comp.Ok δ (compSat M t δ fuel) ξb f ∧
    ξa ∘ ρ = ξ ∘ ρ := by
  have hagree : ∀ v, v.Below r₁.next → ξa v = ξb v :=
    fun v hv => (hξb v (fun hs => (h₂.scope g v hs).not_below hv)).symm
  obtain ⟨hr', hok'⟩ := run_ok_coincide ((h₁.reads.extend (h₂.pre.trans hM))) hagree hr hok
  exact ⟨fun v h₁ h₂ => by rw [hξb v h₂, hξa v h₁], hr', hok',
    comp_eq_of_scope hρ (S := fun v => v ∈ r₁.comp.scope f)
      (fun v hv => (h₁.scope f v hv).not_below) hξa⟩

theorem patOK {Ψ : Builder} {Θ : Interp} {d : Nat} (hΨ : BuilderOK t δ Ψ Θ d)
    (hΘ : Θ.Ok t) (hΘl : Θ.LowerStart) : PatOK t δ Ψ Θ d := by
  intro ρ F
  induction F with
  | eps =>
    intro n cs _
    refine ⟨Built.plain closed_eps (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (by intro s l s' h; simp [QComp.eps, QComp.empty] at h; simp [h.2.1, MLbl.vars]), ?_⟩
    intro M _ fuel _ ξ i j hj
    show QComp.eps.Acc t δ _ ξ i j ↔ _
    rw [acc_eps hj]
    simp only [Pat.sat_eps]
    exact ⟨fun h => ⟨i, h, rfl⟩, fun ⟨j', h, he⟩ => he ▸ h⟩
  | act a =>
    intro n cs hρ
    refine ⟨Built.plain closed_act (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_, ?_⟩
    · intro s l s' h v hv
      simp [QComp.act] at h
      rcases h with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;>
        simp [MLbl.vars, QAct.vars_map] at hv
      obtain ⟨x, _, rfl⟩ := hv
      exact hρ x
    · intro M _ fuel _ ξ i j hj
      show (QComp.act (a.map ρ)).Acc t δ _ ξ i j ↔ _
      rw [acc_act hj, QAct.inst_map]
      simp only [Pat.sat_act]
      constructor
      · rintro ⟨p, hip, hpj, hp⟩
        exact ⟨p + 1, by omega, by omega, by omega, by simpa using hp⟩
      · rintro ⟨j', hj', hij, hjl, hp⟩
        exact ⟨j' - 1, by omega, by omega, hp⟩
  | query Q zs =>
    intro n cs hρ
    obtain ⟨hB, hC⟩ := hΨ Q (zs.map ρ) n cs (by simp only [List.mem_map]; rintro _ ⟨x, _, rfl⟩; exact hρ x)
    refine ⟨hB, fun M hM fuel hf ξ i j hj => ?_⟩
    rw [show (Pat.query Q zs).build Ψ ρ n cs = Ψ Q (zs.map ρ) n cs from rfl, hC M hM fuel hf ξ i j hj]
    simp only [Pat.sat_query, List.map_map]
  | seq F G ihF ihG =>
    intro n cs hρ
    obtain ⟨hB₁, hC₁⟩ := ihF n cs hρ
    obtain ⟨hB₂, hC₂⟩ := ihG (F.build Ψ ρ n cs).next (F.build Ψ ρ n cs).comps
      (fun x => (hρ x).mono hB₁.le)
    refine ⟨Built.combine hB₁ hB₂ (closed_seq hB₁.closed hB₂.closed) (mono_seq hB₁.mono hB₂.mono)
      (fun _ _ _ he _ hv => vars_seq he hv) (fun _ _ h => Lbl.mem_seq h)
      (fun _ _ h => Lbl.mem_seq h) (fun _ _ h => Lbl.mem_seq h), ?_⟩
    intro M hM fuel hf ξ i j hj
    show (QComp.seq _ _).Acc t δ _ ξ i j ↔ _
    have hM₁ := hB₂.pre.trans hM
    rw [acc_seq]
    constructor
    · rintro ⟨f, hf₁, g, hg, ξ', hξ', ⟨m, h₁, h₂⟩, hok₁, hok₂⟩
      have heq : ξ' ∘ ρ = ξ ∘ ρ := comp_eq_of_scope hρ
        (S := fun v => v ∈ (F.build Ψ ρ n cs).comp.scope f ∨ v ∈ (G.build Ψ ρ _ _).comp.scope g)
        (fun v hv => hv.elim (fun h => (hB₁.scope f v h).not_below)
          (fun h hb => (hB₂.scope g v h).not_below (hb.mono hB₁.le)))
        (fun v hv => hξ' v (fun h => hv (Or.inl h)) (fun h => hv (Or.inr h)))
      have hm : m ≤ j := h₂.le
      obtain ⟨m', hm', hF⟩ := (hC₁ M hM₁ fuel hf ξ' i m (by omega)).1
        ⟨f, hf₁, ξ', fun _ _ => rfl, h₁, hok₁⟩
      obtain ⟨j', hj', hG⟩ := (hC₂ M hM fuel hf ξ' m j hj).1 ⟨g, hg, ξ', fun _ _ => rfl, h₂, hok₂⟩
      obtain ⟨j'', hj'', hG'⟩ := hG.lower_start hΘl m' hm'
      rw [heq] at hF hG'
      exact ⟨j'', by omega, .seq hF hG'⟩
    · rintro ⟨j', hj', hS⟩
      obtain ⟨m, hF, hG⟩ := Pat.sat_seq.1 hS
      have hmj : m ≤ j' := hG.le hΘ
      obtain ⟨f, hf₁, ξa, hξa, h₁, hok₁⟩ := (hC₁ M hM₁ fuel hf ξ i m (by omega)).2
        ⟨m, Nat.le_refl _, hF⟩
      have heqa : ξa ∘ ρ = ξ ∘ ρ := comp_eq_of_scope hρ (S := fun v => v ∈ _ )
        (fun v hv => (hB₁.scope f v hv).not_below) hξa
      obtain ⟨g, hg, ξb, hξb, h₂, hok₂⟩ := (hC₂ M hM fuel hf ξa m j hj).2
        ⟨j', hj', by show Pat.Sat _ _ _ _ _ _ _; rw [heqa]; exact hG⟩
      obtain ⟨hξ', h₁', hok₁', _⟩ := combine_acc hρ hB₁ hB₂ hM hξa hξb h₁ hok₁
      exact ⟨f, hf₁, g, hg, ξb, hξ', ⟨m, h₁', h₂⟩, hok₁', hok₂⟩
  | alt F G ihF ihG =>
    intro n cs hρ
    obtain ⟨hB₁, hC₁⟩ := ihF n cs hρ
    obtain ⟨hB₂, hC₂⟩ := ihG (F.build Ψ ρ n cs).next (F.build Ψ ρ n cs).comps
      (fun x => (hρ x).mono hB₁.le)
    refine ⟨Built.combine hB₁ hB₂ (closed_alt hB₁.closed hB₂.closed) (mono_alt hB₁.mono hB₂.mono)
      (fun _ _ _ he _ hv => vars_alt he hv) (fun _ _ h => Lbl.mem_alt h)
      (fun _ _ h => Lbl.mem_alt h) (fun _ _ h => Lbl.mem_alt h), ?_⟩
    intro M hM fuel hf ξ i j hj
    show (QComp.alt _ _).Acc t δ _ ξ i j ↔ _
    rw [acc_alt, hC₁ M (hB₂.pre.trans hM) fuel hf ξ i j hj, hC₂ M hM fuel hf ξ i j hj]
    simp only [Pat.sat_alt]
    constructor
    · rintro (⟨j', h, h'⟩ | ⟨j', h, h'⟩)
      · exact ⟨j', h, Or.inl h'⟩
      · exact ⟨j', h, Or.inr h'⟩
    · rintro ⟨j', h, h' | h'⟩
      · exact Or.inl ⟨j', h, h'⟩
      · exact Or.inr ⟨j', h, h'⟩
  | both F G ihF ihG =>
    intro n cs hρ
    obtain ⟨hB₁, hC₁⟩ := ihF n cs hρ
    obtain ⟨hB₂, hC₂⟩ := ihG (F.build Ψ ρ n cs).next (F.build Ψ ρ n cs).comps
      (fun x => (hρ x).mono hB₁.le)
    refine ⟨Built.combine hB₁ hB₂ (closed_both hB₁.closed hB₂.closed)
      (mono_both hB₁.mono hB₂.mono)
      (fun _ _ _ he _ hv => vars_both he hv) (fun _ _ h => Lbl.mem_both h)
      (fun _ _ h => Lbl.mem_both h) (fun _ _ h => Lbl.mem_both h), ?_⟩
    intro M hM fuel hf ξ i j hj
    show (QComp.both _ _).Acc t δ _ ξ i j ↔ _
    have hM₁ := hB₂.pre.trans hM
    rw [acc_both hB₁.closed hB₂.closed]
    constructor
    · rintro ⟨a, ha, b, hb, ξ', hξ', h₁, h₂, hok₁, hok₂⟩
      have heq : ξ' ∘ ρ = ξ ∘ ρ := comp_eq_of_scope hρ
        (S := fun v => v ∈ (F.build Ψ ρ n cs).comp.scope a ∨ v ∈ (G.build Ψ ρ _ _).comp.scope b)
        (fun v hv => hv.elim (fun h => (hB₁.scope a v h).not_below)
          (fun h hb => (hB₂.scope b v h).not_below (hb.mono hB₁.le)))
        (fun v hv => hξ' v (fun h => hv (Or.inl h)) (fun h => hv (Or.inr h)))
      obtain ⟨j₁, hj₁, hF⟩ := (hC₁ M hM₁ fuel hf ξ' i j hj).1 ⟨a, ha, ξ', fun _ _ => rfl, h₁, hok₁⟩
      obtain ⟨j₂, hj₂, hG⟩ := (hC₂ M hM fuel hf ξ' i j hj).1 ⟨b, hb, ξ', fun _ _ => rfl, h₂, hok₂⟩
      rw [heq] at hF hG
      exact ⟨max j₁ j₂, by omega, .both hF hG rfl⟩
    · rintro ⟨j', hj', hS⟩
      obtain ⟨j₁, j₂, hF, hG, rfl⟩ := Pat.sat_both.1 hS
      obtain ⟨a, ha, ξa, hξa, h₁, hok₁⟩ := (hC₁ M hM₁ fuel hf ξ i j hj).2 ⟨j₁, by omega, hF⟩
      have heqa : ξa ∘ ρ = ξ ∘ ρ := comp_eq_of_scope hρ (S := fun v => v ∈ _ )
        (fun v hv => (hB₁.scope a v hv).not_below) hξa
      obtain ⟨b, hb, ξb, hξb, h₂, hok₂⟩ := (hC₂ M hM fuel hf ξa i j hj).2
        ⟨j₂, by omega, by show Pat.Sat _ _ _ _ _ _ _; rw [heqa]; exact hG⟩
      obtain ⟨hξ', h₁', hok₁', _⟩ := combine_acc hρ hB₁ hB₂ hM hξa hξb h₁ hok₁
      exact ⟨a, ha, b, hb, ξb, hξ', h₁', h₂, hok₁', hok₂⟩

end correct


/-! ## Correctness of query bodies -/

section body

variable {t : List Act} {δ : Obs}

theorem QBody.sat_iff {Θ : Interp} {ξ : LEnv} {P : QBody} {i j : Nat} :
    Θ ⬝ t ⬝ δ ⬝ ξ ⊨ P : i ⇝ j ↔
      ∃ ls : List Loc, ls.length = P.locals.length ∧
        (Θ ⬝ t ⬝ δ ⬝ ξ.bind P.locals ls ⊨ P.pattern : i ⇝ j) ∧ (δ ⬝ ξ.bind P.locals ls ⊨ P.when) ∧
        ∀ F', P.except = some F' → ∀ k ≤ t.length, ¬ Θ ⬝ t ⬝ δ ⬝ ξ.bind P.locals ls ⊨ F' : 0 ⇝ k := by
  constructor
  · intro h
    cases h with
    | mk hlen hξ hpat hwhen hexc => subst hξ; exact ⟨_, hlen, hpat, hwhen, hexc⟩
  · rintro ⟨ls, hlen, hpat, hwhen, hexc⟩
    exact .mk hlen rfl hpat hwhen hexc

theorem LEnv.bind_map (ξ : LEnv) (g : Var → Loc) :
    ∀ (ys : List Var) (x : Var), x ∈ ys → LEnv.bind ξ ys (ys.map g) x = g x
  | [], _, hx => by simp at hx
  | y :: ys, x, hx => by
      simp only [List.map_cons, LEnv.bind]
      by_cases hxy : x = y
      · subst hxy; simp
      · rw [if_neg hxy]
        exact LEnv.bind_map ξ g ys x ((List.mem_cons.1 hx).resolve_left hxy)

/-- What a body's renaming must satisfy: nothing minted from `n` on, locals
    renamed apart from each other and from everything else. -/
structure BodyRen (P : QBody) (ρ : Var → MVar) (n : Nat) : Prop where
  below : ∀ x, (ρ x).Below n
  inj   : ∀ x ∈ P.locals, ∀ y ∈ P.locals, ρ x = ρ y → x = y
  sep   : ∀ x ∈ P.vars, x ∉ P.locals → ∀ y ∈ P.locals, ρ x ≠ ρ y

/-- Choosing new values for the renamed locals is choosing values for the
    locals: the two forms of a body's `∃ ys`. -/
theorem bind_bridge {P : QBody} {ρ : Var → MVar} {n : Nat} (hren : BodyRen P ρ n)
    {ξ : MEnv} {ξq : LEnv} (hval : ∀ x ∈ P.vars, x ∉ P.locals → ξ (ρ x) = ξq x)
    (Φ : LEnv → Prop) (hΦ : ∀ η₁ η₂ : LEnv, (∀ x ∈ P.vars, η₁ x = η₂ x) → (Φ η₁ ↔ Φ η₂)) :
    (∃ ξ₁ : MEnv, (∀ v, v ∉ P.locals.map ρ → ξ₁ v = ξ v) ∧ Φ (ξ₁ ∘ ρ)) ↔
      ∃ ls : List Loc, ls.length = P.locals.length ∧ Φ (ξq.bind P.locals ls) := by
  -- A non-local's renaming is not a renamed local.
  have hout : ∀ x ∈ P.vars, x ∉ P.locals → ρ x ∉ P.locals.map ρ := by
    intro x hx hxl hm
    obtain ⟨y, hy, he⟩ := List.mem_map.1 hm
    exact hren.sep x hx hxl y hy he.symm
  constructor
  · rintro ⟨ξ₁, h₁, hΦ₁⟩
    refine ⟨P.locals.map (fun y => ξ₁ (ρ y)), by simp, (hΦ _ _ fun x hx => ?_).1 hΦ₁⟩
    by_cases hxl : x ∈ P.locals
    · exact (LEnv.bind_map ξq _ P.locals x hxl).symm
    · rw [LEnv.bind_eq_of_not_mem _ _ _ _ hxl]
      show ξ₁ (ρ x) = ξq x
      rw [h₁ _ (hout x hx hxl), hval x hx hxl]
  · rintro ⟨ls, _, hΦ₂⟩
    let ξ₁ : MEnv := fun v => match P.locals.find? (fun y => decide (ρ y = v)) with
      | some y => ξq.bind P.locals ls y
      | none   => ξ v
    have hnone : ∀ v, v ∉ P.locals.map ρ → ξ₁ v = ξ v := by
      intro v hv
      have : P.locals.find? (fun y => decide (ρ y = v)) = none :=
        List.find?_eq_none.2 fun y hy h => hv (List.mem_map.2 ⟨y, hy, by simpa using h⟩)
      simp [ξ₁, this]
    refine ⟨ξ₁, hnone, (hΦ _ _ fun x hx => ?_).2 hΦ₂⟩
    by_cases hxl : x ∈ P.locals
    · have hsome : ∃ y, P.locals.find? (fun y => decide (ρ y = ρ x)) = some y :=
        Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨x, hxl, by simp⟩)
      obtain ⟨y, hy⟩ := hsome
      have hyx : y = x := hren.inj y (List.mem_of_find?_eq_some hy) x hxl
        (by simpa using List.find?_some hy)
      subst hyx
      show ξ₁ (ρ y) = _
      simp [ξ₁, hy]
    · rw [LEnv.bind_eq_of_not_mem _ _ _ _ hxl]
      show ξ₁ (ρ x) = ξq x
      rw [hnone _ (hout x hx hxl), hval x hx hxl]

/-- Acceptance by a guarded automaton: new values for the locals, then the
    guard, then acceptance by the automaton of the pattern. -/
theorem acc_guard {A : QComp} {I : Inv MVar} {locs : List MVar} {ks : List Nat}
    {X : Nat → MEnv → Prop} {ξ : MEnv} {i j : Nat}
    (hind : ∀ f ξ' ξ₁, (∀ v, v ∉ A.scope f → ξ' v = ξ₁ v) →
      ((δ ⬝ ξ' ⊨ I) ↔ (δ ⬝ ξ₁ ⊨ I)) ∧ ∀ k ∈ ks, (X k ξ' ↔ X k ξ₁)) :
    (A.guard I locs ks).Acc t δ X ξ i j ↔
      ∃ ξ₁ : MEnv, (∀ v, v ∉ locs → ξ₁ v = ξ v) ∧ (δ ⬝ ξ₁ ⊨ I) ∧ (∀ k ∈ ks, ¬ X k ξ₁) ∧
        A.Acc t δ X ξ₁ i j := by
  constructor
  · rintro ⟨f, hf, ξ', hξ', hr, hinv, hexc⟩
    simp only [QComp.guard, List.mem_cons, List.mem_append, not_or] at hξ' hinv hexc
    let ξ₁ : MEnv := fun v => if v ∈ A.scope f then ξ v else ξ' v
    have h₁ : ∀ v, v ∉ A.scope f → ξ' v = ξ₁ v := fun v hv => by simp [ξ₁, hv]
    obtain ⟨hI, hX⟩ := hind f ξ' ξ₁ h₁
    refine ⟨ξ₁, fun v hv => ?_, hI.1 (hinv I (Or.inl rfl)),
      fun k hk hk' => hexc k (Or.inl hk) ((hX k hk).2 hk'),
      ⟨f, hf, ξ', h₁, hr, fun I' h => hinv I' (Or.inr h), fun k h => hexc k (Or.inr h)⟩⟩
    by_cases hs : v ∈ A.scope f
    · simp [ξ₁, hs]
    · simp only [ξ₁, hs, if_false]; exact hξ' v ⟨hv, hs⟩
  · rintro ⟨ξ₁, h₁, hI, hX, f, hf, ξ', hξ', hr, hinv, hexc⟩
    obtain ⟨hI', hX'⟩ := hind f ξ' ξ₁ hξ'
    refine ⟨f, hf, ξ', fun v hv => ?_, hr, ?_, ?_⟩
    · simp only [QComp.guard, List.mem_append, not_or] at hv
      rw [hξ' v hv.2, h₁ v hv.1]
    · simp only [QComp.guard, List.mem_cons]
      rintro I' (rfl | h)
      · exact hI'.2 hI
      · exact hinv I' h
    · simp only [QComp.guard, List.mem_append]
      rintro k (hk | hk) hk'
      · exact hX k hk ((hX' k hk).1 hk')
      · exact hexc k hk hk'

/-- What a body construction guarantees, as `Built` but for the scope, which
    also contains the renamed locals. -/
structure BodyBuilt (P : QBody) (ρ : Var → MVar) (n : Nat) (cs : List QComp) (r : BRes) : Prop where
  le     : n ≤ r.next
  pre    : cs <+: r.comps
  closed : r.comp.Closed
  scope  : ∀ s, ∀ v ∈ r.comp.scope s, v ∈ P.locals.map ρ ∨ v.InRange n r.next
  reads  : r.comp.ReadsIn r.comps (MVar.Below r.next)
  mono   : r.comp.Mono
  comps  : (∀ c ∈ cs, c.Closed ∧ c.Mono) → ∀ c ∈ r.comps, c.Closed ∧ c.Mono

theorem bodyOK {Ψ : Builder} {Θ : Interp} {d : Nat} (hPat : PatOK t δ Ψ Θ d) (hΘ : Θ.Ok t)
    {P : QBody} {ρ : Var → MVar} {n : Nat} (hren : BodyRen P ρ n) (cs : List QComp) :
    BodyBuilt P ρ n cs (P.build Ψ ρ n cs) ∧
    ∀ M : List QComp, (P.build Ψ ρ n cs).comps <+: M → ∀ fuel, d + 1 ≤ fuel →
      ∀ (ξ : MEnv) (ξq : LEnv), (∀ x ∈ P.vars, x ∉ P.locals → ξ (ρ x) = ξq x) →
      ∀ i j, j ≤ t.length →
        ((P.build Ψ ρ n cs).comp.Acc t δ (compSat M t δ fuel) ξ i j ↔
          ∃ j', j' ≤ j ∧ Θ ⬝ t ⬝ δ ⬝ ξq ⊨ P : i ⇝ j') := by
  obtain ⟨hB, hC⟩ := hPat ρ P.pattern n cs hren.below
  -- Everything the body adds reads only variables below the fresh tags.
  have hlocs : ∀ v ∈ P.locals.map ρ, v.Below n := by
    simp only [List.mem_map]; rintro _ ⟨x, _, rfl⟩; exact hren.below x
  have hwhen : ∀ v ∈ (P.when.map ρ).vars, v.Below n := by
    rw [Inv.vars_map]; simp only [List.mem_map]; rintro _ ⟨x, _, rfl⟩; exact hren.below x
  -- The guard's invariant depends on the substitution only through `ρ`.
  have hρeq : ∀ f (ξ' ξ₁ : MEnv), (∀ v, v ∉ (P.pattern.build Ψ ρ n cs).comp.scope f → ξ' v = ξ₁ v) →
      ξ' ∘ ρ = ξ₁ ∘ ρ := fun f ξ' ξ₁ h =>
    comp_eq_of_scope hren.below (S := fun v => v ∈ _) (fun v hv => (hB.scope f v hv).not_below) h
  -- The body, once the locals are chosen.
  have core : ∀ (M : List QComp) fuel (ks : List Nat) (ξ : MEnv) (ξq : LEnv) (i j : Nat),
      (P.pattern.build Ψ ρ n cs).comps <+: M → d ≤ fuel → j ≤ t.length →
      (∀ x ∈ P.vars, x ∉ P.locals → ξ (ρ x) = ξq x) →
      (∀ k ∈ ks, ∀ η η' : MEnv, η ∘ ρ = η' ∘ ρ →
        (compSat M t δ fuel k η ↔ compSat M t δ fuel k η')) →
      (∀ (η : MEnv), (∀ k ∈ ks, ¬ compSat M t δ fuel k η) ↔
        ∀ F', P.except = some F' → ∀ k, ¬ Θ ⬝ t ⬝ δ ⬝ (η ∘ ρ) ⊨ F' : 0 ⇝ k) →
      (((P.pattern.build Ψ ρ n cs).comp.guard (P.when.map ρ) (P.locals.map ρ) ks).Acc t δ
          (compSat M t δ fuel) ξ i j ↔ ∃ j', j' ≤ j ∧ Θ ⬝ t ⬝ δ ⬝ ξq ⊨ P : i ⇝ j') := by
    intro M fuel ks ξ ξq i j hM hf hj hval hksρ hks
    rw [acc_guard (fun f ξ' ξ₁ h => ⟨by rw [Inv.sat_map, Inv.sat_map, hρeq f ξ' ξ₁ h],
      fun k hk => hksρ k hk ξ' ξ₁ (hρeq f ξ' ξ₁ h)⟩)]
    -- Reorganise both sides around the choice of the locals.
    have lhs : ∀ ξ₁ : MEnv, ((δ ⬝ ξ₁ ⊨ P.when.map ρ) ∧ (∀ k ∈ ks, ¬ compSat M t δ fuel k ξ₁) ∧
        (P.pattern.build Ψ ρ n cs).comp.Acc t δ (compSat M t δ fuel) ξ₁ i j) ↔
        ((δ ⬝ (ξ₁ ∘ ρ) ⊨ P.when) ∧
          (∀ F', P.except = some F' → ∀ k, ¬ Θ ⬝ t ⬝ δ ⬝ (ξ₁ ∘ ρ) ⊨ F' : 0 ⇝ k) ∧
          ∃ j', j' ≤ j ∧ Θ ⬝ t ⬝ δ ⬝ (ξ₁ ∘ ρ) ⊨ P.pattern : i ⇝ j') := by
      intro ξ₁
      rw [Inv.sat_map, hks ξ₁, hC M hM fuel hf ξ₁ i j hj]
    simp only [lhs]
    rw [bind_bridge hren hval (fun η => (δ ⬝ η ⊨ P.when) ∧
      (∀ F', P.except = some F' → ∀ k, ¬ Θ ⬝ t ⬝ δ ⬝ η ⊨ F' : 0 ⇝ k) ∧
      ∃ j', j' ≤ j ∧ Θ ⬝ t ⬝ δ ⬝ η ⊨ P.pattern : i ⇝ j')]
    · constructor
      · rintro ⟨ls, hlen, hw, hx, j', hj', hp⟩
        exact ⟨j', hj', QBody.sat_iff.2 ⟨ls, hlen, hp, hw, fun F' hF' k _ => hx F' hF' k⟩⟩
      · rintro ⟨j', hj', hb⟩
        obtain ⟨ls, hlen, hp, hw, hx⟩ := QBody.sat_iff.1 hb
        exact ⟨ls, hlen, hw, fun F' hF' => (Pat.not_sat_zero_iff hΘ).1 (hx F' hF'), j', hj', hp⟩
    · intro η₁ η₂ h
      have hp : ∀ x ∈ P.pattern.vars, η₁ x = η₂ x := fun x hx =>
        h x (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hx))))
      have hw : ∀ x ∈ P.when.vars, η₁ x = η₂ x := fun x hx =>
        h x (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hx))))
      have hx : ∀ F', P.except = some F' → ∀ x ∈ F'.vars, η₁ x = η₂ x := fun F' hF' x hx =>
        h x (List.mem_append.2 (Or.inr (by rw [hF']; exact hx)))
      rw [Inv.sat_coincide hw]
      constructor
      · rintro ⟨h₁, h₂, j', hj', h₃⟩
        exact ⟨h₁, fun F' hF' k hk => h₂ F' hF' k ((Pat.sat_coincide (hx F' hF')).2 hk),
          j', hj', (Pat.sat_coincide hp).1 h₃⟩
      · rintro ⟨h₁, h₂, j', hj', h₃⟩
        exact ⟨h₁, fun F' hF' k hk => h₂ F' hF' k ((Pat.sat_coincide (hx F' hF')).1 hk),
          j', hj', (Pat.sat_coincide hp).2 h₃⟩
  -- The bookkeeping of a guarded automaton, given that of its components.
  have guardBuilt : ∀ (ks : List Nat) (n' : Nat) (cs' : List QComp),
      (P.pattern.build Ψ ρ n cs).next ≤ n' → (P.pattern.build Ψ ρ n cs).comps <+: cs' →
      (∀ k ∈ ks, k < cs'.length ∧ ∀ c', cs'[k]? = some c' → c'.ReadsIn cs' (MVar.Below n')) →
      ((∀ c ∈ cs, c.Closed ∧ c.Mono) → ∀ c ∈ cs', c.Closed ∧ c.Mono) →
      BodyBuilt P ρ n cs
        ⟨(P.pattern.build Ψ ρ n cs).comp.guard (P.when.map ρ) (P.locals.map ρ) ks, n', cs'⟩ := by
    intro ks n' cs' hn' hcs' hks hcomps
    have hR := (hB.reads.extend hcs').weaken (fun _ hv => MVar.Below.mono hn' hv)
    refine ⟨Nat.le_trans hB.le hn', hB.pre.trans hcs',
      ⟨hB.closed.start, hB.closed.edges, hB.closed.finals⟩, fun s v hv => ?_, ?_, ?_, hcomps⟩
    · rcases List.mem_append.1 hv with h | h
      · exact Or.inl h
      · exact Or.inr ((hB.scope s v h).mono (Nat.le_refl _) hn')
    · refine .mk hR.edges (fun s I hI v hv => ?_) (fun s v hv => ?_) (fun s k hk => ?_)
        (fun s k hk c' hc' => ?_)
      · rcases List.mem_cons.1 hI with rfl | h
        · exact (hwhen v hv).mono (Nat.le_trans hB.le hn')
        · exact hR.inv s I h v hv
      · rcases List.mem_append.1 hv with h | h
        · exact (hlocs v h).mono (Nat.le_trans hB.le hn')
        · exact hR.scope s v h
      · rcases List.mem_append.1 hk with h | h
        · exact (hks k h).1
        · exact hR.excLt s k h
      · rcases List.mem_append.1 hk with h | h
        · exact (hks k h).2 c' hc'
        · exact hR.exc s k h c' hc'
    · intro s l s' he
      obtain ⟨h₁, h₂⟩ := hB.mono s l s' he
      exact ⟨List.cons_subset_cons _ h₁, List.subset_append_both (List.Subset.refl _) h₂⟩
  unfold QBody.build
  split
  · rename_i hex
    refine ⟨guardBuilt [] _ _ (Nat.le_refl _) (List.prefix_refl _) (by simp) hB.comps, ?_⟩
    intro M hM fuel hf ξ ξq hval i j hj
    exact core M fuel [] ξ ξq i j hM (by omega) hj hval (by simp) (by simp [hex])
  · rename_i F' hex
    obtain ⟨hBe, hCe⟩ := hPat ρ F' _ _ (fun x => (hren.below x).mono hB.le)
    let E := (F'.build Ψ ρ (P.pattern.build Ψ ρ n cs).next (P.pattern.build Ψ ρ n cs).comps)
    have hEpre : E.comps <+: E.comps ++ [E.comp] := List.prefix_append _ _
    have hEget : (E.comps ++ [E.comp])[E.comps.length]? = some E.comp := by simp
    have hElt : E.comps.length < (E.comps ++ [E.comp]).length := by
      rw [List.length_append, List.length_singleton]; omega
    refine ⟨guardBuilt [E.comps.length] _ _ hBe.le (hBe.pre.trans hEpre) ?_ ?_, ?_⟩
    · simp only [List.mem_singleton, forall_eq]
      refine ⟨hElt, fun c' hc' => ?_⟩
      rw [hEget] at hc'; cases hc'
      exact hBe.reads.extend hEpre
    · intro h c hc
      rcases List.mem_append.1 hc with hc | hc
      · exact hBe.comps (hB.comps h) c hc
      · rw [List.mem_singleton] at hc; subst hc; exact ⟨hBe.closed, hBe.mono⟩
    · intro M hM fuel hf ξ ξq hval i j hj
      obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
      have hME : M[E.comps.length]? = some E.comp := by
        rw [getElem?_of_prefix hM hElt]; exact hEget
      -- The `except` component is satisfied iff the excluded pattern occurs.
      have hX : ∀ η : MEnv, compSat M t δ (m + 1) E.comps.length η ↔
          ∃ k, Θ ⬝ t ⬝ δ ⬝ (η ∘ ρ) ⊨ F' : 0 ⇝ k := by
        intro η
        simp only [compSat, hME, Option.some.injEq, exists_eq_left']
        rw [hCe M (hEpre.trans hM) m (by omega) η 0 t.length (Nat.le_refl _)]
        exact ⟨fun ⟨k, _, h⟩ => ⟨k, h⟩, fun ⟨k, h⟩ => ⟨k, h.bound hΘ (Nat.zero_le _), h⟩⟩
      refine core M (m + 1) [E.comps.length] ξ ξq i j
        (hBe.pre.trans (hEpre.trans hM)) (by omega) hj hval ?_ ?_
      · simp only [List.mem_singleton, forall_eq]
        intro η η' h; rw [hX, hX, h]
      · intro η
        simp only [List.mem_singleton, forall_eq, hX, hex, Option.some.injEq, forall_eq']
        exact ⟨fun h k hk => h ⟨k, hk⟩, fun h ⟨k, hk⟩ => h k hk⟩

end body


/-! ## Correctness of invocations and of the whole translation -/

section program

variable {t : List Act} {δ : Obs}

theorem assoc_mem {x : Var} : ∀ {ps : List Var} {args : List MVar} {v : MVar},
    assoc x ps args = some v → v ∈ args
  | [], _, _, h => by simp [assoc] at h
  | _ :: _, [], _, h => by simp [assoc] at h
  | p :: ps, a :: as, v, h => by
      simp only [assoc] at h
      split at h
      · cases h; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (assoc_mem h)

/-- A parameter's renaming denotes the location the semantics binds it to. -/
theorem assoc_bind (ξ₀ : LEnv) (ξ : MEnv) {x : Var} : ∀ {ps : List Var} {args : List MVar},
    x ∈ ps → ps.length = args.length →
      ∃ v, assoc x ps args = some v ∧ LEnv.bind ξ₀ ps (args.map ξ) x = ξ v
  | [], _, hx, _ => by simp at hx
  | _ :: _, [], _, h => by simp at h
  | p :: ps, a :: as, hx, h => by
      simp only [assoc, List.map_cons, LEnv.bind]
      by_cases hxp : x = p
      · simp [hxp]
      · simp only [hxp, if_false]
        exact assoc_bind ξ₀ ξ ((List.mem_cons.1 hx).resolve_left hxp) (by simpa using h)

/-- The renaming of an invoked query meets the requirements of `bodyOK`. -/
theorem Query.ren_bodyRen (q : Query) {args : List MVar} {n : Nat}
    (hargs : ∀ v ∈ args, v.Below n) : BodyRen q.body (q.ren args n) (n + 1) where
  below x := by
    unfold Query.ren
    split
    · show n < n + 1; omega
    · cases h : assoc x q.params args with
      | none => show n < n + 1; omega
      | some v => exact (hargs v (assoc_mem h)).mono (by omega)
  inj x hx y hy h := by
    simp only [Query.ren, hx, hy, if_true] at h
    exact (MVar.tag.inj h).2
  sep x _ hxl y hy h := by
    simp only [Query.ren, hxl, hy, if_true, if_false] at h
    cases ha : assoc x q.params args with
    | none => rw [ha] at h; exact hxl ((MVar.tag.inj h).2 ▸ hy)
    | some v =>
      rw [ha] at h
      have := hargs v (assoc_mem ha)
      rw [Option.getD_some] at h
      subst h
      simp [MVar.Below] at this

theorem Correct.mono {d d' : Nat} (h : d ≤ d') {r : BRes} {R : MEnv → Nat → Nat → Prop}
    (hC : Correct t δ d r R) : Correct t δ d' r R :=
  fun M hM fuel hf => hC M hM fuel (Nat.le_trans h hf)

theorem QProg.WF.declared : ∀ {Δ : QProg}, QProg.WF Δ → ∀ q ∈ Δ, q.Declared
  | [], _, _, hq => by simp at hq
  | q' :: Δ, ⟨hq', _, hΔ⟩, q, hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hq'.1
      · exact QProg.WF.declared hΔ q hq

/-- Invocations resolved in `Δ` are correct, for fuel at least `Δ.length`. -/
theorem buildOK : ∀ (Δ : QProg), (∀ q ∈ Δ, q.Declared) →
    BuilderOK t δ (QProg.build Δ) (QProg.interp t δ Δ) Δ.length
  | [], _ => by
      intro Q args n cs _
      refine ⟨Built.plain closed_empty (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (by intro s l s' h; simp [QComp.empty] at h; simp [h.2.1, MLbl.vars]), ?_⟩
      intro M _ fuel _ ξ i j _
      show QComp.empty.Acc t δ _ ξ i j ↔ _
      rw [acc_empty]; simp [QProg.interp]
  | q :: Δ, hd => by
      have ih := buildOK Δ (fun q' h => hd q' (List.mem_cons_of_mem _ h))
      have hpat := patOK ih (QProg.interp_ok Δ t δ) (QProg.interp_lowerStart Δ t δ)
      intro Q args n cs hargs
      by_cases hQ : Q = q.name
      · subst hQ
        by_cases hlen : args.length = q.params.length
        · have hb : QProg.build (q :: Δ) q.name args n cs =
              QBody.build (QProg.build Δ) (q.ren args n) q.body (n + 1) cs := by
            simp [QProg.build, hlen]
          rw [hb]
          obtain ⟨hBB, hBC⟩ := bodyOK hpat (QProg.interp_ok Δ t δ) (q.ren_bodyRen hargs) cs
          refine ⟨⟨by have := hBB.le; omega, hBB.pre, hBB.closed, fun s v hv => ?_, hBB.reads,
            hBB.mono, hBB.comps⟩, ?_⟩
          · rcases hBB.scope s v hv with h | h
            · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
              simp only [Query.ren, hy, if_true, MVar.InRange]
              have := hBB.le; omega
            · exact h.mono (by omega) (Nat.le_refl _)
          · intro M hM fuel hf ξ i j hj
            rw [hBC M hM fuel (by simpa using hf) ξ (LEnv.empty.bind q.params (args.map ξ)) ?_ i j hj]
            · simp only [QProg.interp_head, List.length_map, hlen, true_and]
            · intro x hx hxl
              have hxp : x ∈ q.params :=
                ((hd q (List.mem_cons_self ..)).2 x hx).resolve_right hxl
              obtain ⟨v, hv, hb⟩ := assoc_bind LEnv.empty ξ hxp hlen.symm
              simp only [Query.ren, hxl, if_false, hv, Option.getD_some]
              exact hb.symm
        · have hb : QProg.build (q :: Δ) q.name args n cs = ⟨.empty, n, cs⟩ := by
            simp [QProg.build, hlen]
          rw [hb]
          refine ⟨Built.plain closed_empty (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
            (by intro s l s' h; simp [QComp.empty] at h; simp [h.2.1, MLbl.vars]), ?_⟩
          intro M _ fuel _ ξ i j _
          show QComp.empty.Acc t δ _ ξ i j ↔ _
          rw [acc_empty]
          simp [QProg.interp_head, hlen]
      · have hb : QProg.build (q :: Δ) Q args n cs = QProg.build Δ Q args n cs := by
          simp [QProg.build, hQ]
        rw [hb]
        obtain ⟨hB, hC⟩ := ih Q args n cs hargs
        refine ⟨hB, fun M hM fuel hf ξ i j hj => ?_⟩
        rw [(hC.mono (by simp)) M hM fuel hf ξ i j hj]
        simp only [QProg.interp_tail q Δ t δ hQ]

/-- **Semantic equivalence.** For a well-formed program `q :: Δ`, an
    execution record satisfies the query model of `q` applied to `ls` iff it
    matches `q` applied to `ls`. -/
theorem Query.toQModel_correct {Δ : QProg} {q : Query} (hwf : QProg.WF (q :: Δ)) (e : Exec)
    {ls : List Loc} (hlen : ls.length = q.params.length) :
    (q.toQModel Δ).Sat e ls ↔ Exec.Matches (q :: Δ) e q.name ls := by
  have hpat := patOK (t := e.trc.toList) (δ := e.obs)
    (buildOK Δ (QProg.WF.declared hwf.2.2)) (QProg.interp_ok Δ _ _) (QProg.interp_lowerStart Δ _ _)
  have hren : BodyRen q.body MVar.src 0 :=
    ⟨fun _ => trivial, fun _ _ _ _ h => MVar.src.inj h,
      fun _ _ hx _ hy h => hx (MVar.src.inj h ▸ hy)⟩
  obtain ⟨_, hC⟩ := bodyOK hpat (QProg.interp_ok Δ _ _) hren []
  refine (hC (q.toQModel Δ).comps (List.prefix_refl _) (Δ.length + 1) (Nat.le_refl _)
    ((q.toQModel Δ).env ls) (LEnv.empty.bind q.params ls) (fun _ _ _ => rfl) 0 _
    (Nat.le_refl _)).trans ?_
  rw [Exec.Matches.iff_head]
  simp only [hlen, true_and]
  exact ⟨fun ⟨j, _, h⟩ => ⟨j, h⟩,
    fun ⟨j, h⟩ => ⟨j, h.bound (QProg.interp_ok Δ _ _) (Nat.zero_le _), h⟩⟩

/-- The constructed model is well formed: every component is closed, and its
    invariants and scope grow along edges (so a model checker may discard a
    substitution as soon as it violates the current state's invariants). -/
theorem Query.toQModel_wf {Δ : QProg} {q : Query} (hwf : QProg.WF (q :: Δ)) :
    (q.toQModel Δ).main.Closed ∧ (q.toQModel Δ).main.Mono ∧
      ∀ c ∈ (q.toQModel Δ).comps, c.Closed ∧ c.Mono := by
  have hpat := patOK (t := [])
    (δ := ⟨fun _ => none, fun _ _ => False, fun _ => False, fun _ => False⟩)
    (buildOK Δ (QProg.WF.declared hwf.2.2)) (QProg.interp_ok Δ _ _) (QProg.interp_lowerStart Δ _ _)
  have hren : BodyRen q.body MVar.src 0 :=
    ⟨fun _ => trivial, fun _ _ _ _ h => MVar.src.inj h,
      fun _ _ hx _ hy h => hx (MVar.src.inj h ▸ hy)⟩
  obtain ⟨hB, _⟩ := bodyOK hpat (QProg.interp_ok Δ _ _) hren []
  exact ⟨hB.closed, hB.mono, hB.comps (by simp)⟩

end program


/-! ## Examples

Computed models of a few queries, checked at compile time.  Update them
deliberately if the construction changes. -/

section examples

/-- `Inj(f, v) { Call(f, [v]) when sk(f) }`. -/
private def qInj : Query :=
  { name := "Inj", params := ["f", "v"],
    body := { pattern := .act (.call "f" ["v"]), when := .pred (.sk "f") } }

-- `Any*`, the call, `Any*`; the invariant holds on every state.
#guard (qInj.toQModel []).main.edges ==
  [(.s0, .any, .s0), (.s0, .act [.call (.src "f") [.src "v"]], .s1), (.s1, .any, .s1)]
#guard (qInj.toQModel []).main.finals == [.s1]
#guard (qInj.toQModel []).main.inv .s0 == [.pred (.sk (.src "f"))]
#guard (qInj.toQModel []).comps.length == 0

/-- `Sanitized(v) { ∃g: Call(g, [v]) when ac(g) }`. -/
private def qSan : Query :=
  { name := "Sanitized", params := ["v"],
    body := { locals := ["g"], pattern := .act (.call "g" ["v"]), when := .pred (.ac "g") } }

/-- `Safe(f, v) { Call(f, [v]) when sk(f) except Sanitized(v) }`. -/
private def qSafe : Query :=
  { name := "Safe", params := ["f", "v"],
    body := { pattern := .act (.call "f" ["v"]), when := .pred (.sk "f"),
              except := some (.query "Sanitized" ["v"]) } }

-- One `except` component, referred to from every state of the positive part;
-- inside it, the sanitizer's local `g` is the tag of invocation `0`, bound
-- there (in its scope) with its invariant.
#guard (qSafe.toQModel [qSan]).comps.length == 1
#guard (qSafe.toQModel [qSan]).main.exc .s1 == [0]
#guard ((qSafe.toQModel [qSan]).comps.map fun c => c.scope .s1) == [[.tag 0 "g"]]
#guard ((qSafe.toQModel [qSan]).comps.map fun c => c.inv .s1) == [[.pred (.ac (.tag 0 "g"))]]
#guard ((qSafe.toQModel [qSan]).comps.map fun c => c.edges) ==
  [[(.s0, .any, .s0), (.s0, .act [.call (.tag 0 "g") [.src "v"]], .s1), (.s1, .any, .s1)]]

/-- `Twice(f) { Call(f, []) & Call(f, []) }`. -/
private def qTwice : Query :=
  { name := "Twice", params := ["f"],
    body := { pattern := .both (.act (.call "f" [])) (.act (.call "f" [])) } }

-- The joint step: one trace action serves both sides.
#guard (qTwice.toQModel []).main.edges.contains
  (.both .s0 .s0, .act [.call (.src "f") [], .call (.src "f") []], .both .s1 .s1)
#guard (qTwice.toQModel []).main.finals == [.both .s1 .s1]

/-- `Pick(f) { (Q(f) ‖ ε) ; Call(f, []) }` with `Q(x) { ∃y: Call(x, [y]) when ac(y) }`:
    the final states remember whether `Q` was used. -/
private def qQ : Query :=
  { name := "Q", params := ["x"],
    body := { locals := ["y"], pattern := .act (.call "x" ["y"]), when := .pred (.ac "y") } }
private def qPick : Query :=
  { name := "Pick", params := ["f"],
    body := { pattern := .seq (.alt (.query "Q" ["f"]) .eps) (.act (.call "f" [])) } }

#guard (qPick.toQModel [qQ]).main.finals == [.seqR (.altL .s1) .s1, .seqR (.altR .s0) .s1]
#guard (qPick.toQModel [qQ]).main.scope (.seqR (.altL .s1) .s1) == [.tag 0 "y"]
#guard (qPick.toQModel [qQ]).main.scope (.seqR (.altR .s0) .s1) == []
#guard (qPick.toQModel [qQ]).main.inv (.seqR (.altL .s1) .s1) == [.tt, .pred (.ac (.tag 0 "y"))]
#guard (qPick.toQModel [qQ]).main.inv (.seqR (.altR .s0) .s1) == [.tt]

end examples

end CoreJS
