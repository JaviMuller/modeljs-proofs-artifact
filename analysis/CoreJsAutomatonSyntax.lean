/-
  # Core JavaScript — Automaton State Space

  This file is *not* a transcription of any figure in the paper: it is this
  branch's own contribution, replacing the μ-trace/summary machinery of
  `ATrc`/`ASummary`/`ASigma`/`ACallBranch` (see `CoreJsAbstractSemantics.lean`,
  now trimmed) with a finite-state automaton whose states and edges are a
  purely static (value-independent) function of the call graph. Motivation and
  the full design discussion are in `DESIGN_AND_PLAN.md` at the repository
  root; read it before this file, in particular §4.2 ("`CallString` and
  `AState`") which this file implements essentially verbatim.

  See `PROBLEMS.md` for the implementation decisions made while turning that
  design into Lean that the design document itself left open.

  Plain Lean 4 — no Mathlib required.
-/

import CoreJsSyntax

namespace CoreJS

/-! ## Call strings

A call string records, for every call currently "open" on the path from the
top level to the current point, the site at which it was made and the
function it entered. Decision 5 of `DESIGN_AND_PLAN.md`: a *non-recursive*
call (its target not already open on the current path) extends the call
string; a *recursive* call (target already open) does not — the callee's
entry is shared with the first, outermost occurrence of that target on the
path. -/

/-- `cs ∈ CallString`: a snapshot of the call sites currently open, oldest
    first. -/
abbrev CallString := List (Idx × Fid)

/-- The function identifiers occurring in a call string, in order. -/
def CallString.fids (cs : CallString) : List Fid := cs.map Prod.snd

/-- Well-formedness: no function identifier occurs twice. This is both what
    justifies "the first/outermost occurrence" being well defined in
    `targetCallString` below, and what bounds a call string's length by the
    (finite) number of functions in scope — see `CallString.length_le` at the
    end of this section. -/
def CallString.WF (cs : CallString) : Prop := cs.fids.Nodup

theorem CallString.WF.nil : CallString.WF [] := List.nodup_nil

/-- The prefix of `cs` ending at (and including) `f`'s first occurrence.
    Total: if `f` does not occur in `cs`, returns `cs` unchanged (this case is
    never taken by `targetCallString`, which only calls it under a membership
    guard, but totality keeps the definition simple). -/
def CallString.truncateAt (f : Fid) : CallString → CallString
  | []          => []
  | p :: rest   => if p.2 = f then [p] else p :: CallString.truncateAt f rest

/-- Every element of the truncated prefix already occurred in `cs`. -/
theorem CallString.mem_truncateAt {f : Fid} :
    ∀ {cs : CallString} {p}, p ∈ CallString.truncateAt f cs → p ∈ cs
  | p :: rest, q, hmem => by
      unfold CallString.truncateAt at hmem
      split at hmem
      case isTrue h =>
          rw [List.mem_singleton] at hmem
          exact hmem ▸ List.mem_cons_self
      case isFalse h =>
          rcases List.mem_cons.mp hmem with rfl | htl
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem p (CallString.mem_truncateAt htl)

/-- Truncation preserves well-formedness: it only ever drops elements, never
    duplicates one that survives. -/
theorem CallString.truncateAt_wf {f : Fid} :
    ∀ {cs : CallString}, CallString.WF cs → CallString.WF (CallString.truncateAt f cs)
  | [],        _ => List.nodup_nil
  | p :: rest, h => by
      unfold CallString.truncateAt
      have hcons : CallString.fids (p :: rest) = p.2 :: CallString.fids rest := rfl
      have hndcons : (p.2 :: CallString.fids rest).Nodup := hcons ▸ h
      have hndrest : CallString.WF rest := (List.nodup_cons.mp hndcons).2
      have hp2notin' : p.2 ∉ CallString.fids rest := (List.nodup_cons.mp hndcons).1
      split
      case isTrue _ => exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
      case isFalse hne =>
          have hIH := CallString.truncateAt_wf (f := f) hndrest
          have hnotin : p.2 ∉ CallString.fids (CallString.truncateAt f rest) := by
            intro hmem
            obtain ⟨q, hq, hqeq⟩ := List.mem_map.mp hmem
            have hqrest : q ∈ rest := CallString.mem_truncateAt hq
            have : p.2 ∈ CallString.fids rest := hqeq ▸ List.mem_map_of_mem hqrest
            exact hp2notin' this
          show (p.2 :: CallString.fids (CallString.truncateAt f rest)).Nodup
          exact List.nodup_cons.mpr ⟨hnotin, hIH⟩

/-- `targetCallString cs site f`: the call string in effect at the callee's
    entry when calling `f` from `site` while the current path is `cs`
    (Decision 5). If `f` is already open (a recursive/mutually-recursive
    call), reuse its first occurrence's instantiation by truncating; otherwise
    extend with the new site. -/
def targetCallString (cs : CallString) (site : Idx) (f : Fid) : CallString :=
  if f ∈ cs.fids then
    CallString.truncateAt f cs
  else
    cs ++ [(site, f)]

theorem targetCallString_wf {cs : CallString} (h : cs.WF) (site : Idx) (f : Fid) :
    (targetCallString cs site f).WF := by
  unfold targetCallString
  split
  case isTrue hmem => exact CallString.truncateAt_wf h
  case isFalse hnmem =>
    have heq : (cs ++ [(site, f)]).fids = cs.fids ++ [f] := by
      simp [CallString.fids, List.map_append]
    show (cs ++ [(site, f)]).fids.Nodup
    rw [heq, List.nodup_append]
    refine ⟨h, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact fun he => hnmem (he ▸ ha)

/-! ### Finiteness of call strings

A well-formed call string never repeats a function identifier, so once every
`Fid` that can occur has been drawn from some fixed finite list, the call
string's own length cannot exceed that list's length — this is the pigeonhole
argument `DESIGN_AND_PLAN.md` §4.2 sketches informally ("no `Fid` can repeat
within one call-string ... so every call-string has length at most
`|dom(Γ)|`"). -/

/-- Delete the first occurrence of `a` from `l`, if any. A hand-rolled helper
    used only for the pigeonhole argument below, so that its properties can be
    proved by direct structural induction rather than chasing the exact shape
    of core's `List.eraseP` lemmas. -/
private def removeOne {α} [DecidableEq α] (a : α) : List α → List α
  | []      => []
  | b :: t  => if b = a then t else b :: removeOne a t

private theorem removeOne_length {α} [DecidableEq α] {a : α} :
    ∀ {l : List α}, a ∈ l → (removeOne a l).length + 1 = l.length
  | b :: t, hmem => by
      unfold removeOne
      by_cases hba : b = a
      · simp [hba]
      · rcases List.mem_cons.mp hmem with rfl | htl
        · exact absurd rfl hba
        · simp only [if_neg hba, List.length_cons]
          have := removeOne_length (a := a) (l := t) htl
          omega

private theorem removeOne_mem {α} [DecidableEq α] {a x : α} (hne : x ≠ a) :
    ∀ {l : List α}, x ∈ removeOne a l → x ∈ l
  | b :: t, hmem => by
      unfold removeOne at hmem
      by_cases hba : b = a
      · simp only [hba] at hmem
        exact List.mem_cons_of_mem b hmem
      · simp only [if_neg hba] at hmem
        rcases List.mem_cons.mp hmem with rfl | htl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem b (removeOne_mem hne htl)

/-- The converse direction: an element surviving `a`'s removal is exactly one
    that was present and isn't `a` itself. -/
private theorem mem_removeOne_of_ne {α} [DecidableEq α] {a x : α} (hxa : x ≠ a) :
    ∀ {l : List α}, x ∈ l → x ∈ removeOne a l
  | b :: t, hmem => by
      unfold removeOne
      by_cases hba : b = a
      · rcases List.mem_cons.mp hmem with rfl | htl
        · exact absurd hba (hba ▸ hxa)
        · simpa [hba] using htl
      · rcases List.mem_cons.mp hmem with rfl | htl
        · simp [hba]
        · simp only [if_neg hba]
          exact List.mem_cons_of_mem b (mem_removeOne_of_ne hxa htl)

theorem List.Nodup.length_le_of_subset {α} [DecidableEq α] :
    ∀ {l fids : List α}, l.Nodup → (∀ a ∈ l, a ∈ fids) → l.length ≤ fids.length
  | [],      fids, _,   _    => Nat.zero_le _
  | a :: t,  fids, hnd, hsub => by
      have ha : a ∈ fids := hsub a (List.mem_cons_self)
      have hat : a ∉ t := (List.nodup_cons.mp hnd).1
      have hndt : t.Nodup := (List.nodup_cons.mp hnd).2
      have hsubt : ∀ x ∈ t, x ∈ removeOne a fids := by
        intro x hx
        have hxa : x ≠ a := fun he => hat (he ▸ hx)
        exact mem_removeOne_of_ne hxa (hsub x (List.mem_cons_of_mem a hx))
      have hIH := List.Nodup.length_le_of_subset hndt hsubt
      have hlen := removeOne_length (a := a) (l := fids) ha
      simp only [List.length_cons]
      omega

/-- The bound stated in `DESIGN_AND_PLAN.md` §4.2: a well-formed call string's
    length cannot exceed the number of function identifiers it draws from. -/
theorem CallString.length_le {cs : CallString} (h : cs.WF) {fids : List Fid}
    (hsub : ∀ f ∈ cs.fids, f ∈ fids) : cs.length ≤ fids.length := by
  have := List.Nodup.length_le_of_subset (l := cs.fids) h hsub
  simpa [CallString.fids] using this

/-! ## Automaton states (§4.2)

Every construct needing a unique per-occurrence automaton state gets one
constructor here, indexed by the call string it occurs under (and, for
everything except `entry`, its own site index — `entry`'s site is already the
last element of its own call string, when nonempty). -/

inductive AState where
  /-- `lookupS`/`lookupD`/`updateS`/`updateD`: the state reached right after
      performing that one action. -/
  | action    (cs : CallString) (site : Idx)
  /-- The continuation of a call site: always fresh per call site (never
      shared, recursive or not — Decision 5/7). -/
  | cont      (cs : CallString) (site : Idx)
  /-- A function body's start. Shared across every call site whose call
      string, after `targetCallString`, truncates to `cs` (Decision 5). -/
  | entry     (cs : CallString)
  /-- `ifElse`'s "then" branch entry. -/
  | ifThen    (cs : CallString) (site : Idx)
  /-- `ifElse`'s "else" branch entry. -/
  | ifElseB   (cs : CallString) (site : Idx)
  /-- `ifElse`'s join point. Always exists as a state; whether anything
      reaches it (at least one branch continues) is a fact about which edges
      happen to target it, not part of the state's own definition
      (Decision 9). -/
  | ifEnd     (cs : CallString) (site : Idx)
  /-- `whileDo`'s body entry. -/
  | whileIn   (cs : CallString) (site : Idx)
  /-- `whileDo`'s exit (loop not taken / loop finished). -/
  | whileOut  (cs : CallString) (site : Idx)
  deriving DecidableEq

/-- Well-formedness of a state relative to the finite sets of call/site
    indices and function identifiers actually occurring in a fixed program:
    every call string mentioned is well formed and drawn from those sets. -/
def AState.WF (idxs : List Idx) (fids : List Fid) : AState → Prop
  | .action cs site   => cs.WF ∧ (∀ f ∈ cs.fids, f ∈ fids) ∧ site ∈ idxs
  | .cont cs site      => cs.WF ∧ (∀ f ∈ cs.fids, f ∈ fids) ∧ site ∈ idxs
  | .entry cs          => cs.WF ∧ (∀ f ∈ cs.fids, f ∈ fids)
  | .ifThen cs site    => cs.WF ∧ (∀ f ∈ cs.fids, f ∈ fids) ∧ site ∈ idxs
  | .ifElseB cs site   => cs.WF ∧ (∀ f ∈ cs.fids, f ∈ fids) ∧ site ∈ idxs
  | .ifEnd cs site     => cs.WF ∧ (∀ f ∈ cs.fids, f ∈ fids) ∧ site ∈ idxs
  | .whileIn cs site   => cs.WF ∧ (∀ f ∈ cs.fids, f ∈ fids) ∧ site ∈ idxs
  | .whileOut cs site  => cs.WF ∧ (∀ f ∈ cs.fids, f ∈ fids) ∧ site ∈ idxs

end CoreJS
