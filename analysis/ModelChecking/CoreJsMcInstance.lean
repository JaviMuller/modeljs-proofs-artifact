/-
  # Core JavaScript — Model checking: the program automaton as an instance

  The automaton of `ProgramAutomaton/`, labeled by an analysis result `L`, as
  a trace system (`autTSys`) and an abstraction (`autAbs`) in the sense of
  `CoreJsMcInterface.lean`, and the program's runs covered by it
  (`aut_covers`, from `sound_top`):

  * states are the automaton's states, starting at the top-level entry; final
    states are those where the top-level program exits or returns (the end
    states of `SoundRun`); edges are the graph's edges defined under `L`,
    silent when their action is `epsilon`;
  * abstract values are `Option ALoc`: an abstract location, or `none` for a
    location `α` does not map (every predicate is false there, concretely and
    abstractly);
  * the facts are the join of the final abstract configurations
    (`topFacts`), so one set of facts serves every walk;
  * matching reads the label's location sets; `may` reads the facts, with
    `ac` covering dependence on an `ac` location as `Obs.ofRun` does; `must`,
    `mustA` and `inhab` are never true: the analysis is a may-analysis, so
    `except` components never exclude anything here.  (Must-matching on
    function identity would need `α` to map nothing but `litLoc (.fid f)` to
    `litLocA (.fid f)`, which `SoundRun` does not state: `AllocSafe` says
    which locations `α` maps, not to what.)

  `aut_asat`: every run of the program from its initial configuration that
  matches the query satisfies the abstract semantics of the query's model
  over the automaton.  The algorithm itself runs on a finite form of the
  automaton (`CoreJsMcFinite.lean`).

  Plain Lean 4 — no Mathlib required.
-/

import ModelChecking.CoreJsMcAlgorithm
import ProgramAutomaton.CoreJsAutomatonSoundness

namespace CoreJS

/-- Covering survives replacing the trace system by one with (at least) the
    same complete walks. -/
theorem Covers.of_walks {A V Φ : Type} {S₁ S₂ : TSys A} {𝔄 : Abs A V Φ} {φ : Φ}
    {R : Exec → Prop}
    (hw : ∀ T s, S₁.Walk S₁.init T s → S₁.final s → ∃ s', S₂.Walk S₂.init T s' ∧ S₂.final s')
    (h : Covers S₁ 𝔄 φ R) : Covers S₂ 𝔄 φ R := by
  intro e he
  obtain ⟨T, s, α, hwalk, hs, hrec⟩ := h e he
  obtain ⟨s', hw', hs'⟩ := hw T s hwalk hs
  exact ⟨T, s', α, hw', hs', hrec⟩

section instance_

variable [Abstract] (Γ : Env) (s₀ : Stmt) (L : Labeling)

/-! ## The trace system -/

/-- `c` is the final abstract configuration of the top-level program at `x`. -/
def TopFinal (x : AState) (c : AConf) : Prop :=
  (∃ xp, AExit Γ [] (.entry []) id s₀ x xp ∧ c = xp (L x)) ∨
  (∃ rp e, ARet Γ [] (.entry []) id s₀ x rp e ∧ c = rp (L x))

/-- The labeled automaton as a trace system. -/
def autTSys : TSys AAct where
  St    := AState
  init  := .entry []
  final x := ∃ c, TopFinal Γ s₀ L x c
  edge a l b := ∃ C ℓ act, AGraph Γ s₀ a b C ℓ ∧ ℓ L = some act ∧ act.visible = l.toList

theorem AWalk.toWalk {Γ : Env} {s₀ : Stmt} {L : Labeling} {a c : AState} {acts : List AAct}
    (h : AWalk Γ s₀ L a c acts) : (autTSys Γ s₀ L).Walk a acts c := by
  induction h with
  | nil => exact .nil
  | @step a b c C ℓ act acts he hℓ _ ih =>
    cases act with
    | epsilon => exact .silent ⟨C, ℓ, .epsilon, he, hℓ, rfl⟩ ih
    | lookup => exact .vis ⟨C, ℓ, _, he, hℓ, rfl⟩ ih
    | update => exact .vis ⟨C, ℓ, _, he, hℓ, rfl⟩ ih
    | call => exact .vis ⟨C, ℓ, _, he, hℓ, rfl⟩ ih
    | ret => exact .vis ⟨C, ℓ, _, he, hℓ, rfl⟩ ih

/-- The join of the final abstract configurations. -/
def topFacts : AConf where
  heap := { obj := fun _ _ _ => False,
            val := fun al => .vals fun v => ∃ x c, TopFinal Γ s₀ L x c ∧ (c.heap.val al).Mem v }
  sto  := ASto.bot
  reg  := { dep := fun a₁ a₂ => ∃ x c, TopFinal Γ s₀ L x c ∧ c.reg.dep a₁ a₂,
            ac  := fun a => ∃ x c, TopFinal Γ s₀ L x c ∧ c.reg.ac a,
            sk  := fun a => ∃ x c, TopFinal Γ s₀ L x c ∧ c.reg.sk a }

/-! ## The abstraction -/

/-- The value of `x` is an abstract location in `L`. -/
def InA (ξ : MVar → Option ALoc) (x : MVar) (L : ALocSet) : Prop := ∃ al, ξ x = some al ∧ L al

def InAs (ξ : MVar → Option ALoc) : List MVar → List ALocSet → Prop
  | [],      []      => True
  | x :: xs, L :: Ls => InA ξ x L ∧ InAs ξ xs Ls
  | _,       _       => False

/-- Matching a query action against an abstract action. -/
def AMatch (ξ : MVar → Option ALoc) : QAct MVar → AAct → Prop
  | .lookup x₁ x₂ x₃, .lookup L₁ L₂ L₃ => InA ξ x₁ L₁ ∧ InA ξ x₂ L₂ ∧ InA ξ x₃ L₃
  | .update x₁ x₂ x₃, .update L₁ L₂ L₃ => InA ξ x₁ L₁ ∧ InA ξ x₂ L₂ ∧ InA ξ x₃ L₃
  | .call xf xs,      .call lf Ls      => ξ xf = some lf ∧ InAs ξ xs Ls
  | .retn xf x,       .ret lf L        => ξ xf = some lf ∧ InA ξ x L
  | _,                _                => False

/-- A predicate may hold of the facts. -/
def PMay (φ : AConf) (ξ : MVar → Option ALoc) : Pred MVar → Prop
  | .sk x      => ∃ al, ξ x = some al ∧ φ.reg.sk al
  | .ac x      => ∃ al, ξ x = some al ∧ (φ.reg.ac al ∨ ∃ al', φ.reg.ac al' ∧ φ.reg.dep al al')
  | .dep x₁ x₂ => ∃ a₁ a₂, ξ x₁ = some a₁ ∧ ξ x₂ = some a₂ ∧ φ.reg.dep a₁ a₂
  | .sv x₁ x₂  => ∃ a₁ a₂ v, ξ x₁ = some a₁ ∧ ξ x₂ = some a₂ ∧
      (φ.heap.val a₁).Mem v ∧ (φ.heap.val a₂).Mem v
  | .hv x c    => ∃ al, ξ x = some al ∧ (φ.heap.val al).Mem c

/-- The concrete observation is abstracted by the facts. -/
def FactsAlpha (α : AlphaFn) (σ : Obs) (φ : AConf) : Prop :=
  (∀ l v, σ.val l = some v → ∃ al, α l = some al ∧ (φ.heap.val al).Mem v) ∧
  (∀ l₁ l₂, σ.dep l₁ l₂ → ∃ a₁ a₂, α l₁ = some a₁ ∧ α l₂ = some a₂ ∧ φ.reg.dep a₁ a₂) ∧
  (∀ l, σ.ac l → ∃ al, α l = some al ∧ (φ.reg.ac al ∨ ∃ al', φ.reg.ac al' ∧ φ.reg.dep al al')) ∧
  (∀ l, σ.sk l → ∃ al, α l = some al ∧ φ.reg.sk al)

open Classical in
/-- The program automaton's abstraction. -/
noncomputable def autAbs : Abs AAct (Option ALoc) AConf where
  act    := Act.Alpha
  facts  := FactsAlpha
  matchA ξ b B := decide (AMatch ξ b B)
  may φ ξ p := decide (PMay φ ξ p)
  must _ _ _ := false
  mustA _ _ _ := false
  inhab _ _ := false

omit [Abstract] in
theorem InAs.of_locsAlpha {α : AlphaFn} {ξ : MEnv} :
    ∀ {xs : List MVar} {Ls : List ALocSet}, LocsAlpha α (xs.map ξ) Ls → InAs (α ∘ ξ) xs Ls
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨h.1, InAs.of_locsAlpha h.2⟩

omit [Abstract] in
theorem autAbs_sound : autAbs.Sound where
  matchA α ξ a c B hB hc := by
    subst hc
    simp only [autAbs, decide_eq_true_eq]
    cases a <;> cases B <;> simp only [QAct.inst] at hB <;>
      first | exact hB.elim | skip
    · exact hB
    · exact hB
    · exact ⟨hB.1, InAs.of_locsAlpha hB.2⟩
    · exact hB
  may α σ φ ξ p hf hp := by
    obtain ⟨hval, hdep, hac, hsk⟩ := hf
    simp only [autAbs, decide_eq_true_eq]
    cases p with
    | sk x => exact hsk _ hp
    | ac x => exact hac _ hp
    | dep x₁ x₂ => obtain ⟨a₁, a₂, h₁, h₂, h⟩ := hdep _ _ hp; exact ⟨a₁, a₂, h₁, h₂, h⟩
    | sv x₁ x₂ =>
      obtain ⟨v, h₁, h₂⟩ := hp
      obtain ⟨a₁, ha₁, hv₁⟩ := hval _ _ h₁
      obtain ⟨a₂, ha₂, hv₂⟩ := hval _ _ h₂
      exact ⟨a₁, a₂, v, ha₁, ha₂, hv₁, hv₂⟩
    | hv x c => exact hval _ _ hp
  must _ _ _ _ _ _ h := by simp [autAbs] at h
  may_congr φ ξ ξ' p h := by
    simp only [autAbs]
    congr 1
    cases p <;> simp only [Pred.vars, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at h <;> simp only [PMay, h]
  must_congr _ _ _ _ _ := rfl
  mustA _ _ _ _ _ _ h := by simp [autAbs] at h
  mustA_congr _ _ _ _ _ := rfl
  inhab _ _ _ _ _ h := by simp [autAbs] at h

/-! ## Coverage of the program's runs -/

omit [Abstract] in
theorem pointwise_of_actsAlpha {α : AlphaFn} :
    ∀ {as : List Act} {As : List AAct}, ActsAlpha α as As → Pointwise (Act.Alpha α) as As
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨h.1, pointwise_of_actsAlpha h.2⟩

theorem factsAlpha_of {α : AlphaFn} {r : Res} {c : AConf} {x : AState}
    (hfin : TopFinal Γ s₀ L x c) (h : AConf.Alpha α ⟨r.heap, r.sto, r.reg⟩ c) :
    FactsAlpha α (Exec.ofRes r).obs (topFacts Γ s₀ L) := by
  obtain ⟨⟨_, hval⟩, _, hdep, hac, hsk⟩ := h
  refine ⟨fun l v hv => ?_, fun l₁ l₂ hd => ?_, fun l hl => ?_, fun l hl => ?_⟩
  · obtain ⟨al, hal, hm⟩ := hval l v hv
    exact ⟨al, hal, ⟨x, c, hfin, hm⟩⟩
  · obtain ⟨a₁, a₂, h₁, h₂, hd'⟩ := hdep l₁ l₂ hd
    exact ⟨a₁, a₂, h₁, h₂, x, c, hfin, hd'⟩
  · rcases hl with hl | ⟨l', hl', hd⟩
    · obtain ⟨al, hal, hm⟩ := hac l hl
      exact ⟨al, hal, Or.inl ⟨x, c, hfin, hm⟩⟩
    · obtain ⟨a₁, a₂, h₁, h₂, hd'⟩ := hdep l l' hd
      obtain ⟨al', hal', hm⟩ := hac l' hl'
      rw [h₂] at hal'; cases hal'
      exact ⟨a₁, h₁, Or.inr ⟨a₂, ⟨x, c, hfin, hm⟩, x, c, hfin, hd'⟩⟩
  · obtain ⟨al, hal, hm⟩ := hsk l hl
    exact ⟨al, hal, x, c, hfin, hm⟩

/-- Every run of the program from its initial configuration is covered by the
    automaton labeled by an analysis result. -/
theorem aut_covers [Concrete] (cspec : ConcreteSpec) (xspec : CrossSpec)
    (hres : AnalysisResult Γ s₀ L) :
    Covers (autTSys Γ s₀ L) autAbs (topFacts Γ s₀ L)
      (fun e => ∃ fs r, BigStep Γ (Conf.init Γ fs s₀) s₀ r ∧ e = Exec.ofRes r) := by
  rintro e ⟨fs, r, hrun, rfl⟩
  rcases sound_top cspec xspec hres hrun with
    ⟨x, xp, hex, _, α, _, _, hconf, acts, hwalk, htrc⟩ |
    ⟨x, rp, e, _, hret, _, α, _, _, hconf, _, acts, hwalk, htrc⟩
  · have hfin : TopFinal Γ s₀ L x (xp (L x)) := Or.inl ⟨xp, hex, rfl⟩
    exact ⟨acts, x, α, hwalk.toWalk, ⟨_, hfin⟩, pointwise_of_actsAlpha htrc,
      factsAlpha_of Γ s₀ L hfin hconf⟩
  · have hfin : TopFinal Γ s₀ L x (rp (L x)) := Or.inr ⟨rp, e, hret, rfl⟩
    exact ⟨acts, x, α, hwalk.toWalk, ⟨_, hfin⟩, pointwise_of_actsAlpha htrc,
      factsAlpha_of Γ s₀ L hfin hconf⟩

/-- **Completeness for the program automaton.** Every run of the program
    matching the query satisfies the abstract semantics of the query's model
    over the automaton labeled by any analysis result. -/
theorem aut_asat [Concrete] (cspec : ConcreteSpec) (xspec : CrossSpec)
    (hres : AnalysisResult Γ s₀ L) {Δ : QProg} {q : Query} (hwf : QProg.WF (q :: Δ))
    {fs : List Fid} {r : Res} (hrun : BigStep Γ (Conf.init Γ fs s₀) s₀ r) {ls : List Loc}
    (hlen : ls.length = q.params.length) (hm : Exec.Matches (q :: Δ) (Exec.ofRes r) q.name ls) :
    (q.toQModel Δ).ASat (autTSys Γ s₀ L) autAbs (topFacts Γ s₀ L) :=
  QModel.asat_of_matches autAbs_sound (aut_covers Γ s₀ L cspec xspec hres) hwf
    ⟨fs, r, hrun, rfl⟩ hlen hm

end instance_

end CoreJS
