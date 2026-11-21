import Ochr.Meaning.Steps.FormErase

/-!
# What a step's hypotheses read of the checker's state (lead7)

The checker's state carries much besides what the simulation speaks of: the flags and one-shot
readings `eval` hands down (`curTail`, `tailDecl`, `headEval`, `wantTy`, …), the log, the editor's
locations. A step's hypotheses read only the *kernel* (`Kern`): Ω, Σ, the declarations, the label
and unknown counters, Δ and its frozen readings, the records, the goal and the reading mode. So the
bookkeeping a checker function does around a sub-run changes nothing a step assumes (`Pre.of_kern`,
`Rel.of_kern`, `DecTab.of_kern`), and the facts about the checker's runs a step uses
(`Steps/FormMachine.lean`) need say no more of the intermediate states than their kernel.

`Mode`: the flags under which a read moves as the strict run's does (not inside `clone`/`peek`, not
in place, not inside an erased term) and the pre-pass classifies the term (not a call's head).
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- Two checker states with the same kernel (Ω up to its temporaries' stored types, `Env.erase`). -/
structure Kern (st st' : MState) : Prop where
  env : st.env.erase = st'.env.erase
  globals : st.globals = st'.globals
  inds : st.inds = st'.inds
  nextLoan : st.nextLoan = st'.nextLoan
  nextAbs : st.nextAbs = st'.nextAbs
  absTy : st.absTy = st'.absTy
  absDecl : st.absDecl = st'.absDecl
  refs : st.refs = st'.refs
  etaRefs : st.etaRefs = st'.etaRefs
  goal : st.goal = st'.goal
  neutrals : st.neutrals = st'.neutrals
  liveScope : st.liveScope = st'.liveScope

theorem Kern.rfl' (st : MState) : Kern st st := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Kern.symm {st st' : MState} (h : Kern st st') : Kern st' st :=
  ⟨h.env.symm, h.globals.symm, h.inds.symm, h.nextLoan.symm, h.nextAbs.symm, h.absTy.symm, h.absDecl.symm,
    h.refs.symm, h.etaRefs.symm, h.goal.symm, h.neutrals.symm, h.liveScope.symm⟩

theorem Kern.trans {a b c : MState} (h₁ : Kern a b) (h₂ : Kern b c) : Kern a c :=
  ⟨h₁.env.trans h₂.env, h₁.globals.trans h₂.globals, h₁.inds.trans h₂.inds, h₁.nextLoan.trans h₂.nextLoan,
    h₁.nextAbs.trans h₂.nextAbs, h₁.absTy.trans h₂.absTy, h₁.absDecl.trans h₂.absDecl, h₁.refs.trans h₂.refs,
    h₁.etaRefs.trans h₂.etaRefs, h₁.goal.trans h₂.goal, h₁.neutrals.trans h₂.neutrals, h₁.liveScope.trans h₂.liveScope⟩

/-- The value in flight counted: two states with one kernel have one kernel with it counted. -/
theorem Kern.withTempT {st st' : MState} (h : Kern st st') (v : Value) (T? : Option Value) :
    Kern (st.withTempT v T?) (st'.withTempT v T?) :=
  ⟨by rw [erase_withTempT, erase_withTempT, h.env], h.globals, h.inds, h.nextLoan, h.nextAbs, h.absTy, h.absDecl, h.refs,
    h.etaRefs, h.goal, h.neutrals, h.liveScope⟩

theorem Kern.norm {st st' : MState} (h : Kern st st') : st.norm = st'.norm := by
  simp only [MState.norm, h.env, h.globals, h.inds, h.nextLoan, h.nextAbs, h.absTy, h.absDecl, h.refs, h.etaRefs,
    h.goal, h.neutrals, h.liveScope]

/-- **A step's hypotheses read only the kernel.** -/
theorem Pre.of_kern {K : RunCtx} {ρ : Assignment} {st st' : MState} (h : Kern st st') (hp : Pre K ρ st) :
    Pre K ρ st' := by
  obtain ⟨c, i, a⟩ := hp
  rw [h.norm] at c i a
  exact ⟨c, i, a⟩

/-- `Rel` reads the checker's state through Ω and the label counter only. -/
theorem _root_.Ochr.Meaning.Steps.Rel.of_env {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st st' : MState} {s : SState}
    (he : st'.env = st.env) (hl : st'.nextLoan = st.nextLoan) (hr : Rel K ρ φ π st s) : Rel K ρ φ π st' s := by
  have e1 : SM' K ρ st' = SM' K ρ st := by simp only [SM', MState.sstate, he, hl]
  have e2 : MState.mean K.dm K.M K.Γ ρ st' = MState.mean K.dm K.M K.Γ ρ st := by simp only [MState.mean, he]
  have e3 : ∀ l, st'.Occurs l ↔ st.Occurs l := fun l => by unfold MState.Occurs; rw [he]
  refine ⟨?_, ?_, ?_, ?_, ?_, hr.holders, hr.records, hr.uniq⟩
  · rw [e1]; exact hr.skel
  · intro l hl' ho; rw [hl] at hl'; exact hr.fresh l hl' ((e3 l).mp ho)
  · rw [e2]; exact hr.sim
  · rw [he]; exact hr.inj
  · rw [he]; exact hr.sites

theorem _root_.Ochr.Meaning.Steps.Rel.of_kern {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st st' : MState} {s : SState}
    (h : Kern st st') (hr : Rel K ρ φ π st s) : Rel K ρ φ π st' s := by
  have h1 : Rel K ρ φ π { st with env := st.env.erase } s := rel_erase.mpr hr
  have h2 : Rel K ρ φ π { st' with env := st'.env.erase } s :=
    h1.of_env (by simp only [h.env]) (by simp only [h.nextLoan])
  exact rel_erase.mp h2

end Ochr.Meaning.Steps.Form

namespace Ochr.Meaning.Steps.Form
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- The decisions stay the checker's across a change of what no decision reads (`DecAligned.of_core`
without the block's captures). -/
theorem DecTab.of_core {D : Decisions} {st st' : MState} (hd : DecTab D st) (h : DecCore st' st)
    (hl : ∀ i, DecideScope.liveVal st' i = DecideScope.liveVal st i) : DecTab D st' where
  flags fuel sc t fl b st₁ hr := by
    obtain ⟨_, hr'⟩ := runs_envRel (DecideScope.sim_bind (DecideScope.sim_withLive _
      ((DecideScope.decideSim fuel).2.2.2.2.2.2.2.2.1 _ _ _ _)) fun d =>
        DecideScope.sim_bind (DecideScope.sim_preFlags t d) fun _ => DecideScope.sim_pure _)
      (envRel_scope_of_core h sc) hr
    exact hd.flags fuel sc t fl b _ hr'
  placeDecl fuel sc p d b st₁ hr := by
    obtain ⟨_, hr'⟩ := runs_envRel (DecideScope.sim_withLive _ ((DecideScope.decideSim fuel).1 _ _))
      (envRel_scope_of_core h sc) hr
    exact hd.placeDecl fuel sc p d b _ hr'
  declOf fuel sc t d b st₁ hr := by
    obtain ⟨_, hr'⟩ := runs_envRel (DecideScope.sim_withLive _ ((DecideScope.decideSim fuel).2.2.2.2.2.2.2.2.1 _ _ _ _))
      (envRel_scope_of_core h sc) hr
    exact hd.declOf fuel sc t d b _ hr'
  copy fuel r c b st₁ hr := by
    obtain ⟨_, hr'⟩ := runs_envRel ((DecideScope.decideSim fuel).2.2.2.1 _) (envRel_of_core h hl) hr
    exact hd.copy fuel r c b _ hr'
  piSort fuel sc t l b st₁ hr := by
    obtain ⟨_, hr'⟩ := runs_envRel (DecideScope.sim_withLive _ ((DecideScope.decideSim fuel).2.2.2.2.2.2.1 _))
      (envRel_scope_of_core h sc) hr
    exact hd.piSort fuel sc t l b _ hr'
  joinMoves fuel sc entry t ms b st₁ hr := by
    obtain ⟨_, hr'⟩ := runs_envRel (jdMoves_sim fuel t entry) (envRel_scope_of_core h sc) hr
    exact hd.joinMoves fuel sc entry t ms b _ hr'
  rePointed fuel sc t ts b st₁ hr := by
    obtain ⟨_, hr'⟩ := runs_envRel (typeState_sim fuel t) (envRel_scope_of_core h sc) hr
    exact hd.rePointed fuel sc t ts b _ hr'
  typeDecl fuel sc T d b st₁ hr := by
    obtain ⟨_, hr'⟩ := runs_envRel (DecideScope.sim_withLive _ ((DecideScope.decideSim fuel).2.2.2.2.2.2.2.2.2.1 _ _ _ _ _ _))
      (envRel_scope_of_core h sc) hr
    exact hd.typeDecl fuel sc T d b _ hr'

/-- **The decisions read only the kernel.** -/
theorem DecTab.of_kern {D : Decisions} {st st' : MState} (h : Kern st st') (hd : DecTab D st) : DecTab D st' :=
  DecTab.of_core hd ⟨h.globals.symm, h.inds.symm, h.absDecl.symm, h.liveScope.symm⟩ fun i => by
    have hs : st'.env.size = st.env.size := by rw [← Env.erase_size, ← Env.erase_size st.env, h.env]
    have hb : ∀ f : Nat, ((st'.env : Env)[f]!).binds = ((st.env : Env)[f]!).binds := fun f => by
      rw [← binds_erase, ← binds_erase st.env, h.env]
    simp only [DecideScope.liveVal, hs, hb]

end Ochr.Meaning.Steps.Form
