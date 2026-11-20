import Ochr.Meaning.Steps.IH

/-!
# The aligned decisions equal the checker's (milestone 3; docs/18 "Decisions, by kind",
*aligned*)

`Decisions` (`Places.lean`) is what the reference run reads from syntax. "Aligned" is discharged
by showing each field equals the checker's `Decide` function, run from a state holding the same
declarations: whether a term is a statement and a proof (`preFlags`), a place's and a term's
declared-type reading (`placeDecl`, `declOf`), copy-ness (`declCopy`), a Π-term's sort
(`sortOf`/`piSort`), and D84's join set (`jdMoves`, on branch `d84`; stated here against the
field only, to be tied to `Decide.jdMoves` when it lands). The instance itself,
`Decisions` built from `Decide.lean`, is `DecisionsInst.lean` (implementer prog-decisions);
these statements are about that instance.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The scope of readings the checker uses at `st`'s top frame is `scopeOf` of its semantic
state (each binding's `decl`, innermost first). -/
theorem scopeOf_sstate (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : scopeOf_sstate_stmt K ρ φ (fuel + 1) := by
  sorry

/-- The checker's state and its scope state at the top frame's readings agree on what decisions
read, both ways. -/
theorem envRel_scopeState' (st : MState) : DecideScope.EnvRel st (scopeState st (DecideScope.topReadings st)) :=
  (DecideScope.envRel_scopeState st).symm

/-- A decision's live call at `st` runs alike at the top frame's scope state. -/
theorem runs_top {α : Type} {x : M α} (hx : DecideScope.Sim DecideScope.EnvRel x) {st st' : MState} {b : Nat} {a : α}
    (h : Runs x st b a st') : ∃ st'', Runs x (scopeState st (DecideScope.topReadings st)) b a st'' :=
  runs_envRel hx (envRel_scopeState' st) h

/-- `Decisions.flags` is `Decide.preFlags` where the latter answers: `CtxOk.dec` at the top frame. -/
theorem flags_aligned (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : flags_aligned_stmt K ρ φ (fuel + 1) := by
  intro st st' t fl _ hctx bh h
  rw [(ih K ρ φ).scopeOf_sstate st]
  obtain ⟨_, h'⟩ := runs_top (DecideScope.sim_bind (DecideScope.sim_withLive _
    ((DecideScope.decideSim (fuel + 1)).2.2.2.2.2.2.2.2.1 _ _ _ _)) fun d =>
      DecideScope.sim_bind (DecideScope.sim_preFlags t d) fun _ => DecideScope.sim_pure _) h
  exact hctx.dec.flags _ _ t fl bh _ h'

/-- `Decisions.placeDecl` is `Decide.placeDecl`. -/
theorem placeDecl_aligned (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : placeDecl_aligned_stmt K ρ φ (fuel + 1) := by
  intro st st' p d _ hctx bh h
  rw [(ih K ρ φ).scopeOf_sstate st]
  obtain ⟨_, h'⟩ := runs_top (DecideScope.sim_withLive _ ((DecideScope.decideSim (fuel + 1)).1 _ _)) h
  exact hctx.dec.placeDecl _ _ p d bh _ h'

/-- `Decisions.declOf` is `Decide.declOf` (unchecked mode). -/
theorem declOf_aligned (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : declOf_aligned_stmt K ρ φ (fuel + 1) := by
  intro st st' t d _ hctx bh h
  rw [(ih K ρ φ).scopeOf_sstate st]
  obtain ⟨_, h'⟩ := runs_top (DecideScope.sim_withLive _
    ((DecideScope.decideSim (fuel + 1)).2.2.2.2.2.2.2.2.1 _ _ _ _)) h
  exact hctx.dec.declOf _ _ t d bh _ h'

/-- `Decisions.copy` is `Decide.declCopy`. -/
theorem copy_aligned (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : copy_aligned_stmt K ρ φ (fuel + 1) := by
  intro st st' d b _ hctx bh h
  exact hctx.dec.copy _ d b bh _ h

/-- `Decisions.piSort` is `Decide.sortOf` of the Π-type value (D55: declared sort = computed). -/
theorem piSort_aligned' (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : piSort_aligned'_stmt K ρ φ (fuel + 1) := by
  intro st st' hs ds c l _ hctx bh h
  rw [(ih K ρ φ).scopeOf_sstate st]
  obtain ⟨_, h'⟩ := runs_top (DecideScope.sim_withLive _ ((DecideScope.decideSim (fuel + 1)).2.2.2.2.2.2.1 _)) h
  exact hctx.dec.piSort _ _ _ l bh _ h'

/-- D84 [Join]: `Decisions.joinMoves` is `Decide.jdMoves` as `Machine.staticJoin` calls it (the
places already `⊥` at the match as its `entry`). -/
theorem joinMoves_aligned (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : joinMoves_aligned_stmt K ρ φ (fuel + 1) := by
  intro st st' entry ms t _ hctx bh h
  rw [(ih K ρ φ).scopeOf_sstate st]
  obtain ⟨_, h'⟩ := runs_top (jdMoves_sim _ t entry) h
  exact hctx.dec.joinMoves _ _ entry t ms bh _ h'

/-- D84 [Id-typestate]/[Obs-ref]: `Decisions.rePointed` is the `repointed` component of
`Decide.typeState`, as `Machine.idType` reads it. -/
theorem rePointed_aligned (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : rePointed_aligned_stmt K ρ φ (fuel + 1) := by
  intro st st' t ts _ hctx bh h
  rw [(ih K ρ φ).scopeOf_sstate st]
  obtain ⟨_, h'⟩ := runs_top (typeState_sim _ t) h
  exact hctx.dec.rePointed _ _ t ts bh _ h'

/-- `Decisions.typeDecl` is `Decide.typeDecl`, the reading of a type term (D19, R3). -/
theorem typeDecl_aligned (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : typeDecl_aligned_stmt K ρ φ (fuel + 1) := by
  intro st st' T d _ hctx bh h
  rw [(ih K ρ φ).scopeOf_sstate st]
  obtain ⟨_, h'⟩ := runs_top (DecideScope.sim_withLive _
    ((DecideScope.decideSim (fuel + 1)).2.2.2.2.2.2.2.2.2.1 _ _ _ _ _ _)) h
  exact hctx.dec.typeDecl _ _ T d bh _ h'

end

end Ochr.Meaning.Steps
