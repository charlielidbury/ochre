import Ochr.Meaning.Steps.DropOneAsm

/-!
# Step lemmas, matches and worlds: `evalMatch`, `evalMatchInd`, `evalMatchByType`,
`splitThenClose`, `generalizeNeutral`, `closeBlock`, `enterWorld`/`exitWorld` (milestone 3)

A match on a known constructor runs one arm, as the reference run does (`run`'s `.matchNat`/
`.matchInd` clauses, with D84's drop at the join). A match on an unknown `σ` *splits*
([Split]): each arm is checked in its own world under the refinement `σ := Cᵢ(σ̄ᵢ)`; the
reference run does not split, since under an assignment `ρ σ` has one tag. The two meet through
**coverage**: every typed assignment selects exactly one arm and extends to that arm's fresh
field unknowns, and the arm's refinement is then a substitution that changes no meaning
(`Steps/Subst.refine_step`). A match on a sealed program first generalises it to a fresh `σ`
with the record `n := σ`, the path condition `ρ σ = ⟦n⟧` (`TypedAssignment.neutral`). After the
arms, the match is closed off as a stuck block, an anonymous function of its captures, which
means the match (a sealed program means its run, and the run of the block's call is the run of
the match: docs/18 (C9), (K1)–(K3)). Worlds: leaving an arm restores the snapshot except names
and the types of unknowns created inside (X1)–(X4), so the restored state means the snapshot.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- [Join], the entry set: from related states the reference's is the checker's, but for the
borrow variables the checker ended early (docs/31 D24). -/
theorem joinEntry (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : joinEntry_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Join], the drop of one place: the checker's `movedPlace` and `dropAtJoin` against the
reference's `joinDropOne` (docs/31 D29, task C). Its obligations are the named statements of
`Steps/DropOne.lean` and `Steps/DropOneAsm.lean`, with the induction hypothesis's [Access] and [End]
statements: the assembly is written (`dropOne_step_asm`); what it rests on is open there. -/
theorem dropOne_step (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : dropOne_step_stmt K ρ φ (fuel + 1) :=
  dropOne_step_asm K ρ φ fuel ih

/-- The reference's drop under a context with another `Δ` is the same: it reads no `Δ`. -/
theorem joinDropOne_withΔ (Δ' : Nat → TyS) (s : SState) (q : Place) :
    joinDropOne ({ K with Δ := Δ' } : RunCtx) φ s q = joinDropOne K φ s q := rfl

/-- **[Join], the drop** (docs/31 D29, task C): the checker's loop over the join's list against the
reference's fold, by induction on the list, one place at a time (`dropOne_step`), the assignment
and the context's `Δ` extended at each, the scope the list is read in kept (`scopeOf_joinDropOne`). -/
theorem joinDrop_step (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : joinDrop_step_stmt K ρ φ (fuel + 1) := by
  intro st st' mt entry hg hctx s π hs hgrain hcopy bh h
  unfold joinDrop
  change Runs (dropLoop (fuel + 1) (K.D.joinMoves (scopeOf s) entry mt)) st bh () st' at h
  change ∃ ρ' Δ', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧
      CtxOk { K with Δ := Δ' } ρ' st' ∧
      Rel { K with Δ := Δ' } ρ' φ π st' ((K.D.joinMoves (scopeOf s) entry mt).foldl (joinDropOne K φ) s) ∧
      Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st'
  generalize hsc : scopeOf s = sc at hgrain hcopy h
  generalize K.D.joinMoves sc entry mt = qs at hgrain hcopy h
  induction qs generalizing K ρ st s bh with
  | nil =>
    rw [runs_dropLoop_nil h]
    refine ⟨ρ, K.Δ, fun _ _ => ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · cases K; exact hctx
    · cases K; exact hs
    · cases K; exact hg
  | cons q qs ihq =>
    obtain ⟨st₁, b₁, h1, h2⟩ := runs_dropLoop_cons h
    obtain ⟨ρ₁, Δ₁, hsz, hext₁, hctx₁, hs₁, hg₁⟩ := dropOne_step K ρ φ fuel ih st st₁ q s π hg hctx hs
      (hsc ▸ hgrain q List.mem_cons_self) (hsc ▸ hcopy q List.mem_cons_self) bh h1
    have hsc₁ : scopeOf (joinDropOne K φ s q) = sc := (scopeOf_joinDropOne K φ s q).trans hsc
    obtain ⟨ρ₂, Δ₂, hext₂, hctx₂, hs₂, hg₂⟩ := ihq ({ K with Δ := Δ₁ } : RunCtx) ρ₁ st₁ hg₁ hctx₁
      (joinDropOne K φ s q) hs₁ b₁ hsc₁ (fun q' hq' => hgrain q' (List.mem_cons_of_mem _ hq'))
      (fun q' hq' => hcopy q' (List.mem_cons_of_mem _ hq')) h2
    refine ⟨ρ₂, Δ₂, fun σ hσ => ⟨(hext₂ σ (Nat.lt_of_lt_of_le hσ hsz)).1.trans (hext₁ σ hσ).1,
      (hext₂ σ (Nat.lt_of_lt_of_le hσ hsz)).2.trans (hext₁ σ hσ).2⟩, ?_, ?_, ?_⟩
    · exact hctx₂
    · rw [List.foldl_cons]; exact hs₂
    · exact hg₂

/-- [Match] on `Nat` with a known constructor (`evalMatch`): below the run's `.matchNat` clause. -/
theorem evalMatch_step (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : evalMatch_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Match] on a declared inductive with a known constructor (`evalMatchInd`): below the run's
`.matchInd` clause. -/
theorem evalMatchInd_step (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : evalMatchInd_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- A match on a proof, by its type (`evalMatchByType`, D45): the one arm of a one-constructor
proposition, its proof fields `⋆` and its data fields fresh unknowns; below the run's clause for
a proof scrutinee under an assignment extended at those unknowns by the fields of the proof's
witness (the proposition is inhabited, since the scrutinee is a member of it). -/
theorem evalMatchByType_step (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : evalMatchByType_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Split] coverage: at a place whose content is the unknown `σ` of a data type, every typed
assignment selects a constructor `c` (exactly one: distinct constructors mean distinct tags), and extends to the arm's fresh field unknowns
(`ctorRefinement`) so that `σ`'s refinement is satisfied. -/
theorem split_coverage (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : split_coverage_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Split-gen] (`generalizeNeutral`): the sealed program `n` at place `p` becomes a fresh `σ`
with the record `n := σ`; under `ρ` extended at `σ` by `⟦n⟧`, the state means the same and the
assignment is typed (the path condition). -/
theorem generalizeNeutral_step (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : generalizeNeutral_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- A stuck block closed off (`closeBlock`): the block is a call of an anonymous function of its
captures, so its sealed result and fills mean what running the match means: below the run's
match clause (the capture by move of a place the selected arm keeps is D84's join, exact; a
split less fine than the arm's own is an over-approximation). The arms are given as the
match term `mt`; `B?` is the match's annotated type. -/
theorem closeBlock_step (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : closeBlock_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- Worlds (X1)–(X4), `exitWorld`: the restored state means the snapshot (every component but
the name counters and the types of unknowns created inside the arm is the snapshot's), and is
`Good` for any assignment the snapshot was. -/
theorem exitWorld_step (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) : exitWorld_step_stmt K ρ φ (fuel + 1) := by
  sorry

end

end Ochr.Meaning.Steps
