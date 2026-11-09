import Ochr.Meaning.Steps.Borrow

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
variable (K : RunCtx) (ρ : Assignment)

/-- `ρ'` extends `ρ` on the unknowns of `st`. -/
def Extends (st : MState) (ρ ρ' : Assignment) : Prop := ∀ σ, σ < st.absTy.size → ρ' σ = ρ σ

/-- [Match] on `Nat` with a known constructor (`evalMatch`): below the run's `.matchNat` clause. -/
theorem evalMatch_step (st st' : MState) (fuel : Nat) (typed : Bool) (p : Place) (z s : Term)
    (expected : Option Value) (v : Value) (T? : Option Value) (hint : TyM)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.evalMatch fuel typed p z s expected) st fuel (v, T?) st') :
    ∃ r s', run K ρ hint (.matchNat p z s) (SM' K ρ st) = some (r, s') ∧
      (∀ φ, meanV K ρ φ r.2.m v ⊑ r.1 φ) ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st' := by
  sorry

/-- [Match] on a declared inductive with a known constructor (`evalMatchInd`): below the run's
`.matchInd` clause. -/
theorem evalMatchInd_step (st st' : MState) (fuel : Nat) (typed : Bool) (p : Place) (ty : String)
    (arms : List (Hint × Term)) (v : Value) (T? : Option Value) (hint : TyM)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.evalMatchInd fuel typed p ty arms) st fuel (v, T?) st') :
    ∃ r s', run K ρ hint (.matchInd p ty arms) (SM' K ρ st) = some (r, s') ∧
      (∀ φ, meanV K ρ φ r.2.m v ⊑ r.1 φ) ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st' := by
  sorry

/-- A match on a proof, by its type (`evalMatchByType`, D45): the one arm of a one-constructor
proposition, its proof fields `⋆` and its data fields fresh unknowns; below the run's clause for
a proof scrutinee under an assignment extended at those unknowns by the fields of the proof's
witness (the proposition is inhabited, since the scrutinee is a member of it). -/
theorem evalMatchByType_step (st st' : MState) (fuel : Nat) (typed : Bool) (p : Place) (ty : String)
    (arms : List (Hint × Term)) (v : Value) (T? : Option Value) (hint : TyM)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.evalMatchByType fuel typed p ty arms none) st fuel (v, T?) st') :
    ∃ ρ', Extends st ρ ρ' ∧ TypedAssignment K.dm K.C K.Γ ρ' st' ∧
      ∃ r s', run K ρ' hint (.matchInd p ty arms) (SM' K ρ' st) = some (r, s') ∧
        (∀ φ, meanV K ρ' φ r.2.m v ⊑ r.1 φ) ∧
        Below (MState.mean K.dm K.C K.Γ ρ' st') s'.toMean ∧ Good K.dm K.C K.Γ ρ' st' := by
  sorry

/-- [Split] coverage: at a place whose content is the unknown `σ` of a data type, every typed
assignment selects a constructor `c` (exactly one: distinct constructors mean distinct tags), and extends to the arm's fresh field unknowns
(`ctorRefinement`) so that `σ`'s refinement is satisfied. -/
theorem split_coverage (st : MState) (fuel σ : Nat) (d : IndDecl) (ps : List Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hσ : st.absTy[σ]? = some (.tInd d.name ps)) :
    ∃ c ρ' r st', Extends st ρ ρ' ∧
      Runs (Ochr.ctorRefinement fuel d (ps) c) st fuel r st' ∧
      TypedAssignment K.dm K.C K.Γ ρ' st' ∧
      ∀ φ, ρ' σ = meanV K ρ' φ (MState.absTyM K.dm K.C K.Γ ρ' st' σ) r := by
  sorry

/-- [Split-gen] (`generalizeNeutral`): the sealed program `n` at place `p` becomes a fresh `σ`
with the record `n := σ`; under `ρ` extended at `σ` by `⟦n⟧`, the state means the same and the
assignment is typed (the path condition). -/
theorem generalizeNeutral_step (st st' : MState) (fuel : Nat) (p : Place) (n : Value) (σ : Nat) (hint : TyM)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.generalizeNeutral fuel p n) st fuel σ st') :
    let ρ' := ρ.ext σ (meanV K ρ noFuture hint n)
    Exact (MState.mean K.dm K.C K.Γ ρ' st') (MState.mean K.dm K.C K.Γ ρ st) ∧
    Good K.dm K.C K.Γ ρ' st' := by
  sorry

/-- A stuck block closed off (`closeBlock`): the block is a call of an anonymous function of its
captures, so its sealed result and fills mean what running the match means: below the run's
match clause (the capture by move of a place the selected arm keeps is D84's join, exact; a
split less fine than the arm's own is an over-approximation). The arms are given as the
match term `mt`; `B?` is the match's annotated type. -/
theorem closeBlock_step (st st' : MState) (fuel : Nat) (mt : Term) (arms : List BlockArm)
    (B? : Option Value) (v : Value) (T? : Option Value) (hint : TyM)
    (hg : Good K.dm K.C K.Γ ρ st)
    (hmt : mt matches .matchNat .. | .matchInd .. | .prim "J" _)
    (h : Runs (Ochr.closeBlock fuel mt arms B?) st fuel (v, T?) st') :
    ∃ r s', run K ρ hint mt (SM' K ρ st) = some (r, s') ∧
      (∀ φ, meanV K ρ φ r.2.m v ⊑ r.1 φ) ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st' := by
  sorry

/-- Worlds (X1)–(X4), `exitWorld`: the restored state means the snapshot (every component but
the name counters and the types of unknowns created inside the arm is the snapshot's), and is
`Good` for any assignment the snapshot was. -/
theorem exitWorld_step (st st' : MState) (w : World)
    (hg : Good K.dm K.C K.Γ ρ w.saved)
    (h : Runs (Ochr.exitWorld w) st 0 () st') :
    Exact (MState.mean K.dm K.C K.Γ ρ st') (MState.mean K.dm K.C K.Γ ρ w.saved) ∧
    (∀ σ, σ < w.saved.absTy.size → st'.absTy[σ]? = w.saved.absTy[σ]?) ∧
    st'.neutrals = w.saved.neutrals ∧ st'.etaRefs = w.saved.etaRefs ∧ st'.goal = w.saved.goal ∧
    Good K.dm K.C K.Γ ρ st' := by
  sorry

end

end Ochr.Meaning.Steps
