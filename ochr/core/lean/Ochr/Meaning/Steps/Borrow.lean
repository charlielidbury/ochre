import Ochr.Meaning.Lemmas
import Ochr.Meaning.WF
import Ochr.Machine

/-!
# Step lemmas, borrows: [End], [Access], [Read], [Borrow], [Assign], [Drop] (milestone 3)

The shape of every step lemma of the skeleton (docs/18 Thm. 14, one rule at a time). A checker
step is a monadic action `f : M α` run by `runMachine` from a state `st` that is `Good` for an
assignment `ρ` (membership and well-formedness, `WF.lean`). If it returns `ok a st'`, then for
the extended assignment `ρ'` (here the same `ρ`: these steps create no unknowns) the meaning of
`st'` is below the semantic step applied to the meaning of `st`, and `st'` is `Good` again.
"Below" is `Below` of `State.lean`; an *exact* step has equality at every position. Each lemma
says which of the three kinds it is: exact, an end (below by `semEnd_below`), or an
over-approximation.

Conventions for provers: the checker's state is read through `MState.sstate` and `MState.mean`
(`State.lean`, `SState.lean`); the semantic side is `SState`'s primitives; `K` is the run
context whose `C` is the knot `codeMeaning` and whose `D` is the checker's `Decide` functions
(instantiated in milestone 3's `Decisions.lean`, not yet written). A lemma may assume `Good`
and nothing else about the state: four natural statements about the checker are false at
arbitrary states (docs/18 §"Facts that hold only at reachable states").
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment)

/-- `f` run from `st` succeeds with `a` and `st'`. -/
def Runs {α : Type} (f : M α) (st : MState) (fuel : Nat) (a : α) (st' : MState) : Prop :=
  ∃ left log, runMachine f st fuel = (.ok a st', left, log)

/-- The meaning of a checker state as the run sees it (`K.C` is the knot). -/
noncomputable def SM' (st : MState) : SState := MState.sstate K.dm K.C K.Γ ρ st

/-- A step is exact: the meanings agree at every position and so do the shapes. -/
def Exact (m m' : Mean) : Prop := (∀ φ p, m.val φ p = m'.val φ p) ∧ ∀ p, m.shape p = m'.shape p

/-- [End ℓ] (`Machine.endBorrow`): with `ℓ`'s borrow held whole at `r`, the result is `semEnd`
exactly, so it is below (`Mean.semEnd_below`); `Good` is kept. The content must be whole, which
the checker checks outside an observation (D53 (h), D68). -/
theorem endBorrow_step (st st' : MState) (fuel l : Nat) (r : Pos)
    (hg : Good K.dm K.C K.Γ ρ st) (hr : Env.shape st.env r = some l)
    (h : Runs (Ochr.endBorrow fuel l) st fuel () st') :
    Exact (MState.mean K.dm K.C K.Γ ρ st') ((MState.mean K.dm K.C K.Γ ρ st).semEnd r l) ∧
    Good K.dm K.C K.Γ ρ st' := by
  sorry

/-- [Access] (`accessPath`, `accessInside`, `accessNeutralHead`): a sequence of [End]s, each
below; the ended labels include every label the accessed position's meaning depends on, so the
result is below the reference's `SState.access` and the accessed content no longer depends on
the future (`Lemmas.meanV_congr`). -/
theorem accessPath_step (st st' : MState) (fuel : Nat) (p : Place) (pos : Pos)
    (hg : Good K.dm K.C K.Γ ρ st) (hpos : resolve (SM' K ρ st) p = some (pos, (p.steps).2))
    (h : Runs (Ochr.accessPath fuel p) st fuel () st') :
    Below (MState.mean K.dm K.C K.Γ ρ st') ((SM' K ρ st).access pos).toMean ∧
    Good K.dm K.C K.Γ ρ st' := by
  sorry

theorem accessInside_step (st st' : MState) (fuel : Nat) (p : Place) (owned : Bool) (pos : Pos)
    (hg : Good K.dm K.C K.Γ ρ st) (hpos : resolve (SM' K ρ st) p = some (pos, (p.steps).2))
    (h : Runs (Ochr.accessInside fuel p owned) st fuel () st') :
    Below (MState.mean K.dm K.C K.Γ ρ st') ((SM' K ρ st).access pos).toMean ∧
    Good K.dm K.C K.Γ ρ st' := by
  sorry

/-- [Read] (`readPlace`): after its access, the result is the place's meaning (future-free), and
the place is unchanged (a copy, by the declared reading, D80) or `moved` (a move); exact against
the run's `readPlace` with the same copy decision (`Decisions.copy`, aligned). -/
theorem readPlace_step (st st' : MState) (fuel : Nat) (p : Place) (v : Value) (copy : Bool)
    (hg : Good K.dm K.C K.Γ ρ st)
    (hcopy : K.D.copy (K.D.placeDecl (scopeOf (SM' K ρ st)) p) = copy)
    (h : Runs (Ochr.readPlace fuel p) st fuel v st') :
    ∃ r s', Ochr.Meaning.readPlace K p copy (SM' K ρ st) = some (r, s') ∧
      (∀ φ, meanV K ρ φ r.2.m v = r.1 φ) ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st' := by
  sorry

/-- [Borrow] (`borrowPlace`): exact against the run's `borrowPlace` with the same fresh label
(`nextLoan`): the place means the label's final content and the borrow the old content. -/
theorem borrowPlace_step (st st' : MState) (fuel : Nat) (p : Place) (v : Value)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.borrowPlace fuel p) st fuel v st') :
    ∃ r s', Ochr.Meaning.borrowPlace K p (SM' K ρ st) = some (r, s') ∧
      (∀ φ, meanV K ρ φ r.2.m v = r.1 φ) ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st' := by
  sorry

/-- [Assign] (`assignPlace`): the owned access (D67, ends), the old content's borrows end
([Drop], ends), then the place means the new value: below the run's `setContent` after
`access`. The written value's meaning is given. -/
theorem assignPlace_step (st st' : MState) (fuel : Nat) (p : Place) (v : Value) (pos : Pos)
    (hg : Good K.dm K.C K.Γ ρ st) (hpos : resolve (SM' K ρ st) p = some (pos, (p.steps).2))
    (hv : ∀ φ φ', meanV K ρ φ .err v = meanV K ρ φ' .err v)
    (h : Runs (Ochr.assignPlace fuel p v) st fuel () st') :
    ∃ s', setContent K pos (p.steps).2 (meanV K ρ noFuture .err v) ((SM' K ρ st).access pos) = some (⟨⟩, s') ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st' := by
  sorry

/-- [Drop] of the top binding (`dropTopBind`): its borrows end, each live loan in it ends its
borrower when held in a binding (D65), then the binding is gone: ends followed by `forget`,
below. -/
theorem dropTopBind_step (st st' : MState) (fuel : Nat)
    (hg : Good K.dm K.C K.Γ ρ st) (h : Runs (Ochr.dropTopBind fuel) st fuel () st') :
    Below (MState.mean K.dm K.C K.Γ ρ st') ((SM' K ρ st).dropLast).toMean ∧
    Good K.dm K.C K.Γ ρ st' := by
  sorry

/-- Popping a frame (`popFrame`): each binding dropped in turn; below. -/
theorem popFrame_step (st st' : MState) (fuel : Nat)
    (hg : Good K.dm K.C K.Γ ρ st) (h : Runs (Ochr.popFrame fuel) st fuel () st') :
    Below (MState.mean K.dm K.C K.Γ ρ st') (MState.mean K.dm K.C K.Γ ρ st) ∧
    Good K.dm K.C K.Γ ρ st' := by
  sorry

end

end Ochr.Meaning.Steps
