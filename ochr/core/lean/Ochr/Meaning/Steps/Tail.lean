import Ochr.Meaning.Steps.Eval
import Ochr.Check

/-!
# Step lemmas, definitions: `checkTail`, `checkFix`, `checkDef`, `checkInd` (milestone 3;
docs/18 Corollary "an accepted definition means an element of its type")

[Def] checks a definition at its generic call: a fresh unknown per parameter (a borrow
parameter's in a cell behind a borrow, a proof parameter's `⋆`), the goal the codomain there,
the body in tail position producing a case tree whose every leaf converts to the goal. Under
every typed assignment of the generic state, following the arms it selects, `evalCore_step`
along the tree gives a leaf whose value is a member of the goal (`conv_sound` at the leaf and
`bodyReturns_sound` for wholeness); so the definition's meaning, the function from assignments
to leaf meanings, is an element of its Π-type. `checkInd` establishes that the data model covers
the declaration ((I1)–(I9) make the fixed point exist).
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The generic state of a `fix` is `Good` for every assignment that gives each parameter's
unknown an element of its type (and the goal is a type). -/
theorem generic_good (st st' : MState) (fuel : Nat) (fv : Value) (cs : List Value) (t : Term)
    (capRec : Array (Option Nat)) (rd : List (DeclInfo × Value))
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.checkFix fuel fv cs t capRec rd) st fuel () st') :
    ∀ ρ', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) →
      TypedAssignment K.dm K.C K.Γ ρ' st' → Good K.dm K.C K.Γ ρ' st' := by
  sorry

/-- `checkTail` with a leaf continuation: every typed assignment of the start state reaches a
leaf (coverage along splits), where the continuation's hypotheses hold for the leaf's value and
type, and the leaf's value means the reference run's result at the start. -/
theorem checkTail_step (st st' : MState) (fuel : Nat) (t : Term) (k : Value → Value → M Unit)
    (hint : TyS)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.checkTail fuel t k) st fuel () st') :
    ∃ ρ' v T stl stl', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧ Good K.dm K.C K.Γ ρ' stl ∧
      Runs (k v T) stl fuel () stl' ∧
      ∃ r s', run K ρ' φ hint t (SM' K ρ' st) = some (r, s') ∧
        meanV K ρ' φ r.2 v ⊑ r.1 ∧ (meanV K ρ' noFuture (.plain .err) T).asTy = r.2.m := by
  sorry

/-- [Def]/[Fix] (`checkFix`): an accepted `fix` means an element of its Π-type (docs/18
Corollary 15): under every assignment of its parameters, the body's reference run gives a
member of the goal, so `mkTele` succeeds and the closure's meaning is in the carrier. -/
theorem checkFix_sound (st st' : MState) (fuel : Nat) (fv : Value) (cs : List Value) (t : Term)
    (capRec : Array (Option Nat)) (rd : List (DeclInfo × Value)) (fT : Value)
    (hg : Good K.dm K.C K.Γ ρ st)
    (hT : ∃ hs ds c, t = .fix ⟨""⟩ hs ds c none .tt ∨ fT = .tPi cs (.pi hs ds c) rd)
    (h : Runs (Ochr.checkFix fuel fv cs t capRec rd) st fuel () st') :
    meanV K ρ φ (.plain .err) (.clo cs t rd) ∈ₛ (meanV K ρ φ (.plain .err) fT).asTy := by
  sorry

/-- [Const]: an accepted constant's value is a member of its goal, under the empty assignment. -/
theorem checkConst_sound (st st' : MState) (d : Ochr.Def) (goal v : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hd : d.doms = [])
    (h : Runs (Ochr.checkDef d) st 2000000 () st')
    (hgl : ∃ g ∈ st'.globals, g.name = d.name ∧ g.ty = goal ∧ g.val = v) :
    meanV K ρ φ (Value.tyS K.dm K.C K.Γ ρ goal) v ∈ₛ (meanV K ρ noFuture (.plain .err) goal).asTy := by
  sorry

/-- [Ind-decl] (`checkInd`): an accepted declaration satisfies (I1)–(I9), so the data model covers
it (the least fixed point exists in the sort's universe; docs/18 Lemma 2). -/
theorem checkInd_sound (st st' : MState) (d : IndDecl)
    (hg : Good K.dm K.C K.Γ ρ st) (h : Runs (Ochr.checkInd d) st 2000000 () st') :
    K.dm.covers d := by
  sorry

end

end Ochr.Meaning.Steps
