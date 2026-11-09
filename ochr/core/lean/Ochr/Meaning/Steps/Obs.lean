import Ochr.Meaning.Steps.Borrow

/-!
# Step lemmas, observation and `Id`: `observe`, `idType`, footprint coverage (milestone 3;
docs/18 (O1)–(O5), docs/27 Def. 5)

The checker observes a side of `Id` on a private copy, ends every borrow left, and reads the
result and the contents of the footprint's owners (`observe`); `Id` then computes to the
conjunction of the equations over the result and the owners (`idType`). The reference run's
`observation` reads the result and *every* position after ending every borrow. They agree by
**footprint coverage**: a position outside the footprint has the same meaning after either
side (a side changes a position only by writing it or a borrow it owns, or by moving it, and
under D84 moves are in the footprint too), so its equation is true and dropping it loses
nothing. So `idType` is exact.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment)

/-- The reference observation of a side, if its run succeeds. -/
noncomputable def refObs (hint : TyM) (t : Term) (s : SState) : Option (List Sem) :=
  (run K ρ hint t s).map fun (r, s') => observation r s'

/-- `observe` (a side on a private copy, every borrow ended, the result and the owners read): the
result and each observed owner mean their components of the reference observation at the
owners' positions; the state is unchanged (a copy). -/
theorem observe_step (st st' : MState) (fuel : Nat) (typed : Bool) (t : Term) (A : Value) (W : List Pos)
    (r : Value) (ws : List Value)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.observe fuel typed t A W) st fuel (r, ws) st') :
    st'.core = st.core ∧
    ∃ o, refObs K ρ (meanV K ρ noFuture .err A).asTy t (SM' K ρ st) = some o ∧
      (∀ φ, o[0]? = some (meanV K ρ φ (meanV K ρ noFuture .err A).asTy r)) ∧
      ∀ (φ : Future) (i j : Nat) (p : Pos), W[i]? = some p → (SM' K ρ st).positions[j]? = some p →
        ws[i]?.map (meanV K ρ φ .err) = o.tail[j]? := by
  sorry

/-- Footprint coverage (docs/18 "Footprint coverage", the third of the five lemmas): a position
outside the footprint of the two sides means the same after either side. -/
theorem footprint_coverage (st : MState) (A t u : Term) (p : Pos) (o₁ o₂ : List Sem) (j : Nat)
    (hg : Good K.dm K.C K.Γ ρ st)
    (hp : p ∉ footprint st.env [t, u]) (hj : (SM' K ρ st).positions[j]? = some p)
    (h₁ : refObs K ρ (meanV K ρ noFuture .err (.sealed A)).asTy t (SM' K ρ st) = some o₁)
    (h₂ : refObs K ρ (meanV K ρ noFuture .err (.sealed A)).asTy u (SM' K ρ st) = some o₂) :
    o₁.tail[j]? = o₂.tail[j]? := by
  sorry

/-- `Id` computes (`idType`): the conjunction over the result and the footprint's owners means
the reference's `Id`, the equality of the two observations; exact, and the state's core is
unchanged. -/
theorem idType_step (st st' : MState) (fuel : Nat) (typed : Bool) (A t u : Term) (P : Value)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.idType fuel typed A t u) st fuel P st') :
    st'.core = st.core ∧
    ∃ r s', run K ρ .err (.id A t u) (SM' K ρ st) = some (r, s') ∧
      ∀ φ, ((meanV K ρ φ .err P).asTy).true ↔ ((r.1 φ).asTy).true := by
  sorry

/-- Owners (RULES §4): every position `owners env l` lists holds, directly or through the content
of a borrow it holds, a loan of `l`; and conversely every position whose meaning depends on `l`
is among them (`Mean.dependsOn`). -/
theorem owners_sound (st : MState) (l : Nat) (p : Pos)
    (hg : Good K.dm K.C K.Γ ρ st) (hl : liveLoan st.env l = true) :
    (MState.mean K.dm K.C K.Γ ρ st).dependsOn p l → p ∈ owners st.env l := by
  sorry

end

end Ochr.Meaning.Steps
