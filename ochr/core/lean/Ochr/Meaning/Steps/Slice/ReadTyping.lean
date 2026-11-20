import Ochr.Meaning.Places

/-!
# The typing of a read, at a member (the slice's request to the data layer)

What the slice's two typing leaves (`dataMean_ne_proof`, `access_root_not_proof`) consume of the
model: reading a place along its path keeps (partial) membership in the path's type. Stated in the
data layer's terms (docs/34): a meaning below a whole member of a type (partial membership's member
disjunct, `MovedOf`), read along a path on which no strict prefix reads `⋆`; the same path on the
member is defined and gives a value above the read, a member of the type the read gives on the
member. No packed element, no field type at the current (possibly partly moved) earlier fields:
the type is the one the run computes on the member. The open disjunct of partial membership is not
covered (the dependent-values area). The join does drop fields under open values: accepted programs
reach it (`SweepProbes.OpenJoin`: the index of a dependent constructor rewritten or lent, then one
arm of a non-tail match moves a non-copy field), and the suite has places it could drop under an
open value (`Sweep.droppedUnderOpen`: unknowns, constructor values, a sealed program in
`DepVec.VPush`). (A first measurement said none: it excluded every partly moved value, and a
rewritten index invalidates the proof field that mentions it, so an open value is often partly
moved too.) For `datamodel` to prove in the tree layer, or to say why it is false.

The slice no longer consumes it (2026-11-20): the reference's drop no longer tests the meaning `⋆`
at the place (`Run.dropAt`), so the drop needs no typing of the read. It is kept as the typing of
reads that every step reading a place will need, for the data layer to prove.
-/

namespace Ochr.Meaning.Steps.Slice

open Ochr Ochr.Meaning

/-- **The typing of a read, at a member** (for `datamodel`). `s` is below the whole member `w` of
`T`; the read of `s` along `ss`, with no strict prefix reading `⋆`, is `x` (at the type `T'`).
Then the same path on `w` is defined, giving `w'` above `x`, a member of the type `U` the read gives
on `w`. Open: the data layer's. -/
theorem follow_below_member (dm : DataModel) (Γ : List IndDecl) (hcov : ∀ d ∈ Γ, dm.covers d)
    (T : TyS) (s w : Sem) (ss : List Step) (x : Sem) (T' : TyS)
    (hw : w.whole) (hsw : DataModel.MovedOf Γ s w) (hm : w ∈ₛ[dm.read] T.m)
    (hnp : ∀ k < ss.length, ∀ y U, Sem.follow dm Γ T s (ss.take k) = some (y, U) → y ≠ .proof)
    (hf : Sem.follow dm Γ T s ss = some (x, T')) :
    ∃ w' U, Sem.follow dm Γ T w ss = some (w', U) ∧ DataModel.MovedOf Γ x w' ∧ w' ∈ₛ[dm.read] U.m := by
  sorry

end Ochr.Meaning.Steps.Slice
