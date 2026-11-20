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
covered (the dependent-values area); the sweep found no place the join could drop with an open
value above it (`Sweep.droppedUnderOpen`). For `datamodel` to prove in the tree layer, or to say why
it is false.

How the slice uses it: where the checker holds data other than `⋆` at a place of a non-copy
reading and the reference reads `⋆` there, the read `x` is `⋆`, so the member's read `w'` is `⋆`
(nothing is above `⋆` but itself, `MovedOf`), a member of `U`; then `U` is a proposition, which the
checker's typing of the place excludes ((D⋆T) and the soundness of `sortOf`, at a root the
position's stored type; at a field the field's declared type).
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
