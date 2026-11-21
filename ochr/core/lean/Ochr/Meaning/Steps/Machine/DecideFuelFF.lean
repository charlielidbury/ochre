import Ochr.Meaning.DecisionsFF
import Ochr.Meaning.Steps.Machine.DecideFuel

/-!
# `DecisionsFF.decide_fuel_agree`, proved (the statement as that file states it)

`DecisionsFF.lean` leaves `decide_fuel_agree` (successful runs of each decision `DecTab` reads agree
whatever the fuel) as a `sorry`; the top-level decision table (`checkerDecisionsFF`) is aligned from
it (`decTab_ff`). This is that statement, `DecideFuelAgree st` verbatim, from `DecideFuel.lean`'s
`fuelAgree_*`. To close the leaf in place: `DecisionsFF.lean` imports `Steps.Machine.DecideFuel`
(which imports only `Slice.DecideKeep` and `Statements`: no cycle) and its `decide_fuel_agree` is
this proof term, verbatim.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- **`DecisionsFF.decide_fuel_agree`, proved**: at every state, every decision `DecTab` reads
answers the same at every fuel at which it succeeds. -/
theorem decide_fuel_agree' (st : MState) : DecideFuelAgree st :=
  ⟨fun t => fuelAgreeFF_of (fuelAgree_flags t) st, fun p => fuelAgreeFF_of (fuelAgree_placeDecl p) st,
    fun t => fuelAgreeFF_of (fuelAgree_declOf t) st, fun r => fuelAgreeFF_of (fuelAgree_copy r) st,
    fun t => fuelAgreeFF_of (fuelAgree_piSort t) st,
    fun entry t => fuelAgreeFF_of (fuelAgree_joinMoves entry t) st,
    fun t => fuelAgreeFF_of (fuelAgree_typeState t) st, fun T => fuelAgreeFF_of (fuelAgree_typeDecl T) st⟩

end Ochr.Meaning.Steps.Machine
