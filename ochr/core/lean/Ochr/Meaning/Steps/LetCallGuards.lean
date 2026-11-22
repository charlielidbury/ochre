import Ochr.Meaning.Steps.CallGuards
import Ochr.Meaning.Steps.MasterUntyped

/-!
# The untyped `let` of a call: the deferred type, pinned (lead26, 2026-11-22; docs/31 D180)

`Machine.LetCallInvU` (proved, `Steps/MasterUntyped.lean`) says the untyped `let` of a call runs the call with the
deferral flag set and binds the result with its type recorded for later (`lazyTy`) where the call came back with none.
These guards run the checker on `I(Z)`, `I` the column's `def I (n : Nat) : Nat := S(n)` (`ColumnIStart.gI`), and pin
both outcomes: with the flag set the call returns no type and records `(I's Π-type, [Z])`; with it clear it returns
`Nat` and records nothing. The whole `let y = I(Z); y`, run untyped, reads `y` back at `Nat` through the deferred type.
-/

namespace Ochr.Meaning.Steps.Form.LetCallGuards

open Ochr
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)

/-- The column's state with `I` declared, the type wanted (`wantTy`, as `demand true` leaves it at a `let`). -/
def st0 : MState := { CallGuards.stJ with wantTy := true }

/-- `I(Z)`, as the `let` runs it: from a state with the deferral flag as given, the value, its type and the recorded
deferred type. -/
def callI (defer : Bool) : M ((Value × Option Value) × Option (Value × List Value)) := do
  modify fun s => { s with deferCallTy := defer, callTyLater := none }
  let r ← Ochr.eval 100 false (.call (.const "I") [.zero] false) none
  pure (r, (← get).callTyLater)

#guard isOk (callI true) st0 100000
#guard isOk (callI false) st0 100000
-- with the flag set: the value `S(Z)`, NO type, the deferred type `(I's Π-type, [Z])` recorded
#guard Value.exact (outVal (callI true) st0 100000).1.1 (.succ .zero)
#guard (outVal (callI true) st0 100000).1.2.isNone
#guard match (outVal (callI true) st0 100000).2 with
  | some (.tPi _ (.pi _ ds _) _, [w]) => ds.length == 1 && Value.exact w .zero
  | _ => false
-- with the flag clear: the type `Nat`, nothing recorded (each guard's negation of the other)
#guard !(outVal (callI false) st0 100000).1.2.isNone
#guard match (outVal (callI false) st0 100000).1.2 with | some T => Value.exact T .tNat | none => false
#guard (outVal (callI false) st0 100000).2.isNone

/-- `let y = I(Z); y`, untyped, out of tail position. -/
def tLetI : Term := .letIn ⟨"y"⟩ (.call (.const "I") [.zero] false) (.place (.var 0))

#guard isOk (Ochr.eval 100 false tLetI none) st0 100000
#guard Value.exact (outVal (Ochr.eval 100 false tLetI none) st0 100000).1 (.succ .zero)

end Ochr.Meaning.Steps.Form.LetCallGuards
