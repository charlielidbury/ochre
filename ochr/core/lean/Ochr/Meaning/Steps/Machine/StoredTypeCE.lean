import Ochr.Meaning.Steps.Statements
import Ochr.Examples.Nat

/-!
# A binding's stored type is not tied to its value (machine11, 2026-11-22)

Two facts stated for the checker alone hold at every state the checker reaches but not at every state `Pre`
allows, because no clause of the invariant (`Form.Inv`: WF1–WF4, WF6, WF8, WF10–WF12, WF14–WF16, `ShapeFacts`, the
label counter) ties a position's stored type to what its value is. A typed read returns the binding's stored type
(`evalCore`'s `.place` clause: `placeType`), and an untyped deferred call records the head's stored type as its
Π-type (`callFn`: `funType` returns the head's type `fT` when it has one, unchecked when the call's type is deferred).

* `Master.SuccArgNoBorrowT` (READ FALSE as stated): at `stB` (`y ↦ loan_0 : Nat`, `x ↦ borrow_0(Z) : Nat`, the
  readings `other`, label counter 1) every clause of `Inv` holds (a borrow whole at a binding, its loan live and
  once, no ⋆, no constructor, no unknown, no type holding a loan), and the typed run of `x` returns `borrow_0(Z)` at
  `Nat`, which passes `expectTy _ Nat` (`runX`).
* The checker fact `LetCallInvU`'s strengthening needs ("an untyped call wanting its type records a Π-type"), FALSE
  as a statement over states: with `f ↦ g : Nat` (a global function stored at `Nat`), the untyped deferred call `f(Z)`
  returns `Z` with no type and records `(Nat, [Z])`, which the `let` does not take (`if let .tPi _ (.pi …) _`): its
  binding gets no type and no deferred one (`runC`).

The minimal restatement for both (the lead's call): a clause of the invariant, checker-only, "a position holding a
borrow stores a borrow type; a position holding a function value (a global function, a closure) stores a Π-type
`.tPi _ (.pi …) _`" (every binder stores the type of what it bound; typed code calls only at a Π-type, `callType`).
-/

namespace Ochr.Meaning.Steps.Machine.StoredTypeCE
open Ochr Ochr.Meaning Ochr.Test

/-- `y ↦ loan_0 : Nat`, `x ↦ borrow_0(Z) : Nat`: a borrow stored at the type `Nat`. -/
def stB : MState :=
  { env := #[{ binds := #[{ hint := ⟨"y"⟩, ty := some .tNat, val := .loan 0 },
                          { hint := ⟨"x"⟩, ty := some .tNat, val := .borrow 0 .zero }] }],
    nextLoan := 1 }

/-- The typed run of `x` and the test against `Nat` (`S`'s argument check). -/
def runX : Option (Value × Option Value) :=
  match (runMachine (do
      modify fun s => { s with wantTy := true }
      let (v, T) ← Ochr.eval 100 true (.place (.var 0)) none
      Ochr.expectTy 100 "the argument of S" T .tNat
      pure (v, T)) stB 100000).1 with
  | .ok r _ => some r
  | _ => none

#guard runX == some (.borrow 0 .zero, some .tNat)

end Ochr.Meaning.Steps.Machine.StoredTypeCE

#guard_msgs (drop warning) in
ochr StoredTypeLCI uses Nats {
  def g (n : Nat) : Nat := n
  def At (k : Nat) : Unit := ?
}

namespace Ochr.Meaning.Steps.Machine.StoredTypeCE
open Ochr Ochr.Meaning Ochr.Test

/-- The checker's state at `At`'s hole, with `f ↦ g` (the global function) stored at the type `Nat`. -/
def st0F : MState :=
  let r := Ochr.Test.runWith (some Prelude) "StoredTypeLCI" StoredTypeLCI { recordStates := true } (located := true)
  match r.rows.find? (·.name == "At") with
  | some row => (row.trace.toList.filterMap fun
      | .state _ false _ st => some st | _ => none).getLast?.getD default
  | none => default

def stF : MState := { st0F with env := st0F.env.modify (st0F.env.size - 1) fun fr =>
  { fr with binds := fr.binds.push { hint := ⟨"f"⟩, ty := some .tNat, val := .gfn "g" } } }

/-- The untyped call `f(Z)` as a `let`'s right-hand side (its type wanted and deferred): value, type, record. -/
def runC : Option (Value × Option Value × Option (Value × List Value)) :=
  match (runMachine (do
      modify fun s => { s with wantTy := true, deferCallTy := true, callTyLater := none }
      let (v, T) ← Ochr.eval 1000 false (.call (.place (.var 0)) [.zero] false) none
      pure (v, T, (← get).callTyLater)) stF 1000000).1 with
  | .ok r _ => some r
  | _ => none

#guard runC == some (.zero, none, some (.tNat, [.zero]))

end Ochr.Meaning.Steps.Machine.StoredTypeCE
