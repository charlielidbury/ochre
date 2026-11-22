import Ochr.Meaning.Steps.Statements
import Ochr.Examples.Nat

/-!
# The deferred type of a call, attacked (lead26, 2026-11-22; docs/31 D183; the lead's conditions 1 and 2 on D180)

An untyped `let` of a call sets the deferral flag (`deferCallTy`) and clears the record (`callTyLater`); the call
(`callFn`) records its Π-type and arguments `(P, ws)` instead of its type where `later` holds (untyped, the type
wanted, the flag set, the declared result not a borrow), and the binding takes its type lazily from that record.
`EvalAt` now concludes, for a call run from a state with the flag set and the record clear, that a recorded pair
means the reference's result type (`Master.LaterOk`). These guards pin, at the checker's own state at a hole of a
real program, what is recorded in the cases least likely to mean the result type: a call that closes off, a
closure head, a borrow argument, a borrow result, an unknown argument, a dependent codomain; and what a run that
did not start with the flag leaves in the record (condition 1).
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr LaterAt uses Nats {
  inductive B := T | F
  def V (b : B) : Type := match b { T => Nat, F => Unit, }
  def G2 (b : B) : V(b) := match b { T => Z, F => (), }
  def Pr (n : Nat) : Nat := match n { Z => Z, S(m) => m, }
  def Inc (n : Nat) : Nat := S(n)
  def Len (r : &Nat) : Nat := clone(*r)
  def Kr (r : &Nat) : &Nat := r
  def At (n : Nat) : Unit := (let x = S(Z); let f = (λ(z : Nat) : Nat => S(z)); ?)
}

namespace Ochr.Meaning.Steps.LaterGuards
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- The checker's state at `At`'s hole: `n ↦ σ0` (variable 2), `x ↦ S(Z)` (variable 1), `f` a closure (variable 0). -/
def stAt : MState :=
  let r := Ochr.Test.runWith (some Prelude) "LaterAt" LaterAt { recordStates := true } (located := true)
  match r.rows.find? (·.name == "At") with
  | some row => (row.trace.toList.filterMap fun
      | .state _ false _ st => some st | _ => none).getLast?.getD default
  | none => default

/-- An untyped run of the call `c` as a `let` runs it: the flag set and the record cleared (`defer`), or both clear;
the value, its type and the record after. -/
def callAt (defer : Bool) (c : Term) (st : MState := stAt) :
    Option ((Value × Option Value) × Option (Value × List Value)) :=
  match (runMachine (do
      modify fun s => { s with deferCallTy := defer, callTyLater := none, wantTy := true }
      let r ← Ochr.eval 1000 false c none
      pure (r, (← get).callTyLater)) st 1000000).1 with
  | .ok r _ => some r
  | _ => none

/-- The recorded Π-type's domains and the recorded arguments. -/
def recShape : Option (Value × List Value) → Option (Nat × List Value)
  | some (.tPi _ (.pi _ ds _) _, ws) => some (ds.length, ws)
  | _ => none

def exactList (xs ys : List Value) : Bool := xs.length == ys.length && (xs.zip ys).all fun (a, b) => Value.exact a b

def recordsArgs (o : Option ((Value × Option Value) × Option (Value × List Value))) (ws : List Value) : Bool :=
  match o with
  | some ((_, none), rc) => match recShape rc with | some (1, ws') => exactList ws ws' | _ => false
  | _ => false

def nArg : Term := .place (.var 2)
def σ0 : Value := .abs 0

-- the hole: `n` an unknown, `x` a number, `f` a closure
#guard Value.exact (valAt stAt.env (.bind 1 1)) σ0
#guard match valAt stAt.env (.bind 1 3) with | .clo .. => true | _ => false

/-! ### An unknown argument: `Inc(n)` records `(Inc's Π-type, [σ0])` and returns `S(σ0)` with no type -/
#guard recordsArgs (callAt true (.call (.const "Inc") [nArg] false)) [σ0]
#guard match callAt true (.call (.const "Inc") [nArg] false) with
  | some ((v, _), _) => Value.exact v (.succ σ0) | none => false
-- without the flag: the type `Nat`, nothing recorded (control)
#guard match callAt false (.call (.const "Inc") [nArg] false) with
  | some ((_, some T), none) => Value.exact T .tNat | _ => false
#guard !recordsArgs (callAt false (.call (.const "Inc") [nArg] false)) [σ0]

/-! ### A call that closes off: `Pr(n)` (its body's match on `σ0` is stuck) records `(Pr's Π-type, [σ0])`; the value is
the sealed call -/
#guard recordsArgs (callAt true (.call (.const "Pr") [nArg] false)) [σ0]
#guard match callAt true (.call (.const "Pr") [nArg] false) with
  | some ((.sealed _, _), _) => true | _ => false

/-! ### A closure head: `f(Z)` records `(f's Π-type, [Z])` -/
#guard recordsArgs (callAt true (.call (.place (.var 0)) [.zero] false)) [.zero]

/-! ### A borrow argument: `Len(&x)` records, the argument the borrow as it was at the call -/
#guard match callAt true (.call (.const "Len") [.borrow (.var 1)] false) with
  | some ((_, none), rc) => match recShape rc with | some (1, [.borrow _ w]) => Value.exact w (.succ .zero) | _ => false
  | _ => false

/-! ### A borrow result: `Kr(&x)` records NOTHING (`later` asks the declared result not be a borrow) and has its type -/
#guard match callAt true (.call (.const "Kr") [.borrow (.var 1)] false) with
  | some ((_, some (.tRef T)), none) => Value.exact T .tNat | _ => false

/-! ### A dependent codomain: `G2(T)` records `(Π(b : B). V(b), [T])` -/
def tT : Term := .ctor "B" 0 ⟨"T"⟩ [] []
def tF : Term := .ctor "B" 1 ⟨"F"⟩ [] []
#guard match callAt true (.call (.const "G2") [tT] false) with
  | some ((_, none), rc) => match recShape rc with | some (1, [.ind "B" 0 _ _ []]) => true | _ => false
  | _ => false
-- the whole `let y = G2(b); y`, untyped, the type wanted: `y` is read at the deferred type at the argument,
-- `Nat` at `T` and `Unit` at `F` (each the other's control)
def letG2 (b : Term) : Option (Value × Option Value) :=
  match (runMachine (do
      modify fun s => { s with wantTy := true }
      Ochr.eval 1000 false (.letIn ⟨"y"⟩ (.call (.const "G2") [b] false) (.place (.var 0))) none) stAt 1000000).1 with
  | .ok r _ => some r
  | _ => none
#guard match letG2 tT with | some (_, some T) => Value.exact T .tNat | _ => false
#guard match letG2 tF with | some (_, some T) => Value.exact T .tUnit | _ => false
#guard !(match letG2 tT with | some (_, some T) => Value.exact T .tUnit | _ => false)

/-! ### Condition 1: what a run leaves in the record when it did not start with the flag. Since main's D130 the checker
CLEARS the record when every evaluation starts (`evalAt`), so a term that runs no call leaves none (`Z`: the stale record
is gone; before D130 it was carried through, machine12's merge flipped this guard). A call run without the flag records
nothing (`Inc(n)` above). -/
def stale : Option (Value × List Value) := some (.tNat, [])
def afterZ : Option (Option (Value × List Value)) :=
  match (runMachine (do
      modify fun s => { s with callTyLater := stale }
      discard (Ochr.eval 1000 false .zero none)
      pure (← get).callTyLater) stAt 1000000).1 with
  | .ok r _ => some r
  | _ => none
#guard afterZ == some none
-- a call without the flag overwrites a stale record with nothing
def afterCall : Option (Option (Value × List Value)) :=
  match (runMachine (do
      modify fun s => { s with callTyLater := stale, wantTy := true }
      discard (Ochr.eval 1000 false (.call (.const "Inc") [nArg] false) none)
      pure (← get).callTyLater) stAt 1000000).1 with
  | .ok r _ => some r
  | _ => none
#guard afterCall == some none

end Ochr.Meaning.Steps.LaterGuards
