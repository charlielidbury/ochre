import Ochr.Meaning.DecisionsFF
import Ochr.Examples.Nat

/-!
# `DecStable` read against today's checker: an attack (exists13)

`Assembly.DecStable` asks that a declaration's field-type and parameter-type runs are the same under the
decisions at the state `st'` that accepted it and at ANY state `st` whose declarations and globals extend
`st'`'s. The decisions at the chain (`chainDecisions`) read a state's tables, and also the frozen readings
of its abstract values (`absDecl`, D96), which `DecStable` leaves unconstrained. A stored global holds an
abstract value only through a hole: below, `T : Type := ?` is stored with the value `σ0`, and `c : T := ?`
with the stored type `σ0`. Every state the checker reaches seeds `σ0`'s reading as `T` froze it
(`Check.seedHoles`, at each item's start), and there the erasure decision at the node `c` of the accepted
field type `Eq(Nat, F(c), Z)` is `(false, false)`; at a state with the same tables but `σ0` read `Prop` it
is `(true, true)`: `c` is read as a proof and the run passes `⋆` to `F` in its place. So `DecStable` as
stated is false for programs with holes at such a state, given a model whose `F` tells `⋆` from `c`'s
value (argued, not kernel-checked: the decisions are checked natively here; the run is not computable).
It holds for programs with no holes as far as read: no stored global holds an abstract value, since a
constant is checked from the empty environment and a function is stored at its written Π-type.
-/

open Ochr Ochr.Test Ochr.Meaning

#guard_msgs (drop warning) in
ochr DecStableHoles uses Nats {
  def T : Type := ?
  def c : T := ?
  def F (x : T) : Nat := ?
  inductive WF := MkWF(h : Eq(Nat, F(c), Z))
}

namespace Ochr.Meaning.DataModel.Exists.DecStableCE

/-- The program's items, resolved as the checker resolves them (the library, then the block). -/
def items : List Item :=
  let p := libOf {} 2000000 DecStableHoles ++ DecStableHoles.decls
  p.filterMap fun d => match (Ochr.Surface.runResolve p d 2000000 false).1 with
    | .ok (.ok it) => some it | _ => none

/-- The tables after the program. -/
def tabs : List GDef × List IndDecl := globalsAfter {} items

/-- The state every later item is checked from: the tables, with the holes' readings seeded. -/
def stSeed : MState := match (runMachine seedHoles { globals := tabs.1, inds := tabs.2 } 1000).1 with
  | .ok () s => s | _ => default

/-- The erasure decision `flagsD` at a term, at a state's top-level scope. -/
def flagsAt (st : MState) (t : Term) : String :=
  match (runMachine (flagsD t 100000) (scopeState st []) 100000).1 with
  | .ok r _ => toString r | .fail (.error m _) => "error: " ++ m | _ => "other"

-- every item is accepted; `c`'s stored type is the abstract value `σ0`, `T`'s stored value
#guard tabs.2.any (·.name == "WF")
#guard (tabs.1.find? (·.name == "c")).map (toString ·.ty) == some "σ0"
-- at the seeded state the node `c` is data; with `σ0` read as `Prop` (same tables) it is a proof
#guard flagsAt stSeed (.const "c") == "(false, false)"
#guard flagsAt { stSeed with absDecl := #[.sort 0, .other] } (.const "c") == "(true, true)"
-- the call `F(c)` itself is data at both
#guard flagsAt stSeed (.call (.const "F") [.const "c"] false) == "(false, false)"
#guard flagsAt { stSeed with absDecl := #[.sort 0, .other] } (.call (.const "F") [.const "c"] false) == "(false, false)"

end Ochr.Meaning.DataModel.Exists.DecStableCE
