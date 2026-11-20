import Ochr.Meaning.Regress.EqJ

/-!
# The rules trial: growth in the `Eq` area that the result names (compiled checks)

`mkEqM` at `W(p) := MkW(t : Tag(match p { MkE2(k) => k }))`, at the hole of `TAt` where `p` is the
unknown `σ0 : E2`: [Eq-inj] computes the field type `Tag(match σ0 {…})` in a typed private run, which
refines `σ0 := MkE2(σ3)` in place (D93); the record survives (D37) and the field type is
`Tag(σ3)`. With stuck field values the computed proposition is `Eq(Tag(σ3), σ1, σ2)`: it names an
unknown made inside the computation, so this growth is inherent (the result's meaning reads it,
pinned by the new record on the old `σ0`). A conversion's growth never is: its result is a
boolean.
-/

open Ochr.Test
#guard_msgs (drop warning) in
ochr GrowAt uses Nats {
  inductive E2 : Type := MkE2(k : Nat)
  inductive Tag (n : Nat) := MkTag(x : Nat)
  def Pick (p : E2) : Nat := match p { MkE2(k) => k }
  inductive W (p : E2) := MkW(t : Tag((match p { MkE2(k) => k })))
  def TAt (p : E2) (x : Nat) (y : Nat) : Nat := ?
}
namespace GrowthProbe
open Ochr
def stT : MState :=
  let r := Ochr.Test.runWith (some Prelude) "GrowAt" GrowAt { recordStates := true } (located := true)
  match r.rows.find? (·.name == "GrowAt") |>.orElse (fun _ => r.rows.find? (·.name == "TAt")) with
  | some row => (row.trace.toList.filterMap fun
      | .state _ false _ st => some st | _ => none).getLast?.getD default
  | none => default
def show' {α : Type} [ToString α] (x : M α) : String :=
  match (runMachine x stT 1000000).1 with
  | .ok a st' => s!"ok {a}; absTy {stT.absTy.toList} -> {st'.absTy.toList}; eta {st'.etaRefs.map (fun (n, v) => (n, toString v))}"
  | .fail _ => s!"fail"
  | .exhausted m => s!"exhausted {m}"
#guard stT.absTy.size == 3
-- unknowns: σ0 : E2 (p), σ1 x, σ2 y
def tagv (n : Value) : Value := .ind "Tag" 0 ⟨"MkTag"⟩ [] [n]
#guard show' (Ochr.mkEqM 100000 (.tInd "W" [.abs 0]) (.ind "W" 0 ⟨"MkW"⟩ [] [tagv (.abs 1)]) (.ind "W" 0 ⟨"MkW"⟩ [] [tagv (.abs 2)])) ==
  "ok Eq(Nat, σ1, σ2); absTy [E2, Nat, Nat] -> [E2, Nat, Nat, Nat]; eta [(0, MkE2(σ3))]"
#guard show' (Ochr.mkEqM 100000 (.tInd "W" [.abs 0]) (.ind "W" 0 ⟨"MkW"⟩ [] [.abs 1]) (.ind "W" 0 ⟨"MkW"⟩ [] [.abs 2])) ==
  "ok Eq(Tag(σ3), σ1, σ2); absTy [E2, Nat, Nat] -> [E2, Nat, Nat, Nat]; eta [(0, MkE2(σ3))]"
end GrowthProbe
