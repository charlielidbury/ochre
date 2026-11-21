import Ochr.Meaning.Steps.ColumnIStart
import Ochr.Meaning.Regress.GenNeutralContent

/-!
# A match in tail position: the checker does not join, the reference does (lead14, 2026-11-21; docs/31 D125)

`def P (n : Nat) : Nat := match n { Z => Z, S m => m }`, checked at its generic call: the body's
match is in tail position, where `checkTail` SPLITS the unknown `σ0` into two worlds and runs the
return continuation at each arm's leaf, with no join (`Machine.checkTailAt`'s `.matchNat` case: "a
match there is split at the generic call, never closed off as a block"). Asserted below by running
`checkTail` on the body from its start state with a continuation that records each leaf:

- world `σ0 := Z`: the leaf holds `n ↦ Z`, the value `Z` in flight;
- world `σ0 := S(σ1)`: the leaf holds `n ↦ S(⊥)` (the arm moved the predecessor), `σ1` in flight.

The reference (`Run.lean`, `runT`'s `.matchNat` clause) runs one arm and THEN drops at the join,
in tail position too (it skips only the [Entry] of a non-tail match, `matchEntry K φ (!tl)`):
`joinDrop K φ entry (.matchNat p z u)`, which moves every place `Decisions.joinMoves` names. Aligned
with the checker's `Decide.jdMoves`, that is `n` WHOLE (asserted below: the `S` arm moves `n.0`, a
number's predecessor, which the join's grain takes as the whole number). So at the leaf the
reference holds `n ↦ moved` where the checker holds `n ↦ Z` (or `S(⊥)`): the two meanings differ at
`n`, and `Rel` (hence `Out`, the conclusion of every step in `Steps/Form.lean`) cannot hold between
the checker's leaf and the reference's end state. The results agree (`0`, or the predecessor), and the
frame that differs is popped right after on both sides.
-/

namespace Ochr.Meaning.Regress.TailJoin

open Ochr Ochr.Meaning Ochr.Meaning.Steps.Form
open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal)

def bodyP : Term := .matchNat (.var 0) .zero (.place (.proj 0 (.var 0)))

/-- `P`'s body start state (as `ColumnI.stI`, `I` renamed `P`), in `checkFix`'s mode. -/
def stP : MState :=
  let selfP : Binding := { ColumnI.selfB with hint := ⟨"P"⟩, val := .gfn "P" }
  let gP : GDef := { name := "P", ty := ColumnI.piNat, fn? := some (.fix ⟨"P"⟩ [⟨"n"⟩] [.nat] .nat none bodyP), val := .gfn "P" }
  let rc : RecCtx := { fn := .gfn "P", entries := #[some 0], cands := [], uid := 0 }
  let env : Env := #[{}, { binds := #[selfP, ColumnI.nB] }]
  { ColumnI.stI with env := env, globals := [gP], typing := true, recStack := [rc], nextRecUid := 1 }

/-- A return continuation that records the leaf it is run at (the state, the value and its type). -/
def kRec (v T : Value) : M Unit := do
  let s ← get
  modifyThe (Array LogEntry) (·.push (.state default true (some (v, some T)) s))

def leaves : List (MState × Value) :=
  (runMachine (Ochr.checkTail 1000 bodyP kRec) stP 100000).2.2.toList.filterMap fun
    | .state _ _ (some (v, _)) st => some (st, v)
    | _ => none

def nAt (st : MState) : Value := st.env[1]!.binds[1]!.val

-- the run succeeds, with two leaves, one per world
#guard isOk (Ochr.checkTail 1000 bodyP kRec) stP 100000
#guard leaves.length == 2
-- world `σ0 := Z`: `n ↦ Z`, `Z` in flight
#guard leaves[0]!.2 == .zero && nAt leaves[0]!.1 == .zero && leaves[0]!.1.refs.length == 1
-- world `σ0 := S(σ1)`: `n ↦ S(⊥)`, `σ1` in flight
#guard leaves[1]!.2 == .abs 1 && nAt leaves[1]!.1 == .succ .bot && leaves[1]!.1.refs.length == 1

-- the join of the match moves `n` whole (what the reference's tail match drops)
def scP : MState := scopeState ColumnI.stI [.other, .pi .other]
#guard match outVal (withLive true (Ochr.jdMoves 100 [] [] bodyP [])) scP 1000 with
  | [.var 0] => true
  | _ => false
#guard isOk (withLive true (Ochr.jdMoves 100 [] [] bodyP [])) scP 1000

end Ochr.Meaning.Regress.TailJoin
