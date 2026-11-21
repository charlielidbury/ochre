import Ochr.Meaning.Steps.ColumnIStart
import Ochr.Meaning.Regress.GenNeutralContent
import Ochr.Test

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

-- no pattern binding is pushed before a leaf: the arm `S m => m` reads the place `n.0`
#guard leaves.all fun (st, _) => st.env.size == 2 && st.env[1]!.binds.size == 2

/-! ## Where the checker joins at a match in tail position (docs/31 D125, the ruling's first step)

Counted from the derivation (`Config.derivation`: every `[Join]` drop, `[Split]` world; a callee's
lines are indented by its depth). Only the SPLIT of an unknown at the generic call runs without a join;
a tail match on a known value joins, at the generic call (`checkTailAt` → `joinCont`) and in a
callee's run (`runBodyCore` → `eval` in tail position → `joinEnds … tail` → `joinDrop`). -/

end Ochr.Meaning.Regress.TailJoin

open Ochr.Test

ochr TailProbe {
  def T1 (n : Nat) : Nat := match n { Z => Z, S m => m }
  def T2 (n : Nat) : Nat := let x = 1; match x { Z => Z, S m => m }
  def T3 (n : Nat) : Nat := T1(1)
  def T4 (n : Nat) : Nat := let f = (λ(x : Nat) : Nat => match x { Z => Z, S m => m }); f(n)
  def T5 (n : Nat) (k : Nat) : Nat := match n { Z => match k { Z => Z, S j => j }, S m => m }
  def T6 (n : Nat) : Nat := let y = Z; match n { Z => y, S m => m }
  def T7 (n : Nat) : Nat := Z; match n { Z => Z, S m => m }
  def T8 (n : Nat) : Nat := let r = match n { Z => Z, S m => m }; r
  def T9 (n : Nat) : Nat := let x = 1; let r = match x { Z => Z, S m => m }; r
}

namespace Ochr.Meaning.Regress.TailJoin

def tlines (name : String) : List String :=
  let r := Ochr.Test.runWith none "TailProbe" TailProbe { trace := true, derivation := true }
  match r.rows.find? (·.name == name) with
  | some row => row.trace.toList.filterMap fun | .line s => some s.trimLeft | _ => none
  | none => []

def tcount (name pfx : String) : Nat := ((tlines name).filter (·.startsWith pfx)).length

-- all accepted
#guard (Ochr.Test.runWith none "TailProbe" TailProbe {}).allAsExpected
-- tail position, unknown scrutinee: split, no join (body; λ body; a match in an arm; under `let`; under `;`)
#guard ["T1", "T4", "T6", "T7"].all fun n => tcount n "[Join]" == 0 && tcount n "[Split]" == 2
#guard tcount "T5" "[Join]" == 0 && tcount "T5" "[Split]" == 4
-- tail position, known scrutinee: joins (`joinCont`)
#guard tcount "T2" "[Join]" == 1 && tcount "T2" "[Split]" == 0
-- a callee's run in tail position (`T1(1)` runs `T1`'s body on `1`): joins
#guard tcount "T3" "[Join]" ≥ 1
-- not in tail position: an unknown scrutinee is closed off as a block (no split, no join at the
-- call); a known one joins
#guard tcount "T8" "[Split]" == 0
#guard tcount "T9" "[Join]" ≥ 1

/-- `P`'s body run as a callee's is (`runBodyCore`: untyped, in tail position) on `n ↦ v`. -/
def stK (v : Value) (tail typed : Bool) : MState :=
  let env := stP.env.set! 1 { binds := #[stP.env[1]!.binds[0]!, { stP.env[1]!.binds[1]! with val := v }] }
  { stP with env := env, tailNext := tail, typing := typed, cfg := { derivation := true } }

def runK (v : Value) (tail typed : Bool) := runMachine (Ochr.eval 1000 typed bodyP none) (stK v tail typed) 100000

def joinedK (v : Value) (tail typed : Bool) : Bool :=
  ((runK v tail typed).2.2.toList.any fun | .line s => s.trimLeft.startsWith "[Join] n dropped" | _ => false) &&
  match (runK v tail typed).1 with
  | .ok _ st => st.env[1]!.binds[1]!.val == .bot
  | _ => false

-- `eval` of the match on a known `n` joins (drops `n`) in tail position too, untyped (a callee's
-- run) or typed, as out of it
#guard [Value.zero, .succ .zero].all fun v => joinedK v true false && joinedK v true true && joinedK v false false

end Ochr.Meaning.Regress.TailJoin
