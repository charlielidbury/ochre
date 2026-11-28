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

**Since main's D119 (docs/31 D125, re-ruled (B′)) the split joins**: each world's arm ends with the
match's join (`joinCont` around the continuation, as a known constructor's arm does), so each leaf
holds `n ↦ ⊥`, as the reference's join drop leaves it (`moved`). The guards below that pinned the
split without a join were flipped to the new behaviour (the leaves, and the `[Join]` counts of
`T1`, `T4`, `T5`, `T6`, `T7`); the rest stay as they were.
-/

namespace Ochr.Meaning.Regress.TailJoin

open Ochr Ochr.Meaning Ochr.Meaning.Steps.Form
open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal)

def bodyP : Term := .matchNat (.var 0) .zero (.place (.proj 0 (.var 0)))

/-- `P`'s body start state (as `ColumnI.stI`: since main's D147/D148 and the model's half of R-dec, docs/31 D296, the
own-name slot `()` at `Unit` and Σ empty, so the same for `I` and `P`), in `checkFix`'s mode. -/
def stP : MState := { ColumnI.stI with typing := true, nextRecUid := 1 }

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
-- world `σ0 := Z`: `n ↦ ⊥` (the join dropped it; before D119 `n ↦ Z`), `Z` in flight
#guard leaves[0]!.2 == .zero && nAt leaves[0]!.1 == .bot && leaves[0]!.1.refs.length == 1
-- world `σ0 := S(σ1)`: `n ↦ ⊥` (before D119 `n ↦ S(⊥)`), `σ1` in flight
#guard leaves[1]!.2 == .abs 1 && nAt leaves[1]!.1 == .bot && leaves[1]!.1.refs.length == 1

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
lines are indented by its depth). Before main's D119 only the SPLIT of an unknown at the generic call
ran without a join; a tail match on a known value joins, at the generic call (`checkTailAt` →
`joinCont`) and in a callee's run (`runBodyCore` → `eval` in tail position → `joinEnds … tail` →
`joinDrop`). Since D119 the split joins too: each world's leaf has a `[Join]` line per place the
join drops there. -/

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
-- tail position, unknown scrutinee: split, and since D119 each world joins (body; λ body; a match in
-- an arm; under `let`; under `;`). Before D119 every `[Join]` count here was 0.
-- `T1`, `T4`, `T7`: `n` dropped in each of the two worlds
#guard ["T1", "T4", "T7"].all fun n => tcount n "[Join]" == 2 && tcount n "[Split]" == 2
-- `T6`: world `Z` drops `n` (the arm moved `y`); world `S` drops `y` and `n`
#guard tcount "T6" "[Join]" == 3 && tcount "T6" "[Split]" == 2
-- `T5`: four worlds (`n` split, then `k` in `n`'s world `Z`); `k` and `n` dropped in each of the three leaves
#guard tcount "T5" "[Join]" == 6 && tcount "T5" "[Split]" == 4
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
