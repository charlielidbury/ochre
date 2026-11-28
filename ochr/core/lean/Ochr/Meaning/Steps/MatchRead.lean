import Ochr.Meaning.Steps.MatchAttack

/-!
# The split at the end of a body: the eight unread facts read against the code and attacked (lead42, 2026-11-28;
docs/31 D250 on)

`Steps/MasterMatch.lean` derives the split at the end of a body (`tStepMatchNat_of`) from twelve named facts; eight had
never been read against the code they are about. Each is read here clause by clause against `Machine.lean` (`checkTail`,
`checkTailAt`'s `.matchNat`, `enterWorld`/`inWorld`/`exitWorld`, `refine`, `freshAbsR`, `generalizeNeutral`, `joinCont`,
`staticJoin`, `movedPlace`, `dropAtJoin`) and `Run.lean` (`runT`'s `.matchNat`, `tagOf`, `SState.access`, `joinDrop`), and
attacked by programs run on the real checker. What is found, in the order of docs/31 D250:

* **The continuation's counters leak into the next world** (`A1` with `kCheck`): `exitWorld` keeps the counter of
  unknowns of the state the previous world ENDED in, which includes the continuation's run at that world's leaf. `TailAt`
  asks of a continuation only that it grows the tables (`GrowsM`), which a continuation that raises the counter of
  unknowns without typing one meets; after it, the second world's fresh field is named above the typed unknowns, so the
  second world's leaf fails `Pre` (`WF6`: the counter is the number of typed unknowns). So `TStepMatchNat` is FALSE as
  stated at such a continuation (every assignment that selects the second world has no leaf). Repair: the continuation
  also keeps the tables' invariant (`TabInv`), which machine code does.
* **The join rewrites the arm's result in flight** (`J4`, `J4a`): `joinCont`'s drops run with the result pushed as a
  temporary; `movedPlace` may generalise and η-refine a sealed program of a one-constructor type, and the substitution
  reaches the temporary, so the continuation receives another value (`MkBox(σ3)`) than the arm returned (`⌈G(σ0)⌉`), equal
  in meaning under the extension. `JoinContG` as stated runs the continuation at the arm's own value: FALSE. Repair: the
  value handed on is existential, its meaning, type and label kept.
* **The editor's located mode** (`locSt`): `checkTail` enters through `locatedTail`, which, where the editor's table holds
  the match, sets `locs.here` (and `locs.arm`) before the scrutinee's access; a continuation that reads `locs.here`
  succeeds at the run's leaves and fails at the end of every chain from the state itself. `TailMatchNatInv` as stated
  (the chain from `st`): FALSE there, as `TailOtherInv` was (machine9). Repair: the chain from a state with the same kernel,
  mode, tail flags and goal.
* **A later world's base** (`WorldBase`): the base of the second world is `exitWorld` of ANY state `cur`; with `cur`'s
  counter below the snapshot's, the fresh field reuses a name in use (`exitBase`), so `WorldRefineG` as stated is FALSE.
  Repair: `cur` grew from the snapshot and keeps the tables' invariant (`TailMatchNatInv` supplies it).
* **A fault of the checker, an incompleteness** (`TB`, `TB2`): a match on a field place at the end of a body is rejected
  ("no such place b.0"), the same match not at the end accepted: `checkTailAt` does not name a field step by a match
  first (`projIn`/`projMatch`), as `evalMatch` does.
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr MatchRd {
  inductive Box := MkBox(v : Nat)
  inductive Two := Lo | Hi
  inductive BoxT := MkBT(v : Two)
  def G (n : Nat) : Box := match n { Z => MkBox(Z), S(m) => MkBox(Z), }
  -- the arm `Z` returns the sealed program `b` holds; the arm `S` moves `b.v`, so world `Z`'s join drops `b.v`
  def J4 (n : Nat) (k : Nat) : Box := (let b = G(clone(n)); match k { Z => G(n), S(j) => match b { MkBox(w) => (let z = w; MkBox(z)), }, })
  -- the same code without the match: the value is the sealed program
  def J4a (n : Nat) (k : Nat) : Box := (let b = G(clone(n)); G(n))
  -- a split at the end of a body (as `MatchAtk.A1`)
  def A1 (x : Nat) (y : Nat) (n : Nat) : Nat := match n { Z => x, S(m) => y, }
  -- a match on a field place: rejected at the end of a body, accepted elsewhere (an incompleteness)
  reject def TB (b : Box) : Nat := match b.0 { Z => 0, S(m) => 1, }
  def TB2 (b : Box) : Nat := (let r = match b.0 { Z => 0, S(m) => 1, }; r)
  reject def TBi (b : BoxT) : Nat := match b.0 { Lo => 0, Hi => 1, }
  def TBi2 (b : BoxT) : Nat := (let r = match b.0 { Lo => 0, Hi => 1, }; r)
}

namespace Ochr.Meaning.Steps.MatchRd

open Ochr Ochr.Meaning
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)

-- every verdict as expected
#guard ((Ochr.Test.runWith (some Prelude) "MatchRd" MatchRd {} (located := false)).allAsExpected)
-- `TB` is rejected at the field place, which `checkTailAt` reads as it stands
#guard ((Ochr.Test.runWith (some Prelude) "MatchRd" MatchRd {} (located := false)).rows.find? (·.name == "TB")).any
  fun r => match r.verdict with | .rejected m _ => (m.splitOn "no such place b.0").length > 1 | _ => false

/-- The resolved body of a definition of the block. -/
def bodyOf (name : String) : Term :=
  match MatchRd.decls.find? (·.name == name) with
  | some d => match Ochr.Surface.runResolve MatchRd.decls d 100000 with
    | (.ok (.ok (.defn df)), _) => df.body
    | _ => .zero
  | none => .zero

/-- The checker's recorded state at the entry of a definition's body (its frame: the function's binding of itself, then
`np` parameters). -/
def entryOf (nm : String) (np : Nat) : Option MState :=
  let r := Ochr.Test.runWith (some Prelude) "MatchRd" MatchRd { recordStates := true } (located := true)
  match r.rows.find? (·.name == nm) with
  | some row => (row.trace.toList.filterMap fun e => match e with
      | .state _ _ _ st => if st.env.size == 2 && st.env[1]!.binds.size == np + 1 then some st else none
      | _ => none).head?
  | none => none

instance : Inhabited (Value → Value → M Unit) := ⟨fun _ _ => pure ()⟩

/-! ## 1. The continuation's counters leak into the next world (`TailAt`'s hypothesis on continuations)

`A1`'s body splits `n ↦ σ2` (counter 3, three typed unknowns). `kCheck b` fails exactly where the top frame names an
unknown with no type (`corrupt`: the checker's form of `WF6`'s first clause at the top frame), and otherwise, if `b`,
raises the counter of unknowns by one without typing an unknown, which `GrowsM` allows. With `b = false` no leaf is
corrupt; with `b = true` the second world's leaf is (world `Z`'s leaf ran the continuation first, `exitWorld` kept its
counter, the fresh `σ'` of world `S` is `σ4` with three, then four, typed unknowns). -/

/-- The top frame names an unknown with no type. -/
def corrupt (st : MState) : Bool :=
  st.env[st.env.size - 1]!.binds.toList.any fun b => b.val.anyAtom fun | .abs i => decide (i ≥ st.absTy.size) | _ => false

/-- Fails at a corrupt state; otherwise raises the counter of unknowns if `bump`. -/
def kCheck (bump : Bool) : Value → Value → M Unit := fun _ _ => do
  let st ← get
  if corrupt st then err "corrupt"
  if bump then modify fun s => { s with nextAbs := s.nextAbs + 1 }

#guard (entryOf "A1" 3).any fun st => st.nextAbs == 3 && st.absTy.size == 3
#guard (entryOf "A1" 3).any fun st => isOk (Ochr.checkTail 1000 (bodyOf "A1") (kCheck false)) st 100000
#guard (entryOf "A1" 3).any fun st => !isOk (Ochr.checkTail 1000 (bodyOf "A1") (kCheck true)) st 100000

/-! ## 2. The join rewrites the arm's result in flight (`JoinContG`)

In `J4`'s world `Z` the arm returns `⌈G(σ0)⌉` (as `J4a`, the same code with no match, hands its continuation), and `b`
holds the same sealed program; the join drops `b.v` (the arm `S` moves it), `movedPlace` generalises `b`'s content
(a one-constructor type) and η-refines it, and the substitution reaches the result pushed as a temporary: the
continuation receives `MkBox(σ3)`. -/

/-- The continuation's value: a sealed program; a constructor value over an unknown. -/
def isSealed : Value → Bool | .sealed _ => true | _ => false
def isBoxAbs : Value → Bool | .ind _ _ _ _ [.abs _] => true | _ => false
def kWhen (P : Value → Bool) : Value → Value → M Unit := fun v _ => if P v then pure () else err "k"

-- `J4a`: the arm's code alone hands its continuation the sealed program
#guard (entryOf "J4a" 2).any fun st => isOk (Ochr.checkTail 1000 (bodyOf "J4a") (kWhen isSealed)) st 100000
-- `J4`: no leaf hands its continuation a sealed program; every leaf hands it `MkBox(σ)`
#guard (entryOf "J4" 2).any fun st => !isOk (Ochr.checkTail 1000 (bodyOf "J4") (kWhen isSealed)) st 100000
#guard (entryOf "J4" 2).any fun st => isOk (Ochr.checkTail 1000 (bodyOf "J4") (kWhen isBoxAbs)) st 100000
-- in world `Z` the join made a generalisation record (the continuation of world `Z` is the first one to run)
#guard (entryOf "J4" 2).any fun st =>
  isOk (Ochr.checkTail 1000 (bodyOf "J4") (fun _ _ => do if (← get).neutrals.length == 1 then pure () else err "k")) st 100000

/-! ## 3. The editor's located mode (`TailMatchNatInv`)

`locSt t st`: `st` with an editor table holding the match `t` itself and `locs.here` unset. `checkTail` enters `t`
through `locatedTail`, whose `locatedCore` sets `locs.here` to `t`'s range before the scrutinee's access; the arms are
not in the table, so their entries keep it. A continuation that needs `locs.here` succeeds at the run's leaves, and fails
at the end of world `Z`'s chain from `st` itself (the access, the refinement, the join's continuation, the arm), which is
what `TailMatchNatInv` as stated asserts exists. -/

def locSt (t : Term) (st : MState) : MState :=
  { st with depth := 0,
            locs := { table := ({} : Std.HashMap USize Loc).insert (termAddr t) ⟨7, 9⟩, keep := #[t], on := true,
                      here := none } }

def kHere : Value → Value → M Unit := fun _ _ => do if (← get).locs.here.isSome then pure () else err "k"

/-- World `Z`'s chain from `st` at fuel `m + 2`: the access, `σ := Z`, the join's continuation, the arm. -/
def chainZ (m : Nat) (t : Term) (k : Value → Value → M Unit) (st : MState) : Bool :=
  match t with
  | .matchNat p z _ =>
    let stA := outSt (do Ochr.natScrutinee m p; Ochr.accessPath m p; Ochr.accessNeutralHead m p) st 100000
    match outVal (Ochr.matchContent p) stA 100000 with
    | .abs σ =>
      let stW := outSt (Ochr.refine m σ .zero) stA 100000
      isOk (Ochr.checkTail m z (outVal (Ochr.joinCont m t k) stW 100000)) (outSt (Ochr.joinCont m t k) stW 100000) 100000
    | _ => false
  | _ => false

#guard (entryOf "A1" 3).any fun st => let t := bodyOf "A1"; isOk (Ochr.checkTail 1000 t kHere) (locSt t st) 100000
#guard (entryOf "A1" 3).any fun st => let t := bodyOf "A1"; !chainZ 998 t kHere (locSt t st)
-- the chain itself is the run's at a continuation that reads nothing of the editor
#guard (entryOf "A1" 3).any fun st => let t := bodyOf "A1"; chainZ 998 t (fun _ _ => pure ()) (locSt t st)

/-! ## 4. A later world's base (`WorldRefineG`'s `WorldBase`)

The second world's base is `exitWorld` of the state the first world ended in; `WorldBase` lets that state be ANY state.
From one whose counter of unknowns is below the snapshot's, the base's fresh field reuses `σ0`, a name in use (`x ↦ σ0`). -/

def exitBase (stA cur : MState) : MState := outSt (Ochr.exitWorld ⟨stA⟩) cur 100000

#guard (entryOf "A1" 3).any fun st =>
  outVal (Ochr.freshAbsR 10 .tNat) (exitBase st { st with nextAbs := 0 }) 100000 == 0 &&
    st.env[1]!.binds[1]!.val == .abs 0

end Ochr.Meaning.Steps.MatchRd
