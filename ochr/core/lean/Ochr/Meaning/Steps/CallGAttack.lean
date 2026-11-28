import Ochr.Meaning.Steps.CallGuards
import Ochr.Meaning.Steps.MasterUntyped

/-!
# The general step for a call of a global, attacked at the checker's own states (lead29, 2026-11-22; docs/31 D200)

Before `Master.StepCallG` (`Steps/MasterCall.lean`) is proved, each of its parts is run on the checker. At the hole of a
real program (`At`: `a ↦ σa`, `c ↦ σc`, `b ↦ Z`) the calls the statement covers are run, typed and untyped:
- a callee whose body runs to a value (`Ip(Z)`, `Ip(c)`), one that closes off (`Pr(c)`), a borrow argument with a data
  result (`Inc(&b)`), a borrow result (`Kr(&b)`);
- for each, what `Kept` asks (the mode flags, the frames, the top readings) and what the post-call relation needs (no
  temporary left behind, no borrow left live, the lender's content).
Then the recursion: a definition whose own check runs a recursive call IN PLACE, whose untyped body makes a recursive
call that no [Rec] check sees (`RecAtk.H`): the general statement is false at that run unless the checker checks it.
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr CallAtk {
  def Ip (n : Nat) : Nat := S(n)
  def Pr (n : Nat) : Nat := match n { Z => Z, S m => m }
  def Inc (x : &Nat) : Unit := *x := S(clone(*x))
  def Kr (x : &Nat) : &Nat := x
  def At (a : Nat) (c : Nat) : Unit := (let b = Z; ?)
}

#guard_msgs (drop warning) in
ochr RecAtk {
  inductive BB := TT | FF
  reject def HAt (p : BB) (n : Nat) : Nat by n := match p {
    TT => match n { Z => Z, S m => match m { Z => (HAt(FF, Z); ?), S k => Z } },
    FF => match n { Z => (HAt(TT, S(S(S(Z)))); Z), S m => Z } }
  reject def H (p : BB) (n : Nat) : Nat by n := match p {
    TT => match n { Z => Z, S m => match m { Z => (H(FF, Z); Z), S k => Z } },
    FF => match n { Z => (H(TT, S(S(S(Z)))); Z), S m => Z } }
}

#guard_msgs (drop warning) in
ochr RetKindAtk {
  def Pick (n : Nat) (x : &Nat) (y : &Nat) : &Nat := match n { Z => x, S m => y }
  def Kc (n : Nat) (x : &Nat) (y : &Nat) : &Nat := Pick(n, x, y)
}

namespace Ochr.Meaning.Steps.Form.CallGAttack

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)

/-- The last state recorded at the hole of definition `nm` of a block. -/
def holeOf (blk : String) (prog : Ochr.Surface.Block) (nm : String) : MState :=
  let r := Ochr.Test.runWith (some Prelude) blk prog { recordStates := true } (located := true)
  match r.rows.find? (·.name == nm) with
  | some row => (row.trace.toList.filterMap fun
      | .state _ false _ st => some st | _ => none).getLast?.getD default
  | none => default

/-- The checker's state at `At`'s hole: the cells' frame (empty), then `At`'s own-name slot (`()` since main's D148), `a ↦ σa` (variable 2),
`c ↦ σc` (variable 1), `b ↦ Z` (variable 0). -/
def stH : MState := holeOf "CallAtk" CallAtk "At"

#guard stH.env.size == 2 && stH.env[1]!.binds.size == 4
#guard Value.exact stH.env[1]!.binds[3]!.val .zero
-- flipped by D147: `At` is not in Σ during its own check (it was 5, `At` included)
#guard stH.globals.length == 4

/-- A call run from the hole, typed or untyped, with the type wanted (as a `let`'s right-hand side). -/
def run (typed : Bool) (t : Term) : M (Value × Option Value) := do
  modify fun s => { s with wantTy := true }
  Ochr.eval 1000 typed t none

def callG (g : String) (as : List Term) : Term := .call (.const g) as false

/-- What `Kept` asks, and what `Out` reads of the frame the call returns to: the mode flags, the number of frames, the
top frame's readings, its temporaries and its bindings' number, as at the start. -/
def keptOk (st st' : MState) : Bool :=
  st'.headEval == st.headEval && st'.copying == st.copying && st'.inPlace == st.inPlace &&
  st'.env.size == st.env.size && DecideScope.topReadings st' == DecideScope.topReadings st &&
  st'.env.back!.temps.size == st.env.back!.temps.size && st'.env.back!.binds.size == st.env.back!.binds.size

/-! ## A body that runs to a value: `Ip(Z)`, `Ip(c)` -/

#guard isOk (run true (callG "Ip" [.zero])) stH 1000000
#guard isOk (run false (callG "Ip" [.zero])) stH 1000000
#guard Value.exact (outVal (run true (callG "Ip" [.zero])) stH 1000000).1 (.succ .zero)
#guard match (outVal (run true (callG "Ip" [.zero])) stH 1000000).2 with | some T => Value.exact T .tNat | _ => false
#guard keptOk stH (outSt (run true (callG "Ip" [.zero])) stH 1000000)
#guard keptOk stH (outSt (run false (callG "Ip" [.zero])) stH 1000000)
-- over an unknown: `S(σc)`, `c` moved (the argument's read)
#guard match (outVal (run true (callG "Ip" [.place (.var 1)])) stH 1000000).1 with | .succ (.abs _) => true | _ => false
#guard keptOk stH (outSt (run true (callG "Ip" [.place (.var 1)])) stH 1000000)
#guard (outSt (run true (callG "Ip" [.place (.var 1)])) stH 1000000).env[1]!.binds[2]!.val == .bot

/-! ## A body that closes off: `Pr(c)` -/

#guard isOk (run true (callG "Pr" [.place (.var 1)])) stH 1000000
#guard match (outVal (run true (callG "Pr" [.place (.var 1)])) stH 1000000).1 with | .sealed _ => true | _ => false
#guard keptOk stH (outSt (run true (callG "Pr" [.place (.var 1)])) stH 1000000)
#guard keptOk stH (outSt (run false (callG "Pr" [.place (.var 1)])) stH 1000000)

/-! ## A borrow argument with a data result: `Inc(&b)` -/

#guard isOk (run true (callG "Inc" [.borrow (.var 0)])) stH 1000000
#guard Value.exact (outVal (run true (callG "Inc" [.borrow (.var 0)])) stH 1000000).1 .unit
#guard keptOk stH (outSt (run true (callG "Inc" [.borrow (.var 0)])) stH 1000000)
-- `b` holds its final content, `S(Z)`, and no label is live after the call (the reference's `callOf` fixes the
-- argument's label at its final and takes it)
#guard Value.exact (outSt (run true (callG "Inc" [.borrow (.var 0)])) stH 1000000).env[1]!.binds[3]!.val (.succ .zero)
#guard Value.exact (outSt (run false (callG "Inc" [.borrow (.var 0)])) stH 1000000).env[1]!.binds[3]!.val (.succ .zero)

/-! ## A borrow result: `Kr(&b)` -/

#guard isOk (run true (callG "Kr" [.borrow (.var 0)])) stH 1000000
#guard match (outVal (run true (callG "Kr" [.borrow (.var 0)])) stH 1000000) with
  | (.borrow g _, some (.tRef _)) => g == stH.nextLoan + 1 | _ => false
#guard keptOk stH (outSt (run true (callG "Kr" [.borrow (.var 0)])) stH 1000000)
-- the lender `b` is a fill over the result's label (a mark), as the reference's `callOf` re-marks it
#guard match (outSt (run true (callG "Kr" [.borrow (.var 0)])) stH 1000000).env[1]!.binds[3]!.val with
  | .gloan g (.loan g') => g == g' && g == stH.nextLoan + 1 | _ => false

/-! ## A recursive call that ran in place before main's D135, whose body made a recursive call no [Rec] check saw

`HAt`'s own check, in the arm `p = TT`, `n = S(Z)`, makes the TYPED call `HAt(FF, Z)` ([Rec] passes: `Z` is a strict
subterm of the entry value `S(Z)`). Before main's D135 its arguments being known, the checker ran `HAt`'s body IN PLACE,
untyped, at `(FF, Z)`, where the body called `HAt(TT, S(S(S(Z))))` untyped with no [Rec] check (lead29's finding, docs/31
D200). Since main's D135 (merged by lead31, docs/31 D204) a call of a function whose check is under way closes off at
once (`Machine.underCheck`), so `HAt(FF, Z)` is closed off and no body of `HAt` runs during its check; the hole after it
is still reached once, with the same environment. The definition is rejected at the typed check of the inner call site
in the arm `p = FF`, `n = Z` (`H`, the same definition without the hole), as before. -/

/-- The environment `HAt`'s hole reports (its note, recorded only when the hole is reached). -/
def holeΩ : List (List (String × Option Value × Value)) :=
  let r := Ochr.Test.runWith (some Prelude) "RecAtk" RecAtk {} (located := true)
  match r.rows.find? (·.name == "HAt") with
  | some row => row.trace.toList.filterMap fun
      | .note _ _ (.hole _ Ω) => some Ω | _ => none
  | none => []

-- the hole is reached once (since D135 after the call closed off; before it, after the in-place run): `p ↦ TT`, `n ↦ S(Z)`
#guard holeΩ.length == 1
#guard holeΩ.all fun Ω =>
  Ω.any (fun (x, _, v) => x == "p" && (match v with | .ind "BB" 0 _ _ [] => true | _ => false)) &&
  Ω.any (fun (x, _, v) => x == "n" && Value.exact v (.succ .zero))

/-- The verdict on one definition of `RecAtk`. -/
def recVerdict (nm : String) : String :=
  match ((Ochr.Test.runWith (some Prelude) "RecAtk" RecAtk {} (located := false)).rows.find? (·.name == nm)) with
  | some r => match r.verdict with
    | Ochr.Verdict.accepted => ""
    | Ochr.Verdict.rejected m _ => m
    | Ochr.Verdict.undecided _ => "?"
  | none => "?"

-- `H` is rejected at the typed check of the inner call site, in the arm `p = FF`, `n = Z`, whose entry value has no strict
-- subterm: the same call the in-place run made unchecked
#guard (recVerdict "H").startsWith "[Rec] at H(TT, 3)"

/-! ## `RetKindG` on instances (the lead's check before building on it)

A callee returning one of two borrow arguments (`Pick`) and a callee whose body ends in a call that closes off (`Kc`,
at the generic `n`) are accepted: in the model their bodies return a parameter's borrow (its label) or `callOf`'s
fresh label (`.ref` branch), so their results are labelled, at a codomain written `&` (by reading: `fixG` is not
computable). A codomain that is a type-function call returning a borrow type cannot arise: `&` in a term position is a
borrow in the surface ("Nat is not a place"), and the core checker rejects a type function whose body is the type
`&Nat` (`defRT`, `refTopOk`), so "written `&`" is exactly "a borrow codomain". -/

#guard (Ochr.Test.runWith (some Prelude) "RetKindAtk" RetKindAtk {} (located := false)).allAsExpected

def defRT : Def := { name := "RT", hs := [⟨"n"⟩], doms := [.nat], cod := .sort 1, body := .ref .nat }
#guard !isOk (checkDef defRT) {} 100000

end Ochr.Meaning.Steps.Form.CallGAttack
