import Ochr.Meaning.Steps.Statements
import Ochr.Examples.Nat
import Ochr.Examples.List

/-!
# `movedPlace` can return a parent through which the place now exists (built)

docs/31 D41 (fifth lead, 2026-11-21). `Machine.movedPlace q` re-roots the parent `p` of a missing
place `q` first. When a strict prefix of `p` holds a live fill, that inner call accesses the prefix
whole, which ends the borrow and gives the prefix its content back, and then asks for `p` again,
which now exists. The outer call does not ask for `q` again: if `p` holds a constructor value (no
fill, no unknown, no sealed program) it returns `p`, though `q` exists through it. Its other branches
(a filled parent, an unknown, a sealed program) all ask for `q` again.

On the checker's own state at the end of `LentAt`'s first arm, where `c` is lent whole to `rr`
(`c = lent_2 loan_2`, `rr = borrow_2 MkOut(MkIn(σ0, σ1), σ2)`), `movedPlace((c.0).0)` returns `c.0`,
which then holds `MkIn(σ0, σ1)`, and `(c.0).0` exists (`#guard`s below). So the drop's statement
(`movedPlace_step_stmt`: the place returned exists, or is a prefix holding `⊥` or `⋆`) is false at
this state for a place at the join's grain, and `MovedPlace.reRoot_created` is its false leaf.

The join does not reach it here: the arm that lends `c` uses `c` whole, so the join moves `c` whole
(K1(g)) and `LentRead` is rejected while `NotLentRead`, the same program without the lending, is
accepted (dropping only `(c.0).0`). A lending before the match is ended by the entry's access of the
captured place. No accepted program is known on which the join reaches the case.
-/

open Ochr.Test

ochr ReRootExists uses Nats, Lists {
  inductive In := MkIn(a : List(Nat), b : List(Nat))
  inductive Out := MkOut(i : In, z : List(Nat))
  def Whole (x : &Out) : &Out := x
  def LentAt (xs : List(Nat)) (ys : List(Nat)) (zs : List(Nat)) (us : List(Nat)) (vs : List(Nat)) (ws : List(Nat)) : Unit := (
    let k = Z;
    let c = MkOut(MkIn(xs, ys), zs);
    let e = MkOut(MkIn(us, vs), ws);
    let rr = Whole(&e);
    match k { Z => (rr := Whole(&c); ()), S m => (let a = (c.0).0; ()) };
    ())
  -- the arm that lends `c` uses it whole: the join moves `c` whole (K1(g))
  reject def LentRead (xs : List(Nat)) (ys : List(Nat)) (zs : List(Nat)) (us : List(Nat)) (vs : List(Nat)) (ws : List(Nat)) : List(Nat) := (
    let k = Z;
    let c = MkOut(MkIn(xs, ys), zs);
    let e = MkOut(MkIn(us, vs), ws);
    let rr = Whole(&e);
    match k { Z => (rr := Whole(&c); ()), S m => (let a = (c.0).0; ()) };
    (c.0).1)
  -- control: without the lending only `(c.0).0` is moved
  def NotLentRead (xs : List(Nat)) (ys : List(Nat)) (zs : List(Nat)) (us : List(Nat)) (vs : List(Nat)) (ws : List(Nat)) : List(Nat) := (
    let k = Z;
    let c = MkOut(MkIn(xs, ys), zs);
    let e = MkOut(MkIn(us, vs), ws);
    let rr = Whole(&e);
    match k { Z => (rr := Whole(&e); ()), S m => (let a = (c.0).0; ()) };
    (c.0).1)
}

namespace Ochr.Meaning.Regress.ReRootExists
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- The value bound to the variable named `x` in the top frame. -/
def valOf (st : MState) (x : String) : Option Value :=
  (st.env.back?.bind fun fr => fr.binds.toList.find? (·.hint.name == x)).map (·.val)

/-- `c` is lent whole, a mark over its loan, and `rr` holds the borrow. -/
def lentWhole (st : MState) : Bool :=
  match valOf st "c", valOf st "rr" with
  | some (.gloan l (.loan m)), some (.borrow k _) => l == m && m == k
  | _, _ => false

/-- The checker's state at the end of `LentAt`'s first arm (the last recorded state with `c` lent). -/
def armSt : MState :=
  let r := Ochr.Test.runWith (some Prelude) "ReRootExists" ReRootExists { recordStates := true } (located := true)
  match r.rows.find? (·.name == "LentAt") with
  | some row => ((row.trace.toList.filterMap fun
      | .state _ true _ st => some st | _ => none).filter lentWhole).getLast?.getD default
  | none => default

#guard lentWhole armSt

/-- `c`'s variable index in the top frame. -/
def cIdx : Nat :=
  match armSt.env.back? with
  | some fr => fr.binds.size - 1 - ((fr.binds.toList.findIdx? (·.hint.name == "c")).getD 0)
  | none => 0

def c0 : Place := .proj 0 (.var cIdx)
def c00 : Place := .proj 0 c0

-- before: neither `c.0` nor `(c.0).0` exists (`c` holds the mark over its loan)
#guard (ckContent armSt.env c0).isNone && (ckContent armSt.env c00).isNone

/-- `movedPlace((c.0).0)` on the arm's state: the place returned and the state after. -/
def after : Option (Place × MState) :=
  match (runMachine (Ochr.movedPlace 1000 c00) armSt 100000).1 with
  | .ok p st => some (p, st)
  | _ => none

-- it returns `c.0` ...
#guard match after with | some (p, _) => p.steps.1 == cIdx && p.steps.2.length == 1 | none => false
-- ... which holds a constructor value of `In`, and `(c.0).0` now exists
#guard match after with
  | some (_, st) => (match ckContent st.env c0 with | some (.ind "In" 0 _ _ _) => true | _ => false) &&
      (ckContent st.env c00).isSome
  | none => false

end Ochr.Meaning.Regress.ReRootExists
