import Ochr.Meaning.Steps.UnderCheckAttack
import Ochr.Meaning.Steps.StageBlockCE

/-!
# `RecDescG` and the knot's stage contexts, attacked on the checker (lead37; docs/31 D232)

The brief's four programs for the fixpoint equation's descent clause (`RecDescG`, `Steps/UnderCheck.lean`), at the holes
of each definition's own check: what the leaf holds and through which values it depends on the definition being
checked (`R` is `ColumnR`'s; `AH`, recursing on its second argument while the first grows, is `UnderCheckAttack`'s):
- `MT`, a recursive call under a TAIL match on another argument: the split runs the arms; the leaf holds a sealed program
  whose head call is the definition (`⌈MT(σ2, σ3)⌉`), as for `R` and `AH`.
- `TB`, returning a borrow of its argument: the closed-off call returns `borrow_2 ⌈…; *r⌉` and fills the argument's
  lender with `⌈…; *r := loan_2; c1⌉`, both headed by `TB`.
- `MB`, `MB0`, a recursive call under a NON-tail match on another argument, and `TBB`, the same returning a borrow: the
  match is closed off as a stuck block that takes the definition's OWN BINDING as a parameter at its declared function
  type (`MB0 : Π(m : Nat) (n : Nat). Nat`), calls it at a part of another parameter (`MB0(m.0, n.0)`), and is applied to
  the global itself. So the leaf depends on the definition through a sealed block's ARGUMENT, not only through sealed
  programs headed by it (docs/31 D213's model fact (b) is too narrow), and the block's function ranges over every value
  of its captures.

THE OBSTRUCTION (docs/31 D232): under the knot's context `K_b` (`MemBelow`: the definition means its stage-`b` closure at
the WEAKENED type) the reference reads `MB0`'s leaf `r` by applying the block's closure, whose first parameter has the
DECLARED type, to the stage closure. At bound `0` (the knot's first step, which reaches this leaf at every assignment
with `n = 0`) that call fails, kernel-checked (`StageBlock.callOf_stage0`: the stage-`0` closure is not a member of the
declared type, `stage0_not_mem`), so `r` means `err` while the reference's direct run of the body gives `0`: the
simulation is false there, for an accepted definition (`MB0r`, which returns `r`). Retyping the block's parameter at the
weakened type, or calling the global by name inside the block, does not help: the block, a function of every value of
its captures, then calls the stage closure above its bound, where it gives `()` at `Unit` (`stage0_apply`), against the
block's codomain `Nat`.
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr RecDescAtk {
  inductive BB := TT | FF
  def MB (m : Nat) (n : Nat) : Nat by n := match n { Z => Z, S k => (let r = (match m { Z => MB(Z, k), S p => MB(S(Z), k) }); ?) }
  def MT (m : Nat) (n : Nat) : Nat by n := match m { Z => Z, S p => match n { Z => Z, S k => (let r = MT(p, k); ?) } }
  def TB (x : &Nat) : &Nat by x := match *x { Z => x, S p => (let r = TB(&p); ?) }
  def TBB (b : BB) (x : &Nat) : &Nat by x := match *x { Z => x, S p => (let r = (match b { TT => TBB(TT, &p), FF => TBB(FF, &p) }); ?) }
  def MB0 (m : Nat) (n : Nat) : Nat by n := (let r = (match m { Z => Z, S p => match n { Z => Z, S k => MB0(p, k) } }); ?)
  def MB0r (m : Nat) (n : Nat) : Nat by n := (let r = (match m { Z => Z, S p => match n { Z => Z, S k => MB0r(p, k) } }); r)
  def NT (n : Nat) (m : Nat) : Nat := match n { Z => Z, S p => (let r = (match m { Z => clone(n), S q => clone(p) }); ?) }
  def NTr (n : Nat) (m : Nat) : Nat := match n { Z => Z, S p => (let r = (match m { Z => clone(n), S q => clone(p) }); r) }
  def NU (n : Nat) (m : Nat) : Nat := match n { Z => Z, S p => (let r = (match m { Z => (n := Z; Z), S q => clone(p) }); ?) }
}

namespace Ochr.Meaning.Steps.Form.RecDescAtk

open Ochr Ochr.Meaning

/-- Every environment a hole of definition `nm` reports. -/
def holes (nm : String) : List (List (String × Option Value × Value)) :=
  let r := Ochr.Test.runWith (some Prelude) "RecDescAtk" RecDescAtk {} (located := true)
  match r.rows.find? (·.name == nm) with
  | some row => row.trace.toList.filterMap fun
      | .note _ _ (.hole _ Ω) => some Ω | _ => none
  | none => []

/-- The innermost binding named `x` at a hole. -/
def valOf (Ω : List (String × Option Value × Value)) (x : String) : String :=
  match Ω.reverse.find? (·.1 == x) with
  | some (_, _, v) => toString v
  | none => "?"

-- every definition is accepted (`MB0r`, which returns the block's value, among them)
#guard ((Ochr.Test.runWith (some Prelude) "RecDescAtk" RecDescAtk {} (located := false)).allAsExpected)
-- a tail match on another argument: a sealed program headed by the definition
#guard (holes "MT").map (valOf · "r") == ["⌈MT(σ2, σ3)⌉"]
-- a returned borrow: the result and the lender's fill are headed by the definition, the fill holding the result's hole
#guard (holes "TB").map (valOf · "r") == ["borrow_2 ⌈let c1 = σ1; let r = TB(&c1); *r⌉"]
#guard (holes "TB").map (valOf · "x") == ["borrow_0 S(⌈let c1 = σ1; let r = TB(&c1); *r := loan_2; c1⌉)"]
-- a non-tail match on another argument: a stuck block taking the definition's own binding as a parameter at its
-- declared type, calling it at a part of another parameter, applied to the global. UNTIL MAIN'S D139 (ruled on D232:
-- a sealed block's text names the function under check by its global; its binding of itself is never a block's
-- parameter): the merge flips these three guards
#guard (holes "MB0").map (valOf · "r") ==
  ["⌈(fix _ (MB0 : Π(m : Nat) (n : Nat). Nat) (m : Nat) (n : Nat) : Nat := match m { Z => 0, S _ => match n { Z => 0, S _ => MB0(m.0, n.0) } })(MB0, σ0, σ1)⌉"]
#guard (holes "MB").map (valOf · "r") ==
  ["⌈(fix _ (MB : Π(m : Nat) (n : Nat). Nat) (m : Nat) (n : Nat) : Nat := match m { Z => MB(0, n.0), S _ => MB((fix _ (n : Nat) : Nat := S(n))(0), n.0) })(MB, σ0, S(σ2))⌉"]
-- the same with a returned borrow: the lender's fill applies the block, the global passed at its declared type
#guard (holes "TBB").map (valOf · "x") ==
  ["borrow_0 S(⌈let c1 = σ2; let r = (fix _ (TBB : Π(b : BB) (x : &Nat). &Nat) (b : BB) (x_0 : &Nat) : &Nat := match b { TT => TBB(TT, &*x_0), FF => TBB(FF, &*x_0) })(TBB, σ0, &c1); *r := loan_8; c1⌉)"]

-- a block is checked only at its captured values (not a recursion matter): `NT`'s block takes `n` WHOLE and reads its
-- predecessor, which the captured `S(σ2)` has and `0` has not (`StageBlock.step_pred_zero`, `closureL_err_of_none`:
-- the model's closure of this block, asked at every value of its parameters, is `err`, so today the model reads the
-- leaf of the accepted `NTr` as `err`); `NU` takes `n` by borrow and writes it in one arm
#guard (holes "NT").map (valOf · "r") ==
  ["⌈(fix _ (n : Nat) (m : Nat) : Nat := match m { Z => clone(n), S _ => clone(n.0) })(S(σ2), σ1)⌉"]
#guard (holes "NU").map (valOf · "r") ==
  ["⌈let c1 = S(σ2); (fix _ (n : &Nat) (m : Nat) : Nat := match m { Z => *n := 0; 0, S _ => clone((*n).0) })(&c1, σ1)⌉"]

end Ochr.Meaning.Steps.Form.RecDescAtk
