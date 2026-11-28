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
-- a non-tail match on another argument: on main a stuck block taking the definition's own binding as a parameter at its
-- declared type, applied to the global (D232). FLIPPED on `spine-exp-block` (exp-block-text, which builds main's D139 in):
-- the block is a sealed TEXT whose cells hold the captured values and whose match names the function under check only as
-- the head of a call, by its global; no cell holds the function
#guard (holes "MB0").map (valOf · "r") ==
  ["⌈let m = σ0; let n = σ1; match m { Z => 0, S _ => match n { Z => 0, S _ => MB0(m.0, n.0) } }⌉"]
#guard (holes "MB").map (valOf · "r") ==
  ["⌈let m = σ0; let n = S(σ2); match m { Z => MB(0, n.0), S _ => MB((fix _ (n : Nat) : Nat := S(n))(0), n.0) }⌉"]
-- the same with a returned borrow: the lender's fill holds the block's text, its cell `x_0` a borrow of the fill's own
-- cell `c1`
#guard (holes "TBB").map (valOf · "x") ==
  ["borrow_0 S(⌈let c1 = σ2; let r = (let b = σ0; let x_0 = &c1; match b { TT => TBB(TT, &*x_0), FF => TBB(FF, &*x_0) }); *r := loan_8; c1⌉)"]

-- a block is checked only at its captured values (not a recursion matter): `NT`'s block takes `n` WHOLE and reads its
-- predecessor, which the captured `S(σ2)` has and `0` has not. On main the model read the block as a closure asked at
-- every value of its parameters (`err`, D233); on `spine-exp-block` the text binds `n` to `S(σ2)` itself and the model's
-- `.block` clause runs the match there only (`Steps/BlockTextNTr`). `NU` takes `n` by borrow and writes it in one arm
#guard (holes "NT").map (valOf · "r") ==
  ["⌈let n = S(σ2); let m = σ1; match m { Z => clone(n), S _ => clone(n.0) }⌉"]
#guard (holes "NU").map (valOf · "r") ==
  ["⌈let c1 = S(σ2); let n = &c1; let m = σ1; match m { Z => *n := 0; 0, S _ => clone((*n).0) }⌉"]

end Ochr.Meaning.Steps.Form.RecDescAtk
