import Ochr.Test

/-! # Nat: in-place addition, the paper's first example

`Nat` and `Unit` are built into the checker. This library holds in-place addition `AddM` and
pure addition `Add`, defined by running `AddM` on a copy, with the first proof, that adding zero
in place does nothing (`AddMZero`), and that adding a successor adds one (`AddS`); and the
returned borrow `TailM`.

A block may use other blocks: `ochr Numbers uses Nats { … }` checks `Nats`' declarations
first, then its own, in one namespace (a clash is an error). Only declarations that a used
block expects to be accepted, and that are accepted, are visible to its users; they are
checked again in each block that uses them, so switching a rule off re-decides them there too,
and each one's verdict is asserted in its home block. `uses` is transitive. The library is one
block per file, each using only what it needs (`Examples/README.md` lists them).

Defined in RULES §1 (syntax), §3 (the machine) and §7 (examples). -/

open Ochr.Test

ochr Nats {
  -- In-place addition: walk down to the `Z` at the bottom of `*x` and replace it with `y`.
  -- `by x` says that `x` gets smaller at each recursive call.
  def AddM (x : &Nat) (y : Nat) : Unit by x := (
    match *x {
      Z => *x := y,
      S p => AddM(&p, y),
    }
  )

  -- Pure addition, by running the in-place version on the local `x`.
  def Add (x : Nat) (y : Nat) : Nat := (
    AddM(&x, y);
    x
  )

  -- An effect as a statement: adding zero in place leaves `*x` as it was. The proof is by
  -- recursion on `*x`: in the `S(p)` arm, the recursive call about `&p` proves the goal about
  -- the whole of `*x`, because the borrow of `p` sits inside `*x`.
  def AddMZero (x : &Nat) : Id(Unit, AddM(x, 0), ()) by x := (
    match *x {
      Z => refl,
      S p => AddMZero(&p),
    }
  )

  -- `x + S(y) = S(x + y)`, proved in place by the same bare recursion, and transferred to
  -- `Add` by lending it the local `x` (the trees of `Inductives` use it).
  def AddMS (x : &Nat) (y : Nat) : Id(Unit, AddM(x, S(y)), AddM(&*x, y); *x := S(*x)) by x := (
    match *x {
      Z => refl,
      S p => AddMS(&p, y),
    }
  )

  def AddS (x : Nat) (y : Nat) : Id(Nat, Add(x, S(y)), S(Add(x, y))) := AddMS(&x, y)

  -- A borrow of the final `Z` of `*x` (a function that returns a borrow; see
  -- `ReturnedBorrows`).
  def TailM (x : &Nat) : &Nat by x := (
    match *x {
      Z => x,
      S p => TailM(&p),
    }
  )
}
