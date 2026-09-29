import Ochr.Test

/-! # 0. Std: the definitions the other files share

An `ochr` block may use other blocks: `ochr Numbers uses Std { … }` checks `Std`'s
declarations first, then its own, in one namespace. Only declarations that `Std` expects to
be accepted, and that are accepted, are visible to its users; they are checked again in
each block that uses them, so switching a rule off re-decides them there too, and each one's
verdict is asserted here, in its home block.

These are the paper's first example, in-place addition `AddM` and pure addition `Add`
defined by running `AddM` on a copy, with the first proof, that adding zero in place does
nothing; the returned borrow `TailM`; the choice of a borrow by a number, `Pick`; and the
data types and type-valued function several files need. The built-in library `False`,
`True` and `And` (RULES §1) is not here: it is part of the checker.

Defined in RULES §1 (syntax), §3 (the machine) and §7 (examples). -/

open Ochr.Test

ochr Std {
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
  -- recursion on `*x`: in the `S p` arm, the recursive call about `&p` proves the goal about
  -- the whole of `*x`, because the borrow of `p` sits inside `*x`.
  def AddMZero (x : &Nat) : Id Unit (AddM(x, 0)) () by x := (
    match *x {
      Z => refl,
      S p => AddMZero(&p),
    }
  )

  -- A borrow of the final `Z` of `*x` (a function that returns a borrow; see
  -- `ReturnedBorrows`).
  def TailM (x : &Nat) : &Nat by x := (
    match *x {
      Z => x,
      S p => TailM(&p),
    }
  )

  -- A borrow into `x` or `y`, chosen by `n`: at an abstract `n`, which one is not known.
  def Pick (n : Nat) (x : &Nat) (y : &Nat) : &Nat := (
    match n {
      Z => x,
      S _ => y,
    }
  )

  -- Data types: booleans, lists and boxes with a parameter, and a type with no closed
  -- values (its only constructor needs one already).
  inductive Bool := false | true
  inductive List (A : Type) := Nil | Cons(h : A, t : List(A))
  inductive Box (A : Type) := MkBox(x : A)
  inductive Empty := E(e : Empty)

  -- A type computed by a program: `U(n)` is `Prop` for every `n`, but only after computing
  -- it; at an abstract `n` it is stuck. `V(n)` proves it. The erasure examples use them.
  def U (n : Nat) : Type := (
    match n {
      Z => Prop,
      S _ => Prop,
    }
  )

  def V (n : Nat) : U(n) := (
    match n {
      Z => ⊤,
      S _ => ⊤,
    }
  )
}

#eval IO.println (run "Std" Std).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Std" Std).allAsExpected
#guard (run "Std" Std).count == 11
