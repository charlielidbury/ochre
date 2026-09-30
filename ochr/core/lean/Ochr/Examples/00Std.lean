import Ochr.Test

/-! # 0. Std and Fixtures: the definitions the other files share

An `ochr` block may use other blocks: `ochr Numbers uses Std { … }` checks `Std`'s
declarations first, then its own, in one namespace. Only declarations that `Std` expects to
be accepted, and that are accepted, are visible to its users; they are checked again in
each block that uses them, so switching a rule off re-decides them there too, and each one's
verdict is asserted here, in its home block.

`Std` holds the paper's first example, in-place addition `AddM` and pure addition `Add`
defined by running `AddM` on a copy, with the first proof, that adding zero in place does
nothing; the returned borrow `TailM`; and the data types several files need. `Fixtures`,
below, holds definitions that only tests need. The library proper, `Pair`, `False`, `True`
and `And` (RULES §1, §8), is the `Prelude` block (`Ochr/Prelude.lean`), which every block
uses implicitly; `Nat` and `Unit` are built into the checker.

Defined in RULES §1 (syntax), §3 (the machine) and §7 (examples). -/

open Ochr.Test

-- The library block, `Prelude` (`Ochr/Prelude.lean`), which every block uses implicitly, is
-- asserted here, since that file cannot run the checker's tests itself.
#guard Prelude.decls.length == 4

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

  -- Data types: booleans, and lists and boxes with a parameter.
  inductive Bool := false | true
  inductive List (A : Type) := Nil | Cons(h : A, t : List(A))
  inductive Box (A : Type) := MkBox(x : A)

  -- A number that code only computes with (a key, an index, a length, a counter) is a
  -- `Word`: unary in the logic, a machine word in the cost model. It is declared `copy`, so
  -- reading one copies it, while reading a `Nat`, the structure in-place code walks and
  -- changes, moves it (D53).
  copy inductive Word := Zero | Succ(pred : Word)
}

-- the exact number of declarations (a truncated file changes it)
#guard Std.decls.length == 8

/-! ## Fixtures

Definitions that only the tests need: a choice of a borrow by a number, a type with no
closed values other than `False`, and a type computed by a program. -/

ochr Fixtures {
  -- A borrow into `x` or `y`, chosen by `n`: at an abstract `n`, which one is not known.
  def Pick (n : Nat) (x : &Nat) (y : &Nat) : &Nat := (
    match n {
      Z => x,
      S _ => y,
    }
  )

  -- A type with no closed values: its only constructor needs one already.
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

-- the exact number of declarations (a truncated file changes it)
#guard Fixtures.decls.length == 4
