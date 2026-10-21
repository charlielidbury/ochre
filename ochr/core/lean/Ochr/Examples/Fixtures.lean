import Ochr.Test

/-! # Fixtures: definitions that only tests need

A choice of a borrow by a number, a type with no closed values other than `False`, and a type
computed by a program. -/

open Ochr.Test

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
  -- (`Prop` lives in `Type₁`, beside `Type`: D66.)
  def U (n : Nat) : Type₁ := (
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
