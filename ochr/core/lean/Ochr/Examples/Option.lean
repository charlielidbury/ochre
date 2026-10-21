import Ochr.Test

/-! # Option: an optional value

`Opt(A) := None | Some(v : A)` (Rust's `Option`), with the propositions `IsSome(A, o)` and
`IsNone(A, o)`. Where nothing fixes `A`, a constructor takes it explicitly: `None[Nat]`. -/

open Ochr.Test

ochr Options {
  -- An optional value (Rust's `Option`), and whether one holds a value, as propositions.
  inductive Opt (A : Type) := None | Some(v : A)

  def IsSome (A : Type) (o : Opt(A)) : Prop := (
    match o {
      None => False,
      Some(_) => ⊤,
    }
  )

  def IsNone (A : Type) (o : Opt(A)) : Prop := (
    match o {
      None => ⊤,
      Some(_) => False,
    }
  )
}
