import Ochr.Test

/-! # Bool: the booleans

`Bool := false | true`, and `IsTrue(b)`, the proposition that `b` is `true`. A comparison
that only branches returns a `Bool` (`Words`' `EqB`, `LeB` and `LtB`); one whose result a
proof needs returns a decision instead (`Logic`'s `Dec`). -/

open Ochr.Test

ochr Bools {
  inductive Bool := false | true

  -- A boolean as a proposition: `⊤` when it is `true`.
  def IsTrue (b : Bool) : Prop := (
    match b {
      false => False,
      true => ⊤,
    }
  )
}
