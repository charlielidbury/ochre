import Ochr.Test

/-! # Box: one value in a box

`Box(A) := MkBox(x : A)`, a data type with a parameter (the tests box functions and
propositions in it). -/

open Ochr.Test

ochr Boxes {
  inductive Box (A : Type) := MkBox(x : A)
}
