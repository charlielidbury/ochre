import Ochr.Examples.Word

/-! # List: lists with a parameter

`List(A) := Nil | Cons(h : A, t : List(A))`, and its length `LenL`, a `Word` (the arrays
library's literals are lists of the right length). -/

open Ochr.Test

ochr Lists uses WordType {
  inductive List (A : Type) := Nil | Cons(h : A, t : List(A))

  -- The length of a list.
  def LenL (E : Type) (l : List(E)) : Word by l := (
    match l {
      Nil => Zero,
      Cons(x, t) => Succ(LenL(E, t)),
    }
  )
}
