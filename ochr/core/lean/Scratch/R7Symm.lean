import Ochr.Test
open Ochr Ochr.Test
/-! Expectations are for ochr-core a0f40123: Split is rejected here and accepted on ochr-core-lean ff6b634a, which fixes R7.

 R7: `symm h` (and `trans`) need `h`'s type to be an equation (or `True`); in a branch whose
refinement makes the hypothesis `False` (an unreachable branch), `symm h` is a type error. The
generic statement is accepted; a split that reaches the unreachable branch is rejected. -/
ochr R7Symm {
  def Gen (n0 : Nat) (n1 : Nat) (h2 : Eq Nat n0 n1) : Nat := J(Nat, n1, n0, λ(z : Nat) : Type => Nat, symm h2, 5)
  reject def Split (n0 : Nat) (n1 : Nat) (h2 : Eq Nat n0 n1) : Nat := (
    match n0 { Z => match n1 { Z => 0, S p => J(Nat, n1, n0, λ(z : Nat) : Type => Nat, symm h2, p) }, S _ => 0 }
  )
  def SplitNoSymm (n0 : Nat) (n1 : Nat) (h2 : Eq Nat n0 n1) : Nat := (
    match n0 { Z => match n1 { Z => 0, S p => J(Nat, n0, n1, λ(z : Nat) : Type => Nat, h2, p) }, S _ => 0 }
  )
}
#eval IO.println (run "R7Symm" R7Symm).show
