import Ochr.Test
open Ochr Ochr.Test

/-! The fail-safe finding classes of the v2 fuzzer on the default rules, each as a true
statement whose proof by case split the checker rejects (the generic statement is accepted,
its refinement errors). The `reject def`s are true statements rejected today: they record the
incompleteness, and would flip to accepted when a class is fixed. -/
ochr V2Classes {
  -- R1: re-normalising a sealed program that forms an `Id` about a cell it has lent out
  -- (the untyped machine types footprint owners from their current value, a loan)
  def R1 (x0 : &Nat) : Prop := Id Prop (match *x0 { Z => Id Unit () (*x0 := 0), S _ => ⊤ }) ⊤
  reject def R1s (x0 : &Nat) : Id Prop (match *x0 { Z => Id Unit () (*x0 := 0), S _ => ⊤ }) ⊤ := (
    match *x0 { Z => refl, S _ => refl }
  )
  -- R2: a stuck block counts a nested λ's write to its own copy as the block's, passes the
  -- place by `&`, and its re-normalisation makes the λ capture a borrow
  def R2 (n0 : Nat) : Prop := Id Nat (match n0 { Z => n0, S p2 => let a5 = (λ(y6 : &Nat) : Unit => n0 := 0); n0 }) n0
  reject def R2s (n0 : Nat) : Id Nat (match n0 { Z => n0, S p2 => let a5 = (λ(y6 : &Nat) : Unit => n0 := 0); n0 }) n0 := (
    match n0 { Z => refl, S p => refl }
  )
  -- R3: conversion observes two stuck blocks' functions at a generic call, where the pair
  -- they were formed under is abstract, so `(*q0).fst` does not exist
  def R3 (q0 : Nat × Nat) : Prop :=
    Id (Nat × Nat) (match q0 { Mk(p0, p1) => match p0 { Z => q0, S p7 => q0 := Mk(p1, p1); q0 } }) (match q0 { Mk(p15, p16) => match p16 { Z => p16 := 0; (1, 0), S _ => q0 } })
  reject def R3s (q0 : Nat × Nat) : Prop :=
    match q0 { Mk(a, b) => Id (Nat × Nat) (match q0 { Mk(p0, p1) => match p0 { Z => q0, S p7 => q0 := Mk(p1, p1); q0 } }) (match q0 { Mk(p15, p16) => match p16 { Z => p16 := 0; (1, 0), S _ => q0 } }) }
}
#eval IO.println (run "V2Classes" V2Classes).show
