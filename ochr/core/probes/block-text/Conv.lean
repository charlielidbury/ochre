import Ochr
open Ochr Ochr.Test

-- checker14: conversion of sealed blocks by text, the one semantic change
ochr Conv14 {
  def F (n : Nat) : Nat := match n { Z => Z, S p => S(Z) }
  -- J blocks with convertible motives of different code: in Id, in a parameter's type, under a split
  def IdJ (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) : Id(Nat, J(Nat, a, b, λ(z : Nat) : Type => Nat, h, Z), J(Nat, a, b, λ(z : Nat) : Type => (let w = Nat; w), h, Z)) := refl
  def DJ (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) (e : Eq(Nat, J(Nat, a, b, λ(z : Nat) : Type => Nat, h, Z), Z)) : Eq(Nat, J(Nat, a, b, λ(z : Nat) : Type => (let w = Nat; w), h, Z), Z) := e
  def SJ (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) : Eq(Nat, J(Nat, a, b, λ(z : Nat) : Type => Nat, h, Z), J(Nat, a, b, λ(z : Nat) : Type => (let w = Nat; w), h, Z)) := match a { Z => refl, S p => refl }
  -- the motives are NOT convertible (different codomains at every point): rejected on both
  reject def NJ (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) : Eq(Unit, J(Nat, a, b, λ(z : Nat) : Type => Unit, h, ()), J(Nat, a, b, λ(z : Nat) : Type => Unit, h, ())) := (let q : Eq(Nat, a, b) = h; refl)
  -- J blocks with different transported terms: rejected
  reject def DJT (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) : Eq(Nat, J(Nat, a, b, λ(z : Nat) : Type => Nat, h, Z), J(Nat, a, b, λ(z : Nat) : Type => Nat, h, S(Z))) := refl
  -- a block against a call of a function with the same body: not convertible on either side
  reject def BC (n : Nat) : Eq(Nat, F(n), (let r = (match n { Z => Z, S p => S(Z) }); r)) := refl
  -- blocks whose cells hold convertible closures of different code
  def CC (m : Nat) : Eq(Nat, (let f = (λ(k : Nat) : Nat => k); let r = (match m { Z => f(Z), S q => Z }); r), (let g = (λ(k : Nat) : Nat => (let y = k; y)); let r = (match m { Z => g(Z), S q => Z }); r)) := refl
  -- false twin: closures that differ
  reject def CCf (m : Nat) : Eq(Nat, (let f = (λ(k : Nat) : Nat => k); let r = (match m { Z => f(Z), S q => Z }); r), (let g = (λ(k : Nat) : Nat => S(k)); let r = (match m { Z => g(Z), S q => Z }); r)) := refl
}

#eval show IO Unit from do
  let r := runWith (some Prelude) "Conv14" Conv14 {} 2000000
  for row in r.rows do
    let v := match row.verdict with
      | .accepted => "accepted"
      | .rejected m _ => s!"rejected: {m}"
      | .undecided m => "undecided: " ++ m
    IO.println s!"ROW {row.name}: {v}"
