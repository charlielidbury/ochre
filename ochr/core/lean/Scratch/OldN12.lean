import Ochr.Test
open Ochr Ochr.Test
/-! The v1.6 fuzzer findings N1 and N2 (notes/fuzzer.md, v1.x log §3), replayed on v2.1: every one is rejected by D41 (an erased term may not write a place that
outlives it), so neither is a proof of false any more. -/
ochr OldN12 {
  reject def LieL (n : Nat) : Id Nat (let c = 0; let f = match n { Z => (c := 1; λ(y : &Nat) : ⊤ => refl), S _ => λ(y : &Nat) : ⊤ => refl }; c) 0 := refl
  reject def BoomL : Eq Nat 1 0 := LieL(0)
  reject def LieV (n : Nat) (h : ⊤) : Id Nat (let c = 0; let f = match n { Z => (c := 1; h), S _ => h }; c) 0 := refl
  reject def BoomV : Eq Nat 1 0 := LieV(0, refl)
  reject def LieR (n : Nat) : Id Nat (let c = 0; let f = match n { Z => (c := 1; let e = refl; e), S _ => refl }; c) 0 := refl
  reject def BoomR : Eq Nat 1 0 := LieR(0)
  reject def LieA (n : Nat) : Id Nat (match n { Z => let c = 5; let a : ⊤ = (c := 0; let e = refl; e); c, S _ => 0 }) 0 := match n { Z => refl, S _ => refl }
  reject def BoomA : Eq Nat 5 0 := LieA(0)
  reject def Main (n : Nat) : Nat := let c = n; let a : ⊤ = (c := 0; let e = refl; e); c
  reject def MainT : Id Nat (Main(1)) 1 := refl
}
#eval IO.println (run "OldN12" OldN12).show
