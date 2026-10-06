import Ochr.Test
open Ochr Ochr.Test

/-! Fuzzer validation, switch `P2` (eraseOnCopy) alone: the ledger listed P2 as a
completeness row under D41, but D41 lets an erased term pass an outer place to an erased
call, and without the private copy that call's writes persist on the direct path while the
closed-off (erased) block skips them. With P2 off, a closed proof of `False` (now the
ledger's P2 witness, `Erasure.BoomP2`). The first block is checked under the default rules,
the second with P2 off; every verdict is as expected in both. -/
ochr P2Default {
  def F5 (x : &Nat) : Prop := *x := 5; ⊤
  def Lie (x : &Nat) : Id(Nat, (let a = match *x { Z => refl, S p => F5(&*x); refl }; *x), *x) := refl
  reject def Boom : False ∧ False := let c = 1; Lie(&c)
  reject def Boom2 : False := let b = Boom; match b { Intro(l, r) => l }
}
ochr P2Off {
  def F5 (x : &Nat) : Prop := *x := 5; ⊤
  def Lie (x : &Nat) : Id(Nat, (let a = match *x { Z => refl, S p => F5(&*x); refl }; *x), *x) := refl
  def Boom : False ∧ False := let c = 1; Lie(&c)
  def Boom2 : False := let b = Boom; match b { Intro(l, r) => l }
}
#eval IO.println (run "P2Default (default rules)" P2Default).show
#eval IO.println (run "P2Off (P2 off: a closed proof of False)" P2Off { eraseOnCopy := false }).show
