import Ochr.Test
open Ochr Ochr.Test

/-! Fuzzer validation, switch `P2` (eraseOnCopy) alone: the ledger lists P2 as a
completeness row under D41, but D41 lets an erased term pass an outer place to an erased
call, and without the private copy that call's writes persist on the direct path while the
closed-off (erased) block skips them. With P2 off, a closed proof of `False`. -/
ochr P2Alone {
  def F5 (x : &Nat) : Prop := *x := 5; ⊤
  def Lie (x : &Nat) : Id Nat (let a = match *x { Z => refl, S p => F5(&*x); refl }; *x) *x := refl
  reject def Boom : False ∧ False := let c = 1; Lie(&c)
  reject def Boom2 : False := let b = Boom; match b { Intro(l, r) => l }
}
#eval IO.println (run "P2Alone" P2Alone).show
-- with P2 off, `Boom` and `Boom2` are accepted (the two `reject def`s fail)
#eval IO.println (run "P2Alone" P2Alone { eraseOnCopy := false }).show
