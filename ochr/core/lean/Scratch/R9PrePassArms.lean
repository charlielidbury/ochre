import Ochr.Test
open Ochr Ochr.Test
/-! R9 (ochr-core-lean b2ce75b5, default rules and with D53): a match whose arms differ in
class, one a proof and one data, on a scrutinee the checker knows. The erasure pre-pass
reads the match's class from every arm's declared type (mixed, so data); the run takes the
live arm (a proof). The pre-pass assertion then fires: "INTERNAL [pre-pass] match … :
erased/proof = (false, false) by its declared type, (true, true) after running". Fail-safe
(the function is rejected). In the fuzzer it hides as a rejected statement, since both paths
hit it; on `ochr-d53-on`, where the assertion is off by default (`prePassAssert` normalises
`d53 := false` but the default is now `true`), it surfaces instead as a D41 error when the
generic path is refined (seed 11, case 90765). `B` is the fuzzer's shape, `B6` the minimum.
Fixed by 37a74e89 (arms that disagree on being a proof defer to the arm that runs): both were
accepted. Since D63 (rule-audit item 10, 38966e3f) such arms have no declared type and both
are rejected ("the arms of a match … disagree about being proofs"); checked on 042a06f7. -/
ochr R9 {
  inductive Or (P : Prop) (Q : Prop) : Prop := Inl(l : P) | Inr(r : Q)
  def EffL (x : &Nat) (h : Or(⊤, ⊤)) : ⊤ :=
    match h { Inl(p) => *x := 1; refl, Inr(q) => *x := 2; refl }
  reject def B (n1 : Nat) : Nat := (let a6 = match n1 { Z => match n1 { Z => EffL(&n1, Inr[⊤, ⊤](refl)), S p7 => 0 }, S p14 => EffL(&n1, Inr[⊤, ⊤](refl)) }; n1)
  reject def B6 : Nat := (let n = 0; let a = match n { Z => refl, S _ => 0 }; n)
}
#eval IO.println (run "R9" R9).show
#eval IO.println (run "R9 (D53 on)" R9 {}).show
