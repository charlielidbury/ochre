import Ochr.Test
open Ochr Ochr.Test
/-! Expectations are for ochr-core a0f40123, which has no erasure pre-pass: OnPair and OnNat are accepted here and rejected (R8) on ochr-core-lean ff6b634a.
 R8 (new on ochr-core-lean ff6b634a, the erasure pre-pass): a closed-off block that calls a
proof-function parameter on a sub-place trips the pre-pass's INTERNAL assertion: the call is
(erased, proof) = (false, false) by its declared type, (true, true) after running. Inside the
block the parameter's declared type is the captured form `(Π(z0 : &Nat). ⊤ : Prop)`. Each
`reject def` is a true statement (a proof-class call has no effect) rejected today; fail-safe. -/
ochr R8 {
  -- the fuzzer's shape (seed 1, case 281), shrunk
  def Stmt (q0 : Nat × Nat) (x1 : &(Nat × Nat)) (h2 : Π (z0 : &Nat). ⊤) : Prop :=
    Id Unit (match q0 { Mk(_, p0) => q0 := (let g2 = h2; g2(&p0); *x1) }) ()
  def OnPair (q0 : Nat × Nat) (h2 : Π (z0 : &Nat). ⊤) : Id Nat (match q0 { Mk(a, p0) => h2(&p0); 0 }) 0 := (
    match q0 { Mk(a, b) => refl }
  )
  def OnNat (n : Nat) (h2 : Π (z0 : &Nat). ⊤) : Id Nat (match n { Z => 0, S p => h2(&p); 0 }) 0 := (
    match n { Z => refl, S _ => refl }
  )
}
#eval IO.println (run "R8" R8).show
