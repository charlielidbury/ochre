import Ochr.Fuzz.Replay
import Ochr.Test
open Ochr Ochr.Fuzz Ochr.Test

ochr C354v {
  def Lemma (u : Unit) : ⊤ := refl
  -- tail: a proof λ (as found)
  def LieL (n : Nat) : Id Nat (let c = 0; let f = match n { Z => (c := 1; λ(y : &Nat) : ⊤ => refl) | S _ => λ(y : &Nat) : ⊤ => refl }; c) 0 := refl
  def BoomL : Eq Nat 1 0 := LieL(0)
  -- tail: a proof variable
  def LieV (n : Nat) (h : ⊤) : Id Nat (let c = 0; let f = match n { Z => (c := 1; h) | S _ => h }; c) 0 := refl
  def BoomV : Eq Nat 1 0 := LieV(0, refl)
  -- tail: a let-bound refl
  def LieR (n : Nat) : Id Nat (let c = 0; let f = match n { Z => (c := 1; let e = refl; e) | S _ => refl }; c) 0 := refl
  def BoomR : Eq Nat 1 0 := LieR(0)
  -- tail: refl itself (a proof former: expected to be consistent)
  def LieF (n : Nat) : Id Nat (let c = 0; let f = match n { Z => (c := 1; refl) | S _ => refl }; c) 0 := refl
  reject def BoomF : Eq Nat 1 0 := LieF(0)
  -- adequacy (case 6232): the typed run erases the ascribed proof, the machine runs it
  def Main (n : Nat) : Nat := let c = n; let a : ⊤ = (c := 0; let e = refl; e); c
  def MainIs1 : Id Nat (Main(1)) 1 := refl
}
#eval IO.println (run "C354v" C354v).show
#eval IO.println (run "C354v" C354v { genGlobal := true, syntacticClass := true }).show
#eval IO.println (run "C354v+fix" C354v { proofByValue := true }).show
