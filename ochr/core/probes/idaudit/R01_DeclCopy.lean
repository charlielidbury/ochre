import Ochr.Examples.Nat
import Ochr.Examples.Fixtures
import Ochr.Examples.Word
open Ochr.Test

/-!
# Probe (docs/30, "After D84"): a counterexample to D84's resource lemma, through copy-or-move

`IdG : Id(Word, Zero, g(()))` is proved by `refl`, with the same type-state on both sides and
convertible values, yet `let v = □; let a = v; v` is accepted with `Zero` and rejected with `g(())`:
copy-or-move is read from the declared type (D80), and `g`'s codomain `TT(0)` reads as `TT`'s arms
`Word | Nat`. `CU2` is the same cause through the Fn rule; `TW`/`gw`/`CUW` is the twin control.
Run: `lake env lean ../probes/idaudit/R01_DeclCopy.lean` from `ochr/core/lean`, after
`lake build Ochr.Examples.Nat Ochr.Examples.Fixtures Ochr.Examples.Word`. Expected output on
main 7ae8cf00: exactly three errors, the flipped controls, `FlipIdG` and `FlipCT` ("expected
rejection, but accepted") and `FlipCU` ("[Read] v was moved out"). Any other error means a
verdict changed.
-/
-- Resource lemma attack: t and u are convertible values (both Zero), but their declared types
-- differ in copy-ness (D80 reads copy from the declared type, a type function's call as its arms).
ochr R01DeclCopy uses WordType {
  def TT (n : Nat) : Type := match n { Z => Word, S _ => Nat }
  def g (u : Unit) : TT(0) := Zero
  -- the Id: proved by refl, both sides move nothing
  def IdG : Id(Word, Zero, g(())) := refl
  reject def FlipIdG : Id(Word, Zero, g(())) := refl
  -- the context `let v = □; let a = v; v`: accepted with t, rejected with u
  def CT (u : Unit) : Word := (let v = Zero; let a = v; v)
  reject def CU (u : Unit) : Word := (let v = g(()); let a = v; v)
  -- flips of the pair
  reject def FlipCT (u : Unit) : Word := (let v = Zero; let a = v; v)
  def FlipCU (u : Unit) : Word := (let v = g(()); let a = v; v)
  -- the same cause through a closure's capture (the Fn rule reads the capture's declared type)
  def CT2 (u : Unit) : Word := (let v = Zero; let f = (λ(w : Unit) : Word => v); f(()))
  reject def CU2 (u : Unit) : Word := (let v = g(()); let f = (λ(w : Unit) : Word => v); f(()))
  -- a lemma form: the use is under a parameter
  def IdGn (n : Nat) : Id(Word, Zero, g(())) := refl
  -- twin: a type function whose arms all read as Word is a copy type, so both fillings pass
  def TW (n : Nat) : Type := match n { Z => Word, S _ => Word }
  def gw (u : Unit) : TW(0) := Zero
  def IdGW : Id(Word, Zero, gw(())) := refl
  def CUW (u : Unit) : Word := (let v = gw(()); let a = v; v)
}
