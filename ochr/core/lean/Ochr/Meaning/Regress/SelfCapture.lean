import Ochr.Test
/-!
# A function's own name inside the body it is checked by (lead13, 2026-11-21; docs/31 D123)

The relation reads a binding the checker marks as naming a function whose body is being checked (D78's
`recUid`) at the context's type of that function (`Binding.refTy`, docs/31 D123): the stage closure
at the weakened type while the definition is being checked. That is sufficient wherever the
function's name reaches no other typed position, and the checker rejects every use of the name in its
own body but the head of a call, with one exception: a recursive function's name captured by a λ.
Asserted here (each verdict is checked when this file builds):

- a non-recursive `F`: `let g = F`, `Ap(F)`, `MkBox(F)`, returning `F`, a λ calling `F`: rejected,
  "F is not in scope in its own body: it declares no decreasing parameter (`by x`), so it is not
  recursive (D31)";
- a recursive `R` (`by n`): `let g = R`, `Ap(R)`, `MkBox(R)`, returning `R`, `let g = R; g(m)`:
  rejected, "[Rec] R occurs in its own body other than as the head of a call (fix L1)"; a λ calling
  `R` at its own parameter: rejected by [Rec] ("not a strict subterm");
- ACCEPTED: `R7`, a λ in `R7`'s body calling `R7` at a strict subterm, and `R9`, the same closure moved
  into another binding. The checker's state then holds `h ↦ .clo [.gfn R7, …] t rd`, the capture's
  recorded type (in `rd`) the FULL Π-type.

What fails today for `R7` (stage 2 of D123, queued for the model lane): the closure VALUE's meaning
(`codeMeaning.clo`, `capsTys rd`) binds the capture at the recorded full Π-type holding the stage
closure (not a member of it), while the reference's own λ, formed in `fixBodyAt`'s frame where `self`
is at the weakened type, captures it at the weakened type. So `Rel.sim` at `h` compares two closures
whose capture types differ, and the closure value's frame is not good (`Strict.SGood`). The capture
part of D123 (a capture whose value is the function being checked read at the context's type, in
`capsTys`/`codeMeaning.clo`) is what this program waits for.
-/

open Ochr.Test

ochr SelfCapture {
  inductive Box (A : Type) := MkBox(x : A)
  def Ap (f : Π(x : Nat). Nat) : Nat := Z
  reject def F1 (n : Nat) : Nat := let g = F1; Z
  reject def F2 (n : Nat) : Nat := Ap(F2)
  reject def F3 (n : Nat) : Box(Π(x : Nat). Nat) := MkBox(F3)
  reject def F4 (n : Nat) : (Π(x : Nat). Nat) := F4
  reject def F5 (n : Nat) : Nat := let h = (λ(x : Nat) : Nat => F5(x)); Z
  reject def R1 (n : Nat) : Nat by n := let g = R1; Z
  reject def R2 (n : Nat) : Nat by n := Ap(R2)
  reject def R3 (n : Nat) : Box(Π(x : Nat). Nat) by n := MkBox(R3)
  reject def R4 (n : Nat) : (Π(x : Nat). Nat) by n := R4
  reject def R5 (n : Nat) : Nat by n := match n { Z => Z, S m => let g = R5; g(m) }
  reject def R6 (n : Nat) : Nat by n := match n { Z => Z, S m => let h = (λ(x : Nat) : Nat => R6(x)); h(m) }
  def R7 (n : Nat) : Nat by n := match n { Z => Z, S m => let h = (λ(x : Nat) : Nat => R7(clone(m))); h(Z) }
  def R9 (n : Nat) : Nat by n := match n { Z => Z, S m => let h = (λ(x : Nat) : Nat => R9(clone(m))); let k = h; k(Z) }
}
