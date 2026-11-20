import Ochr.Meaning.DepWithin
import Ochr.Meaning.BotWrite
import Ochr.Examples.Nat

/-!
# A reading by a constructor field of a number (docs/31 D67, step 3; kernel-checked, for the lead)

`let x = S(a); let r = &x.0` is accepted (`StepKindsProbe`). In the reference `x` then reads
`S(ψ k)` (`borrowPlace` at `[.0]` on a number: `Sem.updAt`'s `.0` case, `Sem.succ`), and `k` is
lent at `(x, [.0])`, key `[(0, 0)]`. The reference's `Sem.step` reaches a number's predecessor two
ways: `.0` (key `(0, 0)`) and, on the partly moved form `S(⊥…)` (`Sem.succ` of a non-whole
argument, `.dat "Nat" [] 1 [w]`), the constructor field `S.0` (key `(1, 0)`). The checker reaches
it one way (`stepV`: `.field` on a number is nothing). So a read of `x` at `[S.0]`, a path no place
of the program produces, is incomparable with `k`'s site by key and reads `k`'s final content:
at `k ↦ 5` it read nothing (`S(5)` is the number `6`), at `k ↦ ⊥` it read `⊥`. The invariant
compares readings at every path; two steps with different keys reaching the same part broke it.

Fixed (the data-layer lane, at the lead's decision: the run reads exactly the steps the checker
reads): `Sem.step`'s named field step never reads a number, whole or partly moved, as `stepV`
reads `.field` only on constructor values and no declaration is named `Nat` ((N)). So the read of
`x` at `[S.0]` is nothing at every future (`succField_reads_nothing`).
-/

open Ochr.Test

ochr StepKindsProbe uses Nats {
  def BorrowPred (a : Nat) : Unit := (let x = S(a); let r = &x.0; ())
}

namespace Ochr.Meaning.Regress.StepKinds
open Ochr Ochr.Meaning

/-- After `let x = S(a); &x.0`: `x` reads `S` of the borrow's final content, the borrow parked. -/
noncomputable def SN (b : SBinding) (c : Sem) : SState :=
  { env := [{ binds := [{ b with val := fun ψ => Sem.succ (ψ 0) }], temps := [fun _ => c] }],
    shape := fun p => if p = .temp 0 0 then some 0 else none, nextLoan := 1,
    lent := fun m => if m = 0 then [⟨.bind 0 0, [.proj 0], false⟩] else [] }

variable (dm : DataModel) (Γ : List IndDecl)

/-- **The read at `[S.0]` is nothing at every future**: at `k ↦ 5` (`x` is the number `6`) and at
`k ↦ ⊥` (`x` is `S(⊥)`) alike. -/
theorem succField_reads_nothing (T : TyS) (v : Sem) :
    Sem.follow dm Γ T (Sem.succ v) [.field ⟨"Nat", 1, 0, ""⟩] = none := by
  unfold Sem.succ
  split
  · rfl
  · split
    · rfl
    · simp [Sem.follow, Sem.step]

end Ochr.Meaning.Regress.StepKinds
