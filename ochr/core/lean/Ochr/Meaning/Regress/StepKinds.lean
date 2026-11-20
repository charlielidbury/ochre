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
at `k ↦ 5` it reads nothing (`S(5)` is the number `6`), at `k ↦ ⊥` it reads `⊥`
(`dws_fails_succField`). The invariant compares readings at every path; two steps with different
keys reaching the same part break it.
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

theorem dws_fails_succField (b : SBinding) (c : Sem) : ¬ DepWithinSites dm Γ (SN b c) := by
  intro h
  have := h (.bind 0 0) [.field ⟨"Nat", 1, 0, ""⟩] (fun l => if l = 0 then .el0 Nat 5 else .err)
    (fun l => if l = 0 then .moved else .err) (fun l hl => ?_)
  · have e1 : Sem.succ (Sem.el0 Nat 5) = .el0 Nat 6 := Sem.succ_el0 5
    have e2 : Sem.succ Sem.moved = .dat "Nat" [] 1 [.moved] none := by
      simp [Sem.succ, Sem.asNat, Sem.as, Sem.whole]
    simp [readV, SN, SState.valAt, e1, e2, Sem.follow, Sem.step, Sem.stepField] at this
  · refine ⟨?_, ?_⟩
    · rw [SState.live_iff]
      by_cases hl0 : l = 0
      · subst hl0; exact ⟨.temp 0 0, by simp [SN, SState.positions], by simp [SN]⟩
      · simp [hl0] at hl
    · by_cases hl0 : l = 0
      · subst hl0; simp [SState.reached, SN, dataHit, pathKey, Step.key, List.isPrefixOf]
      · simp [hl0] at hl

end Ochr.Meaning.Regress.StepKinds
