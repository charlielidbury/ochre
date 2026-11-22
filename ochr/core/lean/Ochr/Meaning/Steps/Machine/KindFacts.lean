import Ochr.Meaning.Steps.Machine.JoinLocal
import Ochr.Meaning.Steps.MasterKind

/-!
# `ExpectRefNat`, proved (machine12)

`Master.ExpectRefNat` (`Steps/MasterKind.lean`): `expectTy` of a borrow type against `Nat` never succeeds. `conv (&A)
Nat` returns `false` on every path that returns at all: the two values differ, `unitTop` changes only `And`, and the
comparison falls to its last arm (neither is a function value); `expectTy` then fails. Walked goal-first with `RetP`.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- `conv` of a borrow type against `Nat` answers `false`. -/
theorem retP_conv_ref_nat (n : Nat) (A : Value) : RetP (· = false) (Ochr.conv n (.tRef A) .tNat) := by
  cases n with
  | zero => unfold Ochr.conv; exact RetP.exhausted'
  | succ n =>
    unfold Ochr.conv
    refine RetP.bind' fun saved => RetP.bind_of (Q := (· = false)) (RetP.onFail' ?_) fun r hr =>
      RetP.bind' fun _ => RetP.pure' hr
    have e1 : (Value.tRef A == Value.tNat) = false := rfl
    simp only [unitTop, e1, Bool.false_eq_true, if_false]
    exact RetP.pure' rfl

/-- **`ExpectRefNat`, PROVED**: `expectTy` of `&A` against `Nat` fails. -/
theorem expectRefNat : Form.Master.ExpectRefNat := by
  intro n w A st st' bh h
  cases n with
  | zero => unfold Ochr.expectTy at h; simp only [runs_exhausted_iff] at h
  | succ n =>
    unfold Ochr.expectTy at h
    obtain ⟨b, s₁, b₁, hc, h₂⟩ := Runs.bind_inv h
    have hb : b = false := (retP_conv_ref_nat n A).run hc
    subst hb
    rw [if_neg Bool.false_ne_true] at h₂
    exact runs_err_false h₂

end Ochr.Meaning.Steps.Machine
