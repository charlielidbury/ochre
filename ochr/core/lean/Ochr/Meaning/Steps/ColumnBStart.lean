import Ochr.Meaning.Steps.ColumnB

/-!
# The borrow column's decisions at `B`'s three scopes, kernel-evaluated (lead9)

`def B : Nat := (let x = S(Z); let y = &x; *y := Z; x)`. As `ColumnStart` does for `C`: each
decision the assembly reads (the erasure pre-pass `flags` and the reading `declOf` of each sub-term,
at the top frame's readings where it is evaluated) is the aligned table's (`DecTab D stC`), which is
the checker's `Decide` run at `stC` with those readings, evaluated here by the kernel. The scopes:
`[]` (the body, `S(Z)`, `Z`), `[duC]` after `x` (the inner `let`, `&x`), and `[duY, duC]` after `y`
(the sequence, `*y := Z`, its `Z`, the read of `x`); `y`'s reading `duY` is `&x`'s, `.ref .other`.
-/

namespace Ochr.Meaning.Steps.Form.ColumnB

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open ColumnC ColumnC.Aux
open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal runs_out)

/-- `*y := Z`. -/
def writeB : Term := .assign (.deref (.var 0)) .zero
/-- `*y := Z; x`. -/
def seqB : Term := .seq writeB (.place (.var 1))
/-- `let y = &x; *y := Z; x`. -/
def innerB : Term := .letIn ⟨"y"⟩ (.borrow (.var 0)) seqB

theorem bodyB_eq : bodyB = .letIn ⟨"x"⟩ (.succ .zero) innerB := rfl

/-- `y`'s reading: `&x`'s. -/
def duY : DeclInfo := .ref .other

namespace Aux

def isRefOther : DeclInfo → Bool
  | .ref .other => true
  | _ => false

theorem isRefOther_eq {d : DeclInfo} (h : isRefOther d = true) : d = duY := by
  cases d <;> simp [isRefOther] at h ⊢
  rename_i A
  cases A <;> simp [isRefOther] at h ⊢
  rfl

theorem ok_flags_bodyB : isOk (flagsRun bodyB) (scopeState stC []) 1000 = true := by decide +kernel
theorem val_flags_bodyB : outVal (flagsRun bodyB) (scopeState stC []) 1000 = (false, false) := by decide +kernel
theorem ok_declOf_bodyB : isOk (declRun bodyB) (scopeState stC []) 1000 = true := by decide +kernel
theorem val_declOf_bodyB : isOther (outVal (declRun bodyB) (scopeState stC []) 1000) = true := by decide +kernel

theorem ok_flags_inner : isOk (flagsRun innerB) (scopeState stC [duC]) 1000 = true := by decide +kernel
theorem val_flags_inner : outVal (flagsRun innerB) (scopeState stC [duC]) 1000 = (false, false) := by decide +kernel
theorem ok_declOf_inner : isOk (declRun innerB) (scopeState stC [duC]) 1000 = true := by decide +kernel
theorem val_declOf_inner : isOther (outVal (declRun innerB) (scopeState stC [duC]) 1000) = true := by decide +kernel

theorem ok_flags_bor : isOk (flagsRun (.borrow (.var 0))) (scopeState stC [duC]) 1000 = true := by decide +kernel
theorem val_flags_bor : outVal (flagsRun (.borrow (.var 0))) (scopeState stC [duC]) 1000 = (false, false) := by
  decide +kernel
theorem ok_declOf_bor : isOk (declRun (.borrow (.var 0))) (scopeState stC [duC]) 1000 = true := by decide +kernel
theorem val_declOf_bor : isRefOther (outVal (declRun (.borrow (.var 0))) (scopeState stC [duC]) 1000) = true := by
  decide +kernel

theorem ok_flags_seq : isOk (flagsRun seqB) (scopeState stC [duY, duC]) 1000 = true := by decide +kernel
theorem val_flags_seq : outVal (flagsRun seqB) (scopeState stC [duY, duC]) 1000 = (false, false) := by decide +kernel
theorem ok_declOf_seq : isOk (declRun seqB) (scopeState stC [duY, duC]) 1000 = true := by decide +kernel
theorem val_declOf_seq : isOther (outVal (declRun seqB) (scopeState stC [duY, duC]) 1000) = true := by decide +kernel

theorem ok_flags_write : isOk (flagsRun writeB) (scopeState stC [duY, duC]) 1000 = true := by decide +kernel
theorem val_flags_write : outVal (flagsRun writeB) (scopeState stC [duY, duC]) 1000 = (false, false) := by
  decide +kernel
theorem ok_declOf_write : isOk (declRun writeB) (scopeState stC [duY, duC]) 1000 = true := by decide +kernel
theorem val_declOf_write : isAny (outVal (declRun writeB) (scopeState stC [duY, duC]) 1000) = false := by
  decide +kernel
theorem val_declOf_write_proof : (outVal (declRun writeB) (scopeState stC [duY, duC]) 1000).isProof = false := by
  decide +kernel

theorem ok_flags_Zy : isOk (flagsRun .zero) (scopeState stC [duY, duC]) 1000 = true := by decide +kernel
theorem val_flags_Zy : outVal (flagsRun .zero) (scopeState stC [duY, duC]) 1000 = (false, false) := by decide +kernel
theorem ok_declOf_Zy : isOk (declRun .zero) (scopeState stC [duY, duC]) 1000 = true := by decide +kernel
theorem val_declOf_Zy : isOther (outVal (declRun .zero) (scopeState stC [duY, duC]) 1000) = true := by decide +kernel

theorem ok_flags_x1 : isOk (flagsRun (.place (.var 1))) (scopeState stC [duY, duC]) 1000 = true := by decide +kernel
theorem val_flags_x1 : outVal (flagsRun (.place (.var 1))) (scopeState stC [duY, duC]) 1000 = (false, false) := by
  decide +kernel
theorem ok_declOf_x1 : isOk (declRun (.place (.var 1))) (scopeState stC [duY, duC]) 1000 = true := by decide +kernel
theorem val_declOf_x1 : isOther (outVal (declRun (.place (.var 1))) (scopeState stC [duY, duC]) 1000) = true := by
  decide +kernel

end Aux

open Aux

section
variable {D : Decisions} (hd : DecTab D stC)
include hd

theorem flags_of {sc : List DeclInfo} {t : Term} (hok : isOk (flagsRun t) (scopeState stC sc) 1000 = true)
    (hv : outVal (flagsRun t) (scopeState stC sc) 1000 = (false, false)) : D.flags sc t = (false, false) := by
  rw [hd.flags 100 sc t _ 1000 _ (runs_out (flagsRun t) _ 1000 hok), hv]

theorem declOf_of {sc : List DeclInfo} {t : Term} (hok : isOk (declRun t) (scopeState stC sc) 1000 = true) :
    D.declOf sc t = outVal (declRun t) (scopeState stC sc) 1000 := by
  rw [hd.declOf 100 sc t _ 1000 _ (runs_out (declRun t) _ 1000 hok)]

theorem flags_bodyB : D.flags [] bodyB = (false, false) := flags_of hd ok_flags_bodyB val_flags_bodyB
theorem flags_inner : D.flags [duC] innerB = (false, false) := flags_of hd ok_flags_inner val_flags_inner
theorem flags_bor : D.flags [duC] (.borrow (.var 0)) = (false, false) := flags_of hd ok_flags_bor val_flags_bor
theorem flags_seq : D.flags [duY, duC] seqB = (false, false) := flags_of hd ok_flags_seq val_flags_seq
theorem flags_write : D.flags [duY, duC] writeB = (false, false) := flags_of hd ok_flags_write val_flags_write
theorem flags_Zy : D.flags [duY, duC] .zero = (false, false) := flags_of hd ok_flags_Zy val_flags_Zy
theorem flags_x1 : D.flags [duY, duC] (.place (.var 1)) = (false, false) := flags_of hd ok_flags_x1 val_flags_x1

theorem declOf_bodyB : D.declOf [] bodyB = duC := by rw [declOf_of hd ok_declOf_bodyB]; exact isOther_eq val_declOf_bodyB
theorem declOf_inner : D.declOf [duC] innerB = duC := by rw [declOf_of hd ok_declOf_inner]; exact isOther_eq val_declOf_inner
theorem declOf_bor : D.declOf [duC] (.borrow (.var 0)) = duY := by
  rw [declOf_of hd ok_declOf_bor]; exact isRefOther_eq val_declOf_bor
theorem declOf_seq : D.declOf [duY, duC] seqB = duC := by rw [declOf_of hd ok_declOf_seq]; exact isOther_eq val_declOf_seq
theorem declOf_Zy : D.declOf [duY, duC] .zero = duC := by rw [declOf_of hd ok_declOf_Zy]; exact isOther_eq val_declOf_Zy
theorem declOf_x1 : D.declOf [duY, duC] (.place (.var 1)) = duC := by
  rw [declOf_of hd ok_declOf_x1]; exact isOther_eq val_declOf_x1
theorem declOf_write_ok : D.declOf [duY, duC] writeB ≠ .any ∧ (D.declOf [duY, duC] writeB).isProof = false := by
  rw [declOf_of hd ok_declOf_write]
  exact ⟨fun e => (by have h := val_declOf_write; rw [e] at h; cases h), val_declOf_write_proof⟩

theorem duY_ok : duY ≠ .any ∧ duY.isProof = false := ⟨fun e => (by cases e), rfl⟩

end

end Ochr.Meaning.Steps.Form.ColumnB
