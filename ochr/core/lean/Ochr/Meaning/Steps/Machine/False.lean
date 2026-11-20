import Ochr.Meaning.Steps.Machine.Defs

/-!
# Statements of `Steps/MachineMono.lean` that are false as written (kernel-checked)

`grows_restoreKeep saved`: `restoreKeep saved` takes the globals and the declarations from
`saved`, so from a state whose declarations differ from `saved`'s it changes them. It keeps the
tables when `saved` has the current globals and declarations, which holds at every use in the
machine (the saved state is read earlier in the same run): `Machine.growsIn_restoreKeep`.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- A saved state with one declaration more than the empty state. -/
def savedX : MState := { inds := [{ name := "X" }] }

/-- **`grows_restoreKeep` is false**: restoring `savedX` from the empty state adds a declaration. -/
theorem not_grows_restoreKeep : ¬ GrowsM (Ochr.restoreKeep savedX) := by
  intro h
  have hr : Runs (Ochr.restoreKeep savedX) {} 0 () _ := ⟨#[], 0, #[], rfl⟩
  have := (h _ _ _ _ hr).inds
  simp [savedX] at this

end Ochr.Meaning.Steps.Machine
