import Ochr.Meaning.Regress.EvalMemGap
import Ochr.Meaning.Steps.MachineMono

/-!
# Two open statements false as stated (sixth lead's inventory, `Meaning/OPEN.md`; kernel-checked)

Found while making the inventory of open statements; each fails for a missing hypothesis that its
use site has, not for a fault of the checker or the model.

1. `MachineMono.grows_restoreKeep` (`restoreKeep saved` only extends the tables, from ANY state):
   `restoreKeep` takes the globals and declarations from `saved`, so from a state whose globals
   differ it does not keep them (`grows_restoreKeep_false`). Every use restores a snapshot of the
   same run, whose globals are the current state's; the statement needs that hypothesis.
2. `Assembly.typedFutureF_exists` (a state good with values in flight has a typed future): a
   flight can type a label at an empty type, and then `GoodF` holds vacuously (membership is asked
   only at typed futures, of which there are none) while no typed future exists
   (`typedFutureF_exists_false`, the empty frame with the label `0` typed `False`).
-/

namespace Ochr.Meaning.Regress.OpenFalse
open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Regress.EvalMemGap
open Ochr.Meaning.Regress.GenNeutralContent (outSt isOk runs_out)

/-! ## 1. `grows_restoreKeep` -/

/-- A snapshot with one global. -/
def saved1 : MState := { globals := [{ name := "g", ty := .tNat, fn? := none, val := .zero }] }

theorem okRK : isOk (Ochr.restoreKeep saved1) S0 10 = true := by decide +kernel

/-- **`grows_restoreKeep` is false**: restoring a snapshot with a global, from the empty frame
(which has none), changes the globals. -/
theorem grows_restoreKeep_false : ¬ GrowsM (Ochr.restoreKeep saved1) := by
  intro h
  have hg := (h S0 10 () _ (runs_out (Ochr.restoreKeep saved1) S0 10 okRK)).globals
  have e : (outSt (Ochr.restoreKeep saved1) S0 10).globals.length = 1 := by decide +kernel
  rw [hg] at e
  simp [S0] at e

/-! ## 2. `typedFutureF_exists` -/

/-- `Good` gives `GoodF` at any flight: a future typed at the flight is typed. -/
theorem goodF_of_good (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (st : MState)
    (fl : Flight) (hg : Good dm C Γ ρ st) : GoodF dm C Γ ρ st fl :=
  ⟨hg.1, ⟨fun φ hφ => hg.2.1.pos φ hφ.1, hg.2.1.absTy, hg.2.1.goal⟩, hg.2.2⟩

/-- **`typedFutureF_exists` is false at every context**: the empty frame with `0` in flight and the
label `0` typed `False` is good with that flight (vacuously), and no future gives `0` a member of
`False`. The statement needs the flight's types inhabited (its use site's flight is a borrow's
content type, inhabited by the borrow's record). -/
theorem typedFutureF_exists_false (K : RunCtx) (ρ : Assignment) :
    ¬ ∀ (st : MState) (fl : Flight), GoodF K.dm K.M K.Γ ρ st fl → ∃ ψ, TypedFutureF K.dm K.M K.Γ ρ st fl ψ := by
  intro h
  obtain ⟨ψ, -, hψ⟩ := h (S0.withTemp .zero) [(0, TyM.prop False)]
    (goodF_of_good _ _ _ ρ _ _ (good_S0T K ρ))
  obtain ⟨⟨a⟩, -⟩ := hψ 0 (TyM.prop False) (by simp)
  exact a

end Ochr.Meaning.Regress.OpenFalse
