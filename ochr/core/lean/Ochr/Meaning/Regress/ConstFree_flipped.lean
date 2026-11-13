import Ochr.Meaning.Steps.Statements

/-!
# A constant of Σ, flipped: with `GlobalsOk` the run's `.const` is the checker's value (built)

`Regress/ConstFree_70247f07.lean` (unbuilt) records `evalCore_step_stmt` false at a `K.C.global`
that is not Σ's. With `GlobalsOk K st` (part of `CtxOk`, now a hypothesis of every statement), the
value conjunct of the statement holds of the record's constant: the checker's `S(Z)`, read at the
run's result type, is the run's result.
-/

namespace Ochr.Meaning.Regress.ConstFlip
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- `def one : Nat := S(Z)`, as a global of Σ. -/
def gOne : GDef := { name := "one", ty := .tNat, fn? := none, val := .succ .zero }
/-- The empty state after it. -/
def stG : MState := { globals := [gOne] }

/-- The run of `.const "one"` returns `K.C.global "one"`, and under `GlobalsOk` the checker's value
means it, at every assignment and future. -/
theorem const_one_ok (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (s : SState) (hG : GlobalsOk K stG) :
    ∃ r, run K ρ φ hint (.const "one") s = some (r, s) ∧ meanV K ρ φ r.2 (.succ .zero) = r.1 := by
  refine ⟨K.C.global "one", rfl, ?_⟩
  have hty := hG.ty "one" gOne rfl ρ
  have hc := hG.const "one" gOne rfl rfl ρ φ
  have hm : (K.C.global "one").2.m = .ty0 Nat := by rw [hty]; rfl
  rw [hc, hm]
  rfl

end Ochr.Meaning.Regress.ConstFlip
