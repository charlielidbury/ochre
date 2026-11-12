import Ochr.Meaning.Steps.Statements

/-!
# `closeCall_step_stmt` as the pilot stated it (D17, 5dc7710b): refuted on its free parameters

The pilot form quantified the callee's type `fT` and the call's readings `kind`, `res`, `fills`,
`tys` freely, with nothing tying them to the callee. The checker's `closeCall` reads none of them
off a value (`evalCall` computes them from the call as written and typing makes them agree with
the callee's declared Π-type), so the statement had to assume the agreement and did not:
- `fT := .zero` gives `calleeRes fv .zero` no shape, so `callOf` fails and the conclusion's `∃`
  is false for every successful run from a `Good` state (`old_false_of_run` below);
- `res := .unit` at a `Nat` codomain makes the checker return `()` where the reference returns
  the value (`closeCall`'s `if res == .unit then return .unit`), and `fills.getD i = true` at a
  `Nat` cell makes the fill `()` where the reference leaves the final content.
The restated form (`Statements.closeCall_step_stmt`) reads the callee through the run
(`run (.val fv)`) and assumes the agreement (`hkind`, `hres`, `hfills`, `htys`).
-/

namespace Ochr.Meaning.Steps.Regress

open Ochr.Meaning Ochr.Meaning.Steps

/-- The pilot's form, verbatim (D17). -/
def closeCall_step_stmt_old (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (fv : Value) (fT : Value) (ws : Array Value)
    (kind : Kind) (res : DeclInfo) (fills : Array Bool) (tys : Array (Option Value)) (v : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hargs : ArgsLoanFree st.env ws)
    (h : Runs (Ochr.closeCall fuel fv ws kind res fills tys) st fuel v st'),
    ∃ r s', callOf (calleeRes K ρ φ fv fT) (argsRes K ρ φ ws) (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ r.2 v = r.1 ∧
      Exact (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st'

/-- A callee typed by `.zero` has no shape. -/
theorem calleeRes_zero_shape (K : RunCtx) (ρ : Assignment) (φ : Future) (fv : Value) :
    (calleeRes K ρ φ fv .zero).2.shape = none := rfl

/-- Without a shape, `callOf` fails. -/
theorem callOf_none_of_noShape (fv : Res) (args : List Res) (s : SState) (h : fv.2.shape = none) :
    callOf fv args s = none := by
  unfold callOf; rw [h]

/-- **The pilot's form is false** whenever the checker closes off any call from a `Good` state
(with `K.Δ` read off it and the arguments loan-free): take `fT := .zero`. -/
theorem old_false_of_run (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat)
    (st st' : MState) (fv : Value) (ws : Array Value) (kind : Kind) (res : DeclInfo)
    (fills : Array Bool) (tys : Array (Option Value)) (v : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hargs : ArgsLoanFree st.env ws)
    (h : Runs (Ochr.closeCall fuel fv ws kind res fills tys) st fuel v st') :
    ¬ closeCall_step_stmt_old K ρ φ fuel := by
  intro hstmt
  obtain ⟨r, s', hc, _⟩ := hstmt st st' fv .zero ws kind res fills tys v hg hΔ hargs h
  rw [callOf_none_of_noShape _ _ _ (calleeRes_zero_shape ..)] at hc
  cases hc

/-- `runBody_step_stmt` as the pilot stated it: `fT` free, not even an input of `runBody`. -/
def runBody_step_stmt_old (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (fv : Value) (cs : List Value) (t : Term)
    (rd : List (DeclInfo × Value)) (ws : Array Value) (v : Value) (fT : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hargs : ArgsLoanFree st.env ws)
    (hfv : fv = .clo cs t rd ∨ ∃ n, fv = .gfn n)
    (h : Runs (Ochr.runBody fuel fv cs t rd ws) st fuel v st'),
    ∃ r s', callOf (calleeRes K ρ φ fv fT) (argsRes K ρ φ ws) (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ r.2 v ⊑ r.1 ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st'

/-- **The pilot's `runBody` form is false** whenever the checker runs any body from a `Good`
state: take `fT := .zero`. (`callFn_step_stmt` had the weaker version of the same defect: its
`fT` was the checker's input, which an untyped run does not check against `fv`; both now read
the callee through the run.) -/
theorem runBody_old_false_of_run (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat)
    (st st' : MState) (fv : Value) (cs : List Value) (t : Term) (rd : List (DeclInfo × Value))
    (ws : Array Value) (v : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hargs : ArgsLoanFree st.env ws)
    (hfv : fv = .clo cs t rd ∨ ∃ n, fv = .gfn n)
    (h : Runs (Ochr.runBody fuel fv cs t rd ws) st fuel v st') :
    ¬ runBody_step_stmt_old K ρ φ fuel := by
  intro hstmt
  obtain ⟨r, s', hc, _⟩ := hstmt st st' fv cs t rd ws v .zero hg hΔ hargs hfv h
  rw [callOf_none_of_noShape _ _ _ (calleeRes_zero_shape ..)] at hc
  cases hc

end Ochr.Meaning.Steps.Regress
