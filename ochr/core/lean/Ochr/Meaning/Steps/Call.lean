import Ochr.Meaning.Steps.Borrow

/-!
# Step lemmas, calls: `callFn`, `runBody`, `closeCall`, `callType`, `recCheck` (milestone 3)

A call in the checker runs the callee's body (`runBody`) or, when the body is stuck, closes off
(`closeCall`, three rows). The reference run applies the callee's meaning (`callOf`). So:
* a direct call is *below* the reference (the body's run is below the function's meaning, by the
  induction hypothesis on the body: docs/18 "a call of a closure, run directly");
* closing off is *exact*: a sealed program means its run, which is the reference's call
  (docs/18 (C1)–(C9)); the row for `&T` is `callOf`'s `.ref` case; η at `Unit` is membership
  (`⟦f⟧(ā) ∈ ⟦Unit⟧`, the one-element set);
* `callType`/`declCallType` compute the codomain at the arguments, the reference's `TyS` of the
  result;
* `recCheck`'s accepting direction is the stabilisation of the stages (the semantic [Rec]).
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment)

/-- The callee as the run sees it: its meaning and its type value's shape. The shape is read
through the run of the type value (the `.pi` clause of `run`); a callee whose type is not a
Π-type has none. -/
noncomputable def calleeRes (fv : Value) (fT : Value) : Res :=
  (fun φ => meanV K ρ φ .err fv,
    match run K ρ .err (.val fT) emptyState with
    | some ((_, T), _) => T
    | none => ⟨.err, none, none⟩)

/-- The arguments as the run sees them, with each borrow argument's label. -/
noncomputable def argsRes (ws : Array Value) : List Res :=
  ws.toList.map fun w => (fun φ => meanV K ρ φ .err w,
    ⟨.err, none, match w with | .borrow l _ => some l | _ => none⟩)

/-- A direct call (`callFn`, untyped or typed): below the reference's `callOf` on the callee's
meaning, and `Good` kept. The arguments are loan-free (WF5, `ArgsLoanFree`). -/
theorem callFn_step (st st' : MState) (fuel : Nat) (typed : Bool) (fv : Value) (fT : Value)
    (ws : Array Value) (tys : Array (Option Value)) (hd : Bool) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hargs : ArgsLoanFree st.env ws)
    (h : Runs (Ochr.callFn fuel typed fv (some fT) ws tys hd) st fuel (v, T?) st') :
    ∃ r s', callOf (calleeRes K ρ fv fT) (argsRes K ρ ws) (SM' K ρ st) = some (r, s') ∧
      (∀ φ, meanV K ρ φ r.2.m v ⊑ r.1 φ) ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st' := by
  sorry

/-- Running a body (`runBody`): the frame pushed with the captures and parameters, the body run,
the frame popped: below the function's meaning applied (the induction hypothesis on the body). -/
theorem runBody_step (st st' : MState) (fuel : Nat) (fv : Value) (cs : List Value) (t : Term)
    (rd : List (DeclInfo × Value)) (ws : Array Value) (v : Value) (fT : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hargs : ArgsLoanFree st.env ws)
    (hfv : fv = .clo cs t rd ∨ ∃ n, fv = .gfn n)
    (h : Runs (Ochr.runBody fuel fv cs t rd ws) st fuel v st') :
    ∃ r s', callOf (calleeRes K ρ fv fT) (argsRes K ρ ws) (SM' K ρ st) = some (r, s') ∧
      (∀ φ, meanV K ρ φ r.2.m v ⊑ r.1 φ) ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st' := by
  sorry

/-- [Close] (`closeCall`), every row: exact against `callOf`. The result is a sealed program (or
`()` at a declared `Unit`, or a borrow of one), and each lent place a fill: both mean what the
reference's call gives them, since a sealed program means its run. -/
theorem closeCall_step (st st' : MState) (fuel : Nat) (fv : Value) (fT : Value) (ws : Array Value)
    (kind : Kind) (res : DeclInfo) (fills : Array Bool) (tys : Array (Option Value)) (v : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hargs : ArgsLoanFree st.env ws)
    (h : Runs (Ochr.closeCall fuel fv ws kind res fills tys) st fuel v st') :
    ∃ r s', callOf (calleeRes K ρ fv fT) (argsRes K ρ ws) (SM' K ρ st) = some (r, s') ∧
      (∀ φ, meanV K ρ φ r.2.m v = r.1 φ) ∧
      Exact (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st' := by
  sorry

/-- [Call-type] (`callType`, `declCallType`): the codomain at the arguments is the reference's
result type. -/
theorem callType_step (st st' : MState) (fuel : Nat) (piTy : Value) (ws : Array Value)
    (tys : Array (Option Value)) (B : Value)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.callType fuel piTy ws tys) st fuel B st') :
    ∀ ps out, (calleeRes K ρ .proof piTy).2.shape = some (ps, out) →
      (meanV K ρ noFuture .err B).asTy =
        (match out with
          | .data B' => B' ((argsRes K ρ ws).map (·.1 noFuture))
          | .ref U => U ((argsRes K ρ ws).map (·.1 noFuture))) := by
  sorry

/-- [Rec]'s accepting direction (`recCheck`), semantically: for a recursive function whose every
recursive call passes a strict subterm of the entry value, the stages of the `fix` clause
stabilise, so the closure's meaning is not `err` and the guard never fires (docs/24 §4, the
semantic form of [Rec]; `Slice.stage_stable` generalised). Stated on the closure value: its
meaning is a member of its Π-type. -/
theorem recCheck_sound (st : MState) (fv : Value) (fT : Value)
    (hg : Good K.dm K.C K.Γ ρ st)
    (hacc : ∃ fuel st', Runs (Ochr.checkFix fuel fv [] (match fv with | .clo _ t _ => t | _ => .tt)) st fuel () st') :
    ∀ φ, meanV K ρ φ .err fv ∈ₛ (meanV K ρ φ .err fT).asTy := by
  sorry

end

end Ochr.Meaning.Steps
