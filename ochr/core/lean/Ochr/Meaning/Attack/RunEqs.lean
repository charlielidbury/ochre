import Ochr.Meaning.Attack.CloseCall

/-!
# Equation lemmas for the run layer, on the shapes the attacks meet

`simp [Sem.updAt]` fails (Lean cannot generate `Sem.updAt`'s equational theorems), and `run`'s
clauses are best used as rewrite rules on concrete constructors. The lemmas here are the
equations by `rfl`, for the attack files to rewrite with.
-/

namespace Ochr.Meaning.Attack

open Ochr.Meaning

theorem updAt_nil (dm : DataModel) (Γ : List IndDecl) (T : TyM) (f : Sem → Sem) (s : Sem) :
    Sem.updAt dm Γ T f [] s = some (f s) := rfl

theorem updAt_deref (dm : DataModel) (Γ : List IndDecl) (T : TyM) (f : Sem → Sem) (sts : List Step) (s : Sem) :
    Sem.updAt dm Γ T f (.deref :: sts) s = Sem.updAt dm Γ T f sts s := rfl

theorem run_ascribe (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (u A : Term) (s : SState) :
    run K ρ φ hint (.ascribe u A) s =
      (do
        let (TA, _) ← SM.onCopy (run K ρ φ (.plain .err) A)
        let T := TyS.plain TA.asTy
        let (v, R) ← run K ρ φ T u
        pure (v, { T with label := R.label })) s := rfl

theorem run_letIn (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (x : Hint) (u w : Term) (s : SState) :
    run K ρ φ hint (.letIn x u w) s =
      (do
        let ((v, T), s) ← run K ρ φ (.plain .err) u s
        let s := pushBindShaped s { ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s) u }
        let ((r, R), s) ← run K ρ φ hint w s
        let s := match T.label with | some l => s.endLabel l | none => s
        some ((r, R), s.dropLast)) := rfl

theorem meanV_abs (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (σ : Nat) :
    meanV K ρ φ hint (.abs σ) = ρ σ := rfl

theorem meanV_tNat (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) :
    meanV K ρ φ hint .tNat = .ty (.ty0 Nat) := rfl

theorem meanV_loan (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (l : Nat) :
    meanV K ρ φ hint (.loan l) = φ l := rfl

end Ochr.Meaning.Attack

namespace Ochr.Meaning.Attack

open Ochr.Meaning

/-- A binding pushed onto the one empty frame of `emptyState`: the frame holds just it. -/
theorem pushBind_emptyState (k : Nat) (b : SBinding) :
    (emptyState k).pushBind b = { env := [{ binds := [b] }], shape := fun _ => none, nextLoan := k } := by
  simp [emptyState, SState.pushBind, SState.topIdx]

/-- `var 0` in that state resolves to the binding, with no steps. -/
theorem resolve_var0_one (k : Nat) (b : SBinding) :
    resolve { env := [{ binds := [b] }], shape := fun _ => none, nextLoan := k } (.var 0)
      = some (.bind 0 0, []) := by
  simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps]

end Ochr.Meaning.Attack
