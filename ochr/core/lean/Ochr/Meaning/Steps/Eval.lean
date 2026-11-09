import Ochr.Meaning.Steps.Borrow

/-!
# Step lemmas, `evalCore` (milestone 3): the run of a term is below the reference run

`evalCore` is the machine's one entry point per term form; the files `Borrow`, `Subst`, `Call`,
`Match`, `Obs`, `Types` state its pieces. This file states the per-form clauses it dispatches to
that are not covered there, and the induction step itself (`evalCore_step`): the checker's run
of a term, at a `Good` state, is below the reference run of the term at the type the context
expects, with the result's meaning below the reference's result, and `Good` is kept for an
assignment extending the given one to the unknowns the run created. This is docs/18 Theorem
14 (a), (b), (c) for one term, and the assembly (milestone 4) applies it along `checkTail`.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment)

/-- The type the context gives, as a `TyM` (`err` when none). -/
noncomputable def hintM (hint : Option Value) : TyM :=
  ((hint.map (meanV K ρ noFuture .err)).map Sem.asTy).getD .err

/-- The induction step. For every `Good` assignment `ρ`, following at each split the arm it
selects, the run of `t` reaches a value below the reference's result, a state below the
reference's, for an assignment `ρ'` extending `ρ` to the unknowns created, and `Good` is kept;
the reference run does not fail. -/
theorem evalCore_step (st st' : MState) (fuel : Nat) (typed : Bool) (t : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.evalCore fuel typed t hint) st fuel (v, T?) st') :
    ∃ ρ', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧
      ∃ r s', run K ρ' (hintM K ρ hint) t (SM' K ρ' st) = some (r, s') ∧
        (∀ φ, meanV K ρ' φ r.2.m v ⊑ r.1 φ) ∧
        (∀ T, T? = some T → (meanV K ρ' noFuture .err T).asTy = r.2.m) ∧
        Below (MState.mean K.dm K.C K.Γ ρ' st') s'.toMean ∧ Good K.dm K.C K.Γ ρ' st' := by
  sorry

/-- [Let]: the binding is pushed at the right-hand side's type and dropped after the tail
(`dropTopBind`); the run's `.letIn` clause. -/
theorem letIn_step (st st' : MState) (fuel : Nat) (typed : Bool) (h0 : Hint) (u w : Term)
    (hint : Option Value) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.evalCore fuel typed (.letIn h0 u w) hint) st fuel (v, T?) st') :
    ∃ ρ' r s', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧
      run K ρ' (hintM K ρ hint) (.letIn h0 u w) (SM' K ρ' st) = some (r, s') ∧
      (∀ φ, meanV K ρ' φ r.2.m v ⊑ r.1 φ) ∧
      Below (MState.mean K.dm K.C K.Γ ρ' st') s'.toMean ∧ Good K.dm K.C K.Γ ρ' st' := by
  sorry

/-- `Eq` (the `.eq` form): both sides on private copies, the type a statement; the result means
`⟦a⟧ = ⟦b⟧` (`Steps/Eq.mkEqM_step`), and the state's core is unchanged. -/
theorem eq_step (st st' : MState) (fuel : Nat) (typed : Bool) (A a b : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.evalCore fuel typed (.eq A a b) hint) st fuel (v, T?) st') :
    st'.core = st.core ∧
    ∃ r s', run K ρ .err (.eq A a b) (SM' K ρ st) = some (r, s') ∧
      ∀ φ, ((meanV K ρ φ .err v).asTy).true ↔ ((r.1 φ).asTy).true := by
  sorry

/-- `J`, both outcomes: computed at convertible endpoints (the transported term runs in place)
or closed off as a stuck block whose one arm is the transported term ([T-J-stuck]); each means
the transported term (docs/24 C9). -/
theorem J_step (st st' : MState) (fuel : Nat) (typed : Bool) (A a b P hh u : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.evalCore fuel typed (.prim "J" [A, a, b, P, hh, u]) hint) st fuel (v, T?) st') :
    ∃ ρ' r s', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧
      run K ρ' (hintM K ρ hint) (.prim "J" [A, a, b, P, hh, u]) (SM' K ρ' st) = some (r, s') ∧
      (∀ φ, meanV K ρ' φ r.2.m v ⊑ r.1 φ) ∧
      Below (MState.mean K.dm K.C K.Γ ρ' st') s'.toMean ∧ Good K.dm K.C K.Γ ρ' st' := by
  sorry

/-- A proof position (a proof-returning call, a proof primitive, a proof `let`): its value is
`⋆`, which is a member of its proposition exactly when the proposition is true; the state is
unchanged (a statement runs on a copy). Membership here is where "a proof's value is `⋆`"
(docs/26 row 1, *same* given membership) is discharged. -/
theorem proof_step (st st' : MState) (fuel : Nat) (typed : Bool) (t : Term) (hint : Option Value)
    (T : Value)
    (hg : Good K.dm K.C K.Γ ρ st)
    (hp : (K.D.flags (scopeOf (SM' K ρ st)) t).2 = true)
    (h : Runs (Ochr.evalCore fuel typed t hint) st fuel (.proof, some T) st') :
    st'.core = st.core ∧ ∀ φ, Sem.proof ∈ₛ (meanV K ρ φ .err T).asTy := by
  sorry

/-- η at `Unit` (D80): where a position's declared reading is `Unit`, the value is `()`, and
`()` is the one element of `⟦Unit⟧`, so the normalisation keeps meaning given membership. -/
theorem etaUnit_step (st : MState) (d : DeclInfo) (v : Value) (hint : TyM)
    (hg : Good K.dm K.C K.Γ ρ st) (hd : d = .unit)
    (hv : ∀ φ, meanV K ρ φ hint v ∈ₛ .ty0 Unit) :
    ∀ φ, meanV K ρ φ hint (Ochr.etaUnit d v) = meanV K ρ φ hint v := by
  sorry

end

end Ochr.Meaning.Steps
