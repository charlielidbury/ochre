import Ochr.Meaning.Steps.Statements

/-!
# The rules trial: is an evaluated value's membership available through the value in flight?

`mkEqM`'s caller (`Steps/EqJAsm.lean`, `eq_step_asm`) needs each side of the `Eq` to be `⊥` or a
member of the equation's type (`Rules/Compose.lean`, `SideOk`). The step statements in the
simulation form count the value they return as in flight (docs/31 D71: `SimConcl`, `SimConclT`,
`eval_step_stmt`: `GoodF … (st'.withTemp v) (flightOf r.2)`). This file records, kernel-checked,
what that component does and does not say about the value.

**It does not type the value.** The value is pushed as a temporary of the top frame
(`MState.withTemp`), and a temporary has no stored type (`posTyM_temp`) and is read at hint `err`
(`hintAt_temp`); `MembershipF.pos` speaks only of positions with a stored type, so it says nothing
about the value in flight. `flightOf r.2` types the future at the value's label (a returned
borrow's content), not the value.

**What it does give**: every unknown the value names is referenced by the state with the value
counted (`MState.Refd.val`, over `Env.values`, temporaries included), so the step's assignment
types those unknowns (`TypedAssignment.mem`). Later extensions agree with it on them (`ExtOk`'s
first clause, for every `σ` below the table's size, which a private copy's restore keeps). That is
exactly the fact counterexample 2 (`Counter.mkEqM_step_stmt_false`: a side `σ₀` sent to `moved`) is
missing in its instance. But `EqJAsm.side_step` discards it: it uses the `GoodF` only to feed
`restore_ext` (`typedAssignment_of_withTemp`) and concludes nothing about the side's unknowns. And
it is not membership of the side: a compound side is not a member of its type because its unknowns
are.

**What the evaluation step would have to conclude** (`EvalMemConcl` below): for a typed run of a
term that is not a proof, returning `(v, some T)`, the value means a (partly moved) member of the
run's result type under every future typed for the state after with the value in flight, as
[Return]'s statement concludes for a body (`bodyReturns_sound_stmt`). By `StrAgree` that type is the
checker's `T`. The `Eq` caller would then still need: the comparison of each side's type with the
equation's (`eqChecks`' `expectTy Ta A'`, a conversion of type values, hence the typing gap again:
`HWT` of `Ta` and `A'`), the side not meaning `moved` unless it is `⊥`, and, for an untyped re-run,
the fact carried over from the typed run. The alternative with the same content: count the value
in flight as a TYPED temporary (its stored type the run's), so that `MembershipF.pos` covers it and
every statement in the simulation form owes it; that is the type-safety half of the main theorem
made an invariant of every step.
-/

namespace Ochr.Meaning.Rules
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- A temporary has no stored type: `Membership` never speaks of it. -/
theorem posTyM_temp (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (st : MState)
    (f i : Nat) : MState.posTyM dm C Γ ρ st (.temp f i) = none := rfl

/-- A temporary is read at hint `err`. -/
theorem hintAt_temp (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (env : Env)
    (f i : Nat) : Env.hintAt dm C Γ ρ env (.temp f i) = .plain TyM.err := rfl

/-- So `MembershipF` of a state with a value in flight holds at the temporary positions for any
value whatever: the clause is vacuous there. -/
theorem membership_temp_vacuous (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment)
    (st : MState) (f i : Nat) (T : TyM) : MState.posTyM dm C Γ ρ st (.temp f i) ≠ some T := by
  simp [posTyM_temp]

/-- **What `eval_step_stmt` would have to conclude** for `mkEqM`'s caller to have membership of a
side: a typed run of a non-proof term that returns `(v, some T)` gives a value meaning a (partly
moved) member of the run's type, under every future typed for the state after with the value in
flight. Stated for the context, assignment and renaming the step concludes with. -/
def EvalMemConcl (K' : RunCtx) (ρ' : Assignment) (st' : MState) (v : Value) (R : TyS) : Prop :=
  ∀ ψ, TypedFutureF K'.dm K'.M K'.Γ ρ' (st'.withTemp v) (flightOf R) ψ →
    DataModel.pmem K'.dm.read K'.Γ (meanV K' ρ' ψ R v) R.m

end Ochr.Meaning.Rules
