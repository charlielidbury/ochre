import Ochr.Meaning.Steps.EvalMem

/-!
# Part (II) of the plan of record, against an abstract strict run (sixth lead, docs/31 D86)

The proof's two halves meet at "the strict reference run succeeds" (docs/31 D83, D86). (I), the
fundamental lemma of the model, is `model1`'s (branch `spine-model`). This file states (II), the
simulation, against the strict run as an abstract interface (`StrictRun`), so that when `model1`'s
definitions land only an instance is supplied. What the interface asks of `model1` is exactly what
the lead's report listed: (a) a strict run with `runT`'s signature; (c) a predicate on reference
states (`SGood`) and the fundamental lemma over it, at every future the relation compares.

Proved here: the membership of an evaluated value at the run's future follows from (II)'s
conclusion and (I) (`evalMem_of_strict`). Stated: the evaluation step in the strict form
(`eval_step_stmtS`), with typed temporaries (D81) and no hole in the term (D84), and the bridge from
the reference state's `SGood` to the checker state's membership (`membershipT_of_sgood`).
-/

namespace Ochr.Meaning.Steps
open Ochr Ochr.Meaning

/-! ## Holes -/

mutual
/-- The term holds a hole `?` somewhere (embedded values are the state's: a clause of the state's
invariant says no code it holds has a hole, docs/31 D84). -/
def _root_.Ochr.Term.hasHolePrim : Term → Bool
  | .prim "hole" _ => true
  | .prim _ as | .tind _ as => Term.hasHolePrimList as
  | .assign _ t | .succ t | .ref t => t.hasHolePrim
  | .letIn _ t u | .seq t u | .cong t u | .ascribe t u => t.hasHolePrim || u.hasHolePrim
  | .matchNat _ z s => z.hasHolePrim || s.hasHolePrim
  | .pi _ ds c => Term.hasHolePrimList ds || c.hasHolePrim
  | .fix _ _ ds c _ b => Term.hasHolePrimList ds || c.hasHolePrim || b.hasHolePrim
  | .call f as _ => f.hasHolePrim || Term.hasHolePrimList as
  | .eq a b c | .id a b c => a.hasHolePrim || b.hasHolePrim || c.hasHolePrim
  | .ctor _ _ _ ps as => Term.hasHolePrimList ps || Term.hasHolePrimList as
  | .matchInd _ _ arms => Term.hasHolePrimArms arms
  | _ => false
termination_by structural t => t

def _root_.Ochr.Term.hasHolePrimList : List Term → Bool
  | [] => false
  | t :: ts => t.hasHolePrim || Term.hasHolePrimList ts
termination_by structural ts => ts

def _root_.Ochr.Term.hasHolePrimArms : List (Hint × Term) → Bool
  | [] => false
  | (_, t) :: ts => t.hasHolePrim || Term.hasHolePrimArms ts
termination_by structural ts => ts
end

/-! ## The interface `model1` supplies -/

/-- **A strict reference run and its fundamental lemma** (docs/31 D83, D86): what (II) is stated
against. `runS` has `runT`'s signature; `SGood K ρ φ s` says the reference state's positions hold
members of their types (and its live labels' records are whole members); `fund` is (I): a successful
strict run from such a state returns a (possibly partly moved) member of the type it returns, and
leaves such a state. Stated at every future, so that the bridge to the checker's `Good` is pointwise. -/
structure StrictRun where
  runS : RunCtx → Assignment → Future → Bool → TyS → Term → SM Res
  SGood : RunCtx → Assignment → Future → SState → Prop
  fund : ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (t : Term) (s s' : SState) (r : Res),
    SGood K ρ φ s → runS K ρ φ tl h t s = some (r, s') →
      DataModel.pmem K.dm K.Γ r.1 r.2.m ∧ SGood K ρ φ s'

section
variable (SR : StrictRun) (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **(II)'s conclusion for a step returning a value**: `SimConclTT` (typed temporaries) with the
strict run in place of the reference run, and the reference state after it `SGood`. -/
def SimConclS (π : Nat → Nat) (st st' : MState) (tt : TempTys) (s : SState) (tl : Bool) (h : TyS)
    (t : Term) (v : Value) (T? : Option Value) : Prop :=
  ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (r : Res) (s' : SState), st.absTy.size ≤ st'.absTy.size ∧
    st.nextLoan ≤ st'.nextLoan ∧ (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧ (∀ l, l < st.nextLoan → π' l = π l) ∧
    SR.runS { K with Δ := Δ' } ρ' φ tl h t s = some (r, s') ∧
    meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧
    (∀ T, T? = some T → StrAgree { K with Δ := Δ' } ρ' T r.2) ∧
    CtxOk { K with Δ := Δ' } ρ' st' ∧ Rel { K with Δ := Δ' } ρ' φ π' (st'.withTemp v) s' ∧
    GoodT K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' (st'.withTemp v) (tt.push st' T?)

/-- **The membership of an evaluated value, from (II) and (I)** (proved): where the strict run
succeeded from an `SGood` reference state, the checker's value means, at the run's future pulled
back along the renaming and at the run's type, a (possibly partly moved) member of that type. With
`StrAgree` that type is the checker's. (Taking it at every typed future needs the extension's values
not to depend on the future: docs/31 D83's technical point.) -/
theorem evalMem_of_strict (K' : RunCtx) (ρ' : Assignment) (π' : Nat → Nat) (tl : Bool) (h : TyS) (t : Term)
    (s s' : SState) (r : Res) (v : Value) (hS : SR.SGood K' ρ' φ s) (hrun : SR.runS K' ρ' φ tl h t s = some (r, s'))
    (hmean : meanV K' ρ' (fun l => φ (π' l)) r.2 v = r.1) :
    DataModel.pmem K'.dm K'.Γ (meanV K' ρ' (fun l => φ (π' l)) r.2 v) r.2.m := by
  rw [hmean]
  exact (SR.fund K' ρ' φ tl h t s s' r hS hrun).1

end

section
variable (SR : StrictRun) (K : RunCtx) (ρ : Assignment) (φ : Future)

set_option linter.unusedVariables false in
/-- **The evaluation step in (II)'s form** (the form `eval_step_stmt` takes once `model1`'s strict run
lands): from a state good with its temporaries typed, related to an `SGood` reference state, for a
term holding no hole (`OpenFalse.eval_hole_false`: the reference has no clause for `?`), the strict
run succeeds (for an untyped run, given that it does: `hok`), the states after are related, and the
value returned sits in flight at the type returned. Under (C) an untyped run's value is typed too: its
membership is (I)'s, given `hok`, so the temporary takes whatever type the run returned. -/
def eval_step_stmtS (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (tt : TempTys) (typed : Bool) (t : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hg : GoodT K.dm K.M K.Γ ρ st tt) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s) (hS : SR.SGood K ρ φ s)
    (hnh : t.hasHolePrim = false)
    (hok : typed = false → (SR.runS K ρ φ st.tailNext (hintM K ρ hint) t s).isSome)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.eval fuel typed t hint) st bh (v, T?) st'),
    SimConclS SR K ρ φ π st st' tt s st.tailNext (hintM K ρ hint) t v T?

/-- (leaf, a guess) **The bridge from the reference state's `SGood` to the checker state's
membership**: at related states, if the reference state is `SGood` at every future the relation
compares (agreeing with the run's off the live labels, typed at them), every typed position of the
checker's state, temporaries included, holds a member at every future of the checker's that is the
pull-back of such a future. The relation gives the meanings equal at those futures (`Rel.sim`); the
checker's stored type is the reference's by the skeleton (`Rel.skel`) for bindings and by the
temporary's typing for temporaries. Open point: `MembershipT` quantifies over EVERY typed future of
the checker's state, including ones that differ from the run's off the live labels, where the two
states are not compared (an inert loan in a sealed program reads the future there, docs/31 D20 item 2). -/
theorem membershipT_of_sgood (π : Nat → Nat) (st : MState) (tt : TempTys) (s : SState)
    (hs : Rel K ρ φ π st s) (hS : ∀ ψ, RelF φ s ψ → TypedLive K s ψ → SR.SGood K ρ ψ s) :
    ∀ ψ, RelF φ s ψ → TypedLive K s ψ → ∀ p T, MState.posTyMT K.dm K.M K.Γ ρ st tt p = some T →
      DataModel.pmem K.dm K.Γ (Env.meanT K.dm K.M K.Γ ρ (fun l => ψ (π l)) st.env tt p) T := by
  sorry

end

end Ochr.Meaning.Steps
