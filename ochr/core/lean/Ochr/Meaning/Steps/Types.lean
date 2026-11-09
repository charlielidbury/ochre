import Ochr.Meaning.Steps.Borrow

/-!
# Step lemmas, types: `evalType`, `piSort`, `capture`, `evalTInd`, `evalCtor`, `fieldTypes`,
`repackCheck`, `lentUnknown`, `valType?` (milestone 3; docs/18 "Five lemmas behind same")

Types are formed by running code on private copies, so `evalType` is the run of the type term
with the state unchanged. `piSort` must agree with `Decisions.piSort` (aligned, D55). `capture`
rewrites a closure's term so that its free places become capture slots: running the rewritten
body with the captures bound means running the original in the forming frame (the `.fix`
clause reads the original). Constructor values and `D(ā)` are the run's `.ctor`/`.tind`
clauses; `fieldTypesOf`/`fieldTypeAt` compute `DataModel.fieldTy`. The wholeness checks
(`repackCheck`, `repackAt`, `bodyReturns`, `lentUnknown`) are checks: their accepting direction
establishes membership of the checked value under every future of the holes still lent from it
(D73, docs/25 case 1). `valType?` soundness is the second of the five lemmas: the meaning of a
value lies in the meaning of the type the checker reads off it.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- `evalType` (a type term, on a private copy): the result means the run's result, and the
state's core is unchanged. -/
theorem evalType_step (st st' : MState) (fuel : Nat) (t : Term) (T : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (h : Runs (Ochr.evalType fuel t) st fuel T st') :
    st'.core = st.core ∧
    ∃ r s', run K ρ φ (.plain .err) t (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ (.plain .err) T = r.1 := by
  sorry

/-- `piSort` agrees with the aligned decision (D55: a type's declared sort is its computed sort). -/
theorem piSort_aligned (st st' : MState) (fuel : Nat) (caps : List Value) (hs : List Hint)
    (ds : List Term) (c : Term) (rd : List (DeclInfo × Value)) (l : Nat)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.piSort fuel (.tPi caps (.pi hs ds c) rd)) st fuel l st') :
    K.D.piSort (scopeOf (SM' K ρ st)) (.pi hs ds c) = l := by
  sorry

/-- `capture`: the closure value the checker forms (captures by value, the term rewritten to read
them as slots) means what the run's `.fix` clause gives the original term in the forming state. -/
theorem capture_step (st st' : MState) (fuel : Nat) (t : Term) (cs : List Value) (t' : Term)
    (rd : List (DeclInfo × Value))
    (hg : Good K.dm K.C K.Γ ρ st) (hfix : t matches .fix ..)
    (h : Runs (Ochr.capture fuel t) st fuel (cs, t', rd) st') :
    ∃ r s', run K ρ φ (.plain .err) t (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ (.plain .err) (.clo cs t' rd) = r.1 ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st' := by
  sorry

/-- `evalCtor` (a constructor value, its parameters written or inferred): the run's `.ctor`
clause at the hint the context gives. -/
theorem evalCtor_step (st st' : MState) (fuel : Nat) (typed : Bool) (ty : String) (c : Nat) (h0 : Hint)
    (pts as : List Term) (hint : Option Value) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.evalCtor fuel typed ty c h0 pts as hint) st fuel (v, T?) st') :
    let hm : TyS := (hint.map (Value.tyS K.dm K.C K.Γ ρ)).getD (.plain .err)
    ∃ r s', run K ρ φ hm (.ctor ty c h0 pts as) (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ hm v = r.1 ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st' := by
  sorry

/-- `evalTInd`: `D(ā)` means the run's `.tind` clause. -/
theorem evalTInd_step (st st' : MState) (fuel : Nat) (typed : Bool) (n : String) (as : List Term)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.evalTInd fuel typed n as) st fuel (v, T?) st') :
    ∃ r s', run K ρ φ (.plain .err) (.tind n as) (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ (.plain .err) v = r.1 ∧ st'.core = st.core := by
  sorry

/-- `fieldTypesOf`: the checker's field types at parameters and fields mean `DataModel.fieldTy`
at their meanings (the telescope, D64). -/
theorem fieldTypesOf_step (st st' : MState) (fuel : Nat) (d : IndDecl) (ps : List Value) (c : Nat)
    (fs : List Value) (tys : List (String × Value))
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.fieldTypesOf fuel d ps c fs) st fuel tys st') :
    ∀ i T, tys[i]?.map (·.2) = some T →
      (meanV K ρ noFuture (.plain .err) T).asTy =
        K.dm.fieldTy d (Value.meanParams K.dm K.C K.Γ ρ noFuture d 0 [] ps) c i
          (Value.meanFields K.dm K.C K.Γ ρ noFuture d (Value.meanParams K.dm K.C K.Γ ρ noFuture d 0 [] ps) c 0 [] (fs.take i)) := by
  sorry

/-- [Repack]'s accepting direction (`repackCheck`): a value checked whole against `T`, with each
part still lent read as an unknown of its type (D73), is a member of `T` under every typed
future. -/
theorem repackCheck_sound (st st' : MState) (fuel : Nat) (what : String) (v T : Value)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.repackCheck fuel what v T) st fuel () st') :
    TypedFuture K.dm K.C K.Γ ρ st φ →
      meanV K ρ φ (Value.tyS K.dm K.C K.Γ ρ T) v ∈ₛ (meanV K ρ noFuture (.plain .err) T).asTy := by
  sorry

/-- [Return]'s accepting direction (`bodyReturns`): the returned value is a member of its type
and every place held by borrow is whole, under every typed future. -/
theorem bodyReturns_sound (st st' : MState) (fuel : Nat) (what : String) (v T : Value)
    (lent : List Place) (lw : String)
    (hg : Good K.dm K.C K.Γ ρ st)
    (h : Runs (Ochr.bodyReturns fuel what v T lent lw) st fuel () st') :
    TypedFuture K.dm K.C K.Γ ρ st φ →
      meanV K ρ φ (Value.tyS K.dm K.C K.Γ ρ T) v ∈ₛ (meanV K ρ noFuture (.plain .err) T).asTy ∧
      (meanV K ρ φ (Value.tyS K.dm K.C K.Γ ρ T) v).whole := by
  sorry

/-- `valType?` is sound (the second of the five lemmas): the meaning of a value lies in the
meaning of the type the checker reads off it. -/
theorem valType_sound (st st' : MState) (fuel : Nat) (v T : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hv : ∃ p, valAt st.env p = v)
    (h : Runs (Ochr.valType? fuel v) st fuel (some T) st') :
    TypedFuture K.dm K.C K.Γ ρ st φ →
      (meanV K ρ φ (Value.tyS K.dm K.C K.Γ ρ T) v).pmem (meanV K ρ noFuture (.plain .err) T).asTy := by
  sorry

end

end Ochr.Meaning.Steps
