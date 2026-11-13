import Ochr.Meaning.Lemmas
import Ochr.Meaning.HintIndep
import Ochr.Meaning.WF
import Ochr.Machine
import Ochr.Check

/-!
# The step statements (milestone 3), centralised

Re-normalisation (`nfSealed`, inside `substV`, `substEnv`, `endBorrow`, `refine`, `renormAll`)
may run a known callee's body, whose checker run is only *below* the callee's meaning (an early
end inside it), so those steps are stated `⊑`/`Below`, not exact; the leaf's wholeness turns
`⊑` into equality where the main theorem needs it.

Every step lemma of the skeleton as a `Prop` indexed by the fuel of the checker call it speaks
about: `X_stmt K ρ φ fuel`. `Steps/IH.lean` bundles them into `StepsIH fuel`, each area file
(`Steps/Borrow.lean`, …) proves `StepsIH fuel → X_stmt (fuel + 1)`, and `Steps/Knot.lean` ties
the knot by induction on fuel: the checker's functions are mutually recursive on fuel
(`endBorrow → substEnv → substV → nfSealed → eval`), so no step lemma is provable alone (the
pilot prover's finding), while this shape keeps the files independently provable and the import
order irrelevant. The spine owns every definition and statement here; provers own only the area
files' proofs and their private auxiliaries.

Statement fixes from the pilot (`spine-prover-borrow`, Scratch.lean): a value a step returns is
in flight and counts as a temporary of the state (`MState.withTemp`) for `Good` and `Below`
(readPlace, borrowPlace); an assigned value is itself part of a `Good` state (assignPlace); a
dropped or popped position means `err` on both sides (`Env.mean` is bounds-checked); the
knot `K.C = codeMeaning K ρ φ` is a hypothesis (`StepsIH.knot`); [Access] is stated as the
checker's composite `accessPath; accessInside` against `SState.access`.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-! ### Helpers from `Steps/Borrow.lean` -/

/-- `f` run from `st` succeeds with `a` and `st'`. -/
def Runs {α : Type} (f : M α) (st : MState) (fuel : Nat) (a : α) (st' : MState) : Prop :=
  ∃ left log, runMachine f st fuel = (.ok a st', left, log)

/-- The meaning of a checker state as the run sees it (`K.C` is the knot; `K.Δ` is `deltaOf st`,
a hypothesis of every statement). -/
noncomputable def SM' (st : MState) : SState := MState.sstate K.dm K.C K.Γ ρ st

/-- A step is exact: the meanings agree at every position and so do the shapes. -/
def Exact (m m' : Mean) : Prop := (∀ φ p, m.val φ p = m'.val φ p) ∧ ∀ p, m.shape p = m'.shape p

/-! ### Helpers from `Steps/Eq.lean` -/

/-- The truth of a type value read as a proposition. -/
noncomputable def propOf (P : Value) : Prop := ((meanV K ρ φ (.plain .err) P).asTy).true

/-! ### Helpers from `Steps/Borrow.lean` -/

/-- The content of a borrow in a (WF10) state is hint-free when it holds no sealed program: what
[End]'s substitution needs (`substV_loan_step_stmt`'s `hf`), discharged from the clause. -/
theorem hintFree_of_wf10 (st : MState) (hwf : WF10 K.Γ st) (v : Value)
    (hv : v ∈ Env.values st.env) (l : Nat) (w : Value) (hvw : v = .borrow l w)
    (hs : w.anyAtom Value.isSealed = false) : HintFree K ρ φ w := by
  have hb := hwf v hv
  subst hvw
  simp only [Value.anyAtom, Value.bareCtor, Bool.false_or] at hb
  exact hintFree_of_recorded K ρ φ w hb hs

/-- A top-hint-free value (its parameters recorded, its sealed programs with hint-free tails:
[Close]'s results and fills) is `HintFree`: the substitution lemmas' hypothesis at [End] on a
borrow of a closed-off call's result, `HintIndep.lean`. -/
theorem hintFree_of_topHintFree (w : Value) (hw : Value.topHintFree K.Γ w = true) : HintFree K ρ φ w :=
  fun h h' => meanV_hintIndep K ρ φ w hw h h'

/-! ### Helpers from `Steps/Call.lean` -/

/-- The callee as the run sees it: its meaning and its type value's shape. The shape is read
through the run of the type value (the `.pi` clause of `run`); a callee whose type is not a
Π-type has none. -/
noncomputable def calleeRes (fv : Value) (fT : Value) : Res :=
  (meanV K ρ φ (.plain .err) fv,
    match fT with
    | .tPi caps t rd =>
      match piShapeOf K ρ φ (stateOf 0 (capsState (capsVals K ρ φ caps) (capsTys K ρ φ rd))) t with
      | some sh => ⟨(meanV K ρ φ (.plain .err) fT).asTy, some (sh.ps, sh.out), none, none⟩
      | none => .plain .err
    | _ => .plain .err)

/-- The arguments as the run sees them, with each borrow argument's label. -/
noncomputable def argsRes (ws : Array Value) : List Res :=
  ws.toList.map fun w => (meanV K ρ φ (.plain .err) w,
    ⟨.err, none, (match w with | .borrow l _ => some l | _ => none), none⟩)

/-! ### Helpers from `Steps/Match.lean` -/

/-- `ρ'` extends `ρ` on the unknowns of `st`. -/
def Extends (st : MState) (ρ ρ' : Assignment) : Prop := ∀ σ, σ < st.absTy.size → ρ' σ = ρ σ

/-! ### Helpers from `Steps/Obs.lean` -/

/-- The reference observation of a side, if its run succeeds. -/
noncomputable def refObs (reps : List Place) (ws : List Sem) (hint : TyS) (t : Term) (s : SState) : Option (List Sem) :=
  (run K ρ φ hint t s).map fun (r, s') => observation φ reps ws r s'

/-! ### Helpers from `Steps/Eval.lean` -/

/-- The type the context gives, as a `TyM` (`err` when none). -/
noncomputable def hintM (hint : Option Value) : TyS :=
  (hint.map (Value.tyS K.dm K.C K.Γ ρ)).getD (.plain .err)

/-- [End ℓ] (`Machine.endBorrow`): with `ℓ`'s borrow held whole at `r`, the result is `semEnd`
exactly, so it is below (`Mean.semEnd_below`); `Good` is kept. The content must be whole, which
the checker checks outside an observation (D53 (h), D68). -/
def endBorrow_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (l : Nat) (r : Pos)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hr : Env.shape st.env r = some l)
    (h : Runs (Ochr.endBorrow fuel l) st fuel () st'),
    Below (MState.mean K.dm K.C K.Γ ρ st') ((MState.mean K.dm K.C K.Γ ρ st).semEnd r l) ∧
    Good K.dm K.C K.Γ ρ st'

/-- [Access] as the checker performs it before a read (`accessPath` then `accessInside`): a
sequence of [End]s, each below; the ended labels include every label the accessed position's
meaning depends on, so the result is below the reference's `SState.access`, and the accessed
content no longer depends on the future (`Lemmas.meanV_congr`). (`accessPath` alone ends only
the path: the pilot prover's finding, so it is not stated on its own.) -/
def access_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (pos : Pos)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (owned : Bool) (hpos : resolve (SM' K ρ st) p = some (pos, (p.steps).2))
    (h : Runs (do Ochr.accessPath fuel p; Ochr.accessInside fuel p owned) st fuel () st'),
    Below (MState.mean K.dm K.C K.Γ ρ st') ((SM' K ρ st).access pos).toMean ∧
    Good K.dm K.C K.Γ ρ st'

/-- The flight of a result: its label, typed at its content type (the reference's result type
carries both). The in-flight value is typed by this where `MState.withTemp` holds it untyped
(`GoodF`, the pilot's refutations in `BorrowCE.lean`). -/
def flightOf (T : TyS) : Flight := match T.label with | some l => [(l, T.m)] | none => []

/-- The flight of a value about to be written at a place of content type `T`: a borrow's label,
typed at `T`. -/
def flightOfWrite (v : Value) (T : TyM) : Flight := match v with | .borrow l _ => [(l, T)] | _ => []

/-- [Read] (`readPlace`): after its access, the result is the place's meaning (future-free), and
the place is unchanged (a copy, by the declared reading, D80) or `moved` (a move); exact against
the run's `readPlace` with the same copy decision (`Decisions.copy`, aligned). -/
def readPlace_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (v : Value) (copy : Bool)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (hcopy : K.D.copy (K.D.placeDecl (scopeOf (SM' K ρ st)) p) = copy)
    (h : Runs (Ochr.readPlace fuel p) st fuel v st'),
    ∃ r s', Ochr.Meaning.readPlace K φ p copy (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ r.2 v = r.1 ∧
      Below (MState.mean K.dm K.C K.Γ ρ (st'.withTemp v)) s'.toMean ∧
      GoodF K.dm K.C K.Γ ρ (st'.withTemp v) (flightOf r.2)

/-- [Borrow] (`borrowPlace`): exact against the run's `borrowPlace` with the same fresh label
(`nextLoan`): the place means the label's final content and the borrow the old content. -/
def borrowPlace_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (v : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.borrowPlace fuel p) st fuel v st'),
    ∃ r s', Ochr.Meaning.borrowPlace K φ p (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ r.2 v = r.1 ∧
      Below (MState.mean K.dm K.C K.Γ ρ (st'.withTemp v)) s'.toMean ∧
      GoodF K.dm K.C K.Γ ρ (st'.withTemp v) (flightOf r.2)

/-- [Assign] (`assignPlace`): the owned access (D67, ends), the old content's borrows end
([Drop], ends), then the place means the new value: below the run's `setContent` after
`access`. The written value's meaning is given. -/
def assignPlace_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (v : Value) (pos : Pos)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hpos : resolve (SM' K ρ st) p = some (pos, (p.steps).2))
    (hgv : GoodF K.dm K.C K.Γ ρ (st.withTemp v) (flightOfWrite v (Env.hintAt K.dm K.C K.Γ ρ st.env pos).m))
    (h : Runs (Ochr.assignPlace fuel p v) st fuel () st'),
    ∃ s', setContent K φ pos (p.steps).2 (meanV K ρ φ (.plain .err) v) ((SM' K ρ st).access pos) = some (⟨⟩, s') ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st'

/-- [Drop] of the top binding (`dropTopBind`): its borrows end, each live loan in it ends its
borrower when held in a binding (D65), then the binding is gone: ends followed by `forget`,
below. -/
def dropTopBind_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (h : Runs (Ochr.dropTopBind fuel) st fuel () st'),
    Below (MState.mean K.dm K.C K.Γ ρ st') ((SM' K ρ st).dropLast).toMean ∧
    Good K.dm K.C K.Γ ρ st'

/-- Popping a frame (`popFrame`): each binding dropped in turn; below. -/
def popFrame_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    -- the popped frame's temporaries hold no borrow (the pilot's refutation: a pop discards
    -- temporaries without ending them; both call sites move the result below first)
    (htemps : ∀ fr, st.env[st.env.size - 1]? = some fr → ∀ v ∈ fr.temps, v.hasBorrow = false)
    (h : Runs (Ochr.popFrame fuel) st fuel () st'),
    Below (MState.mean K.dm K.C K.Γ ρ st') (MState.mean K.dm K.C K.Γ ρ st) ∧
    Good K.dm K.C K.Γ ρ st'

/-- `substV` of a loan: the result means the value read under the future fixed at `ℓ` to the
filling value's meaning (the pure lemma plus re-normalisation). -/
def substV_loan_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (l : Nat) (w v v' : Value) (hint : TyS)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hw : ¬ w.hasLoan l) (hf : HintFree K ρ φ w)
    (h : Runs (Ochr.substV fuel (.loan l) w v) st fuel v' st'),
    meanV K ρ φ hint v' ⊑ meanV K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint v ∧ st'.core = st.core

/-- `substV` of an abstract value by a refinement `r` it means: exact. -/
def substV_abs_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (σ : Nat) (r v v' : Value) (hint : TyS)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (hσ : ρ σ = meanV K ρ φ (.plain (MState.absTyM K.dm K.C K.Γ ρ st σ)) r)
    (h : Runs (Ochr.substV fuel (.abs σ) r v) st fuel v' st'),
    (∀ φ, meanV K ρ φ hint v' ⊑ meanV K ρ φ hint v) ∧ st'.core = st.core

/-- `substEnv` of a loan (the state-wide half of [End] and of [Close]'s fills): every position
reads the fixed future; stored types are untouched (`types = false`: no type holds a loan). -/
def substEnv_loan_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (l : Nat) (w : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hw : ¬ w.hasLoan l) (hf : HintFree K ρ φ w)
    (h : Runs (Ochr.substEnv fuel (.loan l) w false) st fuel () st'),
    (∀ p, (MState.mean K.dm K.C K.Γ ρ st').val φ p ⊑
        (MState.mean K.dm K.C K.Γ ρ st).val (φ.upd l (meanV K ρ φ (.plain .err) w)) p) ∧
    (∀ p, Env.shape st'.env p = Env.shape st.env p)

/-- `substEnv` of an abstract value by a refinement it means (`types = true`: stored types, Δ
and the goal are refined too): exact, and `Good` is kept. -/
def substEnv_abs_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (σ : Nat) (r : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (hσ : ρ σ = meanV K ρ φ (.plain (MState.absTyM K.dm K.C K.Γ ρ st σ)) r)
    (h : Runs (Ochr.substEnv fuel (.abs σ) r true) st fuel () st'),
    Below (MState.mean K.dm K.C K.Γ ρ st') (MState.mean K.dm K.C K.Γ ρ st) ∧
    Good K.dm K.C K.Γ ρ st'

/-- [Seal]: a re-run of a sealed program means the sealed program (its run), and changes nothing
of the state's core (it runs on a private copy). -/
def nfSealed_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (v : Value) (hint : TyS)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (h : Runs (Ochr.nfSealed fuel t) st fuel v st'),
    (∀ φ, meanV K ρ φ hint v ⊑ meanV K ρ φ hint (.sealed t)) ∧ st'.core = st.core

/-- `canonNeutral`: a sealed program already generalised in this world is its `σ`, which the
path condition makes mean the same. -/
def canonNeutral_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (v v' : Value) (hint : TyS)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (h : Runs (Ochr.canonNeutral v) st 0 v' st'),
    (∀ φ, meanV K ρ φ hint v' = meanV K ρ φ hint v) ∧ st'.core = st.core

/-- `renormAll`: re-running every sealed program of the state keeps every meaning. -/
def renormAll_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (h : Runs (Ochr.renormAll fuel) st fuel () st'),
    Below (MState.mean K.dm K.C K.Γ ρ st') (MState.mean K.dm K.C K.Γ ρ st) ∧
    Good K.dm K.C K.Γ ρ st'

/-- [Split]'s refinement `σ := r` (`refine`): under an assignment that gives `σ` the meaning of
`r` (the arm the assignment selects, with its fields assigned), the substitution is exact and
`Good` is kept; the record in `refs` states no fact. -/
def refine_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (σ : Nat) (r : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (hσ : ρ σ = meanV K ρ φ (.plain (MState.absTyM K.dm K.C K.Γ ρ st σ)) r)
    (h : Runs (Ochr.refine fuel σ r) st fuel () st'),
    Below (MState.mean K.dm K.C K.Γ ρ st') (MState.mean K.dm K.C K.Γ ρ st) ∧
    Good K.dm K.C K.Γ ρ st'

/-- `Eq` computes soundly: whatever `mkEqM` returns means `⟦a⟧ = ⟦b⟧` at `A`, and the state's
core is unchanged. -/
def mkEqM_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (A a b P : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (hA : ∀ φ, (meanV K ρ φ (.plain .err) A).asTy = (meanV K ρ noFuture (.plain .err) A).asTy)
    (h : Runs (Ochr.mkEqM fuel A a b) st fuel P st'),
    (∀ φ, propOf K ρ φ P ↔
      meanV K ρ φ (.plain (meanV K ρ noFuture (.plain .err) A).asTy) a = meanV K ρ φ (.plain (meanV K ρ noFuture (.plain .err) A).asTy) b) ∧
    st'.core = st.core

/-- Conversion is sound: two values convertible at a state, both (partly moved) members of one
type, have equal meanings under every future. The accepting direction only; `convStack` only
makes `conv` answer `false` more often, so no hypothesis on it. -/
def conv_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (v w : Value) (T : TyM)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (hv : (meanV K ρ φ (.plain T) v).pmem T) (hw : (meanV K ρ φ (.plain T) w).pmem T)
    (h : Runs (Ochr.conv fuel v w) st fuel true st'),
    meanV K ρ φ (.plain T) v = meanV K ρ φ (.plain T) w

/-- [Conv-pi]: convertible Π-type values have equal type meanings (equal Lean carriers), by
`funext` over the generic arguments, which range over the whole domain (docs/18 (V4)). -/
def convPi_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (P Q : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (h : Runs (Ochr.convPi fuel P Q) st fuel true st'),
    ∀ φ, (meanV K ρ φ (.plain .err) P).asTy = (meanV K ρ φ (.plain .err) Q).asTy

/-- [Conv-fun]: two function values with convertible observations of their generic calls mean
the same function (extensionality on good carriers, docs/18 (V5), `Slice.pi_ext`). -/
def convFn_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (f g : Value) (T : TyM)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (hf : meanV K ρ φ (.plain T) f ∈ₛ T) (hgm : meanV K ρ φ (.plain T) g ∈ₛ T)
    (h : Runs (Ochr.convFn fuel f g) st fuel true st'),
    meanV K ρ φ (.plain T) f = meanV K ρ φ (.plain T) g

/-- [Rewrite]: when the equation `h : Eq(A, a, b)` is true, the rewritten goal is true iff the
goal is (the occurrences replaced mean the same). -/
def rewriteGoal_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (rev : Bool) (hT : Term) (A a b G G' : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (hh : Runs (Ochr.eval fuel true hT) st fuel (.proof, some (.tEq A a b)) st)
    (h : Runs (Ochr.rewriteGoal fuel rev hT G) st fuel G' st'),
    ∀ φ, propOf K ρ φ (.tEq A a b) → (propOf K ρ φ G' ↔ propOf K ρ φ G)

/-- The meaning of a type value does not depend on the future (docs/27 Lemma 5: no stored type
holds a live loan), at every state the checker reaches. Used to read types under `noFuture`. -/
def type_futureFree_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState) (T : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hT : ∃ p, MState.posTyM K.dm K.C K.Γ ρ st p = some (meanV K ρ noFuture (.plain .err) T).asTy),
    ∀ φ', (meanV K ρ φ (.plain .err) T).asTy = (meanV K ρ φ' (.plain .err) T).asTy

/-- A direct call (`callFn`, untyped or typed): below the reference's `callOf` on the callee's
meaning, and `Good` kept. The arguments are loan-free (WF5, `ArgsLoanFree`). -/
def callFn_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (fv : Value) (fT : Value)
    (ws : Array Value) (tys : Array (Option Value)) (hd : Bool) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hargs : ArgsLoanFree st.env ws)
    -- the callee as the run reads it (`closeCall_step_stmt`); `fT` is the checker's input only
    (fres : Res) (hf : run K ρ φ (.plain .err) (.val fv) (SM' K ρ st) = some (fres, SM' K ρ st))
    (h : Runs (Ochr.callFn fuel typed fv (some fT) ws tys hd) st fuel (v, T?) st'),
    ∃ r s', callOf fres (argsRes K ρ φ ws) (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ r.2 v ⊑ r.1 ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st'

/-- Running a body (`runBody`): the frame pushed with the captures and parameters, the body run,
the frame popped: below the function's meaning applied (the induction hypothesis on the body). -/
def runBody_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (fv : Value) (cs : List Value) (t : Term)
    (rd : List (DeclInfo × Value)) (ws : Array Value) (v : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hargs : ArgsLoanFree st.env ws)
    (hfv : fv = .clo cs t rd ∨ ∃ n, fv = .gfn n)
    -- the callee as the run reads it (the pilot form took `fT` free: `Regress/CloseCallStmt.lean`)
    (fres : Res) (hf : run K ρ φ (.plain .err) (.val fv) (SM' K ρ st) = some (fres, SM' K ρ st))
    (h : Runs (Ochr.runBody fuel fv cs t rd ws) st fuel v st'),
    ∃ r s', callOf fres (argsRes K ρ φ ws) (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ r.2 v ⊑ r.1 ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st'

/-- [Close] (`closeCall`), every row: exact against `callOf`. The result is a sealed program (or
`()` at a declared `Unit`, or a borrow of one), and each lent place a fill: both mean what the
reference's call gives them, since a sealed program means its run.

The callee's meaning and shape are the run's reading of the value (`run (.val fv)`: a closure's
or Π-closure's shape from its term, a global's from `K.C`, an abstract value's from `Δ`; a sealed
callee has no shape yet, docs/31 item 3), not a separately quantified type (the pilot form took
`fT` free, so `fT := .zero` refuted it at once: `Regress/CloseCallStmt.lean`). The row and the
declared-`Unit` readings `kind`, `res`, `fills` and the cells' types `tys` are read off the call
as written (`evalCall`) and trusted; typing makes them agree with the callee's shape, which the
hypotheses `hkind`, `hres`, `hfills`, `htys` state (without them a `res := .unit` at a `Nat`
codomain, or a `fills` entry at a `Nat` cell, made the checker return `()` where the reference
returns the value: the same file). -/
def closeCall_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (fv : Value) (ws : Array Value)
    (kind : Kind) (res : DeclInfo) (fills : Array Bool) (tys : Array (Option Value)) (v : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hargs : ArgsLoanFree st.env ws)
    (fres : Res) (hf : run K ρ φ (.plain .err) (.val fv) (SM' K ρ st) = some (fres, SM' K ρ st))
    (ps : List PiParam) (out : PiOut) (hsh : fres.2.shape = some (ps, out))
    (hkind : kind = .ref ↔ ∃ U, out = .ref U)
    (hres : res = .unit → ∀ B, out = .data B → B ((argsRes K ρ φ ws).map (·.1)) = .ty0 Unit)
    (hfills : ∀ i : Nat, fills.getD i false = true → ∀ p : PiParam, ps[i]? = some p →
      p.dom (((argsRes K ρ φ ws).map (·.1)).take i) = .ty0 Unit)
    (htys : ∀ (i l : Nat) (w : Value), ws[i]? = some (Value.borrow l w) → ∀ p : PiParam, ps[i]? = some p →
      ∃ T : Value, tys[i]? = some (some (Value.tRef T)) ∧
        (Value.tyS K.dm K.C K.Γ ρ T).m = p.dom (((argsRes K ρ φ ws).map (·.1)).take i))
    (h : Runs (Ochr.closeCall fuel fv ws kind res fills tys) st fuel v st'),
    ∃ r s', callOf fres (argsRes K ρ φ ws) (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ r.2 v = r.1 ∧
      Exact (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st'

/-- [Call-type] (`callType`, `declCallType`): the codomain at the arguments is the reference's
result type. -/
def callType_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (piTy : Value) (ws : Array Value)
    (tys : Array (Option Value)) (B : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.callType fuel piTy ws tys) st fuel B st'),
    ∀ ps out, (calleeRes K ρ φ .proof piTy).2.shape = some (ps, out) →
      (meanV K ρ noFuture (.plain .err) B).asTy =
        (match out with
          | .data B' => B' ((argsRes K ρ φ ws).map (·.1))
          | .ref U => U ((argsRes K ρ φ ws).map (·.1)))

/-- [Rec]'s accepting direction (`recCheck`), semantically: for a recursive function whose every
recursive call passes a strict subterm of the entry value, the stages of the `fix` clause
stabilise, so the closure's meaning is not `err` and the guard never fires (docs/24 §4, the
semantic form of [Rec]; `Slice.stage_stable` generalised). Stated on the closure value: its
meaning is a member of its Π-type. -/
def recCheck_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState) (fv : Value) (fT : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    -- `fT` is the value's own declared Π-type, as the checker reads it (the pilot form took it
    -- free: `fT := .zero` refuted it, the defect class of `Regress/CloseCallStmt.lean`)
    (hfT : ∃ st', Runs (Ochr.funType? fuel fv none) st fuel (some fT) st')
    (hacc : ∃ fuel st', Runs (Ochr.checkFix fuel fv [] (match fv with | .clo _ t _ => t | _ => .tt)) st fuel () st'),
    meanV K ρ φ (.plain .err) fv ∈ₛ (meanV K ρ φ (.plain .err) fT).asTy

/-- [Match] on `Nat` with a known constructor (`evalMatch`): below the run's `.matchNat` clause. -/
def evalMatch_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (p : Place) (z s : Term)
    (expected : Option Value) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.evalMatch fuel typed p z s expected) st fuel (v, T?) st'),
    -- the run's hint is the checker's expected type (a free hint against `expected` was refutable
    -- on a hint-dependent arm value)
    ∃ r s', run K ρ φ (hintM K ρ expected) (.matchNat p z s) (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ r.2 v ⊑ r.1 ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st'

/-- [Match] on a declared inductive with a known constructor (`evalMatchInd`): below the run's
`.matchInd` clause. -/
def evalMatchInd_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (p : Place) (ty : String)
    (arms : List (Hint × Term)) (v : Value) (T? : Option Value) (hint : TyS)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.evalMatchInd fuel typed p ty arms) st fuel (v, T?) st'),
    ∃ r s', run K ρ φ hint (.matchInd p ty arms) (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ r.2 v ⊑ r.1 ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st'

/-- A match on a proof, by its type (`evalMatchByType`, D45): the one arm of a one-constructor
proposition, its proof fields `⋆` and its data fields fresh unknowns; below the run's clause for
a proof scrutinee under an assignment extended at those unknowns by the fields of the proof's
witness (the proposition is inhabited, since the scrutinee is a member of it). -/
def evalMatchByType_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (p : Place) (ty : String)
    (arms : List (Hint × Term)) (v : Value) (T? : Option Value) (hint : TyS)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.evalMatchByType fuel typed p ty arms none) st fuel (v, T?) st'),
    ∃ ρ', Extends st ρ ρ' ∧ TypedAssignment K.dm K.C K.Γ ρ' st' ∧
      ∃ r s', run K ρ' φ hint (.matchInd p ty arms) (SM' K ρ' st) = some (r, s') ∧
        meanV K ρ' φ r.2 v ⊑ r.1 ∧
        Below (MState.mean K.dm K.C K.Γ ρ' st') s'.toMean ∧ Good K.dm K.C K.Γ ρ' st'

/-- [Split] coverage: at a place whose content is the unknown `σ` of a data type, every typed
assignment selects a constructor `c` (exactly one: distinct constructors mean distinct tags), and extends to the arm's fresh field unknowns
(`ctorRefinement`) so that `σ`'s refinement is satisfied. -/
def split_coverage_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState) (σ : Nat) (d : IndDecl) (ps : List Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hσ : st.absTy[σ]? = some (.tInd d.name ps)),
    ∃ c ρ' r st', Extends st ρ ρ' ∧
      Runs (Ochr.ctorRefinement fuel d (ps) c) st fuel r st' ∧
      TypedAssignment K.dm K.C K.Γ ρ' st' ∧
      ρ' σ = meanV K ρ' φ (.plain (MState.absTyM K.dm K.C K.Γ ρ' st' σ)) r

/-- [Split-gen] (`generalizeNeutral`): the sealed program `n` at place `p` becomes a fresh `σ`
with the record `n := σ`; under `ρ` extended at `σ` by `⟦n⟧`, the state means the same and the
assignment is typed (the path condition). -/
def generalizeNeutral_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (n : Value) (σ : Nat)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.generalizeNeutral fuel p n) st fuel σ st'),
    -- `n` is read at the type the checker gives `σ` (as `refine_step_stmt`'s `hσ`; a free hint
    -- was refutable: the place read `n` at its own hint, `σ` at the free one)
    let ρ' := ρ.ext σ (meanV K ρ φ (.plain (MState.absTyM K.dm K.C K.Γ ρ st' σ)) n)
    Exact (MState.mean K.dm K.C K.Γ ρ' st') (MState.mean K.dm K.C K.Γ ρ st) ∧
    Good K.dm K.C K.Γ ρ' st'

/-- A stuck block closed off (`closeBlock`): the block is a call of an anonymous function of its
captures, so its sealed result and fills mean what running the match means: below the run's
match clause (the capture by move of a place the selected arm keeps is D84's join, exact; a
split less fine than the arm's own is an over-approximation). The arms are given as the
match term `mt`; `B?` is the match's annotated type. -/
def closeBlock_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (mt : Term) (arms : List BlockArm)
    (B? : Option Value) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (hmt : mt matches .matchNat .. | .matchInd .. | .prim "J" _)
    (h : Runs (Ochr.closeBlock fuel mt arms B?) st fuel (v, T?) st'),
    ∃ r s', run K ρ φ (hintM K ρ B?) mt (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ r.2 v ⊑ r.1 ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st'

/-- Worlds (X1)–(X4), `exitWorld`: the restored state means the snapshot (every component but
the name counters and the types of unknowns created inside the arm is the snapshot's), and is
`Good` for any assignment the snapshot was. -/
def exitWorld_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (w : World)
    (hg : Good K.dm K.C K.Γ ρ w.saved)
    (h : Runs (Ochr.exitWorld w) st 0 () st'),
    Exact (MState.mean K.dm K.C K.Γ ρ st') (MState.mean K.dm K.C K.Γ ρ w.saved) ∧
    (∀ σ, σ < w.saved.absTy.size → st'.absTy[σ]? = w.saved.absTy[σ]?) ∧
    st'.neutrals = w.saved.neutrals ∧ st'.etaRefs = w.saved.etaRefs ∧ st'.goal = w.saved.goal ∧
    Good K.dm K.C K.Γ ρ st'

/-- `observe` (a side on a private copy, a fresh `σ` written through each re-pointed binding
([Obs-ref]), every borrow ended, the result and the owners read): for the written values `ws`
the fresh unknowns mean under the extended assignment, the result and each observed owner mean
their components of the reference observation at the owners' positions; the state is unchanged
(a copy). -/
def observe_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (t : Term) (A : Value) (W : List Pos)
    (r : Value) (ws : List Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.observe fuel typed t A W) st fuel (r, ws) st'),
    st'.core = st.core ∧
    ∃ o, ∃ wsS, refObs K ρ φ (K.D.rePointed (scopeOf (SM' K ρ st)) t) wsS (.plain (meanV K ρ noFuture (.plain .err) A).asTy) t (SM' K ρ st) = some o ∧
      o[0]? = some (meanV K ρ φ (.plain (meanV K ρ noFuture (.plain .err) A).asTy) r) ∧
      ∀ (i j : Nat) (p : Pos), W[i]? = some p → (SM' K ρ st).positions[j]? = some p →
        ws[i]?.map (meanV K ρ φ (.plain .err)) = o.tail[j]?

/-- Footprint coverage (docs/18 "Footprint coverage", the third of the five lemmas): a position
outside the footprint of the two sides means the same after either side. -/
def footprint_coverage_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState) (A t u : Term) (p : Pos) (o₁ o₂ : List Sem) (j : Nat) (reps : List Place) (ws : List Sem)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (hp : p ∉ footprint st.env [t, u]) (hj : (SM' K ρ st).positions[j]? = some p)
    (h₁ : refObs K ρ φ reps ws (.plain (meanV K ρ noFuture (.plain .err) (.sealed A)).asTy) t (SM' K ρ st) = some o₁)
    (h₂ : refObs K ρ φ reps ws (.plain (meanV K ρ noFuture (.plain .err) (.sealed A)).asTy) u (SM' K ρ st) = some o₂),
    o₁.tail[j]? = o₂.tail[j]?

/-- `Id` computes (`idType`): the conjunction over the result and the footprint's owners means
the reference's `Id`, the equality of the two observations; exact, and the state's core is
unchanged. -/
def idType_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (A t u : Term) (P : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.idType fuel typed A t u) st fuel P st'),
    st'.core = st.core ∧
    ∃ r s', run K ρ φ (.plain .err) (.id A t u) (SM' K ρ st) = some (r, s') ∧
      ((meanV K ρ φ (.plain .err) P).asTy).true ↔ (r.1.asTy).true

/-- Owners (RULES §4): every position `owners env l` lists holds, directly or through the content
of a borrow it holds, a loan of `l`; and conversely every position whose meaning depends on `l`
is among them (`Mean.dependsOn`). -/
def owners_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState) (l : Nat) (p : Pos)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hl : liveLoan st.env l = true),
    (MState.mean K.dm K.C K.Γ ρ st).dependsOn p l → p ∈ owners st.env l

/-- `evalType` (a type term, on a private copy): the result means the run's result, and the
state's core is unchanged. -/
def evalType_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (T : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (h : Runs (Ochr.evalType fuel t) st fuel T st'),
    st'.core = st.core ∧
    ∃ r s', run K ρ φ (.plain .err) t (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ (.plain .err) T = r.1

/-- `piSort` agrees with the aligned decision (D55: a type's declared sort is its computed sort). -/
def piSort_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (caps : List Value) (hs : List Hint)
    (ds : List Term) (c : Term) (rd : List (DeclInfo × Value)) (l : Nat)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.piSort fuel (.tPi caps (.pi hs ds c) rd)) st fuel l st'),
    K.D.piSort (scopeOf (SM' K ρ st)) (.pi hs ds c) = l

/-- `capture`: the closure value the checker forms (captures by value, the term rewritten to read
them as slots) means what the run's `.fix` clause gives the original term in the forming state. -/
def capture_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (cs : List Value) (t' : Term)
    (rd : List (DeclInfo × Value))
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hfix : t matches .fix ..)
    (h : Runs (Ochr.capture fuel t) st fuel (cs, t', rd) st'),
    ∃ r s', run K ρ φ (.plain .err) t (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ (.plain .err) (.clo cs t' rd) = r.1 ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st'

/-- `evalCtor` (a constructor value, its parameters written or inferred): the run's `.ctor`
clause at the hint the context gives. -/
def evalCtor_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (ty : String) (c : Nat) (h0 : Hint)
    (pts as : List Term) (hint : Option Value) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.evalCtor fuel typed ty c h0 pts as hint) st fuel (v, T?) st'),
    let hm : TyS := (hint.map (Value.tyS K.dm K.C K.Γ ρ)).getD (.plain .err)
    ∃ r s', run K ρ φ hm (.ctor ty c h0 pts as) (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ hm v = r.1 ∧
      Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st'

/-- `evalTInd`: `D(ā)` means the run's `.tind` clause. -/
def evalTInd_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (n : String) (as : List Term)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.evalTInd fuel typed n as) st fuel (v, T?) st'),
    ∃ r s', run K ρ φ (.plain .err) (.tind n as) (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ (.plain .err) v = r.1 ∧ st'.core = st.core

/-- `fieldTypesOf`: the checker's field types at parameters and fields mean `DataModel.fieldTy`
at their meanings (the telescope, D64). -/
def fieldTypesOf_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (d : IndDecl) (ps : List Value) (c : Nat)
    (fs : List Value) (tys : List (String × Value))
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.fieldTypesOf fuel d ps c fs) st fuel tys st'),
    ∀ i T, tys[i]?.map (·.2) = some T →
      (meanV K ρ noFuture (.plain .err) T).asTy =
        K.dm.fieldTy d (Value.meanParams K.dm K.C K.Γ ρ noFuture d 0 [] ps) c i
          (Value.meanFields K.dm K.C K.Γ ρ noFuture d (Value.meanParams K.dm K.C K.Γ ρ noFuture d 0 [] ps) c 0 [] (fs.take i))

/-- [Repack]'s accepting direction (`repackCheck`): a value checked whole against `T`, with each
part still lent read as an unknown of its type (D73), is a member of `T` under every typed
future. -/
def repackCheck_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (what : String) (v T : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.repackCheck fuel what v T) st fuel () st'),
    TypedFuture K.dm K.C K.Γ ρ st φ →
      meanV K ρ φ (Value.tyS K.dm K.C K.Γ ρ T) v ∈ₛ (meanV K ρ noFuture (.plain .err) T).asTy

/-- [Return]'s accepting direction (`bodyReturns`): the returned value is a member of its type
and every place held by borrow is whole, under every typed future. -/
def bodyReturns_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (what : String) (v T : Value)
    (lent : List Place) (lw : String)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.bodyReturns fuel what v T lent lw) st fuel () st'),
    TypedFuture K.dm K.C K.Γ ρ st φ →
      meanV K ρ φ (Value.tyS K.dm K.C K.Γ ρ T) v ∈ₛ (meanV K ρ noFuture (.plain .err) T).asTy ∧
      (meanV K ρ φ (Value.tyS K.dm K.C K.Γ ρ T) v).whole

/-- `valType?` is sound (the second of the five lemmas): the meaning of a value lies in the
meaning of the type the checker reads off it. -/
def valType_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (v T : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hv : ∃ p, valAt st.env p = v)
    (h : Runs (Ochr.valType? fuel v) st fuel (some T) st'),
    TypedFuture K.dm K.C K.Γ ρ st φ →
      (meanV K ρ φ (Value.tyS K.dm K.C K.Γ ρ T) v).pmem (meanV K ρ noFuture (.plain .err) T).asTy

/-- [Borrow] keeps (WF1)–(WF3): the fresh label is held once, at the destination; the lent
place's content holds no live loan (after [Access]), so the borrow relation stays acyclic. -/
def borrow_wf_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (v : Value)
    (hwf : WF K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (h : Runs (Ochr.borrowPlace fuel p) st fuel v st'),
    WF1 st'.env ∧ WF2 st'.env ∧ WF3 st'.env

/-- [End] keeps (WF1)–(WF3): the ended label leaves Ω; a reborrow's loan in its content moves
to the lender, above it in the borrow relation. (WF2) needs (WF3) here (docs/18 §"Well-formedness"). -/
def end_wf_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (l : Nat)
    (hwf : WF K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (h : Runs (Ochr.endBorrow fuel l) st fuel () st'),
    WF1 st'.env ∧ WF2 st'.env ∧ WF3 st'.env

/-- [Assign] keeps (WF1)–(WF3): D67 ends the loans in the overwritten owned part, and the old
content's borrows end ([Drop]). -/
def assign_wf_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (v : Value)
    (hwf : WF K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (h : Runs (Ochr.assignPlace fuel p v) st fuel () st'),
    WF1 st'.env ∧ WF2 st'.env ∧ WF3 st'.env

/-- [Close] keeps (WF1)–(WF4): the fills are closed sealed programs (C1), the arguments were
loan-free (C8), and a returned borrow's fresh label is held once. -/
def close_wf_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (fv : Value) (ws : Array Value) (kind : Kind)
    (res : DeclInfo) (fills : Array Bool) (tys : Array (Option Value)) (v : Value)
    (hwf : WF K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hargs : ArgsLoanFree st.env ws)
    (h : Runs (Ochr.closeCall fuel fv ws kind res fills tys) st fuel v st'),
    WF1 st'.env ∧ WF2 st'.env ∧ WF3 st'.env ∧ WF4 st'.env

/-- Closure formation keeps (WF4): the captures are read after [Access] (loan-free) and may not
hold `⊥` (the capture check), and a Π-closure captures no borrow (D48). -/
def capture_wf_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (cs : List Value) (t' : Term)
    (rd : List (DeclInfo × Value))
    (hwf : WF K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (h : Runs (Ochr.capture fuel t) st fuel (cs, t', rd) st'),
    ¬ (Value.clo cs t' rd).anyAtom Value.badCapture ∧ WF4 st'.env

/-- Every step of `evalCore` keeps (WF6): names are allocated at and below the counters, which
only grow. -/
def eval_wf6_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (t : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hwf : WF K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (h : Runs (Ochr.evalCore fuel typed t hint) st fuel (v, T?) st'),
    WF6 st' ∧ st.nextAbs ≤ st'.nextAbs ∧ st.nextLoan ≤ st'.nextLoan

/-- Every step of `evalCore` keeps (WF7) and (WF8): the only places a borrow type is formed
check D66 and D48, and no step puts `&` below the top of a type. -/
def eval_wf78_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (t : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hwf : WF K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hprog : t.refsOk = true)
    (h : Runs (Ochr.evalCore fuel typed t hint) st fuel (v, T?) st'),
    WF7 K.dm K.C K.Γ ρ st' ∧ WF8 st'

/-- Types are hole-free at every reachable state (docs/27 Lemma 5): no stored type, type of an
unknown, record or goal holds a live loan. Stated as the invariant the step lemmas carry; it is
what lets types be read under `noFuture`. -/
def types_holeFree_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState) (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st),
    (∀ (f i : Nat) (b : Binding), st.env[f]?.bind (fun fr : Frame => fr.binds[i]?) = some b →
      ∀ T : Value, b.ty = some T → ∀ l ∈ T.loans, liveLoan st.env l = false) ∧
    (∀ T ∈ st.absTy.toList, ∀ l ∈ T.loans, liveLoan st.env l = false) ∧
    (∀ G, st.goal = some G → ∀ l ∈ G.loans, liveLoan st.env l = false)

/-- The induction step. For every `Good` assignment `ρ`, following at each split the arm it
selects, the run of `t` reaches a value below the reference's result, a state below the
reference's, for an assignment `ρ'` extending `ρ` to the unknowns created, and `Good` is kept;
the reference run does not fail. -/
def evalCore_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (t : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.evalCore fuel typed t hint) st fuel (v, T?) st'),
    ∃ ρ', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧
      ∃ r s', run K ρ' φ (hintM K ρ hint) t (SM' K ρ' st) = some (r, s') ∧
        meanV K ρ' φ r.2 v ⊑ r.1 ∧
        (∀ T, T? = some T → (meanV K ρ' noFuture (.plain .err) T).asTy = r.2.m) ∧
        Below (MState.mean K.dm K.C K.Γ ρ' st') s'.toMean ∧ Good K.dm K.C K.Γ ρ' st'

/-- [Let]: the binding is pushed at the right-hand side's type and dropped after the tail
(`dropTopBind`); the run's `.letIn` clause. -/
def letIn_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (h0 : Hint) (u w : Term)
    (hint : Option Value) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.evalCore fuel typed (.letIn h0 u w) hint) st fuel (v, T?) st'),
    ∃ ρ' r s', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧
      run K ρ' φ (hintM K ρ hint) (.letIn h0 u w) (SM' K ρ' st) = some (r, s') ∧
      meanV K ρ' φ r.2 v ⊑ r.1 ∧
      Below (MState.mean K.dm K.C K.Γ ρ' st') s'.toMean ∧ Good K.dm K.C K.Γ ρ' st'

/-- `Eq` (the `.eq` form): both sides on private copies, the type a statement; the result means
`⟦a⟧ = ⟦b⟧` (`Steps/Eq.mkEqM_step`), and the state's core is unchanged. -/
def eq_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (A a b : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.evalCore fuel typed (.eq A a b) hint) st fuel (v, T?) st'),
    st'.core = st.core ∧
    ∃ r s', run K ρ φ (.plain .err) (.eq A a b) (SM' K ρ st) = some (r, s') ∧
      ((meanV K ρ φ (.plain .err) v).asTy).true ↔ (r.1.asTy).true

/-- `J`, both outcomes: computed at convertible endpoints (the transported term runs in place)
or closed off as a stuck block whose one arm is the transported term ([T-J-stuck]); each means
the transported term (docs/24 C9). -/
def J_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (A a b P hh u : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.evalCore fuel typed (.prim "J" [A, a, b, P, hh, u]) hint) st fuel (v, T?) st'),
    ∃ ρ' r s', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧
      run K ρ' φ (hintM K ρ hint) (.prim "J" [A, a, b, P, hh, u]) (SM' K ρ' st) = some (r, s') ∧
      meanV K ρ' φ r.2 v ⊑ r.1 ∧
      Below (MState.mean K.dm K.C K.Γ ρ' st') s'.toMean ∧ Good K.dm K.C K.Γ ρ' st'

/-- A proof position (a proof-returning call, a proof primitive, a proof `let`): its value is
`⋆`, which is a member of its proposition exactly when the proposition is true; the state is
unchanged (a statement runs on a copy). Membership here is where "a proof's value is `⋆`"
(docs/26 row 1, *same* given membership) is discharged. -/
def proof_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (t : Term) (hint : Option Value)
    (T : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (hp : (K.D.flags (scopeOf (SM' K ρ st)) t).2 = true)
    (h : Runs (Ochr.evalCore fuel typed t hint) st fuel (.proof, some T) st'),
    st'.core = st.core ∧ Sem.proof ∈ₛ (meanV K ρ φ (.plain .err) T).asTy

/-- η at `Unit` (D80): where a position's declared reading is `Unit`, the value is `()`, and
`()` is the one element of `⟦Unit⟧`, so the normalisation keeps meaning given membership. -/
def etaUnit_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState) (d : DeclInfo) (v : Value) (hint : TyS)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hd : d = .unit)
    (hv : meanV K ρ φ hint v ∈ₛ .ty0 Unit),
    meanV K ρ φ hint (Ochr.etaUnit d v) = meanV K ρ φ hint v

/-- The generic state of a `fix` is `Good` for every assignment that gives each parameter's
unknown an element of its type (and the goal is a type). -/
def generic_good_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (fv : Value) (cs : List Value) (t : Term)
    (capRec : Array (Option Nat)) (rd : List (DeclInfo × Value))
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.checkFix fuel fv cs t capRec rd) st fuel () st'),
    ∀ ρ', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) →
      TypedAssignment K.dm K.C K.Γ ρ' st' → Good K.dm K.C K.Γ ρ' st'

/-- `checkTail` with a leaf continuation: every typed assignment of the start state reaches a
leaf (coverage along splits), where the continuation's hypotheses hold for the leaf's value and
type, and the leaf's value means the reference run's result at the start. -/
def checkTail_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (k : Value → Value → M Unit)
    (hint : TyS)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.checkTail fuel t k) st fuel () st'),
    ∃ ρ' v T stl stl', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧ Good K.dm K.C K.Γ ρ' stl ∧
      Runs (k v T) stl fuel () stl' ∧
      ∃ r s', run K ρ' φ hint t (SM' K ρ' st) = some (r, s') ∧
        meanV K ρ' φ r.2 v ⊑ r.1 ∧ (meanV K ρ' noFuture (.plain .err) T).asTy = r.2.m

/-- [Def]/[Fix] (`checkFix`): an accepted `fix` means an element of its Π-type (docs/18
Corollary 15): under every assignment of its parameters, the body's reference run gives a
member of the goal, so `mkTele` succeeds and the closure's meaning is in the carrier. -/
def checkFix_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (fv : Value) (cs : List Value) (t : Term)
    (capRec : Array (Option Nat)) (rd : List (DeclInfo × Value)) (fT : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    -- `fT` is the fix's own Π-type (the pilot form's `∨` left `fT` free on one side; the defect
    -- class of `Regress/CloseCallStmt.lean`)
    (hT : ∃ self hs ds c r body, t = .fix self hs ds c r body ∧ fT = .tPi cs (.pi hs ds c) rd)
    (h : Runs (Ochr.checkFix fuel fv cs t capRec rd) st fuel () st'),
    meanV K ρ φ (.plain .err) (.clo cs t rd) ∈ₛ (meanV K ρ φ (.plain .err) fT).asTy

/-- [Const]: an accepted constant's value is a member of its goal, under the empty assignment. -/
def checkConst_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (d : Ochr.Def) (goal v : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (hd : d.doms = [])
    (h : Runs (Ochr.checkDef d) st 2000000 () st')
    (hgl : ∃ g ∈ st'.globals, g.name = d.name ∧ g.ty = goal ∧ g.val = v),
    meanV K ρ φ (Value.tyS K.dm K.C K.Γ ρ goal) v ∈ₛ (meanV K ρ noFuture (.plain .err) goal).asTy

/-- [Ind-decl] (`checkInd`): an accepted declaration satisfies (I1)–(I9), so the data model covers
it (the least fixed point exists in the sort's universe; docs/18 Lemma 2). -/
def checkInd_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (d : IndDecl)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (h : Runs (Ochr.checkInd d) st 2000000 () st'),
    K.dm.covers d

/-- The scope of readings the checker uses at `st`'s top frame is `scopeOf` of its semantic
state (each binding's `decl`, innermost first). -/
def scopeOf_sstate_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState),
    scopeOf (SM' K ρ st) = ((st.env.back?.map (·.binds.toList.map (·.decl))).getD []).reverse

/-- `Decisions.flags` is `Decide.preFlags` where the latter answers. -/
def flags_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (t : Term) (d : DeclInfo) (fl : Bool × Bool)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.preFlags t d) st 2000000 (some fl) st'),
    K.D.flags (scopeOf (SM' K ρ st)) t = fl

/-- `Decisions.placeDecl` is `Decide.placeDecl`. -/
def placeDecl_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (d : DeclInfo)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.placeDecl fuel (scopeOf (SM' K ρ st)) p) st fuel d st'),
    K.D.placeDecl (scopeOf (SM' K ρ st)) p = d

/-- `Decisions.declOf` is `Decide.declOf` (unchecked mode). -/
def declOf_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (d : DeclInfo)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.declOf fuel false (scopeOf (SM' K ρ st)) [] t) st fuel d st'),
    K.D.declOf (scopeOf (SM' K ρ st)) t = d

/-- `Decisions.copy` is `Decide.declCopy`. -/
def copy_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (d : DeclInfo) (b : Bool)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.declCopy fuel d) st fuel b st'),
    K.D.copy d = b

/-- `Decisions.piSort` is `Decide.sortOf` of the Π-type value (D55: declared sort = computed). -/
def piSort_aligned'_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (caps : List Value) (hs : List Hint)
    (ds : List Term) (c : Term) (rd : List (DeclInfo × Value)) (l : Nat)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.sortOf fuel (.tPi caps (.pi hs ds c) rd)) st fuel l st'),
    K.D.piSort (scopeOf (SM' K ρ st)) (.pi hs ds c) = l

/-- D84 [Join]: `Decisions.joinMoves` is `Decide.jdMoves` as `Machine.staticJoin` calls it (the
places already `⊥` at the match as its `entry`). -/
def joinMoves_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (entry ms : List Place) (t : Term)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.jdMoves fuel [] [] t entry) st fuel ms st'),
    K.D.joinMoves (scopeOf (SM' K ρ st)) entry t = ms

/-- D84 [Id-typestate]/[Obs-ref]: `Decisions.rePointed` is the `repointed` component of
`Decide.typeState`, as `Machine.idType` reads it. -/
def rePointed_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (ts : TypeState)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.typeState fuel t) st fuel ts st'),
    K.D.rePointed (scopeOf (SM' K ρ st)) t = ts.repointed

end

end Ochr.Meaning.Steps
