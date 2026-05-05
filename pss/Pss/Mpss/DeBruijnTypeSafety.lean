import Pss.Mpss.DeBruijnTransitivityElim

/-! # `Pss.Mpss.DeBruijnTypeSafety` — de Bruijn type-safety endpoints

This module states the de Bruijn versions of the type-safety endpoints over
the already-ported operational and well-formed judgments. The remaining hard
metatheoretic ingredients are explicit premises rather than axioms.
-/

namespace Pss
namespace DeBruijn

/-- De Bruijn analogue of Lemma 11's use in progress: at the empty context,
`Top` has no function supertype. -/
def NoTopFunctionSupertypes : Prop :=
  ∀ {bound : Term}, WSubMStar [] .top (.abs bound .top) → False

/-- Context-generic form of the `Top`-has-no-function-supertype obstruction.
This is the shape needed by arbitrary-context function-bound inversion. -/
def NoTopFunctionSupertypesAt : Prop :=
  ∀ {Γ : Ctx} {bound : Term}, WSubMStar Γ .top (.abs bound .top) → False

/-- Context-generic abstraction obstruction: `Top` has no abstraction
supertype, regardless of the abstraction body. -/
def NoTopAbstractionSupertypesAt : Prop :=
  ∀ {Γ : Ctx} {bound body : Term}, WSubMStar Γ .top (.abs bound body) → False

/-- The abstraction obstruction specializes to the function-supertype
obstruction used by progress and β preservation. -/
def NoTopFunctionSupertypesAt.of_abs
    (hNoTop : NoTopAbstractionSupertypesAt) :
    NoTopFunctionSupertypesAt :=
  hNoTop

/-- Once de Bruijn Theorem 3 is available at every context, `Top` cannot have a
function supertype at any context. Diagrammatic subtyping from `Top` can only
join at `Top`, while equivalence chains from an abstraction can only target
another abstraction. -/
noncomputable def NoTopFunctionSupertypesAt_of
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ []) :
    NoTopFunctionSupertypesAt := by
  intro Γ bound hTopFun
  obtain ⟨join, hSubTop, hEqAbs⟩ := hTopFun.toMSub_of (hcomm (Γ := Γ))
  have hJoinTop : join = .top := hSubTop.top_inv
  subst hJoinTop
  obtain ⟨bound', body', hAbsTop⟩ := hEqAbs.abs_inv
  cases hAbsTop

/-- Once de Bruijn Theorem 3 is available at every context, `Top` cannot have
any abstraction supertype. -/
noncomputable def NoTopAbstractionSupertypesAt_of
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ []) :
    NoTopAbstractionSupertypesAt := by
  intro Γ bound body hTopAbs
  obtain ⟨join, hSubTop, hEqAbs⟩ := hTopAbs.toMSub_of (hcomm (Γ := Γ))
  have hJoinTop : join = .top := hSubTop.top_inv
  subst hJoinTop
  obtain ⟨bound', body', hAbsTop⟩ := hEqAbs.abs_inv
  cases hAbsTop

/-- Once de Bruijn Theorem 3 is available at the empty context, `Top` cannot
have a function supertype. -/
noncomputable def NoTopFunctionSupertypes_of
    (hcomm : StrongCommutes [] []) :
    NoTopFunctionSupertypes := by
  intro bound hTopFun
  obtain ⟨join, hSubTop, hEqAbs⟩ := hTopFun.toMSub_of hcomm
  have hJoinTop : join = .top := hSubTop.top_inv
  subst hJoinTop
  obtain ⟨bound', body', hAbsTop⟩ := hEqAbs.abs_inv
  cases hAbsTop

/-- The context-generic obstruction specializes to the closed progress
obstruction. -/
def NoTopFunctionSupertypes_of_at
    (hNoTop : NoTopFunctionSupertypesAt) :
    NoTopFunctionSupertypes :=
  hNoTop (Γ := [])

/-- De Bruijn progress, conditional on the `Top`-has-no-function-supertype
fact. A closed well-formed term is an abstraction, `Top`, or takes an
operational step. -/
theorem Theorem_4_DeBruijn_Progress_of
    (hNoTop : NoTopFunctionSupertypes)
    {t : Term} (hwf : WfM [] t) :
    (∃ bound body, t = .abs bound body) ∨
      t = .top ∨
      (∃ t', Step t t') := by
  induction t with
  | bvar i =>
      exact (Term.no_scoped_zero_bvar i hwf.scoped).elim
  | top =>
      exact Or.inr (Or.inl rfl)
  | abs bound body =>
      exact Or.inl ⟨bound, body, rfl⟩
  | app u v ihU ihV =>
      obtain ⟨funBound, hFun, hArg⟩ := hwf.app_inv
      have hScopedU : Term.Scoped 0 u := hFun.scoped_left
      have hScopedV : Term.Scoped 0 v := hArg.scoped_left
      have hwfU : WfM [] u := hFun.wf_left
      have hwfV : WfM [] v := hArg.wf_left
      cases ihU hwfU with
      | inl hAbs =>
          obtain ⟨bound, body, hEqU⟩ := hAbs
          subst hEqU
          cases ihV hwfV with
          | inl _ =>
              exact Or.inr (Or.inr
                ⟨_, StepAt.beta hScopedU hScopedV⟩)
          | inr hVRest =>
              cases hVRest with
              | inl _ =>
                  exact Or.inr (Or.inr
                    ⟨_, StepAt.beta hScopedU hScopedV⟩)
              | inr hStepV =>
                  obtain ⟨v', hStepV⟩ := hStepV
                  exact Or.inr (Or.inr
                    ⟨_, StepAt.appR hScopedU hStepV⟩)
      | inr hURest =>
          cases hURest with
          | inl hTop =>
              subst hTop
              exact (hNoTop hFun).elim
          | inr hStepU =>
              obtain ⟨u', hStepU⟩ := hStepU
              exact Or.inr (Or.inr
                ⟨_, StepAt.appL hStepU hScopedV⟩)

/-- De Bruijn progress from the empty-context strong-commutativity premise
used by Theorem 3. -/
noncomputable def Theorem_4_DeBruijn_Progress_of_StrongCommutativity
    (hcomm : StrongCommutes [] [])
    {t : Term} (hwf : WfM [] t) :
    (∃ bound body, t = .abs bound body) ∨
      t = .top ∨
      (∃ t', Step t t') :=
  Theorem_4_DeBruijn_Progress_of (NoTopFunctionSupertypes_of hcomm) hwf

/-- De Bruijn analogue of Lemma 6's preservation payload for operational
steps at arbitrary context depth. -/
def StepPreservesWfM : Type :=
  ∀ {Γ : Ctx} {t t' : Term}, StepAt Γ.depth t t' → WfM Γ t → WfM Γ t'

/-- Remaining β payload for de Bruijn operational well-formedness
preservation. -/
def StepBetaPreservesWfM : Type :=
  ∀ {Γ : Ctx} {bound body arg : Term},
    WfM Γ (.app (.abs bound body) arg) →
      WfM Γ (Term.instantiate 0 arg body)

/-- De Bruijn analogue of Lemma 7 in the exact β-instantiation shape:
substituting an argument that is a well-subtype of the abstraction bound
preserves body well-formedness. -/
def BetaInstantiationPreservesWfM : Type :=
  ∀ {Γ : Ctx} {bound body arg : Term},
    WSubMStar Γ arg bound →
      WfM ({ bound := bound, kind := .sub } :: Γ) body →
        WfM Γ (Term.instantiate 0 arg body)

/-- Function-bound inversion payload needed by the β case: if an abstraction
has a function supertype, their bounds are transitively well-equivalent. -/
def AbsFunctionBoundInversion : Type :=
  ∀ {Γ : Ctx} {bound body result : Term},
    WSubMStar Γ (.abs bound body) (.abs result .top) →
      WEquMStar Γ bound result

/-- Diagrammatic function-bound inversion payload: after Theorem 3 collapses a
well-subtyping chain between functions to a single diagrammatic subtype step,
the remaining obligation is to recover transitive well-equivalence between the
bounds. -/
def AbsFunctionBoundInversionOfMSub : Type :=
  ∀ {Γ : Ctx} {bound body result : Term},
    WfM Γ (.abs bound body) →
      WfM Γ (.abs result .top) →
    MSub Γ [] (.abs bound body) (.abs result .top) →
      WEquMStar Γ bound result

/-- Type-valued common-reduct diagram for a well-subtyping chain from an
abstraction to a function supertype. This avoids eliminating the Prop-valued
`MSub` witness when constructing Type-valued well-equivalence evidence. -/
structure AbsFunctionBoundDiagram
    (Γ : Ctx) (bound body result : Term) : Type where
  joinBound : Term
  joinBody : Term
  subJoin :
    MSubRedStar Γ [] (.abs bound body) (.abs joinBound joinBody)
  eqJoin :
    MEqRedStar Γ [] (.abs result .top) (.abs joinBound joinBody)
  wfJoinBound : WfM Γ joinBound

/-- Type-valued common-reduct diagram whose reduction chains themselves remain
in `Type`. This is the shape future extraction from `WSubMStar` should
produce to avoid Prop-elimination barriers. -/
structure AbsFunctionBoundChainDiagram
    (Γ : Ctx) (bound body result : Term) : Type where
  joinBound : Term
  joinBody : Term
  subJoin :
    MSubRedChain Γ [] (.abs bound body) (.abs joinBound joinBody)
  eqJoin :
    MEqRedChain Γ [] (.abs result .top) (.abs joinBound joinBody)
  wfJoinBound : WfM Γ joinBound

/-- Generic Type-valued common-reduct diagram for abstraction-to-abstraction
well-subtyping. The function-supertype diagram is the specialization where
the target body is `Top`. -/
structure AbsAbsBoundChainDiagram
    (Γ : Ctx) (bound body result resultBody : Term) : Type where
  joinBound : Term
  joinBody : Term
  subJoin :
    MSubRedChain Γ [] (.abs bound body) (.abs joinBound joinBody)
  eqJoin :
    MEqRedChain Γ [] (.abs result resultBody) (.abs joinBound joinBody)
  wfJoinBound : WfM Γ joinBound

/-- Specialize a generic abstraction-to-abstraction diagram to the
function-supertype diagram used by β preservation. -/
def AbsFunctionBoundChainDiagram.of_abs_abs
    {Γ : Ctx} {bound body result : Term}
    (d : AbsAbsBoundChainDiagram Γ bound body result .top) :
    AbsFunctionBoundChainDiagram Γ bound body result where
  joinBound := d.joinBound
  joinBody := d.joinBody
  subJoin := d.subJoin
  eqJoin := d.eqJoin
  wfJoinBound := d.wfJoinBound

/-- Remaining Type-valued diagram payload for function-bound inversion. -/
def AbsFunctionBoundDiagramPayload : Type :=
  ∀ {Γ : Ctx} {bound body result : Term},
    WSubMStar Γ (.abs bound body) (.abs result .top) →
      AbsFunctionBoundDiagram Γ bound body result

/-- Remaining Type-valued chain-diagram payload for function-bound
inversion. -/
def AbsFunctionBoundChainDiagramPayload : Type :=
  ∀ {Γ : Ctx} {bound body result : Term},
    WSubMStar Γ (.abs bound body) (.abs result .top) →
      AbsFunctionBoundChainDiagram Γ bound body result

/-- One-step well-subtyping abstraction diagram payload. This is the
non-transitive local target for extracting Type-valued diagrams from `WSubM`
while ruling out the branch that factors through `Top`. -/
def WSubMAbsAbsChainDiagramPayload : Type :=
  ∀ {Γ : Ctx} {bound body result resultBody : Term},
    NoTopAbstractionSupertypesAt →
      WfM Γ (.abs bound body) →
        WfM Γ (.abs result resultBody) →
          WSubM Γ (.abs bound body) (.abs result resultBody) →
            AbsAbsBoundChainDiagram Γ bound body result resultBody

/-- Function-bound chain diagrams are the function-supertype specialization
of the one-step abstraction-to-abstraction diagram payload. -/
noncomputable def AbsFunctionBoundChainDiagramPayload_of_wsubm
    (hOne : WSubMAbsAbsChainDiagramPayload) :
    ∀ {Γ : Ctx} {bound body result : Term},
      NoTopAbstractionSupertypesAt →
        WfM Γ (.abs bound body) →
          WfM Γ (.abs result .top) →
            WSubM Γ (.abs bound body) (.abs result .top) →
              AbsFunctionBoundChainDiagram Γ bound body result := by
  intro Γ bound body result hNoTop hwfSource hwfTarget hSub
  exact AbsFunctionBoundChainDiagram.of_abs_abs
    (hOne hNoTop hwfSource hwfTarget hSub)

/-- Reflexive abstraction-to-abstraction chain diagram. -/
def AbsAbsBoundChainDiagram.refl
    {Γ : Ctx} {bound body : Term}
    (hwf : WfM Γ (.abs bound body)) :
    AbsAbsBoundChainDiagram Γ bound body bound body where
  joinBound := bound
  joinBody := body
  subJoin := MSubRedChain.refl
  eqJoin := MEqRedChain.refl
  wfJoinBound := hwf.fun_inv.1

/-- Prepend an equivalence step on the left side of an abstraction diagram. -/
noncomputable def AbsAbsBoundChainDiagram.lf1
    {Γ : Ctx} {bound body bound' body' result resultBody : Term}
    (hred : MEqRed Γ [] (.abs bound body) (.abs bound' body'))
    (d : AbsAbsBoundChainDiagram Γ bound' body' result resultBody) :
    AbsAbsBoundChainDiagram Γ bound body result resultBody where
  joinBound := d.joinBound
  joinBody := d.joinBody
  subJoin := MSubRedChain.trans
    (MSubRedChain.single
      (MSubRed.equ (PrevalidExt.nil hred.prevalid) hred))
    d.subJoin
  eqJoin := d.eqJoin
  wfJoinBound := d.wfJoinBound

/-- Append an equivalence step on the right side of an abstraction diagram. -/
noncomputable def AbsAbsBoundChainDiagram.rgh
    {Γ : Ctx} {bound body result resultBody result' resultBody' : Term}
    (d : AbsAbsBoundChainDiagram Γ bound body result' resultBody')
    (hred : MEqRed Γ [] (.abs result resultBody) (.abs result' resultBody')) :
    AbsAbsBoundChainDiagram Γ bound body result resultBody where
  joinBound := d.joinBound
  joinBody := d.joinBody
  subJoin := d.subJoin
  eqJoin := MEqRedChain.trans (MEqRedChain.single hred) d.eqJoin
  wfJoinBound := d.wfJoinBound

/-- Forget the Type-valued chain structure of a function-bound diagram,
embedding its chains into the existing Prop-valued closures. -/
def AbsFunctionBoundDiagram.of_chain {Γ : Ctx} {bound body result : Term}
    (d : AbsFunctionBoundChainDiagram Γ bound body result) :
    AbsFunctionBoundDiagram Γ bound body result where
  joinBound := d.joinBound
  joinBody := d.joinBody
  subJoin := d.subJoin.to_star
  eqJoin := d.eqJoin.to_star
  wfJoinBound := d.wfJoinBound

/-- A chain-diagram payload can be consumed anywhere the older Prop-closure
diagram payload is expected. -/
def AbsFunctionBoundDiagramPayload.of_chain
    (hDiagram : AbsFunctionBoundChainDiagramPayload) :
    AbsFunctionBoundDiagramPayload := by
  intro Γ bound body result hFun
  exact AbsFunctionBoundDiagram.of_chain (hDiagram hFun)

/-- A Type-valued common-reduct diagram gives the transitive bound
well-equivalence needed by β preservation. -/
noncomputable def AbsFunctionBoundInversion_of_diagram
    (hDiagram : AbsFunctionBoundDiagramPayload) :
    AbsFunctionBoundInversion := by
  intro Γ bound body result hFun
  let d := hDiagram hFun
  have hwfBound : WfM Γ bound := hFun.wf_left.fun_inv.1
  have hwfResult : WfM Γ result := hFun.wf_right.fun_inv.1
  have hBoundJoin : MEqRedStar Γ [] bound d.joinBound :=
    MSubRedStar.abs_bound_red d.subJoin
  have hResultJoin : MEqRedStar Γ [] result d.joinBound :=
    MEqRedStar.abs_bound_red d.eqJoin
  have hLeft : WEquMStar Γ bound d.joinBound :=
    WEquMStar.of_MEqRedStar_fwd_of_wf hBoundJoin hwfBound d.wfJoinBound
  have hRight : WEquMStar Γ d.joinBound result :=
    WEquMStar.of_MEqRedStar_back_of_wf hResultJoin hwfResult d.wfJoinBound
  exact WEquMStar.trans d.wfJoinBound hLeft hRight

/-- A Type-valued chain common-reduct diagram also gives the transitive bound
well-equivalence needed by β preservation. -/
noncomputable def AbsFunctionBoundInversion_of_chain_diagram
    (hDiagram : AbsFunctionBoundChainDiagramPayload) :
    AbsFunctionBoundInversion := by
  intro Γ bound body result hFun
  let d := hDiagram hFun
  have hwfBound : WfM Γ bound := hFun.wf_left.fun_inv.1
  have hwfResult : WfM Γ result := hFun.wf_right.fun_inv.1
  have hBoundJoin : MEqRedChain Γ [] bound d.joinBound :=
    MSubRedChain.abs_bound_chain d.subJoin
  have hResultJoin : MEqRedChain Γ [] result d.joinBound :=
    MEqRedChain.abs_bound_chain d.eqJoin
  have hLeft : WEquMStar Γ bound d.joinBound :=
    WEquMStar.of_MEqRedStar_fwd_of_wf hBoundJoin.to_star
      hwfBound d.wfJoinBound
  have hRight : WEquMStar Γ d.joinBound result :=
    WEquMStar.of_MEqRedStar_back_of_wf hResultJoin.to_star
      hwfResult d.wfJoinBound
  exact WEquMStar.trans d.wfJoinBound hLeft hRight

/-- One-step abstraction-function subtype inversion: any direct empty-stack
subtype reduction from one abstraction to another can only change the bound by
an equivalence reduction. -/
noncomputable def MSubRed.abs_function_bound_inversion
    {Γ : Ctx} {bound body result : Term}
    (_hwfSource : WfM Γ (.abs bound body))
    (hwfTarget : WfM Γ (.abs result .top))
    (h : MSubRed Γ [] (.abs bound body) (.abs result .top)) :
    WEquMStar Γ bound result := by
  have hwfResult : WfM Γ result := hwfTarget.fun_inv.1
  have hwfBound : WfM Γ bound := _hwfSource.fun_inv.1
  cases h with
  | equ _ hEq =>
      cases hEq with
      | fun_ hBound _ =>
          exact WEquMStar.of_WEquM hwfBound hwfResult
            (WEquM.lf1 hBound (WEquM.rfl hwfResult))
  | fun_ _ hBound _ =>
      exact WEquMStar.of_WEquM hwfBound hwfResult
        (WEquM.lf1 hBound (WEquM.rfl hwfResult))

/-- The arbitrary-context β inversion payload follows from context-generic
Theorem 3 and the single-diagrammatic-step abstraction-bound inversion. -/
noncomputable def AbsFunctionBoundInversion_of_msub
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ [])
    (hInv : AbsFunctionBoundInversionOfMSub) :
    AbsFunctionBoundInversion := by
  intro Γ bound body result hFun
  exact hInv hFun.wf_left hFun.wf_right
    (hFun.toMSub_of (hcomm (Γ := Γ)))

/-- The β preservation payload follows from function-bound inversion and the
exact de Bruijn body-instantiation preservation lemma. -/
noncomputable def StepBetaPreservesWfM_of
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversion) :
    StepBetaPreservesWfM := by
  intro Γ bound body arg hwf
  obtain ⟨result, hFun, hArg⟩ := hwf.app_inv
  have hEquBoundResult : WEquMStar Γ bound result := hInv hFun
  have hSubResultBound : WSubMStar Γ result bound :=
    hEquBoundResult.symm.toWSubMStar
  have hwfAbs : WfM Γ (.abs bound body) := hFun.wf_left
  have hAbsParts := hwfAbs.fun_inv
  have hwfResult : WfM Γ result := hArg.wf_right
  have hStarArgBound : WSubMStar Γ arg bound :=
    WSubMStar.trs hArg hwfResult hSubResultBound
  exact hSubst hStarArgBound hAbsParts.2

/-- Remaining `.sub` head replacement payload for de Bruijn well-formedness.
This is the de Bruijn narrowing/replacement bridge needed when an abstraction
bound changes. -/
def WfMSubHeadReplace : Type :=
  ∀ {Γ : Ctx} {old new body : Term},
    MEqRed Γ [] old new →
      WfM ({ bound := old, kind := .sub } :: Γ) body →
        WfM ({ bound := new, kind := .sub } :: Γ) body

/-- Sharpened `.sub` head replacement payload for the operational
abstraction-bound case. The step proof already has `WfM Γ new`, so callers do
not need the stronger replacement theorem that works without it. -/
def WfMSubHeadReplaceOfNewWf : Type :=
  ∀ {Γ : Ctx} {old new body : Term},
    MEqRed Γ [] old new →
      WfM Γ new →
        WfM ({ bound := old, kind := .sub } :: Γ) body →
          WfM ({ bound := new, kind := .sub } :: Γ) body

namespace StepAt

/-- All structural operational well-formedness preservation cases reduce to
the β payload and the abstraction-bound replacement payload. The result is
wrapped in `Nonempty` because `StepAt` is `Prop`-valued while `WfM` is
`Type`-valued. -/
theorem wf_right_nonempty_of
    (hBeta : StepBetaPreservesWfM)
    (hSubHeadReplace : WfMSubHeadReplace)
    {depth : Nat} {t t' : Term} (hstep : StepAt depth t t') :
    Nonempty (∀ {Γ : Ctx}, Γ.depth = depth → WfM Γ t → WfM Γ t') := by
  induction hstep with
  | beta =>
      exact ⟨fun {Γ} _hdepth hwf => hBeta (Γ := Γ) hwf⟩
  | @appL depth op op' arg hOp _hArgScoped ih =>
      exact ⟨fun {Γ} hdepth hwf =>
        let ⟨funBound, hFun, hArg⟩ := hwf.app_inv
        let hwfOp' : WfM Γ op' := ih.some hdepth hFun.wf_left
        let hBack : WSubMStar Γ op' op :=
          WSubMStar.of_StepAt_back (by simpa [hdepth] using hOp)
            hFun.wf_left hwfOp'
        WfM.app (WSubMStar.trans hFun.wf_left hBack hFun) hArg⟩
  | @appR depth op arg arg' _hOpScoped hArgStep ih =>
      exact ⟨fun {Γ} hdepth hwf =>
        let ⟨funBound, hFun, hArg⟩ := hwf.app_inv
        let hwfArg' : WfM Γ arg' := ih.some hdepth hArg.wf_left
        let hBack : WSubMStar Γ arg' arg :=
          WSubMStar.of_StepAt_back (by simpa [hdepth] using hArgStep)
            hArg.wf_left hwfArg'
        WfM.app hFun (WSubMStar.trans hArg.wf_left hBack hArg)⟩
  | @absBound depth bound bound' body hBound _hBodyScoped _ih =>
      exact ⟨fun {Γ} hdepth hwf =>
        let hParts := hwf.fun_inv
        let hwfBound' : WfM Γ bound' := _ih.some hdepth hParts.1
        let hEqBound : MEqRed Γ [] bound bound' :=
          MEqRed.of_StepAt (by simpa [hdepth] using hBound) rfl
            (PrevalidExt.nil hParts.1.prevalid)
        WfM.fun_ hwfBound' (hSubHeadReplace hEqBound hParts.2)⟩
  | @absBody depth bound body body' _hBoundScoped hBody ih =>
      exact ⟨fun {Γ} hdepth hwf =>
        let hParts := hwf.fun_inv
        let hBody' : WfM ({ bound := bound, kind := .sub } :: Γ) body' :=
          ih.some (by simpa [Ctx.depth, hdepth]) hParts.2
        WfM.fun_ hParts.1 hBody'⟩

/-- Sharpened variant of `StepAt.wf_right_nonempty_of`: the abstraction-bound
case only requires replacement when the new bound is already well-formed in
the ambient context. -/
theorem wf_right_nonempty_of_new_wf
    (hBeta : StepBetaPreservesWfM)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf)
    {depth : Nat} {t t' : Term} (hstep : StepAt depth t t') :
    Nonempty (∀ {Γ : Ctx}, Γ.depth = depth → WfM Γ t → WfM Γ t') := by
  induction hstep with
  | beta =>
      exact ⟨fun {Γ} _hdepth hwf => hBeta (Γ := Γ) hwf⟩
  | @appL depth op op' arg hOp _hArgScoped ih =>
      exact ⟨fun {Γ} hdepth hwf =>
        let ⟨funBound, hFun, hArg⟩ := hwf.app_inv
        let hwfOp' : WfM Γ op' := ih.some hdepth hFun.wf_left
        let hBack : WSubMStar Γ op' op :=
          WSubMStar.of_StepAt_back (by simpa [hdepth] using hOp)
            hFun.wf_left hwfOp'
        WfM.app (WSubMStar.trans hFun.wf_left hBack hFun) hArg⟩
  | @appR depth op arg arg' _hOpScoped hArgStep ih =>
      exact ⟨fun {Γ} hdepth hwf =>
        let ⟨funBound, hFun, hArg⟩ := hwf.app_inv
        let hwfArg' : WfM Γ arg' := ih.some hdepth hArg.wf_left
        let hBack : WSubMStar Γ arg' arg :=
          WSubMStar.of_StepAt_back (by simpa [hdepth] using hArgStep)
            hArg.wf_left hwfArg'
        WfM.app hFun (WSubMStar.trans hArg.wf_left hBack hArg)⟩
  | @absBound depth bound bound' body hBound _hBodyScoped _ih =>
      exact ⟨fun {Γ} hdepth hwf =>
        let hParts := hwf.fun_inv
        let hwfBound' : WfM Γ bound' := _ih.some hdepth hParts.1
        let hEqBound : MEqRed Γ [] bound bound' :=
          MEqRed.of_StepAt (by simpa [hdepth] using hBound) rfl
            (PrevalidExt.nil hParts.1.prevalid)
        WfM.fun_ hwfBound'
          (hSubHeadReplace hEqBound hwfBound' hParts.2)⟩
  | @absBody depth bound body body' _hBoundScoped hBody ih =>
      exact ⟨fun {Γ} hdepth hwf =>
        let hParts := hwf.fun_inv
        let hBody' : WfM ({ bound := bound, kind := .sub } :: Γ) body' :=
          ih.some (by simpa [Ctx.depth, hdepth]) hParts.2
        WfM.fun_ hParts.1 hBody'⟩

end StepAt

/-- De Bruijn operational well-formedness preservation reduced to the two
remaining hard payloads: β instantiation and `.sub` head replacement. -/
noncomputable def StepPreservesWfM_of
    (hBeta : StepBetaPreservesWfM)
    (hSubHeadReplace : WfMSubHeadReplace) :
    StepPreservesWfM := by
  intro Γ t t' hstep hwf
  exact (StepAt.wf_right_nonempty_of hBeta hSubHeadReplace hstep).some rfl hwf

/-- De Bruijn operational well-formedness preservation reduced to β
instantiation and the sharpened `.sub` head replacement payload that receives
well-formedness of the new bound. -/
noncomputable def StepPreservesWfM_of_new_wf
    (hBeta : StepBetaPreservesWfM)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf) :
    StepPreservesWfM := by
  intro Γ t t' hstep hwf
  exact (StepAt.wf_right_nonempty_of_new_wf hBeta hSubHeadReplace hstep).some
    rfl hwf

/-- Operational well-formedness preservation reduced to the lower-level β
components and the sharpened `.sub` head replacement payload. -/
noncomputable def StepPreservesWfM_of_components
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversion)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf) :
    StepPreservesWfM :=
  StepPreservesWfM_of_new_wf
    (StepBetaPreservesWfM_of hSubst hInv)
    hSubHeadReplace

/-- β preservation reduced directly to the Type-valued function-bound diagram
payload and the body-instantiation lemma. -/
noncomputable def StepBetaPreservesWfM_of_diagram
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundDiagramPayload) :
    StepBetaPreservesWfM :=
  StepBetaPreservesWfM_of hSubst
    (AbsFunctionBoundInversion_of_diagram hDiagram)

/-- Operational well-formedness preservation reduced to the body-instantiation
lemma, the Type-valued function-bound diagram payload, and sharpened `.sub`
head replacement. -/
noncomputable def StepPreservesWfM_of_diagram_components
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundDiagramPayload)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf) :
    StepPreservesWfM :=
  StepPreservesWfM_of_new_wf
    (StepBetaPreservesWfM_of_diagram hSubst hDiagram)
    hSubHeadReplace

/-- β preservation reduced directly to the Type-valued function-bound
chain-diagram payload and the body-instantiation lemma. -/
noncomputable def StepBetaPreservesWfM_of_chain_diagram
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundChainDiagramPayload) :
    StepBetaPreservesWfM :=
  StepBetaPreservesWfM_of hSubst
    (AbsFunctionBoundInversion_of_chain_diagram hDiagram)

/-- Operational well-formedness preservation reduced to the body-instantiation
lemma, the Type-valued function-bound chain diagram payload, and sharpened
`.sub` head replacement. -/
noncomputable def StepPreservesWfM_of_chain_diagram_components
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundChainDiagramPayload)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf) :
    StepPreservesWfM :=
  StepPreservesWfM_of_new_wf
    (StepBetaPreservesWfM_of_chain_diagram hSubst hDiagram)
    hSubHeadReplace

/-- De Bruijn preservation, conditional on operational well-formedness
preservation. The operational step is at the ambient context depth so the
closed case specializes to `Step`. -/
noncomputable def Theorem_5_DeBruijn_Preservation_of
    (hStepPres : StepPreservesWfM)
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u := by
  have hwfT : WfM Γ t := hwf.wf_left
  have hwfT' : WfM Γ t' := hStepPres hstep hwfT
  have hBack : WSubMStar Γ t' t :=
    WSubMStar.of_StepAt_back hstep hwfT hwfT'
  exact WSubMStar.trans hwfT hBack hwf

/-- Closed-term specialization of de Bruijn preservation, using the
operational `Step` alias. -/
noncomputable def Theorem_5_DeBruijn_ClosedPreservation_of
    (hStepPres : StepPreservesWfM)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_Preservation_of hStepPres hwf hstep

end DeBruijn
end Pss
