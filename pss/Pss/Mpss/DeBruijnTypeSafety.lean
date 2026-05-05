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

/-- Named de Bruijn Theorem 4 obstruction: context-generic function
supertypes of `Top` are impossible once Theorem 3 is available at every
context. -/
noncomputable def Theorem_4_DeBruijn_NoTopFunctionSupertypesAt_of
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ []) :
    NoTopFunctionSupertypesAt :=
  NoTopFunctionSupertypesAt_of hcomm

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

/-- Named de Bruijn Theorem 4 obstruction: context-generic abstraction
supertypes of `Top` are impossible once Theorem 3 is available at every
context. -/
noncomputable def Theorem_4_DeBruijn_NoTopAbstractionSupertypesAt_of
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ []) :
    NoTopAbstractionSupertypesAt :=
  NoTopAbstractionSupertypesAt_of hcomm

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

/-- Named de Bruijn Theorem 4 closed obstruction: at the empty context,
function supertypes of `Top` are impossible once Theorem 3 is available. -/
noncomputable def Theorem_4_DeBruijn_NoTopFunctionSupertypes_of
    (hcomm : StrongCommutes [] []) :
    NoTopFunctionSupertypes :=
  NoTopFunctionSupertypes_of hcomm

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

/-- Function-bound inversion under the well-formed-equivalence context
invariant used by contextual preservation. This is weaker than the
context-generic inversion payload and matches the actual invariant available
in the recursive `MEqRed` preservation proof. -/
def AbsFunctionBoundInversionUnderWfCtx : Type :=
  ∀ {Γ : Ctx} {bound body result : Term},
    WfCtxEqu Γ →
      WSubMStar Γ (.abs bound body) (.abs result .top) →
        WEquMStar Γ bound result

/-- A context-generic function-bound inversion payload specializes to the
well-formed-equivalence context invariant. -/
def AbsFunctionBoundInversionUnderWfCtx.of_global
    (hInv : AbsFunctionBoundInversion) :
    AbsFunctionBoundInversionUnderWfCtx := by
  intro Γ bound body result _hΓ hFun
  exact hInv hFun

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

/-- Type-valued diagrammatic common reduct for one well-subtyping
derivation. This mirrors `MSub` but keeps both reduction chains in `Type`, so
later payloads can construct evidence without eliminating a Prop-valued
existential. -/
structure WSubMChainDiagram (Γ : Ctx) (source target : Term) : Type where
  join : Term
  subJoin : MSubRedChain Γ [] source join
  eqJoin : MEqRedChain Γ [] target join

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

/-- Shape-only version of the Type-valued function-bound common-reduct
diagram. It records that the common reduct is an abstraction, but leaves the
well-formedness of the joined bound as an explicit later obligation. -/
structure AbsFunctionBoundChainShape
    (Γ : Ctx) (bound body result : Term) : Type where
  joinBound : Term
  joinBody : Term
  subJoin :
    MSubRedChain Γ [] (.abs bound body) (.abs joinBound joinBody)
  eqJoin :
    MEqRedChain Γ [] (.abs result .top) (.abs joinBound joinBody)

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

/-- Forget only the bound well-formedness component of a function-bound chain
diagram. -/
def AbsFunctionBoundChainShape.of_diagram
    {Γ : Ctx} {bound body result : Term}
    (d : AbsFunctionBoundChainDiagram Γ bound body result) :
    AbsFunctionBoundChainShape Γ bound body result where
  joinBound := d.joinBound
  joinBody := d.joinBody
  subJoin := d.subJoin
  eqJoin := d.eqJoin

/-- Complete a shape-only function-bound diagram once the joined bound is
known well formed. -/
def AbsFunctionBoundChainShape.to_diagram
    {Γ : Ctx} {bound body result : Term}
    (d : AbsFunctionBoundChainShape Γ bound body result)
    (hwfJoinBound : WfM Γ d.joinBound) :
    AbsFunctionBoundChainDiagram Γ bound body result where
  joinBound := d.joinBound
  joinBody := d.joinBody
  subJoin := d.subJoin
  eqJoin := d.eqJoin
  wfJoinBound := hwfJoinBound

/-- Remaining Type-valued diagram payload for function-bound inversion. -/
def AbsFunctionBoundDiagramPayload : Type :=
  ∀ {Γ : Ctx} {bound body result : Term},
    WSubMStar Γ (.abs bound body) (.abs result .top) →
      AbsFunctionBoundDiagram Γ bound body result

/-- Remaining shape-only Type-valued chain-diagram payload for
function-bound inversion. It packages the common-reduct shape separately
from the joined-bound well-formedness proof. -/
def AbsFunctionBoundChainShapePayload : Type :=
  ∀ {Γ : Ctx} {bound body result : Term},
    WSubMStar Γ (.abs bound body) (.abs result .top) →
      AbsFunctionBoundChainShape Γ bound body result

/-- Remaining joined-bound well-formedness payload for a chosen shape-only
function-bound common-reduct payload. -/
def AbsFunctionBoundChainShapeWfPayload
    (hShape : AbsFunctionBoundChainShapePayload) : Type :=
  ∀ {Γ : Ctx} {bound body result : Term}
    (hSub : WSubMStar Γ (.abs bound body) (.abs result .top)),
      WfM Γ ((hShape hSub).joinBound)

/-- Joined-bound well-formedness for shape-only function-bound common
reducts under the stronger well-formed-equivalence context invariant. -/
def AbsFunctionBoundChainShapeWfUnderWfCtxPayload
    (hShape : AbsFunctionBoundChainShapePayload) : Type :=
  ∀ {Γ : Ctx} {bound body result : Term}
    (hSub : WSubMStar Γ (.abs bound body) (.abs result .top)),
      WfCtxEqu Γ → WfM Γ ((hShape hSub).joinBound)

/-- Closed-context specialization of joined-bound well-formedness for
shape-only function-bound common reducts. -/
def AbsFunctionBoundChainShapeWfClosedPayload
    (hShape : AbsFunctionBoundChainShapePayload) : Type :=
  ∀ {bound body result : Term}
    (hSub : WSubMStar [] (.abs bound body) (.abs result .top)),
      WfM [] ((hShape hSub).joinBound)

/-- Conditional empty-stack well-formedness preservation for one equivalence
reduction step. This is the exact local premise needed to turn a
function-bound shape into a full diagram. -/
def MEqRedPreservesWfM : Type :=
  ∀ {Γ : Ctx} {x y : Term}, MEqRedJ Γ [] x y → WfM Γ x → WfM Γ y

/-- Contextual well-formedness preservation for one equivalence reduction
step, with the stronger invariants needed away from the empty stack. -/
def MEqRedPreservesWfMContextual : Type :=
  ∀ {Γ : Ctx} {s : Stack} {x y : Term},
    WfCtxEqu Γ → WfStack Γ s → MEqRed Γ s x y → WfM Γ x → WfM Γ y

namespace Stack

/-- Plug a machine stack back into a term by applying the stack head first.
This is the well-formedness invariant missing from the broad stack-only
contextual preservation target: `MEqRed Γ s t t'` should be related to the
typing of `plug t s`, not just to the typing of `t` and each stack element
separately. -/
def plug (t : Term) : Stack → Term
  | [] => t
  | operand :: s => plug (.app t operand) s

@[simp] theorem plug_nil (t : Term) : plug t [] = t := rfl

@[simp] theorem plug_cons (t operand : Term) (s : Stack) :
    plug t (operand :: s) = plug (.app t operand) s := rfl

end Stack

/-- Machine-state well-formedness: a control term is well formed together
with its pending stack when the plugged application spine is well formed. -/
def WfMachineState (Γ : Ctx) (t : Term) (s : Stack) : Type :=
  WfM Γ (Stack.plug t s)

/-- Corrected stack-indexed preservation target: a reduction preserves
well-formedness of the whole machine state obtained by plugging the pending
stack into the control term. The earlier target
`MEqRedPreservesWfMContextual` is refuted below because it only remembered
per-element stack well-formedness. -/
def MEqRedPreservesWfMachineState : Type :=
  ∀ {Γ : Ctx} {s : Stack} {x y : Term},
    WfCtxEqu Γ → MEqRed Γ s x y →
      WfMachineState Γ x s → WfMachineState Γ y s

/-- Machine-state residual for `Me-Pro`: promotion through an equivalence
binding must preserve the whole plugged state. This is nontrivial because
the source state types `bvar i` under the pending stack, while `WfCtxEqu`
only directly types the stored annotation at an empty stack. -/
def MEqRedProPreservesWfMachineStatePayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {i : Nat} {α α' : Term},
    WfCtxEqu Γ →
      Γ.equBinds i α →
        MEqRed Γ s α α' →
          WfMachineState Γ (.bvar i) s →
            WfMachineState Γ α' s

/-- Smaller `Me-Pro` machine-state residual: only transport the source
machine state from the variable to its equivalence annotation. The recursive
premise for the annotation reduction then handles `α → α'`. -/
def MEqRedProAnnotationMachineStatePayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {i : Nat} {α : Term},
    WfCtxEqu Γ →
      Γ.equBinds i α →
        WfMachineState Γ (.bvar i) s →
          WfMachineState Γ α s

/-- Machine-state residual for `Me-Bet`. -/
def MEqRedBetaPreservesWfMachineStatePayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {bound arg arg' body body' : Term},
    WfCtxEqu Γ →
      Term.Scoped Γ.depth bound →
        MEqRed ({ bound := bound, kind := .sub } :: Γ)
          (Stack.shift 0 s) body body' →
          MEqRed Γ [] arg arg' →
            WfMachineState Γ (.app (.abs bound body) arg) s →
              WfMachineState Γ (Term.instantiate 0 arg' body') s

/-- Smaller immediate-target residual for `Me-Bet` machine states. Once the
β target term is well formed, the remaining pending stack can be handled by
the generic tail-step preservation residual used by other machine-state
constructor splits. -/
def MEqRedBetaTargetPreservesWfMPayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {bound arg arg' body body' : Term},
    WfCtxEqu Γ →
      Term.Scoped Γ.depth bound →
        MEqRed ({ bound := bound, kind := .sub } :: Γ)
          (Stack.shift 0 s) body body' →
          MEqRed Γ [] arg arg' →
            WfMachineState Γ (.app (.abs bound body) arg) s →
              WfM Γ (Term.instantiate 0 arg' body')

/-- Body-preservation residual for the `Me-Bet` target. The body reduction
runs under the source `.sub bound` head and the shifted pending machine stack.
This isolates the recursive body-preservation part of the beta target from
argument preservation and beta instantiation. -/
def MEqRedBetaBodyPreservesWfMPayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {bound body body' : Term},
    WfCtxEqu Γ →
      WfStack Γ s →
        WfM Γ bound →
          MEqRed ({ bound := bound, kind := .sub } :: Γ)
            (Stack.shift 0 s) body body' →
            WfM ({ bound := bound, kind := .sub } :: Γ) body →
              WfM ({ bound := bound, kind := .sub } :: Γ) body'

/-- Machine-state residual for changing the head operand after the
empty-stack argument reduction in `Me-App`. -/
def MEqRedMachineStackHeadReplacePayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {u v v' : Term},
    WfCtxEqu Γ →
      MEqRed Γ [] v v' →
        WfMachineState Γ u (v :: s) →
          WfMachineState Γ u (v' :: s)

/-- Machine-state control transport: replacing the control term by a
well-subtype preserves plugged-state well-formedness. This is the reusable
shape behind stack-head replacement for `Me-App` when the tail stack is
nonempty. -/
def WfMachineStateControlLeftPayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {control control' : Term},
    WSubMStar Γ control' control →
      WfMachineState Γ control s →
        WfMachineState Γ control' s

/-- Application congruence residual for transitive well-subtyping on the
operator side. This is the structural fact needed to iterate control-left
machine-state transport through a pending stack. -/
def WSubMStarAppOperatorPayload : Type :=
  ∀ {Γ : Ctx} {operator operator' operand : Term},
    WSubMStar Γ operator' operator →
      WfM Γ (.app operator operand) →
        WfM Γ (.app operator' operand) →
          WSubMStar Γ (.app operator' operand) (.app operator operand)

/-- Bridge residual from diagrammatic transitive subtyping back into
well-subtyping. Existing code can strip `WSubMStar` to `MSubStar` and lift
the diagrammatic chain structurally through applications; this payload is the
remaining well-formed re-embedding step. -/
def MSubStarToWSubMStarPayload : Type :=
  ∀ {Γ : Ctx} {source target : Term},
    MSubStar Γ [] source target →
      WfM Γ source →
        WfM Γ target →
          WSubMStar Γ source target

/-- One-step diagrammatic subtyping well-formedness preservation. This is the
chain-local well-formedness premise needed to re-embed `MSubStar` into
`WSubMStar`. -/
def MSubPreservesWfMPayload : Type :=
  ∀ {Γ : Ctx} {source target : Term},
    MSub Γ [] source target →
      WfM Γ source →
        WfM Γ target

/-- One-step diagrammatic subtyping re-embedding into transitive
well-subtyping once both endpoints are known well formed. -/
def MSubToWSubMStarPayload : Type :=
  ∀ {Γ : Ctx} {source target : Term},
    MSub Γ [] source target →
      WfM Γ source →
        WfM Γ target →
          WSubMStar Γ source target

/-- Stack-extension bridge for well-subtyping stripped to diagrammatic
subtyping. A `WSubMStar` lives at the empty stack, but structural application
lifting for diagrammatic subtyping expects the operator relation under the
operand stack head. -/
def WSubMStarToStackedMSubStarPayload : Prop :=
  ∀ {Γ : Ctx} {source target operand : Term},
    WSubMStar Γ source target →
      Term.Scoped Γ.depth operand →
        MSubStar Γ [operand] source target

/-- One-step diagrammatic stack lift: expose a diagrammatic subtype step at
the empty stack under one operand stack head. -/
def MSubStackLiftPayload : Prop :=
  ∀ {Γ : Ctx} {source target operand : Term},
    MSub Γ [] source target →
      Term.Scoped Γ.depth operand →
        MSub Γ [operand] source target

/-- General one-step diagrammatic stack extension by one operand at the outer
end of an arbitrary operand stack. -/
def MSubStackAppendPayload : Prop :=
  ∀ {Γ : Ctx} {s : Stack} {source target operand : Term},
    MSub Γ s source target →
      Term.Scoped Γ.depth operand →
        MSub Γ (s ++ [operand]) source target

/-- Stack lift for subtype-reduction chains under one operand stack head. -/
def MSubRedStarStackLiftPayload : Prop :=
  ∀ {Γ : Ctx} {source target operand : Term},
    MSubRedStar Γ [] source target →
      Term.Scoped Γ.depth operand →
        MSubRedStar Γ [operand] source target

/-- Stack lift for one subtype-reduction step under one operand stack head. -/
def MSubRedStackLiftPayload : Type :=
  ∀ {Γ : Ctx} {source target operand : Term},
    MSubRed Γ [] source target →
      Term.Scoped Γ.depth operand →
        MSubRed Γ [operand] source target

/-- General one-step subtype-reduction stack extension by one operand at the
outer end of an arbitrary operand stack. This is the induction-ready form:
operator premises in `Ms-App` live under a non-empty stack, so the empty-stack
head lift is only a specialization. -/
def MSubRedStackAppendPayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {source target operand : Term},
    MSubRed Γ s source target →
      Term.Scoped Γ.depth operand →
        MSubRed Γ (s ++ [operand]) source target

/-- Star-level subtype-reduction stack extension by one operand at the outer
end of an arbitrary operand stack. -/
def MSubRedStarStackAppendPayload : Prop :=
  ∀ {Γ : Ctx} {s : Stack} {source target operand : Term},
    MSubRedStar Γ s source target →
      Term.Scoped Γ.depth operand →
        MSubRedStar Γ (s ++ [operand]) source target

/-- The only empty-stack-only subtype-reduction constructor case left by the
general stack-append induction. -/
def MSubRedFunStackAppendPayload : Type :=
  ∀ {Γ : Ctx} {bound bound' body body' operand : Term},
    Term.Scoped Γ.depth bound →
      MEqRed Γ [] bound bound' →
        MSubRed ({ bound := bound, kind := .sub } :: Γ) [] body body' →
          Term.Scoped Γ.depth operand →
            MSubRed Γ [operand] (.abs bound body) (.abs bound' body')

/-- Convert the body subtype step of an empty-stack `Ms-Fun` into the
equivalence body step needed by the non-empty-stack `Me-FOp`/`Ms-Equ`
rebuild. This is intentionally stronger than ordinary body stack transport:
`Ms-Fun` changes the abstraction bound, while `Ms-FOp` alone preserves it. -/
def MSubRedSubHeadToEquHeadAsMEqPayload : Type :=
  ∀ {Γ : Ctx} {bound operand body body' : Term},
    MSubRed ({ bound := bound, kind := .sub } :: Γ) [] body body' →
      Term.Scoped Γ.depth operand →
        MEqRed ({ bound := operand, kind := .equ } :: Γ) [] body body'


/-- Stack lift for equivalence-reduction chains under one operand stack head. -/
def MEqRedStarStackLiftPayload : Prop :=
  ∀ {Γ : Ctx} {source target operand : Term},
    MEqRedStar Γ [] source target →
      Term.Scoped Γ.depth operand →
        MEqRedStar Γ [operand] source target

/-- Stack lift for one equivalence-reduction step under one operand stack
head. -/
def MEqRedStackLiftPayload : Type :=
  ∀ {Γ : Ctx} {source target operand : Term},
    MEqRed Γ [] source target →
      Term.Scoped Γ.depth operand →
        MEqRed Γ [operand] source target

/-- General one-step equivalence-reduction stack extension by one operand at
the outer end of an arbitrary operand stack. The `Me-App` constructor needs
exactly this stronger induction principle for its operator premise. -/
def MEqRedStackAppendPayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {source target operand : Term},
    MEqRed Γ s source target →
      Term.Scoped Γ.depth operand →
        MEqRed Γ (s ++ [operand]) source target

/-- Star-level equivalence-reduction stack extension by one operand at the
outer end of an arbitrary operand stack. -/
def MEqRedStarStackAppendPayload : Prop :=
  ∀ {Γ : Ctx} {s : Stack} {source target operand : Term},
    MEqRedStar Γ s source target →
      Term.Scoped Γ.depth operand →
        MEqRedStar Γ (s ++ [operand]) source target

/-- The only empty-stack-only equivalence-reduction constructor case left by
the general stack-append induction. -/
def MEqRedFunStackAppendPayload : Type :=
  ∀ {Γ : Ctx} {bound bound' body body' operand : Term},
    MEqRed Γ [] bound bound' →
      MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body' →
        Term.Scoped Γ.depth operand →
          MEqRed Γ [operand] (.abs bound body) (.abs bound' body')

/-- Transport an empty-stack equivalence body reduction from the source
function `.sub` head to the stack-introduced operand `.equ` head. This is the
body premise needed to rebuild a non-empty-stack `Me-Fun` as `Me-FOp`. -/
def MEqRedSubHeadToEquHeadPayload : Type :=
  ∀ {Γ : Ctx} {bound operand body body' : Term},
    MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body' →
      Term.Scoped Γ.depth operand →
        MEqRed ({ bound := operand, kind := .equ } :: Γ) [] body body'

/-- Transitive diagrammatic stack lift under one operand stack head. -/
def MSubStarStackLiftPayload : Prop :=
  ∀ {Γ : Ctx} {source target operand : Term},
    MSubStar Γ [] source target →
      Term.Scoped Γ.depth operand →
        MSubStar Γ [operand] source target

/-- Transitive diagrammatic stack extension by one operand at the outer end of
an arbitrary operand stack. -/
def MSubStarStackAppendPayload : Prop :=
  ∀ {Γ : Ctx} {s : Stack} {source target operand : Term},
    MSubStar Γ s source target →
      Term.Scoped Γ.depth operand →
        MSubStar Γ (s ++ [operand]) source target

/-- Machine-state residual for `Me-Fun`, which only fires at the empty
stack. -/
def MEqRedFunPreservesWfMachineStatePayload : Type :=
  ∀ {Γ : Ctx} {bound bound' body body' : Term},
    WfCtxEqu Γ →
      MEqRed Γ [] bound bound' →
        MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body' →
          WfMachineState Γ (.abs bound body) [] →
            WfMachineState Γ (.abs bound' body') []

/-- Machine-state residual for `Me-TAp`. -/
def MEqRedTApPreservesWfMachineStatePayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {u : Term},
    WfCtxEqu Γ →
      Term.Scoped Γ.depth u →
        WfMachineState Γ (.app .top u) s →
          WfMachineState Γ .top s

/-- Machine-state residual for `Me-FOp`; this is where the plugged-state
typing supplies the operand-to-bound relationship exposed by
`WfMachineState.fop_operand_bound`. -/
def MEqRedFOpPreservesWfMachineStatePayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {bound bound' operand body body' : Term},
    WfCtxEqu Γ →
      MEqRed Γ [] bound bound' →
        Term.Scoped Γ.depth operand →
          MEqRed ({ bound := operand, kind := .equ } :: Γ)
            (Stack.shift 0 s) body body' →
            WfMachineState Γ (.abs bound body) (operand :: s) →
              WfMachineState Γ (.abs bound' body') (operand :: s)

namespace WfMachineState

/-- Tail view of a non-empty plugged machine state. -/
def tail_state {Γ : Ctx} {t operand : Term} {s : Stack} :
    WfMachineState Γ t (operand :: s) →
      WfMachineState Γ (.app t operand) s := by
  intro hState
  simpa [WfMachineState, Stack.plug] using hState

/-- A well-formed non-empty machine state exposes the first application in
the plugged stack. -/
noncomputable def head_app_wf {Γ : Ctx} {t operand : Term} {s : Stack} :
    WfMachineState Γ t (operand :: s) → WfM Γ (.app t operand) := by
  induction s generalizing t operand with
  | nil =>
      intro hState
      simpa [WfMachineState, Stack.plug] using hState
  | cons next rest ih =>
      intro hState
      have hNext : WfM Γ (.app (.app t operand) next) :=
        ih (t := .app t operand) (operand := next) (by
          simpa [WfMachineState, Stack.plug] using hState)
      obtain ⟨_, hFun, _⟩ := hNext.app_inv
      exact hFun.wf_left

/-- A plugged well-formed machine state always contains a well-formed
control term. -/
noncomputable def control_wf {Γ : Ctx} {t : Term} {s : Stack} :
    WfMachineState Γ t s → WfM Γ t := by
  cases s with
  | nil =>
      intro hState
      simpa [WfMachineState, Stack.plug] using hState
  | cons operand tail =>
      intro hState
      have hApp : WfM Γ (.app t operand) := head_app_wf hState
      obtain ⟨_, hFun, _⟩ := hApp.app_inv
      exact hFun.wf_left

/-- A plugged well-formed machine state supplies the older per-element
`WfStack` invariant as a projection. -/
noncomputable def stack_wf {Γ : Ctx} {t : Term} {s : Stack} :
    WfMachineState Γ t s → WfStack Γ s := by
  induction s generalizing t with
  | nil =>
      intro _hState
      exact WfStack.nil
  | cons operand tail ih =>
      intro hState
      have hApp : WfM Γ (.app t operand) := head_app_wf hState
      obtain ⟨_, _hFun, hArg⟩ := hApp.app_inv
      exact WfStack.cons hArg.wf_left (ih (tail_state hState))

/-- From a well-formed machine state headed by an abstraction, recover the
typed `Me-FOp` premise that the popped operand is a well-subtype of the
abstraction bound. The function-bound inversion payload bridges the result
bound chosen by `Wf-App` back to the abstraction's actual bound. -/
noncomputable def fop_operand_bound
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    {Γ : Ctx} {s : Stack} {bound body operand : Term}
    (hΓ : WfCtxEqu Γ)
    (hState : WfMachineState Γ (.abs bound body) (operand :: s)) :
    WSubMStar Γ operand bound := by
  have hApp : WfM Γ (.app (.abs bound body) operand) :=
    head_app_wf hState
  obtain ⟨result, hFun, hArg⟩ := hApp.app_inv
  have hEquBoundResult : WEquMStar Γ bound result := hInv hΓ hFun
  have hSubResultBound : WSubMStar Γ result bound :=
    hEquBoundResult.symm.toWSubMStar
  exact WSubMStar.trans hArg.wf_right hArg hSubResultBound

end WfMachineState

/-- Assemble corrected machine-state preservation from the constructor-level
machine-state residuals. The `Me-App` case is partly structural: the
operator IH preserves the plugged state under the original operand head, and
`hStackHead` accounts for the empty-stack operand reduction changing that
head. -/
noncomputable def MEqRedPreservesWfMachineState.of_components
    (hPro : MEqRedProPreservesWfMachineStatePayload)
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hStackHead : MEqRedMachineStackHeadReplacePayload)
    (hFun : MEqRedFunPreservesWfMachineStatePayload)
    (hTAp : MEqRedTApPreservesWfMachineStatePayload)
    (hFOp : MEqRedFOpPreservesWfMachineStatePayload) :
    MEqRedPreservesWfMachineState := by
  intro Γ s x y hΓ hred hState
  revert hΓ hState
  induction hred with
  | pro hpv hb hred ih =>
      intro hΓ hState
      exact hPro hΓ hb hred hState
  | bet ht hBody hArg _ihBody _ihArg =>
      intro hΓ hState
      exact hBeta hΓ ht hBody hArg hState
  | top hpv =>
      intro hΓ hState
      exact hState
  | @app Γapp sapp u u' v v' hOp hArg ihOp _ihArg =>
      intro hΓ hState
      have hOpState : WfMachineState Γapp u (v :: sapp) := by
        simpa [WfMachineState, Stack.plug] using hState
      have hOpState' := ihOp hΓ hOpState
      exact hStackHead hΓ hArg hOpState'
  | var hpv hi =>
      intro hΓ hState
      exact hState
  | fun_ hBound hBody _ihBound _ihBody =>
      intro hΓ hState
      exact hFun hΓ hBound hBody hState
  | tAp hpv hu =>
      intro hΓ hState
      exact hTAp hΓ hu hState
  | fOp hBound hOperand hBody _ihBound _ihBody =>
      intro hΓ hState
      exact hFOp hΓ hBound hOperand hBody hState

/-- Assemble corrected machine-state preservation using the smaller `Me-Pro`
annotation transport residual. The recursive premise from the `Me-Pro`
constructor then preserves the annotation reduction itself. -/
noncomputable def MEqRedPreservesWfMachineState.of_components_pro_annotation
    (hPro : MEqRedProAnnotationMachineStatePayload)
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hStackHead : MEqRedMachineStackHeadReplacePayload)
    (hFun : MEqRedFunPreservesWfMachineStatePayload)
    (hTAp : MEqRedTApPreservesWfMachineStatePayload)
    (hFOp : MEqRedFOpPreservesWfMachineStatePayload) :
    MEqRedPreservesWfMachineState := by
  intro Γ s x y hΓ hred hState
  revert hΓ hState
  induction hred with
  | pro hpv hb hred ih =>
      intro hΓ hState
      exact ih hΓ (hPro hΓ hb hState)
  | bet ht hBody hArg _ihBody _ihArg =>
      intro hΓ hState
      exact hBeta hΓ ht hBody hArg hState
  | top hpv =>
      intro hΓ hState
      exact hState
  | @app Γapp sapp u u' v v' hOp hArg ihOp _ihArg =>
      intro hΓ hState
      have hOpState : WfMachineState Γapp u (v :: sapp) := by
        simpa [WfMachineState, Stack.plug] using hState
      have hOpState' := ihOp hΓ hOpState
      exact hStackHead hΓ hArg hOpState'
  | var hpv hi =>
      intro hΓ hState
      exact hState
  | fun_ hBound hBody _ihBound _ihBody =>
      intro hΓ hState
      exact hFun hΓ hBound hBody hState
  | tAp hpv hu =>
      intro hΓ hState
      exact hTAp hΓ hu hState
  | fOp hBound hOperand hBody _ihBound _ihBody =>
      intro hΓ hState
      exact hFOp hΓ hBound hOperand hBody hState

/-- Operator-side application congruence for `WSubMStar` discharges
control-left machine-state transport by induction over the pending stack. -/
noncomputable def WfMachineStateControlLeftPayload.of_app_operator
    (hApp : WSubMStarAppOperatorPayload) :
    WfMachineStateControlLeftPayload := by
  intro Γ s control control' hSub hState
  induction s generalizing control control' with
  | nil =>
      simpa [WfMachineState, Stack.plug] using hSub.wf_left
  | cons operand tail ih =>
      have hAppControl : WfM Γ (.app control operand) :=
        WfMachineState.head_app_wf hState
      obtain ⟨bound, hFun, hArg⟩ := hAppControl.app_inv
      have hFun' : WSubMStar Γ control' (.abs bound .top) :=
        WSubMStar.trans hSub.wf_right hSub hFun
      have hAppControl' : WfM Γ (.app control' operand) :=
        WfM.app hFun' hArg
      have hSubApp : WSubMStar Γ (.app control' operand)
          (.app control operand) :=
        hApp hSub hAppControl hAppControl'
      have hTail' : WfMachineState Γ (.app control' operand) tail :=
        ih hSubApp (WfMachineState.tail_state hState)
      simpa [WfMachineState, Stack.plug] using hTail'

/-- Diagrammatic re-embedding discharges operator-side application congruence
for `WSubMStar`: first expose the operator relation as a diagrammatic chain
under the operand stack head, use the existing fixed-argument application
lift, then re-embed the lifted diagrammatic chain. -/
noncomputable def WSubMStarAppOperatorPayload.of_stacked_msubstar_bridge
    (hStack : WSubMStarToStackedMSubStarPayload)
    (hBridge : MSubStarToWSubMStarPayload) :
    WSubMStarAppOperatorPayload := by
  intro Γ operator operator' operand hOp hApp hApp'
  obtain ⟨_, _hFun, hArg⟩ := hApp.app_inv
  have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil hApp.prevalid
  have hOpStack : MSubStar Γ [operand] operator' operator :=
    hStack hOp hArg.wf_left.scoped
  have hMSubApp : MSubStar Γ [] (.app operator' operand)
      (.app operator operand) :=
    msubStar_app_fixed_arg hpvNil hArg.wf_left.scoped hOpStack
  exact hBridge hMSubApp hApp' hApp

/-- Re-embed a diagrammatic subtype chain into well-subtyping from one-step
well-formedness preservation plus one-step well-subtyping re-embedding. -/
noncomputable def MSubStarToWSubMStarPayload.of_steps
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload) :
    MSubStarToWSubMStarPayload := by
  intro Γ source target hChain hwfSource hwfTarget
  suffices key : ∀ {source : Term} (h : MSubStar Γ [] source target),
      Nonempty (WfM Γ source → WfM Γ target →
        WSubMStar Γ source target) from
    (key hChain).some hwfSource hwfTarget
  intro source h
  refine Relation.ReflTransGen.head_induction_on (b := target)
    (P := fun source (_ : MSubStar Γ [] source target) =>
      Nonempty (WfM Γ source → WfM Γ target →
        WSubMStar Γ source target)) h ?_ ?_
  · exact ⟨fun hwfSource _hwfTarget => WSubMStar.refl_of_wfM hwfSource⟩
  · intro source mid hHead hTail ih
    exact ⟨fun hwfSource hwfTarget =>
      let hwfMid : WfM Γ mid := hPres hHead hwfSource
      let hLeft : WSubMStar Γ source mid := hStep hHead hwfSource hwfMid
      let hRight : WSubMStar Γ mid target := (ih.some hwfMid hwfTarget)
      WSubMStar.trans hwfMid hLeft hRight⟩

/-- Reduction-chain stack lifts discharge one-step diagrammatic stack lift by
lifting both sides of the common-reduct diagram under the operand head. -/
def MSubStackLiftPayload.of_reduction_lifts
    (hSubLift : MSubRedStarStackLiftPayload)
    (hEqLift : MEqRedStarStackLiftPayload) :
    MSubStackLiftPayload := by
  intro Γ source target operand hSub hOperand
  obtain ⟨join, hSubChain, hEqChain⟩ := hSub
  exact ⟨join, hSubLift hSubChain hOperand, hEqLift hEqChain hOperand⟩

/-- Reduction-chain stack appends discharge one-step diagrammatic stack append
by lifting both sides of the common-reduct diagram under the appended
operand. -/
def MSubStackAppendPayload.of_reduction_appends
    (hSubAppend : MSubRedStarStackAppendPayload)
    (hEqAppend : MEqRedStarStackAppendPayload) :
    MSubStackAppendPayload := by
  intro Γ s source target operand hSub hOperand
  obtain ⟨join, hSubChain, hEqChain⟩ := hSub
  exact ⟨join, hSubAppend hSubChain hOperand, hEqAppend hEqChain hOperand⟩

/-- The generalized diagrammatic stack append payload specializes to the
empty-stack head lift. -/
def MSubStackLiftPayload.of_append
    (hAppend : MSubStackAppendPayload) :
    MSubStackLiftPayload := by
  intro Γ source target operand hStep hOperand
  simpa using (hAppend (Γ := Γ) (s := ([] : Stack)) hStep hOperand)

/-- The generalized subtype-reduction stack append payload specializes to the
empty-stack head lift used by the current assembly. -/
def MSubRedStackLiftPayload.of_append
    (hAppend : MSubRedStackAppendPayload) :
    MSubRedStackLiftPayload := by
  intro Γ source target operand hStep hOperand
  simpa using (hAppend (s := ([] : Stack)) hStep hOperand)

/-- The generalized equivalence-reduction stack append payload specializes to
the empty-stack head lift used by the current assembly. -/
def MEqRedStackLiftPayload.of_append
    (hAppend : MEqRedStackAppendPayload) :
    MEqRedStackLiftPayload := by
  intro Γ source target operand hStep hOperand
  simpa using (hAppend (s := ([] : Stack)) hStep hOperand)

/-- Body transport from the source `.sub` head to the operand `.equ` head
discharges the empty-stack-only `Me-Fun` stack append residual. -/
def MEqRedFunStackAppendPayload.of_body_transport
    (hBody : MEqRedSubHeadToEquHeadPayload) :
    MEqRedFunStackAppendPayload := by
  intro Γ bound bound' body body' operand hBound hBodyRed hOperand
  exact MEqRed.fOp hBound hOperand (hBody hBodyRed hOperand)

/-- A body subtype-to-equivalence conversion under the operand `.equ` head
discharges the empty-stack-only `Ms-Fun` stack append residual: rebuild the
non-empty-stack abstraction step as `Ms-Equ` over `Me-FOp`. -/
noncomputable def MSubRedFunStackAppendPayload.of_body_equ_transport
    (hBody : MSubRedSubHeadToEquHeadAsMEqPayload) :
    MSubRedFunStackAppendPayload := by
  intro Γ bound bound' body body' operand _hBoundScoped hBound hBodyRed hOperand
  have hpv : PrevalidExt Γ [operand] :=
    PrevalidExt.cons (PrevalidExt.nil hBound.prevalid) hOperand
  exact MSubRed.equ hpv (MEqRed.fOp hBound hOperand (hBody hBodyRed hOperand))

namespace Stack

/-- Shifting commutes with appending one operand to the outer end of a stack. -/
theorem shift_append_single (cutoff : Nat) (s : Stack) (operand : Term) :
    Stack.shift cutoff (s ++ [operand]) =
      Stack.shift cutoff s ++ [Term.shift cutoff operand] := by
  induction s with
  | nil =>
      rfl
  | cons head tail ih =>
      simp [Stack.shift, Stack.shiftBy, Term.shift, ih]

end Stack

namespace PrevalidExt

/-- Append a scoped operand to the outer end of a prevalid operand stack. -/
noncomputable def append_operand {Γ : Ctx} {s : Stack} {operand : Term} :
    PrevalidExt Γ s →
      Term.Scoped Γ.depth operand →
        PrevalidExt Γ (s ++ [operand]) := by
  intro hpv hOperand
  induction hpv with
  | nil hΓ =>
      exact PrevalidExt.cons (PrevalidExt.nil hΓ) hOperand
  | cons hpvHead hHead ih =>
      exact PrevalidExt.cons ih hHead

end PrevalidExt

/-- The generalized equivalence-reduction stack append lift follows by
structural induction once the empty-stack-only `Me-Fun` case is supplied. -/
noncomputable def MEqRedStackAppendPayload.of_fun
    (hFun : MEqRedFunStackAppendPayload) :
    MEqRedStackAppendPayload := by
  intro Γ s source target operand hStep hOperand
  induction hStep generalizing operand with
  | pro hpv hb hred ih =>
      exact MEqRed.pro (PrevalidExt.append_operand hpv hOperand) hb
        (ih hOperand)
  | @bet Γp sp t v v' body body' ht hBody hArg ihBody _ihArg =>
      have hOperand' : Term.Scoped
          (Ctx.depth ({ bound := t, kind := .sub } :: Γp))
          (Term.shift 0 operand) := by
        simpa [Ctx.depth] using
          (Term.shift_scoped 0 Γp.depth operand (Nat.zero_le _) hOperand)
      exact MEqRed.bet ht
        (by
          simpa [Stack.shift_append_single] using ihBody hOperand')
        hArg
  | top hpv =>
      exact MEqRed.top (PrevalidExt.append_operand hpv hOperand)
  | app hOp hArg ihOp _ihArg =>
      exact MEqRed.app (ihOp hOperand) hArg
  | var hpv hi =>
      exact MEqRed.var (PrevalidExt.append_operand hpv hOperand) hi
  | fun_ hBound hBody _ihBound _ihBody =>
      exact hFun hBound hBody hOperand
  | tAp hpv hu =>
      exact MEqRed.tAp (PrevalidExt.append_operand hpv hOperand) hu
  | @fOp Γp sp t t' α body body' hBound hOperandHead hBody _ihBound ihBody =>
      have hOperand' : Term.Scoped
          (Ctx.depth ({ bound := α, kind := .equ } :: Γp))
          (Term.shift 0 operand) := by
        simpa [Ctx.depth] using
          (Term.shift_scoped 0 Γp.depth operand (Nat.zero_le _) hOperand)
      exact MEqRed.fOp hBound hOperandHead
        (by
          simpa [Stack.shift_append_single] using ihBody hOperand')

/-- The generalized subtype-reduction stack append lift follows by
structural induction once `Ms-Equ` can reuse equivalence stack append and the
empty-stack-only `Ms-Fun` case is supplied. -/
noncomputable def MSubRedStackAppendPayload.of_fun
    (hEqAppend : MEqRedStackAppendPayload)
    (hFun : MSubRedFunStackAppendPayload) :
    MSubRedStackAppendPayload := by
  intro Γ s source target operand hStep hOperand
  induction hStep generalizing operand with
  | pro hpv hb =>
      exact MSubRed.pro (PrevalidExt.append_operand hpv hOperand) hb
  | top hpv hu =>
      exact MSubRed.top (PrevalidExt.append_operand hpv hOperand) hu
  | equ hpv hEq =>
      exact MSubRed.equ (PrevalidExt.append_operand hpv hOperand)
        (hEqAppend hEq hOperand)
  | app hOp hv ihOp =>
      exact MSubRed.app (ihOp hOperand) hv
  | fun_ ht hBound hBody _ihBody =>
      exact hFun ht hBound hBody hOperand
  | @fOp Γp sp t α body body' ht hOperandHead hBody ihBody =>
      have hOperand' : Term.Scoped
          (Ctx.depth ({ bound := α, kind := .equ } :: Γp))
          (Term.shift 0 operand) := by
        simpa [Ctx.depth] using
          (Term.shift_scoped 0 Γp.depth operand (Nat.zero_le _) hOperand)
      exact MSubRed.fOp ht hOperandHead
        (by
          simpa [Stack.shift_append_single] using ihBody hOperand')

/-- One-step subtype-reduction stack append iterates to subtype-reduction
chains. -/
def MSubRedStarStackAppendPayload.of_step
    (hStep : MSubRedStackAppendPayload) :
    MSubRedStarStackAppendPayload := by
  intro Γ s source target operand hStar hOperand
  induction hStar with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hPrefix hHead ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single ⟨hStep hHead.some hOperand⟩)

/-- One-step equivalence-reduction stack append iterates to equivalence-
reduction chains. -/
def MEqRedStarStackAppendPayload.of_step
    (hStep : MEqRedStackAppendPayload) :
    MEqRedStarStackAppendPayload := by
  intro Γ s source target operand hStar hOperand
  induction hStar with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hPrefix hHead ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single ⟨hStep hHead.some hOperand⟩)

/-- The generalized subtype-reduction star append payload specializes to the
empty-stack head lift used by the current assembly. -/
def MSubRedStarStackLiftPayload.of_append
    (hAppend : MSubRedStarStackAppendPayload) :
    MSubRedStarStackLiftPayload := by
  intro Γ source target operand hStar hOperand
  simpa using (hAppend (Γ := Γ) (s := ([] : Stack)) hStar hOperand)

/-- The generalized equivalence-reduction star append payload specializes to
the empty-stack head lift used by the current assembly. -/
def MEqRedStarStackLiftPayload.of_append
    (hAppend : MEqRedStarStackAppendPayload) :
    MEqRedStarStackLiftPayload := by
  intro Γ source target operand hStar hOperand
  simpa using (hAppend (Γ := Γ) (s := ([] : Stack)) hStar hOperand)

/-- One-step subtype-reduction stack lift iterates to subtype-reduction
chains. -/
def MSubRedStarStackLiftPayload.of_step
    (hStep : MSubRedStackLiftPayload) :
    MSubRedStarStackLiftPayload := by
  intro Γ source target operand hStar hOperand
  induction hStar with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hPrefix hHead ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single ⟨hStep hHead.some hOperand⟩)

/-- One-step equivalence-reduction stack lift iterates to equivalence-
reduction chains. -/
def MEqRedStarStackLiftPayload.of_step
    (hStep : MEqRedStackLiftPayload) :
    MEqRedStarStackLiftPayload := by
  intro Γ source target operand hStar hOperand
  induction hStar with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hPrefix hHead ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single ⟨hStep hHead.some hOperand⟩)

/-- A one-step diagrammatic stack lift iterates to a transitive diagrammatic
stack lift. -/
def MSubStarStackLiftPayload.of_step
    (hStep : MSubStackLiftPayload) :
    MSubStarStackLiftPayload := by
  intro Γ source target operand hStar hOperand
  induction hStar with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hPrefix hHead ih =>
      exact Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single
        (hStep hHead hOperand))

/-- One-step diagrammatic stack append iterates to transitive diagrammatic
chains. -/
def MSubStarStackAppendPayload.of_step
    (hStep : MSubStackAppendPayload) :
    MSubStarStackAppendPayload := by
  intro Γ s source target operand hStar hOperand
  induction hStar with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hPrefix hHead ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single (hStep hHead hOperand))

/-- The generalized transitive diagrammatic stack append payload specializes
to the empty-stack head lift. -/
def MSubStarStackLiftPayload.of_append
    (hAppend : MSubStarStackAppendPayload) :
    MSubStarStackLiftPayload := by
  intro Γ source target operand hStar hOperand
  simpa using (hAppend (Γ := Γ) (s := ([] : Stack)) hStar hOperand)

/-- A transitive diagrammatic stack lift discharges the well-subtyping to
stacked diagrammatic bridge by first stripping `WSubMStar` to `MSubStar`. -/
def WSubMStarToStackedMSubStarPayload.of_msubstar_stack_lift
    (hLift : MSubStarStackLiftPayload) :
    WSubMStarToStackedMSubStarPayload := by
  intro Γ source target operand hSub hOperand
  exact hLift hSub.toMSubStar hOperand

/-- A transitive diagrammatic stack append payload discharges the
well-subtyping to stacked-diagrammatic bridge by specializing to the appended
singleton stack. -/
def WSubMStarToStackedMSubStarPayload.of_msubstar_stack_append
    (hAppend : MSubStarStackAppendPayload) :
    WSubMStarToStackedMSubStarPayload :=
  WSubMStarToStackedMSubStarPayload.of_msubstar_stack_lift
    (MSubStarStackLiftPayload.of_append hAppend)

/-- Body-transport residuals assemble the generalized equivalence-reduction
star append payload. -/
noncomputable def MEqRedStarStackAppendPayload.of_body_transport
    (hEqBody : MEqRedSubHeadToEquHeadPayload) :
    MEqRedStarStackAppendPayload :=
  MEqRedStarStackAppendPayload.of_step
    (MEqRedStackAppendPayload.of_fun
      (MEqRedFunStackAppendPayload.of_body_transport hEqBody))

/-- Body-transport residuals assemble the generalized subtype-reduction star
append payload. -/
noncomputable def MSubRedStarStackAppendPayload.of_body_transports
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload) :
    MSubRedStarStackAppendPayload :=
  MSubRedStarStackAppendPayload.of_step
    (MSubRedStackAppendPayload.of_fun
      (MEqRedStackAppendPayload.of_fun
        (MEqRedFunStackAppendPayload.of_body_transport hEqBody))
      (MSubRedFunStackAppendPayload.of_body_equ_transport hSubBody))

/-- Body-transport residuals assemble the generalized diagrammatic stack
append payload. -/
noncomputable def MSubStackAppendPayload.of_body_transports
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload) :
    MSubStackAppendPayload :=
  MSubStackAppendPayload.of_reduction_appends
    (MSubRedStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MEqRedStarStackAppendPayload.of_body_transport hEqBody)

/-- Body-transport residuals for the two empty-stack function constructors
discharge one-step diagrammatic stack lifting. This wires the full stack-lift
decomposition into the smaller residuals exposed above. -/
noncomputable def MSubStackLiftPayload.of_body_transports
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload) :
    MSubStackLiftPayload :=
  MSubStackLiftPayload.of_append
    (MSubStackAppendPayload.of_body_transports hEqBody hSubBody)

/-- Body-transport residuals assemble the generalized transitive diagrammatic
stack append payload. -/
noncomputable def MSubStarStackAppendPayload.of_body_transports
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload) :
    MSubStarStackAppendPayload :=
  MSubStarStackAppendPayload.of_step
    (MSubStackAppendPayload.of_body_transports hEqBody hSubBody)

/-- The well-subtyping-to-stacked-diagrammatic bridge can now be assembled
directly from the two body-transport residuals for stack-lifted reductions. -/
noncomputable def WSubMStarToStackedMSubStarPayload.of_body_transports
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload) :
    WSubMStarToStackedMSubStarPayload :=
  WSubMStarToStackedMSubStarPayload.of_msubstar_stack_append
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)

/-- Append-native variant of `of_stacked_msubstar_bridge`: callers can expose
the generalized stack-append payload directly and let this wrapper perform
the singleton-stack specialization. -/
noncomputable def WSubMStarAppOperatorPayload.of_stacked_msubstar_append_bridge
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload) :
    WSubMStarAppOperatorPayload :=
  WSubMStarAppOperatorPayload.of_stacked_msubstar_bridge
    (WSubMStarToStackedMSubStarPayload.of_msubstar_stack_append hAppend)
    hBridge

/-- Application-operator congruence assembled from the reduced stack-lift
body transports and one-step diagrammatic re-embedding components. -/
noncomputable def WSubMStarAppOperatorPayload.of_body_transports_and_steps
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload) :
    WSubMStarAppOperatorPayload :=
  WSubMStarAppOperatorPayload.of_stacked_msubstar_append_bridge
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)

/-- Append-native control-left transport: expose the generalized
diagrammatic stack-append payload directly, then use the standard
operator-side application congruence wrapper. -/
noncomputable def WfMachineStateControlLeftPayload.of_msubstar_stack_append
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload) :
    WfMachineStateControlLeftPayload :=
  WfMachineStateControlLeftPayload.of_app_operator
    (WSubMStarAppOperatorPayload.of_stacked_msubstar_append_bridge
      hAppend hBridge)

/-- Control-left machine-state transport assembled from the same reduced
stack-lift body transports plus one-step diagrammatic re-embedding
components. -/
noncomputable def WfMachineStateControlLeftPayload.of_body_transports_and_steps
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload) :
    WfMachineStateControlLeftPayload :=
  WfMachineStateControlLeftPayload.of_msubstar_stack_append
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)

/-- Remaining operator-side payload for the contextual `Me-App`
well-formedness case. The operator reduction happens under stack `v :: s`,
so it is not directly covered by the empty-stack `WSubMStar` endpoint
extension helpers. -/
def MEqRedAppFunctionSupertypePayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {u u' v bound : Term},
    WfCtxEqu Γ →
      WfStack Γ s →
        WfM Γ v →
          WSubMStar Γ u (.abs bound .top) →
            MEqRed Γ (v :: s) u u' →
              WSubMStar Γ u' (.abs bound .top)

/-- Typed operator-side payload for the `Me-App` well-formedness case. The
source application typing supplies both the operator function supertype and
the operand-to-bound relationship; the latter is exactly the information
missing from `MEqRedAppFunctionSupertypePayload`. -/
def MEqRedAppFunctionSupertypeTypedPayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {u u' v bound : Term},
    WfCtxEqu Γ →
      WfStack Γ s →
        WSubMStar Γ v bound →
          WSubMStar Γ u (.abs bound .top) →
            MEqRed Γ (v :: s) u u' →
              WSubMStar Γ u' (.abs bound .top)

/-- Machine-state-aware operator-side payload for the `Me-App`/tail-step
case. Compared with `MEqRedAppFunctionSupertypeTypedPayload`, this retains
the full plugged source machine-state evidence that is available in the
machine-preservation path. -/
def MEqRedAppFunctionSupertypeMachinePayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {u u' v bound : Term},
    WfCtxEqu Γ →
      WfMachineState Γ u (v :: s) →
        WSubMStar Γ v bound →
          WSubMStar Γ u (.abs bound .top) →
            MEqRed Γ (v :: s) u u' →
              WSubMStar Γ u' (.abs bound .top)

/-- The typed operator payload implies the machine-state-aware version by
forgetting the additional plugged-state evidence down to `WfStack`. -/
noncomputable def MEqRedAppFunctionSupertypeMachinePayload.of_typed
    (hTyped : MEqRedAppFunctionSupertypeTypedPayload) :
    MEqRedAppFunctionSupertypeMachinePayload := by
  intro Γ s u u' v bound hΓ hState hArg hFun hred
  have hStack : WfStack Γ (v :: s) := WfMachineState.stack_wf hState
  exact hTyped hΓ (WfStack.tail hStack) hArg hFun hred

/-- Immediate target-application well-formedness for a stack-indexed operator
step. This is the smaller fact needed by recursive machine-state tail
transport; it avoids requiring callers to expose a particular function
supertype for the target operator. -/
def MEqRedAppTargetPreservesWfMPayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {u u' v : Term},
    WfCtxEqu Γ →
      WfMachineState Γ u (v :: s) →
        MEqRed Γ (v :: s) u u' →
          WfM Γ (.app u' v)

/-- A machine-state-aware operator function-supertype payload supplies the
smaller immediate target-application well-formedness payload. -/
noncomputable def MEqRedAppTargetPreservesWfMPayload.of_machine_operator
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload) :
    MEqRedAppTargetPreservesWfMPayload := by
  intro Γ s u u' v hΓ hState hred
  have hImmediateSource : WfM Γ (.app u v) :=
    WfMachineState.head_app_wf hState
  obtain ⟨bound, hFun, hArg⟩ := hImmediateSource.app_inv
  exact WfM.app (hOpFun hΓ hState hArg hFun hred) hArg

/-- The typed operator-function residual also supplies immediate
target-application preservation by forgetting the plugged machine-state
evidence down to the tail-stack well-formedness used by the typed payload. -/
noncomputable def MEqRedAppTargetPreservesWfMPayload.of_typed_operator
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload) :
    MEqRedAppTargetPreservesWfMPayload :=
  MEqRedAppTargetPreservesWfMPayload.of_machine_operator
    (MEqRedAppFunctionSupertypeMachinePayload.of_typed hOpFun)

/-- Generic left-endpoint transport for well-subtyping along a stack-indexed
equivalence reduction. This is the precise reusable shape behind the
operator side of contextual `Me-App`. -/
def MEqRedStackPreservesWSubMStarLeft : Type :=
  ∀ {Γ : Ctx} {s : Stack} {source source' target : Term},
    WfCtxEqu Γ →
      WfStack Γ s →
        WSubMStar Γ source target →
          MEqRed Γ s source source' →
            WSubMStar Γ source' target

/-- Stack-indexed left-endpoint transport discharges the application-operator
function-supertype payload. -/
def MEqRedAppFunctionSupertypePayload.of_left_transport
    (hLeft : MEqRedStackPreservesWSubMStarLeft) :
    MEqRedAppFunctionSupertypePayload := by
  intro Γ s u u' v bound hΓ hStack hwfV hFun hred
  exact hLeft hΓ (WfStack.cons hwfV hStack) hFun hred

/-- The native `Me-App` operator payload is too broad with only `WfStack`.
The operator can be a well-formed abstraction whose body uses its bound
variable as a function; `Me-FOp` with stack operand `Top` then reduces the
body to `Top Top`, so the target abstraction cannot remain a well-subtype of
a function type. -/
noncomputable def MEqRedAppFunctionSupertypePayload.not_of_no_top
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedAppFunctionSupertypePayload → False := by
  intro hOpFun
  let bound : Term := .abs .top .top
  let body : Term := .app (.bvar 0) .top
  let body' : Term := .app .top .top
  have hpvEmpty : Prevalid [] := Prevalid.empty
  have hwfTopEmpty : WfM [] .top := WfM.top hpvEmpty
  have hwfBound : WfM [] bound := by
    dsimp [bound]
    exact WfM.fun_ (WfM.top Prevalid.empty)
      (WfM.top (Prevalid.sub Prevalid.empty Term.Scoped.top))
  let ΓSub : Ctx := [{ bound := bound, kind := .sub }]
  have hpvSub : Prevalid ΓSub :=
    Prevalid.sub hpvEmpty hwfBound.scoped
  have hwfVarSub : WfM ΓSub (.bvar 0) := by
    exact @WfM.varSub ΓSub 0 bound hpvSub
      (by simp [ΓSub, Ctx.subBinds, bound])
  have hwfBoundSub : WfM ΓSub bound := by
    simpa [ΓSub, bound, Term.shift] using
      hwfBound.weaken_head hpvSub hpvEmpty
  have hProSub : MSubRed ΓSub [] (.bvar 0) bound := by
    simpa [ΓSub, bound, Term.shift] using
      (MSubRed.pro (PrevalidExt.nil hpvSub)
        (by simp [ΓSub, Ctx.subBinds, bound]))
  have hFunVarSub : WSubMStar ΓSub (.bvar 0) bound :=
    WSubMStar.sub hwfVarSub
      (WSubM.lf2 hwfVarSub hProSub hwfBoundSub (WSubM.rfl hwfBoundSub))
      hwfBoundSub
  have hArgSub : WSubMStar ΓSub .top .top :=
    WSubMStar.refl_of_wfM (WfM.top hpvSub)
  have hwfBodySub : WfM ΓSub body := by
    dsimp [body, bound]
    exact WfM.app hFunVarSub hArgSub
  have hwfAbs : WfM [] (.abs bound body) :=
    WfM.fun_ hwfBound hwfBodySub
  have hwfAbsTop : WfM [] (.abs bound .top) :=
    WfM.fun_ hwfBound (WfM.top hpvSub)
  have hBoundRed : MEqRed [] [] bound bound :=
    MEqRed.refl (PrevalidExt.nil hpvEmpty) hwfBound.scoped
  have hBodyTop : MSubRed ΓSub [] body .top := by
    exact MSubRed.top (PrevalidExt.nil hpvSub) hwfBodySub.scoped
  have hAbsSubTop : MSubRed [] [] (.abs bound body) (.abs bound .top) := by
    exact MSubRed.fun_ hwfBound.scoped hBoundRed hBodyTop
  have hAbsFun : WSubMStar [] (.abs bound body) (.abs bound .top) :=
    WSubMStar.sub hwfAbs
      (WSubM.lf2 hwfAbs hAbsSubTop hwfAbsTop (WSubM.rfl hwfAbsTop))
      hwfAbsTop
  let ΓEqu : Ctx := [{ bound := .top, kind := .equ }]
  have hpvEqu : Prevalid ΓEqu :=
    Prevalid.equ Prevalid.empty Term.Scoped.top
  have hpvEquNil : PrevalidExt ΓEqu [] := PrevalidExt.nil hpvEqu
  have hpvEquTopStack : PrevalidExt ΓEqu [.top] :=
    PrevalidExt.cons hpvEquNil Term.Scoped.top
  have hTopRedTopStack : MEqRed ΓEqu [.top] .top .top :=
    MEqRed.top hpvEquTopStack
  have hBvarRedTopStack : MEqRed ΓEqu [.top] (.bvar 0) .top := by
    simpa [ΓEqu, Term.shift] using
      (MEqRed.pro hpvEquTopStack
        (by simp [ΓEqu, Ctx.equBinds])
        hTopRedTopStack)
  have hTopRedTopNil : MEqRed ΓEqu [] .top .top :=
    MEqRed.top hpvEquNil
  have hBodyRed : MEqRed ΓEqu [] body body' := by
    dsimp [body, body']
    exact MEqRed.app hBvarRedTopStack hTopRedTopNil
  have hAbsRed :
      MEqRed [] [.top] (.abs bound body) (.abs bound body') := by
    exact MEqRed.fOp hBoundRed Term.Scoped.top hBodyRed
  have hAbsFun' : WSubMStar [] (.abs bound body') (.abs bound .top) :=
    hOpFun WfCtxEqu.empty WfStack.nil hwfTopEmpty hAbsFun hAbsRed
  have hwfAbs' : WfM [] (.abs bound body') := hAbsFun'.wf_left
  have hwfBody'Sub : WfM ΓSub body' := by
    simpa [ΓSub, bound] using hwfAbs'.fun_inv.2
  obtain ⟨funBound, hTopFun, _hArg⟩ := hwfBody'Sub.app_inv
  exact hNoTop hTopFun

/-- Consequently, the stack-indexed left-endpoint transport route is also
too broad: it implies the native `Me-App` operator payload refuted above. -/
noncomputable def MEqRedStackPreservesWSubMStarLeft.not_of_no_top
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedStackPreservesWSubMStarLeft → False := by
  intro hLeft
  exact MEqRedAppFunctionSupertypePayload.not_of_no_top hNoTop
    (MEqRedAppFunctionSupertypePayload.of_left_transport hLeft)

/-- Remaining context-replacement payload for the contextual `Me-Fun`
well-formedness case. After the body reduction is preserved under the old
`.sub` head, the body witness must be transported to the changed bound. -/
def MEqRedFunBodyReplacePayload : Type :=
  ∀ {Γ : Ctx} {bound bound' body' : Term},
    WfCtxEqu Γ →
      WfM Γ bound →
        WfM Γ bound' →
          MEqRed Γ [] bound bound' →
            WfM ({ bound := bound, kind := .sub } :: Γ) body' →
              WfM ({ bound := bound', kind := .sub } :: Γ) body'

/-- Remaining body payload for the contextual `Me-FOp` well-formedness case.
The source abstraction body is well-formed under `.sub bound`, but the
reduction premise runs under an `.equ operand` head from the stack. -/
def MEqRedFOpBodyPayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {bound bound' operand body body' : Term},
    WfCtxEqu Γ →
      WfStack Γ s →
        WfM Γ bound →
          WfM Γ bound' →
            WfM Γ operand →
              WfM ({ bound := bound, kind := .sub } :: Γ) body →
                MEqRed Γ [] bound bound' →
                  MEqRed ({ bound := operand, kind := .equ } :: Γ)
                    (Stack.shift 0 s) body body' →
                    WfM ({ bound := bound', kind := .sub } :: Γ) body'

/-- Typed `Me-FOp` body residual. Unlike `MEqRedFOpBodyPayload`, this records
the application typing fact that the stack operand is a well-subtype of the
abstraction bound. This is the premise missing from the broad contextual
target refuted by `MEqRedPreservesWfMContextual.not_of_no_top`. -/
def MEqRedFOpBodyTypedPayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {bound bound' operand body body' : Term},
    WfCtxEqu Γ →
      WfStack Γ s →
        WfM Γ bound →
          WfM Γ bound' →
            WSubMStar Γ operand bound →
              WfM ({ bound := bound, kind := .sub } :: Γ) body →
                MEqRed Γ [] bound bound' →
                  MEqRed ({ bound := operand, kind := .equ } :: Γ)
                    (Stack.shift 0 s) body body' →
                    WfM ({ bound := bound', kind := .sub } :: Γ) body'

/-- Tail transport residual for `Me-FOp` machine states after the target
immediate application has been retyped. This is deliberately stack-indexed:
the `Me-FOp` body reduction lives under the remaining tail stack, so it does
not by itself give an empty-stack well-subtyping relation between the
immediate source and target applications. -/
def MEqRedFOpTailTransportPayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {bound bound' operand body body' : Term},
    WfMachineState Γ (.abs bound body) (operand :: s) →
      WfM Γ (.app (.abs bound' body') operand) →
        WfMachineState Γ (.abs bound' body') (operand :: s)

/-- Exact tail transport residual for the `Me-FOp` machine-state case. Unlike
`MEqRedFOpTailTransportPayload`, this keeps the actual bound/body reduction
evidence in scope for the remaining tail-stack argument. -/
def MEqRedFOpTailTransportExactPayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {bound bound' operand body body' : Term},
    WfCtxEqu Γ →
      MEqRed Γ [] bound bound' →
        Term.Scoped Γ.depth operand →
          MEqRed ({ bound := operand, kind := .equ } :: Γ)
            (Stack.shift 0 s) body body' →
            WfMachineState Γ (.abs bound body) (operand :: s) →
              WfM Γ (.app (.abs bound' body') operand) →
                WfMachineState Γ (.abs bound' body') (operand :: s)

/-- The non-empty-tail part of exact `Me-FOp` machine-state transport. The
empty remaining-tail case is definitional from the target immediate
application typing. -/
def MEqRedFOpTailTransportConsPayload : Type :=
  ∀ {Γ : Ctx} {tail : Stack}
      {bound bound' operand next body body' : Term},
    WfCtxEqu Γ →
      MEqRed Γ [] bound bound' →
        Term.Scoped Γ.depth operand →
          MEqRed ({ bound := operand, kind := .equ } :: Γ)
            (Stack.shift 0 (next :: tail)) body body' →
            WfMachineState Γ (.abs bound body) (operand :: next :: tail) →
              WfM Γ (.app (.abs bound' body') operand) →
                WfMachineState Γ (.abs bound' body') (operand :: next :: tail)

/-- Tail-step machine-state preservation for the immediate application step
that remains after a non-empty-stack `Me-FOp`. The source and target controls
are the immediate applications; the stack is the remaining tail. -/
def MEqRedFOpTailStepPreservesPayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {source target : Term},
    WfCtxEqu Γ →
      MEqRed Γ s source target →
        WfM Γ target →
          WfMachineState Γ source s →
            WfMachineState Γ target s

/-- Constructor-generic tail-step machine-state preservation. This is the
neutral name for the residual first exposed by the `Me-FOp` tail transport:
once the immediate target control is well formed, preserve the same reduction
step under the remaining machine stack. -/
def MEqRedMachineTailStepPreservesPayload : Type :=
  ∀ {Γ : Ctx} {s : Stack} {source target : Term},
    WfCtxEqu Γ →
      MEqRed Γ s source target →
        WfM Γ target →
          WfMachineState Γ source s →
            WfMachineState Γ target s

/-- The original `Me-FOp`-named tail-step residual is the constructor-generic
machine-tail residual. -/
def MEqRedFOpTailStepPreservesPayload.of_machine_tail
    (hTail : MEqRedMachineTailStepPreservesPayload) :
    MEqRedFOpTailStepPreservesPayload :=
  hTail

/-- The constructor-generic machine-tail residual is exactly the original
`Me-FOp`-named tail-step residual. -/
def MEqRedMachineTailStepPreservesPayload.of_fop_tail_step
    (hTail : MEqRedFOpTailStepPreservesPayload) :
    MEqRedMachineTailStepPreservesPayload :=
  hTail

/-- Non-empty-stack part of the tail-step preservation residual. The empty
stack case is definitional from the supplied target well-formedness. -/
def MEqRedFOpTailStepPreservesConsPayload : Type :=
  ∀ {Γ : Ctx} {tail : Stack} {source target next : Term},
    WfCtxEqu Γ →
      MEqRed Γ (next :: tail) source target →
        WfM Γ target →
          WfMachineState Γ source (next :: tail) →
            WfMachineState Γ target (next :: tail)

/-- Constructor-generic non-empty machine-tail preservation residual. This is
the neutral name for the non-empty case of the original `Me-FOp` tail-step
split. -/
def MEqRedMachineTailStepPreservesConsPayload : Type :=
  ∀ {Γ : Ctx} {tail : Stack} {source target next : Term},
    WfCtxEqu Γ →
      MEqRed Γ (next :: tail) source target →
        WfM Γ target →
          WfMachineState Γ source (next :: tail) →
            WfMachineState Γ target (next :: tail)

/-- The original `Me-FOp`-named non-empty tail residual is the
constructor-generic non-empty machine-tail residual. -/
def MEqRedFOpTailStepPreservesConsPayload.of_machine_tail_cons
    (hCons : MEqRedMachineTailStepPreservesConsPayload) :
    MEqRedFOpTailStepPreservesConsPayload :=
  hCons

/-- The constructor-generic non-empty machine-tail residual is exactly the
original `Me-FOp`-named non-empty tail residual. -/
def MEqRedMachineTailStepPreservesConsPayload.of_fop_tail_cons
    (hCons : MEqRedFOpTailStepPreservesConsPayload) :
    MEqRedMachineTailStepPreservesConsPayload :=
  hCons

/-- Tail-step preservation reduces to its non-empty-stack case. -/
def MEqRedFOpTailStepPreservesPayload.of_cons
    (hCons : MEqRedFOpTailStepPreservesConsPayload) :
    MEqRedFOpTailStepPreservesPayload := by
  intro Γ s source target hΓ hred hwfTarget hState
  cases s with
  | nil =>
      simpa [WfMachineState, Stack.plug] using hwfTarget
  | cons next tail =>
      exact hCons hΓ hred hwfTarget hState

/-- Neutral machine-tail preservation reduces to its non-empty-stack case. -/
def MEqRedMachineTailStepPreservesPayload.of_cons
    (hCons : MEqRedMachineTailStepPreservesConsPayload) :
    MEqRedMachineTailStepPreservesPayload :=
  MEqRedMachineTailStepPreservesPayload.of_fop_tail_step
    (MEqRedFOpTailStepPreservesPayload.of_cons
      (MEqRedFOpTailStepPreservesConsPayload.of_machine_tail_cons hCons))

/-- `Me-Bet` machine-state preservation reduces to immediate β-target
well-formedness plus generic preservation of the resulting step under the
remaining pending stack. -/
noncomputable def MEqRedBetaPreservesWfMachineStatePayload.of_target_and_tail_step
    (hTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload) :
    MEqRedBetaPreservesWfMachineStatePayload := by
  intro Γ s bound arg arg' body body' hΓ ht hBody hArg hState
  have hwfTarget : WfM Γ (Term.instantiate 0 arg' body') :=
    hTarget hΓ ht hBody hArg hState
  exact hTailStep hΓ (MEqRed.bet ht hBody hArg) hwfTarget hState

/-- Neutral machine-tail variant of
`MEqRedBetaPreservesWfMachineStatePayload.of_target_and_tail_step`. -/
noncomputable def MEqRedBetaPreservesWfMachineStatePayload.of_target_and_machine_tail
    (hTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload) :
    MEqRedBetaPreservesWfMachineStatePayload :=
  MEqRedBetaPreservesWfMachineStatePayload.of_target_and_tail_step hTarget
    (MEqRedFOpTailStepPreservesPayload.of_machine_tail hTail)

/-- A non-empty tail step reduces to typed operator-function preservation for
the immediate application, followed by preservation of the induced
application step under the remaining tail. -/
noncomputable def MEqRedFOpTailStepPreservesConsPayload.of_typed_operator
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload) :
    MEqRedFOpTailStepPreservesConsPayload := by
  intro Γ tail source target next hΓ hred hwfTarget hState
  have hStack : WfStack Γ (next :: tail) :=
    WfMachineState.stack_wf hState
  have hStackTail : WfStack Γ tail := WfStack.tail hStack
  have hImmediateSource : WfM Γ (.app source next) :=
    WfMachineState.head_app_wf hState
  obtain ⟨bound, hFunSource, hArgNext⟩ := hImmediateSource.app_inv
  have hFunTarget : WSubMStar Γ target (.abs bound .top) :=
    hOpFun hΓ hStackTail hArgNext hFunSource hred
  have hImmediateTarget : WfM Γ (.app target next) :=
    WfM.app hFunTarget hArgNext
  have hNextRefl : MEqRed Γ [] next next :=
    MEqRed.refl (PrevalidExt.nil hArgNext.wf_left.prevalid)
      hArgNext.wf_left.scoped
  have hAppRed : MEqRed Γ tail (.app source next) (.app target next) :=
    MEqRed.app hred hNextRefl
  exact hTailStep (s := tail) (source := .app source next)
    (target := .app target next) hΓ hAppRed hImmediateTarget
    (WfMachineState.tail_state (t := source) (operand := next)
      (s := tail) hState)

/-- Machine-state-aware variant of
`MEqRedFOpTailStepPreservesConsPayload.of_typed_operator`. This is the
sharper payload shape for the machine-preservation path. -/
noncomputable def MEqRedFOpTailStepPreservesConsPayload.of_machine_operator
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload) :
    MEqRedFOpTailStepPreservesConsPayload := by
  intro Γ tail source target next hΓ hred hwfTarget hState
  have hImmediateSource : WfM Γ (.app source next) :=
    WfMachineState.head_app_wf hState
  obtain ⟨bound, hFunSource, hArgNext⟩ := hImmediateSource.app_inv
  have hFunTarget : WSubMStar Γ target (.abs bound .top) :=
    hOpFun hΓ hState hArgNext hFunSource hred
  have hImmediateTarget : WfM Γ (.app target next) :=
    WfM.app hFunTarget hArgNext
  have hNextRefl : MEqRed Γ [] next next :=
    MEqRed.refl (PrevalidExt.nil hArgNext.wf_left.prevalid)
      hArgNext.wf_left.scoped
  have hAppRed : MEqRed Γ tail (.app source next) (.app target next) :=
    MEqRed.app hred hNextRefl
  exact hTailStep (s := tail) (source := .app source next)
    (target := .app target next) hΓ hAppRed hImmediateTarget
    (WfMachineState.tail_state (t := source) (operand := next)
      (s := tail) hState)

/-- Smaller target-application variant of the non-empty tail-step reduction.
The recursive tail transport only needs `WfM Γ (target next)`, not an
explicit function-supertype witness for `target`. -/
noncomputable def MEqRedFOpTailStepPreservesConsPayload.of_target_app
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload) :
    MEqRedFOpTailStepPreservesConsPayload := by
  intro Γ tail source target next hΓ hred _hwfTarget hState
  have hImmediateTarget : WfM Γ (.app target next) :=
    hTargetApp hΓ hState hred
  have hImmediateSource : WfM Γ (.app source next) :=
    WfMachineState.head_app_wf hState
  obtain ⟨_, _hFunSource, hArgNext⟩ := hImmediateSource.app_inv
  have hNextRefl : MEqRed Γ [] next next :=
    MEqRed.refl (PrevalidExt.nil hArgNext.wf_left.prevalid)
      hArgNext.wf_left.scoped
  have hAppRed : MEqRed Γ tail (.app source next) (.app target next) :=
    MEqRed.app hred hNextRefl
  exact hTailStep (s := tail) (source := .app source next)
    (target := .app target next) hΓ hAppRed hImmediateTarget
    (WfMachineState.tail_state (t := source) (operand := next)
      (s := tail) hState)

/-- Neutral machine-tail spelling of the target-application reduction for
non-empty tail-step preservation. -/
noncomputable def MEqRedMachineTailStepPreservesConsPayload.of_target_app
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload) :
    MEqRedMachineTailStepPreservesConsPayload :=
  MEqRedMachineTailStepPreservesConsPayload.of_fop_tail_cons
    (MEqRedFOpTailStepPreservesConsPayload.of_target_app hTargetApp
      (MEqRedFOpTailStepPreservesPayload.of_machine_tail hTail))

/-- Neutral machine-tail spelling of the typed-operator reduction for
non-empty tail-step preservation. -/
noncomputable def MEqRedMachineTailStepPreservesConsPayload.of_typed_operator
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload) :
    MEqRedMachineTailStepPreservesConsPayload :=
  MEqRedMachineTailStepPreservesConsPayload.of_target_app
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun) hTail

/-- Neutral machine-tail spelling of the machine-state-aware operator
reduction for non-empty tail-step preservation. -/
noncomputable def MEqRedMachineTailStepPreservesConsPayload.of_machine_operator
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload) :
    MEqRedMachineTailStepPreservesConsPayload :=
  MEqRedMachineTailStepPreservesConsPayload.of_target_app
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun) hTail

/-- The non-empty-tail `Me-FOp` transport reduces to preserving the immediate
application `Me-App` step under the remaining tail stack. -/
noncomputable def MEqRedFOpTailTransportConsPayload.of_tail_step
    (hTailStep : MEqRedFOpTailStepPreservesPayload) :
    MEqRedFOpTailTransportConsPayload := by
  intro Γ tail bound bound' operand next body body'
    hΓ hBound hOperand hBody hState hAppTarget
  obtain ⟨_, _hTargetFun, hTargetArg⟩ := hAppTarget.app_inv
  have hArgRefl : MEqRed Γ [] operand operand :=
    MEqRed.refl (PrevalidExt.nil hTargetArg.wf_left.prevalid)
      hTargetArg.wf_left.scoped
  have hAbsRed :
      MEqRed Γ (operand :: next :: tail) (.abs bound body)
        (.abs bound' body') :=
    MEqRed.fOp hBound hOperand hBody
  have hAppRed :
      MEqRed Γ (next :: tail) (.app (.abs bound body) operand)
        (.app (.abs bound' body') operand) :=
    MEqRed.app hAbsRed hArgRefl
  exact hTailStep (s := next :: tail)
    (source := .app (.abs bound body) operand)
    (target := .app (.abs bound' body') operand)
    hΓ hAppRed hAppTarget (WfMachineState.tail_state hState)

/-- Exact `Me-FOp` tail transport reduces to the non-empty-tail case; the
single-operand machine state follows directly from the target application
typing. -/
def MEqRedFOpTailTransportExactPayload.of_cons
    (hCons : MEqRedFOpTailTransportConsPayload) :
    MEqRedFOpTailTransportExactPayload := by
  intro Γ s bound bound' operand body body' hΓ hBound hOperand hBody hState hApp
  cases s with
  | nil =>
      simpa [WfMachineState, Stack.plug] using hApp
  | cons next tail =>
      exact hCons hΓ hBound hOperand hBody hState hApp

/-- The machine-state `Me-FOp` residual reduces to the typed body payload,
function-bound inversion for the source abstraction application, empty-stack
preservation for the bound step, and a tail-stack transport residual. -/
noncomputable def MEqRedFOpPreservesWfMachineStatePayload.of_typed_body
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBoundPres :
      ∀ {Γ : Ctx} {source target : Term},
        WfCtxEqu Γ → MEqRed Γ [] source target → WfM Γ source → WfM Γ target)
    (hBody : MEqRedFOpBodyTypedPayload)
    (hTail : MEqRedFOpTailTransportPayload) :
    MEqRedFOpPreservesWfMachineStatePayload := by
  intro Γ s bound bound' operand body body' hΓ hBound hOperandScoped hBodyRed hState
  have hStack : WfStack Γ (operand :: s) :=
    WfMachineState.stack_wf hState
  have hwfOperand : WfM Γ operand := WfStack.head hStack
  have hStackTail : WfStack Γ s := WfStack.tail hStack
  have hwfAbs : WfM Γ (.abs bound body) :=
    WfMachineState.control_wf hState
  have hwfBound : WfM Γ bound := hwfAbs.fun_inv.1
  have hwfBody : WfM ({ bound := bound, kind := .sub } :: Γ) body :=
    hwfAbs.fun_inv.2
  have hOperandBound : WSubMStar Γ operand bound :=
    WfMachineState.fop_operand_bound hInv hΓ hState
  have hwfBound' : WfM Γ bound' :=
    hBoundPres hΓ hBound hwfBound
  have hwfBody' :
      WfM ({ bound := bound', kind := .sub } :: Γ) body' :=
    hBody hΓ hStackTail hwfBound hwfBound' hOperandBound hwfBody
      hBound hBodyRed
  have hwfAbs' : WfM Γ (.abs bound' body') :=
    WfM.fun_ hwfBound' hwfBody'
  have hBoundSubBound' : WSubMStar Γ bound bound' :=
    WSubMStar.of_MEqRed_fwd hBound hwfBound hwfBound'
  have hOperandBound' : WSubMStar Γ operand bound' :=
    WSubMStar.trans hwfBound hOperandBound hBoundSubBound'
  have hwfAbsTop' : WfM Γ (.abs bound' .top) :=
    WfM.fun_ hwfBound'
      (WfM.top (Prevalid.sub hwfBound'.prevalid hwfBound'.scoped))
  have hBodyTop : MSubRed ({ bound := bound', kind := .sub } :: Γ) [] body' .top :=
    MSubRed.top (PrevalidExt.nil hwfBody'.prevalid) hwfBody'.scoped
  have hBoundRefl : MEqRed Γ [] bound' bound' :=
    MEqRed.refl (PrevalidExt.nil hwfBound'.prevalid) hwfBound'.scoped
  have hAbsSubTop : MSubRed Γ [] (.abs bound' body') (.abs bound' .top) :=
    MSubRed.fun_ hwfBound'.scoped hBoundRefl hBodyTop
  have hFunTarget : WSubMStar Γ (.abs bound' body') (.abs bound' .top) :=
    WSubMStar.of_MSubRed_fwd hAbsSubTop hwfAbs' hwfAbsTop'
  have hAppTarget : WfM Γ (.app (.abs bound' body') operand) :=
    WfM.app hFunTarget hOperandBound'
  exact hTail hState hAppTarget

/-- Exact-tail variant of
`MEqRedFOpPreservesWfMachineStatePayload.of_typed_body`, keeping the original
`Me-FOp` reduction premises available to the tail transport residual. -/
noncomputable def MEqRedFOpPreservesWfMachineStatePayload.of_typed_body_exact_tail
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBoundPres :
      ∀ {Γ : Ctx} {source target : Term},
        WfCtxEqu Γ → MEqRed Γ [] source target → WfM Γ source → WfM Γ target)
    (hBody : MEqRedFOpBodyTypedPayload)
    (hTail : MEqRedFOpTailTransportExactPayload) :
    MEqRedFOpPreservesWfMachineStatePayload := by
  intro Γ s bound bound' operand body body' hΓ hBound hOperandScoped hBodyRed hState
  have hStack : WfStack Γ (operand :: s) :=
    WfMachineState.stack_wf hState
  have hStackTail : WfStack Γ s := WfStack.tail hStack
  have hwfAbs : WfM Γ (.abs bound body) :=
    WfMachineState.control_wf hState
  have hwfBound : WfM Γ bound := hwfAbs.fun_inv.1
  have hwfBody : WfM ({ bound := bound, kind := .sub } :: Γ) body :=
    hwfAbs.fun_inv.2
  have hOperandBound : WSubMStar Γ operand bound :=
    WfMachineState.fop_operand_bound hInv hΓ hState
  have hwfBound' : WfM Γ bound' :=
    hBoundPres hΓ hBound hwfBound
  have hwfBody' :
      WfM ({ bound := bound', kind := .sub } :: Γ) body' :=
    hBody hΓ hStackTail hwfBound hwfBound' hOperandBound hwfBody
      hBound hBodyRed
  have hwfAbs' : WfM Γ (.abs bound' body') :=
    WfM.fun_ hwfBound' hwfBody'
  have hBoundSubBound' : WSubMStar Γ bound bound' :=
    WSubMStar.of_MEqRed_fwd hBound hwfBound hwfBound'
  have hOperandBound' : WSubMStar Γ operand bound' :=
    WSubMStar.trans hwfBound hOperandBound hBoundSubBound'
  have hwfAbsTop' : WfM Γ (.abs bound' .top) :=
    WfM.fun_ hwfBound'
      (WfM.top (Prevalid.sub hwfBound'.prevalid hwfBound'.scoped))
  have hBodyTop : MSubRed ({ bound := bound', kind := .sub } :: Γ) [] body' .top :=
    MSubRed.top (PrevalidExt.nil hwfBody'.prevalid) hwfBody'.scoped
  have hBoundRefl : MEqRed Γ [] bound' bound' :=
    MEqRed.refl (PrevalidExt.nil hwfBound'.prevalid) hwfBound'.scoped
  have hAbsSubTop : MSubRed Γ [] (.abs bound' body') (.abs bound' .top) :=
    MSubRed.fun_ hwfBound'.scoped hBoundRefl hBodyTop
  have hFunTarget : WSubMStar Γ (.abs bound' body') (.abs bound' .top) :=
    WSubMStar.of_MSubRed_fwd hAbsSubTop hwfAbs' hwfAbsTop'
  have hAppTarget : WfM Γ (.app (.abs bound' body') operand) :=
    WfM.app hFunTarget hOperandBound'
  exact hTail hΓ hBound hOperandScoped hBodyRed hState hAppTarget

/-- The native `Me-FOp` body residual is still too broad with only
`WfStack`: the stack operand can be `Top` while the abstraction body uses the
head variable as a function. Under the `.equ Top` head the body can reduce to
`Top Top`, which would have to be well formed under the target `.sub` head. -/
noncomputable def MEqRedFOpBodyPayload.not_of_no_top
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedFOpBodyPayload → False := by
  intro hBodyPayload
  let bound : Term := .abs .top .top
  let body : Term := .app (.bvar 0) .top
  let body' : Term := .app .top .top
  have hpvEmpty : Prevalid [] := Prevalid.empty
  have hwfTopEmpty : WfM [] .top := WfM.top hpvEmpty
  have hwfBound : WfM [] bound := by
    dsimp [bound]
    exact WfM.fun_ (WfM.top Prevalid.empty)
      (WfM.top (Prevalid.sub Prevalid.empty Term.Scoped.top))
  let ΓSub : Ctx := [{ bound := bound, kind := .sub }]
  have hpvSub : Prevalid ΓSub :=
    Prevalid.sub hpvEmpty hwfBound.scoped
  have hwfVarSub : WfM ΓSub (.bvar 0) := by
    exact @WfM.varSub ΓSub 0 bound hpvSub
      (by simp [ΓSub, Ctx.subBinds, bound])
  have hwfBoundSub : WfM ΓSub bound := by
    simpa [ΓSub, bound, Term.shift] using
      hwfBound.weaken_head hpvSub hpvEmpty
  have hProSub : MSubRed ΓSub [] (.bvar 0) bound := by
    simpa [ΓSub, bound, Term.shift] using
      (MSubRed.pro (PrevalidExt.nil hpvSub)
        (by simp [ΓSub, Ctx.subBinds, bound]))
  have hFunSub : WSubMStar ΓSub (.bvar 0) bound :=
    WSubMStar.sub hwfVarSub
      (WSubM.lf2 hwfVarSub hProSub hwfBoundSub (WSubM.rfl hwfBoundSub))
      hwfBoundSub
  have hArgSub : WSubMStar ΓSub .top .top :=
    WSubMStar.refl_of_wfM (WfM.top hpvSub)
  have hwfBodySub : WfM ΓSub body := by
    dsimp [body, bound]
    exact WfM.app hFunSub hArgSub
  let ΓEqu : Ctx := [{ bound := .top, kind := .equ }]
  have hpvEqu : Prevalid ΓEqu :=
    Prevalid.equ Prevalid.empty Term.Scoped.top
  have hpvEquNil : PrevalidExt ΓEqu [] := PrevalidExt.nil hpvEqu
  have hpvEquTopStack : PrevalidExt ΓEqu [.top] :=
    PrevalidExt.cons hpvEquNil Term.Scoped.top
  have hTopRedTopStack : MEqRed ΓEqu [.top] .top .top :=
    MEqRed.top hpvEquTopStack
  have hBvarRedTopStack : MEqRed ΓEqu [.top] (.bvar 0) .top := by
    simpa [ΓEqu, Term.shift] using
      (MEqRed.pro hpvEquTopStack
        (by simp [ΓEqu, Ctx.equBinds])
        hTopRedTopStack)
  have hTopRedTopNil : MEqRed ΓEqu [] .top .top :=
    MEqRed.top hpvEquNil
  have hBodyRed : MEqRed ΓEqu [] body body' := by
    dsimp [body, body']
    exact MEqRed.app hBvarRedTopStack hTopRedTopNil
  have hBoundRed : MEqRed [] [] bound bound :=
    MEqRed.refl (PrevalidExt.nil hpvEmpty) hwfBound.scoped
  have hwfBody'Sub : WfM ΓSub body' := by
    simpa [ΓSub, bound, body', Stack.shift] using
      hBodyPayload WfCtxEqu.empty WfStack.nil hwfBound hwfBound
        hwfTopEmpty hwfBodySub hBoundRed hBodyRed
  obtain ⟨funBound, hTopFun, _hArg⟩ := hwfBody'Sub.app_inv
  exact hNoTop hTopFun

/-- The current contextual preservation target is too broad with only
`WfStack`: the same `Me-FOp` counterexample is a one-step reduction from a
well-formed abstraction at stack `[Top]` to an abstraction whose body is
`Top Top`. -/
noncomputable def MEqRedPreservesWfMContextual.not_of_no_top
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMContextual → False := by
  intro hpres
  let bound : Term := .abs .top .top
  let body : Term := .app (.bvar 0) .top
  let body' : Term := .app .top .top
  have hpvEmpty : Prevalid [] := Prevalid.empty
  have hwfTopEmpty : WfM [] .top := WfM.top hpvEmpty
  have hwfBound : WfM [] bound := by
    dsimp [bound]
    exact WfM.fun_ (WfM.top Prevalid.empty)
      (WfM.top (Prevalid.sub Prevalid.empty Term.Scoped.top))
  let ΓSub : Ctx := [{ bound := bound, kind := .sub }]
  have hpvSub : Prevalid ΓSub :=
    Prevalid.sub hpvEmpty hwfBound.scoped
  have hwfVarSub : WfM ΓSub (.bvar 0) := by
    exact @WfM.varSub ΓSub 0 bound hpvSub
      (by simp [ΓSub, Ctx.subBinds, bound])
  have hwfBoundSub : WfM ΓSub bound := by
    simpa [ΓSub, bound, Term.shift] using
      hwfBound.weaken_head hpvSub hpvEmpty
  have hProSub : MSubRed ΓSub [] (.bvar 0) bound := by
    simpa [ΓSub, bound, Term.shift] using
      (MSubRed.pro (PrevalidExt.nil hpvSub)
        (by simp [ΓSub, Ctx.subBinds, bound]))
  have hFunSub : WSubMStar ΓSub (.bvar 0) bound :=
    WSubMStar.sub hwfVarSub
      (WSubM.lf2 hwfVarSub hProSub hwfBoundSub (WSubM.rfl hwfBoundSub))
      hwfBoundSub
  have hArgSub : WSubMStar ΓSub .top .top :=
    WSubMStar.refl_of_wfM (WfM.top hpvSub)
  have hwfBodySub : WfM ΓSub body := by
    dsimp [body, bound]
    exact WfM.app hFunSub hArgSub
  have hwfAbs : WfM [] (.abs bound body) := by
    exact WfM.fun_ hwfBound hwfBodySub
  let ΓEqu : Ctx := [{ bound := .top, kind := .equ }]
  have hpvEqu : Prevalid ΓEqu :=
    Prevalid.equ Prevalid.empty Term.Scoped.top
  have hpvEquNil : PrevalidExt ΓEqu [] := PrevalidExt.nil hpvEqu
  have hpvEquTopStack : PrevalidExt ΓEqu [.top] :=
    PrevalidExt.cons hpvEquNil Term.Scoped.top
  have hTopRedTopStack : MEqRed ΓEqu [.top] .top .top :=
    MEqRed.top hpvEquTopStack
  have hBvarRedTopStack : MEqRed ΓEqu [.top] (.bvar 0) .top := by
    simpa [ΓEqu, Term.shift] using
      (MEqRed.pro hpvEquTopStack
        (by simp [ΓEqu, Ctx.equBinds])
        hTopRedTopStack)
  have hTopRedTopNil : MEqRed ΓEqu [] .top .top :=
    MEqRed.top hpvEquNil
  have hBodyRed : MEqRed ΓEqu [] body body' := by
    dsimp [body, body']
    exact MEqRed.app hBvarRedTopStack hTopRedTopNil
  have hBoundRed : MEqRed [] [] bound bound :=
    MEqRed.refl (PrevalidExt.nil hpvEmpty) hwfBound.scoped
  have hAbsRed :
      MEqRed [] [.top] (.abs bound body) (.abs bound body') := by
    exact MEqRed.fOp hBoundRed Term.Scoped.top hBodyRed
  have hwfAbs' : WfM [] (.abs bound body') :=
    hpres WfCtxEqu.empty (WfStack.cons hwfTopEmpty WfStack.nil)
      hAbsRed hwfAbs
  have hwfBody'Sub : WfM ΓSub body' := by
    simpa [ΓSub, bound] using hwfAbs'.fun_inv.2
  obtain ⟨funBound, hTopFun, _hArg⟩ := hwfBody'Sub.app_inv
  exact hNoTop hTopFun

/-- Transport a function body from the source `.sub` binder to the
stack-introduced `.equ` binder used by `Me-FOp`. -/
def WfMSubHeadToEquHeadPayload : Type :=
  ∀ {Γ : Ctx} {bound operand body : Term},
    WfCtxEqu Γ →
      WfM Γ bound →
        WfM Γ operand →
          WfM ({ bound := bound, kind := .sub } :: Γ) body →
            WfM ({ bound := operand, kind := .equ } :: Γ) body

/-- Transport a function body back from the stack-introduced `.equ` binder to
the target `.sub` binder after the bound has reduced. -/
def WfMEquHeadToSubHeadPayload : Type :=
  ∀ {Γ : Ctx} {operand bound body : Term},
    WfCtxEqu Γ →
      WfM Γ operand →
        WfM Γ bound →
          WfM ({ bound := operand, kind := .equ } :: Γ) body →
            WfM ({ bound := bound, kind := .sub } :: Γ) body

/-- Uniform head-kind/body transport for the `Me-FOp` gap. It changes both
the head annotation and the head binding kind while preserving body
well-formedness. The source and target annotations are both required to be
well formed in the tail context. This payload is intentionally retained only
as a diagnostic/convenience interface: `WfMHeadKindTransportPayload.not_of_no_top`
shows it is too strong under the no-Top-function-supertype obstruction. -/
def WfMHeadKindTransportPayload : Type :=
  ∀ {Γ : Ctx} {source target body : Term} {sourceKind targetKind : CtxEntryKind},
    WfCtxEqu Γ →
      WfM Γ source →
        WfM Γ target →
          WfM ({ bound := source, kind := sourceKind } :: Γ) body →
            WfM ({ bound := target, kind := targetKind } :: Γ) body

/-- The unrestricted source `.sub` to stack-introduced `.equ` body transport
is too strong: a body can use the `.sub` head variable as a function, while
transporting it to an `.equ Top` head would make `Top` have a function
supertype. -/
noncomputable def WfMSubHeadToEquHeadPayload.not_of_no_top
    (hNoTop : NoTopFunctionSupertypesAt) :
    WfMSubHeadToEquHeadPayload → False := by
  intro hTransport
  let bound : Term := .abs .top .top
  let body : Term := .app (.bvar 0) .top
  have hpvEmpty : Prevalid [] := Prevalid.empty
  have hwfTopEmpty : WfM [] .top := WfM.top hpvEmpty
  have hwfBound : WfM [] bound := by
    dsimp [bound]
    exact WfM.fun_ (WfM.top Prevalid.empty)
      (WfM.top (Prevalid.sub Prevalid.empty Term.Scoped.top))
  let ΓSub : Ctx := [{ bound := bound, kind := .sub }]
  have hpvSub : Prevalid ΓSub :=
    Prevalid.sub hpvEmpty hwfBound.scoped
  have hwfVarSub : WfM ΓSub (.bvar 0) := by
    exact @WfM.varSub ΓSub 0 bound hpvSub
      (by simp [ΓSub, Ctx.subBinds, bound])
  have hwfBoundSub : WfM ΓSub bound := by
    simpa [ΓSub, bound, Term.shift] using
      hwfBound.weaken_head hpvSub hpvEmpty
  have hProSub : MSubRed ΓSub [] (.bvar 0) bound := by
    simpa [ΓSub, bound, Term.shift] using
      (MSubRed.pro (PrevalidExt.nil hpvSub)
        (by simp [ΓSub, Ctx.subBinds, bound]))
  have hFunSub : WSubMStar ΓSub (.bvar 0) bound :=
    WSubMStar.sub hwfVarSub
      (WSubM.lf2 hwfVarSub hProSub hwfBoundSub (WSubM.rfl hwfBoundSub))
      hwfBoundSub
  have hArgSub : WSubMStar ΓSub .top .top :=
    WSubMStar.refl_of_wfM (WfM.top hpvSub)
  have hwfBodySub : WfM ΓSub body := by
    dsimp [body, bound]
    exact WfM.app hFunSub hArgSub
  have hwfBodyEqu :
      WfM ([{ bound := .top, kind := .equ }] : Ctx) body :=
    hTransport WfCtxEqu.empty hwfBound hwfTopEmpty hwfBodySub
  obtain ⟨funBound, hFunEqu, _hArgEqu⟩ := hwfBodyEqu.app_inv
  let ΓEqu : Ctx := [{ bound := .top, kind := .equ }]
  have hpvEqu : Prevalid ΓEqu :=
    Prevalid.equ Prevalid.empty Term.Scoped.top
  have hwfVarEqu : WfM ΓEqu (.bvar 0) := by
    exact @WfM.varEqu ΓEqu 0 .top hpvEqu
      (by simp [ΓEqu, Ctx.equBinds])
  have hwfTopEqu : WfM ΓEqu .top := WfM.top hpvEqu
  have hBvarTop : MEqRed ΓEqu [] (.bvar 0) .top := by
    have hTopRefl : MEqRed ΓEqu [] .top .top :=
      MEqRed.refl (PrevalidExt.nil hpvEqu) Term.Scoped.top
    simpa [ΓEqu, Term.shift] using
      (MEqRed.pro (PrevalidExt.nil hpvEqu)
        (by simp [ΓEqu, Ctx.equBinds]) hTopRefl)
  have hTopVar : WSubMStar ΓEqu .top (.bvar 0) :=
    WSubMStar.of_MEqRed_back hBvarTop hwfVarEqu hwfTopEqu
  have hTopFun : WSubMStar ΓEqu .top (.abs funBound .top) :=
    WSubMStar.trans hwfVarEqu hTopVar (by simpa [ΓEqu] using hFunEqu)
  exact hNoTop hTopFun

/-- Uniform head-kind transport specializes to the source `.sub` to
stack-introduced `.equ` direction used by `Me-FOp`. -/
def WfMSubHeadToEquHeadPayload.of_head_kind_transport
    (hTransport : WfMHeadKindTransportPayload) :
    WfMSubHeadToEquHeadPayload := by
  intro Γ bound operand body hΓ hwfBound hwfOperand hwfBody
  exact hTransport (sourceKind := .sub) (targetKind := .equ)
    hΓ hwfBound hwfOperand hwfBody

/-- Consequently, the uniform head-kind/body transport payload is also too
strong under the no-Top-function-supertype obstruction. -/
noncomputable def WfMHeadKindTransportPayload.not_of_no_top
    (hNoTop : NoTopFunctionSupertypesAt) :
    WfMHeadKindTransportPayload → False := by
  intro hTransport
  exact WfMSubHeadToEquHeadPayload.not_of_no_top hNoTop
    (WfMSubHeadToEquHeadPayload.of_head_kind_transport hTransport)

/-- Uniform head-kind transport also specializes to the target `.equ` to
`.sub` direction used after the `Me-FOp` body has been preserved. -/
def WfMEquHeadToSubHeadPayload.of_head_kind_transport
    (hTransport : WfMHeadKindTransportPayload) :
    WfMEquHeadToSubHeadPayload := by
  intro Γ operand bound body hΓ hwfOperand hwfBound hwfBody
  exact hTransport (sourceKind := .equ) (targetKind := .sub)
    hΓ hwfOperand hwfBound hwfBody

/-- The `Me-FOp` body residual follows from source `.sub`→`.equ` transport,
contextual preservation under the stack-introduced `.equ` head, and target
`.equ`→`.sub` transport. -/
noncomputable def MEqRedFOpBodyPayload.of_head_transports
    (hpres : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedFOpBodyPayload := by
  intro Γ s bound bound' operand body body' hΓ hStack hwfBound hwfBound'
    hwfOperand hwfBody _hredBound hredBody
  have hΓEqu : WfCtxEqu ({ bound := operand, kind := .equ } :: Γ) :=
    WfCtxEqu.equ hΓ hwfOperand
  have hStackEqu :
      WfStack ({ bound := operand, kind := .equ } :: Γ) (Stack.shift 0 s) :=
    WfStack.weaken_equ_head hStack hwfOperand
  have hwfBodyEqu :
      WfM ({ bound := operand, kind := .equ } :: Γ) body :=
    hSubToEqu hΓ hwfBound hwfOperand hwfBody
  have hwfBody'Equ :
      WfM ({ bound := operand, kind := .equ } :: Γ) body' :=
    hpres hΓEqu hStackEqu hredBody hwfBodyEqu
  exact hEquToSub hΓ hwfOperand hwfBound' hwfBody'Equ

/-- The broad/native `Me-FOp` body residual implies the typed version by
recovering operand well-formedness from the source application's
operand-to-bound premise. -/
noncomputable def MEqRedFOpBodyTypedPayload.of_untyped
    (hBody : MEqRedFOpBodyPayload) :
    MEqRedFOpBodyTypedPayload := by
  intro Γ s bound bound' operand body body' hΓ hStack hwfBound hwfBound'
    hOperandBound hwfBody hredBound hredBody
  exact hBody hΓ hStack hwfBound hwfBound' hOperandBound.wf_left hwfBody
    hredBound hredBody

/-- The typed `Me-FOp` body residual follows from the same directional
head/body transports as the native residual; the typed operand premise
supplies the operand well-formedness needed to enter the stack-introduced
`.equ` context. -/
noncomputable def MEqRedFOpBodyTypedPayload.of_head_transports
    (hpres : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedFOpBodyTypedPayload :=
  MEqRedFOpBodyTypedPayload.of_untyped
    (MEqRedFOpBodyPayload.of_head_transports hpres hSubToEqu hEquToSub)

/-- Direct `Me-FOp` body residual from contextual preservation and one
uniform head-kind/body transport payload. This is only a diagnostic
convenience wrapper: `WfMHeadKindTransportPayload.not_of_no_top` shows the
uniform transport premise is too strong for the final preservation route. -/
noncomputable def MEqRedFOpBodyPayload.of_head_kind_transport
    (hpres : MEqRedPreservesWfMContextual)
    (hTransport : WfMHeadKindTransportPayload) :
    MEqRedFOpBodyPayload :=
  MEqRedFOpBodyPayload.of_head_transports hpres
    (WfMSubHeadToEquHeadPayload.of_head_kind_transport hTransport)
    (WfMEquHeadToSubHeadPayload.of_head_kind_transport hTransport)

/-- Typed direct `Me-FOp` body residual from contextual preservation and one
uniform head-kind/body transport payload. This is also diagnostic, for the
same reason as `MEqRedFOpBodyPayload.of_head_kind_transport`. -/
noncomputable def MEqRedFOpBodyTypedPayload.of_head_kind_transport
    (hpres : MEqRedPreservesWfMContextual)
    (hTransport : WfMHeadKindTransportPayload) :
    MEqRedFOpBodyTypedPayload :=
  MEqRedFOpBodyTypedPayload.of_head_transports hpres
    (WfMSubHeadToEquHeadPayload.of_head_kind_transport hTransport)
    (WfMEquHeadToSubHeadPayload.of_head_kind_transport hTransport)

/-- Remaining β payload for contextual `MEqRed` well-formedness
preservation. This is the constructor-level analogue of the operational β
payload, but for reduction targets produced by `Me-Bet`. -/
def MEqRedBetaPreservesWfMContextual : Type :=
  ∀ {Γ : Ctx} {s : Stack} {bound arg arg' body body' : Term},
    WfCtxEqu Γ →
      WfStack Γ s →
        Term.Scoped Γ.depth bound →
          MEqRed ({ bound := bound, kind := .sub } :: Γ)
            (Stack.shift 0 s) body body' →
            MEqRed Γ [] arg arg' →
              WfM Γ (.app (.abs bound body) arg) →
                WfM Γ (Term.instantiate 0 arg' body')

/-- Empty-stack preservation under a well-formed-equivalence context. -/
def MEqRedPreservesWfMUnderWfCtx : Type :=
  ∀ {Γ : Ctx} {x y : Term}, WfCtxEqu Γ → MEqRedJ Γ [] x y → WfM Γ x → WfM Γ y

/-- The contextual β constructor residual supplies the immediate β-target
well-formedness residual for machine-state preservation. A plugged source
machine state exposes the immediate β application as the control term and
the pending stack as a well-formed stack. -/
noncomputable def MEqRedBetaTargetPreservesWfMPayload.of_contextual
    (hBeta : MEqRedBetaPreservesWfMContextual) :
    MEqRedBetaTargetPreservesWfMPayload := by
  intro Γ s bound arg arg' body body' hΓ ht hBody hArg hState
  have hStack : WfStack Γ s := WfMachineState.stack_wf hState
  have hwfSource : WfM Γ (.app (.abs bound body) arg) :=
    WfMachineState.control_wf hState
  exact hBeta hΓ hStack ht hBody hArg hwfSource

/-- Contextual preservation supplies the beta body-preservation residual by
specializing under the source `.sub` head and shifting the pending stack
through that head. -/
noncomputable def MEqRedBetaBodyPreservesWfMPayload.of_contextual
    (hPres : MEqRedPreservesWfMContextual) :
    MEqRedBetaBodyPreservesWfMPayload := by
  intro Γ s bound body body' hΓ hStack hwfBound hBody hwfBody
  exact hPres (WfCtxEqu.sub hΓ) (WfStack.weaken_sub_head hStack hwfBound)
    hBody hwfBody

/-- Immediate β-target well-formedness from the exact beta-instantiation
lemma, function-bound inversion, beta-body preservation, and empty-stack
argument preservation. -/
noncomputable def MEqRedBetaTargetPreservesWfMPayload.of_body_arg_and_subst
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBodyPres : MEqRedBetaBodyPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx) :
    MEqRedBetaTargetPreservesWfMPayload := by
  intro Γ s bound arg arg' body body' hΓ _ht hBody hArg hState
  have hStack : WfStack Γ s := WfMachineState.stack_wf hState
  have hwfSource : WfM Γ (.app (.abs bound body) arg) :=
    WfMachineState.control_wf hState
  obtain ⟨result, hFun, hArgTyping⟩ := hwfSource.app_inv
  have hwfAbs : WfM Γ (.abs bound body) := hFun.wf_left
  have hwfBound : WfM Γ bound := hwfAbs.fun_inv.1
  have hwfBody : WfM ({ bound := bound, kind := .sub } :: Γ) body :=
    hwfAbs.fun_inv.2
  have hwfBody' :
      WfM ({ bound := bound, kind := .sub } :: Γ) body' :=
    hBodyPres hΓ hStack hwfBound hBody hwfBody
  have hwfArg : WfM Γ arg := hArgTyping.wf_left
  have hwfArg' : WfM Γ arg' := hEmpty hΓ ⟨hArg⟩ hwfArg
  have hArgBack : WSubMStar Γ arg' arg :=
    WSubMStar.of_MEqRed_back hArg hwfArg hwfArg'
  have hArgResult : WSubMStar Γ arg' result :=
    WSubMStar.trans hwfArg hArgBack hArgTyping
  have hEquBoundResult : WEquMStar Γ bound result := hInv hΓ hFun
  have hSubResultBound : WSubMStar Γ result bound :=
    hEquBoundResult.symm.toWSubMStar
  have hArgBound : WSubMStar Γ arg' bound :=
    WSubMStar.trans hArgTyping.wf_right hArgResult hSubResultBound
  exact hSubst hArgBound hwfBody'

/-- Machine-state preservation specializes to empty-stack well-formedness
preservation. -/
noncomputable def MEqRedPreservesWfMUnderWfCtx.of_machine_state
    (hpres : MEqRedPreservesWfMachineState) :
    MEqRedPreservesWfMUnderWfCtx := by
  intro Γ x y hΓ hred hwf
  simpa [WfMachineState, Stack.plug] using
    hpres hΓ hred.some (by simpa [WfMachineState, Stack.plug] using hwf)

/-- Convenience form of the typed `Me-FOp` machine-state reduction using the
existing empty-stack preservation payload for the abstraction-bound step. -/
noncomputable def MEqRedFOpPreservesWfMachineStatePayload.of_typed_body_and_empty
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hBody : MEqRedFOpBodyTypedPayload)
    (hTail : MEqRedFOpTailTransportPayload) :
    MEqRedFOpPreservesWfMachineStatePayload :=
  MEqRedFOpPreservesWfMachineStatePayload.of_typed_body hInv
    (fun hΓ hred hwf => hEmpty hΓ ⟨hred⟩ hwf)
    hBody hTail

/-- Exact-tail convenience form of the typed `Me-FOp` machine-state
reduction using the existing empty-stack preservation payload for the
abstraction-bound step. -/
noncomputable def MEqRedFOpPreservesWfMachineStatePayload.of_typed_body_exact_tail_and_empty
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hBody : MEqRedFOpBodyTypedPayload)
    (hTail : MEqRedFOpTailTransportExactPayload) :
    MEqRedFOpPreservesWfMachineStatePayload :=
  MEqRedFOpPreservesWfMachineStatePayload.of_typed_body_exact_tail hInv
    (fun hΓ hred hwf => hEmpty hΓ ⟨hred⟩ hwf)
    hBody hTail

/-- Non-empty-tail convenience form of the typed `Me-FOp` machine-state
reduction. The empty remaining-tail case is discharged by
`MEqRedFOpTailTransportExactPayload.of_cons`. -/
noncomputable def MEqRedFOpPreservesWfMachineStatePayload.of_typed_body_cons_tail_and_empty
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hBody : MEqRedFOpBodyTypedPayload)
    (hTail : MEqRedFOpTailTransportConsPayload) :
    MEqRedFOpPreservesWfMachineStatePayload :=
  MEqRedFOpPreservesWfMachineStatePayload.of_typed_body_exact_tail_and_empty
    hInv hEmpty hBody (MEqRedFOpTailTransportExactPayload.of_cons hTail)

/-- Tail-step variant of the typed `Me-FOp` machine-state reduction. The
non-empty tail is reduced to preservation of the induced immediate
application step under the remaining tail stack. -/
noncomputable def MEqRedFOpPreservesWfMachineStatePayload.of_typed_body_tail_step_and_empty
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hBody : MEqRedFOpBodyTypedPayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload) :
    MEqRedFOpPreservesWfMachineStatePayload :=
  MEqRedFOpPreservesWfMachineStatePayload.of_typed_body_cons_tail_and_empty
    hInv hEmpty hBody
    (MEqRedFOpTailTransportConsPayload.of_tail_step hTailStep)

/-- Non-empty-tail-step variant of the typed `Me-FOp` machine-state
reduction. The induced immediate-application step at an empty residual tail
is discharged definitionally. -/
noncomputable def MEqRedFOpPreservesWfMachineStatePayload.of_typed_body_tail_step_cons_and_empty
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hBody : MEqRedFOpBodyTypedPayload)
    (hTailStep : MEqRedFOpTailStepPreservesConsPayload) :
    MEqRedFOpPreservesWfMachineStatePayload :=
  MEqRedFOpPreservesWfMachineStatePayload.of_typed_body_tail_step_and_empty
    hInv hEmpty hBody
    (MEqRedFOpTailStepPreservesPayload.of_cons hTailStep)

/-- Typed-operator variant of the `Me-FOp` machine-state reduction. The
non-empty induced tail step is reduced to typed operator preservation for the
immediate application plus a recursive tail-step residual. -/
noncomputable def MEqRedFOpPreservesWfMachineStatePayload.of_typed_body_operator_tail_step_and_empty
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload) :
    MEqRedFOpPreservesWfMachineStatePayload :=
  MEqRedFOpPreservesWfMachineStatePayload.of_typed_body_tail_step_cons_and_empty
    hInv hEmpty hBody
    (MEqRedFOpTailStepPreservesConsPayload.of_typed_operator
      hOpFun hTailStep)

/-- Machine-state-aware operator variant of the typed `Me-FOp`
machine-state reduction. -/
noncomputable def MEqRedFOpPreservesWfMachineStatePayload.of_typed_body_machine_operator_tail_step_and_empty
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload) :
    MEqRedFOpPreservesWfMachineStatePayload :=
  MEqRedFOpPreservesWfMachineStatePayload.of_typed_body_tail_step_cons_and_empty
    hInv hEmpty hBody
    (MEqRedFOpTailStepPreservesConsPayload.of_machine_operator
      hOpFun hTailStep)

/-- Target-application variant of the typed `Me-FOp` machine-state reduction.
The recursive non-empty tail route only requires immediate target
well-formedness plus the recursive tail-step residual. -/
noncomputable def MEqRedFOpPreservesWfMachineStatePayload.of_typed_body_target_app_tail_step_and_empty
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload) :
    MEqRedFOpPreservesWfMachineStatePayload :=
  MEqRedFOpPreservesWfMachineStatePayload.of_typed_body_tail_step_cons_and_empty
    hInv hEmpty hBody
    (MEqRedFOpTailStepPreservesConsPayload.of_target_app
      hTargetApp hTailStep)

/-- Control-term transport plus empty-stack preservation discharges the
machine-state stack-head replacement residual. The source plugged state
exposes the immediate application `u v`; after preserving the empty-stack
operand step, `u v'` is well formed and is a well-subtype of `u v` by a
backward `Me-App` embedding. -/
noncomputable def MEqRedMachineStackHeadReplacePayload.of_control_left
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hControl : WfMachineStateControlLeftPayload) :
    MEqRedMachineStackHeadReplacePayload := by
  intro Γ s u v v' hΓ hred hState
  have hApp : WfM Γ (.app u v) := WfMachineState.head_app_wf hState
  obtain ⟨bound, hFun, hArg⟩ := hApp.app_inv
  have hwfV : WfM Γ v := hArg.wf_left
  have hwfV' : WfM Γ v' := hEmpty hΓ ⟨hred⟩ hwfV
  have hArgBack : WSubMStar Γ v' v :=
    WSubMStar.of_MEqRed_back hred hwfV hwfV'
  have hArg' : WSubMStar Γ v' bound :=
    WSubMStar.trans hwfV hArgBack hArg
  have hApp' : WfM Γ (.app u v') := WfM.app hFun hArg'
  have hpvStack : PrevalidExt Γ [v] :=
    PrevalidExt.cons (PrevalidExt.nil hwfV.prevalid) hwfV.scoped
  have hOpRefl : MEqRed Γ [v] u u :=
    MEqRed.refl hpvStack hFun.wf_left.scoped
  have hAppRed : MEqRed Γ [] (.app u v) (.app u v') :=
    MEqRed.app hOpRefl hred
  have hControlBack : WSubMStar Γ (.app u v') (.app u v) :=
    WSubMStar.of_MEqRed_back hAppRed hApp hApp'
  have hTail' : WfMachineState Γ (.app u v') s :=
    hControl hControlBack (WfMachineState.tail_state hState)
  simpa [WfMachineState, Stack.plug] using hTail'

/-- Append-native stack-head replacement assembly: build control-left
transport from the generalized diagrammatic stack-append payload. -/
noncomputable def MEqRedMachineStackHeadReplacePayload.of_msubstar_stack_append
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload) :
    MEqRedMachineStackHeadReplacePayload :=
  MEqRedMachineStackHeadReplacePayload.of_control_left hEmpty
    (WfMachineStateControlLeftPayload.of_msubstar_stack_append
      hAppend hBridge)

/-- Stack-head replacement assembled from empty-stack preservation and the
reduced stack-lift body-transport package. -/
noncomputable def MEqRedMachineStackHeadReplacePayload.of_body_transports_and_steps
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload) :
    MEqRedMachineStackHeadReplacePayload :=
  MEqRedMachineStackHeadReplacePayload.of_msubstar_stack_append hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)

/-- Control-left transport discharges the smaller `Me-Pro` annotation
machine-state residual. The empty-stack `Me-Pro` step embeds backward as
`α ≤* bvar i`; control transport then replaces the machine-state control. -/
noncomputable def MEqRedProAnnotationMachineStatePayload.of_control_left
    (hControl : WfMachineStateControlLeftPayload) :
    MEqRedProAnnotationMachineStatePayload := by
  intro Γ s i α hΓ hb hState
  have hwfVar : WfM Γ (.bvar i) := WfMachineState.control_wf hState
  have hwfα : WfM Γ α := WfCtxEqu.lookup_equ hΓ hwfVar.prevalid hb
  have hαRefl : MEqRed Γ [] α α :=
    MEqRed.refl (PrevalidExt.nil hwfα.prevalid) hwfα.scoped
  have hPro : MEqRed Γ [] (.bvar i) α :=
    MEqRed.pro (PrevalidExt.nil hwfVar.prevalid) hb hαRefl
  have hαVar : WSubMStar Γ α (.bvar i) :=
    WSubMStar.of_MEqRed_back hPro hwfVar hwfα
  exact hControl hαVar hState

/-- Append-native `Me-Pro` annotation machine-state assembly: build
control-left transport from the generalized diagrammatic stack-append
payload. -/
noncomputable def MEqRedProAnnotationMachineStatePayload.of_msubstar_stack_append
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload) :
    MEqRedProAnnotationMachineStatePayload :=
  MEqRedProAnnotationMachineStatePayload.of_control_left
    (WfMachineStateControlLeftPayload.of_msubstar_stack_append
      hAppend hBridge)

/-- The smaller `Me-Pro` annotation machine-state residual assembled from the
reduced stack-lift body-transport package. -/
noncomputable def MEqRedProAnnotationMachineStatePayload.of_body_transports_and_steps
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload) :
    MEqRedProAnnotationMachineStatePayload :=
  MEqRedProAnnotationMachineStatePayload.of_msubstar_stack_append
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)

/-- The `Me-TAp` machine-state residual is vacuous under the context-generic
no-`Top`-function-supertype fact: a plugged source state for `.app .top u`
exposes a well-formed immediate application headed by `Top`. -/
noncomputable def MEqRedTApPreservesWfMachineStatePayload.of_no_top
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedTApPreservesWfMachineStatePayload := by
  intro Γ s u hΓ hu hState
  have hBad : WfM Γ (.app .top u) := by
    cases s with
    | nil =>
        simpa [WfMachineState, Stack.plug] using hState
    | cons operand tail =>
        have hOuter : WfM Γ (.app (.app .top u) operand) :=
          WfMachineState.head_app_wf hState
        obtain ⟨_, hFun, _⟩ := hOuter.app_inv
        exact hFun.wf_left
  obtain ⟨bound, hFun, _hArg⟩ := hBad.app_inv
  exact (hNoTop hFun).elim

/-- The empty-stack `Me-Fun` machine-state residual reduces to empty-stack
preservation plus the existing body context-replacement payload. -/
noncomputable def MEqRedFunPreservesWfMachineStatePayload.of_empty_and_body_replace
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hBodyReplace : MEqRedFunBodyReplacePayload) :
    MEqRedFunPreservesWfMachineStatePayload := by
  intro Γ bound bound' body body' hΓ hredBound hredBody hState
  have hwfAbs : WfM Γ (.abs bound body) := by
    simpa [WfMachineState, Stack.plug] using hState
  have hwfBound : WfM Γ bound := hwfAbs.fun_inv.1
  have hwfBody : WfM ({ bound := bound, kind := .sub } :: Γ) body :=
    hwfAbs.fun_inv.2
  have hwfBound' : WfM Γ bound' :=
    hEmpty hΓ ⟨hredBound⟩ hwfBound
  have hΓBody : WfCtxEqu ({ bound := bound, kind := .sub } :: Γ) :=
    WfCtxEqu.sub hΓ
  have hwfBody'Old : WfM ({ bound := bound, kind := .sub } :: Γ) body' :=
    hEmpty hΓBody ⟨hredBody⟩ hwfBody
  have hwfTarget : WfM Γ (.abs bound' body') :=
    WfM.fun_ hwfBound'
      (hBodyReplace hΓ hwfBound hwfBound' hredBound hwfBody'Old)
  simpa [WfMachineState, Stack.plug] using hwfTarget

/-- Reduced machine-state preservation assembly after discharging the
structural `Me-App` head replacement, `Me-Fun`, and `Me-TAp` residuals
through smaller premises. The broad `Me-Pro` machine residual is split and
discharged through control-left annotation transport; control-left itself
is reduced to operator-side application congruence for `WSubMStar`. The
remaining constructor-sized machine residuals are `Me-Bet` and `Me-FOp`. -/
noncomputable def MEqRedPreservesWfMachineState.of_reduced_components
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppOp : WSubMStarAppOperatorPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt)
    (hFOp : MEqRedFOpPreservesWfMachineStatePayload) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_components_pro_annotation
    (MEqRedProAnnotationMachineStatePayload.of_control_left
      (WfMachineStateControlLeftPayload.of_app_operator hAppOp))
    hBeta
    (MEqRedMachineStackHeadReplacePayload.of_control_left hEmpty
      (WfMachineStateControlLeftPayload.of_app_operator hAppOp))
    (MEqRedFunPreservesWfMachineStatePayload.of_empty_and_body_replace
      hEmpty hFunBody)
    (MEqRedTApPreservesWfMachineStatePayload.of_no_top hNoTop)
    hFOp

/-- Append-native external-empty reduced assembly for control/app-operator
transport. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt)
    (hFOp : MEqRedFOpPreservesWfMachineStatePayload) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_components_pro_annotation
    (MEqRedProAnnotationMachineStatePayload.of_msubstar_stack_append
      hAppend hBridge)
    hBeta
    (MEqRedMachineStackHeadReplacePayload.of_msubstar_stack_append
      hEmpty hAppend hBridge)
    (MEqRedFunPreservesWfMachineStatePayload.of_empty_and_body_replace
      hEmpty hFunBody)
    (MEqRedTApPreservesWfMachineStatePayload.of_no_top hNoTop)
    hFOp

/-- External-empty reduced assembly using the current body-transport
decomposition for control/app-operator transport. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt)
    (hFOp : MEqRedFOpPreservesWfMachineStatePayload) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append
    hBeta hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hFunBody hNoTop hFOp

/-- External-empty machine-state assembly with both the control/app-operator
side and the `Me-FOp` constructor reduced to their typed body/tail transport
residuals. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hFOpTail : MEqRedFOpTailTransportPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append
    hBeta hEmpty hAppend hBridge hFunBody hNoTop
    (MEqRedFOpPreservesWfMachineStatePayload.of_typed_body_and_empty
      hInv hEmpty hFOpBody hFOpTail)

/-- External-empty machine-state assembly with both the control/app-operator
side and the `Me-FOp` constructor reduced to their typed body/tail transport
residuals. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_typed_fop
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hFOpTail : MEqRedFOpTailTransportPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop
    hBeta hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hFOpTail hFunBody hNoTop

/-- Exact-tail variant of
`MEqRedPreservesWfMachineState.of_body_transports_and_typed_fop`, retaining
the `Me-FOp` reduction evidence in the remaining tail-transport residual. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_exact_tail
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hFOpTail : MEqRedFOpTailTransportExactPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append
    hBeta hEmpty hAppend hBridge hFunBody hNoTop
    (MEqRedFOpPreservesWfMachineStatePayload.of_typed_body_exact_tail_and_empty
      hInv hEmpty hFOpBody hFOpTail)

/-- Exact-tail variant of
`MEqRedPreservesWfMachineState.of_body_transports_and_typed_fop`, retaining
the `Me-FOp` reduction evidence in the remaining tail-transport residual. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_typed_fop_exact_tail
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hFOpTail : MEqRedFOpTailTransportExactPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_exact_tail
    hBeta hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hFOpTail hFunBody hNoTop

/-- Non-empty-tail variant of
`MEqRedPreservesWfMachineState.of_body_transports_and_typed_fop_exact_tail`.
The no-tail `Me-FOp` machine-state case is discharged definitionally from the
target immediate application typing. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_cons_tail
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hFOpTail : MEqRedFOpTailTransportConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_exact_tail
    hBeta hEmpty hAppend hBridge hInv hFOpBody
    (MEqRedFOpTailTransportExactPayload.of_cons hFOpTail)
    hFunBody hNoTop

/-- Non-empty-tail variant of
`MEqRedPreservesWfMachineState.of_body_transports_and_typed_fop_exact_tail`.
The no-tail `Me-FOp` machine-state case is discharged definitionally from the
target immediate application typing. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_typed_fop_cons_tail
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hFOpTail : MEqRedFOpTailTransportConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_cons_tail
    hBeta hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hFOpTail hFunBody hNoTop

/-- Tail-step variant of
`MEqRedPreservesWfMachineState.of_body_transports_and_typed_fop_cons_tail`,
reducing the remaining non-empty `Me-FOp` tail obligation to preservation of
the induced immediate application step under the tail stack. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_tail_step
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hFOpTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_cons_tail
    hBeta hEmpty hAppend hBridge hInv hFOpBody
    (MEqRedFOpTailTransportConsPayload.of_tail_step hFOpTailStep)
    hFunBody hNoTop

/-- Tail-step variant of
`MEqRedPreservesWfMachineState.of_body_transports_and_typed_fop_cons_tail`,
reducing the remaining non-empty `Me-FOp` tail obligation to preservation of
the induced immediate application step under the tail stack. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_typed_fop_tail_step
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hFOpTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_tail_step
    hBeta hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hFOpTailStep hFunBody hNoTop

/-- Non-empty-tail-step variant of
`MEqRedPreservesWfMachineState.of_body_transports_and_typed_fop_tail_step`.
The induced immediate-application step at an empty residual tail is
definitionally discharged. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_tail_step_cons
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hFOpTailStep : MEqRedFOpTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_tail_step
    hBeta hEmpty hAppend hBridge hInv hFOpBody
    (MEqRedFOpTailStepPreservesPayload.of_cons hFOpTailStep)
    hFunBody hNoTop

/-- Non-empty-tail-step variant of
`MEqRedPreservesWfMachineState.of_body_transports_and_typed_fop_tail_step`.
The induced immediate-application step at an empty residual tail is
definitionally discharged. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_typed_fop_tail_step_cons
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hFOpTailStep : MEqRedFOpTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_tail_step_cons
    hBeta hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hFOpTailStep hFunBody hNoTop

/-- Typed-operator variant of the current machine-state assembly. The
remaining non-empty `Me-FOp` tail-step is reduced to typed operator
preservation for the immediate application plus a recursive tail-step
residual. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_operator_tail_step
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hFOpTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_tail_step_cons
    hBeta hEmpty hAppend hBridge hInv hFOpBody
    (MEqRedFOpTailStepPreservesConsPayload.of_typed_operator
      hOpFun hFOpTailStep)
    hFunBody hNoTop

/-- Typed-operator variant of the current machine-state assembly. The
remaining non-empty `Me-FOp` tail-step is reduced to typed operator
preservation for the immediate application plus a recursive tail-step
residual. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_typed_fop_operator_tail_step
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hFOpTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_operator_tail_step
    hBeta hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hFOpTailStep hFunBody hNoTop

/-- Machine-state-aware operator variant of the current machine-state
assembly. This keeps the full plugged source state in the residual used to
preserve the immediate operator function supertype in recursive `Me-FOp`
tail steps. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_machine_operator_tail_step
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hFOpTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_tail_step_cons
    hBeta hEmpty hAppend hBridge hInv hFOpBody
    (MEqRedFOpTailStepPreservesConsPayload.of_machine_operator
      hOpFun hFOpTailStep)
    hFunBody hNoTop

/-- Machine-state-aware operator variant of the current machine-state
assembly. This keeps the full plugged source state in the residual used to
preserve the immediate operator function supertype in recursive `Me-FOp`
tail steps. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_typed_fop_machine_operator_tail_step
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hFOpTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_machine_operator_tail_step
    hBeta hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hFOpTailStep hFunBody hNoTop

/-- Target-application variant of the current machine-state assembly. This
keeps the recursive `Me-FOp` tail route at the exact immediate
target-application well-formedness residual plus the recursive tail-step
residual. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_target_app_tail_step
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hFOpTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_tail_step_cons
    hBeta hEmpty hAppend hBridge hInv hFOpBody
    (MEqRedFOpTailStepPreservesConsPayload.of_target_app
      hTargetApp hFOpTailStep)
    hFunBody hNoTop

/-- Target-application variant of the current machine-state assembly. This
keeps the recursive `Me-FOp` tail route at the exact immediate
target-application well-formedness residual plus the recursive tail-step
residual. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_typed_fop_target_app_tail_step
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hFOpTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_target_app_tail_step
    hBeta hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hTargetApp hFOpTailStep hFunBody hNoTop

/-- External-empty assembly with both `Me-Bet` and `Me-FOp` routed through
immediate target well-formedness plus the shared tail-step residual. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_target_app_tail_step
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_typed_fop_target_app_tail_step
    (MEqRedBetaPreservesWfMachineStatePayload.of_target_and_tail_step
      hBetaTarget hTailStep)
    hEmpty hAppend hBridge hInv hFOpBody hTargetApp hTailStep hFunBody hNoTop

/-- External-empty assembly with both `Me-Bet` and `Me-FOp` routed through
immediate target well-formedness plus the shared tail-step residual, with the
control-left residual still exposed through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_beta_target_typed_fop_target_app_tail_step
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_target_app_tail_step
    hBetaTarget hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hTargetApp hTailStep hFunBody hNoTop

/-- Typed-operator entry point for the external-empty assembly with both
`Me-Bet` and `Me-FOp` routed through immediate target well-formedness plus the
shared tail-step residual. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_operator_tail_step
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_target_app_tail_step
    hBetaTarget hEmpty hAppend hBridge hInv hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    hTailStep hFunBody hNoTop

/-- Typed-operator entry point for the external-empty assembly with both
`Me-Bet` and `Me-FOp` routed through immediate target well-formedness plus the
shared tail-step residual, with the control-left residual still exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_beta_target_typed_fop_operator_tail_step
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_operator_tail_step
    hBetaTarget hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hTailStep hFunBody hNoTop

/-- Machine-state-aware operator entry point for the external-empty assembly
with both `Me-Bet` and `Me-FOp` routed through immediate target
well-formedness plus the shared tail-step residual. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_machine_operator_tail_step
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_target_app_tail_step
    hBetaTarget hEmpty hAppend hBridge hInv hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    hTailStep hFunBody hNoTop

/-- Machine-state-aware operator entry point for the external-empty assembly
with both `Me-Bet` and `Me-FOp` routed through immediate target
well-formedness plus the shared tail-step residual, with the control-left
residual still exposed through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_beta_target_typed_fop_machine_operator_tail_step
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_machine_operator_tail_step
    hBetaTarget hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hTailStep hFunBody hNoTop

/-- Neutral machine-tail spelling of
`of_body_transports_and_beta_target_typed_fop_target_app_tail_step`. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_target_app_machine_tail
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_target_app_tail_step
    hBetaTarget hEmpty hAppend hBridge hInv hFOpBody hTargetApp
    (MEqRedFOpTailStepPreservesPayload.of_machine_tail hTail)
    hFunBody hNoTop

/-- Neutral machine-tail spelling of
`of_body_transports_and_beta_target_typed_fop_target_app_tail_step`, with the
control-left residual still exposed through the older body-transport surface.
-/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_beta_target_typed_fop_target_app_machine_tail
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_target_app_machine_tail
    hBetaTarget hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hTargetApp hTail hFunBody hNoTop

/-- Typed-operator, neutral machine-tail entry point for the external-empty
assembly with both `Me-Bet` and `Me-FOp` routed through immediate target
well-formedness. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_operator_machine_tail
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_target_app_machine_tail
    hBetaTarget hEmpty hAppend hBridge hInv hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    hTail hFunBody hNoTop

/-- Typed-operator, neutral machine-tail entry point for the external-empty
assembly with both `Me-Bet` and `Me-FOp` routed through immediate target
well-formedness, with the control-left residual still exposed through the
older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_beta_target_typed_fop_operator_machine_tail
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_operator_machine_tail
    hBetaTarget hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hTail hFunBody hNoTop

/-- Machine-state-aware operator, neutral machine-tail entry point for the
external-empty assembly with both `Me-Bet` and `Me-FOp` routed through
immediate target well-formedness. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_machine_operator_machine_tail
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_target_app_machine_tail
    hBetaTarget hEmpty hAppend hBridge hInv hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    hTail hFunBody hNoTop

/-- Machine-state-aware operator, neutral machine-tail entry point for the
external-empty assembly with both `Me-Bet` and `Me-FOp` routed through
immediate target well-formedness, with the control-left residual still
exposed through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_beta_target_typed_fop_machine_operator_machine_tail
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_machine_operator_machine_tail
    hBetaTarget hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hTail hFunBody hNoTop

/-- Non-empty-tail spelling of the strongest external-empty target-application
assembly. The empty tail case is handled by the target well-formedness
premise. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_target_app_machine_tail_cons
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_target_app_machine_tail
    hBetaTarget hEmpty hAppend hBridge hInv hFOpBody hTargetApp
    (MEqRedMachineTailStepPreservesPayload.of_cons hTailCons)
    hFunBody hNoTop

/-- Non-empty-tail spelling of the strongest external-empty target-application
assembly, with the control-left residual still exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_beta_target_typed_fop_target_app_machine_tail_cons
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_target_app_machine_tail_cons
    hBetaTarget hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hTargetApp hTailCons hFunBody hNoTop

/-- Contextual-β variant of the strongest external-empty target-application
assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_contextual_beta_typed_fop_target_app_machine_tail_cons
    (hBeta : MEqRedBetaPreservesWfMContextual)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_target_app_machine_tail_cons
    (MEqRedBetaTargetPreservesWfMPayload.of_contextual hBeta)
    hEmpty hAppend hBridge hInv hFOpBody hTargetApp hTailCons
    hFunBody hNoTop

/-- Contextual-β variant of the strongest external-empty target-application
assembly, with the control-left residual still exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_contextual_beta_typed_fop_target_app_machine_tail_cons
    (hBeta : MEqRedBetaPreservesWfMContextual)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_contextual_beta_typed_fop_target_app_machine_tail_cons
    hBeta hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hTargetApp hTailCons hFunBody hNoTop

/-- Typed-operator, non-empty-tail spelling of the strongest external-empty
assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_operator_machine_tail_cons
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_target_app_machine_tail_cons
    hBetaTarget hEmpty hAppend hBridge hInv hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_typed_operator hOpFun hTail)
    hFunBody hNoTop

/-- Typed-operator, non-empty-tail spelling of the strongest external-empty
assembly, with the control-left residual still exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_beta_target_typed_fop_operator_machine_tail_cons
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_operator_machine_tail_cons
    hBetaTarget hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hTail hFunBody hNoTop

/-- Contextual-β typed-operator, non-empty-tail spelling of the strongest
external-empty assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_contextual_beta_typed_fop_operator_machine_tail_cons
    (hBeta : MEqRedBetaPreservesWfMContextual)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_operator_machine_tail_cons
    (MEqRedBetaTargetPreservesWfMPayload.of_contextual hBeta)
    hEmpty hAppend hBridge hInv hFOpBody hOpFun hTail hFunBody hNoTop

/-- Contextual-β typed-operator, non-empty-tail spelling of the strongest
external-empty assembly, with the control-left residual still exposed through
the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_contextual_beta_typed_fop_operator_machine_tail_cons
    (hBeta : MEqRedBetaPreservesWfMContextual)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_contextual_beta_typed_fop_operator_machine_tail_cons
    hBeta hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hTail hFunBody hNoTop

/-- Machine-state-aware operator, non-empty-tail spelling of the strongest
external-empty assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_machine_operator_machine_tail_cons
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_target_app_machine_tail_cons
    hBetaTarget hEmpty hAppend hBridge hInv hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_machine_operator hOpFun hTail)
    hFunBody hNoTop

/-- Machine-state-aware operator, non-empty-tail spelling of the strongest
external-empty assembly, with the control-left residual still exposed through
the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_beta_target_typed_fop_machine_operator_machine_tail_cons
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_machine_operator_machine_tail_cons
    hBetaTarget hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hTail hFunBody hNoTop

/-- Contextual-β machine-state-aware operator, non-empty-tail spelling of the
strongest external-empty assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_contextual_beta_typed_fop_machine_operator_machine_tail_cons
    (hBeta : MEqRedBetaPreservesWfMContextual)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_machine_operator_machine_tail_cons
    (MEqRedBetaTargetPreservesWfMPayload.of_contextual hBeta)
    hEmpty hAppend hBridge hInv hFOpBody hOpFun hTail hFunBody hNoTop

/-- Contextual-β machine-state-aware operator, non-empty-tail spelling of the
strongest external-empty assembly, with the control-left residual still
exposed through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_contextual_beta_typed_fop_machine_operator_machine_tail_cons
    (hBeta : MEqRedBetaPreservesWfMContextual)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_contextual_beta_typed_fop_machine_operator_machine_tail_cons
    hBeta hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hTail hFunBody hNoTop

/-- Split-beta variant of the strongest external-empty target-application
assembly. The beta branch is reduced to beta instantiation, function-bound
inversion, body preservation under the source `.sub` head, and empty-stack
argument preservation. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_split_beta_typed_fop_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_beta_target_typed_fop_target_app_machine_tail_cons
    (MEqRedBetaTargetPreservesWfMPayload.of_body_arg_and_subst
      hSubst hInv hBetaBody hEmpty)
    hEmpty hAppend hBridge hInv hFOpBody hTargetApp hTailCons hFunBody hNoTop

/-- Split-beta variant of the strongest external-empty target-application
assembly, with the control-left residual still exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_split_beta_typed_fop_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_split_beta_typed_fop_target_app_machine_tail_cons
    hSubst hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hTargetApp hTailCons hFunBody hNoTop

/-- Split-beta, typed-operator variant of the strongest external-empty
assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_split_beta_typed_fop_operator_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_split_beta_typed_fop_target_app_machine_tail_cons
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_typed_operator hOpFun hTail)
    hFunBody hNoTop

/-- Split-beta, typed-operator variant of the strongest external-empty
assembly, with the control-left residual still exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_split_beta_typed_fop_operator_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_split_beta_typed_fop_operator_machine_tail_cons
    hSubst hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hFunBody hNoTop

/-- Split-beta, machine-state-aware operator variant of the strongest
external-empty assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_split_beta_typed_fop_machine_operator_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_split_beta_typed_fop_target_app_machine_tail_cons
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_machine_operator hOpFun hTail)
    hFunBody hNoTop

/-- Split-beta, machine-state-aware operator variant of the strongest
external-empty assembly, with the control-left residual still exposed through
the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_split_beta_typed_fop_machine_operator_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_split_beta_typed_fop_machine_operator_machine_tail_cons
    hSubst hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hFunBody hNoTop

/-- External-empty spelling of the direct split-beta target-application
assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_split_beta_typed_fop_target_app_machine_tail_cons
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hTargetApp
    hTailCons hFunBody hNoTop

/-- External-empty spelling of the direct split-beta target-application
assembly, with stack append exposed through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons
    hSubst hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hTargetApp hTailCons hFunBody hNoTop

/-- External-empty, typed-operator spelling of the direct split-beta assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_typed_operator hOpFun hTail)
    hFunBody hNoTop

/-- External-empty, typed-operator spelling of the direct split-beta assembly,
with stack append exposed through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_operator_machine_tail
    hSubst hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hFunBody hNoTop

/-- External-empty, machine-state-aware operator spelling of the direct
split-beta assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_machine_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_machine_operator hOpFun hTail)
    hFunBody hNoTop

/-- External-empty, machine-state-aware operator spelling of the direct
split-beta assembly, with stack append exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_machine_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_machine_operator_machine_tail
    hSubst hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hFunBody hNoTop

/-- External-empty native-`FOp`-body spelling of the direct split-beta
target-application assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons
    hSubst hEmpty hAppend hBridge hInv hBetaBody
    (MEqRedFOpBodyTypedPayload.of_untyped hFOpBody) hTargetApp hTailCons
    hFunBody hNoTop

/-- External-empty native-`FOp`-body spelling of the direct split-beta
target-application assembly, with stack append exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_target_app_machine_tail_cons
    hSubst hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hTargetApp hTailCons hFunBody hNoTop

/-- External-empty typed-operator entry point for the native-`FOp`-body direct
split-beta assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_target_app_machine_tail_cons
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_typed_operator hOpFun hTail)
    hFunBody hNoTop

/-- External-empty typed-operator entry point for the native-`FOp`-body direct
split-beta assembly, with stack append exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_operator_machine_tail
    hSubst hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hFunBody hNoTop

/-- External-empty machine-state-aware operator entry point for the
native-`FOp`-body direct split-beta assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_machine_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_target_app_machine_tail_cons
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_machine_operator hOpFun hTail)
    hFunBody hNoTop

/-- External-empty machine-state-aware operator entry point for the
native-`FOp`-body direct split-beta assembly, with stack append exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_machine_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_machine_operator_machine_tail
    hSubst hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hFunBody hNoTop

/-- Reduced machine-state preservation assembly that uses constructor
recursive hypotheses directly for the empty-stack subreductions in `Me-App`
and `Me-Fun`. This removes the external empty-stack preservation premise
from the main machine-state assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_reduced_components_no_empty
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hStack : WSubMStarToStackedMSubStarPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt)
    (hFOp : MEqRedFOpPreservesWfMachineStatePayload) :
    MEqRedPreservesWfMachineState := by
  intro Γ s x y hΓ hred hState
  revert hΓ hState
  induction hred with
  | pro hpv hb hred ih =>
      intro hΓ hState
      have hControl : WfMachineStateControlLeftPayload :=
        WfMachineStateControlLeftPayload.of_app_operator
          (WSubMStarAppOperatorPayload.of_stacked_msubstar_bridge
            hStack hBridge)
      exact ih hΓ
        (MEqRedProAnnotationMachineStatePayload.of_control_left
          hControl hΓ hb hState)
  | bet ht hBody hArg _ihBody _ihArg =>
      intro hΓ hState
      exact hBeta hΓ ht hBody hArg hState
  | top hpv =>
      intro hΓ hState
      exact hState
  | @app Γapp sapp u u' v v' hOp hArg ihOp ihArg =>
      intro hΓ hState
      have hOpState : WfMachineState Γapp u (v :: sapp) := by
        simpa [WfMachineState, Stack.plug] using hState
      have hOpState' : WfMachineState Γapp u' (v :: sapp) :=
        ihOp hΓ hOpState
      have hApp : WfM Γapp (.app u' v) :=
        WfMachineState.head_app_wf hOpState'
      obtain ⟨bound, hFun, hArgSub⟩ := hApp.app_inv
      have hwfV : WfM Γapp v := hArgSub.wf_left
      have hVState : WfMachineState Γapp v [] := by
        simpa [WfMachineState, Stack.plug] using hwfV
      have hVState' : WfMachineState Γapp v' [] := ihArg hΓ hVState
      have hwfV' : WfM Γapp v' := by
        simpa [WfMachineState, Stack.plug] using hVState'
      have hArgBack : WSubMStar Γapp v' v :=
        WSubMStar.of_MEqRed_back hArg hwfV hwfV'
      have hArg' : WSubMStar Γapp v' bound :=
        WSubMStar.trans hwfV hArgBack hArgSub
      have hApp' : WfM Γapp (.app u' v') := WfM.app hFun hArg'
      have hpvStack : PrevalidExt Γapp [v] :=
        PrevalidExt.cons (PrevalidExt.nil hwfV.prevalid) hwfV.scoped
      have hOpRefl : MEqRed Γapp [v] u' u' :=
        MEqRed.refl hpvStack hFun.wf_left.scoped
      have hAppRed : MEqRed Γapp [] (.app u' v) (.app u' v') :=
        MEqRed.app hOpRefl hArg
      have hControlBack : WSubMStar Γapp (.app u' v') (.app u' v) :=
        WSubMStar.of_MEqRed_back hAppRed hApp hApp'
      have hControl : WfMachineStateControlLeftPayload :=
        WfMachineStateControlLeftPayload.of_app_operator
          (WSubMStarAppOperatorPayload.of_stacked_msubstar_bridge
            hStack hBridge)
      have hTail' : WfMachineState Γapp (.app u' v') sapp :=
        hControl hControlBack (WfMachineState.tail_state hOpState')
      simpa [WfMachineState, Stack.plug] using hTail'
  | var hpv hi =>
      intro hΓ hState
      exact hState
  | @fun_ Γfun bound bound' body body' hBound hBody ihBound ihBody =>
      intro hΓ hState
      have hwfAbs : WfM Γfun (.abs bound body) := by
        simpa [WfMachineState, Stack.plug] using hState
      have hwfBound : WfM Γfun bound := hwfAbs.fun_inv.1
      have hwfBody : WfM ({ bound := bound, kind := .sub } :: Γfun) body :=
        hwfAbs.fun_inv.2
      have hBoundState : WfMachineState Γfun bound [] := by
        simpa [WfMachineState, Stack.plug] using hwfBound
      have hBoundState' : WfMachineState Γfun bound' [] :=
        ihBound hΓ hBoundState
      have hwfBound' : WfM Γfun bound' := by
        simpa [WfMachineState, Stack.plug] using hBoundState'
      have hΓBody : WfCtxEqu ({ bound := bound, kind := .sub } :: Γfun) :=
        WfCtxEqu.sub hΓ
      have hBodyState : WfMachineState
          ({ bound := bound, kind := .sub } :: Γfun) body [] := by
        simpa [WfMachineState, Stack.plug] using hwfBody
      have hBodyState' : WfMachineState
          ({ bound := bound, kind := .sub } :: Γfun) body' [] :=
        ihBody hΓBody hBodyState
      have hwfBody'Old :
          WfM ({ bound := bound, kind := .sub } :: Γfun) body' := by
        simpa [WfMachineState, Stack.plug] using hBodyState'
      have hwfTarget : WfM Γfun (.abs bound' body') :=
        WfM.fun_ hwfBound'
          (hFunBody hΓ hwfBound hwfBound' hBound hwfBody'Old)
      simpa [WfMachineState, Stack.plug] using hwfTarget
  | tAp hpv hu =>
      intro hΓ hState
      exact MEqRedTApPreservesWfMachineStatePayload.of_no_top
        hNoTop hΓ hu hState
  | fOp hBound hOperand hBody _ihBound _ihBody =>
      intro hΓ hState
      exact hFOp hΓ hBound hOperand hBody hState

/-- Append-native no-external-empty machine-state assembly: expose the
generalized diagrammatic stack-append payload directly and specialize it to
the stacked-diagrammatic bridge used by the recursive constructor proof. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt)
    (hFOp : MEqRedFOpPreservesWfMachineStatePayload) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_reduced_components_no_empty
    hBeta
    (WSubMStarToStackedMSubStarPayload.of_msubstar_stack_append hAppend)
    hBridge hFunBody hNoTop hFOp

/-- Reduced machine-state preservation assembled directly from the
body-transport residuals for stack lifting and the one-step diagrammatic
re-embedding components. This is the current most decomposed assembly for the
control/app-operator side of machine preservation. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt)
    (hFOp : MEqRedFOpPreservesWfMachineStatePayload) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty
    hBeta
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hFunBody hNoTop hFOp

/-- Control-left-parametric no-external-empty variant of the typed
target-application `Me-FOp` machine-state assembly. The recursive induction
handles the `Me-FOp` bound step at the empty stack; the remaining non-empty
tail is still exposed as the target-application tail-step residual. -/
noncomputable def MEqRedPreservesWfMachineState.of_control_left_no_empty_and_typed_fop_target_app_tail_step
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hControl : WfMachineStateControlLeftPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hFOpTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState := by
  intro Γ s x y hΓ hred hState
  revert hΓ hState
  induction hred with
  | pro hpv hb hred ih =>
      intro hΓ hState
      exact ih hΓ
        (MEqRedProAnnotationMachineStatePayload.of_control_left
          hControl hΓ hb hState)
  | bet ht hBody hArg _ihBody _ihArg =>
      intro hΓ hState
      exact hBeta hΓ ht hBody hArg hState
  | top hpv =>
      intro hΓ hState
      exact hState
  | @app Γapp sapp u u' v v' hOp hArg ihOp ihArg =>
      intro hΓ hState
      have hOpState : WfMachineState Γapp u (v :: sapp) := by
        simpa [WfMachineState, Stack.plug] using hState
      have hOpState' : WfMachineState Γapp u' (v :: sapp) :=
        ihOp hΓ hOpState
      have hApp : WfM Γapp (.app u' v) :=
        WfMachineState.head_app_wf hOpState'
      obtain ⟨bound, hFun, hArgSub⟩ := hApp.app_inv
      have hwfV : WfM Γapp v := hArgSub.wf_left
      have hVState : WfMachineState Γapp v [] := by
        simpa [WfMachineState, Stack.plug] using hwfV
      have hVState' : WfMachineState Γapp v' [] := ihArg hΓ hVState
      have hwfV' : WfM Γapp v' := by
        simpa [WfMachineState, Stack.plug] using hVState'
      have hArgBack : WSubMStar Γapp v' v :=
        WSubMStar.of_MEqRed_back hArg hwfV hwfV'
      have hArg' : WSubMStar Γapp v' bound :=
        WSubMStar.trans hwfV hArgBack hArgSub
      have hApp' : WfM Γapp (.app u' v') := WfM.app hFun hArg'
      have hpvStack : PrevalidExt Γapp [v] :=
        PrevalidExt.cons (PrevalidExt.nil hwfV.prevalid) hwfV.scoped
      have hOpRefl : MEqRed Γapp [v] u' u' :=
        MEqRed.refl hpvStack hFun.wf_left.scoped
      have hAppRed : MEqRed Γapp [] (.app u' v) (.app u' v') :=
        MEqRed.app hOpRefl hArg
      have hControlBack : WSubMStar Γapp (.app u' v') (.app u' v) :=
        WSubMStar.of_MEqRed_back hAppRed hApp hApp'
      have hTail' : WfMachineState Γapp (.app u' v') sapp :=
        hControl hControlBack (WfMachineState.tail_state hOpState')
      simpa [WfMachineState, Stack.plug] using hTail'
  | var hpv hi =>
      intro hΓ hState
      exact hState
  | @fun_ Γfun bound bound' body body' hBound hBody ihBound ihBody =>
      intro hΓ hState
      have hwfAbs : WfM Γfun (.abs bound body) := by
        simpa [WfMachineState, Stack.plug] using hState
      have hwfBound : WfM Γfun bound := hwfAbs.fun_inv.1
      have hwfBody : WfM ({ bound := bound, kind := .sub } :: Γfun) body :=
        hwfAbs.fun_inv.2
      have hBoundState : WfMachineState Γfun bound [] := by
        simpa [WfMachineState, Stack.plug] using hwfBound
      have hBoundState' : WfMachineState Γfun bound' [] :=
        ihBound hΓ hBoundState
      have hwfBound' : WfM Γfun bound' := by
        simpa [WfMachineState, Stack.plug] using hBoundState'
      have hΓBody : WfCtxEqu ({ bound := bound, kind := .sub } :: Γfun) :=
        WfCtxEqu.sub hΓ
      have hBodyState : WfMachineState
          ({ bound := bound, kind := .sub } :: Γfun) body [] := by
        simpa [WfMachineState, Stack.plug] using hwfBody
      have hBodyState' : WfMachineState
          ({ bound := bound, kind := .sub } :: Γfun) body' [] :=
        ihBody hΓBody hBodyState
      have hwfBody'Old :
          WfM ({ bound := bound, kind := .sub } :: Γfun) body' := by
        simpa [WfMachineState, Stack.plug] using hBodyState'
      have hwfTarget : WfM Γfun (.abs bound' body') :=
        WfM.fun_ hwfBound'
          (hFunBody hΓ hwfBound hwfBound' hBound hwfBody'Old)
      simpa [WfMachineState, Stack.plug] using hwfTarget
  | tAp hpv hu =>
      intro hΓ hState
      exact MEqRedTApPreservesWfMachineStatePayload.of_no_top
        hNoTop hΓ hu hState
  | @fOp Γfop sfop bound bound' operand body body'
      hBound hOperandScoped hBodyRed ihBound _ihBody =>
      intro hΓ hState
      have hStack : WfStack Γfop (operand :: sfop) :=
        WfMachineState.stack_wf hState
      have hStackTail : WfStack Γfop sfop := WfStack.tail hStack
      have hwfAbs : WfM Γfop (.abs bound body) :=
        WfMachineState.control_wf hState
      have hwfBound : WfM Γfop bound := hwfAbs.fun_inv.1
      have hwfBody : WfM ({ bound := bound, kind := .sub } :: Γfop) body :=
        hwfAbs.fun_inv.2
      have hOperandBound : WSubMStar Γfop operand bound :=
        WfMachineState.fop_operand_bound hInv hΓ hState
      have hBoundState : WfMachineState Γfop bound [] := by
        simpa [WfMachineState, Stack.plug] using hwfBound
      have hBoundState' : WfMachineState Γfop bound' [] :=
        ihBound hΓ hBoundState
      have hwfBound' : WfM Γfop bound' := by
        simpa [WfMachineState, Stack.plug] using hBoundState'
      have hwfBody' :
          WfM ({ bound := bound', kind := .sub } :: Γfop) body' :=
        hFOpBody hΓ hStackTail hwfBound hwfBound' hOperandBound hwfBody
          hBound hBodyRed
      have hwfAbs' : WfM Γfop (.abs bound' body') :=
        WfM.fun_ hwfBound' hwfBody'
      have hBoundSubBound' : WSubMStar Γfop bound bound' :=
        WSubMStar.of_MEqRed_fwd hBound hwfBound hwfBound'
      have hOperandBound' : WSubMStar Γfop operand bound' :=
        WSubMStar.trans hwfBound hOperandBound hBoundSubBound'
      have hwfAbsTop' : WfM Γfop (.abs bound' .top) :=
        WfM.fun_ hwfBound'
          (WfM.top (Prevalid.sub hwfBound'.prevalid hwfBound'.scoped))
      have hBodyTop :
          MSubRed ({ bound := bound', kind := .sub } :: Γfop) [] body' .top :=
        MSubRed.top (PrevalidExt.nil hwfBody'.prevalid) hwfBody'.scoped
      have hBoundRefl : MEqRed Γfop [] bound' bound' :=
        MEqRed.refl (PrevalidExt.nil hwfBound'.prevalid) hwfBound'.scoped
      have hAbsSubTop :
          MSubRed Γfop [] (.abs bound' body') (.abs bound' .top) :=
        MSubRed.fun_ hwfBound'.scoped hBoundRefl hBodyTop
      have hFunTarget : WSubMStar Γfop (.abs bound' body') (.abs bound' .top) :=
        WSubMStar.of_MSubRed_fwd hAbsSubTop hwfAbs' hwfAbsTop'
      have hAppTarget : WfM Γfop (.app (.abs bound' body') operand) :=
        WfM.app hFunTarget hOperandBound'
      cases sfop with
      | nil =>
          simpa [WfMachineState, Stack.plug] using hAppTarget
      | cons next tail =>
          exact
            (MEqRedFOpTailStepPreservesConsPayload.of_target_app
              hTargetApp hFOpTailStep)
              hΓ (MEqRed.fOp hBound hOperandScoped hBodyRed)
              hwfAbs' hState

/-- Append-native no-external-empty variant of the typed target-application
`Me-FOp` machine-state assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_typed_fop_target_app_tail_step
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hFOpTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_control_left_no_empty_and_typed_fop_target_app_tail_step
    hBeta
    (WfMachineStateControlLeftPayload.of_msubstar_stack_append
      hAppend hBridge)
    hInv hFOpBody hTargetApp hFOpTailStep hFunBody hNoTop

/-- No-external-empty variant of the typed target-application `Me-FOp`
machine-state assembly, with the control-left residual still exposed through
the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_typed_fop_target_app_tail_step
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hFOpTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_typed_fop_target_app_tail_step
    hBeta
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hTargetApp hFOpTailStep hFunBody hNoTop

/-- No-external-empty typed-operator variant of the `Me-FOp` route. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_typed_fop_operator_tail_step
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hFOpTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_typed_fop_target_app_tail_step
    hBeta hAppend hBridge hInv hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    hFOpTailStep hFunBody hNoTop

/-- No-external-empty typed-operator variant of the `Me-FOp` route, with the
control-left residual still exposed through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_typed_fop_operator_tail_step
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hFOpTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_typed_fop_operator_tail_step
    hBeta
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hFOpTailStep hFunBody hNoTop

/-- No-external-empty machine-state-aware operator variant of the `Me-FOp`
route. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_typed_fop_machine_operator_tail_step
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hFOpTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_typed_fop_target_app_tail_step
    hBeta hAppend hBridge hInv hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    hFOpTailStep hFunBody hNoTop

/-- No-external-empty machine-state-aware operator variant of the `Me-FOp`
route, with the control-left residual still exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_typed_fop_machine_operator_tail_step
    (hBeta : MEqRedBetaPreservesWfMachineStatePayload)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hFOpTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_typed_fop_machine_operator_tail_step
    hBeta
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hFOpTailStep hFunBody hNoTop

/-- No-external-empty assembly with both `Me-Bet` and `Me-FOp` routed through
immediate target well-formedness plus the shared tail-step residual. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_target_app_tail_step
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_typed_fop_target_app_tail_step
    (MEqRedBetaPreservesWfMachineStatePayload.of_target_and_tail_step
      hBetaTarget hTailStep)
    hAppend hBridge hInv hFOpBody hTargetApp hTailStep hFunBody hNoTop

/-- No-external-empty assembly with both `Me-Bet` and `Me-FOp` routed through
immediate target well-formedness plus the shared tail-step residual, with the
control-left residual still exposed through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_beta_target_typed_fop_target_app_tail_step
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_target_app_tail_step
    hBetaTarget
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hTargetApp hTailStep hFunBody hNoTop

/-- Typed-operator entry point for the no-external-empty assembly with both
`Me-Bet` and `Me-FOp` routed through immediate target well-formedness plus the
shared tail-step residual. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_operator_tail_step
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_target_app_tail_step
    hBetaTarget hAppend hBridge hInv hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    hTailStep hFunBody hNoTop

/-- Typed-operator entry point for the no-external-empty assembly with both
`Me-Bet` and `Me-FOp` routed through immediate target well-formedness plus the
shared tail-step residual, with the control-left residual still exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_beta_target_typed_fop_operator_tail_step
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_operator_tail_step
    hBetaTarget
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hTailStep hFunBody hNoTop

/-- Machine-state-aware operator entry point for the no-external-empty
assembly with both `Me-Bet` and `Me-FOp` routed through immediate target
well-formedness plus the shared tail-step residual. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_machine_operator_tail_step
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_target_app_tail_step
    hBetaTarget hAppend hBridge hInv hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    hTailStep hFunBody hNoTop

/-- Machine-state-aware operator entry point for the no-external-empty
assembly with both `Me-Bet` and `Me-FOp` routed through immediate target
well-formedness plus the shared tail-step residual, with the control-left
residual still exposed through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_beta_target_typed_fop_machine_operator_tail_step
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTailStep : MEqRedFOpTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_machine_operator_tail_step
    hBetaTarget
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hTailStep hFunBody hNoTop

/-- Neutral machine-tail spelling of
`of_body_transports_no_empty_and_beta_target_typed_fop_target_app_tail_step`.
-/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_target_app_machine_tail
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_target_app_tail_step
    hBetaTarget hAppend hBridge hInv hFOpBody hTargetApp
    (MEqRedFOpTailStepPreservesPayload.of_machine_tail hTail)
    hFunBody hNoTop

/-- Neutral machine-tail spelling of
`of_body_transports_no_empty_and_beta_target_typed_fop_target_app_tail_step`,
with the control-left residual still exposed through the older body-transport
surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_beta_target_typed_fop_target_app_machine_tail
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_target_app_machine_tail
    hBetaTarget
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hTargetApp hTail hFunBody hNoTop

/-- Typed-operator, neutral machine-tail entry point for the no-external-empty
assembly with both `Me-Bet` and `Me-FOp` routed through immediate target
well-formedness. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_operator_machine_tail
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_target_app_machine_tail
    hBetaTarget hAppend hBridge hInv hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    hTail hFunBody hNoTop

/-- Typed-operator, neutral machine-tail entry point for the no-external-empty
assembly with both `Me-Bet` and `Me-FOp` routed through immediate target
well-formedness, with the control-left residual still exposed through the
older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_beta_target_typed_fop_operator_machine_tail
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_operator_machine_tail
    hBetaTarget
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hTail hFunBody hNoTop

/-- Machine-state-aware operator, neutral machine-tail entry point for the
no-external-empty assembly with both `Me-Bet` and `Me-FOp` routed through
immediate target well-formedness. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_machine_operator_machine_tail
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_target_app_machine_tail
    hBetaTarget hAppend hBridge hInv hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    hTail hFunBody hNoTop

/-- Machine-state-aware operator, neutral machine-tail entry point for the
no-external-empty assembly with both `Me-Bet` and `Me-FOp` routed through
immediate target well-formedness, with the control-left residual still exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_beta_target_typed_fop_machine_operator_machine_tail
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_machine_operator_machine_tail
    hBetaTarget
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hTail hFunBody hNoTop

/-- Non-empty-tail spelling of the strongest no-external-empty
target-application assembly. The empty tail case is definitional from the
immediate target well-formedness premise. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_target_app_machine_tail_cons
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_target_app_machine_tail
    hBetaTarget hAppend hBridge hInv hFOpBody hTargetApp
    (MEqRedMachineTailStepPreservesPayload.of_cons hTailCons)
    hFunBody hNoTop

/-- Non-empty-tail spelling of the strongest no-external-empty
target-application assembly, with the control-left residual still exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_beta_target_typed_fop_target_app_machine_tail_cons
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_target_app_machine_tail_cons
    hBetaTarget
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hTargetApp hTailCons hFunBody hNoTop

/-- Contextual-β variant of the strongest no-external-empty
target-application assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_contextual_beta_typed_fop_target_app_machine_tail_cons
    (hBeta : MEqRedBetaPreservesWfMContextual)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_target_app_machine_tail_cons
    (MEqRedBetaTargetPreservesWfMPayload.of_contextual hBeta)
    hAppend hBridge hInv hFOpBody hTargetApp hTailCons hFunBody hNoTop

/-- Contextual-β variant of the strongest no-external-empty target-application
assembly, with the control-left residual still exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_contextual_beta_typed_fop_target_app_machine_tail_cons
    (hBeta : MEqRedBetaPreservesWfMContextual)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_contextual_beta_typed_fop_target_app_machine_tail_cons
    hBeta
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hTargetApp hTailCons hFunBody hNoTop

/-- Typed-operator, non-empty-tail spelling of the strongest
no-external-empty assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_operator_machine_tail_cons
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_target_app_machine_tail_cons
    hBetaTarget hAppend hBridge hInv hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_typed_operator hOpFun hTail)
    hFunBody hNoTop

/-- Typed-operator, non-empty-tail spelling of the strongest no-external-empty
assembly, with the control-left residual still exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_beta_target_typed_fop_operator_machine_tail_cons
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_operator_machine_tail_cons
    hBetaTarget
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hTail hFunBody hNoTop

/-- Contextual-β, typed-operator, non-empty-tail spelling of the strongest
no-external-empty assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_contextual_beta_typed_fop_operator_machine_tail_cons
    (hBeta : MEqRedBetaPreservesWfMContextual)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_operator_machine_tail_cons
    (MEqRedBetaTargetPreservesWfMPayload.of_contextual hBeta)
    hAppend hBridge hInv hFOpBody hOpFun hTail hFunBody hNoTop

/-- Contextual-β, typed-operator, non-empty-tail spelling of the strongest
no-external-empty assembly, with the control-left residual still exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_contextual_beta_typed_fop_operator_machine_tail_cons
    (hBeta : MEqRedBetaPreservesWfMContextual)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_contextual_beta_typed_fop_operator_machine_tail_cons
    hBeta
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hTail hFunBody hNoTop

/-- Machine-state-aware operator, non-empty-tail spelling of the strongest
no-external-empty assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_machine_operator_machine_tail_cons
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_target_app_machine_tail_cons
    hBetaTarget hAppend hBridge hInv hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_machine_operator hOpFun hTail)
    hFunBody hNoTop

/-- Machine-state-aware operator, non-empty-tail spelling of the strongest
no-external-empty assembly, with the control-left residual still exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_beta_target_typed_fop_machine_operator_machine_tail_cons
    (hBetaTarget : MEqRedBetaTargetPreservesWfMPayload)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_machine_operator_machine_tail_cons
    hBetaTarget
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hTail hFunBody hNoTop

/-- Contextual-β, machine-state-aware operator, non-empty-tail spelling of
the strongest no-external-empty assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_contextual_beta_typed_fop_machine_operator_machine_tail_cons
    (hBeta : MEqRedBetaPreservesWfMContextual)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_machine_operator_machine_tail_cons
    (MEqRedBetaTargetPreservesWfMPayload.of_contextual hBeta)
    hAppend hBridge hInv hFOpBody hOpFun hTail hFunBody hNoTop

/-- Contextual-β, machine-state-aware operator, non-empty-tail spelling of
the strongest no-external-empty assembly, with the control-left residual still
exposed through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_contextual_beta_typed_fop_machine_operator_machine_tail_cons
    (hBeta : MEqRedBetaPreservesWfMContextual)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_contextual_beta_typed_fop_machine_operator_machine_tail_cons
    hBeta
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hFOpBody hOpFun hTail hFunBody hNoTop

/-- Split-beta variant of the strongest no-external-empty target-application
assembly. The beta branch is reduced to beta instantiation, function-bound
inversion, body preservation under the source `.sub` head, and empty-stack
argument preservation. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_split_beta_typed_fop_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_beta_target_typed_fop_target_app_machine_tail_cons
    (MEqRedBetaTargetPreservesWfMPayload.of_body_arg_and_subst
      hSubst hInv hBetaBody hEmpty)
    hAppend hBridge hInv hFOpBody hTargetApp hTailCons hFunBody hNoTop

/-- Split-beta variant of the strongest no-external-empty target-application
assembly, with the control-left residual still exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_split_beta_typed_fop_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_split_beta_typed_fop_target_app_machine_tail_cons
    hSubst hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hTargetApp hTailCons hFunBody hNoTop

/-- Split-beta, typed-operator variant of the strongest no-external-empty
assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_split_beta_typed_fop_operator_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_split_beta_typed_fop_target_app_machine_tail_cons
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_typed_operator hOpFun hTail)
    hFunBody hNoTop

/-- Split-beta, typed-operator variant of the strongest no-external-empty
assembly, with the control-left residual still exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_split_beta_typed_fop_operator_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_split_beta_typed_fop_operator_machine_tail_cons
    hSubst hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hFunBody hNoTop

/-- Split-beta, machine-state-aware operator variant of the strongest
no-external-empty assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_split_beta_typed_fop_machine_operator_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_split_beta_typed_fop_target_app_machine_tail_cons
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_machine_operator hOpFun hTail)
    hFunBody hNoTop

/-- Split-beta, machine-state-aware operator variant of the strongest
no-external-empty assembly, with the control-left residual still exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_split_beta_typed_fop_machine_operator_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_split_beta_typed_fop_machine_operator_machine_tail_cons
    hSubst hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hFunBody hNoTop

/-- Control-left-parametric no-external-empty split-beta assembly. The
`Me-Bet` branch uses the constructor induction hypothesis for the empty-stack
argument reduction instead of requiring an external empty-stack preservation
premise. -/
noncomputable def MEqRedPreservesWfMachineState.of_control_left_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hControl : WfMachineStateControlLeftPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState := by
  intro Γ s x y hΓ hred hState
  revert hΓ hState
  induction hred with
  | pro hpv hb hred ih =>
      intro hΓ hState
      exact ih hΓ
        (MEqRedProAnnotationMachineStatePayload.of_control_left
          hControl hΓ hb hState)
  | @bet Γβ sβ bound arg arg' body body' ht hBody hArg _ihBody ihArg =>
      intro hΓ hState
      have hStack : WfStack Γβ sβ := WfMachineState.stack_wf hState
      have hwfSource : WfM Γβ (.app (.abs bound body) arg) :=
        WfMachineState.control_wf hState
      obtain ⟨result, hFun, hArgTyping⟩ := hwfSource.app_inv
      have hwfAbs : WfM Γβ (.abs bound body) := hFun.wf_left
      have hwfBound : WfM Γβ bound := hwfAbs.fun_inv.1
      have hwfBody : WfM ({ bound := bound, kind := .sub } :: Γβ) body :=
        hwfAbs.fun_inv.2
      have hwfBody' :
          WfM ({ bound := bound, kind := .sub } :: Γβ) body' :=
        hBetaBody hΓ hStack hwfBound hBody hwfBody
      have hwfArg : WfM Γβ arg := hArgTyping.wf_left
      have hArgState : WfMachineState Γβ arg [] := by
        simpa [WfMachineState, Stack.plug] using hwfArg
      have hArgState' : WfMachineState Γβ arg' [] := ihArg hΓ hArgState
      have hwfArg' : WfM Γβ arg' := by
        simpa [WfMachineState, Stack.plug] using hArgState'
      have hArgBack : WSubMStar Γβ arg' arg :=
        WSubMStar.of_MEqRed_back hArg hwfArg hwfArg'
      have hArgResult : WSubMStar Γβ arg' result :=
        WSubMStar.trans hwfArg hArgBack hArgTyping
      have hEquBoundResult : WEquMStar Γβ bound result := hInv hΓ hFun
      have hSubResultBound : WSubMStar Γβ result bound :=
        hEquBoundResult.symm.toWSubMStar
      have hArgBound : WSubMStar Γβ arg' bound :=
        WSubMStar.trans hArgTyping.wf_right hArgResult hSubResultBound
      have hwfTarget : WfM Γβ (Term.instantiate 0 arg' body') :=
        hSubst hArgBound hwfBody'
      exact (MEqRedMachineTailStepPreservesPayload.of_cons hTailCons)
        hΓ (MEqRed.bet ht hBody hArg) hwfTarget hState
  | top hpv =>
      intro hΓ hState
      exact hState
  | @app Γapp sapp u u' v v' hOp hArg ihOp ihArg =>
      intro hΓ hState
      have hOpState : WfMachineState Γapp u (v :: sapp) := by
        simpa [WfMachineState, Stack.plug] using hState
      have hOpState' : WfMachineState Γapp u' (v :: sapp) :=
        ihOp hΓ hOpState
      have hApp : WfM Γapp (.app u' v) :=
        WfMachineState.head_app_wf hOpState'
      obtain ⟨bound, hFun, hArgSub⟩ := hApp.app_inv
      have hwfV : WfM Γapp v := hArgSub.wf_left
      have hVState : WfMachineState Γapp v [] := by
        simpa [WfMachineState, Stack.plug] using hwfV
      have hVState' : WfMachineState Γapp v' [] := ihArg hΓ hVState
      have hwfV' : WfM Γapp v' := by
        simpa [WfMachineState, Stack.plug] using hVState'
      have hArgBack : WSubMStar Γapp v' v :=
        WSubMStar.of_MEqRed_back hArg hwfV hwfV'
      have hArg' : WSubMStar Γapp v' bound :=
        WSubMStar.trans hwfV hArgBack hArgSub
      have hApp' : WfM Γapp (.app u' v') := WfM.app hFun hArg'
      have hpvStack : PrevalidExt Γapp [v] :=
        PrevalidExt.cons (PrevalidExt.nil hwfV.prevalid) hwfV.scoped
      have hOpRefl : MEqRed Γapp [v] u' u' :=
        MEqRed.refl hpvStack hFun.wf_left.scoped
      have hAppRed : MEqRed Γapp [] (.app u' v) (.app u' v') :=
        MEqRed.app hOpRefl hArg
      have hControlBack : WSubMStar Γapp (.app u' v') (.app u' v) :=
        WSubMStar.of_MEqRed_back hAppRed hApp hApp'
      have hTail' : WfMachineState Γapp (.app u' v') sapp :=
        hControl hControlBack (WfMachineState.tail_state hOpState')
      simpa [WfMachineState, Stack.plug] using hTail'
  | var hpv hi =>
      intro hΓ hState
      exact hState
  | @fun_ Γfun bound bound' body body' hBound hBody ihBound ihBody =>
      intro hΓ hState
      have hwfAbs : WfM Γfun (.abs bound body) := by
        simpa [WfMachineState, Stack.plug] using hState
      have hwfBound : WfM Γfun bound := hwfAbs.fun_inv.1
      have hwfBody : WfM ({ bound := bound, kind := .sub } :: Γfun) body :=
        hwfAbs.fun_inv.2
      have hBoundState : WfMachineState Γfun bound [] := by
        simpa [WfMachineState, Stack.plug] using hwfBound
      have hBoundState' : WfMachineState Γfun bound' [] :=
        ihBound hΓ hBoundState
      have hwfBound' : WfM Γfun bound' := by
        simpa [WfMachineState, Stack.plug] using hBoundState'
      have hΓBody : WfCtxEqu ({ bound := bound, kind := .sub } :: Γfun) :=
        WfCtxEqu.sub hΓ
      have hBodyState : WfMachineState
          ({ bound := bound, kind := .sub } :: Γfun) body [] := by
        simpa [WfMachineState, Stack.plug] using hwfBody
      have hBodyState' : WfMachineState
          ({ bound := bound, kind := .sub } :: Γfun) body' [] :=
        ihBody hΓBody hBodyState
      have hwfBody'Old :
          WfM ({ bound := bound, kind := .sub } :: Γfun) body' := by
        simpa [WfMachineState, Stack.plug] using hBodyState'
      have hwfTarget : WfM Γfun (.abs bound' body') :=
        WfM.fun_ hwfBound'
          (hFunBody hΓ hwfBound hwfBound' hBound hwfBody'Old)
      simpa [WfMachineState, Stack.plug] using hwfTarget
  | tAp hpv hu =>
      intro hΓ hState
      exact MEqRedTApPreservesWfMachineStatePayload.of_no_top
        hNoTop hΓ hu hState
  | @fOp Γfop sfop bound bound' operand body body'
      hBound hOperandScoped hBodyRed ihBound _ihBody =>
      intro hΓ hState
      have hStack : WfStack Γfop (operand :: sfop) :=
        WfMachineState.stack_wf hState
      have hStackTail : WfStack Γfop sfop := WfStack.tail hStack
      have hwfAbs : WfM Γfop (.abs bound body) :=
        WfMachineState.control_wf hState
      have hwfBound : WfM Γfop bound := hwfAbs.fun_inv.1
      have hwfBody : WfM ({ bound := bound, kind := .sub } :: Γfop) body :=
        hwfAbs.fun_inv.2
      have hOperandBound : WSubMStar Γfop operand bound :=
        WfMachineState.fop_operand_bound hInv hΓ hState
      have hBoundState : WfMachineState Γfop bound [] := by
        simpa [WfMachineState, Stack.plug] using hwfBound
      have hBoundState' : WfMachineState Γfop bound' [] :=
        ihBound hΓ hBoundState
      have hwfBound' : WfM Γfop bound' := by
        simpa [WfMachineState, Stack.plug] using hBoundState'
      have hwfBody' :
          WfM ({ bound := bound', kind := .sub } :: Γfop) body' :=
        hFOpBody hΓ hStackTail hwfBound hwfBound' hOperandBound hwfBody
          hBound hBodyRed
      have hwfAbs' : WfM Γfop (.abs bound' body') :=
        WfM.fun_ hwfBound' hwfBody'
      have hBoundSubBound' : WSubMStar Γfop bound bound' :=
        WSubMStar.of_MEqRed_fwd hBound hwfBound hwfBound'
      have hOperandBound' : WSubMStar Γfop operand bound' :=
        WSubMStar.trans hwfBound hOperandBound hBoundSubBound'
      have hwfAbsTop' : WfM Γfop (.abs bound' .top) :=
        WfM.fun_ hwfBound'
          (WfM.top (Prevalid.sub hwfBound'.prevalid hwfBound'.scoped))
      have hBodyTop :
          MSubRed ({ bound := bound', kind := .sub } :: Γfop) [] body' .top :=
        MSubRed.top (PrevalidExt.nil hwfBody'.prevalid) hwfBody'.scoped
      have hBoundRefl : MEqRed Γfop [] bound' bound' :=
        MEqRed.refl (PrevalidExt.nil hwfBound'.prevalid) hwfBound'.scoped
      have hAbsSubTop :
          MSubRed Γfop [] (.abs bound' body') (.abs bound' .top) :=
        MSubRed.fun_ hwfBound'.scoped hBoundRefl hBodyTop
      have hFunTarget : WSubMStar Γfop (.abs bound' body') (.abs bound' .top) :=
        WSubMStar.of_MSubRed_fwd hAbsSubTop hwfAbs' hwfAbsTop'
      have hAppTarget : WfM Γfop (.app (.abs bound' body') operand) :=
        WfM.app hFunTarget hOperandBound'
      cases sfop with
      | nil =>
          simpa [WfMachineState, Stack.plug] using hAppTarget
      | cons next tail =>
          exact
            (MEqRedMachineTailStepPreservesConsPayload.of_target_app
              hTargetApp
              (MEqRedMachineTailStepPreservesPayload.of_cons hTailCons))
              hΓ (MEqRed.fOp hBound hOperandScoped hBodyRed)
              hwfAbs' hState

/-- Append-native direct no-external-empty split-beta assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_control_left_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons
    hSubst
    (WfMachineStateControlLeftPayload.of_msubstar_stack_append
      hAppend hBridge)
    hInv hBetaBody hFOpBody hTargetApp hTailCons hFunBody hNoTop

/-- No-external-empty split-beta assembly. The `Me-Bet` branch uses the
constructor induction hypothesis for the empty-stack argument reduction
instead of requiring an external empty-stack preservation premise. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hTargetApp hTailCons hFunBody hNoTop

/-- Typed-operator variant of the direct no-external-empty split-beta
assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons
    hSubst hAppend hBridge hInv hBetaBody hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_typed_operator hOpFun hTail)
    hFunBody hNoTop

/-- Typed-operator variant of the direct no-external-empty split-beta
assembly, with the control-left residual still exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_operator_machine_tail
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hFunBody hNoTop

/-- Machine-state-aware operator variant of the direct no-external-empty
split-beta assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_machine_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons
    hSubst hAppend hBridge hInv hBetaBody hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_machine_operator hOpFun hTail)
    hFunBody hNoTop

/-- Machine-state-aware operator variant of the direct no-external-empty
split-beta assembly, with the control-left residual still exposed through
the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_machine_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_machine_operator_machine_tail
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hFunBody hNoTop

/-- Native-`FOp`-body variant of the direct no-external-empty split-beta
assembly. The native body residual is converted to the typed one using the
operand-to-bound premise available in the `Me-FOp` branch. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons
    hSubst hAppend hBridge hInv hBetaBody
    (MEqRedFOpBodyTypedPayload.of_untyped hFOpBody) hTargetApp hTailCons
    hFunBody hNoTop

/-- Native-`FOp`-body variant of the direct no-external-empty split-beta
assembly, with the control-left residual still exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hTargetApp hTailCons
    hFunBody hNoTop

/-- Typed-operator entry point for the native-`FOp`-body direct split-beta
machine assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons
    hSubst hAppend hBridge hInv hBetaBody hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_typed_operator hOpFun hTail)
    hFunBody hNoTop

/-- Typed-operator entry point for the native-`FOp`-body direct split-beta
machine assembly, with the control-left residual still exposed through the
older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_operator_machine_tail
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hFunBody hNoTop

/-- Machine-state-aware operator entry point for the native-`FOp`-body direct
split-beta machine assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_machine_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons
    hSubst hAppend hBridge hInv hBetaBody hFOpBody
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_machine_operator hOpFun hTail)
    hFunBody hNoTop

/-- Machine-state-aware operator entry point for the native-`FOp`-body direct
split-beta machine assembly, with the control-left residual still exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_machine_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_machine_operator_machine_tail
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hFunBody hNoTop

/-- Empty-stack left-endpoint transport for well-subtyping along one
equivalence-reduction step. Unlike `MEqRedStackPreservesWSubMStarLeft`, this
version is directly compatible with the empty-stack `WSubM` equivalence
embedding rules. -/
def MEqRedEmptyPreservesWSubMStarLeft : Type :=
  ∀ {Γ : Ctx} {source source' target : Term},
    WfCtxEqu Γ →
      WSubMStar Γ source target →
        MEqRed Γ [] source source' →
          WSubMStar Γ source' target

/-- The contextual preservation payload specializes to the empty stack. -/
noncomputable def MEqRedPreservesWfMUnderWfCtx.of_contextual
    (hpres : MEqRedPreservesWfMContextual) :
    MEqRedPreservesWfMUnderWfCtx := by
  intro Γ x y hΓ hred hwf
  exact hpres hΓ WfStack.nil hred.some hwf

/-- Empty-stack left-endpoint transport follows from empty-stack
well-formedness preservation. The proof embeds the forward equivalence step
backward as `source' ≤ source`, then composes with the original
`source ≤ target` chain. -/
noncomputable def MEqRedEmptyPreservesWSubMStarLeft.of_wf_preservation
    (hpres : MEqRedPreservesWfMUnderWfCtx) :
    MEqRedEmptyPreservesWSubMStarLeft := by
  intro Γ source source' target hΓ hSub hred
  have hwfSource : WfM Γ source := hSub.wf_left
  have hwfSource' : WfM Γ source' :=
    hpres hΓ ⟨hred⟩ hwfSource
  have hBack : WSubMStar Γ source' source :=
    WSubMStar.of_MEqRed_back hred hwfSource hwfSource'
  exact WSubMStar.trans hwfSource hBack hSub

/-- Contextual well-formedness preservation also supplies the empty-stack
left-endpoint well-subtyping transport by specializing to `[]`. -/
noncomputable def MEqRedEmptyPreservesWSubMStarLeft.of_contextual
    (hpres : MEqRedPreservesWfMContextual) :
    MEqRedEmptyPreservesWSubMStarLeft :=
  MEqRedEmptyPreservesWSubMStarLeft.of_wf_preservation
    (MEqRedPreservesWfMUnderWfCtx.of_contextual hpres)

/-- Machine-state preservation supplies empty-stack left-endpoint transport
by specializing the machine state to the empty stack. -/
noncomputable def MEqRedEmptyPreservesWSubMStarLeft.of_machine_state
    (hpres : MEqRedPreservesWfMachineState) :
    MEqRedEmptyPreservesWSubMStarLeft :=
  MEqRedEmptyPreservesWSubMStarLeft.of_wf_preservation
    (MEqRedPreservesWfMUnderWfCtx.of_machine_state hpres)

/-- `Me-Pro` well-formedness preservation under the contextual preservation
payload. `WfCtxEqu.lookup_equ` supplies the promoted annotation's
well-formedness before the recursive reduction premise is used. -/
noncomputable def MEqRed.pro_preservesWfM_of_contextual
    (hpres : MEqRedPreservesWfMContextual)
    {Γ : Ctx} {s : Stack} {i : Nat} {α α' : Term}
    (hΓ : WfCtxEqu Γ) (hStack : WfStack Γ s)
    (hb : Γ.equBinds i α) (hred : MEqRed Γ s α α')
    (hwfVar : WfM Γ (.bvar i)) : WfM Γ α' := by
  have hwfα : WfM Γ α := WfCtxEqu.lookup_equ hΓ hwfVar.prevalid hb
  exact hpres hΓ hStack hred hwfα

/-- `Me-Top` preserves well-formedness directly from the reduction's
prevalidity witness. -/
noncomputable def MEqRed.top_preservesWfM
    {Γ : Ctx} {s : Stack} (hpv : PrevalidExt Γ s)
    (_hwf : WfM Γ .top) : WfM Γ .top :=
  WfM.top (PrevalidExt.ctx hpv)

/-- `Me-Var` preserves well-formedness by returning the original variable
well-formedness witness. -/
def MEqRed.var_preservesWfM
    {Γ : Ctx} {s : Stack} {i : Nat}
    (_hpv : PrevalidExt Γ s) (_hi : i < Γ.depth)
    (hwf : WfM Γ (.bvar i)) : WfM Γ (.bvar i) :=
  hwf

/-- `Me-TAp` preserves well-formedness because its target is `Top`. -/
noncomputable def MEqRed.tAp_preservesWfM
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (_hu : Term.Scoped Γ.depth u)
    (_hwf : WfM Γ (.app .top u)) : WfM Γ .top :=
  WfM.top (PrevalidExt.ctx hpv)

/-- `Me-App` well-formedness preservation reduced to the operator-side
function-supertype payload. The argument side is discharged from the
contextual empty-stack preservation specialization. -/
noncomputable def MEqRed.app_preservesWfM_of_contextual
    (hpres : MEqRedPreservesWfMContextual)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    {Γ : Ctx} {s : Stack} {u u' v v' : Term}
    (hΓ : WfCtxEqu Γ) (hStack : WfStack Γ s)
    (hredOp : MEqRed Γ (v :: s) u u')
    (hredArg : MEqRed Γ [] v v')
    (hwfApp : WfM Γ (.app u v)) : WfM Γ (.app u' v') := by
  obtain ⟨bound, hFun, hArg⟩ := hwfApp.app_inv
  have hwfV : WfM Γ v := hArg.wf_left
  have hwfV' : WfM Γ v' := hpres hΓ WfStack.nil hredArg hwfV
  have hFun' : WSubMStar Γ u' (.abs bound .top) :=
    hOpFun hΓ hStack hwfV hFun hredOp
  have hArgBack : WSubMStar Γ v' v :=
    WSubMStar.of_MEqRed_back hredArg hwfV hwfV'
  have hArg' : WSubMStar Γ v' bound :=
    WSubMStar.trans hwfV hArgBack hArg
  exact WfM.app hFun' hArg'

/-- Typed `Me-App` well-formedness preservation. This variant feeds the
operand-to-bound premise from source application typing to the operator
payload, avoiding the broad stack-only operator residual. -/
noncomputable def MEqRed.app_preservesWfM_of_empty_and_typed_operator
    (hpres : MEqRedPreservesWfMUnderWfCtx)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    {Γ : Ctx} {s : Stack} {u u' v v' : Term}
    (hΓ : WfCtxEqu Γ) (hStack : WfStack Γ s)
    (hredOp : MEqRed Γ (v :: s) u u')
    (hredArg : MEqRed Γ [] v v')
    (hwfApp : WfM Γ (.app u v)) : WfM Γ (.app u' v') := by
  obtain ⟨bound, hFun, hArg⟩ := hwfApp.app_inv
  have hwfV : WfM Γ v := hArg.wf_left
  have hwfV' : WfM Γ v' := hpres hΓ ⟨hredArg⟩ hwfV
  have hFun' : WSubMStar Γ u' (.abs bound .top) :=
    hOpFun hΓ hStack hArg hFun hredOp
  have hArgBack : WSubMStar Γ v' v :=
    WSubMStar.of_MEqRed_back hredArg hwfV hwfV'
  have hArg' : WSubMStar Γ v' bound :=
    WSubMStar.trans hwfV hArgBack hArg
  exact WfM.app hFun' hArg'

/-- `Me-Fun` well-formedness preservation reduced to the body
context-replacement payload. -/
noncomputable def MEqRed.fun_preservesWfM_of_contextual
    (hpres : MEqRedPreservesWfMContextual)
    (hBodyReplace : MEqRedFunBodyReplacePayload)
    {Γ : Ctx} {bound bound' body body' : Term}
    (hΓ : WfCtxEqu Γ)
    (hredBound : MEqRed Γ [] bound bound')
    (hredBody : MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body')
    (hwfAbs : WfM Γ (.abs bound body)) :
    WfM Γ (.abs bound' body') := by
  have hwfBound : WfM Γ bound := hwfAbs.fun_inv.1
  have hwfBody : WfM ({ bound := bound, kind := .sub } :: Γ) body :=
    hwfAbs.fun_inv.2
  have hwfBound' : WfM Γ bound' :=
    hpres hΓ WfStack.nil hredBound hwfBound
  have hΓBody : WfCtxEqu ({ bound := bound, kind := .sub } :: Γ) :=
    WfCtxEqu.sub hΓ
  have hwfBodyOld : WfM ({ bound := bound, kind := .sub } :: Γ) body' :=
    hpres hΓBody WfStack.nil hredBody hwfBody
  exact WfM.fun_ hwfBound'
    (hBodyReplace hΓ hwfBound hwfBound' hredBound hwfBodyOld)

/-- `Me-FOp` well-formedness preservation reduced to the body payload that
bridges from the stack-introduced `.equ` head back to the target `.sub`
head. -/
noncomputable def MEqRed.fOp_preservesWfM_of_contextual
    (hpres : MEqRedPreservesWfMContextual)
    (hBody : MEqRedFOpBodyPayload)
    {Γ : Ctx} {s : Stack} {bound bound' operand body body' : Term}
    (hΓ : WfCtxEqu Γ) (hStack : WfStack Γ s)
    (hwfOperand : WfM Γ operand)
    (hredBound : MEqRed Γ [] bound bound')
    (hredBody : MEqRed ({ bound := operand, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body')
    (hwfAbs : WfM Γ (.abs bound body)) :
    WfM Γ (.abs bound' body') := by
  have hwfBound : WfM Γ bound := hwfAbs.fun_inv.1
  have hwfBody : WfM ({ bound := bound, kind := .sub } :: Γ) body :=
    hwfAbs.fun_inv.2
  have hwfBound' : WfM Γ bound' :=
    hpres hΓ WfStack.nil hredBound hwfBound
  exact WfM.fun_ hwfBound'
    (hBody hΓ hStack hwfBound hwfBound' hwfOperand hwfBody hredBound hredBody)

/-- Typed `Me-FOp` well-formedness preservation. This is the constructive
replacement shape for the broad contextual helper: the caller must provide
the application typing premise `operand ≤* bound`, and only empty-stack
preservation is needed for the abstraction-bound reduction. -/
noncomputable def MEqRed.fOp_preservesWfM_of_empty_and_typed_body
    (hpres : MEqRedPreservesWfMUnderWfCtx)
    (hBody : MEqRedFOpBodyTypedPayload)
    {Γ : Ctx} {s : Stack} {bound bound' operand body body' : Term}
    (hΓ : WfCtxEqu Γ) (hStack : WfStack Γ s)
    (hOperandBound : WSubMStar Γ operand bound)
    (hredBound : MEqRed Γ [] bound bound')
    (hredBody : MEqRed ({ bound := operand, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body')
    (hwfAbs : WfM Γ (.abs bound body)) :
    WfM Γ (.abs bound' body') := by
  have hwfBound : WfM Γ bound := hwfAbs.fun_inv.1
  have hwfBody : WfM ({ bound := bound, kind := .sub } :: Γ) body :=
    hwfAbs.fun_inv.2
  have hwfBound' : WfM Γ bound' :=
    hpres hΓ ⟨hredBound⟩ hwfBound
  exact WfM.fun_ hwfBound'
    (hBody hΓ hStack hwfBound hwfBound' hOperandBound hwfBody
      hredBound hredBody)

/-- Contextual `MEqRed` well-formedness preservation assembled from the
remaining constructor payloads. The direct cases are proved here; the β,
application-operator, function-body replacement, and `fOp` body bridges stay
explicit. -/
noncomputable def MEqRedPreservesWfMContextual.of_components
    (hBeta : MEqRedBetaPreservesWfMContextual)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual := by
  intro Γ s x y hΓ hStack hred hwf
  revert hΓ hStack hwf
  induction hred with
  | pro hpv hb hred ih =>
      intro hΓ hStack hwf
      have hwfα := WfCtxEqu.lookup_equ hΓ hwf.prevalid hb
      exact ih hΓ hStack hwfα
  | bet ht hBody hArg _ihBody _ihArg =>
      intro hΓ hStack hwf
      exact hBeta hΓ hStack ht hBody hArg hwf
  | top hpv =>
      intro hΓ hStack hwf
      exact MEqRed.top_preservesWfM hpv hwf
  | app hOp hArg _ihOp ihArg =>
      intro hΓ hStack hwf
      obtain ⟨bound, hFun, hArgTyping⟩ := hwf.app_inv
      have hwfV := hArgTyping.wf_left
      have hwfV' := ihArg hΓ WfStack.nil hwfV
      have hFun' :=
        hOpFun hΓ hStack hwfV hFun hOp
      have hArgBack :=
        WSubMStar.of_MEqRed_back hArg hwfV hwfV'
      have hArgTyping' :=
        WSubMStar.trans hwfV hArgBack hArgTyping
      exact WfM.app hFun' hArgTyping'
  | var hpv hi =>
      intro hΓ hStack hwf
      exact MEqRed.var_preservesWfM hpv hi hwf
  | fun_ hBound hBody ihBound ihBody =>
      intro hΓ hStack hwf
      have hwfBound := hwf.fun_inv.1
      have hwfBody :=
        hwf.fun_inv.2
      have hwfBound' := ihBound hΓ WfStack.nil hwfBound
      have hwfBodyOld :=
        ihBody (WfCtxEqu.sub hΓ) WfStack.nil hwfBody
      exact WfM.fun_ hwfBound'
        (hFunBody hΓ hwfBound hwfBound' hBound hwfBodyOld)
  | tAp hpv hu =>
      intro hΓ hStack hwf
      exact MEqRed.tAp_preservesWfM hpv hu hwf
  | fOp hBound hOperand hBody ihBound _ihBody =>
      intro hΓ hStack hwf
      have hwfOperand := WfStack.head hStack
      have hStackTail := WfStack.tail hStack
      have hwfBound := hwf.fun_inv.1
      have hwfBody :=
        hwf.fun_inv.2
      have hwfBound' := ihBound hΓ WfStack.nil hwfBound
      exact WfM.fun_ hwfBound'
        (hFOpBody hΓ hStackTail hwfBound hwfBound' hwfOperand
          hwfBody hBound hBody)

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

/-- Extract a Type-valued diagrammatic common reduct from one de Bruijn
well-subtyping derivation. -/
noncomputable def WSubM.to_chain_diagram {Γ : Ctx} {source target : Term}
    (hSub : WSubM Γ source target) :
    WSubMChainDiagram Γ source target := by
  exact (WSubM.rec
    (motive_1 := fun _ _ _ => PUnit)
    (motive_2 := fun Γ source target _ =>
      WSubMChainDiagram Γ source target)
    (motive_3 := fun _ _ _ _ => PUnit)
    (fun _ _ => PUnit.unit)
    (fun _ _ => PUnit.unit)
    (fun _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit)
    (fun {Γ t} _ _ => {
      join := t
      subJoin := MSubRedChain.refl
      eqJoin := MEqRedChain.refl
    })
    (fun {Γ source source' target} hred _ d => {
      join := d.join
      subJoin := MSubRedChain.trans
        (MSubRedChain.single
          (MSubRed.equ (PrevalidExt.nil hred.prevalid) hred))
        d.subJoin
      eqJoin := d.eqJoin
    })
    (fun {Γ source source' target} _ hred _ _ _ _ d => {
      join := d.join
      subJoin := MSubRedChain.trans (MSubRedChain.single hred) d.subJoin
      eqJoin := d.eqJoin
    })
    (fun {Γ source target target'} _ hred d => {
      join := d.join
      subJoin := d.subJoin
      eqJoin := MEqRedChain.trans (MEqRedChain.single hred) d.eqJoin
    })
    (fun _ _ _ _ _ _ => PUnit.unit)
    (fun _ _ _ _ _ _ => PUnit.unit)
    hSub)

/-- Forget the Type-valued one-step well-subtyping diagram into the existing
Prop-valued diagrammatic subtyping relation. -/
def WSubMChainDiagram.toMSub {Γ : Ctx} {source target : Term}
    (d : WSubMChainDiagram Γ source target) : MSub Γ [] source target :=
  ⟨d.join, d.subJoin.to_star, d.eqJoin.to_star⟩

/-- Compose two Type-valued well-subtyping diagrams, using de Bruijn Lemma 1
to commute the first diagram's right equivalence leg against the second
diagram's left subtype leg. -/
noncomputable def WSubMChainDiagram.trans_of {Γ : Ctx}
    (hcomm : StrongCommutes Γ []) {source mid target : Term}
    (d₁ : WSubMChainDiagram Γ source mid)
    (d₂ : WSubMChainDiagram Γ mid target) :
    WSubMChainDiagram Γ source target := by
  obtain ⟨join, hEqJoin, hSubJoin⟩ :=
    commute_subChain_eqChain_of hcomm d₂.subJoin d₁.eqJoin
  exact {
    join := join
    subJoin := MSubRedChain.trans d₁.subJoin hSubJoin
    eqJoin := MEqRedChain.trans d₂.eqJoin hEqJoin
  }

/-- Extract a Type-valued diagrammatic common reduct from transitive
well-subtyping, assuming de Bruijn strong commutativity at the empty stack. -/
noncomputable def WSubMStar.to_chain_diagram_of {Γ : Ctx}
    (hcomm : StrongCommutes Γ []) {source target : Term}
    (hSub : WSubMStar Γ source target) :
    WSubMChainDiagram Γ source target := by
  exact (WSubMStar.rec
    (motive_1 := fun _ _ _ => PUnit)
    (motive_2 := fun _ _ _ _ => PUnit)
    (motive_3 := fun Γ source target _ =>
      StrongCommutes Γ [] → WSubMChainDiagram Γ source target)
    (fun _ _ => PUnit.unit)
    (fun _ _ => PUnit.unit)
    (fun _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit)
    (fun _ _ => PUnit.unit)
    (fun _ _ _ => PUnit.unit)
    (fun _ _ _ _ _ _ _ => PUnit.unit)
    (fun _ _ _ => PUnit.unit)
    (fun _ h _ _ _ _ => fun _ => h.to_chain_diagram)
    (fun _ _ _ ihLeft _ ihRight => fun hcomm =>
      WSubMChainDiagram.trans_of hcomm (ihLeft hcomm) (ihRight hcomm))
    hSub) hcomm

/-- Named de Bruijn Theorem 3 use-site in Type-valued chain-diagram form.
This keeps the chain witnesses needed by the function-bound inversion layer,
instead of immediately forgetting them to Prop-valued closures. -/
noncomputable def Theorem_3_DeBruijn_WSubMStar_toChainDiagram_of
    {Γ : Ctx} {source target : Term}
    (hcomm : StrongCommutes Γ [])
    (hSub : WSubMStar Γ source target) :
    WSubMChainDiagram Γ source target :=
  hSub.to_chain_diagram_of hcomm

namespace WEquMStar

/-- Extract a Type-valued diagrammatic common reduct from transitive
well-equivalence, via the well-subtyping embedding and the chain-diagram
Theorem 3 use-site. -/
noncomputable def to_chain_diagram_of {Γ : Ctx}
    (hcomm : StrongCommutes Γ []) {source target : Term}
    (hEqu : WEquMStar Γ source target) :
    WSubMChainDiagram Γ source target :=
  hEqu.toWSubMStar.to_chain_diagram_of hcomm

end WEquMStar

/-- Named de Bruijn Theorem 3 well-equivalence use-site in Type-valued
chain-diagram form. -/
noncomputable def Theorem_3_DeBruijn_WEquMStar_toChainDiagram_of
    {Γ : Ctx} {source target : Term}
    (hcomm : StrongCommutes Γ [])
    (hEqu : WEquMStar Γ source target) :
    WSubMChainDiagram Γ source target :=
  hEqu.to_chain_diagram_of hcomm

/-- Extract the abstraction-shaped function-bound common reduct from a
transitive function-supertype derivation. This is the star-level diagram
shape needed before proving the joined bound is well-formed. -/
noncomputable def WSubMStar.abs_function_bound_chain_shape_of
    {Γ : Ctx} (hcomm : StrongCommutes Γ [])
    {bound body result : Term}
    (hSub : WSubMStar Γ (.abs bound body) (.abs result .top)) :
    AbsFunctionBoundChainShape Γ bound body result := by
  let d := hSub.to_chain_diagram_of hcomm
  obtain ⟨joinBound, joinBody, hJoin⟩ := d.eqJoin.abs_inv_type
  cases hJoin with
  | up hJoin =>
      exact {
        joinBound := joinBound
        joinBody := joinBody
        subJoin := by simpa [hJoin] using d.subJoin
        eqJoin := by simpa [hJoin] using d.eqJoin
      }

/-- Strong commutativity at every context supplies the shape-only
function-bound payload for transitive well-subtyping. -/
noncomputable def AbsFunctionBoundChainShapePayload_of
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ []) :
    AbsFunctionBoundChainShapePayload := by
  intro Γ bound body result hSub
  exact WSubMStar.abs_function_bound_chain_shape_of (hcomm (Γ := Γ)) hSub

/-- Named Theorem 3-to-function-bound-shape adapter used by the de Bruijn
preservation route. It exposes the abstraction-shaped chain witnesses without
requiring callers to rebuild the transitive well-subtyping collapse. -/
noncomputable def Theorem_3_DeBruijn_AbsFunctionBoundChainShapePayload_of
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ []) :
    AbsFunctionBoundChainShapePayload :=
  AbsFunctionBoundChainShapePayload_of hcomm

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

/-- Append an equivalence chain on the right side of an abstraction diagram. -/
noncomputable def AbsAbsBoundChainDiagram.rgh_chain
    {Γ : Ctx} {bound body result resultBody result' resultBody' : Term}
    (d : AbsAbsBoundChainDiagram Γ bound body result' resultBody')
    (hred : MEqRedChain Γ [] (.abs result resultBody)
      (.abs result' resultBody')) :
    AbsAbsBoundChainDiagram Γ bound body result resultBody := by
  suffices key : ∀ {target : Term},
      MEqRedChain Γ [] (.abs result resultBody) target →
        ∀ {result' resultBody' : Term},
          PLift (target = .abs result' resultBody') →
            AbsAbsBoundChainDiagram Γ bound body result' resultBody' →
              AbsAbsBoundChainDiagram Γ bound body result resultBody from
    key hred ⟨rfl⟩ d
  intro target hChain
  induction hChain with
  | refl =>
      intro result' resultBody' hEq d
      cases hEq with
      | up hEq =>
          cases hEq
          exact d
  | tail hChain hStep ih =>
      intro result' resultBody' hEq d
      cases hEq with
      | up hEq =>
          subst hEq
          obtain ⟨midBound, midBody, hMid⟩ := hChain.abs_inv_type
          cases hMid with
          | up hMid =>
              subst hMid
              exact ih ⟨rfl⟩ (AbsAbsBoundChainDiagram.rgh d hStep)

/-- Prepend a subtype step on the left side of an abstraction diagram, after
the subtype step target has been classified as an abstraction. The
classification is the part that must rule out the `Top` branch separately. -/
noncomputable def AbsAbsBoundChainDiagram.lf2_abs
    {Γ : Ctx} {bound body bound' body' result resultBody : Term}
    (hred : MSubRed Γ [] (.abs bound body) (.abs bound' body'))
    (d : AbsAbsBoundChainDiagram Γ bound' body' result resultBody) :
    AbsAbsBoundChainDiagram Γ bound body result resultBody where
  joinBound := d.joinBound
  joinBody := d.joinBody
  subJoin := MSubRedChain.trans (MSubRedChain.single hred) d.subJoin
  eqJoin := d.eqJoin
  wfJoinBound := d.wfJoinBound

/-- Apply the abstraction `Top` obstruction after appending a right
equivalence chain to the well-subtyping derivation. -/
noncomputable def NoTopAbstractionSupertypesAt.of_wsubm_right_chain
    {Γ : Ctx} {result resultBody target : Term}
    (hNoTop : NoTopAbstractionSupertypesAt)
    (hwfTop : WfM Γ .top)
    (hwfTarget : WfM Γ (.abs result resultBody))
    (hSub : WSubM Γ .top target)
    (hred : MEqRedChain Γ [] (.abs result resultBody) target) :
    False :=
  hNoTop (WSubMStar.sub hwfTop
    (WSubM.right_rgh_chain hSub hred.to_star) hwfTarget)

/-- Extract an abstraction diagram from one de Bruijn well-subtyping
derivation, with a right-equivalence continuation to the final abstraction
target. The continuation lets right-equivalence branches keep using the
original well-formed target when ruling out paths through `Top`. -/
noncomputable def WSubM.abs_abs_chain_diagram_with_right_chain
    {Γ : Ctx} {source target : Term}
    (hSub : WSubM Γ source target) :
    ∀ {bound body result resultBody : Term},
      NoTopAbstractionSupertypesAt →
        WfM Γ (.abs result resultBody) →
          PLift (source = .abs bound body) →
            MEqRedChain Γ [] (.abs result resultBody) target →
              AbsAbsBoundChainDiagram Γ bound body result resultBody := by
  exact (WSubM.rec
    (motive_1 := fun _ _ _ => PUnit)
    (motive_2 := fun Γ source target _ =>
      ∀ {bound body result resultBody : Term},
        NoTopAbstractionSupertypesAt →
          WfM Γ (.abs result resultBody) →
            PLift (source = .abs bound body) →
              MEqRedChain Γ [] (.abs result resultBody) target →
                AbsAbsBoundChainDiagram Γ bound body result resultBody)
    (motive_3 := fun _ _ _ _ => PUnit)
    (fun _ _ => PUnit.unit)
    (fun _ _ => PUnit.unit)
    (fun _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit)
    (fun {Γ t} hwf _ => by
      intro bound body result resultBody _hNoTop _hwfTarget hSource hRight
      cases hSource with
      | up hSource =>
          subst hSource
          exact AbsAbsBoundChainDiagram.rgh_chain
            (AbsAbsBoundChainDiagram.refl hwf) hRight)
    (fun {Γ v v' t} hred _ ih => by
      intro bound body result resultBody hNoTop hwfTarget hSource hRight
      cases hSource with
      | up hSource =>
          subst hSource
          obtain ⟨bound', body', hTarget⟩ := hred.abs_inv_type
          cases hTarget with
          | up hTarget =>
              subst hTarget
              exact AbsAbsBoundChainDiagram.lf1 hred
                (ih hNoTop hwfTarget (PLift.up (Eq.refl _)) hRight))
    (fun {Γ v v' t} _hwfV hred hwfV' hsub _ _ ih => by
      intro bound body result resultBody hNoTop hwfTarget hSource hRight
      cases hSource with
      | up hSource =>
          subst hSource
          cases hred.abs_inv_type with
          | inl hTop =>
              cases hTop with
              | up hTop =>
                  subst hTop
                  exact False.elim
                    (NoTopAbstractionSupertypesAt.of_wsubm_right_chain
                      hNoTop hwfV' hwfTarget hsub hRight)
          | inr hAbs =>
              obtain ⟨bound', body', hTarget⟩ := hAbs
              cases hTarget with
              | up hTarget =>
                  subst hTarget
                  exact AbsAbsBoundChainDiagram.lf2_abs hred
                    (ih hNoTop hwfTarget (PLift.up (Eq.refl _)) hRight))
    (fun {Γ v t t'} _ hred ih => by
      intro bound body result resultBody hNoTop hwfTarget hSource hRight
      exact ih hNoTop hwfTarget hSource (MEqRedChain.tail hRight hred))
    (fun _ _ _ _ _ _ => PUnit.unit)
    (fun _ _ _ _ _ _ => PUnit.unit)
    hSub)

/-- One-step well-subtyping abstraction diagram extraction. -/
noncomputable def WSubM.abs_abs_chain_diagram :
    WSubMAbsAbsChainDiagramPayload := by
  intro Γ bound body result resultBody hNoTop _hwfSource hwfTarget hSub
  exact hSub.abs_abs_chain_diagram_with_right_chain
    hNoTop hwfTarget (PLift.up (Eq.refl _)) MEqRedChain.refl

/-- Direct one-step function-bound chain diagram extraction from `WSubM`. -/
noncomputable def WSubM.abs_function_bound_chain_diagram
    {Γ : Ctx} {bound body result : Term}
    (hNoTop : NoTopAbstractionSupertypesAt)
    (_hwfSource : WfM Γ (.abs bound body))
    (hwfTarget : WfM Γ (.abs result .top))
    (hSub : WSubM Γ (.abs bound body) (.abs result .top)) :
    AbsFunctionBoundChainDiagram Γ bound body result :=
  AbsFunctionBoundChainDiagram.of_abs_abs
    (hSub.abs_abs_chain_diagram_with_right_chain
      hNoTop hwfTarget (PLift.up (Eq.refl _)) MEqRedChain.refl)

/-- Direct one-step function-bound inversion from `WSubM`, obtained by
projecting the Type-valued chain diagram. -/
noncomputable def WSubM.abs_function_bound_inversion
    {Γ : Ctx} {bound body result : Term}
    (hNoTop : NoTopAbstractionSupertypesAt)
    (hwfSource : WfM Γ (.abs bound body))
    (hwfTarget : WfM Γ (.abs result .top))
    (hSub : WSubM Γ (.abs bound body) (.abs result .top)) :
    WEquMStar Γ bound result := by
  let d := hSub.abs_function_bound_chain_diagram hNoTop hwfSource hwfTarget
  have hwfBound : WfM Γ bound := hwfSource.fun_inv.1
  have hwfResult : WfM Γ result := hwfTarget.fun_inv.1
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

/-- Choose Type-valued chains from an older Prop-closure function-bound
diagram. This is a compatibility bridge for payloads that already know the
common reduct but produced Prop-valued closures. -/
noncomputable def AbsFunctionBoundChainDiagram.of_diagram
    {Γ : Ctx} {bound body result : Term}
    (d : AbsFunctionBoundDiagram Γ bound body result) :
    AbsFunctionBoundChainDiagram Γ bound body result where
  joinBound := d.joinBound
  joinBody := d.joinBody
  subJoin := MSubRedChain.of_star d.subJoin
  eqJoin := MEqRedChain.of_star d.eqJoin
  wfJoinBound := d.wfJoinBound

/-- A chain-diagram payload can be consumed anywhere the older Prop-closure
diagram payload is expected. -/
def AbsFunctionBoundDiagramPayload.of_chain
    (hDiagram : AbsFunctionBoundChainDiagramPayload) :
    AbsFunctionBoundDiagramPayload := by
  intro Γ bound body result hFun
  exact AbsFunctionBoundDiagram.of_chain (hDiagram hFun)

/-- A shape payload plus its joined-bound well-formedness payload completes
the full Type-valued chain-diagram payload. -/
def AbsFunctionBoundChainDiagramPayload.of_shape
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfPayload hShape) :
    AbsFunctionBoundChainDiagramPayload := by
  intro Γ bound body result hFun
  exact (hShape hFun).to_diagram (hShapeWf hFun)

/-- Stepwise empty-stack equivalence preservation supplies the joined-bound
well-formedness needed to complete a shape-only function-bound payload. -/
noncomputable def AbsFunctionBoundChainShapeWfPayload_of_meq
    (hShape : AbsFunctionBoundChainShapePayload)
    (hpres : MEqRedPreservesWfM) :
    AbsFunctionBoundChainShapeWfPayload hShape := by
  intro Γ bound body result hFun
  have hwfBound : WfM Γ bound := hFun.wf_left.fun_inv.1
  let hBoundChain : MEqRedChain Γ [] bound (hShape hFun).joinBound :=
    MSubRedChain.abs_bound_chain (hShape hFun).subJoin
  exact hBoundChain.to_star.wf_right_of hpres hwfBound

/-- Contextual empty-stack equivalence preservation supplies joined-bound
well-formedness under a well-formed-equivalence context. -/
noncomputable def AbsFunctionBoundChainShapeWfUnderWfCtxPayload_of_meq
    (hShape : AbsFunctionBoundChainShapePayload)
    (hpres : MEqRedPreservesWfMUnderWfCtx) :
    AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape := by
  intro Γ bound body result hFun hΓ
  have hwfBound : WfM Γ bound := hFun.wf_left.fun_inv.1
  let hBoundChain : MEqRedChain Γ [] bound (hShape hFun).joinBound :=
    MSubRedChain.abs_bound_chain (hShape hFun).subJoin
  exact hBoundChain.to_star.wf_right_of
    (fun hred hwf => hpres hΓ hred hwf) hwfBound

/-- Contextual `MEqRed` well-formedness preservation supplies joined-bound
well-formedness under a well-formed-equivalence context. -/
noncomputable def AbsFunctionBoundChainShapeWfUnderWfCtxPayload_of_contextual
    (hShape : AbsFunctionBoundChainShapePayload)
    (hpres : MEqRedPreservesWfMContextual) :
    AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape :=
  AbsFunctionBoundChainShapeWfUnderWfCtxPayload_of_meq hShape
    (MEqRedPreservesWfMUnderWfCtx.of_contextual hpres)

/-- Machine-state preservation supplies joined-bound well-formedness under a
well-formed-equivalence context by specializing to the empty stack. -/
noncomputable def AbsFunctionBoundChainShapeWfUnderWfCtxPayload_of_machine_state
    (hShape : AbsFunctionBoundChainShapePayload)
    (hpres : MEqRedPreservesWfMachineState) :
    AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape :=
  AbsFunctionBoundChainShapeWfUnderWfCtxPayload_of_meq hShape
    (MEqRedPreservesWfMUnderWfCtx.of_machine_state hpres)

/-- The well-formed-equivalence-context joined-bound payload specializes to
closed contexts. -/
def AbsFunctionBoundChainShapeWfClosedPayload.of_wfctx
    {hShape : AbsFunctionBoundChainShapePayload}
    (hWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape) :
    AbsFunctionBoundChainShapeWfClosedPayload hShape := by
  intro bound body result hFun
  exact hWf hFun WfCtxEqu.empty

/-- Contextual `MEqRed` preservation supplies closed joined-bound
well-formedness for shape-only function-bound diagrams. -/
noncomputable def AbsFunctionBoundChainShapeWfClosedPayload_of_contextual
    (hShape : AbsFunctionBoundChainShapePayload)
    (hpres : MEqRedPreservesWfMContextual) :
    AbsFunctionBoundChainShapeWfClosedPayload hShape :=
  AbsFunctionBoundChainShapeWfClosedPayload.of_wfctx
    (AbsFunctionBoundChainShapeWfUnderWfCtxPayload_of_contextual hShape hpres)

/-- Machine-state preservation supplies closed joined-bound well-formedness
for shape-only function-bound diagrams by specializing through the
well-formed-equivalence context route. -/
noncomputable def AbsFunctionBoundChainShapeWfClosedPayload_of_machine_state
    (hShape : AbsFunctionBoundChainShapePayload)
    (hpres : MEqRedPreservesWfMachineState) :
    AbsFunctionBoundChainShapeWfClosedPayload hShape :=
  AbsFunctionBoundChainShapeWfClosedPayload.of_wfctx
    (AbsFunctionBoundChainShapeWfUnderWfCtxPayload_of_machine_state
      hShape hpres)

/-- An older Prop-closure diagram payload can be upgraded to the Type-valued
chain-diagram payload by choosing chain witnesses for the two closures. -/
noncomputable def AbsFunctionBoundChainDiagramPayload.of_diagram
    (hDiagram : AbsFunctionBoundDiagramPayload) :
    AbsFunctionBoundChainDiagramPayload := by
  intro Γ bound body result hFun
  exact AbsFunctionBoundChainDiagram.of_diagram (hDiagram hFun)

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

/-- A shape-only chain payload plus joined-bound well-formedness under
`WfCtxEqu` gives the function-bound inversion needed by contextual
preservation. -/
noncomputable def AbsFunctionBoundInversionUnderWfCtx_of_chain_shape
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape) :
    AbsFunctionBoundInversionUnderWfCtx := by
  intro Γ bound body result hΓ hFun
  let d := (hShape hFun).to_diagram (hShapeWf hFun hΓ)
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

/-- Function-bound inversion under `WfCtxEqu`, with the joined-bound
well-formedness supplied by machine-state preservation specialized to the
empty stack. -/
noncomputable def AbsFunctionBoundInversionUnderWfCtx_of_chain_shape_machine_state
    (hShape : AbsFunctionBoundChainShapePayload)
    (hpres : MEqRedPreservesWfMachineState) :
    AbsFunctionBoundInversionUnderWfCtx :=
  AbsFunctionBoundInversionUnderWfCtx_of_chain_shape hShape
    (AbsFunctionBoundChainShapeWfUnderWfCtxPayload_of_machine_state
      hShape hpres)

/-- The older Prop-closure diagram payload can also feed function-bound
inversion through the Type-valued chain endpoint by choosing chain witnesses
for both closures. -/
noncomputable def AbsFunctionBoundInversion_of_diagram_via_chain
    (hDiagram : AbsFunctionBoundDiagramPayload) :
    AbsFunctionBoundInversion :=
  AbsFunctionBoundInversion_of_chain_diagram
    (AbsFunctionBoundChainDiagramPayload.of_diagram hDiagram)

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

/-- Constructor-local direct residuals needed to replace a `.sub` head in a
well-formed body once the replacement bound is already well formed.

This packages the exact recursive premises consumed by
`WfM.sub_head_replace_from_direct_payloads_of_new_wf`: direct term
replacement in the immediate old head, direct replacement under one preserved
head, empty-stack equivalence preservation in the old head, and the two
application/function subtype residuals. -/
structure WfMSubHeadReplaceDirectPayloads
    (Γ : Ctx) (old new : Term) : Type where
  wf : ∀ {x : Term},
    WfM ({ bound := old, kind := .sub } :: Γ) x →
      WfM ({ bound := new, kind := .sub } :: Γ) x
  wfUnder : ∀ {head : CtxEntry} {x : Term},
    WfM (head :: { bound := old, kind := .sub } :: Γ) x →
      WfM (head :: { bound := new, kind := .sub } :: Γ) x
  eqPresOld : ∀ {x y : Term},
    MEqRedJ ({ bound := old, kind := .sub } :: Γ) [] x y →
      WfM ({ bound := old, kind := .sub } :: Γ) x →
        WfM ({ bound := old, kind := .sub } :: Γ) y
  app : ∀ {arg u u' : Term},
    Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) arg →
      MSubRed ({ bound := old, kind := .sub } :: Γ) (arg :: []) u u' →
        WfM ({ bound := new, kind := .sub } :: Γ) (.app u arg) →
        WSubMStar ({ bound := new, kind := .sub } :: Γ)
          (.app u arg) (.app u' arg)
  fun_ : ∀ {t t' body body' : Term},
    Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) t →
      MEqRed ({ bound := old, kind := .sub } :: Γ) [] t t' →
        MSubRed ({ bound := t, kind := .sub } ::
            { bound := old, kind := .sub } :: Γ) [] body body' →
        WfM ({ bound := new, kind := .sub } :: Γ) (.abs t body) →
        WSubMStar ({ bound := new, kind := .sub } :: Γ)
          (.abs t body) (.abs t' body')

/-- Assemble the sharpened `.sub` head replacement payload from the direct
constructor-local residual package used by the de Bruijn well-formedness
replacement theorem. -/
noncomputable def WfMSubHeadReplaceOfNewWf.of_direct_payloads
    (hPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new) :
    WfMSubHeadReplaceOfNewWf := by
  intro Γ old new body hOldNew hNew hBody
  let p := hPayloads hOldNew hNew
  exact WfM.sub_head_replace_from_direct_payloads_of_new_wf hBody hOldNew
    hNew p.wf p.wfUnder p.eqPresOld p.app p.fun_

/-- Preserved-head `.sub` replacement payload. This is the recursive shape
needed after descending under one binder while the replaced `.sub` entry
remains in the tail. -/
def WfMSubUnderHeadReplaceOfNewWf : Type :=
  ∀ {Γ : Ctx} {head : CtxEntry} {old new body : Term},
    MEqRed Γ [] old new →
      WfM Γ new →
        WfM (head :: { bound := old, kind := .sub } :: Γ) body →
          WfM (head :: { bound := new, kind := .sub } :: Γ) body

/-- Constructor-local direct residuals needed for preserved-head `.sub`
replacement once the replacement bound is already well formed. -/
structure WfMSubUnderHeadReplaceDirectPayloads
    (Γ : Ctx) (head : CtxEntry) (old new : Term) : Type where
  wf : ∀ {x : Term},
    WfM (head :: { bound := old, kind := .sub } :: Γ) x →
      WfM (head :: { bound := new, kind := .sub } :: Γ) x
  wfUnder : ∀ {head' : CtxEntry} {x : Term},
    WfM (head' :: head :: { bound := old, kind := .sub } :: Γ) x →
      WfM (head' :: head :: { bound := new, kind := .sub } :: Γ) x
  eqPresOld : ∀ {x y : Term},
    MEqRedJ (head :: { bound := old, kind := .sub } :: Γ) [] x y →
      WfM (head :: { bound := old, kind := .sub } :: Γ) x →
        WfM (head :: { bound := old, kind := .sub } :: Γ) y
  app : ∀ {arg u u' : Term},
    Term.Scoped (Ctx.depth (head :: { bound := old, kind := .sub } :: Γ)) arg →
      MSubRed (head :: { bound := old, kind := .sub } :: Γ)
        (arg :: []) u u' →
        WfM (head :: { bound := new, kind := .sub } :: Γ) (.app u arg) →
        WSubMStar (head :: { bound := new, kind := .sub } :: Γ)
          (.app u arg) (.app u' arg)
  fun_ : ∀ {t t' body body' : Term},
    Term.Scoped (Ctx.depth (head :: { bound := old, kind := .sub } :: Γ)) t →
      MEqRed (head :: { bound := old, kind := .sub } :: Γ) [] t t' →
        MSubRed ({ bound := t, kind := .sub } :: head ::
            { bound := old, kind := .sub } :: Γ) [] body body' →
        WfM (head :: { bound := new, kind := .sub } :: Γ) (.abs t body) →
        WSubMStar (head :: { bound := new, kind := .sub } :: Γ)
          (.abs t body) (.abs t' body')

/-- Assemble preserved-head `.sub` replacement from the direct
constructor-local residual package used by the de Bruijn well-formedness
under-head replacement theorem. -/
noncomputable def WfMSubUnderHeadReplaceOfNewWf.of_direct_payloads
    (hPayloads : ∀ {Γ : Ctx} {head : CtxEntry} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubUnderHeadReplaceDirectPayloads Γ head old new) :
    WfMSubUnderHeadReplaceOfNewWf := by
  intro Γ head old new body hOldNew hNew hBody
  let p := hPayloads (head := head) hOldNew hNew
  exact WfM.sub_under_head_replace_from_direct_payloads_of_new_wf
    hBody hOldNew hNew p.wf p.wfUnder p.eqPresOld p.app p.fun_

/-- Direct top-level `.sub` replacement residuals, factored so the
preserved-head recursion is supplied separately by
`WfMSubUnderHeadReplaceOfNewWf`. -/
structure WfMSubHeadReplaceImmediateDirectPayloads
    (Γ : Ctx) (old new : Term) : Type where
  wf : ∀ {x : Term},
    WfM ({ bound := old, kind := .sub } :: Γ) x →
      WfM ({ bound := new, kind := .sub } :: Γ) x
  eqPresOld : ∀ {x y : Term},
    MEqRedJ ({ bound := old, kind := .sub } :: Γ) [] x y →
      WfM ({ bound := old, kind := .sub } :: Γ) x →
        WfM ({ bound := old, kind := .sub } :: Γ) y
  app : ∀ {arg u u' : Term},
    Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) arg →
      MSubRed ({ bound := old, kind := .sub } :: Γ) (arg :: []) u u' →
        WfM ({ bound := new, kind := .sub } :: Γ) (.app u arg) →
        WSubMStar ({ bound := new, kind := .sub } :: Γ)
          (.app u arg) (.app u' arg)
  fun_ : ∀ {t t' body body' : Term},
    Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) t →
      MEqRed ({ bound := old, kind := .sub } :: Γ) [] t t' →
        MSubRed ({ bound := t, kind := .sub } ::
            { bound := old, kind := .sub } :: Γ) [] body body' →
        WfM ({ bound := new, kind := .sub } :: Γ) (.abs t body) →
        WSubMStar ({ bound := new, kind := .sub } :: Γ)
          (.abs t body) (.abs t' body')

/-- Combine immediate top-level direct residuals with the preserved-head
replacement payload to obtain the full direct residual package. -/
def WfMSubHeadReplaceDirectPayloads.of_immediate_and_under
    {Γ : Ctx} {old new : Term}
    (hOldNew : MEqRed Γ [] old new)
    (hNew : WfM Γ new)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (p : WfMSubHeadReplaceImmediateDirectPayloads Γ old new) :
    WfMSubHeadReplaceDirectPayloads Γ old new where
  wf := p.wf
  wfUnder := fun hBody => hUnder hOldNew hNew hBody
  eqPresOld := p.eqPresOld
  app := p.app
  fun_ := p.fun_

/-- Assemble top-level `.sub` head replacement from immediate direct residuals
and a preserved-head replacement payload. -/
noncomputable def
    WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new) :
    WfMSubHeadReplaceOfNewWf :=
  WfMSubHeadReplaceOfNewWf.of_direct_payloads
    (fun hOldNew hNew =>
      WfMSubHeadReplaceDirectPayloads.of_immediate_and_under
        hOldNew hNew hUnder (hPayloads hOldNew hNew))

/-- The existing sharpened `.sub` head replacement payload discharges the
body-replacement payload needed by the contextual `Me-Fun` case. -/
def MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf
    (hReplace : WfMSubHeadReplaceOfNewWf) :
    MEqRedFunBodyReplacePayload := by
  intro Γ bound bound' body' _hΓ _hwfBound hwfBound' hred hwfBody'
  exact hReplace hred hwfBound' hwfBody'

/-- Body-replacement payload from the direct top-level `.sub` replacement
residual package. -/
noncomputable def MEqRedFunBodyReplacePayload.of_direct_sub_payloads
    (hPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new) :
    MEqRedFunBodyReplacePayload :=
  MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hPayloads)

/-- Body-replacement payload from immediate top-level `.sub` replacement
residuals plus the named preserved-head replacement payload. -/
noncomputable def MEqRedFunBodyReplacePayload.of_immediate_sub_payloads_and_under
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new) :
    MEqRedFunBodyReplacePayload :=
  MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hPayloads)

/-- Sub-replacement entry point for the typed-`FOp` direct split-beta
machine assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons
    hSubst hAppend hBridge hInv hBetaBody hFOpBody hTargetApp hTailCons
    (MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf hReplace) hNoTop

/-- Sub-replacement entry point for the typed-`FOp` direct split-beta
machine assembly, with the control-left residual still exposed through the
older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_sub_replace
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hTargetApp hTailCons hReplace hNoTop

/-- Sub-replacement entry point for the native-`FOp` direct split-beta
machine assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons
    hSubst hAppend hBridge hInv hBetaBody hFOpBody hTargetApp hTailCons
    (MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf hReplace) hNoTop

/-- Sub-replacement entry point for the native-`FOp` direct split-beta
machine assembly, with the control-left residual still exposed through the
older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons_sub_replace
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hTargetApp hTailCons hReplace hNoTop

/-- Typed-operator sub-replacement entry point for the typed-`FOp` direct
split-beta machine assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_operator_machine_tail_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_operator_machine_tail
    hSubst hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf hReplace) hNoTop

/-- Typed-operator sub-replacement entry point for the typed-`FOp` direct
split-beta machine assembly, with the control-left residual still exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_operator_machine_tail_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_operator_machine_tail_sub_replace
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hReplace hNoTop

/-- Machine-operator sub-replacement entry point for the typed-`FOp` direct
split-beta machine assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_machine_operator_machine_tail_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_machine_operator_machine_tail
    hSubst hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf hReplace) hNoTop

/-- Machine-operator sub-replacement entry point for the typed-`FOp` direct
split-beta machine assembly, with the control-left residual still exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_machine_operator_machine_tail_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_machine_operator_machine_tail_sub_replace
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hReplace hNoTop

/-- Typed-operator sub-replacement entry point for the native-`FOp` direct
split-beta machine assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_operator_machine_tail_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_operator_machine_tail
    hSubst hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf hReplace) hNoTop

/-- Typed-operator sub-replacement entry point for the native-`FOp` direct
split-beta machine assembly, with the control-left residual still exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_operator_machine_tail_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_operator_machine_tail_sub_replace
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hReplace hNoTop

/-- Machine-operator sub-replacement entry point for the native-`FOp` direct
split-beta machine assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_machine_operator_machine_tail_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_machine_operator_machine_tail
    hSubst hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf hReplace) hNoTop

/-- Machine-operator sub-replacement entry point for the native-`FOp` direct
split-beta machine assembly, with the control-left residual still exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_machine_operator_machine_tail_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_machine_operator_machine_tail_sub_replace
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hReplace hNoTop

/-- External-empty sub-replacement entry point for the typed-`FOp` direct
split-beta target-application assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hTargetApp hTailCons
    (MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf hReplace) hNoTop

/-- External-empty sub-replacement entry point for the typed-`FOp` direct
split-beta target-application assembly, with stack append exposed through the
older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_sub_replace
    hSubst hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hTargetApp hTailCons hReplace hNoTop

/-- External-empty sub-replacement entry point for the native-`FOp` direct
split-beta target-application assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_target_app_machine_tail_cons_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_target_app_machine_tail_cons
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hTargetApp hTailCons
    (MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf hReplace) hNoTop

/-- External-empty sub-replacement entry point for the native-`FOp` direct
split-beta target-application assembly, with stack append exposed through the
older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_target_app_machine_tail_cons_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_target_app_machine_tail_cons_sub_replace
    hSubst hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hTargetApp hTailCons hReplace hNoTop

/-- External-empty typed-operator sub-replacement entry point for the
typed-`FOp` direct split-beta assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_operator_machine_tail_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_operator_machine_tail
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf hReplace) hNoTop

/-- External-empty typed-operator sub-replacement entry point for the
typed-`FOp` direct split-beta assembly, with stack append exposed through the
older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_operator_machine_tail_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_operator_machine_tail_sub_replace
    hSubst hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hReplace hNoTop

/-- External-empty machine-operator sub-replacement entry point for the
typed-`FOp` direct split-beta assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_machine_operator_machine_tail_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_machine_operator_machine_tail
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf hReplace) hNoTop

/-- External-empty machine-operator sub-replacement entry point for the
typed-`FOp` direct split-beta assembly, with stack append exposed through the
older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_machine_operator_machine_tail_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_machine_operator_machine_tail_sub_replace
    hSubst hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hReplace hNoTop

/-- External-empty typed-operator sub-replacement entry point for the
native-`FOp` direct split-beta assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_operator_machine_tail_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_operator_machine_tail
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf hReplace) hNoTop

/-- External-empty typed-operator sub-replacement entry point for the
native-`FOp` direct split-beta assembly, with stack append exposed through the
older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_operator_machine_tail_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_operator_machine_tail_sub_replace
    hSubst hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hReplace hNoTop

/-- External-empty machine-operator sub-replacement entry point for the
native-`FOp` direct split-beta assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_machine_operator_machine_tail_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_machine_operator_machine_tail
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf hReplace) hNoTop

/-- External-empty machine-operator sub-replacement entry point for the
native-`FOp` direct split-beta assembly, with stack append exposed through the
older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_machine_operator_machine_tail_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_machine_operator_machine_tail_sub_replace
    hSubst hEmpty
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hBetaBody hFOpBody hOpFun hTail hReplace hNoTop

/-- External-empty contextual entry point for the typed-`FOp` direct
split-beta target-application assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_sub_replace
    hSubst
    (MEqRedPreservesWfMUnderWfCtx.of_contextual hCtx)
    hAppend hBridge hInv
    (MEqRedBetaBodyPreservesWfMPayload.of_contextual hCtx)
    (MEqRedFOpBodyTypedPayload.of_head_transports hCtx hSubToEqu hEquToSub)
    hTargetApp hTailCons hReplace hNoTop

/-- External-empty contextual entry point for the typed-`FOp` direct
split-beta target-application assembly, with stack append exposed through the
older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_contextual
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hCtx hSubToEqu hEquToSub
    hTargetApp hTailCons hReplace hNoTop

/-- External-empty contextual entry point for the native-`FOp` direct
split-beta target-application assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_target_app_machine_tail_cons_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_contextual
    hSubst hAppend hBridge hInv hCtx hSubToEqu hEquToSub
    hTargetApp hTailCons hReplace hNoTop

/-- External-empty contextual entry point for the native-`FOp` direct
split-beta target-application assembly, with stack append exposed through the
older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_target_app_machine_tail_cons_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_target_app_machine_tail_cons_contextual
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hCtx hSubToEqu hEquToSub
    hTargetApp hTailCons hReplace hNoTop

/-- External-empty typed-operator contextual entry point for the typed-`FOp`
direct split-beta assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_operator_machine_tail_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_contextual
    hSubst hAppend hBridge hInv hCtx hSubToEqu hEquToSub
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_typed_operator hOpFun hTail)
    hReplace hNoTop

/-- External-empty typed-operator contextual entry point for the typed-`FOp`
direct split-beta assembly, with stack append exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_operator_machine_tail_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_operator_machine_tail_contextual
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hCtx hSubToEqu hEquToSub hOpFun hTail hReplace hNoTop

/-- External-empty machine-operator contextual entry point for the typed-`FOp`
direct split-beta assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_machine_operator_machine_tail_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_contextual
    hSubst hAppend hBridge hInv hCtx hSubToEqu hEquToSub
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_machine_operator hOpFun hTail)
    hReplace hNoTop

/-- External-empty machine-operator contextual entry point for the typed-`FOp`
direct split-beta assembly, with stack append exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_machine_operator_machine_tail_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_machine_operator_machine_tail_contextual
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hCtx hSubToEqu hEquToSub hOpFun hTail hReplace hNoTop

/-- External-empty typed-operator contextual entry point for the native-`FOp`
direct split-beta assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_operator_machine_tail_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_target_app_machine_tail_cons_contextual
    hSubst hAppend hBridge hInv hCtx hSubToEqu hEquToSub
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_typed_operator hOpFun hTail)
    hReplace hNoTop

/-- External-empty typed-operator contextual entry point for the native-`FOp`
direct split-beta assembly, with stack append exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_operator_machine_tail_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_operator_machine_tail_contextual
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hCtx hSubToEqu hEquToSub hOpFun hTail hReplace hNoTop

/-- External-empty machine-operator contextual entry point for the native-`FOp`
direct split-beta assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_machine_operator_machine_tail_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_target_app_machine_tail_cons_contextual
    hSubst hAppend hBridge hInv hCtx hSubToEqu hEquToSub
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_machine_operator hOpFun hTail)
    hReplace hNoTop

/-- External-empty machine-operator contextual entry point for the native-`FOp`
direct split-beta assembly, with stack append exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_machine_operator_machine_tail_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_machine_operator_machine_tail_contextual
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hCtx hSubToEqu hEquToSub hOpFun hTail hReplace hNoTop

/-- Contextual-preservation entry point for the typed-`FOp` direct split-beta
machine assembly. The contextual preservation payload supplies the beta body
preservation residual, while the directional `Me-FOp` head transports supply
the typed body residual. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_sub_replace
    hSubst hAppend hBridge hInv
    (MEqRedBetaBodyPreservesWfMPayload.of_contextual hCtx)
    (MEqRedFOpBodyTypedPayload.of_head_transports hCtx hSubToEqu hEquToSub)
    hTargetApp hTailCons hReplace hNoTop

/-- Contextual-preservation entry point for the typed-`FOp` direct split-beta
machine assembly, with the control-left residual still exposed through the
older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_contextual
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hCtx hSubToEqu hEquToSub
    hTargetApp hTailCons hReplace hNoTop

/-- Contextual-preservation entry point for the native-`FOp` direct
split-beta machine assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_contextual
    hSubst hAppend hBridge hInv hCtx hSubToEqu hEquToSub
    hTargetApp hTailCons hReplace hNoTop

/-- Contextual-preservation entry point for the native-`FOp` direct
split-beta machine assembly, with the control-left residual still exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons_contextual
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hCtx hSubToEqu hEquToSub
    hTargetApp hTailCons hReplace hNoTop

/-- Typed-operator contextual entry point for the typed-`FOp` direct
split-beta machine assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_operator_machine_tail_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_contextual
    hSubst hAppend hBridge hInv hCtx hSubToEqu hEquToSub
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_typed_operator hOpFun hTail)
    hReplace hNoTop

/-- Typed-operator contextual entry point for the typed-`FOp` direct
split-beta machine assembly, with the control-left residual still exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_operator_machine_tail_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_operator_machine_tail_contextual
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hCtx hSubToEqu hEquToSub hOpFun hTail hReplace hNoTop

/-- Machine-operator contextual entry point for the typed-`FOp` direct
split-beta machine assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_machine_operator_machine_tail_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_contextual
    hSubst hAppend hBridge hInv hCtx hSubToEqu hEquToSub
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_machine_operator hOpFun hTail)
    hReplace hNoTop

/-- Machine-operator contextual entry point for the typed-`FOp` direct
split-beta machine assembly, with the control-left residual still exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_machine_operator_machine_tail_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_machine_operator_machine_tail_contextual
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hCtx hSubToEqu hEquToSub hOpFun hTail hReplace hNoTop

/-- Typed-operator contextual entry point for the native-`FOp` direct
split-beta machine assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_operator_machine_tail_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons_contextual
    hSubst hAppend hBridge hInv hCtx hSubToEqu hEquToSub
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_typed_operator hOpFun hTail)
    hReplace hNoTop

/-- Typed-operator contextual entry point for the native-`FOp` direct
split-beta machine assembly, with the control-left residual still exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_operator_machine_tail_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_operator_machine_tail_contextual
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hCtx hSubToEqu hEquToSub hOpFun hTail hReplace hNoTop

/-- Machine-operator contextual entry point for the native-`FOp` direct
split-beta machine assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_machine_operator_machine_tail_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons_contextual
    hSubst hAppend hBridge hInv hCtx hSubToEqu hEquToSub
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_machine_operator hOpFun hTail)
    hReplace hNoTop

/-- Machine-operator contextual entry point for the native-`FOp` direct
split-beta machine assembly, with the control-left residual still exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_machine_operator_machine_tail_contextual
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hCtx : MEqRedPreservesWfMContextual)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_machine_operator_machine_tail_contextual
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hInv hCtx hSubToEqu hEquToSub hOpFun hTail hReplace hNoTop

/-- `Me-Fun` well-formedness preservation using the existing sharpened
`.sub` head replacement payload. -/
noncomputable def MEqRed.fun_preservesWfM_of_sub_head_replace
    (hpres : MEqRedPreservesWfMContextual)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    {Γ : Ctx} {bound bound' body body' : Term}
    (hΓ : WfCtxEqu Γ)
    (hredBound : MEqRed Γ [] bound bound')
    (hredBody : MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body')
    (hwfAbs : WfM Γ (.abs bound body)) :
    WfM Γ (.abs bound' body') :=
  MEqRed.fun_preservesWfM_of_contextual hpres
    (MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf hReplace)
    hΓ hredBound hredBody hwfAbs

/-- `Me-Fun` well-formedness preservation from direct `.sub` replacement
residual payloads. -/
noncomputable def MEqRed.fun_preservesWfM_of_direct_sub_payloads
    (hpres : MEqRedPreservesWfMContextual)
    (hPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    {Γ : Ctx} {bound bound' body body' : Term}
    (hΓ : WfCtxEqu Γ)
    (hredBound : MEqRed Γ [] bound bound')
    (hredBody : MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body')
    (hwfAbs : WfM Γ (.abs bound body)) :
    WfM Γ (.abs bound' body') :=
  MEqRed.fun_preservesWfM_of_contextual hpres
    (MEqRedFunBodyReplacePayload.of_direct_sub_payloads hPayloads)
    hΓ hredBound hredBody hwfAbs

/-- `Me-Fun` well-formedness preservation from immediate top-level `.sub`
replacement residuals plus the named preserved-head replacement payload. -/
noncomputable def MEqRed.fun_preservesWfM_of_immediate_sub_payloads_and_under
    (hpres : MEqRedPreservesWfMContextual)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    {Γ : Ctx} {bound bound' body body' : Term}
    (hΓ : WfCtxEqu Γ)
    (hredBound : MEqRed Γ [] bound bound')
    (hredBody : MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body')
    (hwfAbs : WfM Γ (.abs bound body)) :
    WfM Γ (.abs bound' body') :=
  MEqRed.fun_preservesWfM_of_contextual hpres
    (MEqRedFunBodyReplacePayload.of_immediate_sub_payloads_and_under
      hUnder hPayloads)
    hΓ hredBound hredBody hwfAbs

/-- Contextual `MEqRed` well-formedness preservation assembled from the
remaining constructor payloads, using the existing sharpened `.sub` head
replacement payload for `Me-Fun`. -/
noncomputable def MEqRedPreservesWfMContextual.of_components_and_sub_replace
    (hBeta : MEqRedBetaPreservesWfMContextual)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components hBeta hOpFun
    (MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf hReplace)
    hFOpBody

/-- Contextual `MEqRed` well-formedness preservation assembled from the
remaining constructor payloads, using direct `.sub` replacement residuals for
`Me-Fun`. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_components_and_direct_sub_payloads
    (hBeta : MEqRedBetaPreservesWfMContextual)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components hBeta hOpFun
    (MEqRedFunBodyReplacePayload.of_direct_sub_payloads hSubPayloads)
    hFOpBody

/-- Contextual `MEqRed` well-formedness preservation assembled from the
remaining constructor payloads, using immediate top-level `.sub` replacement
residuals plus the named preserved-head replacement payload for `Me-Fun`. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_components_and_immediate_sub_payloads_and_under
    (hBeta : MEqRedBetaPreservesWfMContextual)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components hBeta hOpFun
    (MEqRedFunBodyReplacePayload.of_immediate_sub_payloads_and_under
      hUnder hSubPayloads)
    hFOpBody

/-- Contextual `MEqRed` well-formedness preservation with the β constructor
proved from the ordinary β-instantiation lemma and function-bound inversion.
The remaining constructor-specific residuals are the stack-indexed
application-operator and `Me-FOp` body bridges, plus the `Me-Fun` body
replacement bridge. -/
noncomputable def MEqRedPreservesWfMContextual.of_components_no_beta
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversion)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual := by
  intro Γ s x y hΓ hStack hred hwf
  revert hΓ hStack hwf
  induction hred with
  | pro hpv hb hred ih =>
      intro hΓ hStack hwf
      have hwfα := WfCtxEqu.lookup_equ hΓ hwf.prevalid hb
      exact ih hΓ hStack hwfα
  | @bet Γβ sβ bound arg arg' body body' ht hBody hArg ihBody ihArg =>
      intro hΓ hStack hwf
      obtain ⟨result, hFun, hArgTyping⟩ := hwf.app_inv
      have hwfAbs : WfM Γβ (.abs bound body) := hFun.wf_left
      have hwfBound : WfM Γβ bound := hwfAbs.fun_inv.1
      have hwfBody : WfM ({ bound := bound, kind := .sub } :: Γβ) body :=
        hwfAbs.fun_inv.2
      have hwfBody' :
          WfM ({ bound := bound, kind := .sub } :: Γβ) body' :=
        ihBody (WfCtxEqu.sub hΓ)
          (WfStack.weaken_sub_head hStack hwfBound) hwfBody
      have hwfArg : WfM Γβ arg := hArgTyping.wf_left
      have hwfArg' : WfM Γβ arg' := ihArg hΓ WfStack.nil hwfArg
      have hArgBack : WSubMStar Γβ arg' arg :=
        WSubMStar.of_MEqRed_back hArg hwfArg hwfArg'
      have hArgResult : WSubMStar Γβ arg' result :=
        WSubMStar.trans hwfArg hArgBack hArgTyping
      have hEquBoundResult : WEquMStar Γβ bound result := hInv hFun
      have hSubResultBound : WSubMStar Γβ result bound :=
        hEquBoundResult.symm.toWSubMStar
      have hArgBound : WSubMStar Γβ arg' bound :=
        WSubMStar.trans hArgTyping.wf_right hArgResult hSubResultBound
      exact hSubst hArgBound hwfBody'
  | top hpv =>
      intro hΓ hStack hwf
      exact MEqRed.top_preservesWfM hpv hwf
  | app hOp hArg _ihOp ihArg =>
      intro hΓ hStack hwf
      obtain ⟨bound, hFun, hArgTyping⟩ := hwf.app_inv
      have hwfV := hArgTyping.wf_left
      have hwfV' := ihArg hΓ WfStack.nil hwfV
      have hFun' :=
        hOpFun hΓ hStack hwfV hFun hOp
      have hArgBack :=
        WSubMStar.of_MEqRed_back hArg hwfV hwfV'
      have hArgTyping' :=
        WSubMStar.trans hwfV hArgBack hArgTyping
      exact WfM.app hFun' hArgTyping'
  | var hpv hi =>
      intro hΓ hStack hwf
      exact MEqRed.var_preservesWfM hpv hi hwf
  | fun_ hBound hBody ihBound ihBody =>
      intro hΓ hStack hwf
      have hwfBound := hwf.fun_inv.1
      have hwfBody :=
        hwf.fun_inv.2
      have hwfBound' := ihBound hΓ WfStack.nil hwfBound
      have hwfBodyOld :=
        ihBody (WfCtxEqu.sub hΓ) WfStack.nil hwfBody
      exact WfM.fun_ hwfBound'
        (hFunBody hΓ hwfBound hwfBound' hBound hwfBodyOld)
  | tAp hpv hu =>
      intro hΓ hStack hwf
      exact MEqRed.tAp_preservesWfM hpv hu hwf
  | fOp hBound hOperand hBody ihBound _ihBody =>
      intro hΓ hStack hwf
      have hwfOperand := WfStack.head hStack
      have hStackTail := WfStack.tail hStack
      have hwfBound := hwf.fun_inv.1
      have hwfBody :=
        hwf.fun_inv.2
      have hwfBound' := ihBound hΓ WfStack.nil hwfBound
      exact WfM.fun_ hwfBound'
        (hFOpBody hΓ hStackTail hwfBound hwfBound' hwfOperand
          hwfBody hBound hBody)

/-- Contextual `MEqRed` well-formedness preservation with the β constructor
proved from a function-bound inversion payload that is only required under
`WfCtxEqu`. This is the sharper form for contextual preservation. -/
noncomputable def MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual := by
  intro Γ s x y hΓ hStack hred hwf
  revert hΓ hStack hwf
  induction hred with
  | pro hpv hb hred ih =>
      intro hΓ hStack hwf
      have hwfα := WfCtxEqu.lookup_equ hΓ hwf.prevalid hb
      exact ih hΓ hStack hwfα
  | @bet Γβ sβ bound arg arg' body body' ht hBody hArg ihBody ihArg =>
      intro hΓ hStack hwf
      obtain ⟨result, hFun, hArgTyping⟩ := hwf.app_inv
      have hwfAbs : WfM Γβ (.abs bound body) := hFun.wf_left
      have hwfBound : WfM Γβ bound := hwfAbs.fun_inv.1
      have hwfBody : WfM ({ bound := bound, kind := .sub } :: Γβ) body :=
        hwfAbs.fun_inv.2
      have hwfBody' :
          WfM ({ bound := bound, kind := .sub } :: Γβ) body' :=
        ihBody (WfCtxEqu.sub hΓ)
          (WfStack.weaken_sub_head hStack hwfBound) hwfBody
      have hwfArg : WfM Γβ arg := hArgTyping.wf_left
      have hwfArg' : WfM Γβ arg' := ihArg hΓ WfStack.nil hwfArg
      have hArgBack : WSubMStar Γβ arg' arg :=
        WSubMStar.of_MEqRed_back hArg hwfArg hwfArg'
      have hArgResult : WSubMStar Γβ arg' result :=
        WSubMStar.trans hwfArg hArgBack hArgTyping
      have hEquBoundResult : WEquMStar Γβ bound result := hInv hΓ hFun
      have hSubResultBound : WSubMStar Γβ result bound :=
        hEquBoundResult.symm.toWSubMStar
      have hArgBound : WSubMStar Γβ arg' bound :=
        WSubMStar.trans hArgTyping.wf_right hArgResult hSubResultBound
      exact hSubst hArgBound hwfBody'
  | top hpv =>
      intro hΓ hStack hwf
      exact MEqRed.top_preservesWfM hpv hwf
  | app hOp hArg _ihOp ihArg =>
      intro hΓ hStack hwf
      obtain ⟨bound, hFun, hArgTyping⟩ := hwf.app_inv
      have hwfV := hArgTyping.wf_left
      have hwfV' := ihArg hΓ WfStack.nil hwfV
      have hFun' :=
        hOpFun hΓ hStack hwfV hFun hOp
      have hArgBack :=
        WSubMStar.of_MEqRed_back hArg hwfV hwfV'
      have hArgTyping' :=
        WSubMStar.trans hwfV hArgBack hArgTyping
      exact WfM.app hFun' hArgTyping'
  | var hpv hi =>
      intro hΓ hStack hwf
      exact MEqRed.var_preservesWfM hpv hi hwf
  | fun_ hBound hBody ihBound ihBody =>
      intro hΓ hStack hwf
      have hwfBound := hwf.fun_inv.1
      have hwfBody :=
        hwf.fun_inv.2
      have hwfBound' := ihBound hΓ WfStack.nil hwfBound
      have hwfBodyOld :=
        ihBody (WfCtxEqu.sub hΓ) WfStack.nil hwfBody
      exact WfM.fun_ hwfBound'
        (hFunBody hΓ hwfBound hwfBound' hBound hwfBodyOld)
  | tAp hpv hu =>
      intro hΓ hStack hwf
      exact MEqRed.tAp_preservesWfM hpv hu hwf
  | fOp hBound hOperand hBody ihBound _ihBody =>
      intro hΓ hStack hwf
      have hwfOperand := WfStack.head hStack
      have hStackTail := WfStack.tail hStack
      have hwfBound := hwf.fun_inv.1
      have hwfBody :=
        hwf.fun_inv.2
      have hwfBound' := ihBound hΓ WfStack.nil hwfBound
      exact WfM.fun_ hwfBound'
        (hFOpBody hΓ hStackTail hwfBound hwfBound' hwfOperand
          hwfBody hBound hBody)

/-- Contextual `MEqRed` well-formedness preservation with β proved from
function-bound inversion under `WfCtxEqu`, native `Me-App` operator
transport, native `Me-Fun` body replacement, and the `Me-FOp` bridge factored
into the two directional head/body transports. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_head_transports
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual := by
  intro Γ s x y hΓ hStack hred hwf
  revert hΓ hStack hwf
  induction hred with
  | pro hpv hb hred ih =>
      intro hΓ hStack hwf
      have hwfα := WfCtxEqu.lookup_equ hΓ hwf.prevalid hb
      exact ih hΓ hStack hwfα
  | @bet Γβ sβ bound arg arg' body body' ht hBody hArg ihBody ihArg =>
      intro hΓ hStack hwf
      obtain ⟨result, hFun, hArgTyping⟩ := hwf.app_inv
      have hwfAbs : WfM Γβ (.abs bound body) := hFun.wf_left
      have hwfBound : WfM Γβ bound := hwfAbs.fun_inv.1
      have hwfBody : WfM ({ bound := bound, kind := .sub } :: Γβ) body :=
        hwfAbs.fun_inv.2
      have hwfBody' :
          WfM ({ bound := bound, kind := .sub } :: Γβ) body' :=
        ihBody (WfCtxEqu.sub hΓ)
          (WfStack.weaken_sub_head hStack hwfBound) hwfBody
      have hwfArg : WfM Γβ arg := hArgTyping.wf_left
      have hwfArg' : WfM Γβ arg' := ihArg hΓ WfStack.nil hwfArg
      have hArgBack : WSubMStar Γβ arg' arg :=
        WSubMStar.of_MEqRed_back hArg hwfArg hwfArg'
      have hArgResult : WSubMStar Γβ arg' result :=
        WSubMStar.trans hwfArg hArgBack hArgTyping
      have hEquBoundResult : WEquMStar Γβ bound result := hInv hΓ hFun
      have hSubResultBound : WSubMStar Γβ result bound :=
        hEquBoundResult.symm.toWSubMStar
      have hArgBound : WSubMStar Γβ arg' bound :=
        WSubMStar.trans hArgTyping.wf_right hArgResult hSubResultBound
      exact hSubst hArgBound hwfBody'
  | top hpv =>
      intro hΓ hStack hwf
      exact MEqRed.top_preservesWfM hpv hwf
  | app hOp hArg _ihOp ihArg =>
      intro hΓ hStack hwf
      obtain ⟨bound, hFun, hArgTyping⟩ := hwf.app_inv
      have hwfV := hArgTyping.wf_left
      have hwfV' := ihArg hΓ WfStack.nil hwfV
      have hFun' :=
        hOpFun hΓ hStack hwfV hFun hOp
      have hArgBack :=
        WSubMStar.of_MEqRed_back hArg hwfV hwfV'
      have hArgTyping' :=
        WSubMStar.trans hwfV hArgBack hArgTyping
      exact WfM.app hFun' hArgTyping'
  | var hpv hi =>
      intro hΓ hStack hwf
      exact MEqRed.var_preservesWfM hpv hi hwf
  | fun_ hBound hBody ihBound ihBody =>
      intro hΓ hStack hwf
      have hwfBound := hwf.fun_inv.1
      have hwfBody :=
        hwf.fun_inv.2
      have hwfBound' := ihBound hΓ WfStack.nil hwfBound
      have hwfBodyOld :=
        ihBody (WfCtxEqu.sub hΓ) WfStack.nil hwfBody
      exact WfM.fun_ hwfBound'
        (hFunBody hΓ hwfBound hwfBound' hBound hwfBodyOld)
  | tAp hpv hu =>
      intro hΓ hStack hwf
      exact MEqRed.tAp_preservesWfM hpv hu hwf
  | @fOp Γf sf bound bound' operand body body' hBound hOperand hBody ihBound ihBody =>
      intro hΓ hStack hwf
      have hwfOperand := WfStack.head hStack
      have hStackTail := WfStack.tail hStack
      have hΓEqu : WfCtxEqu ({ bound := operand, kind := .equ } :: Γf) :=
        WfCtxEqu.equ hΓ hwfOperand
      have hStackEqu :=
        WfStack.weaken_equ_head hStackTail hwfOperand
      have hwfBound := hwf.fun_inv.1
      have hwfBody :=
        hwf.fun_inv.2
      have hwfBodyEqu :=
        hSubToEqu hΓ hwfBound hwfOperand hwfBody
      have hwfBody'Equ :=
        ihBody hΓEqu hStackEqu hwfBodyEqu
      have hwfBound' := ihBound hΓ WfStack.nil hwfBound
      exact WfM.fun_ hwfBound'
        (hEquToSub hΓ hwfOperand hwfBound' hwfBody'Equ)

/-- Variant of
`MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_head_transports`
using the sharpened `.sub` head replacement payload for `Me-Fun`. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_sub_replace_and_head_transports
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_head_transports
    hSubst hInv hOpFun
    (MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf hReplace)
    hSubToEqu hEquToSub

/-- Variant of
`MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_head_transports`
using direct `.sub` replacement residual payloads for `Me-Fun`. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_direct_sub_payloads_and_head_transports
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_sub_replace_and_head_transports
    hSubst hInv hOpFun
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)
    hSubToEqu hEquToSub

/-- Variant of
`MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_head_transports`
using immediate top-level `.sub` replacement residuals plus the named
preserved-head replacement payload for `Me-Fun`. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_immediate_sub_payloads_and_under_and_head_transports
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_sub_replace_and_head_transports
    hSubst hInv hOpFun
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hSubToEqu hEquToSub

/-- Split-residual contextual preservation using the native `Me-App`
operator payload and one uniform head-kind/body transport payload for
`Me-FOp`. This is retained as a diagnostic assembly route; the uniform
head-kind premise is refutable under the no-Top-function-supertype
obstruction. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_head_kind_transport
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hHeadTransport : WfMHeadKindTransportPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_head_transports
    hSubst hInv hOpFun hFunBody
    (WfMSubHeadToEquHeadPayload.of_head_kind_transport hHeadTransport)
    (WfMEquHeadToSubHeadPayload.of_head_kind_transport hHeadTransport)

/-- Split-residual contextual preservation using the native `Me-App`
operator payload, sharpened `.sub` head replacement for `Me-Fun`, and one
uniform head-kind/body transport payload for `Me-FOp`. This is retained as a
diagnostic assembly route; the uniform head-kind premise is refutable under
the no-Top-function-supertype obstruction. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_sub_replace_and_head_kind_transport
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hHeadTransport : WfMHeadKindTransportPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_sub_replace_and_head_transports
    hSubst hInv hOpFun hReplace
    (WfMSubHeadToEquHeadPayload.of_head_kind_transport hHeadTransport)
    (WfMEquHeadToSubHeadPayload.of_head_kind_transport hHeadTransport)

/-- Contextual `MEqRed` well-formedness preservation with β, `Me-App`, and
`Me-FOp` factored through reusable endpoint/head-transport payloads. This is
the fully factored route: compared with the split assemblers above, it also
replaces the native `Me-App` operator payload by stacked left-endpoint
transport for well-subtyping. -/
noncomputable def MEqRedPreservesWfMContextual.of_factored_components_no_beta
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual := by
  intro Γ s x y hΓ hStack hred hwf
  revert hΓ hStack hwf
  induction hred with
  | pro hpv hb hred ih =>
      intro hΓ hStack hwf
      have hwfα := WfCtxEqu.lookup_equ hΓ hwf.prevalid hb
      exact ih hΓ hStack hwfα
  | @bet Γβ sβ bound arg arg' body body' ht hBody hArg ihBody ihArg =>
      intro hΓ hStack hwf
      obtain ⟨result, hFun, hArgTyping⟩ := hwf.app_inv
      have hwfAbs : WfM Γβ (.abs bound body) := hFun.wf_left
      have hwfBound : WfM Γβ bound := hwfAbs.fun_inv.1
      have hwfBody : WfM ({ bound := bound, kind := .sub } :: Γβ) body :=
        hwfAbs.fun_inv.2
      have hwfBody' :
          WfM ({ bound := bound, kind := .sub } :: Γβ) body' :=
        ihBody (WfCtxEqu.sub hΓ)
          (WfStack.weaken_sub_head hStack hwfBound) hwfBody
      have hwfArg : WfM Γβ arg := hArgTyping.wf_left
      have hwfArg' : WfM Γβ arg' := ihArg hΓ WfStack.nil hwfArg
      have hArgBack : WSubMStar Γβ arg' arg :=
        WSubMStar.of_MEqRed_back hArg hwfArg hwfArg'
      have hArgResult : WSubMStar Γβ arg' result :=
        WSubMStar.trans hwfArg hArgBack hArgTyping
      have hEquBoundResult : WEquMStar Γβ bound result := hInv hΓ hFun
      have hSubResultBound : WSubMStar Γβ result bound :=
        hEquBoundResult.symm.toWSubMStar
      have hArgBound : WSubMStar Γβ arg' bound :=
        WSubMStar.trans hArgTyping.wf_right hArgResult hSubResultBound
      exact hSubst hArgBound hwfBody'
  | top hpv =>
      intro hΓ hStack hwf
      exact MEqRed.top_preservesWfM hpv hwf
  | app hOp hArg _ihOp ihArg =>
      intro hΓ hStack hwf
      obtain ⟨bound, hFun, hArgTyping⟩ := hwf.app_inv
      have hwfV := hArgTyping.wf_left
      have hwfV' := ihArg hΓ WfStack.nil hwfV
      have hFun' :=
        hLeft hΓ (WfStack.cons hwfV hStack) hFun hOp
      have hArgBack :=
        WSubMStar.of_MEqRed_back hArg hwfV hwfV'
      have hArgTyping' :=
        WSubMStar.trans hwfV hArgBack hArgTyping
      exact WfM.app hFun' hArgTyping'
  | var hpv hi =>
      intro hΓ hStack hwf
      exact MEqRed.var_preservesWfM hpv hi hwf
  | fun_ hBound hBody ihBound ihBody =>
      intro hΓ hStack hwf
      have hwfBound := hwf.fun_inv.1
      have hwfBody :=
        hwf.fun_inv.2
      have hwfBound' := ihBound hΓ WfStack.nil hwfBound
      have hwfBodyOld :=
        ihBody (WfCtxEqu.sub hΓ) WfStack.nil hwfBody
      exact WfM.fun_ hwfBound'
        (hFunBody hΓ hwfBound hwfBound' hBound hwfBodyOld)
  | tAp hpv hu =>
      intro hΓ hStack hwf
      exact MEqRed.tAp_preservesWfM hpv hu hwf
  | @fOp Γf sf bound bound' operand body body' hBound hOperand hBody ihBound ihBody =>
      intro hΓ hStack hwf
      have hwfOperand := WfStack.head hStack
      have hStackTail := WfStack.tail hStack
      have hΓEqu : WfCtxEqu ({ bound := operand, kind := .equ } :: Γf) :=
        WfCtxEqu.equ hΓ hwfOperand
      have hStackEqu :=
        WfStack.weaken_equ_head hStackTail hwfOperand
      have hwfBound := hwf.fun_inv.1
      have hwfBody :=
        hwf.fun_inv.2
      have hwfBodyEqu :=
        hSubToEqu hΓ hwfBound hwfOperand hwfBody
      have hwfBody'Equ :=
        ihBody hΓEqu hStackEqu hwfBodyEqu
      have hwfBound' := ihBound hΓ WfStack.nil hwfBound
      exact WfM.fun_ hwfBound'
        (hEquToSub hΓ hwfOperand hwfBound' hwfBody'Equ)

/-- Factored contextual preservation using the existing sharpened `.sub`
head replacement payload for `Me-Fun`. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_factored_components_no_beta_and_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_factored_components_no_beta hSubst hInv
    hLeft (MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf hReplace)
    hSubToEqu hEquToSub

/-- Factored contextual preservation using direct `.sub` replacement
residual payloads for `Me-Fun`. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_factored_components_no_beta_and_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_factored_components_no_beta_and_sub_replace
    hSubst hInv hLeft
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)
    hSubToEqu hEquToSub

/-- Factored contextual preservation using immediate top-level `.sub`
replacement residuals plus the named preserved-head replacement payload for
`Me-Fun`. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_factored_components_no_beta_and_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_factored_components_no_beta_and_sub_replace
    hSubst hInv hLeft
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hSubToEqu hEquToSub

/-- Factored contextual preservation using one uniform head-kind transport
payload for both `Me-FOp` body transport directions. This is retained as a
diagnostic assembly route; the uniform head-kind premise is refutable under
the no-Top-function-supertype obstruction. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_factored_components_no_beta_and_head_kind_transport
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hHeadTransport : WfMHeadKindTransportPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_factored_components_no_beta hSubst hInv
    hLeft hFunBody
    (WfMSubHeadToEquHeadPayload.of_head_kind_transport hHeadTransport)
    (WfMEquHeadToSubHeadPayload.of_head_kind_transport hHeadTransport)

/-- Factored contextual preservation using sharpened `.sub` head replacement
for `Me-Fun` and one uniform head-kind transport payload for `Me-FOp`. This
is retained as a diagnostic assembly route; the uniform head-kind premise is
refutable under the no-Top-function-supertype obstruction. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_factored_components_no_beta_and_sub_replace_and_head_kind_transport
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hHeadTransport : WfMHeadKindTransportPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_factored_components_no_beta_and_sub_replace
    hSubst hInv hLeft hReplace
    (WfMSubHeadToEquHeadPayload.of_head_kind_transport hHeadTransport)
    (WfMEquHeadToSubHeadPayload.of_head_kind_transport hHeadTransport)

/-- Contextual `MEqRed` well-formedness preservation assembled without a
separate β residual, using the existing sharpened `.sub` head replacement
payload for `Me-Fun`. -/
noncomputable def MEqRedPreservesWfMContextual.of_components_no_beta_and_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversion)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta hSubst hInv hOpFun
    (MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf hReplace)
    hFOpBody

/-- Contextual `MEqRed` preservation assembled without a separate β
residual, using direct `.sub` replacement residual payloads for `Me-Fun`. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_components_no_beta_and_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversion)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta_and_sub_replace
    hSubst hInv hOpFun
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)
    hFOpBody

/-- Contextual `MEqRed` preservation assembled without a separate β
residual, using immediate top-level `.sub` replacement residuals plus the
named preserved-head replacement payload for `Me-Fun`. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_components_no_beta_and_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversion)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta_and_sub_replace
    hSubst hInv hOpFun
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hFOpBody

/-- Contextual `MEqRed` well-formedness preservation assembled from the
well-formed-context function-bound inversion payload and the sharpened `.sub`
head replacement payload, with the β case proved internally. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv hSubst
    hInv hOpFun
    (MEqRedFunBodyReplacePayload.of_sub_head_replace_new_wf hReplace)
    hFOpBody

/-- Contextual `MEqRed` preservation assembled from well-formed-context
function-bound inversion and direct `.sub` replacement residual payloads. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_sub_replace
    hSubst hInv hOpFun
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)
    hFOpBody

/-- Contextual `MEqRed` preservation assembled from well-formed-context
function-bound inversion, immediate top-level `.sub` replacement residuals,
and the named preserved-head replacement payload. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_sub_replace
    hSubst hInv hOpFun
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hFOpBody

/-- Contextual `MEqRed` preservation assembled without a separate β residual,
using a Type-valued function-bound chain diagram instead of a raw
function-bound inversion premise. -/
noncomputable def MEqRedPreservesWfMContextual.of_chain_diagram_no_beta
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundChainDiagramPayload)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta hSubst
    (AbsFunctionBoundInversion_of_chain_diagram hDiagram)
    hOpFun hFunBody hFOpBody

/-- Contextual `MEqRed` preservation assembled from a Type-valued
function-bound chain diagram and the sharpened `.sub` head replacement
payload, with the β case proved internally. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_diagram_no_beta_and_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundChainDiagramPayload)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta_and_sub_replace hSubst
    (AbsFunctionBoundInversion_of_chain_diagram hDiagram)
    hOpFun hReplace hFOpBody

/-- Contextual `MEqRed` preservation assembled from a Type-valued
function-bound chain diagram and direct `.sub` replacement residual payloads. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_diagram_no_beta_and_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundChainDiagramPayload)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_diagram_no_beta_and_sub_replace
    hSubst hDiagram hOpFun
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)
    hFOpBody

/-- Contextual `MEqRed` preservation assembled from a Type-valued
function-bound chain diagram, immediate top-level `.sub` replacement
residuals, and the named preserved-head replacement payload. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_diagram_no_beta_and_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundChainDiagramPayload)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_diagram_no_beta_and_sub_replace
    hSubst hDiagram hOpFun
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hFOpBody

/-- Contextual `MEqRed` preservation assembled from a shape-only
function-bound chain payload plus joined-bound well-formedness, with the β
case proved internally. -/
noncomputable def MEqRedPreservesWfMContextual.of_chain_shape_no_beta
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_diagram_no_beta hSubst
    (AbsFunctionBoundChainDiagramPayload.of_shape hShape hShapeWf)
    hOpFun hFunBody hFOpBody

/-- Contextual `MEqRed` preservation assembled from a shape-only
function-bound chain payload, joined-bound well-formedness, and the sharpened
`.sub` head replacement payload, with the β case proved internally. -/
noncomputable def MEqRedPreservesWfMContextual.of_chain_shape_no_beta_and_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_diagram_no_beta_and_sub_replace
    hSubst (AbsFunctionBoundChainDiagramPayload.of_shape hShape hShapeWf)
    hOpFun hReplace hFOpBody

/-- Contextual `MEqRed` preservation assembled from a shape-only
function-bound chain payload, joined-bound well-formedness, and direct `.sub`
replacement residual payloads. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_no_beta_and_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_no_beta_and_sub_replace
    hSubst hShape hShapeWf hOpFun
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)
    hFOpBody

/-- Contextual `MEqRed` preservation assembled from a shape-only
function-bound chain payload, joined-bound well-formedness, immediate
top-level `.sub` replacement residuals, and the named preserved-head
replacement payload. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_no_beta_and_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_no_beta_and_sub_replace
    hSubst hShape hShapeWf hOpFun
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hFOpBody

/-- Contextual `MEqRed` preservation assembled from a shape-only
function-bound chain payload plus joined-bound well-formedness only under
`WfCtxEqu`, with the β case proved internally. -/
noncomputable def MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv hSubst
    (AbsFunctionBoundInversionUnderWfCtx_of_chain_shape hShape hShapeWf)
    hOpFun hFunBody hFOpBody

/-- Contextual `MEqRed` preservation assembled from a shape-only
function-bound chain payload, joined-bound well-formedness under `WfCtxEqu`,
and the sharpened `.sub` head replacement payload, with the β case proved
internally. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_sub_replace
    hSubst (AbsFunctionBoundInversionUnderWfCtx_of_chain_shape hShape hShapeWf)
    hOpFun hReplace hFOpBody

/-- Contextual `MEqRed` preservation assembled from a shape-only
function-bound chain payload, joined-bound well-formedness under `WfCtxEqu`,
and direct `.sub` replacement residual payloads. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_sub_replace
    hSubst hShape hShapeWf hOpFun
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)
    hFOpBody

/-- Contextual `MEqRed` preservation assembled from a shape-only
function-bound chain payload, joined-bound well-formedness under `WfCtxEqu`,
immediate top-level `.sub` replacement residuals, and the named
preserved-head replacement payload. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_sub_replace
    hSubst hShape hShapeWf hOpFun
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hFOpBody

/-- Contextual preservation from a shape-only function-bound chain payload,
joined-bound well-formedness under `WfCtxEqu`, the native `Me-App` operator
payload, and the two directional `Me-FOp` head/body transports. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_head_transports
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_head_transports
    hSubst (AbsFunctionBoundInversionUnderWfCtx_of_chain_shape hShape hShapeWf)
    hOpFun hFunBody hSubToEqu hEquToSub

/-- Contextual preservation from a shape-only function-bound chain payload,
joined-bound well-formedness under `WfCtxEqu`, the native `Me-App` operator
payload, the sharpened `.sub` head replacement payload, and the two
directional `Me-FOp` head/body transports. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_sub_replace_and_head_transports
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_sub_replace_and_head_transports
    hSubst (AbsFunctionBoundInversionUnderWfCtx_of_chain_shape hShape hShapeWf)
    hOpFun hReplace hSubToEqu hEquToSub

/-- Contextual preservation from a shape-only function-bound chain payload,
joined-bound well-formedness under `WfCtxEqu`, the native `Me-App` operator
payload, and one uniform head-kind/body transport payload for `Me-FOp`. This
is retained as a diagnostic assembly route; the uniform head-kind premise is
refutable under the no-Top-function-supertype obstruction. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_head_kind_transport
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hHeadTransport : WfMHeadKindTransportPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_head_kind_transport
    hSubst (AbsFunctionBoundInversionUnderWfCtx_of_chain_shape hShape hShapeWf)
    hOpFun hFunBody hHeadTransport

/-- Contextual preservation from a shape-only function-bound chain payload,
joined-bound well-formedness under `WfCtxEqu`, the native `Me-App` operator
payload, sharpened `.sub` head replacement for `Me-Fun`, and one uniform
head-kind/body transport payload for `Me-FOp`. This is retained as a
diagnostic assembly route; the uniform head-kind premise is refutable under
the no-Top-function-supertype obstruction. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_sub_replace_and_head_kind_transport
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hHeadTransport : WfMHeadKindTransportPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_components_no_beta_under_wfctx_inv_and_sub_replace_and_head_kind_transport
    hSubst (AbsFunctionBoundInversionUnderWfCtx_of_chain_shape hShape hShapeWf)
    hOpFun hReplace hHeadTransport

/-- Contextual preservation from a shape-only function-bound chain payload,
joined-bound well-formedness under `WfCtxEqu`, and stacked left-endpoint
transport, leaving the `Me-Fun` and `Me-FOp` body residuals in their native
forms. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_left_factored_no_beta
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta
    hSubst hShape hShapeWf
    (MEqRedAppFunctionSupertypePayload.of_left_transport hLeft)
    hFunBody hFOpBody

/-- Contextual preservation from a shape-only function-bound chain payload,
joined-bound well-formedness under `WfCtxEqu`, stacked left-endpoint
transport, and the sharpened `.sub` head replacement payload, leaving the
`Me-FOp` body residual in its native form. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_left_factored_no_beta_and_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_sub_replace
    hSubst hShape hShapeWf
    (MEqRedAppFunctionSupertypePayload.of_left_transport hLeft)
    hReplace hFOpBody

/-- Contextual preservation from a shape-only function-bound chain payload,
joined-bound well-formedness under `WfCtxEqu`, stacked left-endpoint
transport, and the two directional `Me-FOp` head/body transports. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_factored_no_beta_and_head_transports
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_factored_components_no_beta
    hSubst (AbsFunctionBoundInversionUnderWfCtx_of_chain_shape hShape hShapeWf)
    hLeft hFunBody hSubToEqu hEquToSub

/-- Contextual preservation from a shape-only function-bound chain payload,
joined-bound well-formedness under `WfCtxEqu`, stacked left-endpoint
transport, the sharpened `.sub` head replacement payload for `Me-Fun`, and
the two directional `Me-FOp` head/body transports. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_factored_no_beta_and_sub_replace_and_head_transports
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_factored_components_no_beta_and_sub_replace
    hSubst (AbsFunctionBoundInversionUnderWfCtx_of_chain_shape hShape hShapeWf)
    hLeft hReplace hSubToEqu hEquToSub

/-- Contextual preservation from a shape-only function-bound chain payload,
joined-bound well-formedness under `WfCtxEqu`, and the factored residual
payloads for stacked left-endpoint transport and head-kind body transport. -/
noncomputable def MEqRedPreservesWfMContextual.of_chain_shape_wfctx_factored_no_beta
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hFunBody : MEqRedFunBodyReplacePayload)
    (hHeadTransport : WfMHeadKindTransportPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_factored_components_no_beta_and_head_kind_transport
    hSubst (AbsFunctionBoundInversionUnderWfCtx_of_chain_shape hShape hShapeWf)
    hLeft hFunBody hHeadTransport

/-- Contextual preservation from a shape-only function-bound chain payload,
joined-bound well-formedness under `WfCtxEqu`, the sharpened `.sub` head
replacement payload for `Me-Fun`, and the two final factored residual
payloads. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_factored_no_beta_and_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hHeadTransport : WfMHeadKindTransportPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_factored_components_no_beta_and_sub_replace_and_head_kind_transport
    hSubst (AbsFunctionBoundInversionUnderWfCtx_of_chain_shape hShape hShapeWf)
    hLeft hReplace hHeadTransport

/-- Contextual preservation assembled from the shape-only chain payload, with
the joined-bound well-formedness side condition derived from an already
available machine-state preservation theorem specialized to empty stacks. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_machine_state_no_beta_and_sub_replace_and_head_transports
    (hMachine : MEqRedPreservesWfMachineState)
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_sub_replace_and_head_transports
    hSubst hShape
    (AbsFunctionBoundChainShapeWfUnderWfCtxPayload_of_machine_state
      hShape hMachine)
    hOpFun hReplace hSubToEqu hEquToSub

/-- Factored contextual preservation assembled from the shape-only chain
payload, with the joined-bound well-formedness side condition derived from
an already available machine-state preservation theorem specialized to empty
stacks. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_machine_state_factored_no_beta_and_sub_replace_and_head_transports
    (hMachine : MEqRedPreservesWfMachineState)
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_wfctx_factored_no_beta_and_sub_replace_and_head_transports
    hSubst hShape
    (AbsFunctionBoundChainShapeWfUnderWfCtxPayload_of_machine_state
      hShape hMachine)
    hLeft hReplace hSubToEqu hEquToSub

/-- Machine-state preservation route whose contextual subproof is assembled
from the shape-only function-bound chain payload, joined-bound
well-formedness under `WfCtxEqu`, the native `Me-App` operator payload,
sharpened `.sub` head replacement, and the two directional `Me-FOp`
head/body transports. The remaining machine-specific residuals are the
stack/control body transports and target/tail application payloads. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_contextual
    hSubst hAppend hBridge
    (AbsFunctionBoundInversionUnderWfCtx_of_chain_shape hShape hShapeWf)
    (MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_sub_replace_and_head_transports
      hSubst hShape hShapeWf hOpFun hReplace hSubToEqu hEquToSub)
    hSubToEqu hEquToSub hTargetApp hTailCons hReplace hNoTop

/-- Machine-state preservation route whose contextual subproof is assembled
from the shape-only function-bound chain payload, with the control-left
residual still exposed through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_chain_shape_wfctx_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_target_app_machine_tail_cons
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hShape hShapeWf hOpFun
    hSubToEqu hEquToSub hTargetApp hTailCons hReplace hNoTop

/-- Factored variant of
`MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_chain_shape_wfctx_target_app_machine_tail_cons`
using stacked left-endpoint transport for the contextual `Me-App` operator
case. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_contextual
    hSubst hAppend hBridge
    (AbsFunctionBoundInversionUnderWfCtx_of_chain_shape hShape hShapeWf)
    (MEqRedPreservesWfMContextual.of_chain_shape_wfctx_factored_no_beta_and_sub_replace_and_head_transports
      hSubst hShape hShapeWf hLeft hReplace hSubToEqu hEquToSub)
    hSubToEqu hEquToSub hTargetApp hTailCons hReplace hNoTop

/-- Factored variant of
`MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_chain_shape_wfctx_target_app_machine_tail_cons`,
with the control-left residual still exposed through the older body-transport
surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_target_app_machine_tail_cons
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hShape hShapeWf hLeft
    hSubToEqu hEquToSub hTargetApp hTailCons hReplace hNoTop

/-- Typed-operator variant of the factored chain-shape machine route. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_target_app_machine_tail_cons
    hSubst hAppend hBridge hShape hShapeWf hLeft
    hSubToEqu hEquToSub
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_typed_operator hOpFun hTail)
    hReplace hNoTop

/-- Typed-operator variant of the factored chain-shape machine route, with
the control-left residual still exposed through the older body-transport
surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_operator_machine_tail
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hShape hShapeWf hLeft hSubToEqu hEquToSub hOpFun hTail hReplace hNoTop

/-- Machine-operator variant of the factored chain-shape machine route. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_machine_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_target_app_machine_tail_cons
    hSubst hAppend hBridge hShape hShapeWf hLeft
    hSubToEqu hEquToSub
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_machine_operator hOpFun hTail)
    hReplace hNoTop

/-- Machine-operator variant of the factored chain-shape machine route, with
the control-left residual still exposed through the older body-transport
surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_machine_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_machine_operator_machine_tail
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hShape hShapeWf hLeft hSubToEqu hEquToSub hOpFun hTail hReplace hNoTop

/-- Diagnostic head-kind-transport variant of the factored chain-shape
machine route. The uniform head-kind premise remains too strong for the
final route, but this wrapper keeps the diagnostic interface aligned with
the strongest machine assembly. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hHeadTransport : WfMHeadKindTransportPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_target_app_machine_tail_cons
    hSubst hAppend hBridge hShape hShapeWf hLeft
    (WfMSubHeadToEquHeadPayload.of_head_kind_transport hHeadTransport)
    (WfMEquHeadToSubHeadPayload.of_head_kind_transport hHeadTransport)
    hTargetApp hTailCons hReplace hNoTop

/-- Diagnostic head-kind-transport variant of the factored chain-shape
machine route, with the control-left residual still exposed through the
older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hHeadTransport : WfMHeadKindTransportPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_target_app_machine_tail_cons
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hShape hShapeWf hLeft hHeadTransport hTargetApp hTailCons hReplace hNoTop

/-- Typed-operator diagnostic head-kind variant of the factored chain-shape
machine route. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hHeadTransport : WfMHeadKindTransportPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_target_app_machine_tail_cons
    hSubst hAppend hBridge hShape hShapeWf hLeft hHeadTransport
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_typed_operator hOpFun hTail)
    hReplace hNoTop

/-- Typed-operator diagnostic head-kind variant of the factored chain-shape
machine route, with the control-left residual still exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hHeadTransport : WfMHeadKindTransportPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_operator_machine_tail
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hShape hShapeWf hLeft hHeadTransport hOpFun hTail hReplace hNoTop

/-- Machine-operator diagnostic head-kind variant of the factored chain-shape
machine route. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_machine_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hHeadTransport : WfMHeadKindTransportPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_target_app_machine_tail_cons
    hSubst hAppend hBridge hShape hShapeWf hLeft hHeadTransport
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_machine_operator hOpFun hTail)
    hReplace hNoTop

/-- Machine-operator diagnostic head-kind variant of the factored chain-shape
machine route, with the control-left residual still exposed through the older
body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_machine_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hHeadTransport : WfMHeadKindTransportPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_machine_operator_machine_tail
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hShape hShapeWf hLeft hHeadTransport hOpFun hTail hReplace hNoTop

/-- External-empty machine-state preservation route whose contextual subproof
is assembled from the shape-only function-bound chain payload, joined-bound
well-formedness under `WfCtxEqu`, the native `Me-App` operator payload,
sharpened `.sub` head replacement, and the two directional `Me-FOp`
head/body transports. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_contextual
    hSubst hAppend hBridge
    (AbsFunctionBoundInversionUnderWfCtx_of_chain_shape hShape hShapeWf)
    (MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_sub_replace_and_head_transports
      hSubst hShape hShapeWf hOpFun hReplace hSubToEqu hEquToSub)
    hSubToEqu hEquToSub hTargetApp hTailCons hReplace hNoTop

/-- External-empty chain-shape machine route, with stack append exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_chain_shape_wfctx_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_target_app_machine_tail_cons
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hShape hShapeWf hOpFun
    hSubToEqu hEquToSub hTargetApp hTailCons hReplace hNoTop

/-- External-empty factored chain-shape route using stacked left-endpoint
transport for the contextual `Me-App` operator case. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_factored_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_contextual
    hSubst hAppend hBridge
    (AbsFunctionBoundInversionUnderWfCtx_of_chain_shape hShape hShapeWf)
    (MEqRedPreservesWfMContextual.of_chain_shape_wfctx_factored_no_beta_and_sub_replace_and_head_transports
      hSubst hShape hShapeWf hLeft hReplace hSubToEqu hEquToSub)
    hSubToEqu hEquToSub hTargetApp hTailCons hReplace hNoTop

/-- External-empty factored chain-shape route, with stack append exposed
through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_chain_shape_wfctx_factored_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_factored_target_app_machine_tail_cons
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hShape hShapeWf hLeft
    hSubToEqu hEquToSub hTargetApp hTailCons hReplace hNoTop

/-- External-empty typed-operator variant of the factored chain-shape route. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_factored_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_factored_target_app_machine_tail_cons
    hSubst hAppend hBridge hShape hShapeWf hLeft
    hSubToEqu hEquToSub
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_typed_operator hOpFun hTail)
    hReplace hNoTop

/-- External-empty typed-operator factored chain-shape route, with stack
append exposed through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_chain_shape_wfctx_factored_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_factored_operator_machine_tail
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hShape hShapeWf hLeft hSubToEqu hEquToSub hOpFun hTail hReplace hNoTop

/-- External-empty machine-operator variant of the factored chain-shape route. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_factored_machine_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_factored_target_app_machine_tail_cons
    hSubst hAppend hBridge hShape hShapeWf hLeft
    hSubToEqu hEquToSub
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_machine_operator hOpFun hTail)
    hReplace hNoTop

/-- External-empty machine-operator factored chain-shape route, with stack
append exposed through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_chain_shape_wfctx_factored_machine_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_factored_machine_operator_machine_tail
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hShape hShapeWf hLeft hSubToEqu hEquToSub hOpFun hTail hReplace hNoTop

/-- External-empty diagnostic head-kind variant of the factored chain-shape
machine route. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hHeadTransport : WfMHeadKindTransportPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_factored_target_app_machine_tail_cons
    hSubst hAppend hBridge hShape hShapeWf hLeft
    (WfMSubHeadToEquHeadPayload.of_head_kind_transport hHeadTransport)
    (WfMEquHeadToSubHeadPayload.of_head_kind_transport hHeadTransport)
    hTargetApp hTailCons hReplace hNoTop

/-- External-empty diagnostic head-kind chain-shape route, with stack append
exposed through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_target_app_machine_tail_cons
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hHeadTransport : WfMHeadKindTransportPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_target_app_machine_tail_cons
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hShape hShapeWf hLeft hHeadTransport hTargetApp hTailCons hReplace hNoTop

/-- External-empty typed-operator diagnostic head-kind variant of the factored
chain-shape route. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hHeadTransport : WfMHeadKindTransportPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_target_app_machine_tail_cons
    hSubst hAppend hBridge hShape hShapeWf hLeft hHeadTransport
    (MEqRedAppTargetPreservesWfMPayload.of_typed_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_typed_operator hOpFun hTail)
    hReplace hNoTop

/-- External-empty typed-operator diagnostic head-kind chain-shape route, with
stack append exposed through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hHeadTransport : WfMHeadKindTransportPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_operator_machine_tail
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hShape hShapeWf hLeft hHeadTransport hOpFun hTail hReplace hNoTop

/-- External-empty machine-operator diagnostic head-kind variant of the
factored chain-shape route. -/
noncomputable def MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_machine_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hHeadTransport : WfMHeadKindTransportPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_target_app_machine_tail_cons
    hSubst hAppend hBridge hShape hShapeWf hLeft hHeadTransport
    (MEqRedAppTargetPreservesWfMPayload.of_machine_operator hOpFun)
    (MEqRedMachineTailStepPreservesConsPayload.of_machine_operator hOpFun hTail)
    hReplace hNoTop

/-- External-empty machine-operator diagnostic head-kind chain-shape route,
with stack append exposed through the older body-transport surface. -/
noncomputable def MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_machine_operator_machine_tail
    (hSubst : BetaInstantiationPreservesWfM)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hHeadTransport : WfMHeadKindTransportPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hReplace : WfMSubHeadReplaceOfNewWf)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_chain_shape_wfctx_factored_head_kind_machine_operator_machine_tail
    hSubst
    (MSubStarStackAppendPayload.of_body_transports hEqBody hSubBody)
    (MSubStarToWSubMStarPayload.of_steps hPres hStep)
    hShape hShapeWf hLeft hHeadTransport hOpFun hTail hReplace hNoTop

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

/-- Operational well-formedness preservation from the direct `.sub` head
replacement residual package. -/
noncomputable def StepPreservesWfM_of_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversion)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new) :
    StepPreservesWfM :=
  StepPreservesWfM_of_components hSubst hInv
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)

/-- Operational well-formedness preservation from immediate top-level direct
`.sub` replacement residuals and a factored preserved-head replacement
payload. -/
noncomputable def
    StepPreservesWfM_of_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversion)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new) :
    StepPreservesWfM :=
  StepPreservesWfM_of_components hSubst hInv
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)

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

/-- Diagrammatic operational preservation from the direct `.sub` head
replacement residual package. -/
noncomputable def StepPreservesWfM_of_diagram_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundDiagramPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new) :
    StepPreservesWfM :=
  StepPreservesWfM_of_diagram_components hSubst hDiagram
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)

/-- Diagrammatic operational preservation from immediate top-level direct
`.sub` replacement residuals and a factored preserved-head replacement
payload. -/
noncomputable def
    StepPreservesWfM_of_diagram_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundDiagramPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new) :
    StepPreservesWfM :=
  StepPreservesWfM_of_diagram_components hSubst hDiagram
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)

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

/-- Chain-diagram operational preservation from the direct `.sub` head
replacement residual package. -/
noncomputable def
    StepPreservesWfM_of_chain_diagram_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundChainDiagramPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new) :
    StepPreservesWfM :=
  StepPreservesWfM_of_chain_diagram_components hSubst hDiagram
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)

/-- Chain-diagram operational preservation from immediate top-level direct
`.sub` replacement residuals and a factored preserved-head replacement
payload. -/
noncomputable def
    StepPreservesWfM_of_chain_diagram_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundChainDiagramPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new) :
    StepPreservesWfM :=
  StepPreservesWfM_of_chain_diagram_components hSubst hDiagram
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)

/-- β preservation reduced to the shape-only function-bound chain payload,
its joined-bound well-formedness payload, and the body-instantiation lemma. -/
noncomputable def StepBetaPreservesWfM_of_chain_shape
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfPayload hShape) :
    StepBetaPreservesWfM :=
  StepBetaPreservesWfM_of_chain_diagram hSubst
    (AbsFunctionBoundChainDiagramPayload.of_shape hShape hShapeWf)

/-- Operational well-formedness preservation reduced to the body-instantiation
lemma, the shape-only function-bound chain payload, its joined-bound
well-formedness payload, and sharpened `.sub` head replacement. -/
noncomputable def StepPreservesWfM_of_chain_shape_components
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfPayload hShape)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf) :
    StepPreservesWfM :=
  StepPreservesWfM_of_new_wf
    (StepBetaPreservesWfM_of_chain_shape hSubst hShape hShapeWf)
    hSubHeadReplace

/-- Chain-shape operational preservation from the direct `.sub` head
replacement residual package. -/
noncomputable def StepPreservesWfM_of_chain_shape_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfPayload hShape)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new) :
    StepPreservesWfM :=
  StepPreservesWfM_of_chain_shape_components hSubst hShape hShapeWf
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)

/-- Chain-shape operational preservation from immediate top-level direct
`.sub` replacement residuals and a factored preserved-head replacement
payload. -/
noncomputable def
    StepPreservesWfM_of_chain_shape_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfPayload hShape)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new) :
    StepPreservesWfM :=
  StepPreservesWfM_of_chain_shape_components hSubst hShape hShapeWf
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)

/-- Operational well-formedness preservation reduced to the body-instantiation
lemma, the shape-only function-bound chain payload, empty-stack equivalence
well-formedness preservation for the joined bound, and sharpened `.sub` head
replacement. -/
noncomputable def StepPreservesWfM_of_chain_shape_meq_components
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hMEqPres : MEqRedPreservesWfM)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf) :
    StepPreservesWfM :=
  StepPreservesWfM_of_chain_shape_components hSubst hShape
    (AbsFunctionBoundChainShapeWfPayload_of_meq hShape hMEqPres)
    hSubHeadReplace

/-- Chain-shape operational preservation with joined-bound well-formedness
from empty-stack equivalence preservation, and `.sub` head replacement from
the direct residual package. -/
noncomputable def
    StepPreservesWfM_of_chain_shape_meq_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hMEqPres : MEqRedPreservesWfM)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new) :
    StepPreservesWfM :=
  StepPreservesWfM_of_chain_shape_meq_components hSubst hShape hMEqPres
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)

/-- Chain-shape operational preservation with joined-bound well-formedness
from empty-stack equivalence preservation, plus immediate top-level direct
`.sub` replacement residuals and a factored preserved-head replacement
payload. -/
noncomputable def
    StepPreservesWfM_of_chain_shape_meq_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hMEqPres : MEqRedPreservesWfM)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new) :
    StepPreservesWfM :=
  StepPreservesWfM_of_chain_shape_meq_components hSubst hShape hMEqPres
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)

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

/-- De Bruijn preservation with operational preservation assembled from the
body-instantiation lemma, function-bound inversion, and the sharpened `.sub`
head replacement payload. -/
noncomputable def Theorem_5_DeBruijn_Preservation_of_components
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversion)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf)
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  Theorem_5_DeBruijn_Preservation_of
    (StepPreservesWfM_of_components hSubst hInv hSubHeadReplace)
    hwf hstep

/-- De Bruijn preservation from direct operational components and the direct
`.sub` head replacement residual package. -/
noncomputable def Theorem_5_DeBruijn_Preservation_of_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversion)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  Theorem_5_DeBruijn_Preservation_of
    (StepPreservesWfM_of_components_and_direct_sub_replace
      hSubst hInv hSubPayloads)
    hwf hstep

/-- De Bruijn preservation from direct operational components, immediate
top-level `.sub` replacement residuals, and the named preserved-head
replacement payload. -/
noncomputable def
    Theorem_5_DeBruijn_Preservation_of_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversion)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  Theorem_5_DeBruijn_Preservation_of
    (StepPreservesWfM_of_components_and_immediate_sub_replace_and_under
      hSubst hInv hUnder hSubPayloads)
    hwf hstep

/-- Closed-term Theorem 5 entry point for the direct operational
preservation components. -/
noncomputable def Theorem_5_DeBruijn_ClosedPreservation_of_components
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversion)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_ClosedPreservation_of
    (StepPreservesWfM_of_components hSubst hInv hSubHeadReplace)
    hwf hstep

/-- Closed-term Theorem 5 from direct operational components and the direct
`.sub` head replacement residual package. -/
noncomputable def
    Theorem_5_DeBruijn_ClosedPreservation_of_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversion)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_ClosedPreservation_of
    (StepPreservesWfM_of_components_and_direct_sub_replace
      hSubst hInv hSubPayloads)
    hwf hstep

/-- Closed-term Theorem 5 from direct operational components, immediate
top-level `.sub` replacement residuals, and the named preserved-head
replacement payload. -/
noncomputable def
    Theorem_5_DeBruijn_ClosedPreservation_of_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversion)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_ClosedPreservation_of
    (StepPreservesWfM_of_components_and_immediate_sub_replace_and_under
      hSubst hInv hUnder hSubPayloads)
    hwf hstep

/-- De Bruijn preservation with operational preservation assembled from the
body-instantiation lemma, the Type-valued function-bound diagram payload, and
the sharpened `.sub` head replacement payload. -/
noncomputable def Theorem_5_DeBruijn_Preservation_of_diagram_components
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundDiagramPayload)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf)
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  Theorem_5_DeBruijn_Preservation_of
    (StepPreservesWfM_of_diagram_components
      hSubst hDiagram hSubHeadReplace)
    hwf hstep

/-- De Bruijn preservation with diagrammatic function-bound payload and
direct `.sub` replacement residual package. -/
noncomputable def
    Theorem_5_DeBruijn_Preservation_of_diagram_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundDiagramPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  Theorem_5_DeBruijn_Preservation_of
    (StepPreservesWfM_of_diagram_components_and_direct_sub_replace
      hSubst hDiagram hSubPayloads)
    hwf hstep

/-- De Bruijn preservation with diagrammatic function-bound payload,
immediate top-level `.sub` replacement residuals, and the named
preserved-head replacement payload. -/
noncomputable def
    Theorem_5_DeBruijn_Preservation_of_diagram_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundDiagramPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  Theorem_5_DeBruijn_Preservation_of
    (StepPreservesWfM_of_diagram_components_and_immediate_sub_replace_and_under
      hSubst hDiagram hUnder hSubPayloads)
    hwf hstep

/-- Closed-term Theorem 5 entry point for the Type-valued function-bound
diagram preservation components. -/
noncomputable def Theorem_5_DeBruijn_ClosedPreservation_of_diagram_components
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundDiagramPayload)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_ClosedPreservation_of
    (StepPreservesWfM_of_diagram_components
      hSubst hDiagram hSubHeadReplace)
    hwf hstep

/-- Closed-term Theorem 5 with diagrammatic function-bound payload and
direct `.sub` replacement residual package. -/
noncomputable def
    Theorem_5_DeBruijn_ClosedPreservation_of_diagram_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundDiagramPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_ClosedPreservation_of
    (StepPreservesWfM_of_diagram_components_and_direct_sub_replace
      hSubst hDiagram hSubPayloads)
    hwf hstep

/-- Closed-term Theorem 5 with diagrammatic function-bound payload,
immediate top-level `.sub` replacement residuals, and the named
preserved-head replacement payload. -/
noncomputable def
    Theorem_5_DeBruijn_ClosedPreservation_of_diagram_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundDiagramPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_ClosedPreservation_of
    (StepPreservesWfM_of_diagram_components_and_immediate_sub_replace_and_under
      hSubst hDiagram hUnder hSubPayloads)
    hwf hstep

/-- De Bruijn preservation with operational preservation assembled from the
body-instantiation lemma, the Type-valued function-bound chain diagram
payload, and the sharpened `.sub` head replacement payload. -/
noncomputable def Theorem_5_DeBruijn_Preservation_of_chain_diagram_components
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundChainDiagramPayload)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf)
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  Theorem_5_DeBruijn_Preservation_of
    (StepPreservesWfM_of_chain_diagram_components
      hSubst hDiagram hSubHeadReplace)
    hwf hstep

/-- De Bruijn preservation with chain-diagram function-bound payload and
direct `.sub` replacement residual package. -/
noncomputable def
    Theorem_5_DeBruijn_Preservation_of_chain_diagram_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundChainDiagramPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  Theorem_5_DeBruijn_Preservation_of
    (StepPreservesWfM_of_chain_diagram_components_and_direct_sub_replace
      hSubst hDiagram hSubPayloads)
    hwf hstep

/-- De Bruijn preservation with chain-diagram function-bound payload,
immediate top-level `.sub` replacement residuals, and the named
preserved-head replacement payload. -/
noncomputable def
    Theorem_5_DeBruijn_Preservation_of_chain_diagram_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundChainDiagramPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  Theorem_5_DeBruijn_Preservation_of
    (StepPreservesWfM_of_chain_diagram_components_and_immediate_sub_replace_and_under
      hSubst hDiagram hUnder hSubPayloads)
    hwf hstep

/-- Closed-term Theorem 5 entry point for the Type-valued function-bound
chain-diagram preservation components. -/
noncomputable def Theorem_5_DeBruijn_ClosedPreservation_of_chain_diagram_components
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundChainDiagramPayload)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_ClosedPreservation_of
    (StepPreservesWfM_of_chain_diagram_components
      hSubst hDiagram hSubHeadReplace)
    hwf hstep

/-- Closed-term Theorem 5 with chain-diagram function-bound payload and
direct `.sub` replacement residual package. -/
noncomputable def
    Theorem_5_DeBruijn_ClosedPreservation_of_chain_diagram_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundChainDiagramPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_ClosedPreservation_of
    (StepPreservesWfM_of_chain_diagram_components_and_direct_sub_replace
      hSubst hDiagram hSubPayloads)
    hwf hstep

/-- Closed-term Theorem 5 with chain-diagram function-bound payload,
immediate top-level `.sub` replacement residuals, and the named
preserved-head replacement payload. -/
noncomputable def
    Theorem_5_DeBruijn_ClosedPreservation_of_chain_diagram_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hDiagram : AbsFunctionBoundChainDiagramPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_ClosedPreservation_of
    (StepPreservesWfM_of_chain_diagram_components_and_immediate_sub_replace_and_under
      hSubst hDiagram hUnder hSubPayloads)
    hwf hstep

/-- De Bruijn preservation with operational preservation assembled from the
body-instantiation lemma, the shape-only function-bound chain payload, its
joined-bound well-formedness payload, and the sharpened `.sub` head
replacement payload. -/
noncomputable def Theorem_5_DeBruijn_Preservation_of_chain_shape_components
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfPayload hShape)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf)
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  Theorem_5_DeBruijn_Preservation_of
    (StepPreservesWfM_of_chain_shape_components
      hSubst hShape hShapeWf hSubHeadReplace)
    hwf hstep

/-- De Bruijn preservation with shape-only function-bound chain payload,
joined-bound well-formedness payload, and direct `.sub` replacement residual
package. -/
noncomputable def
    Theorem_5_DeBruijn_Preservation_of_chain_shape_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfPayload hShape)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  Theorem_5_DeBruijn_Preservation_of
    (StepPreservesWfM_of_chain_shape_components_and_direct_sub_replace
      hSubst hShape hShapeWf hSubPayloads)
    hwf hstep

/-- De Bruijn preservation with shape-only function-bound chain payload,
joined-bound well-formedness payload, immediate top-level `.sub` replacement
residuals, and the named preserved-head replacement payload. -/
noncomputable def
    Theorem_5_DeBruijn_Preservation_of_chain_shape_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfPayload hShape)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  Theorem_5_DeBruijn_Preservation_of
    (StepPreservesWfM_of_chain_shape_components_and_immediate_sub_replace_and_under
      hSubst hShape hShapeWf hUnder hSubPayloads)
    hwf hstep

/-- Closed-term Theorem 5 entry point for the shape-only function-bound
chain preservation components. -/
noncomputable def Theorem_5_DeBruijn_ClosedPreservation_of_chain_shape_components
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfPayload hShape)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_ClosedPreservation_of
    (StepPreservesWfM_of_chain_shape_components
      hSubst hShape hShapeWf hSubHeadReplace)
    hwf hstep

/-- Closed-term Theorem 5 with shape-only function-bound chain payload,
joined-bound well-formedness payload, and direct `.sub` replacement residual
package. -/
noncomputable def
    Theorem_5_DeBruijn_ClosedPreservation_of_chain_shape_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfPayload hShape)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_ClosedPreservation_of
    (StepPreservesWfM_of_chain_shape_components_and_direct_sub_replace
      hSubst hShape hShapeWf hSubPayloads)
    hwf hstep

/-- Closed-term Theorem 5 with shape-only function-bound chain payload,
joined-bound well-formedness payload, immediate top-level `.sub` replacement
residuals, and the named preserved-head replacement payload. -/
noncomputable def
    Theorem_5_DeBruijn_ClosedPreservation_of_chain_shape_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfPayload hShape)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_ClosedPreservation_of
    (StepPreservesWfM_of_chain_shape_components_and_immediate_sub_replace_and_under
      hSubst hShape hShapeWf hUnder hSubPayloads)
    hwf hstep

/-- De Bruijn preservation with the chain-shape joined-bound well-formedness
payload derived from empty-stack equivalence preservation. -/
noncomputable def Theorem_5_DeBruijn_Preservation_of_chain_shape_meq_components
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hMEqPres : MEqRedPreservesWfM)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf)
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  Theorem_5_DeBruijn_Preservation_of
    (StepPreservesWfM_of_chain_shape_meq_components
      hSubst hShape hMEqPres hSubHeadReplace)
    hwf hstep

/-- De Bruijn preservation with chain-shape joined-bound well-formedness from
empty-stack equivalence preservation, and `.sub` head replacement from the
direct residual package. -/
noncomputable def
    Theorem_5_DeBruijn_Preservation_of_chain_shape_meq_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hMEqPres : MEqRedPreservesWfM)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  Theorem_5_DeBruijn_Preservation_of
    (StepPreservesWfM_of_chain_shape_meq_components_and_direct_sub_replace
      hSubst hShape hMEqPres hSubPayloads)
    hwf hstep

/-- De Bruijn preservation with chain-shape joined-bound well-formedness from
empty-stack equivalence preservation, immediate top-level `.sub` replacement
residuals, and the named preserved-head replacement payload. -/
noncomputable def
    Theorem_5_DeBruijn_Preservation_of_chain_shape_meq_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hMEqPres : MEqRedPreservesWfM)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  Theorem_5_DeBruijn_Preservation_of
    (StepPreservesWfM_of_chain_shape_meq_components_and_immediate_sub_replace_and_under
      hSubst hShape hMEqPres hUnder hSubPayloads)
    hwf hstep

/-- Closed-term Theorem 5 entry point for chain-shape preservation when the
joined-bound well-formedness payload is supplied by empty-stack equivalence
preservation. -/
noncomputable def
    Theorem_5_DeBruijn_ClosedPreservation_of_chain_shape_meq_components
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hMEqPres : MEqRedPreservesWfM)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_ClosedPreservation_of
    (StepPreservesWfM_of_chain_shape_meq_components
      hSubst hShape hMEqPres hSubHeadReplace)
    hwf hstep

/-- Closed-term Theorem 5 with chain-shape joined-bound well-formedness from
empty-stack equivalence preservation, and `.sub` head replacement from the
direct residual package. -/
noncomputable def
    Theorem_5_DeBruijn_ClosedPreservation_of_chain_shape_meq_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hMEqPres : MEqRedPreservesWfM)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_ClosedPreservation_of
    (StepPreservesWfM_of_chain_shape_meq_components_and_direct_sub_replace
      hSubst hShape hMEqPres hSubPayloads)
    hwf hstep

/-- Closed-term Theorem 5 with chain-shape joined-bound well-formedness from
empty-stack equivalence preservation, immediate top-level `.sub` replacement
residuals, and the named preserved-head replacement payload. -/
noncomputable def
    Theorem_5_DeBruijn_ClosedPreservation_of_chain_shape_meq_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hMEqPres : MEqRedPreservesWfM)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_ClosedPreservation_of
    (StepPreservesWfM_of_chain_shape_meq_components_and_immediate_sub_replace_and_under
      hSubst hShape hMEqPres hUnder hSubPayloads)
    hwf hstep

end DeBruijn
end Pss
