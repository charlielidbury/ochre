import Pss.Mpss.DeBruijnTransitivityElim

/-! # `Pss.Mpss.DeBruijnTypeSafety` — de Bruijn type-safety endpoints

This module states the de Bruijn versions of the type-safety endpoints over
the already-ported operational and well-formed judgments. The remaining hard
metatheoretic ingredients are explicit premises rather than axioms.
-/

namespace Pss
namespace DeBruijn

set_option maxHeartbeats 800000

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

/-- De Bruijn operational preservation under the well-formed-equivalence
context invariant. This is the surface naturally supplied by the
machine-state preservation route. -/
def StepPreservesWfMUnderWfCtx : Type :=
  ∀ {Γ : Ctx} {t t' : Term},
    WfCtxEqu Γ → StepAt Γ.depth t t' → WfM Γ t → WfM Γ t'

/-- Remaining β payload for de Bruijn operational well-formedness
preservation. -/
def StepBetaPreservesWfM : Type :=
  ∀ {Γ : Ctx} {bound body arg : Term},
    WfM Γ (.app (.abs bound body) arg) →
      WfM Γ (Term.instantiate 0 arg body)

/-- β preservation under the well-formed-equivalence context invariant. -/
def StepBetaPreservesWfMUnderWfCtx : Type :=
  ∀ {Γ : Ctx} {bound body arg : Term},
    WfCtxEqu Γ →
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

/-- De Bruijn subtype-chain substitution payload needed by the application
case of β-instantiation preservation. -/
def BetaInstantiationPreservesWSubMStar : Type :=
  ∀ {Γ : Ctx} {bound arg lhs rhs : Term},
    WSubMStar Γ arg bound →
      WSubMStar ({ bound := bound, kind := .sub } :: Γ) lhs rhs →
        WSubMStar Γ (Term.instantiate 0 arg lhs) (Term.instantiate 0 arg rhs)

/-- De Bruijn one-step subtype substitution payload. Together with
well-formedness substitution it reconstructs the transitive
`WSubMStar` payload. -/
def BetaInstantiationPreservesWSubM : Type :=
  ∀ {Γ : Ctx} {bound arg lhs rhs : Term},
    WSubMStar Γ arg bound →
      WSubM ({ bound := bound, kind := .sub } :: Γ) lhs rhs →
        WSubM Γ (Term.instantiate 0 arg lhs) (Term.instantiate 0 arg rhs)

/-- Empty-stack equivalence-reduction substitution payload for de Bruijn
β-instantiation. -/
def BetaInstantiationPreservesMEqRed : Type :=
  ∀ {Γ : Ctx} {bound arg lhs rhs : Term},
    WSubMStar Γ arg bound →
      MEqRed ({ bound := bound, kind := .sub } :: Γ) [] lhs rhs →
        MEqRed Γ [] (Term.instantiate 0 arg lhs) (Term.instantiate 0 arg rhs)

/-- Empty-stack subtype-reduction substitution payload for de Bruijn
β-instantiation. -/
def BetaInstantiationPreservesMSubRed : Type :=
  ∀ {Γ : Ctx} {bound arg lhs rhs : Term},
    WSubMStar Γ arg bound →
      MSubRed ({ bound := bound, kind := .sub } :: Γ) [] lhs rhs →
        MSubRed Γ [] (Term.instantiate 0 arg lhs) (Term.instantiate 0 arg rhs)

/-- Stack-parametric equivalence-reduction substitution payload for de Bruijn
β-instantiation. -/
def BetaInstantiationPreservesMEqRedStack : Type :=
  ∀ {Γ : Ctx} {bound arg lhs rhs : Term} {s : Stack},
    WSubMStar Γ arg bound →
      MEqRed ({ bound := bound, kind := .sub } :: Γ) s lhs rhs →
        MEqRed Γ (Stack.instantiate 0 arg s)
          (Term.instantiate 0 arg lhs) (Term.instantiate 0 arg rhs)

/-- Stack-parametric subtype-reduction substitution payload for de Bruijn
β-instantiation. -/
def BetaInstantiationPreservesMSubRedStack : Type :=
  ∀ {Γ : Ctx} {bound arg lhs rhs : Term} {s : Stack},
    WSubMStar Γ arg bound →
      MSubRed ({ bound := bound, kind := .sub } :: Γ) s lhs rhs →
        MSubRed Γ (Stack.instantiate 0 arg s)
          (Term.instantiate 0 arg lhs) (Term.instantiate 0 arg rhs)

/-- Empty-stack subtype-reduction substitution payload targeting the
diagrammatic-star layer. This weaker target matches the de Bruijn `Ms-Pro`
head case, where a well-subtyping chain naturally erases to `MSubStar`
rather than to one raw machine reduction step. -/
def BetaInstantiationPreservesMSubRedMSubStar : Prop :=
  ∀ {Γ : Ctx} {bound arg lhs rhs : Term},
    WSubMStar Γ arg bound →
      MSubRed ({ bound := bound, kind := .sub } :: Γ) [] lhs rhs →
        MSubStar Γ [] (Term.instantiate 0 arg lhs)
          (Term.instantiate 0 arg rhs)

/-- Stack-parametric subtype-reduction substitution payload targeting the
diagrammatic-star layer. -/
def BetaInstantiationPreservesMSubRedStackMSubStar : Prop :=
  ∀ {Γ : Ctx} {bound arg lhs rhs : Term} {s : Stack},
    WSubMStar Γ arg bound →
      MSubRed ({ bound := bound, kind := .sub } :: Γ) s lhs rhs →
        MSubStar Γ (Stack.instantiate 0 arg s)
          (Term.instantiate 0 arg lhs) (Term.instantiate 0 arg rhs)

/-- The remaining head-variable branch of arbitrary-stack `MSubRed.pro`
substitution. A source head `.sub` lookup reduces `bvar 0` to the lifted
bound; after β-instantiation this asks for a machine subtype reduction from
the argument to the instantiated lifted bound over the instantiated stack. -/
def BetaInstantiationPreservesMSubRedProHeadPayload : Type :=
  ∀ {Γ : Ctx} {bound arg : Term} {s : Stack},
    WSubMStar Γ arg bound →
      PrevalidExt ({ bound := bound, kind := .sub } :: Γ) s →
        MSubRed Γ (Stack.instantiate 0 arg s)
          (Term.instantiate 0 arg (.bvar 0))
          (Term.instantiate 0 arg (Term.shift 0 bound))

/-- Star-shaped variant of the `MSubRed.pro` head frontier. This is the shape
directly reachable from `WSubMStar.toMSubStar` plus diagrammatic stack
transport; collapsing it back to a raw machine subtype step is a separate
transitivity-elimination obligation. -/
def BetaInstantiationPreservesMSubRedProHeadMSubStarPayload : Prop :=
  ∀ {Γ : Ctx} {bound arg : Term} {s : Stack},
    WSubMStar Γ arg bound →
      PrevalidExt ({ bound := bound, kind := .sub } :: Γ) s →
        MSubStar Γ (Stack.instantiate 0 arg s)
          (Term.instantiate 0 arg (.bvar 0))
          (Term.instantiate 0 arg (Term.shift 0 bound))

/-- Body-level payload for the `MSubRed.fun_` case of star-targeted
β-instantiation. The body premise starts under the original function bound
`t`, while the reconstructed abstraction target requires the transformed body
chain under the equivalence target `t'`. -/
def BetaInstantiationPreservesMSubRedFunBodyMSubStarPayload : Prop :=
  ∀ {Γ : Ctx} {bound arg t t' body body' : Term},
    WSubMStar Γ arg bound →
      MEqRed Γ [] (Term.instantiate 0 arg t) (Term.instantiate 0 arg t') →
        MSubRed ({ bound := t, kind := .sub } ::
            { bound := bound, kind := .sub } :: Γ) [] body body' →
          MSubStar ({ bound := Term.instantiate 0 arg t', kind := .sub } :: Γ)
            [] (Term.instantiate 1 (Term.shift 0 arg) body)
            (Term.instantiate 1 (Term.shift 0 arg) body')

/-- Body-level payload for the `MSubRed.fOp` case of star-targeted
β-instantiation under the preserved operand `.equ` head. -/
def BetaInstantiationPreservesMSubRedFOpBodyMSubStarPayload : Prop :=
  ∀ {Γ : Ctx} {bound arg α body body' : Term} {s : Stack},
    WSubMStar Γ arg bound →
      MSubRed ({ bound := α, kind := .equ } ::
          { bound := bound, kind := .sub } :: Γ) (Stack.shift 0 s) body body' →
        MSubStar ({ bound := Term.instantiate 0 arg α, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.instantiate 0 arg s))
          (Term.instantiate 1 (Term.shift 0 arg) body)
          (Term.instantiate 1 (Term.shift 0 arg) body')

/-- Generic body-level payload for β-instantiation under one preserved
context head. The target stack keeps the direct pointwise instantiated shape;
constructor-specific adapters can rewrite it to shifted-tail form when needed.
-/
def BetaInstantiationPreservesMSubRedUnderHeadMSubStarPayload : Prop :=
  ∀ {Γ : Ctx} {bound arg head body body' : Term}
      {kind : CtxEntryKind} {s : Stack},
    WSubMStar Γ arg bound →
      MSubRed ({ bound := head, kind := kind } ::
          { bound := bound, kind := .sub } :: Γ) s body body' →
        MSubStar ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
          (Stack.instantiate 1 (Term.shift 0 arg) s)
          (Term.instantiate 1 (Term.shift 0 arg) body)
          (Term.instantiate 1 (Term.shift 0 arg) body')

/-- Stack-parametric equivalence-reduction β-instantiation under one
preserved context head. -/
def BetaInstantiationPreservesMEqRedUnderHeadStack : Type :=
  ∀ {Γ : Ctx} {bound arg head lhs rhs : Term}
      {kind : CtxEntryKind} {s : Stack},
    WSubMStar Γ arg bound →
      MEqRed ({ bound := head, kind := kind } ::
          { bound := bound, kind := .sub } :: Γ) s lhs rhs →
        MEqRed ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
          (Stack.instantiate 1 (Term.shift 0 arg) s)
          (Term.instantiate 1 (Term.shift 0 arg) lhs)
          (Term.instantiate 1 (Term.shift 0 arg) rhs)

/-- Generic stack-parametric equivalence-reduction β-instantiation under an
arbitrary list of preserved context heads. This is the abstraction that the
numbered five/six/seven/eight stack payloads below specialize from. -/
def BetaInstantiationPreservesMEqRedUnderHeadsStack (n : Nat) : Type :=
  ∀ {Γ : Ctx} {bound arg lhs rhs : Term} {heads : Ctx} {s : Stack},
    heads.length = n →
      WSubMStar Γ arg bound →
        MEqRed (heads ++ { bound := bound, kind := .sub } :: Γ) s lhs rhs →
          MEqRed (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
            (Stack.instantiate n (Term.shiftBy 0 n arg) s)
            (Term.instantiate n (Term.shiftBy 0 n arg) lhs)
            (Term.instantiate n (Term.shiftBy 0 n arg) rhs)

/-- The generic preserved-head stack payload specializes at zero heads to the
existing stack-parametric substitution surface. -/
def BetaInstantiationPreservesMEqRedStack.of_generic
    (h : BetaInstantiationPreservesMEqRedUnderHeadsStack 0) :
    BetaInstantiationPreservesMEqRedStack := by
  intro Γ bound arg lhs rhs s hArg hRed
  have h' := h (heads := []) rfl hArg hRed
  simpa [Ctx.instantiateBetaPrefix, Term.shiftBy_zero_id] using h'

/-- The existing stack-parametric substitution surface is the zero-head
specialization of the generic preserved-head payload. -/
def BetaInstantiationPreservesMEqRedUnderHeadsStack.of_stack
    (h : BetaInstantiationPreservesMEqRedStack) :
    BetaInstantiationPreservesMEqRedUnderHeadsStack 0 := by
  intro Γ bound arg lhs rhs heads s hlen hArg hRed
  cases heads with
  | nil =>
      have h' := h (Γ := Γ) (bound := bound) (arg := arg)
        (lhs := lhs) (rhs := rhs) (s := s) hArg hRed
      simpa [Ctx.instantiateBetaPrefix, Term.shiftBy_zero_id] using h'
  | cons head heads =>
      simp at hlen

/-- The generic preserved-head stack payload specializes to the existing
one-head surface. -/
def BetaInstantiationPreservesMEqRedUnderHeadStack.of_generic
    (h : BetaInstantiationPreservesMEqRedUnderHeadsStack 1) :
    BetaInstantiationPreservesMEqRedUnderHeadStack := by
  intro Γ bound arg head lhs rhs kind s hArg hRed
  have h' := h (heads := [{ bound := head, kind := kind }]) rfl hArg hRed
  simpa [Ctx.instantiateBetaPrefix, Term.shift, Term.shiftBy_compose,
    Term.shiftBy_zero_id, Nat.add_assoc] using h'

/-- Constructor-facing `Me-Fun` frontier for under-head equivalence
β-instantiation. The body premise lives under one additional `.sub` binder,
so this is the first recursive binder case left by the structural assembler.
-/
def BetaInstantiationPreservesMEqRedUnderHeadFunStackPayload : Type :=
  ∀ {Γ : Ctx} {bound arg head t t' body body' : Term}
      {kind : CtxEntryKind},
    WSubMStar Γ arg bound →
      MEqRed ({ bound := head, kind := kind } ::
          { bound := bound, kind := .sub } :: Γ) [] t t' →
        MEqRed ({ bound := t, kind := .sub } ::
            { bound := head, kind := kind } ::
            { bound := bound, kind := .sub } :: Γ) [] body body' →
          MEqRed ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
            [] (Term.instantiate 1 (Term.shift 0 arg) (.abs t body))
            (Term.instantiate 1 (Term.shift 0 arg) (.abs t' body'))

/-- Constructor-facing `Me-Bet` frontier for under-head equivalence
β-instantiation. This packages the β target arithmetic and body
substitution under the abstraction binder. -/
def BetaInstantiationPreservesMEqRedUnderHeadBetStackPayload : Type :=
  ∀ {Γ : Ctx} {bound arg head t v v' body body' : Term}
      {kind : CtxEntryKind} {s : Stack},
    WSubMStar Γ arg bound →
      Term.Scoped
        (Ctx.depth ({ bound := head, kind := kind } ::
          { bound := bound, kind := .sub } :: Γ)) t →
        MEqRed ({ bound := t, kind := .sub } ::
            { bound := head, kind := kind } ::
            { bound := bound, kind := .sub } :: Γ) (Stack.shift 0 s)
          body body' →
          MEqRed ({ bound := head, kind := kind } ::
              { bound := bound, kind := .sub } :: Γ) [] v v' →
            MEqRed ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
              (Stack.instantiate 1 (Term.shift 0 arg) s)
              (Term.instantiate 1 (Term.shift 0 arg) (.app (.abs t body) v))
              (Term.instantiate 1 (Term.shift 0 arg)
                (Term.instantiate 0 v' body'))

/-- Constructor-facing `Me-FOp` frontier for under-head equivalence
β-instantiation under the operand `.equ` binder. -/
def BetaInstantiationPreservesMEqRedUnderHeadFOpStackPayload : Type :=
  ∀ {Γ : Ctx} {bound arg head t t' α body body' : Term}
      {kind : CtxEntryKind} {s : Stack},
    WSubMStar Γ arg bound →
      MEqRed ({ bound := head, kind := kind } ::
          { bound := bound, kind := .sub } :: Γ) [] t t' →
        Term.Scoped
          (Ctx.depth ({ bound := head, kind := kind } ::
            { bound := bound, kind := .sub } :: Γ)) α →
          MEqRed ({ bound := α, kind := .equ } ::
              { bound := head, kind := kind } ::
              { bound := bound, kind := .sub } :: Γ) (Stack.shift 0 s)
            body body' →
            MEqRed ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
              (Stack.instantiate 1 (Term.shift 0 arg) (α :: s))
              (Term.instantiate 1 (Term.shift 0 arg) (.abs t body))
              (Term.instantiate 1 (Term.shift 0 arg) (.abs t' body'))

/-- Preserved-head `Ms-Pro` frontier for under-head star-targeted subtype
β-instantiation. -/
def BetaInstantiationPreservesMSubRedUnderHeadProMSubStarPayload : Prop :=
  ∀ {Γ : Ctx} {bound arg head target : Term}
      {kind : CtxEntryKind} {s : Stack} {i : Nat},
    WSubMStar Γ arg bound →
      PrevalidExt ({ bound := head, kind := kind } ::
          { bound := bound, kind := .sub } :: Γ) s →
        Ctx.subBinds ({ bound := head, kind := kind } ::
            { bound := bound, kind := .sub } :: Γ) i target →
          MSubStar ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
            (Stack.instantiate 1 (Term.shift 0 arg) s)
            (Term.instantiate 1 (Term.shift 0 arg) (.bvar i))
            (Term.instantiate 1 (Term.shift 0 arg) target)

/-- Constructor-facing `Ms-Fun` frontier for under-head star-targeted subtype
β-instantiation. -/
def BetaInstantiationPreservesMSubRedUnderHeadFunMSubStarPayload : Prop :=
  ∀ {Γ : Ctx} {bound arg head t t' body body' : Term}
      {kind : CtxEntryKind},
    WSubMStar Γ arg bound →
      Term.Scoped
        (Ctx.depth ({ bound := head, kind := kind } ::
          { bound := bound, kind := .sub } :: Γ)) t →
        MEqRed ({ bound := head, kind := kind } ::
          { bound := bound, kind := .sub } :: Γ) [] t t' →
        MSubRed ({ bound := t, kind := .sub } ::
          { bound := head, kind := kind } ::
          { bound := bound, kind := .sub } :: Γ) [] body body' →
          MSubStar ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
            [] (Term.instantiate 1 (Term.shift 0 arg) (.abs t body))
            (Term.instantiate 1 (Term.shift 0 arg) (.abs t' body'))

/-- Constructor-facing `Ms-FOp` frontier for under-head star-targeted subtype
β-instantiation. -/
def BetaInstantiationPreservesMSubRedUnderHeadFOpMSubStarPayload : Prop :=
  ∀ {Γ : Ctx} {bound arg head t α body body' : Term}
      {kind : CtxEntryKind} {s : Stack},
    WSubMStar Γ arg bound →
      Term.Scoped
        (Ctx.depth ({ bound := head, kind := kind } ::
          { bound := bound, kind := .sub } :: Γ)) t →
        Term.Scoped
          (Ctx.depth ({ bound := head, kind := kind } ::
            { bound := bound, kind := .sub } :: Γ)) α →
        MSubRed ({ bound := α, kind := .equ } ::
          { bound := head, kind := kind } ::
          { bound := bound, kind := .sub } :: Γ) (Stack.shift 0 s) body body' →
          MSubStar ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
            (Stack.instantiate 1 (Term.shift 0 arg) (α :: s))
            (Term.instantiate 1 (Term.shift 0 arg) (.abs t body))
            (Term.instantiate 1 (Term.shift 0 arg) (.abs t body'))

/-- Changed-bound transport needed after applying generic under-head
β-instantiation to the `MSubRed.fun_` body premise. This is not a general
`.sub` head replacement theorem: arbitrary subtype chains can use `Ms-Pro` at
the changed head. -/
def BetaInstantiationPreservesMSubRedFunBodyHeadChangeMSubStarPayload : Prop :=
  ∀ {Γ : Ctx} {bound arg t t' body body' : Term},
    WSubMStar Γ arg bound →
      MEqRed Γ [] (Term.instantiate 0 arg t) (Term.instantiate 0 arg t') →
        MSubStar ({ bound := Term.instantiate 0 arg t, kind := .sub } :: Γ)
          [] (Term.instantiate 1 (Term.shift 0 arg) body)
          (Term.instantiate 1 (Term.shift 0 arg) body') →
          MSubStar ({ bound := Term.instantiate 0 arg t', kind := .sub } :: Γ)
            [] (Term.instantiate 1 (Term.shift 0 arg) body)
            (Term.instantiate 1 (Term.shift 0 arg) body')

/-- The de Bruijn β-instantiation preservation frontier is not blocked on
scoping: substituting an argument for the innermost body variable preserves
the ambient context depth. The remaining payload is the MPSS well-formedness
reconstruction captured by `BetaInstantiationPreservesWfM`. -/
noncomputable def BetaInstantiationPreservesScoped
    {Γ : Ctx} {bound body arg : Term}
    (hArgBound : WSubMStar Γ arg bound)
    (hBody : WfM ({ bound := bound, kind := .sub } :: Γ) body) :
    Term.Scoped Γ.depth (Term.instantiate 0 arg body) :=
  Term.instantiate_scoped 0 Γ.depth arg body (Nat.zero_le Γ.depth)
    hArgBound.scoped_left hBody.scoped

/-- Stack-parametric equivalence-reduction substitution specializes to the
existing empty-stack payload. -/
noncomputable def BetaInstantiationPreservesMEqRed.of_stack
    (hStack : BetaInstantiationPreservesMEqRedStack) :
    BetaInstantiationPreservesMEqRed := by
  intro Γ bound arg lhs rhs hArgBound hred
  simpa using hStack hArgBound hred

/-- Stack-parametric subtype-reduction substitution specializes to the
existing empty-stack payload. -/
noncomputable def BetaInstantiationPreservesMSubRed.of_stack
    (hStack : BetaInstantiationPreservesMSubRedStack) :
    BetaInstantiationPreservesMSubRed := by
  intro Γ bound arg lhs rhs hArgBound hred
  simpa using hStack hArgBound hred

/-- Raw stack-parametric subtype-reduction substitution embeds into the
weaker diagrammatic-star target. -/
noncomputable def BetaInstantiationPreservesMSubRedStackMSubStar.of_raw
    (hRaw : BetaInstantiationPreservesMSubRedStack) :
    BetaInstantiationPreservesMSubRedStackMSubStar := by
  intro Γ bound arg lhs rhs s hArgBound hred
  exact MSubStar.of_MSubRed (hRaw hArgBound hred)

/-- Stack-parametric diagrammatic-star subtype-reduction substitution
specializes to the empty-stack star payload. -/
noncomputable def BetaInstantiationPreservesMSubRedMSubStar.of_stack
    (hStack : BetaInstantiationPreservesMSubRedStackMSubStar) :
    BetaInstantiationPreservesMSubRedMSubStar := by
  intro Γ bound arg lhs rhs hArgBound hred
  simpa using hStack hArgBound hred

/-- Raw empty-stack subtype-reduction substitution embeds into the
empty-stack diagrammatic-star target. -/
noncomputable def BetaInstantiationPreservesMSubRedMSubStar.of_raw
    (hRaw : BetaInstantiationPreservesMSubRed) :
    BetaInstantiationPreservesMSubRedMSubStar := by
  intro Γ bound arg lhs rhs hArgBound hred
  exact MSubStar.of_MSubRed (hRaw hArgBound hred)

/-- Prevalidity of an instantiated stack follows from source-stack
prevalidity and the substituted argument's scopedness. -/
noncomputable def BetaInstantiationPreservesPrevalidExtStack
    {Γ : Ctx} {bound arg : Term} {s : Stack}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) s) :
    PrevalidExt Γ (Stack.instantiate 0 arg s) := by
  have hs : Stack.Scoped Γ.depth (Stack.instantiate 0 arg s) :=
    Stack.Scoped.instantiate (Nat.zero_le Γ.depth) hArgBound.scoped_left
      (by
        simpa [Ctx.depth, Nat.succ_eq_add_one] using
          PrevalidExt.stack_scoped hpv)
  exact PrevalidExt.of_stack_scoped hArgBound.prevalid hs

/-- Extract the stored head-bound scopedness from a prevalid non-empty
context, uniformly over the entry kind. -/
private noncomputable def prevalid_head_scoped
    {Γ : Ctx} {head : Term} {kind : CtxEntryKind}
    (hpv : Prevalid ({ bound := head, kind := kind } :: Γ)) :
    Term.Scoped Γ.depth head := by
  cases kind with
  | sub =>
      cases hpv with
      | sub _ hHead => exact hHead
  | equ =>
      cases hpv with
      | equ _ hHead => exact hHead

/-- Generic prevalidity transport for the preserved context prefix after a
β-instantiation removes the `.sub` entry below it. -/
noncomputable def BetaInstantiationPreservesPrevalidPrefix
    {Γ : Ctx} {bound arg : Term} (heads : Ctx)
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : Prevalid (heads ++ { bound := bound, kind := .sub } :: Γ)) :
    Prevalid (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ) := by
  induction heads with
  | nil =>
      simpa [Ctx.instantiateBetaPrefix] using Prevalid.tail hpv
  | cons head heads ih =>
      have hpvTail :
          Prevalid (heads ++ { bound := bound, kind := .sub } :: Γ) :=
        Prevalid.tail hpv
      have hTail := ih hpvTail
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgBound.scoped_left
      have hHeadScoped :
          Term.Scoped (Γ.depth + heads.length + 1) head.bound := by
        simpa [Ctx.depth, List.length_append, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using prevalid_head_scoped hpv
      have hHeadInstScoped :
          Term.Scoped
            (Ctx.depth (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) head.bound) := by
        have hInst := Term.instantiate_scoped heads.length
          (Γ.depth + heads.length) (Term.shiftBy 0 heads.length arg)
          head.bound (by omega) hArgShiftScoped hHeadScoped
        simpa [Ctx.depth, List.length_append, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hInst
      cases head with
      | mk headBound kind =>
          cases kind with
          | sub =>
              exact Prevalid.sub hTail hHeadInstScoped
          | equ =>
              exact Prevalid.equ hTail hHeadInstScoped

/-- Generic prevalidity transport for β-instantiation under an arbitrary
number of preserved context heads. -/
noncomputable def BetaInstantiationPreservesPrevalidExtUnderHeads
    {Γ : Ctx} {bound arg : Term} {heads : Ctx} {s : Stack} {n : Nat}
    (hlen : heads.length = n)
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt (heads ++ { bound := bound, kind := .sub } :: Γ) s) :
    PrevalidExt (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
      (Stack.instantiate n (Term.shiftBy 0 n arg) s) := by
  subst hlen
  have hctx :=
    BetaInstantiationPreservesPrevalidPrefix heads hArgBound (PrevalidExt.ctx hpv)
  have hArgShiftScoped :
      Term.Scoped (Γ.depth + heads.length)
        (Term.shiftBy 0 heads.length arg) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Term.shiftBy_scoped 0 heads.length Γ.depth arg
        (Nat.zero_le Γ.depth) hArgBound.scoped_left
  have hsSource :
      Stack.Scoped (Γ.depth + heads.length + 1) s := by
    simpa [Ctx.depth, List.length_append, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using PrevalidExt.stack_scoped hpv
  have hsTarget :
      Stack.Scoped
        (Ctx.depth (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
        (Stack.instantiate heads.length
          (Term.shiftBy 0 heads.length arg) s) := by
    have hStack := Stack.Scoped.instantiate
      (depth := Γ.depth + heads.length)
      (k := heads.length)
      (v := Term.shiftBy 0 heads.length arg)
      (s := s) (by omega) hArgShiftScoped hsSource
    simpa [Ctx.depth, List.length_append, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hStack
  exact PrevalidExt.of_stack_scoped hctx hsTarget

/-- Result package for transporting an `.equ` lookup through the generic
β-instantiation prefix. -/
structure Ctx.EquBindsInstantiateBetaPrefixResult
    (Γ : Ctx) (arg α : Term) (heads : Ctx) (i : Nat) where
  j : Nat
  var_eq :
    Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) (.bvar i) =
      .bvar j
  bind :
    Ctx.equBinds (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ) j
      (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) α)

/-- Transport an `.equ` lookup through the generic β-instantiation prefix.
The result index accounts for the removed `.sub` entry below `heads`, and
the variable-instantiation equality identifies the corresponding target
`bvar`. -/
noncomputable def Ctx.equBinds_instantiateBetaPrefix
    {Γ : Ctx} {bound arg α : Term} {heads : Ctx} {i : Nat}
    (hb : Ctx.equBinds (heads ++ { bound := bound, kind := .sub } :: Γ) i α) :
    Ctx.EquBindsInstantiateBetaPrefixResult Γ arg α heads i := by
  induction heads generalizing i α with
  | nil =>
      cases i with
      | zero =>
          simp [Ctx.equBinds] at hb
      | succ i =>
          simp [Ctx.equBinds] at hb
          let tailTarget := Classical.choose hb
          have htailAnd := Classical.choose_spec hb
          have htailLookup : Ctx.lookupEqu Γ i = some tailTarget := htailAnd.1
          have htarget : Term.shift 0 tailTarget = α := htailAnd.2
          have htargetInst :
              Term.instantiate 0 arg α = tailTarget := by
            simpa [← htarget] using Term.instantiate_shift_id 0 arg tailTarget
          have htargetInst' :
              Term.instantiate 0 (Term.shiftBy 0 0 arg) α = tailTarget := by
            simpa [Term.shiftBy_zero_id] using htargetInst
          refine ⟨i, ?_, ?_⟩
          · simp [Term.instantiate]
          · simpa [Ctx.instantiateBetaPrefix, Ctx.equBinds, htargetInst'] using
              htailLookup
  | cons head heads ih =>
      cases head with
      | mk headBound kind =>
          cases i with
          | zero =>
              cases kind with
              | sub =>
                  simp [Ctx.equBinds] at hb
              | equ =>
                  simp [Ctx.equBinds] at hb
                  subst hb
                  have htargetInst :
                      Term.instantiate (heads.length + 1)
                          (Term.shiftBy 0 (heads.length + 1) arg)
                          (Term.shift 0 headBound) =
                        Term.shift 0
                          (Term.instantiate heads.length
                            (Term.shiftBy 0 heads.length arg) headBound) := by
                    have h := Term.instantiate_succ_shift_zero heads.length
                      (Term.shiftBy 0 heads.length arg) headBound
                    simpa [Term.shift, Term.shiftBy_compose, Nat.add_assoc] using h
                  refine ⟨0, ?_, ?_⟩
                  · simp [Term.instantiate]
                  · simp [Ctx.instantiateBetaPrefix, Ctx.equBinds, htargetInst]
          | succ i =>
              simp [Ctx.equBinds] at hb
              let tailTarget := Classical.choose hb
              have htailAnd := Classical.choose_spec hb
              have htailLookup :
                  Ctx.lookupEqu (heads ++ { bound := bound, kind := .sub } :: Γ) i =
                    some tailTarget := htailAnd.1
              have htarget : Term.shift 0 tailTarget = α := htailAnd.2
              have hbTail :
                  Ctx.equBinds (heads ++ { bound := bound, kind := .sub } :: Γ)
                    i tailTarget := by
                simpa [Ctx.equBinds] using htailLookup
              rcases ih hbTail with ⟨j, hvar, hbind⟩
              have hvarCurrent :
                  Term.instantiate (heads.length + 1)
                      (Term.shiftBy 0 (heads.length + 1) arg) (.bvar (i + 1)) =
                    Term.shift 0
                      (Term.instantiate heads.length
                        (Term.shiftBy 0 heads.length arg) (.bvar i)) := by
                have h := Term.instantiate_succ_shift_zero heads.length
                  (Term.shiftBy 0 heads.length arg) (.bvar i)
                simpa [Term.shift, Term.shiftBy_compose, Nat.add_assoc] using h
              have htargetInst :
                  Term.instantiate (heads.length + 1)
                      (Term.shiftBy 0 (heads.length + 1) arg) α =
                    Term.shift 0
                      (Term.instantiate heads.length
                        (Term.shiftBy 0 heads.length arg) tailTarget) := by
                have h := Term.instantiate_succ_shift_zero heads.length
                  (Term.shiftBy 0 heads.length arg) tailTarget
                simpa [← htarget, Term.shift, Term.shiftBy_compose,
                  Nat.add_assoc] using h
              refine ⟨j + 1, ?_, ?_⟩
              · change
                  Term.instantiate (heads.length + 1)
                      (Term.shiftBy 0 (heads.length + 1) arg) (.bvar (i + 1)) =
                    .bvar (j + 1)
                rw [hvarCurrent, hvar]
                simp [Term.shift]
              · let headEntry : CtxEntry :=
                  { bound := Term.instantiate heads.length
                      (Term.shiftBy 0 heads.length arg) headBound,
                    kind := kind }
                change Ctx.equBinds
                  (headEntry :: (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
                  (j + 1)
                  (Term.instantiate (heads.length + 1)
                    (Term.shiftBy 0 (heads.length + 1) arg) α)
                rw [htargetInst]
                simpa [headEntry] using
                  Ctx.equBinds_weaken_head headEntry hbind

/-- Generic `MEqRed.pro` transport for β-instantiation below an arbitrary
preserved-head prefix. -/
noncomputable def BetaInstantiationPreservesMEqRedUnderHeadsStack.pro
    {Γ : Ctx} {bound arg α α' : Term} {heads : Ctx} {s : Stack} {i : Nat}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt (heads ++ { bound := bound, kind := .sub } :: Γ) s)
    (hb : Ctx.equBinds (heads ++ { bound := bound, kind := .sub } :: Γ) i α)
    (hα :
      MEqRed (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
        (Stack.instantiate heads.length (Term.shiftBy 0 heads.length arg) s)
        (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) α)
        (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) α')) :
    MEqRed (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
      (Stack.instantiate heads.length (Term.shiftBy 0 heads.length arg) s)
      (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) (.bvar i))
      (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) α') := by
  have hpvTarget := BetaInstantiationPreservesPrevalidExtUnderHeads
    (n := heads.length) rfl hArgBound hpv
  rcases Ctx.equBinds_instantiateBetaPrefix
      (Γ := Γ) (bound := bound) (arg := arg) (heads := heads) hb with
    ⟨j, hvar, hbind⟩
  rw [hvar]
  exact MEqRed.pro hpvTarget hbind hα

/-- **Universal β-instantiation under any number of preserved context heads.**

This is the single induction that subsumes the entire per-depth ladder
`BetaInstantiationPreservesMEqRedUnder{Zero,One,...,ThirtySeven}HeadsStack`.
Recursion is on the `MEqRed` derivation with `n`, `heads`, and the stack
generalized; the binder cases (`bet`, `fun_`, `fOp`) consume the IH at
`(n + 1, newHead :: heads, ...)`. The substitution-composition algebra
needed by the `bet` target is `Term.instantiate_zero_after_many`. -/
noncomputable def BetaInstantiationPreservesMEqRedUnderHeadsStack_universal :
    ∀ n, BetaInstantiationPreservesMEqRedUnderHeadsStack n := by
  intro n Γ bound arg lhs rhs heads s hlen hArgBound hRed
  -- Eliminate the explicit `n` parameter; the proof works directly with
  -- `heads.length`. This unifies the algebra at the cost of one substitution.
  subst hlen
  -- Generalize the MEqRed's context so the induction can reshape it across
  -- binder sub-derivations.
  generalize hC : (heads ++ ({ bound := bound, kind := .sub } :: Γ : Ctx)) =
    C at hRed
  induction hRed generalizing heads with
  | pro hpv hb hα ih =>
      subst hC
      exact BetaInstantiationPreservesMEqRedUnderHeadsStack.pro
        (Γ := Γ) (bound := bound) (arg := arg) (heads := heads)
        hArgBound hpv hb (ih (heads := heads) rfl)
  | top hpv =>
      subst hC
      have hpvTarget := BetaInstantiationPreservesPrevalidExtUnderHeads
        (n := heads.length) rfl hArgBound hpv
      simpa [Term.instantiate] using MEqRed.top hpvTarget
  | @app Γ' s' u u' v v' hOp hArg' ihOp ihArg =>
      subst hC
      have hOp' := ihOp (heads := heads) rfl
      have hArg' := ihArg (heads := heads) rfl
      simpa [Term.instantiate, Stack.instantiate] using MEqRed.app hOp' hArg'
  | @var Γ' s' i hpv hi =>
      subst hC
      have hpvTarget := BetaInstantiationPreservesPrevalidExtUnderHeads
        (n := heads.length) rfl hArgBound hpv
      have hArgScoped : Term.Scoped Γ.depth arg := hArgBound.scoped_left
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgScoped
      have hi_lt : i < Γ.depth + heads.length + 1 := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := bound, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at hi
        omega
      have hbvar_scoped :
          Term.Scoped (Γ.depth + heads.length + 1) (.bvar i) :=
        Term.Scoped.bvar hi_lt
      have hLHSScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) (.bvar i)) :=
        Term.instantiate_scoped heads.length (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg) (.bvar i) (by omega)
          hArgShiftScoped hbvar_scoped
      have hLHSScoped' :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) (.bvar i)) := by
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hLHSScoped
      exact MEqRed.refl hpvTarget hLHSScoped'
  | @tAp Γ' s' u hpv hu =>
      subst hC
      have hpvTarget := BetaInstantiationPreservesPrevalidExtUnderHeads
        (n := heads.length) rfl hArgBound hpv
      have hArgScoped : Term.Scoped Γ.depth arg := hArgBound.scoped_left
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgScoped
      have hu' : Term.Scoped (Γ.depth + heads.length + 1) u := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := bound, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at hu
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hu
      have huInstScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) u) :=
        Term.instantiate_scoped heads.length (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg) u (by omega)
          hArgShiftScoped hu'
      have huInstScoped' :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) u) := by
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using huInstScoped
      simpa [Term.instantiate] using MEqRed.tAp hpvTarget huInstScoped'
  | @bet Γ' s' t v v' body body' ht hbody harg ihBody ihArg =>
      subst hC
      have hBody' :=
        ihBody (heads := { bound := t, kind := .sub } :: heads)
          (by simp [List.cons_append])
      have hArg' := ihArg (heads := heads) rfl
      have hLen_succ :
          ({ bound := t, kind := .sub } :: heads : Ctx).length =
            heads.length + 1 := by simp
      have hshift_succ :
          Term.shiftBy 0 (heads.length + 1) arg =
            Term.shift 0 (Term.shiftBy 0 heads.length arg) := by
        have h := Term.shiftBy_compose 0 heads.length 1 arg
        simpa [Term.shift] using h.symm
      have hStack_succ :
          Stack.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) (Stack.shift 0 s') =
            Stack.shift 0 (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) s') := by
        rw [hshift_succ]
        exact Stack.instantiate_succ_shift_zero heads.length
          (Term.shiftBy 0 heads.length arg) s'
      have hCtx_succ :
          Ctx.instantiateBetaPrefix arg (heads.length + 1)
              ({ bound := t, kind := .sub } :: heads) =
            { bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) t,
                kind := .sub } ::
              Ctx.instantiateBetaPrefix arg heads.length heads := by
        simp [Ctx.instantiateBetaPrefix]
      have hArgScoped : Term.Scoped Γ.depth arg := hArgBound.scoped_left
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgScoped
      have htOriginal : Term.Scoped (Γ.depth + heads.length + 1) t := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := bound, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at ht
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht
      have htInstScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) t) :=
        Term.instantiate_scoped heads.length (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg) t (by omega)
          hArgShiftScoped htOriginal
      have htInstScoped' :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) t) := by
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htInstScoped
      have hBodyReady :
          MEqRed
            ({ bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) t,
                kind := .sub } ::
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Stack.shift 0 (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) s'))
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body)
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body') := by
        simp only [List.length_cons] at hBody'
        rw [hCtx_succ] at hBody'
        rw [hStack_succ] at hBody'
        simpa using hBody'
      have hBet :=
        MEqRed.bet
          (Γ := Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
          (s := Stack.instantiate heads.length
            (Term.shiftBy 0 heads.length arg) s')
          (t := Term.instantiate heads.length
            (Term.shiftBy 0 heads.length arg) t)
          (v := Term.instantiate heads.length
            (Term.shiftBy 0 heads.length arg) v)
          (v' := Term.instantiate heads.length
            (Term.shiftBy 0 heads.length arg) v')
          (body := Term.instantiate (heads.length + 1)
            (Term.shiftBy 0 (heads.length + 1) arg) body)
          (body' := Term.instantiate (heads.length + 1)
            (Term.shiftBy 0 (heads.length + 1) arg) body')
          htInstScoped' hBodyReady hArg'
      have hTarget :
          Term.instantiate 0
              (Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) v')
              (Term.instantiate (heads.length + 1)
                (Term.shiftBy 0 (heads.length + 1) arg) body') =
            Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg)
              (Term.instantiate 0 v' body') := by
        rw [hshift_succ]
        exact Term.instantiate_zero_after_many heads.length
          (Term.shiftBy 0 heads.length arg) v' body'
      simpa [Term.instantiate, hTarget, ← hshift_succ] using hBet
  | @fun_ Γ' t t' body body' hT hBody ihT ihBody =>
      subst hC
      have hT' := ihT (heads := heads) rfl
      have hBody' :=
        ihBody (heads := { bound := t, kind := .sub } :: heads)
          (by simp [List.cons_append])
      have hLen_succ :
          ({ bound := t, kind := .sub } :: heads : Ctx).length =
            heads.length + 1 := by simp
      have hCtx_succ :
          Ctx.instantiateBetaPrefix arg (heads.length + 1)
              ({ bound := t, kind := .sub } :: heads) =
            { bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) t,
                kind := .sub } ::
              Ctx.instantiateBetaPrefix arg heads.length heads := by
        simp [Ctx.instantiateBetaPrefix]
      have hshift_succ :
          Term.shiftBy 0 (heads.length + 1) arg =
            Term.shift 0 (Term.shiftBy 0 heads.length arg) := by
        have h := Term.shiftBy_compose 0 heads.length 1 arg
        simpa [Term.shift] using h.symm
      have hBodyReady :
          MEqRed
            ({ bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) t,
                kind := .sub } ::
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            []
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body)
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body') := by
        simp only [List.length_cons] at hBody'
        rw [hCtx_succ] at hBody'
        simpa using hBody'
      have hFun := MEqRed.fun_ hT' hBodyReady
      simpa [Term.instantiate, hshift_succ] using hFun
  | @fOp Γ' s' t t' α body body' hT hα hBody ihT ihBody =>
      subst hC
      have hT' := ihT (heads := heads) rfl
      have hBody' :=
        ihBody (heads := { bound := α, kind := .equ } :: heads)
          (by simp [List.cons_append])
      have hLen_succ :
          ({ bound := α, kind := .equ } :: heads : Ctx).length =
            heads.length + 1 := by simp
      have hshift_succ :
          Term.shiftBy 0 (heads.length + 1) arg =
            Term.shift 0 (Term.shiftBy 0 heads.length arg) := by
        have h := Term.shiftBy_compose 0 heads.length 1 arg
        simpa [Term.shift] using h.symm
      have hStack_succ :
          Stack.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) (Stack.shift 0 s') =
            Stack.shift 0 (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) s') := by
        rw [hshift_succ]
        exact Stack.instantiate_succ_shift_zero heads.length
          (Term.shiftBy 0 heads.length arg) s'
      have hCtx_succ :
          Ctx.instantiateBetaPrefix arg (heads.length + 1)
              ({ bound := α, kind := .equ } :: heads) =
            { bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) α,
                kind := .equ } ::
              Ctx.instantiateBetaPrefix arg heads.length heads := by
        simp [Ctx.instantiateBetaPrefix]
      have hArgScoped : Term.Scoped Γ.depth arg := hArgBound.scoped_left
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgScoped
      have hαOriginal : Term.Scoped (Γ.depth + heads.length + 1) α := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := bound, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at hα
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hα
      have hαInstScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) α) :=
        Term.instantiate_scoped heads.length (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg) α (by omega)
          hArgShiftScoped hαOriginal
      have hαInstScoped' :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) α) := by
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hαInstScoped
      have hBodyReady :
          MEqRed
            ({ bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) α,
                kind := .equ } ::
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Stack.shift 0 (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) s'))
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body)
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body') := by
        simp only [List.length_cons] at hBody'
        rw [hCtx_succ] at hBody'
        rw [hStack_succ] at hBody'
        simpa using hBody'
      have hFOp := MEqRed.fOp hT' hαInstScoped' hBodyReady
      simpa [Term.instantiate, Stack.instantiate, hshift_succ] using hFOp

/-- The closed equivalence-reduction substitution payload, proved
unconditionally via the universal `∀n` β-instantiation theorem.

This wires `BetaInstantiationPreservesMEqRedUnderHeadsStack_universal` into
the empty-prefix surface used by downstream consumers; `BetaInstantiationPreservesMEqRedStack`
no longer needs to be assumed.

**Note on the missing `MSubRed` companion.** A parallel
`BetaInstantiationPreservesMSubRedStack_proved` would be the obvious next
step, but the `MSubRed.pro` head case is not provable from the universal
companion alone: at `bvar 0` the source head case asks for a single raw
`MSubRed Γ s arg bound` step, but the only premise we have is
`WSubMStar Γ arg bound`, which produces `MSubStar` (a transitive closure)
rather than a single raw step. Collapsing star to raw is itself the
content of transitivity-elimination. Consequently the closed `MSubRed`
surface remains assumed at the `BetaInstantiationPreservesMSubRedStack`
type level; only the diagrammatic-star variant
(`BetaInstantiationPreservesMSubRedStackMSubStar.of_constructors`) admits a
direct constructor-level proof. The historical per-depth ladder for
`MSubRed` (when it briefly existed) targeted `MSubStar` for exactly this
reason. -/
noncomputable def BetaInstantiationPreservesMEqRedStack_proved :
    BetaInstantiationPreservesMEqRedStack :=
  BetaInstantiationPreservesMEqRedStack.of_generic
    (BetaInstantiationPreservesMEqRedUnderHeadsStack_universal 0)

/-! ## subBinds transport for β-instantiation prefix -/

/-- Result-package classification for transporting an `.sub` lookup through
the generic β-instantiation prefix. The lookup either lands in a preserved
head (or in `Γ`) — in which case the instantiated context yields a fresh
`subBinds` — or it lands on the dropped `.sub` head, which collapses
`bvar i` after instantiation to the lifted `arg` and the target to the
lifted `bound`. -/
inductive Ctx.SubBindsInstantiateBetaPrefixCase
    (Γ : Ctx) (arg bound target : Term) (heads : Ctx) (i : Nat) : Prop where
  | preserved (j : Nat)
      (var_eq :
        Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) (.bvar i) =
          .bvar j)
      (bind :
        Ctx.subBinds (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ) j
          (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) target))
  | argHead
      (heq : i = heads.length)
      (var_eq :
        Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) (.bvar i) =
          Term.shiftBy 0 heads.length arg)
      (target_eq :
        Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) target =
          Term.shiftBy 0 heads.length bound)

/-- Transport an `.sub` lookup through the generic β-instantiation prefix.
Mirrors `Ctx.equBinds_instantiateBetaPrefix` but classifies the lookup into
either a preserved binding or the dropped `.sub` head. -/
theorem Ctx.subBinds_instantiateBetaPrefix
    {Γ : Ctx} {bound arg target : Term} {heads : Ctx} {i : Nat}
    (hb :
      Ctx.subBinds (heads ++ { bound := bound, kind := .sub } :: Γ) i target) :
    Ctx.SubBindsInstantiateBetaPrefixCase Γ arg bound target heads i := by
  induction heads generalizing i target with
  | nil =>
      cases i with
      | zero =>
          -- Lookup hits the dropped `.sub` head.
          simp [Ctx.subBinds] at hb
          subst hb
          refine Ctx.SubBindsInstantiateBetaPrefixCase.argHead rfl ?_ ?_
          · simp [Term.instantiate]
          · simpa [Term.shiftBy_zero_id] using
              Term.instantiate_shift_id 0 arg bound
      | succ i =>
          -- Lookup descends into `Γ`.
          simp [Ctx.subBinds] at hb
          rcases hb with ⟨tailTarget, htail, htarget⟩
          subst htarget
          have hbind :
              Ctx.subBinds Γ i tailTarget := by
            simpa [Ctx.subBinds] using htail
          have htargetInst :
              Term.instantiate 0 arg (Term.shift 0 tailTarget) = tailTarget :=
            Term.instantiate_shift_id 0 arg tailTarget
          have htargetInst' :
              Term.instantiate 0 (Term.shiftBy 0 0 arg) (Term.shift 0 tailTarget)
                = tailTarget := by
            simpa [Term.shiftBy_zero_id] using htargetInst
          refine Ctx.SubBindsInstantiateBetaPrefixCase.preserved i ?_ ?_
          · simp [Term.instantiate]
          · simpa [Ctx.instantiateBetaPrefix, Ctx.subBinds, htargetInst'] using
              hbind
  | cons head heads ih =>
      cases head with
      | mk headBound kind =>
          cases i with
          | zero =>
              cases kind with
              | sub =>
                  -- Lookup is the head's lifted bound.
                  simp [Ctx.subBinds] at hb
                  subst hb
                  refine Ctx.SubBindsInstantiateBetaPrefixCase.preserved 0 ?_ ?_
                  · simp [Term.instantiate]
                  · have htargetInst :
                        Term.instantiate (heads.length + 1)
                            (Term.shiftBy 0 (heads.length + 1) arg)
                            (Term.shift 0 headBound) =
                          Term.shift 0
                            (Term.instantiate heads.length
                              (Term.shiftBy 0 heads.length arg) headBound) := by
                      have h := Term.instantiate_succ_shift_zero heads.length
                        (Term.shiftBy 0 heads.length arg) headBound
                      simpa [Term.shift, Term.shiftBy_compose, Nat.add_assoc]
                        using h
                    simp [Ctx.instantiateBetaPrefix, Ctx.subBinds, htargetInst]
              | equ =>
                  simp [Ctx.subBinds] at hb
          | succ i =>
              -- Recurse through `heads`.
              simp [Ctx.subBinds] at hb
              rcases hb with ⟨tailTarget, htail, htarget⟩
              subst htarget
              have hbTail :
                  Ctx.subBinds (heads ++ { bound := bound, kind := .sub } :: Γ)
                    i tailTarget := by
                simpa [Ctx.subBinds] using htail
              cases ih (i := i) (target := tailTarget) hbTail with
              | preserved j hvar hbind =>
                  have hvarCurrent :
                      Term.instantiate (heads.length + 1)
                          (Term.shiftBy 0 (heads.length + 1) arg) (.bvar (i + 1)) =
                        Term.shift 0
                          (Term.instantiate heads.length
                            (Term.shiftBy 0 heads.length arg) (.bvar i)) := by
                    have h := Term.instantiate_succ_shift_zero heads.length
                      (Term.shiftBy 0 heads.length arg) (.bvar i)
                    simpa [Term.shift, Term.shiftBy_compose, Nat.add_assoc]
                      using h
                  have htargetInst :
                      Term.instantiate (heads.length + 1)
                          (Term.shiftBy 0 (heads.length + 1) arg)
                          (Term.shift 0 tailTarget) =
                        Term.shift 0
                          (Term.instantiate heads.length
                            (Term.shiftBy 0 heads.length arg) tailTarget) := by
                    have h := Term.instantiate_succ_shift_zero heads.length
                      (Term.shiftBy 0 heads.length arg) tailTarget
                    simpa [Term.shift, Term.shiftBy_compose, Nat.add_assoc]
                      using h
                  refine Ctx.SubBindsInstantiateBetaPrefixCase.preserved (j + 1)
                    ?_ ?_
                  · change
                      Term.instantiate (heads.length + 1)
                          (Term.shiftBy 0 (heads.length + 1) arg)
                          (.bvar (i + 1)) =
                        .bvar (j + 1)
                    rw [hvarCurrent, hvar]
                    simp [Term.shift]
                  · let headEntry : CtxEntry :=
                      { bound := Term.instantiate heads.length
                          (Term.shiftBy 0 heads.length arg) headBound,
                        kind := kind }
                    change Ctx.subBinds
                      (headEntry ::
                        (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
                      (j + 1)
                      (Term.instantiate (heads.length + 1)
                        (Term.shiftBy 0 (heads.length + 1) arg)
                        (Term.shift 0 tailTarget))
                    rw [htargetInst]
                    simpa [headEntry] using
                      Ctx.subBinds_weaken_head headEntry hbind
              | argHead heq hvar htarget_eq =>
                  -- Promote: i = heads.length, so source index is heads.length + 1
                  -- which equals the new prefix length.
                  refine Ctx.SubBindsInstantiateBetaPrefixCase.argHead ?_ ?_ ?_
                  · simp [heq]
                  · -- bvar (i + 1) = bvar (heads.length + 1) instantiates to
                    -- `Term.shiftBy 0 (heads.length + 1) arg`.
                    subst heq
                    simp [Term.instantiate]
                  · -- Goal length unfolds to heads.length + 1.
                    show Term.instantiate (heads.length + 1)
                        (Term.shiftBy 0 (heads.length + 1) arg)
                        (Term.shift 0 tailTarget) =
                      Term.shiftBy 0 (heads.length + 1) bound
                    have hshift :
                        Term.instantiate (heads.length + 1)
                            (Term.shiftBy 0 (heads.length + 1) arg)
                            (Term.shift 0 tailTarget) =
                          Term.shift 0
                            (Term.instantiate heads.length
                              (Term.shiftBy 0 heads.length arg) tailTarget) := by
                      have h := Term.instantiate_succ_shift_zero heads.length
                        (Term.shiftBy 0 heads.length arg) tailTarget
                      simpa [Term.shift, Term.shiftBy_compose, Nat.add_assoc]
                        using h
                    rw [hshift, htarget_eq]
                    have hcomp :
                        Term.shiftBy 0 (heads.length + 1) bound =
                          Term.shift 0 (Term.shiftBy 0 heads.length bound) := by
                      have h := Term.shiftBy_compose 0 heads.length 1 bound
                      simpa [Term.shift] using h.symm
                    rw [hcomp]

/-! ## MSubRed → MSubStar β-instantiation prep -/

/-- Generic stack-parametric subtype-reduction β-instantiation under an
arbitrary list of preserved context heads, targeting the diagrammatic-star
layer. This is the abstraction the universal `∀n` theorem proves directly.
-/
def BetaInstantiationPreservesMSubRedUnderHeadsStackMSubStar (n : Nat) : Prop :=
  ∀ {Γ : Ctx} {bound arg lhs rhs : Term} {heads : Ctx} {s : Stack},
    heads.length = n →
      WSubMStar Γ arg bound →
        MSubRed (heads ++ { bound := bound, kind := .sub } :: Γ) s lhs rhs →
          MSubStar (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
            (Stack.instantiate n (Term.shiftBy 0 n arg) s)
            (Term.instantiate n (Term.shiftBy 0 n arg) lhs)
            (Term.instantiate n (Term.shiftBy 0 n arg) rhs)

/-- Specialize the generic preserved-head MSubStar payload to zero heads,
yielding the empty-prefix stack-targeted surface. -/
noncomputable def BetaInstantiationPreservesMSubRedStackMSubStar.of_underHeads_zero
    (h : BetaInstantiationPreservesMSubRedUnderHeadsStackMSubStar 0) :
    BetaInstantiationPreservesMSubRedStackMSubStar := by
  intro Γ bound arg lhs rhs s hArg hRed
  have h' := h (heads := []) rfl hArg hRed
  simpa [Ctx.instantiateBetaPrefix, Term.shiftBy_zero_id] using h'

/-! ## Symmetric β-instantiation respect (`MEqRedRespectsBetaInstantiate`)

This is a *symmetric* companion to the asymmetric β-instantiation surface
above. Instead of asking for a `WSubMStar Γ arg bound` premise to relate the
substituted argument to the dropped `.sub` head, this surface bakes the
argument **into** the discharged `.sub` head — so the LHS and RHS contexts
agree on the argument and the lemma needs no ambient subtype premise, only
scoping.

This is the shape needed by the `bet × bet` diamond cell: when both the
abstraction body and the inner argument move by `MEqRed`, the two β-fires
must be reconciled at a common β-target `Term.instantiate 0 arg' body'`. The
symmetric form above only handles the body half (with `arg` fixed); the
caller composes a separate `MEqRed`-step on the argument position to bridge
to `arg'`.

**Why symmetric and not asymmetric.** The natural statement for `bet × bet`
would have the LHS instantiate by the *original* argument and the RHS
instantiate by the *reduced* argument: an asymmetric form. That form is
genuinely harder because the `MEqRed.var` case at `i = heads.length` would
need to lift `MEqRed Γ [] arg arg'` to a non-empty stack
`Stack.instantiate n (shiftBy 0 n arg') s`, and stack-extension is **not**
generally valid for de Bruijn `MEqRed`: the only constructors that fire on
abstractions are `fun_` (empty stack) and `fOp` (specific stack head). Per
the symmetric-vs-asymmetric tradeoff documented in the dispatch outline,
the symmetric form is "strictly easier" and the asymmetric form was
attempted but walls at this var-stack-extension point. The downstream
caller composes the symmetric form with a separate argument-position
transport.
-/

/-- Scope-only analogue of `BetaInstantiationPreservesPrevalidPrefix`. The
substituted argument is not related to any pre-existing `.sub` head; instead
the dropped head's bound *is* `arg`, and we only need its scoping. -/
noncomputable def BetaInstantiationPreservesPrevalidPrefixOfScoped
    {Γ : Ctx} {arg : Term} (heads : Ctx)
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hpv : Prevalid (heads ++ { bound := arg, kind := .sub } :: Γ)) :
    Prevalid (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ) := by
  induction heads with
  | nil =>
      simpa [Ctx.instantiateBetaPrefix] using Prevalid.tail hpv
  | cons head heads ih =>
      have hpvTail :
          Prevalid (heads ++ { bound := arg, kind := .sub } :: Γ) :=
        Prevalid.tail hpv
      have hTail := ih hpvTail
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgScoped
      have hHeadScoped :
          Term.Scoped (Γ.depth + heads.length + 1) head.bound := by
        simpa [Ctx.depth, List.length_append, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using prevalid_head_scoped hpv
      have hHeadInstScoped :
          Term.Scoped
            (Ctx.depth (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) head.bound) := by
        have hInst := Term.instantiate_scoped heads.length
          (Γ.depth + heads.length) (Term.shiftBy 0 heads.length arg)
          head.bound (by omega) hArgShiftScoped hHeadScoped
        simpa [Ctx.depth, List.length_append, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hInst
      cases head with
      | mk headBound kind =>
          cases kind with
          | sub =>
              exact Prevalid.sub hTail hHeadInstScoped
          | equ =>
              exact Prevalid.equ hTail hHeadInstScoped

/-- Scope-only analogue of `BetaInstantiationPreservesPrevalidExtUnderHeads`.
-/
noncomputable def BetaInstantiationPreservesPrevalidExtUnderHeadsOfScoped
    {Γ : Ctx} {arg : Term} {heads : Ctx} {s : Stack} {n : Nat}
    (hlen : heads.length = n)
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hpv : PrevalidExt (heads ++ { bound := arg, kind := .sub } :: Γ) s) :
    PrevalidExt (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
      (Stack.instantiate n (Term.shiftBy 0 n arg) s) := by
  subst hlen
  have hctx :=
    BetaInstantiationPreservesPrevalidPrefixOfScoped heads hArgScoped
      (PrevalidExt.ctx hpv)
  have hArgShiftScoped :
      Term.Scoped (Γ.depth + heads.length)
        (Term.shiftBy 0 heads.length arg) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Term.shiftBy_scoped 0 heads.length Γ.depth arg
        (Nat.zero_le Γ.depth) hArgScoped
  have hsSource :
      Stack.Scoped (Γ.depth + heads.length + 1) s := by
    simpa [Ctx.depth, List.length_append, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using PrevalidExt.stack_scoped hpv
  have hsTarget :
      Stack.Scoped
        (Ctx.depth (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
        (Stack.instantiate heads.length
          (Term.shiftBy 0 heads.length arg) s) := by
    have hStack := Stack.Scoped.instantiate
      (depth := Γ.depth + heads.length)
      (k := heads.length)
      (v := Term.shiftBy 0 heads.length arg)
      (s := s) (by omega) hArgShiftScoped hsSource
    simpa [Ctx.depth, List.length_append, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hStack
  exact PrevalidExt.of_stack_scoped hctx hsTarget

/-- Scope-only analogue of `Ctx.equBinds_instantiateBetaPrefix`: transports
an `.equ` lookup through the symmetric β-instantiation prefix. The
underlying algebra is identical to the asymmetric version because the
`bound` parameter only appears as the `.sub` entry being dropped, not as
an algebraic input. -/
noncomputable def Ctx.equBinds_instantiateBetaPrefix_ofScoped
    {Γ : Ctx} {arg α : Term} {heads : Ctx} {i : Nat}
    (hb : Ctx.equBinds (heads ++ { bound := arg, kind := .sub } :: Γ) i α) :
    Ctx.EquBindsInstantiateBetaPrefixResult Γ arg α heads i :=
  Ctx.equBinds_instantiateBetaPrefix (bound := arg) hb

/-- Symmetric β-instantiation under any number of preserved context heads,
indexed by the number of preserved heads. The argument moves nowhere — both
sides instantiate by the same `arg`, and only the body/stack chain reduces.

This is the symmetric companion to
`BetaInstantiationPreservesMEqRedUnderHeadsStack`, taking only
`Term.Scoped Γ.depth arg` as the argument-side premise instead of a
`WSubMStar` chain. The dropped `.sub` entry's bound is `arg` itself. -/
def MEqRedRespectsBetaInstantiateUnderHeadsStack (n : Nat) : Type :=
  ∀ {Γ : Ctx} {arg lhs rhs : Term} {heads : Ctx} {s : Stack},
    heads.length = n →
      Term.Scoped Γ.depth arg →
        MEqRed (heads ++ { bound := arg, kind := .sub } :: Γ) s lhs rhs →
          MEqRed (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
            (Stack.instantiate n (Term.shiftBy 0 n arg) s)
            (Term.instantiate n (Term.shiftBy 0 n arg) lhs)
            (Term.instantiate n (Term.shiftBy 0 n arg) rhs)

/-- Symmetric closed-stack β-instantiation: at empty preserved-prefix the
universal lemma collapses to substituting `arg` directly under the dropped
`.sub` head. -/
def MEqRedRespectsBetaInstantiateStack : Type :=
  ∀ {Γ : Ctx} {arg lhs rhs : Term} {s : Stack},
    Term.Scoped Γ.depth arg →
      MEqRed ({ bound := arg, kind := .sub } :: Γ) s lhs rhs →
        MEqRed Γ (Stack.instantiate 0 arg s)
          (Term.instantiate 0 arg lhs)
          (Term.instantiate 0 arg rhs)

/-- Generic `MEqRed.pro` transport for symmetric β-instantiation below an
arbitrary preserved-head prefix. -/
noncomputable def MEqRedRespectsBetaInstantiateUnderHeadsStack.pro
    {Γ : Ctx} {arg α α' : Term} {heads : Ctx} {s : Stack} {i : Nat}
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hpv : PrevalidExt (heads ++ { bound := arg, kind := .sub } :: Γ) s)
    (hb : Ctx.equBinds (heads ++ { bound := arg, kind := .sub } :: Γ) i α)
    (hα :
      MEqRed (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
        (Stack.instantiate heads.length (Term.shiftBy 0 heads.length arg) s)
        (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) α)
        (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) α')) :
    MEqRed (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
      (Stack.instantiate heads.length (Term.shiftBy 0 heads.length arg) s)
      (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) (.bvar i))
      (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg) α') := by
  have hpvTarget := BetaInstantiationPreservesPrevalidExtUnderHeadsOfScoped
    (n := heads.length) rfl hArgScoped hpv
  rcases Ctx.equBinds_instantiateBetaPrefix_ofScoped
      (Γ := Γ) (arg := arg) (heads := heads) hb with
    ⟨j, hvar, hbind⟩
  rw [hvar]
  exact MEqRed.pro hpvTarget hbind hα

/-- The zero-prefix specialization of the universal symmetric
β-instantiation theorem matches the closed-stack surface. -/
def MEqRedRespectsBetaInstantiateStack.of_generic
    (h : MEqRedRespectsBetaInstantiateUnderHeadsStack 0) :
    MEqRedRespectsBetaInstantiateStack := by
  intro Γ arg lhs rhs s hArgScoped hRed
  have h' := h (heads := []) rfl hArgScoped hRed
  simpa [Ctx.instantiateBetaPrefix, Term.shiftBy_zero_id] using h'

/-- **Universal symmetric β-instantiation respect** under any number of
preserved context heads.

Mirrors `BetaInstantiationPreservesMEqRedUnderHeadsStack_universal` but
with `Term.Scoped Γ.depth arg` instead of a `WSubMStar` chain. The
discharged `.sub` head's bound is `arg` itself, so the LHS and RHS
contexts agree on the dropped binder. The induction is unchanged from the
asymmetric universal — every algebraic step that consumed `hArgBound`
consumed it via `.scoped_left`, which we now have directly. -/
noncomputable def MEqRedRespectsBetaInstantiateUnderHeadsStack_universal :
    ∀ n, MEqRedRespectsBetaInstantiateUnderHeadsStack n := by
  intro n Γ arg lhs rhs heads s hlen hArgScoped hRed
  subst hlen
  generalize hC : (heads ++ ({ bound := arg, kind := .sub } :: Γ : Ctx)) =
    C at hRed
  induction hRed generalizing heads with
  | pro hpv hb hα ih =>
      subst hC
      exact MEqRedRespectsBetaInstantiateUnderHeadsStack.pro
        (Γ := Γ) (arg := arg) (heads := heads)
        hArgScoped hpv hb (ih (heads := heads) rfl)
  | top hpv =>
      subst hC
      have hpvTarget := BetaInstantiationPreservesPrevalidExtUnderHeadsOfScoped
        (n := heads.length) rfl hArgScoped hpv
      simpa [Term.instantiate] using MEqRed.top hpvTarget
  | @app Γ' s' u u' v v' hOp hArg' ihOp ihArg =>
      subst hC
      have hOp' := ihOp (heads := heads) rfl
      have hArg' := ihArg (heads := heads) rfl
      simpa [Term.instantiate, Stack.instantiate] using MEqRed.app hOp' hArg'
  | @var Γ' s' i hpv hi =>
      subst hC
      have hpvTarget := BetaInstantiationPreservesPrevalidExtUnderHeadsOfScoped
        (n := heads.length) rfl hArgScoped hpv
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgScoped
      have hi_lt : i < Γ.depth + heads.length + 1 := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := arg, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at hi
        omega
      have hbvar_scoped :
          Term.Scoped (Γ.depth + heads.length + 1) (.bvar i) :=
        Term.Scoped.bvar hi_lt
      have hLHSScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) (.bvar i)) :=
        Term.instantiate_scoped heads.length (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg) (.bvar i) (by omega)
          hArgShiftScoped hbvar_scoped
      have hLHSScoped' :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) (.bvar i)) := by
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hLHSScoped
      exact MEqRed.refl hpvTarget hLHSScoped'
  | @tAp Γ' s' u hpv hu =>
      subst hC
      have hpvTarget := BetaInstantiationPreservesPrevalidExtUnderHeadsOfScoped
        (n := heads.length) rfl hArgScoped hpv
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgScoped
      have hu' : Term.Scoped (Γ.depth + heads.length + 1) u := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := arg, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at hu
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hu
      have huInstScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) u) :=
        Term.instantiate_scoped heads.length (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg) u (by omega)
          hArgShiftScoped hu'
      have huInstScoped' :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) u) := by
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using huInstScoped
      simpa [Term.instantiate] using MEqRed.tAp hpvTarget huInstScoped'
  | @bet Γ' s' t v v' body body' ht hbody harg ihBody ihArg =>
      subst hC
      have hBody' :=
        ihBody (heads := { bound := t, kind := .sub } :: heads)
          (by simp [List.cons_append])
      have hArg' := ihArg (heads := heads) rfl
      have hLen_succ :
          ({ bound := t, kind := .sub } :: heads : Ctx).length =
            heads.length + 1 := by simp
      have hshift_succ :
          Term.shiftBy 0 (heads.length + 1) arg =
            Term.shift 0 (Term.shiftBy 0 heads.length arg) := by
        have h := Term.shiftBy_compose 0 heads.length 1 arg
        simpa [Term.shift] using h.symm
      have hStack_succ :
          Stack.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) (Stack.shift 0 s') =
            Stack.shift 0 (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) s') := by
        rw [hshift_succ]
        exact Stack.instantiate_succ_shift_zero heads.length
          (Term.shiftBy 0 heads.length arg) s'
      have hCtx_succ :
          Ctx.instantiateBetaPrefix arg (heads.length + 1)
              ({ bound := t, kind := .sub } :: heads) =
            { bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) t,
                kind := .sub } ::
              Ctx.instantiateBetaPrefix arg heads.length heads := by
        simp [Ctx.instantiateBetaPrefix]
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgScoped
      have htOriginal : Term.Scoped (Γ.depth + heads.length + 1) t := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := arg, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at ht
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht
      have htInstScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) t) :=
        Term.instantiate_scoped heads.length (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg) t (by omega)
          hArgShiftScoped htOriginal
      have htInstScoped' :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) t) := by
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htInstScoped
      have hBodyReady :
          MEqRed
            ({ bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) t,
                kind := .sub } ::
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Stack.shift 0 (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) s'))
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body)
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body') := by
        simp only [List.length_cons] at hBody'
        rw [hCtx_succ] at hBody'
        rw [hStack_succ] at hBody'
        simpa using hBody'
      have hBet :=
        MEqRed.bet
          (Γ := Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
          (s := Stack.instantiate heads.length
            (Term.shiftBy 0 heads.length arg) s')
          (t := Term.instantiate heads.length
            (Term.shiftBy 0 heads.length arg) t)
          (v := Term.instantiate heads.length
            (Term.shiftBy 0 heads.length arg) v)
          (v' := Term.instantiate heads.length
            (Term.shiftBy 0 heads.length arg) v')
          (body := Term.instantiate (heads.length + 1)
            (Term.shiftBy 0 (heads.length + 1) arg) body)
          (body' := Term.instantiate (heads.length + 1)
            (Term.shiftBy 0 (heads.length + 1) arg) body')
          htInstScoped' hBodyReady hArg'
      have hTarget :
          Term.instantiate 0
              (Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) v')
              (Term.instantiate (heads.length + 1)
                (Term.shiftBy 0 (heads.length + 1) arg) body') =
            Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg)
              (Term.instantiate 0 v' body') := by
        rw [hshift_succ]
        exact Term.instantiate_zero_after_many heads.length
          (Term.shiftBy 0 heads.length arg) v' body'
      simpa [Term.instantiate, hTarget, ← hshift_succ] using hBet
  | @fun_ Γ' t t' body body' hT hBody ihT ihBody =>
      subst hC
      have hT' := ihT (heads := heads) rfl
      have hBody' :=
        ihBody (heads := { bound := t, kind := .sub } :: heads)
          (by simp [List.cons_append])
      have hCtx_succ :
          Ctx.instantiateBetaPrefix arg (heads.length + 1)
              ({ bound := t, kind := .sub } :: heads) =
            { bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) t,
                kind := .sub } ::
              Ctx.instantiateBetaPrefix arg heads.length heads := by
        simp [Ctx.instantiateBetaPrefix]
      have hshift_succ :
          Term.shiftBy 0 (heads.length + 1) arg =
            Term.shift 0 (Term.shiftBy 0 heads.length arg) := by
        have h := Term.shiftBy_compose 0 heads.length 1 arg
        simpa [Term.shift] using h.symm
      have hBodyReady :
          MEqRed
            ({ bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) t,
                kind := .sub } ::
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            []
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body)
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body') := by
        simp only [List.length_cons] at hBody'
        rw [hCtx_succ] at hBody'
        simpa using hBody'
      have hFun := MEqRed.fun_ hT' hBodyReady
      simpa [Term.instantiate, hshift_succ] using hFun
  | @fOp Γ' s' t t' α body body' hT hα hBody ihT ihBody =>
      subst hC
      have hT' := ihT (heads := heads) rfl
      have hBody' :=
        ihBody (heads := { bound := α, kind := .equ } :: heads)
          (by simp [List.cons_append])
      have hshift_succ :
          Term.shiftBy 0 (heads.length + 1) arg =
            Term.shift 0 (Term.shiftBy 0 heads.length arg) := by
        have h := Term.shiftBy_compose 0 heads.length 1 arg
        simpa [Term.shift] using h.symm
      have hStack_succ :
          Stack.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) (Stack.shift 0 s') =
            Stack.shift 0 (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) s') := by
        rw [hshift_succ]
        exact Stack.instantiate_succ_shift_zero heads.length
          (Term.shiftBy 0 heads.length arg) s'
      have hCtx_succ :
          Ctx.instantiateBetaPrefix arg (heads.length + 1)
              ({ bound := α, kind := .equ } :: heads) =
            { bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) α,
                kind := .equ } ::
              Ctx.instantiateBetaPrefix arg heads.length heads := by
        simp [Ctx.instantiateBetaPrefix]
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgScoped
      have hαOriginal : Term.Scoped (Γ.depth + heads.length + 1) α := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := arg, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at hα
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hα
      have hαInstScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) α) :=
        Term.instantiate_scoped heads.length (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg) α (by omega)
          hArgShiftScoped hαOriginal
      have hαInstScoped' :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) α) := by
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hαInstScoped
      have hBodyReady :
          MEqRed
            ({ bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) α,
                kind := .equ } ::
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Stack.shift 0 (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) s'))
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body)
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body') := by
        simp only [List.length_cons] at hBody'
        rw [hCtx_succ] at hBody'
        rw [hStack_succ] at hBody'
        simpa using hBody'
      have hFOp := MEqRed.fOp hT' hαInstScoped' hBodyReady
      simpa [Term.instantiate, Stack.instantiate, hshift_succ] using hFOp

/-- Closed symmetric β-instantiation respect for de Bruijn `MEqRed`,
proved unconditionally via the universal `∀n` symmetric theorem.

This is the load-bearing surface for the `bet × bet` diamond cell: when an
abstraction body reduces under a `.sub`-bound argument, the post-β
instantiation preserves equivalence-reduction. The argument itself does
not move in this surface; the caller composes a separate
argument-position transport for `bet × bet`'s asymmetric closure. -/
noncomputable def MEqRedRespectsBetaInstantiateStack_proved :
    MEqRedRespectsBetaInstantiateStack :=
  MEqRedRespectsBetaInstantiateStack.of_generic
    (MEqRedRespectsBetaInstantiateUnderHeadsStack_universal 0)

/-! ## Fused kind-narrowing β-substitution

The `bet × bet` diamond cell would ideally consume a **fully asymmetric**
β-substitution surface where the LHS body is instantiated by the original
argument `arg` and the RHS body by its post-step `arg'`. That fully
asymmetric shape is, however, **structurally impossible to prove as a
single `MEqRed` step**: the `Me-FOp` constructor's stack-head and body-
context binder are syntactically the same `α`, and the asymmetric LHS/
RHS substitution would require them to be `α[arg/n]` versus `α[arg'/n]`
respectively whenever `α` references the discharged binder. Both `Me-Pro`
discharge (post-context lookups must agree with the body recursive
premise's LHS endpoint) and `Me-FOp` constructor consistency (the body
binder must match the stack head) impose conflicting constraints on
which substitution argument the post-substitution context uses.

The closest provable surface that **enables the `bet × bet` cell** is the
**fused kind-narrowing β-substitution**: a body derivation in `.sub`-head
context with bound `arg` is converted to substitution by `arg'` (the
post-step argument), with both LHS and RHS uniformly substituted by
`arg'`. This is structurally identical to the symmetric form except that
the dropped `.sub` head's bound (`arg`) and the substitution argument
(`arg'`) are **decoupled**: the proof goes through unchanged with `arg'`
playing the role of the substitution argument throughout, with `arg`
appearing only as the source context's discharged head bound. The
"fusion" is with `MEqRed.sub_to_equ_head_replace` (commit `8e72b12`,
`Pss/Mpss/DeBruijnReductions.lean:1953`), which would convert the
`.sub`-bound source body to an `.equ`-bound body before substitution;
the present surface skips that explicit conversion and substitutes
directly by `arg'`, achieving the same downstream effect.

For the `bet × bet` consumer, this surface combines with the body
diamond closure and `v`'s diamond closure to produce a chain
`MEqRedStar` from `instantiate 0 v₁' body₁'` to a common reduct
`instantiate 0 v₃ body₃`. A single-`MEqRed`-step bridge for that chain
is foreclosed by the structural conflicts described above; the diamond
cell composes along the chain. -/

/-- Universal fused kind-narrowing β-substitution under any number of
preserved context heads, indexed by the number of preserved heads. The
dropped `.sub` head's bound is `arg`; the substitution argument is
`arg'`. Both must be scoped at `Γ.depth`. The proof structure mirrors the
symmetric case, with `arg'` substituting throughout the post-context,
post-stack, and post-body. -/
def MEqRedFusedKindNarrowedBetaSubstUnderHeadsStack (n : Nat) : Type :=
  ∀ {Γ : Ctx} {arg arg' lhs rhs : Term} {heads : Ctx} {s : Stack},
    heads.length = n →
      Term.Scoped Γ.depth arg →
        Term.Scoped Γ.depth arg' →
          MEqRed (heads ++ { bound := arg, kind := .sub } :: Γ) s lhs rhs →
            MEqRed (Ctx.instantiateBetaPrefix arg' n heads ++ Γ)
              (Stack.instantiate n (Term.shiftBy 0 n arg') s)
              (Term.instantiate n (Term.shiftBy 0 n arg') lhs)
              (Term.instantiate n (Term.shiftBy 0 n arg') rhs)

/-- Closed-stack fused kind-narrowing β-substitution: at empty preserved-
prefix the universal lemma collapses to the natural surface used by the
`bet × bet` diamond's chain closure. -/
def MEqRedFusedKindNarrowedBetaSubstStack : Type :=
  ∀ {Γ : Ctx} {arg arg' lhs rhs : Term} {s : Stack},
    Term.Scoped Γ.depth arg →
      Term.Scoped Γ.depth arg' →
        MEqRed ({ bound := arg, kind := .sub } :: Γ) s lhs rhs →
          MEqRed Γ (Stack.instantiate 0 arg' s)
            (Term.instantiate 0 arg' lhs)
            (Term.instantiate 0 arg' rhs)

/-- Asymmetric prevalidity helper: prevalidity of the post-substitution
context (using `arg'`) with post-stack (using `arg'`) when the source has
`{arg, .sub}` head. Both `arg` and `arg'` need only be scoped at `Γ.depth`. -/
noncomputable def BetaInstantiationPreservesPrevalidPrefixKindNarrowed
    {Γ : Ctx} {arg arg' : Term} (heads : Ctx)
    (hArg'Scoped : Term.Scoped Γ.depth arg')
    (hpv : Prevalid (heads ++ { bound := arg, kind := .sub } :: Γ)) :
    Prevalid (Ctx.instantiateBetaPrefix arg' heads.length heads ++ Γ) := by
  induction heads with
  | nil =>
      simpa [Ctx.instantiateBetaPrefix] using Prevalid.tail hpv
  | cons head heads ih =>
      have hpvTail :
          Prevalid (heads ++ { bound := arg, kind := .sub } :: Γ) :=
        Prevalid.tail hpv
      have hTail := ih hpvTail
      have hArg'ShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg') := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg'
            (Nat.zero_le Γ.depth) hArg'Scoped
      have hHeadScoped :
          Term.Scoped (Γ.depth + heads.length + 1) head.bound := by
        simpa [Ctx.depth, List.length_append, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using prevalid_head_scoped hpv
      have hHeadInstScoped :
          Term.Scoped
            (Ctx.depth (Ctx.instantiateBetaPrefix arg' heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg') head.bound) := by
        have hInst := Term.instantiate_scoped heads.length
          (Γ.depth + heads.length) (Term.shiftBy 0 heads.length arg')
          head.bound (by omega) hArg'ShiftScoped hHeadScoped
        simpa [Ctx.depth, List.length_append, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hInst
      cases head with
      | mk headBound kind =>
          cases kind with
          | sub =>
              exact Prevalid.sub hTail hHeadInstScoped
          | equ =>
              exact Prevalid.equ hTail hHeadInstScoped

/-- Asymmetric `PrevalidExt` helper: the post-substitution context uses
`arg'` (the substitution argument) and the post-stack uses `arg'`. -/
noncomputable def BetaInstantiationPreservesPrevalidExtUnderHeadsKindNarrowed
    {Γ : Ctx} {arg arg' : Term} {heads : Ctx} {s : Stack} {n : Nat}
    (hlen : heads.length = n)
    (hArg'Scoped : Term.Scoped Γ.depth arg')
    (hpv : PrevalidExt (heads ++ { bound := arg, kind := .sub } :: Γ) s) :
    PrevalidExt (Ctx.instantiateBetaPrefix arg' n heads ++ Γ)
      (Stack.instantiate n (Term.shiftBy 0 n arg') s) := by
  subst hlen
  have hctx :=
    BetaInstantiationPreservesPrevalidPrefixKindNarrowed heads hArg'Scoped
      (PrevalidExt.ctx hpv)
  have hArg'ShiftScoped :
      Term.Scoped (Γ.depth + heads.length)
        (Term.shiftBy 0 heads.length arg') := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Term.shiftBy_scoped 0 heads.length Γ.depth arg'
        (Nat.zero_le Γ.depth) hArg'Scoped
  have hsSource :
      Stack.Scoped (Γ.depth + heads.length + 1) s := by
    simpa [Ctx.depth, List.length_append, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using PrevalidExt.stack_scoped hpv
  have hsTarget :
      Stack.Scoped
        (Ctx.depth (Ctx.instantiateBetaPrefix arg' heads.length heads ++ Γ))
        (Stack.instantiate heads.length
          (Term.shiftBy 0 heads.length arg') s) := by
    have hStack := Stack.Scoped.instantiate
      (depth := Γ.depth + heads.length)
      (k := heads.length)
      (v := Term.shiftBy 0 heads.length arg')
      (s := s) (by omega) hArg'ShiftScoped hsSource
    simpa [Ctx.depth, List.length_append, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hStack
  exact PrevalidExt.of_stack_scoped hctx hsTarget

/-- Generic `MEqRed.pro` transport for fused kind-narrowing β-substitution
below an arbitrary preserved-head prefix. The post-context uses the
substitution argument `arg'`, so `equBinds` lookups return targets
substituted by `arg'`, matching the body recursive premise's LHS
endpoint. -/
noncomputable def MEqRedFusedKindNarrowedBetaSubstUnderHeadsStack.pro
    {Γ : Ctx} {arg arg' α α' : Term} {heads : Ctx} {s : Stack} {i : Nat}
    (hArg'Scoped : Term.Scoped Γ.depth arg')
    (hpv : PrevalidExt (heads ++ { bound := arg, kind := .sub } :: Γ) s)
    (hb : Ctx.equBinds (heads ++ { bound := arg, kind := .sub } :: Γ) i α)
    (hα :
      MEqRed (Ctx.instantiateBetaPrefix arg' heads.length heads ++ Γ)
        (Stack.instantiate heads.length (Term.shiftBy 0 heads.length arg') s)
        (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg') α)
        (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg') α')) :
    MEqRed (Ctx.instantiateBetaPrefix arg' heads.length heads ++ Γ)
      (Stack.instantiate heads.length (Term.shiftBy 0 heads.length arg') s)
      (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg')
        (.bvar i))
      (Term.instantiate heads.length (Term.shiftBy 0 heads.length arg')
        α') := by
  have hpvTarget :=
    BetaInstantiationPreservesPrevalidExtUnderHeadsKindNarrowed
      (n := heads.length) rfl hArg'Scoped hpv
  rcases Ctx.equBinds_instantiateBetaPrefix
      (Γ := Γ) (bound := arg) (arg := arg') (heads := heads) hb with
    ⟨j, hvar, hbind⟩
  rw [hvar]
  exact MEqRed.pro hpvTarget hbind hα

/-- The zero-prefix specialization of the universal fused kind-narrowing
β-substitution theorem matches the closed-stack surface. -/
def MEqRedFusedKindNarrowedBetaSubstStack.of_generic
    (h : MEqRedFusedKindNarrowedBetaSubstUnderHeadsStack 0) :
    MEqRedFusedKindNarrowedBetaSubstStack := by
  intro Γ arg arg' lhs rhs s hArgScoped hArg'Scoped hRed
  have h' := h (heads := []) rfl hArgScoped hArg'Scoped hRed
  simpa [Ctx.instantiateBetaPrefix, Term.shiftBy_zero_id] using h'

/-- **Universal fused kind-narrowing β-substitution respect** under any
number of preserved context heads.

Mirrors `MEqRedRespectsBetaInstantiateUnderHeadsStack_universal` but with
the substitution argument `arg'` decoupled from the discharged `.sub`
head's bound `arg`. The proof is structurally identical, with `arg'`
replacing `arg` everywhere except in the source context shape. -/
noncomputable def MEqRedFusedKindNarrowedBetaSubstUnderHeadsStack_universal :
    ∀ n, MEqRedFusedKindNarrowedBetaSubstUnderHeadsStack n := by
  intro n Γ arg arg' lhs rhs heads s hlen hArgScoped hArg'Scoped hRed
  subst hlen
  generalize hC : (heads ++ ({ bound := arg, kind := .sub } :: Γ : Ctx)) =
    C at hRed
  induction hRed generalizing heads with
  | pro hpv hb hα ih =>
      subst hC
      exact MEqRedFusedKindNarrowedBetaSubstUnderHeadsStack.pro
        (Γ := Γ) (arg := arg) (arg' := arg') (heads := heads)
        hArg'Scoped hpv hb (ih (heads := heads) rfl)
  | top hpv =>
      subst hC
      have hpvTarget :=
        BetaInstantiationPreservesPrevalidExtUnderHeadsKindNarrowed
          (n := heads.length) rfl hArg'Scoped hpv
      simpa [Term.instantiate] using MEqRed.top hpvTarget
  | @app Γ' s' u u' v v' hOp hArg ihOp ihArg =>
      subst hC
      have hOp' := ihOp (heads := heads) rfl
      have hArgRec := ihArg (heads := heads) rfl
      simpa [Term.instantiate, Stack.instantiate] using
        MEqRed.app hOp' (by simpa [Stack.instantiate] using hArgRec)
  | @var Γ' s' i hpv hi =>
      subst hC
      have hpvTarget :=
        BetaInstantiationPreservesPrevalidExtUnderHeadsKindNarrowed
          (n := heads.length) rfl hArg'Scoped hpv
      have hArg'ShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg') := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg'
            (Nat.zero_le Γ.depth) hArg'Scoped
      have hi_lt : i < Γ.depth + heads.length + 1 := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := arg, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at hi
        omega
      have hbvar_scoped :
          Term.Scoped (Γ.depth + heads.length + 1) (.bvar i) :=
        Term.Scoped.bvar hi_lt
      have hScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg') (.bvar i)) :=
        Term.instantiate_scoped heads.length (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg') (.bvar i) (by omega)
          hArg'ShiftScoped hbvar_scoped
      have hScoped' :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg' heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg') (.bvar i)) := by
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hScoped
      exact MEqRed.refl hpvTarget hScoped'
  | @tAp Γ' s' u hpv hu =>
      subst hC
      have hpvTarget :=
        BetaInstantiationPreservesPrevalidExtUnderHeadsKindNarrowed
          (n := heads.length) rfl hArg'Scoped hpv
      have hArg'ShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg') := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg'
            (Nat.zero_le Γ.depth) hArg'Scoped
      have hu' : Term.Scoped (Γ.depth + heads.length + 1) u := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := arg, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at hu
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hu
      have huInstScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg') u) :=
        Term.instantiate_scoped heads.length (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg') u (by omega)
          hArg'ShiftScoped hu'
      have huInstScoped' :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg' heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg') u) := by
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using huInstScoped
      simpa [Term.instantiate] using MEqRed.tAp hpvTarget huInstScoped'
  | @bet Γ' s' t v v' body body' ht hbody harg ihBody ihArg =>
      subst hC
      have hBody' :=
        ihBody (heads := { bound := t, kind := .sub } :: heads)
          (by simp [List.cons_append])
      have hArgRec := ihArg (heads := heads) rfl
      have hshift_succ' :
          Term.shiftBy 0 (heads.length + 1) arg' =
            Term.shift 0 (Term.shiftBy 0 heads.length arg') := by
        have h := Term.shiftBy_compose 0 heads.length 1 arg'
        simpa [Term.shift] using h.symm
      have hStack_succ' :
          Stack.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg') (Stack.shift 0 s') =
            Stack.shift 0 (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg') s') := by
        rw [hshift_succ']
        exact Stack.instantiate_succ_shift_zero heads.length
          (Term.shiftBy 0 heads.length arg') s'
      have hCtx_succ :
          Ctx.instantiateBetaPrefix arg' (heads.length + 1)
              ({ bound := t, kind := .sub } :: heads) =
            { bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg') t,
                kind := .sub } ::
              Ctx.instantiateBetaPrefix arg' heads.length heads := by
        simp [Ctx.instantiateBetaPrefix]
      have hArg'ShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg') := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg'
            (Nat.zero_le Γ.depth) hArg'Scoped
      have htOriginal : Term.Scoped (Γ.depth + heads.length + 1) t := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := arg, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at ht
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht
      have htInstScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg') t) :=
        Term.instantiate_scoped heads.length (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg') t (by omega)
          hArg'ShiftScoped htOriginal
      have htInstScoped' :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg' heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg') t) := by
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htInstScoped
      have hBodyReady :
          MEqRed
            ({ bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg') t,
                kind := .sub } ::
              (Ctx.instantiateBetaPrefix arg' heads.length heads ++ Γ))
            (Stack.shift 0 (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg') s'))
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg') body)
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg') body') := by
        simp only [List.length_cons] at hBody'
        rw [hCtx_succ] at hBody'
        rw [hStack_succ'] at hBody'
        simpa using hBody'
      have hBet :=
        MEqRed.bet
          (Γ := Ctx.instantiateBetaPrefix arg' heads.length heads ++ Γ)
          (s := Stack.instantiate heads.length
            (Term.shiftBy 0 heads.length arg') s')
          (t := Term.instantiate heads.length
            (Term.shiftBy 0 heads.length arg') t)
          (v := Term.instantiate heads.length
            (Term.shiftBy 0 heads.length arg') v)
          (v' := Term.instantiate heads.length
            (Term.shiftBy 0 heads.length arg') v')
          (body := Term.instantiate (heads.length + 1)
            (Term.shiftBy 0 (heads.length + 1) arg') body)
          (body' := Term.instantiate (heads.length + 1)
            (Term.shiftBy 0 (heads.length + 1) arg') body')
          htInstScoped' hBodyReady hArgRec
      have hTarget :
          Term.instantiate 0
              (Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg') v')
              (Term.instantiate (heads.length + 1)
                (Term.shiftBy 0 (heads.length + 1) arg') body') =
            Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg')
              (Term.instantiate 0 v' body') := by
        rw [hshift_succ']
        exact Term.instantiate_zero_after_many heads.length
          (Term.shiftBy 0 heads.length arg') v' body'
      simpa [Term.instantiate, hTarget, ← hshift_succ'] using hBet
  | @fun_ Γ' t t' body body' hT hBody ihT ihBody =>
      subst hC
      have hT' := ihT (heads := heads) rfl
      have hBody' :=
        ihBody (heads := { bound := t, kind := .sub } :: heads)
          (by simp [List.cons_append])
      have hCtx_succ :
          Ctx.instantiateBetaPrefix arg' (heads.length + 1)
              ({ bound := t, kind := .sub } :: heads) =
            { bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg') t,
                kind := .sub } ::
              Ctx.instantiateBetaPrefix arg' heads.length heads := by
        simp [Ctx.instantiateBetaPrefix]
      have hshift_succ' :
          Term.shiftBy 0 (heads.length + 1) arg' =
            Term.shift 0 (Term.shiftBy 0 heads.length arg') := by
        have h := Term.shiftBy_compose 0 heads.length 1 arg'
        simpa [Term.shift] using h.symm
      have hBodyReady :
          MEqRed
            ({ bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg') t,
                kind := .sub } ::
              (Ctx.instantiateBetaPrefix arg' heads.length heads ++ Γ))
            []
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg') body)
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg') body') := by
        simp only [List.length_cons] at hBody'
        rw [hCtx_succ] at hBody'
        simpa using hBody'
      have hFun := MEqRed.fun_ hT' hBodyReady
      simpa [Term.instantiate, hshift_succ'] using hFun
  | @fOp Γ' s' t t' α body body' hT hα hBody ihT ihBody =>
      subst hC
      have hT' := ihT (heads := heads) rfl
      have hBody' :=
        ihBody (heads := { bound := α, kind := .equ } :: heads)
          (by simp [List.cons_append])
      have hshift_succ' :
          Term.shiftBy 0 (heads.length + 1) arg' =
            Term.shift 0 (Term.shiftBy 0 heads.length arg') := by
        have h := Term.shiftBy_compose 0 heads.length 1 arg'
        simpa [Term.shift] using h.symm
      have hStack_succ' :
          Stack.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg') (Stack.shift 0 s') =
            Stack.shift 0 (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg') s') := by
        rw [hshift_succ']
        exact Stack.instantiate_succ_shift_zero heads.length
          (Term.shiftBy 0 heads.length arg') s'
      have hCtx_succ :
          Ctx.instantiateBetaPrefix arg' (heads.length + 1)
              ({ bound := α, kind := .equ } :: heads) =
            { bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg') α,
                kind := .equ } ::
              Ctx.instantiateBetaPrefix arg' heads.length heads := by
        simp [Ctx.instantiateBetaPrefix]
      have hArg'ShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg') := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg'
            (Nat.zero_le Γ.depth) hArg'Scoped
      have hαOriginal : Term.Scoped (Γ.depth + heads.length + 1) α := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := arg, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at hα
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hα
      have hαInstScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg') α) :=
        Term.instantiate_scoped heads.length (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg') α (by omega)
          hArg'ShiftScoped hαOriginal
      have hαInstScoped' :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg' heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg') α) := by
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hαInstScoped
      have hBodyReady :
          MEqRed
            ({ bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg') α,
                kind := .equ } ::
              (Ctx.instantiateBetaPrefix arg' heads.length heads ++ Γ))
            (Stack.shift 0 (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg') s'))
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg') body)
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg') body') := by
        simp only [List.length_cons] at hBody'
        rw [hCtx_succ] at hBody'
        rw [hStack_succ'] at hBody'
        simpa using hBody'
      have hFOp := MEqRed.fOp hT' hαInstScoped' hBodyReady
      simpa [Term.instantiate, Stack.instantiate, hshift_succ'] using hFOp

/-- Closed fused kind-narrowing β-substitution respect for de Bruijn
`MEqRed`, proved unconditionally via the universal `∀n` theorem. The
discharged `.sub` head's bound `arg` and the substitution argument
`arg'` are decoupled — both must be scoped at `Γ.depth`. -/
noncomputable def MEqRedFusedKindNarrowedBetaSubstStack_proved :
    MEqRedFusedKindNarrowedBetaSubstStack :=
  MEqRedFusedKindNarrowedBetaSubstStack.of_generic
    (MEqRedFusedKindNarrowedBetaSubstUnderHeadsStack_universal 0)

/-! ## de Bruijn Lemma 2 `Me-Bet × Me-Bet` cell — chain output

The `bet × bet` source cell of de Bruijn Lemma 2 closes via two pieces of
machinery composed along an `MEqRedStar` chain: the proved fused
kind-narrowing β-substitution (which provides the body-progress single
step at the discharged `.sub` head) and an argument-transport hypothesis
(which provides the argument-progress chain when the body is then evaluated
at the joined `v₃`). The argument-transport hypothesis is conditional —
this file's job is to discharge the cell **assuming** the transport
machinery; the discharge of the transport itself is handled in a separate
work product. -/

/-- Stack-level instantiate-shift cancellation: instantiating below a fresh
top-level binder cancels the surrounding stack shift. Specializes
`Stack.instantiate_shiftBy_zero_tail` with `n = 0`. -/
private theorem Stack.instantiate_zero_shift_zero_id (v : Term) (s : Stack) :
    Stack.instantiate 0 v (Stack.shift 0 s) = s := by
  induction s with
  | nil => rfl
  | cons α s ih =>
      show Term.instantiate 0 v (Term.shift 0 α) ::
          Stack.instantiate 0 v (Stack.shift 0 s) = α :: s
      rw [Term.instantiate_shift_id 0 v α, ih]

/-- Argument-position transport hypothesis: a body whose `bvar 0` references
all become `arg` after instantiation, paired with a step `arg → arg'`,
produces a chain to the form where they all become `arg'`. The MEqRed-side
analog of the LN paper's argument-position substitution lemma. Conditional
on this hypothesis being discharged separately.

This payload is `Prop`-valued because `MEqRedStar` is `Prop`-valued
(`Relation.ReflTransGen` of the `MEqRedJ` proposition wrapper). -/
def MEqRedArgTransportPayload : Prop :=
  ∀ {Γ : Ctx} {arg arg' body : Term} {s : Stack},
    Term.Scoped (Γ.depth + 1) body →
    MEqRed Γ [] arg arg' →
    PrevalidExt Γ s →
    MEqRedStar Γ s
      (Term.instantiate 0 arg body)
      (Term.instantiate 0 arg' body)

namespace EqDiamonds

/-- The `Me-Bet × Me-Bet` source cell of de Bruijn Lemma 2 with chain output.
Closes the diamond at `Term.instantiate 0 v₃ body₃` via:
- body diamond → `body₃`, joining `body₁'`/`body₂'` at the extended `.sub`
  head context;
- arg diamond → `v₃`, joining `v₁'`/`v₂'` at the empty stack;
- the proved fused kind-narrowing β-substitution helper for the body
  progress single step;
- the argument-transport hypothesis for the arg progress chain.

The body- and arg-diamond hypotheses are stated using `MEqRedJ` (the `Prop`
wrapper around `MEqRed`) to match the existing `EqDiamonds` shape. The
underlying `Type`-valued `MEqRed` derivations are extracted with `.some`
where needed.

Conditional on `MEqRedArgTransportPayload`. -/
theorem bet_bet_chain_of
    (hArgTransport : MEqRedArgTransportPayload)
    {Γ : Ctx} {s : Stack} {t v body body₁' body₂' v₁' v₂' : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hBody₁ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₁')
    (hArg₁ : MEqRed Γ [] v v₁')
    (hBody₂ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂')
    (hArg₂ : MEqRed Γ [] v v₂') :
    ∃ t₃,
      MEqRedStar Γ s (Term.instantiate 0 v₁' body₁') t₃
      ∧ MEqRedStar Γ s (Term.instantiate 0 v₂' body₂') t₃ := by
  -- Body diamond closure: body₁' / body₂' join at body₃ under `{t,.sub}` head.
  obtain ⟨body₃, hBody₁₃J, hBody₂₃J⟩ := hBodyDiamond hBody₁ hBody₂
  -- Arg diamond closure: v₁' / v₂' join at v₃ at the empty stack.
  obtain ⟨v₃, hArg₁₃J, hArg₂₃J⟩ := hArgDiamond hArg₁ hArg₂
  -- Extract Type-valued MEqRed derivations from the Nonempty wrappers.
  let hBody₁₃ : MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
    body₁' body₃ := hBody₁₃J.some
  let hBody₂₃ : MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
    body₂' body₃ := hBody₂₃J.some
  let hArg₁₃ : MEqRed Γ [] v₁' v₃ := hArg₁₃J.some
  let hArg₂₃ : MEqRed Γ [] v₂' v₃ := hArg₂₃J.some
  -- Common reduct.
  refine ⟨Term.instantiate 0 v₃ body₃, ?_, ?_⟩
  · -- LHS chain: instantiate 0 v₁' body₁' →* instantiate 0 v₃ body₃.
    have hv₁'Scoped : Term.Scoped Γ.depth v₁' := hArg₁.scoped_right
    -- Body progress (single step) via fused kind-narrowing β-substitution.
    have hBodyProgress :
        MEqRed Γ (Stack.instantiate 0 v₁' (Stack.shift 0 s))
          (Term.instantiate 0 v₁' body₁')
          (Term.instantiate 0 v₁' body₃) :=
      MEqRedFusedKindNarrowedBetaSubstStack_proved
        (arg := t) (arg' := v₁') ht hv₁'Scoped hBody₁₃
    have hStackEq :
        Stack.instantiate 0 v₁' (Stack.shift 0 s) = s :=
      Stack.instantiate_zero_shift_zero_id v₁' s
    have hBodyProgress' :
        MEqRed Γ s
          (Term.instantiate 0 v₁' body₁')
          (Term.instantiate 0 v₁' body₃) := by
      simpa [hStackEq] using hBodyProgress
    -- Arg progress (chain) via the argument-transport hypothesis.
    have hBody₃Scoped : Term.Scoped (Γ.depth + 1) body₃ := by
      simpa [Ctx.depth] using hBody₁₃.scoped_right
    have hpvΓs : PrevalidExt Γ s :=
      PrevalidExt.weaken_head_inv hBody₁.prevalidExt
    have hArgChain :
        MEqRedStar Γ s
          (Term.instantiate 0 v₁' body₃)
          (Term.instantiate 0 v₃ body₃) :=
      hArgTransport hBody₃Scoped hArg₁₃ hpvΓs
    exact (MEqRedStar.single hBodyProgress').trans hArgChain
  · -- RHS chain: instantiate 0 v₂' body₂' →* instantiate 0 v₃ body₃.
    have hv₂'Scoped : Term.Scoped Γ.depth v₂' := hArg₂.scoped_right
    have hBodyProgress :
        MEqRed Γ (Stack.instantiate 0 v₂' (Stack.shift 0 s))
          (Term.instantiate 0 v₂' body₂')
          (Term.instantiate 0 v₂' body₃) :=
      MEqRedFusedKindNarrowedBetaSubstStack_proved
        (arg := t) (arg' := v₂') ht hv₂'Scoped hBody₂₃
    have hStackEq :
        Stack.instantiate 0 v₂' (Stack.shift 0 s) = s :=
      Stack.instantiate_zero_shift_zero_id v₂' s
    have hBodyProgress' :
        MEqRed Γ s
          (Term.instantiate 0 v₂' body₂')
          (Term.instantiate 0 v₂' body₃) := by
      simpa [hStackEq] using hBodyProgress
    have hBody₃Scoped : Term.Scoped (Γ.depth + 1) body₃ := by
      simpa [Ctx.depth] using hBody₂₃.scoped_right
    have hpvΓs : PrevalidExt Γ s :=
      PrevalidExt.weaken_head_inv hBody₂.prevalidExt
    have hArgChain :
        MEqRedStar Γ s
          (Term.instantiate 0 v₂' body₃)
          (Term.instantiate 0 v₃ body₃) :=
      hArgTransport hBody₃Scoped hArg₂₃ hpvΓs
    exact (MEqRedStar.single hBodyProgress').trans hArgChain

/-! ### Cross-β `bet × app` and `app × bet` chain cells

These cells handle the asymmetric case where one side `bet`-fires and the
other `app`-fires (the operator step is then forced through `Me-FOp` by
the non-empty stack). The closure strategy mirrors `bet_bet_chain_of`,
with two extra ingredients to bridge the kind mismatch:

- The `app`-side operator step inverts to `Me-FOp`, producing a body
  derivation in `.equ`-head context with bound `v` (the operand).
- The `bet`-side body derivation is in `.sub`-head context with bound `t`
  (the abstraction's bound).

Without an `equ → sub` head-replacement direction (which would be
unsound: `Me-Pro` lookups on `.equ` heads cannot be transported to
`.sub` heads), we cannot directly diamond the two body derivations at a
common context. The cell instead accepts a **`.sub`-head bridging
hypothesis** for the `app`-side body — a derivation in the natural
`.sub`-head context, with bound `t`, that targets the same `body₂'` that
the `Me-FOp` inversion produces. This bridging hypothesis is the
conditional residual.

The chain output is `Term.instantiate 0 v₃ body₃` for body₃ joined at
the `.sub`-head and v₃ joined at the empty stack. The RHS
`.app (.abs t' body₂') v''` is β-fired in a single step (using a
reflexive body derivation in `.sub`-head with bound `t'`), then
transported to the joined form via `MEqRedFusedKindNarrowedBetaSubstStack_proved`
and the argument-transport hypothesis. -/

/-- The `Me-Bet × Me-App` source cell of de Bruijn Lemma 2 with chain
output. The LHS `bet`-fires; the RHS `app`-fires, with the operator step
inverting to `Me-FOp` (the only constructor that produces a non-`.app`
source at non-empty stack from a `.abs` head).

Conditional on:
- `MEqRedArgTransportPayload` (the argument-position transport lemma)
- A body diamond at the `.sub`-head context with bound `t`
- An argument diamond at the empty stack
- A `.sub`-head bridging hypothesis `hBody₂Sub` that re-derives
  the `Me-FOp` inversion's body₂' in a `.sub`-head context with bound
  `t`. This converts the `.equ`-head body₂' (with bound `v`) to the
  `.sub`-head form needed for the body diamond and the
  `MEqRedFusedKindNarrowedBetaSubstStack_proved` bridge. -/
theorem bet_app_chain_of
    (hArgTransport : MEqRedArgTransportPayload)
    {Γ : Ctx} {s : Stack} {t v body body₁' v₁' v₂' hOp₂_target : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hBody₁ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₁')
    (hArg₁ : MEqRed Γ [] v v₁')
    (hOp₂ : MEqRed Γ (v :: s) (.abs t body) hOp₂_target)
    (hArg₂ : MEqRed Γ [] v v₂')
    (hBody₂Sub :
      ∀ {body₂' t' : Term},
        hOp₂_target = .abs t' body₂' →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂') :
    ∃ t₃,
      MEqRedStar Γ s (Term.instantiate 0 v₁' body₁') t₃
      ∧ MEqRedStar Γ s (.app hOp₂_target v₂') t₃ := by
  -- Invert the operator step. `MEqRed Γ (v :: s) (.abs t body) hOp₂_target`
  -- has only one applicable constructor: `Me-FOp`.
  cases hOp₂ with
  | fOp hT₂ hα₂ hBody₂equ =>
    -- After inversion: hOp₂_target = .abs t' body₂'.
    rename_i t' body₂'
    -- Pull the .sub-head bridging body derivation for body₂'.
    have hBody₂sub :
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂' :=
      hBody₂Sub rfl
    -- Body diamond joins body₁' / body₂' at the `.sub`-head context.
    obtain ⟨body₃, hBody₁₃J, hBody₂₃J⟩ := hBodyDiamond hBody₁ hBody₂sub
    -- Arg diamond joins v₁' / v₂' at the empty stack.
    obtain ⟨v₃, hArg₁₃J, hArg₂₃J⟩ := hArgDiamond hArg₁ hArg₂
    let hBody₁₃ :
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
          body₁' body₃ := hBody₁₃J.some
    let hBody₂₃ :
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
          body₂' body₃ := hBody₂₃J.some
    let hArg₁₃ : MEqRed Γ [] v₁' v₃ := hArg₁₃J.some
    let hArg₂₃ : MEqRed Γ [] v₂' v₃ := hArg₂₃J.some
    refine ⟨Term.instantiate 0 v₃ body₃, ?_, ?_⟩
    · -- LHS chain: instantiate 0 v₁' body₁' →* instantiate 0 v₃ body₃.
      have hv₁'Scoped : Term.Scoped Γ.depth v₁' := hArg₁.scoped_right
      have hBodyProgress :
          MEqRed Γ (Stack.instantiate 0 v₁' (Stack.shift 0 s))
            (Term.instantiate 0 v₁' body₁')
            (Term.instantiate 0 v₁' body₃) :=
        MEqRedFusedKindNarrowedBetaSubstStack_proved
          (arg := t) (arg' := v₁') ht hv₁'Scoped hBody₁₃
      have hStackEq :
          Stack.instantiate 0 v₁' (Stack.shift 0 s) = s :=
        Stack.instantiate_zero_shift_zero_id v₁' s
      have hBodyProgress' :
          MEqRed Γ s
            (Term.instantiate 0 v₁' body₁')
            (Term.instantiate 0 v₁' body₃) := by
        simpa [hStackEq] using hBodyProgress
      have hBody₃Scoped : Term.Scoped (Γ.depth + 1) body₃ := by
        simpa [Ctx.depth] using hBody₁₃.scoped_right
      have hpvΓs : PrevalidExt Γ s :=
        PrevalidExt.weaken_head_inv hBody₁.prevalidExt
      have hArgChain :
          MEqRedStar Γ s
            (Term.instantiate 0 v₁' body₃)
            (Term.instantiate 0 v₃ body₃) :=
        hArgTransport hBody₃Scoped hArg₁₃ hpvΓs
      exact (MEqRedStar.single hBodyProgress').trans hArgChain
    · -- RHS chain: .app (.abs t' body₂') v₂' →* instantiate 0 v₃ body₃.
      -- Step 1: β-fire RHS via Me-Bet, using a reflexive .sub-head body
      -- derivation at bound t' and a reflexive arg derivation at v₂'.
      have hpvΓs : PrevalidExt Γ s :=
        PrevalidExt.weaken_head_inv hBody₁.prevalidExt
      have ht' : Term.Scoped Γ.depth t' := hT₂.scoped_right
      have hPrevalidT' :
          Prevalid ({bound := t', kind := .sub} :: Γ) :=
        Prevalid.sub (PrevalidExt.ctx hpvΓs) ht'
      have hpvBody₂t' :
          PrevalidExt ({bound := t', kind := .sub} :: Γ) (Stack.shift 0 s) :=
        PrevalidExt.weaken_head hpvΓs hPrevalidT'
      have hBody₂'Scoped : Term.Scoped (Γ.depth + 1) body₂' := by
        simpa [Ctx.depth] using hBody₂equ.scoped_right
      have hBody₂'Scoped_t' :
          Term.Scoped
            (Ctx.depth ({bound := t', kind := .sub} :: Γ)) body₂' := by
        simpa [Ctx.depth, Nat.succ_eq_add_one] using hBody₂'Scoped
      have hBodyReflT' :
          MEqRed ({bound := t', kind := .sub} :: Γ) (Stack.shift 0 s)
            body₂' body₂' :=
        MEqRed.refl hpvBody₂t' hBody₂'Scoped_t'
      have hv₂'Scoped : Term.Scoped Γ.depth v₂' := hArg₂.scoped_right
      have hpvNil : PrevalidExt Γ [] :=
        PrevalidExt.nil (PrevalidExt.ctx hpvΓs)
      have hArgReflv₂' : MEqRed Γ [] v₂' v₂' :=
        MEqRed.refl hpvNil hv₂'Scoped
      have hβStep :
          MEqRed Γ s (.app (.abs t' body₂') v₂')
            (Term.instantiate 0 v₂' body₂') :=
        MEqRed.bet ht' hBodyReflT' hArgReflv₂'
      -- Step 2: body progress (single step) via FusedKindNarrowed at
      -- .sub-head bound t (matching the body diamond's context).
      have hBodyProgress :
          MEqRed Γ (Stack.instantiate 0 v₂' (Stack.shift 0 s))
            (Term.instantiate 0 v₂' body₂')
            (Term.instantiate 0 v₂' body₃) :=
        MEqRedFusedKindNarrowedBetaSubstStack_proved
          (arg := t) (arg' := v₂') ht hv₂'Scoped hBody₂₃
      have hStackEq :
          Stack.instantiate 0 v₂' (Stack.shift 0 s) = s :=
        Stack.instantiate_zero_shift_zero_id v₂' s
      have hBodyProgress' :
          MEqRed Γ s
            (Term.instantiate 0 v₂' body₂')
            (Term.instantiate 0 v₂' body₃) := by
        simpa [hStackEq] using hBodyProgress
      -- Step 3: arg-transport chain to the joined v₃.
      have hBody₃Scoped : Term.Scoped (Γ.depth + 1) body₃ := by
        simpa [Ctx.depth] using hBody₂₃.scoped_right
      have hArgChain :
          MEqRedStar Γ s
            (Term.instantiate 0 v₂' body₃)
            (Term.instantiate 0 v₃ body₃) :=
        hArgTransport hBody₃Scoped hArg₂₃ hpvΓs
      -- Compose: app step → β step → body progress → arg transport.
      exact ((MEqRedStar.single hβStep).trans
        (MEqRedStar.single hBodyProgress')).trans hArgChain

/-- The `Me-App × Me-Bet` source cell of de Bruijn Lemma 2 with chain
output. Symmetric to `bet_app_chain_of`: LHS `app`-fires (with the
operator step forced through `Me-FOp`), RHS `bet`-fires.

Conditional on the same hypotheses as `bet_app_chain_of`, with the
roles swapped. The output is the same chain target with LHS/RHS chains
swapped. -/
theorem app_bet_chain_of
    (hArgTransport : MEqRedArgTransportPayload)
    {Γ : Ctx} {s : Stack} {t v body body₂' v₁' v₂' hOp₁_target : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hOp₁ : MEqRed Γ (v :: s) (.abs t body) hOp₁_target)
    (hArg₁ : MEqRed Γ [] v v₁')
    (hBody₂ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂')
    (hArg₂ : MEqRed Γ [] v v₂')
    (hBody₁Sub :
      ∀ {body₁' t' : Term},
        hOp₁_target = .abs t' body₁' →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₁') :
    ∃ t₃,
      MEqRedStar Γ s (.app hOp₁_target v₁') t₃
      ∧ MEqRedStar Γ s (Term.instantiate 0 v₂' body₂') t₃ := by
  obtain ⟨t₃, hLeft, hRight⟩ :=
    bet_app_chain_of hArgTransport hBodyDiamond hArgDiamond ht hBody₂ hArg₂
      hOp₁ hArg₁ hBody₁Sub
  exact ⟨t₃, hRight, hLeft⟩

end EqDiamonds

/-- Prevalidity transport for β-instantiation under one preserved context
head. The preserved head's bound is instantiated while the discharged `.sub`
tail is removed. -/
noncomputable def BetaInstantiationPreservesPrevalidExtUnderHead
    {Γ : Ctx} {bound arg head : Term} {kind : CtxEntryKind} {s : Stack}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := head, kind := kind } ::
        { bound := bound, kind := .sub } :: Γ) s) :
    PrevalidExt ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
      (Stack.instantiate 1 (Term.shift 0 arg) s) := by
  have h := BetaInstantiationPreservesPrevalidExtUnderHeads
    (heads := [{ bound := head, kind := kind }]) rfl hArgBound hpv
  simpa [Ctx.instantiateBetaPrefix, Term.shift, Term.shiftBy_compose,
    Term.shiftBy_zero_id, Nat.add_assoc] using h

/-- Reflexive equivalence reduction is stable under de Bruijn
β-instantiation below one preserved context head. -/
noncomputable def BetaInstantiationPreservesMEqRedUnderHeadStack.refl
    {Γ : Ctx} {bound arg head u : Term} {kind : CtxEntryKind} {s : Stack}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := head, kind := kind } ::
        { bound := bound, kind := .sub } :: Γ) s)
    (hu :
      Term.Scoped
        (Ctx.depth ({ bound := head, kind := kind } ::
          { bound := bound, kind := .sub } :: Γ)) u) :
    MEqRed ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
      (Stack.instantiate 1 (Term.shift 0 arg) s)
      (Term.instantiate 1 (Term.shift 0 arg) u)
      (Term.instantiate 1 (Term.shift 0 arg) u) := by
  have hArgShiftScoped : Term.Scoped (Γ.depth + 1) (Term.shift 0 arg) :=
    Term.shift_scoped 0 Γ.depth arg (Nat.zero_le Γ.depth)
      hArgBound.scoped_left
  have hu' :
      Term.Scoped
        (Ctx.depth ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ))
        (Term.instantiate 1 (Term.shift 0 arg) u) := by
    have hInst :
        Term.Scoped (Γ.depth + 1)
          (Term.instantiate 1 (Term.shift 0 arg) u) :=
      Term.instantiate_scoped 1 (Γ.depth + 1) (Term.shift 0 arg) u
        (by omega) hArgShiftScoped (by
          simpa [Ctx.depth, Nat.succ_eq_add_one, Nat.add_assoc] using hu)
    simpa [Ctx.depth, Nat.succ_eq_add_one] using hInst
  exact MEqRed.refl
    (BetaInstantiationPreservesPrevalidExtUnderHead hArgBound hpv) hu'

/-- `MEqRed.top` is stable under de Bruijn β-instantiation below one
preserved context head. -/
noncomputable def BetaInstantiationPreservesMEqRedUnderHeadStack.top
    {Γ : Ctx} {bound arg head : Term} {kind : CtxEntryKind} {s : Stack}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := head, kind := kind } ::
        { bound := bound, kind := .sub } :: Γ) s) :
    MEqRed ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
      (Stack.instantiate 1 (Term.shift 0 arg) s)
      (Term.instantiate 1 (Term.shift 0 arg) .top)
      (Term.instantiate 1 (Term.shift 0 arg) .top) := by
  simpa using
    MEqRed.top (BetaInstantiationPreservesPrevalidExtUnderHead hArgBound hpv)

/-- The preserved innermost variable in an under-head `MEqRed.var` leaf
remains the innermost variable after β-instantiation of the tail head. -/
noncomputable def BetaInstantiationPreservesMEqRedUnderHeadStack.var_zero
    {Γ : Ctx} {bound arg head : Term} {kind : CtxEntryKind} {s : Stack}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := head, kind := kind } ::
        { bound := bound, kind := .sub } :: Γ) s) :
    MEqRed ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
      (Stack.instantiate 1 (Term.shift 0 arg) s)
      (Term.instantiate 1 (Term.shift 0 arg) (.bvar 0))
      (Term.instantiate 1 (Term.shift 0 arg) (.bvar 0)) := by
  have hi : 0 < Ctx.depth
      ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ) := by
    simp [Ctx.depth]
  simpa [Term.instantiate] using
    MEqRed.var (BetaInstantiationPreservesPrevalidExtUnderHead hArgBound hpv) hi

/-- The discharged tail-head variable in an under-head `MEqRed.var` leaf
instantiates to the lifted argument and reduces reflexively. -/
noncomputable def BetaInstantiationPreservesMEqRedUnderHeadStack.var_one
    {Γ : Ctx} {bound arg head : Term} {kind : CtxEntryKind} {s : Stack}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := head, kind := kind } ::
        { bound := bound, kind := .sub } :: Γ) s) :
    MEqRed ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
      (Stack.instantiate 1 (Term.shift 0 arg) s)
      (Term.instantiate 1 (Term.shift 0 arg) (.bvar 1))
      (Term.instantiate 1 (Term.shift 0 arg) (.bvar 1)) := by
  have hArgShiftScoped : Term.Scoped
      (Ctx.depth ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ))
      (Term.shift 0 arg) := by
    simpa [Ctx.depth, Nat.succ_eq_add_one] using
      Term.shift_scoped 0 Γ.depth arg (Nat.zero_le Γ.depth)
        hArgBound.scoped_left
  simpa [Term.instantiate] using
    MEqRed.refl (BetaInstantiationPreservesPrevalidExtUnderHead hArgBound hpv)
      hArgShiftScoped

/-- Variables strictly past the discharged tail head in an under-head
`MEqRed.var` leaf descend by one index. -/
noncomputable def BetaInstantiationPreservesMEqRedUnderHeadStack.var_succ_succ
    {Γ : Ctx} {bound arg head : Term} {kind : CtxEntryKind} {s : Stack}
    {i : Nat}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := head, kind := kind } ::
        { bound := bound, kind := .sub } :: Γ) s)
    (hi :
      i + 2 < Ctx.depth ({ bound := head, kind := kind } ::
        { bound := bound, kind := .sub } :: Γ)) :
    MEqRed ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
      (Stack.instantiate 1 (Term.shift 0 arg) s)
      (Term.instantiate 1 (Term.shift 0 arg) (.bvar (i + 2)))
      (Term.instantiate 1 (Term.shift 0 arg) (.bvar (i + 2))) := by
  have hiTarget :
      i + 1 < Ctx.depth
        ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ) := by
    simpa [Ctx.depth, Nat.succ_eq_add_one, Nat.add_assoc] using hi
  simpa [Term.instantiate] using
    MEqRed.var (BetaInstantiationPreservesPrevalidExtUnderHead hArgBound hpv)
      hiTarget

/-- Combined under-head `MEqRed.var` substitution helper. The preserved head
stays at index zero, the discharged tail head becomes the lifted argument,
and deeper variables descend by one index. -/
noncomputable def BetaInstantiationPreservesMEqRedUnderHeadStack.var
    {Γ : Ctx} {bound arg head : Term} {kind : CtxEntryKind} {s : Stack}
    {i : Nat}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := head, kind := kind } ::
        { bound := bound, kind := .sub } :: Γ) s)
    (hi :
      i < Ctx.depth ({ bound := head, kind := kind } ::
        { bound := bound, kind := .sub } :: Γ)) :
    MEqRed ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
      (Stack.instantiate 1 (Term.shift 0 arg) s)
      (Term.instantiate 1 (Term.shift 0 arg) (.bvar i))
      (Term.instantiate 1 (Term.shift 0 arg) (.bvar i)) := by
  cases i with
  | zero =>
      exact BetaInstantiationPreservesMEqRedUnderHeadStack.var_zero
        hArgBound hpv
  | succ i =>
      cases i with
      | zero =>
          exact BetaInstantiationPreservesMEqRedUnderHeadStack.var_one
            hArgBound hpv
      | succ i =>
          exact BetaInstantiationPreservesMEqRedUnderHeadStack.var_succ_succ
            hArgBound hpv hi

/-- `MEqRed.tAp` is stable under de Bruijn β-instantiation below one
preserved context head. -/
noncomputable def BetaInstantiationPreservesMEqRedUnderHeadStack.tAp
    {Γ : Ctx} {bound arg head u : Term} {kind : CtxEntryKind} {s : Stack}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := head, kind := kind } ::
        { bound := bound, kind := .sub } :: Γ) s)
    (hu :
      Term.Scoped
        (Ctx.depth ({ bound := head, kind := kind } ::
          { bound := bound, kind := .sub } :: Γ)) u) :
    MEqRed ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
      (Stack.instantiate 1 (Term.shift 0 arg) s)
      (Term.instantiate 1 (Term.shift 0 arg) (.app .top u))
      (Term.instantiate 1 (Term.shift 0 arg) .top) := by
  have hArgShiftScoped : Term.Scoped (Γ.depth + 1) (Term.shift 0 arg) :=
    Term.shift_scoped 0 Γ.depth arg (Nat.zero_le Γ.depth)
      hArgBound.scoped_left
  have hu' :
      Term.Scoped
        (Ctx.depth ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ))
        (Term.instantiate 1 (Term.shift 0 arg) u) := by
    have hInst :
        Term.Scoped (Γ.depth + 1)
          (Term.instantiate 1 (Term.shift 0 arg) u) :=
      Term.instantiate_scoped 1 (Γ.depth + 1) (Term.shift 0 arg) u
        (by omega) hArgShiftScoped (by
          simpa [Ctx.depth, Nat.succ_eq_add_one, Nat.add_assoc] using hu)
    simpa [Ctx.depth, Nat.succ_eq_add_one] using hInst
  simpa [Term.instantiate] using
    MEqRed.tAp
      (BetaInstantiationPreservesPrevalidExtUnderHead hArgBound hpv) hu'

/-- The `MEqRed.app` constructor reassembles an under-head β-instantiated
equivalence step from transformed operator and argument pieces. -/
noncomputable def BetaInstantiationPreservesMEqRedUnderHeadStack.app
    {Γ : Ctx} {arg head u u' v v' : Term} {kind : CtxEntryKind} {s : Stack}
    (hFn :
      MEqRed ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
        (Term.instantiate 1 (Term.shift 0 arg) v ::
          Stack.instantiate 1 (Term.shift 0 arg) s)
        (Term.instantiate 1 (Term.shift 0 arg) u)
        (Term.instantiate 1 (Term.shift 0 arg) u'))
    (hArg :
      MEqRed ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
        [] (Term.instantiate 1 (Term.shift 0 arg) v)
        (Term.instantiate 1 (Term.shift 0 arg) v')) :
    MEqRed ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
      (Stack.instantiate 1 (Term.shift 0 arg) s)
      (Term.instantiate 1 (Term.shift 0 arg) (.app u v))
      (Term.instantiate 1 (Term.shift 0 arg) (.app u' v')) := by
  simpa [Term.instantiate, Stack.instantiate] using MEqRed.app hFn hArg

/-- The `MEqRed.pro` constructor reassembles under-head β-instantiation from
the transformed promoted-bound equivalence step. The index split accounts for
the preserved head at `0`, the discharged `.sub` tail head at `1`, and all
deeper variables descending by one index. -/
noncomputable def BetaInstantiationPreservesMEqRedUnderHeadStack.pro
    {Γ : Ctx} {bound arg head α α' : Term} {kind : CtxEntryKind}
    {s : Stack} {i : Nat}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := head, kind := kind } ::
        { bound := bound, kind := .sub } :: Γ) s)
    (hb :
      Ctx.equBinds ({ bound := head, kind := kind } ::
        { bound := bound, kind := .sub } :: Γ) i α)
    (hα :
      MEqRed ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
        (Stack.instantiate 1 (Term.shift 0 arg) s)
        (Term.instantiate 1 (Term.shift 0 arg) α)
        (Term.instantiate 1 (Term.shift 0 arg) α')) :
    MEqRed ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
      (Stack.instantiate 1 (Term.shift 0 arg) s)
      (Term.instantiate 1 (Term.shift 0 arg) (.bvar i))
      (Term.instantiate 1 (Term.shift 0 arg) α') := by
  have hpvTarget :
      PrevalidExt ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
        (Stack.instantiate 1 (Term.shift 0 arg) s) :=
    BetaInstantiationPreservesPrevalidExtUnderHead hArgBound hpv
  cases i with
  | zero =>
      cases kind with
      | sub =>
          simp [Ctx.equBinds] at hb
      | equ =>
          simp [Ctx.equBinds] at hb
          subst hb
          have hbind :
              Ctx.equBinds
                ({ bound := Term.instantiate 0 arg head, kind := CtxEntryKind.equ } :: Γ)
                0 (Term.shift 0 (Term.instantiate 0 arg head)) := by
            simp [Ctx.equBinds]
          have htargetInst :
              Term.instantiate 1 (Term.shift 0 arg) (Term.shift 0 head) =
                Term.shift 0 (Term.instantiate 0 arg head) := by
            exact (Term.shiftBy_instantiate 0 1 0 arg head (Nat.le_refl 0)).symm
          have hαFor :
              MEqRed
                ({ bound := Term.instantiate 0 arg head, kind := CtxEntryKind.equ } :: Γ)
                (Stack.instantiate 1 (Term.shift 0 arg) s)
                (Term.shift 0 (Term.instantiate 0 arg head))
                (Term.instantiate 1 (Term.shift 0 arg) α') := by
            simpa [htargetInst] using hα
          simpa [Term.instantiate, htargetInst] using
            MEqRed.pro hpvTarget hbind hαFor
  | succ i =>
      cases i with
      | zero =>
          cases kind <;> simp [Ctx.equBinds] at hb
      | succ j =>
          cases kind with
          | sub =>
              simp [Ctx.equBinds] at hb
              let tailTarget := Classical.choose hb
              have htailAnd := Classical.choose_spec hb
              have htailLookup : Ctx.lookupEqu Γ j = some tailTarget :=
                htailAnd.1
              have htarget :
                  Term.shift 0 (Term.shift 0 tailTarget) = α :=
                htailAnd.2
              have htail : Ctx.equBinds Γ j tailTarget := by
                simpa [Ctx.equBinds] using htailLookup
              have hbind :
                  Ctx.equBinds
                    ({ bound := Term.instantiate 0 arg head, kind := CtxEntryKind.sub } :: Γ)
                    (j + 1) (Term.shift 0 tailTarget) := by
                exact Ctx.equBinds_weaken_head
                  ({ bound := Term.instantiate 0 arg head, kind := CtxEntryKind.sub } : CtxEntry)
                  htail
              have htargetInst :
                  Term.instantiate 1 (Term.shift 0 arg)
                    (Term.shift 0 (Term.shift 0 tailTarget)) =
                    Term.shift 0 tailTarget := by
                simpa [Term.shift_shift_zero] using
                  Term.instantiate_shift_id 1 (Term.shift 0 arg)
                    (Term.shift 0 tailTarget)
              have hαFor :
                  MEqRed
                    ({ bound := Term.instantiate 0 arg head, kind := CtxEntryKind.sub } :: Γ)
                    (Stack.instantiate 1 (Term.shift 0 arg) s)
                    (Term.shift 0 tailTarget)
                    (Term.instantiate 1 (Term.shift 0 arg) α') := by
                simpa [← htarget, htargetInst] using hα
              simpa [Term.instantiate, htargetInst] using
                MEqRed.pro hpvTarget hbind hαFor
          | equ =>
              simp [Ctx.equBinds] at hb
              let tailTarget := Classical.choose hb
              have htailAnd := Classical.choose_spec hb
              have htailLookup : Ctx.lookupEqu Γ j = some tailTarget :=
                htailAnd.1
              have htarget :
                  Term.shift 0 (Term.shift 0 tailTarget) = α :=
                htailAnd.2
              have htail : Ctx.equBinds Γ j tailTarget := by
                simpa [Ctx.equBinds] using htailLookup
              have hbind :
                  Ctx.equBinds
                    ({ bound := Term.instantiate 0 arg head, kind := CtxEntryKind.equ } :: Γ)
                    (j + 1) (Term.shift 0 tailTarget) := by
                exact Ctx.equBinds_weaken_head
                  ({ bound := Term.instantiate 0 arg head, kind := CtxEntryKind.equ } : CtxEntry)
                  htail
              have htargetInst :
                  Term.instantiate 1 (Term.shift 0 arg)
                    (Term.shift 0 (Term.shift 0 tailTarget)) =
                    Term.shift 0 tailTarget := by
                simpa [Term.shift_shift_zero] using
                  Term.instantiate_shift_id 1 (Term.shift 0 arg)
                    (Term.shift 0 tailTarget)
              have hαFor :
                  MEqRed
                    ({ bound := Term.instantiate 0 arg head, kind := CtxEntryKind.equ } :: Γ)
                    (Stack.instantiate 1 (Term.shift 0 arg) s)
                    (Term.shift 0 tailTarget)
                    (Term.instantiate 1 (Term.shift 0 arg) α') := by
                simpa [← htarget, htargetInst] using hα
              simpa [Term.instantiate, htargetInst] using
                MEqRed.pro hpvTarget hbind hαFor

/-- Assemble under-head equivalence β-instantiation from constructor-local
frontiers. Structural cases are discharged here; the remaining explicit
inputs are precisely the recursive binder constructors. -/
noncomputable def BetaInstantiationPreservesMEqRedUnderHeadStack.of_constructors
    (hFun : BetaInstantiationPreservesMEqRedUnderHeadFunStackPayload)
    (hBet : BetaInstantiationPreservesMEqRedUnderHeadBetStackPayload)
    (hFOp : BetaInstantiationPreservesMEqRedUnderHeadFOpStackPayload) :
    BetaInstantiationPreservesMEqRedUnderHeadStack := by
  intro Γ bound arg head lhs rhs kind s hArgBound hred
  generalize hC : ({ bound := head, kind := kind } ::
      { bound := bound, kind := .sub } :: Γ) = C at hred
  induction hred generalizing Γ bound arg head kind with
  | pro hpv hb hα ih =>
      subst hC
      exact BetaInstantiationPreservesMEqRedUnderHeadStack.pro
        hArgBound hpv hb (ih hArgBound rfl)
  | bet ht hbody harg =>
      subst hC
      exact hBet hArgBound ht hbody harg
  | top hpv =>
      subst hC
      exact BetaInstantiationPreservesMEqRedUnderHeadStack.top hArgBound hpv
  | app hOp hArg ihOp ihArg =>
      subst hC
      exact BetaInstantiationPreservesMEqRedUnderHeadStack.app
        (ihOp hArgBound rfl) (ihArg hArgBound rfl)
  | var hpv hi =>
      subst hC
      exact BetaInstantiationPreservesMEqRedUnderHeadStack.var hArgBound hpv hi
  | fun_ hBound hBody =>
      subst hC
      exact hFun hArgBound hBound hBody
  | tAp hpv hu =>
      subst hC
      exact BetaInstantiationPreservesMEqRedUnderHeadStack.tAp
        hArgBound hpv hu
  | fOp hBound hα hBody =>
      subst hC
      exact hFOp hArgBound hBound hα hBody

/-- Reflexive equivalence reduction is stable under de Bruijn
β-instantiation at any stack. -/
noncomputable def BetaInstantiationPreservesMEqRedStack.refl
    {Γ : Ctx} {bound arg u : Term} {s : Stack}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) s)
    (hu : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) u) :
    MEqRed Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg u) (Term.instantiate 0 arg u) := by
  have hu' : Term.Scoped Γ.depth (Term.instantiate 0 arg u) :=
    Term.instantiate_scoped 0 Γ.depth arg u (Nat.zero_le Γ.depth)
      hArgBound.scoped_left (by
        simpa [Ctx.depth, Nat.succ_eq_add_one] using hu)
  exact MEqRed.refl (BetaInstantiationPreservesPrevalidExtStack hArgBound hpv) hu'

/-- Reflexive subtype reduction is stable under de Bruijn β-instantiation at
any stack. -/
noncomputable def BetaInstantiationPreservesMSubRedStack.refl
    {Γ : Ctx} {bound arg u : Term} {s : Stack}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) s)
    (hu : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) u) :
    MSubRed Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg u) (Term.instantiate 0 arg u) :=
  MSubRed.refl (BetaInstantiationPreservesPrevalidExtStack hArgBound hpv)
    (by
      exact Term.instantiate_scoped 0 Γ.depth arg u (Nat.zero_le Γ.depth)
        hArgBound.scoped_left (by
          simpa [Ctx.depth, Nat.succ_eq_add_one] using hu))

/-- Empty-stack reflexive equivalence reduction is stable under de Bruijn
β-instantiation. -/
noncomputable def BetaInstantiationPreservesMEqRed.refl
    {Γ : Ctx} {bound arg u : Term}
    (hArgBound : WSubMStar Γ arg bound)
    (hu : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) u) :
    MEqRed Γ [] (Term.instantiate 0 arg u) (Term.instantiate 0 arg u) := by
  simpa using
    BetaInstantiationPreservesMEqRedStack.refl hArgBound
      (PrevalidExt.nil (Prevalid.sub hArgBound.prevalid hArgBound.scoped_right))
      hu

/-- Empty-stack reflexive subtype reduction is stable under de Bruijn
β-instantiation. -/
noncomputable def BetaInstantiationPreservesMSubRed.refl
    {Γ : Ctx} {bound arg u : Term}
    (hArgBound : WSubMStar Γ arg bound)
    (hu : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) u) :
    MSubRed Γ [] (Term.instantiate 0 arg u) (Term.instantiate 0 arg u) := by
  simpa using
    BetaInstantiationPreservesMSubRedStack.refl hArgBound
      (PrevalidExt.nil (Prevalid.sub hArgBound.prevalid hArgBound.scoped_right))
      hu

/-- Top terms are a closed β-instantiation well-formedness leaf. -/
noncomputable def BetaInstantiationPreservesWfM.top
    {Γ : Ctx} {bound arg : Term}
    (hArgBound : WSubMStar Γ arg bound) :
    WfM Γ (Term.instantiate 0 arg .top) := by
  simpa using WfM.top hArgBound.prevalid

/-- The substituted head variable case of β-instantiation is exactly the
argument well-formedness carried by the subtype premise. -/
noncomputable def BetaInstantiationPreservesWfM.var_zero
    {Γ : Ctx} {bound arg : Term} :
    WSubMStar Γ arg bound →
      WfM Γ (Term.instantiate 0 arg (.bvar 0)) :=
  fun hArgBound => by
    simpa [Term.instantiate] using hArgBound.wf_left

/-- Successor `.sub` variables descend from the extended body context back to
the tail context during β-instantiation. -/
noncomputable def BetaInstantiationPreservesWfM.var_succ_sub
    {Γ : Ctx} {bound arg t : Term} {i : Nat}
    (hArgBound : WSubMStar Γ arg bound)
    (hb : Ctx.subBinds ({ bound := bound, kind := .sub } :: Γ) (i + 1) t) :
    WfM Γ (Term.instantiate 0 arg (.bvar (i + 1))) := by
  have hpv : Prevalid Γ := hArgBound.prevalid
  simp [Ctx.subBinds] at hb
  cases hlook : Ctx.lookupSub Γ i with
  | none =>
      simp [hlook] at hb
  | some tail =>
      have htail : Γ.subBinds i tail := by
        simpa [Ctx.subBinds] using hlook
      simpa [Term.instantiate] using WfM.varSub hpv htail

/-- Successor `.equ` variables descend from the extended body context back to
the tail context during β-instantiation. -/
noncomputable def BetaInstantiationPreservesWfM.var_succ_equ
    {Γ : Ctx} {bound arg α : Term} {i : Nat}
    (hArgBound : WSubMStar Γ arg bound)
    (hb : Ctx.equBinds ({ bound := bound, kind := .sub } :: Γ) (i + 1) α) :
    WfM Γ (Term.instantiate 0 arg (.bvar (i + 1))) := by
  have hpv : Prevalid Γ := hArgBound.prevalid
  simp [Ctx.equBinds] at hb
  cases hlook : Ctx.lookupEqu Γ i with
  | none =>
      simp [hlook] at hb
  | some tail =>
      have htail : Γ.equBinds i tail := by
        simpa [Ctx.equBinds] using hlook
      simpa [Term.instantiate] using WfM.varEqu hpv htail

/-- Combined variable case for the de Bruijn β-instantiation
well-formedness payload. -/
noncomputable def BetaInstantiationPreservesWfM.var
    {Γ : Ctx} {bound arg : Term} {i : Nat}
    (hArgBound : WSubMStar Γ arg bound)
    (hBody : WfM ({ bound := bound, kind := .sub } :: Γ) (.bvar i)) :
    WfM Γ (Term.instantiate 0 arg (.bvar i)) := by
  cases hBody with
  | varSub _ hb =>
      cases i with
      | zero =>
          exact BetaInstantiationPreservesWfM.var_zero hArgBound
      | succ i =>
          exact BetaInstantiationPreservesWfM.var_succ_sub hArgBound hb
  | varEqu _ hb =>
      cases i with
      | zero =>
          simp [Ctx.equBinds] at hb
      | succ i =>
          exact BetaInstantiationPreservesWfM.var_succ_equ hArgBound hb

/-- Abstraction reassembly for the de Bruijn β-instantiation
well-formedness payload. The remaining work is the recursive reconstruction
of the instantiated bound and body under the instantiated bound head. -/
noncomputable def BetaInstantiationPreservesWfM.abs
    {Γ : Ctx} {arg t body : Term}
    (hBound :
      WfM Γ (Term.instantiate 0 arg t))
    (hBody :
      WfM ({ bound := Term.instantiate 0 arg t, kind := .sub } :: Γ)
        (Term.instantiate 1 (Term.shift 0 arg) body)) :
    WfM Γ (Term.instantiate 0 arg (.abs t body)) := by
  simpa [Term.instantiate] using WfM.fun_ hBound hBody

/-- Application reassembly for the de Bruijn β-instantiation
well-formedness payload. The remaining work is preservation of the operator
and argument subtype chains through instantiation. -/
noncomputable def BetaInstantiationPreservesWfM.app
    {Γ : Ctx} {arg u v t : Term}
    (hOp :
      WSubMStar Γ (Term.instantiate 0 arg u)
        (.abs (Term.instantiate 0 arg t) .top))
    (hArg :
      WSubMStar Γ (Term.instantiate 0 arg v)
        (Term.instantiate 0 arg t)) :
    WfM Γ (Term.instantiate 0 arg (.app u v)) := by
  simpa [Term.instantiate] using WfM.app hOp hArg

/-- The application case of de Bruijn β-instantiation well-formedness follows
from substitution preservation for `WSubMStar` chains. -/
noncomputable def BetaInstantiationPreservesWfM.app_of_wsubmstar
    (hSubstStar : BetaInstantiationPreservesWSubMStar)
    {Γ : Ctx} {bound arg u v : Term}
    (hArgBound : WSubMStar Γ arg bound)
    (hBody : WfM ({ bound := bound, kind := .sub } :: Γ) (.app u v)) :
    WfM Γ (Term.instantiate 0 arg (.app u v)) := by
  cases hBody with
  | app hOp hArg =>
      have hOp' := hSubstStar hArgBound hOp
      have hArg' := hSubstStar hArgBound hArg
      exact BetaInstantiationPreservesWfM.app
        (by simpa [Term.instantiate] using hOp')
        hArg'

/-- `WSubMStar.sub` reassembly for de Bruijn β-instantiation. -/
noncomputable def BetaInstantiationPreservesWSubMStar.sub
    {Γ : Ctx} {arg lhs rhs : Term}
    (hInstLhs : WfM Γ (Term.instantiate 0 arg lhs))
    (hInstSub :
      WSubM Γ (Term.instantiate 0 arg lhs) (Term.instantiate 0 arg rhs))
    (hInstRhs : WfM Γ (Term.instantiate 0 arg rhs)) :
    WSubMStar Γ (Term.instantiate 0 arg lhs) (Term.instantiate 0 arg rhs) :=
  WSubMStar.sub hInstLhs hInstSub hInstRhs

/-- `WSubMStar.trs` reassembly for de Bruijn β-instantiation. -/
noncomputable def BetaInstantiationPreservesWSubMStar.trs
    {Γ : Ctx} {arg lhs mid rhs : Term}
    (hLeft :
      WSubMStar Γ (Term.instantiate 0 arg lhs) (Term.instantiate 0 arg mid))
    (hMid : WfM Γ (Term.instantiate 0 arg mid))
    (hRight :
      WSubMStar Γ (Term.instantiate 0 arg mid) (Term.instantiate 0 arg rhs)) :
    WSubMStar Γ (Term.instantiate 0 arg lhs) (Term.instantiate 0 arg rhs) :=
  WSubMStar.trs hLeft hMid hRight

/-- The transitive subtype-chain substitution payload follows from the
well-formedness substitution payload and the one-step subtype substitution
payload. -/
noncomputable def BetaInstantiationPreservesWSubMStar.of_wsubm
    (hWf : BetaInstantiationPreservesWfM)
    (hSub : BetaInstantiationPreservesWSubM) :
    BetaInstantiationPreservesWSubMStar := by
  intro Γ bound arg lhs rhs hArgBound hChain
  exact (WSubMStar.rec
    (motive_1 := fun _ _ _ => PUnit)
    (motive_2 := fun _ _ _ _ => PUnit)
    (motive_3 := fun Δ lhs rhs _ =>
      ∀ {Γ : Ctx} {bound arg : Term},
        Δ = ({ bound := bound, kind := .sub } :: Γ) →
          WSubMStar Γ arg bound →
            WSubMStar Γ (Term.instantiate 0 arg lhs)
              (Term.instantiate 0 arg rhs))
    (fun _ _ => PUnit.unit)
    (fun _ _ => PUnit.unit)
    (fun _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit)
    (fun _ _ => PUnit.unit)
    (fun _ _ _ => PUnit.unit)
    (fun _ _ _ _ _ _ _ => PUnit.unit)
    (fun _ _ _ => PUnit.unit)
    (fun hwfL hsub hwfR _ _ _ => by
      intro Γ bound arg hΔ hArgBound
      subst hΔ
      exact BetaInstantiationPreservesWSubMStar.sub
        (hWf hArgBound hwfL) (hSub hArgBound hsub) (hWf hArgBound hwfR))
    (fun _ hwfMid _ ihLeft _ ihRight => by
      intro Γ bound arg hΔ hArgBound
      subst hΔ
      exact BetaInstantiationPreservesWSubMStar.trs
        (ihLeft rfl hArgBound) (hWf hArgBound hwfMid)
        (ihRight rfl hArgBound))
    hChain) rfl hArgBound

/-- `WSubM.rfl` reassembly for de Bruijn β-instantiation. -/
noncomputable def BetaInstantiationPreservesWSubM.rfl
    {Γ : Ctx} {arg t : Term}
    (hInst : WfM Γ (Term.instantiate 0 arg t)) :
    WSubM Γ (Term.instantiate 0 arg t) (Term.instantiate 0 arg t) :=
  WSubM.rfl hInst

/-- `WSubM.lf1` reassembly for de Bruijn β-instantiation. -/
noncomputable def BetaInstantiationPreservesWSubM.lf1
    {Γ : Ctx} {arg lhs lhs' rhs : Term}
    (hRed :
      MEqRed Γ [] (Term.instantiate 0 arg lhs)
        (Term.instantiate 0 arg lhs'))
    (hTail :
      WSubM Γ (Term.instantiate 0 arg lhs') (Term.instantiate 0 arg rhs)) :
    WSubM Γ (Term.instantiate 0 arg lhs) (Term.instantiate 0 arg rhs) :=
  WSubM.lf1 hRed hTail

/-- `WSubM.lf2` reassembly for de Bruijn β-instantiation. -/
noncomputable def BetaInstantiationPreservesWSubM.lf2
    {Γ : Ctx} {arg lhs lhs' rhs : Term}
    (hLhs : WfM Γ (Term.instantiate 0 arg lhs))
    (hRed :
      MSubRed Γ [] (Term.instantiate 0 arg lhs)
        (Term.instantiate 0 arg lhs'))
    (hLhs' : WfM Γ (Term.instantiate 0 arg lhs'))
    (hTail :
      WSubM Γ (Term.instantiate 0 arg lhs') (Term.instantiate 0 arg rhs)) :
    WSubM Γ (Term.instantiate 0 arg lhs) (Term.instantiate 0 arg rhs) :=
  WSubM.lf2 hLhs hRed hLhs' hTail

/-- `WSubM.rgh` reassembly for de Bruijn β-instantiation. -/
noncomputable def BetaInstantiationPreservesWSubM.rgh
    {Γ : Ctx} {arg lhs rhs rhs' : Term}
    (hTail :
      WSubM Γ (Term.instantiate 0 arg lhs) (Term.instantiate 0 arg rhs'))
    (hRed :
      MEqRed Γ [] (Term.instantiate 0 arg rhs)
        (Term.instantiate 0 arg rhs')) :
    WSubM Γ (Term.instantiate 0 arg lhs) (Term.instantiate 0 arg rhs) :=
  WSubM.rgh hTail hRed

/-- One-step subtype substitution follows from well-formedness substitution
and empty-stack equivalence/subtype reduction substitution. -/
noncomputable def BetaInstantiationPreservesWSubM.of_reductions
    (hWf : BetaInstantiationPreservesWfM)
    (hEq : BetaInstantiationPreservesMEqRed)
    (hSubRed : BetaInstantiationPreservesMSubRed) :
    BetaInstantiationPreservesWSubM := by
  intro Γ bound arg lhs rhs hArgBound hSub
  exact (WSubM.rec
    (motive_1 := fun _ _ _ => PUnit)
    (motive_2 := fun Δ lhs rhs _ =>
      ∀ {Γ : Ctx} {bound arg : Term},
        Δ = ({ bound := bound, kind := .sub } :: Γ) →
          WSubMStar Γ arg bound →
            WSubM Γ (Term.instantiate 0 arg lhs)
              (Term.instantiate 0 arg rhs))
    (motive_3 := fun _ _ _ _ => PUnit)
    (fun _ _ => PUnit.unit)
    (fun _ _ => PUnit.unit)
    (fun _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit)
    (fun hwf _ => by
      intro Γ bound arg hΔ hArgBound
      subst hΔ
      exact BetaInstantiationPreservesWSubM.rfl (hWf hArgBound hwf))
    (fun hred _ ih => by
      intro Γ bound arg hΔ hArgBound
      subst hΔ
      exact BetaInstantiationPreservesWSubM.lf1 (hEq hArgBound hred)
        (ih (by rfl) hArgBound))
    (fun hwfL hred hwfL' _ _ _ ih => by
      intro Γ bound arg hΔ hArgBound
      subst hΔ
      exact BetaInstantiationPreservesWSubM.lf2
        (hWf hArgBound hwfL) (hSubRed hArgBound hred)
        (hWf hArgBound hwfL') (ih (by rfl) hArgBound))
    (fun _ hred ih => by
      intro Γ bound arg hΔ hArgBound
      subst hΔ
      exact BetaInstantiationPreservesWSubM.rgh (ih (by rfl) hArgBound)
        (hEq hArgBound hred))
    (fun _ _ _ _ _ _ => PUnit.unit)
    (fun _ _ _ _ _ _ => PUnit.unit)
    hSub) (by rfl) hArgBound

/-- `MEqRed.top` is stable under de Bruijn β-instantiation. -/
noncomputable def BetaInstantiationPreservesMEqRed.top
    {Γ : Ctx} {bound arg : Term}
    (hArgBound : WSubMStar Γ arg bound) :
    MEqRed Γ [] (Term.instantiate 0 arg .top)
      (Term.instantiate 0 arg .top) := by
  simpa using MEqRed.top (PrevalidExt.nil hArgBound.prevalid)

/-- `MEqRed.top` is stable under de Bruijn β-instantiation at any stack. -/
noncomputable def BetaInstantiationPreservesMEqRedStack.top
    {Γ : Ctx} {bound arg : Term} {s : Stack}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) s) :
    MEqRed Γ (Stack.instantiate 0 arg s) (Term.instantiate 0 arg .top)
      (Term.instantiate 0 arg .top) := by
  simpa using MEqRed.top (BetaInstantiationPreservesPrevalidExtStack hArgBound hpv)

/-- The head variable in an `MEqRed.var` leaf instantiates to the substituted
argument, reducing reflexively in the tail context. -/
noncomputable def BetaInstantiationPreservesMEqRed.var_zero
    {Γ : Ctx} {bound arg : Term}
    (hArgBound : WSubMStar Γ arg bound) :
    MEqRed Γ [] (Term.instantiate 0 arg (.bvar 0))
      (Term.instantiate 0 arg (.bvar 0)) := by
  simpa [Term.instantiate] using
    MEqRed.refl (PrevalidExt.nil hArgBound.prevalid) hArgBound.scoped_left

/-- The head variable in an arbitrary-stack `MEqRed.var` leaf instantiates to
the substituted argument, reducing reflexively in the tail context. -/
noncomputable def BetaInstantiationPreservesMEqRedStack.var_zero
    {Γ : Ctx} {bound arg : Term} {s : Stack}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) s) :
    MEqRed Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg (.bvar 0))
      (Term.instantiate 0 arg (.bvar 0)) := by
  simpa [Term.instantiate] using
    MEqRed.refl (BetaInstantiationPreservesPrevalidExtStack hArgBound hpv)
      hArgBound.scoped_left

/-- Successor variables in an `MEqRed.var` leaf descend to the tail context
during de Bruijn β-instantiation. -/
noncomputable def BetaInstantiationPreservesMEqRed.var_succ
    {Γ : Ctx} {bound arg : Term} {i : Nat}
    (hArgBound : WSubMStar Γ arg bound)
    (hi : i + 1 < Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) :
    MEqRed Γ [] (Term.instantiate 0 arg (.bvar (i + 1)))
      (Term.instantiate 0 arg (.bvar (i + 1))) := by
  have hiTail : i < Γ.depth := by
    exact Nat.succ_lt_succ_iff.mp (by
      simpa [Ctx.depth, Nat.succ_eq_add_one] using hi)
  simpa [Term.instantiate] using
    MEqRed.var (PrevalidExt.nil hArgBound.prevalid) hiTail

/-- Successor variables in an arbitrary-stack `MEqRed.var` leaf descend to
the tail context during de Bruijn β-instantiation. -/
noncomputable def BetaInstantiationPreservesMEqRedStack.var_succ
    {Γ : Ctx} {bound arg : Term} {s : Stack} {i : Nat}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) s)
    (hi : i + 1 < Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) :
    MEqRed Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg (.bvar (i + 1)))
      (Term.instantiate 0 arg (.bvar (i + 1))) := by
  have hiTail : i < Γ.depth := by
    exact Nat.succ_lt_succ_iff.mp (by
      simpa [Ctx.depth, Nat.succ_eq_add_one] using hi)
  simpa [Term.instantiate] using
    MEqRed.var (BetaInstantiationPreservesPrevalidExtStack hArgBound hpv)
      hiTail

/-- Combined arbitrary-stack `MEqRed.var` substitution helper. This is the
constructor-facing form: the head variable is replaced by the substituted
argument, while successor variables descend into the tail context. -/
noncomputable def BetaInstantiationPreservesMEqRedStack.var
    {Γ : Ctx} {bound arg : Term} {s : Stack} {i : Nat}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) s)
    (hi : i < Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) :
    MEqRed Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg (.bvar i))
      (Term.instantiate 0 arg (.bvar i)) := by
  cases i with
  | zero =>
    exact BetaInstantiationPreservesMEqRedStack.var_zero hArgBound hpv
  | succ i =>
    exact BetaInstantiationPreservesMEqRedStack.var_succ hArgBound hpv hi

/-- The stack-parametric variable helper specializes to the existing
empty-stack variable helper shape. -/
noncomputable def BetaInstantiationPreservesMEqRed.var_of_stack
    {Γ : Ctx} {bound arg : Term} {i : Nat}
    (hArgBound : WSubMStar Γ arg bound)
    (hi : i < Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) :
    MEqRed Γ [] (Term.instantiate 0 arg (.bvar i))
      (Term.instantiate 0 arg (.bvar i)) := by
  simpa using
    BetaInstantiationPreservesMEqRedStack.var hArgBound
      (PrevalidExt.nil (Prevalid.sub hArgBound.prevalid hArgBound.scoped_right)) hi

/-- `MSubRed.top` is stable under de Bruijn β-instantiation. -/
noncomputable def BetaInstantiationPreservesMSubRed.top
    {Γ : Ctx} {bound arg u : Term}
    (hArgBound : WSubMStar Γ arg bound)
    (hu : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) u) :
    MSubRed Γ [] (Term.instantiate 0 arg u)
      (Term.instantiate 0 arg .top) := by
  have hu' : Term.Scoped Γ.depth (Term.instantiate 0 arg u) :=
    Term.instantiate_scoped 0 Γ.depth arg u (Nat.zero_le Γ.depth)
      hArgBound.scoped_left (by
        simpa [Ctx.depth, Nat.succ_eq_add_one] using hu)
  simpa using MSubRed.top (PrevalidExt.nil hArgBound.prevalid) hu'

/-- `MSubRed.top` is stable under de Bruijn β-instantiation at any stack. -/
noncomputable def BetaInstantiationPreservesMSubRedStack.top
    {Γ : Ctx} {bound arg u : Term} {s : Stack}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) s)
    (hu : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) u) :
    MSubRed Γ (Stack.instantiate 0 arg s) (Term.instantiate 0 arg u)
      (Term.instantiate 0 arg .top) := by
  have hu' : Term.Scoped Γ.depth (Term.instantiate 0 arg u) :=
    Term.instantiate_scoped 0 Γ.depth arg u (Nat.zero_le Γ.depth)
      hArgBound.scoped_left (by
        simpa [Ctx.depth, Nat.succ_eq_add_one] using hu)
  simpa using MSubRed.top
    (BetaInstantiationPreservesPrevalidExtStack hArgBound hpv) hu'

/-- `MSubRed.top` substitution embedded into the diagrammatic-star layer. -/
noncomputable def BetaInstantiationPreservesMSubRedStack.top_msubstar
    {Γ : Ctx} {bound arg u : Term} {s : Stack}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) s)
    (hu : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) u) :
    MSubStar Γ (Stack.instantiate 0 arg s) (Term.instantiate 0 arg u)
      (Term.instantiate 0 arg .top) :=
  MSubStar.of_MSubRed
    (BetaInstantiationPreservesMSubRedStack.top hArgBound hpv hu)

/-- Successor variables in an arbitrary-stack `MSubRed.pro` leaf descend to
the tail context during de Bruijn β-instantiation. The remaining head-variable
case is the substantive bridge from a `WSubMStar` bound premise to a machine
subtype reduction over the instantiated stack. -/
noncomputable def BetaInstantiationPreservesMSubRedStack.pro_succ
    {Γ : Ctx} {bound arg t : Term} {s : Stack} {i : Nat}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) s)
    (hb : Ctx.subBinds ({ bound := bound, kind := .sub } :: Γ) (i + 1) t) :
    MSubRed Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg (.bvar (i + 1)))
      (Term.instantiate 0 arg t) := by
  simp [Ctx.subBinds] at hb
  cases hlook : Ctx.lookupSub Γ i with
  | none =>
      simp [hlook] at hb
  | some tail =>
      simp [hlook] at hb
      subst hb
      have htail : Γ.subBinds i tail := by
        simpa [Ctx.subBinds] using hlook
      have htarget :
          Γ.subBinds i (Term.instantiate 0 arg (Term.shift 0 tail)) := by
        have hid : Term.instantiate 0 arg (Term.shift 0 tail) = tail :=
          Term.instantiate_shift_id 0 arg tail
        simpa [hid] using htail
      simpa [Term.instantiate] using
        MSubRed.pro (BetaInstantiationPreservesPrevalidExtStack hArgBound hpv)
          htarget

/-- Constructor-facing arbitrary-stack `MSubRed.pro` substitution, split into
the explicit head-variable payload and the proved successor-variable
descent. -/
noncomputable def BetaInstantiationPreservesMSubRedStack.pro
    (hHead : BetaInstantiationPreservesMSubRedProHeadPayload)
    {Γ : Ctx} {bound arg t : Term} {s : Stack} {i : Nat}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) s)
    (hb : Ctx.subBinds ({ bound := bound, kind := .sub } :: Γ) i t) :
    MSubRed Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg (.bvar i)) (Term.instantiate 0 arg t) := by
  cases i with
  | zero =>
      simp [Ctx.subBinds] at hb
      subst hb
      simpa using hHead hArgBound hpv
  | succ i =>
      exact BetaInstantiationPreservesMSubRedStack.pro_succ hArgBound hpv hb

/-- Constructor-facing arbitrary-stack `MSubRed.pro` substitution at the
diagrammatic-star layer. Unlike the raw `MSubRed` helper, this closes the
head variable branch using the star-shaped head payload; the successor branch
embeds the raw machine step into `MSubStar`. -/
noncomputable def BetaInstantiationPreservesMSubRedStack.pro_msubstar
    (hHead : BetaInstantiationPreservesMSubRedProHeadMSubStarPayload)
    {Γ : Ctx} {bound arg t : Term} {s : Stack} {i : Nat}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) s)
    (hb : Ctx.subBinds ({ bound := bound, kind := .sub } :: Γ) i t) :
    MSubStar Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg (.bvar i)) (Term.instantiate 0 arg t) := by
  cases i with
  | zero =>
      simp [Ctx.subBinds] at hb
      subst hb
      exact hHead hArgBound hpv
  | succ i =>
      exact MSubStar.of_MSubRed
        (BetaInstantiationPreservesMSubRedStack.pro_succ hArgBound hpv hb)

/-- `MEqRed.tAp` is stable under de Bruijn β-instantiation at the empty
stack. -/
noncomputable def BetaInstantiationPreservesMEqRed.tAp
    {Γ : Ctx} {bound arg u : Term}
    (hArgBound : WSubMStar Γ arg bound)
    (hu : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) u) :
    MEqRed Γ [] (Term.instantiate 0 arg (.app .top u))
      (Term.instantiate 0 arg .top) := by
  have hu' : Term.Scoped Γ.depth (Term.instantiate 0 arg u) :=
    Term.instantiate_scoped 0 Γ.depth arg u (Nat.zero_le Γ.depth)
      hArgBound.scoped_left (by
        simpa [Ctx.depth, Nat.succ_eq_add_one] using hu)
  simpa [Term.instantiate] using
    MEqRed.tAp (PrevalidExt.nil hArgBound.prevalid) hu'

/-- `MEqRed.tAp` is stable under de Bruijn β-instantiation at any stack. -/
noncomputable def BetaInstantiationPreservesMEqRedStack.tAp
    {Γ : Ctx} {bound arg u : Term} {s : Stack}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) s)
    (hu : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) u) :
    MEqRed Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg (.app .top u)) (Term.instantiate 0 arg .top) := by
  have hu' : Term.Scoped Γ.depth (Term.instantiate 0 arg u) :=
    Term.instantiate_scoped 0 Γ.depth arg u (Nat.zero_le Γ.depth)
      hArgBound.scoped_left (by
        simpa [Ctx.depth, Nat.succ_eq_add_one] using hu)
  simpa [Term.instantiate] using
    MEqRed.tAp (BetaInstantiationPreservesPrevalidExtStack hArgBound hpv) hu'

/-- The `MEqRed.app` constructor reassembles a stack-parametric
β-instantiated equivalence-reduction step from its operator and argument
pieces. -/
noncomputable def BetaInstantiationPreservesMEqRedStack.app
    {Γ : Ctx} {arg u u' v v' : Term} {s : Stack}
    (hFn :
      MEqRed Γ (Term.instantiate 0 arg v :: Stack.instantiate 0 arg s)
        (Term.instantiate 0 arg u) (Term.instantiate 0 arg u'))
    (hArg :
      MEqRed Γ [] (Term.instantiate 0 arg v) (Term.instantiate 0 arg v')) :
    MEqRed Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg (.app u v))
      (Term.instantiate 0 arg (.app u' v')) := by
  simpa [Term.instantiate] using MEqRed.app hFn hArg

/-- `MSubRed.equ` reduces de Bruijn β-instantiation subtype substitution to
the corresponding equivalence-reduction substitution leaf. -/
noncomputable def BetaInstantiationPreservesMSubRed.equ
    {Γ : Ctx} {bound arg u v : Term}
    (hArgBound : WSubMStar Γ arg bound)
    (hEq :
      MEqRed Γ [] (Term.instantiate 0 arg u) (Term.instantiate 0 arg v)) :
    MSubRed Γ [] (Term.instantiate 0 arg u) (Term.instantiate 0 arg v) :=
  MSubRed.equ (PrevalidExt.nil hArgBound.prevalid) hEq

/-- Stack-parametric `MSubRed.equ` reassembly once the transformed
equivalence-reduction step is already available. -/
noncomputable def BetaInstantiationPreservesMSubRedStack.equ
    {Γ : Ctx} {arg u v : Term} {s : Stack}
    (hEq :
      MEqRed Γ (Stack.instantiate 0 arg s)
        (Term.instantiate 0 arg u) (Term.instantiate 0 arg v)) :
    MSubRed Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg u) (Term.instantiate 0 arg v) :=
  MSubRed.equ hEq.prevalidExt hEq

/-- Stack-parametric `MSubRed.equ` substitution embedded into the
diagrammatic-star layer. -/
noncomputable def BetaInstantiationPreservesMSubRedStack.equ_msubstar
    {Γ : Ctx} {arg u v : Term} {s : Stack}
    (hEq :
      MEqRed Γ (Stack.instantiate 0 arg s)
        (Term.instantiate 0 arg u) (Term.instantiate 0 arg v)) :
    MSubStar Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg u) (Term.instantiate 0 arg v) :=
  MSubStar.of_MSubRed (BetaInstantiationPreservesMSubRedStack.equ hEq)

/-- The `MSubRed.equ` case of de Bruijn β-instantiation follows from the
empty-stack equivalence-reduction substitution payload. -/
noncomputable def BetaInstantiationPreservesMSubRed.equ_of_meq
    (hEqPayload : BetaInstantiationPreservesMEqRed)
    {Γ : Ctx} {bound arg u v : Term}
    (hArgBound : WSubMStar Γ arg bound)
    (hEq : MEqRed ({ bound := bound, kind := .sub } :: Γ) [] u v) :
    MSubRed Γ [] (Term.instantiate 0 arg u) (Term.instantiate 0 arg v) :=
  BetaInstantiationPreservesMSubRed.equ hArgBound (hEqPayload hArgBound hEq)

/-- `MSubRed.equ` reduces stack-parametric de Bruijn β-instantiation subtype
substitution to the corresponding stack-parametric equivalence-reduction
substitution leaf. -/
noncomputable def BetaInstantiationPreservesMSubRedStack.equ_of_meq
    (hEqPayload : BetaInstantiationPreservesMEqRedStack)
    {Γ : Ctx} {bound arg u v : Term} {s : Stack}
    (hArgBound : WSubMStar Γ arg bound)
    (hEq : MEqRed ({ bound := bound, kind := .sub } :: Γ) s u v) :
    MSubRed Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg u) (Term.instantiate 0 arg v) :=
  BetaInstantiationPreservesMSubRedStack.equ (hEqPayload hArgBound hEq)

/-- The `MSubRed.app` constructor reassembles a stack-parametric
β-instantiated subtype-reduction step from its operator piece and preserved
argument scopedness. -/
noncomputable def BetaInstantiationPreservesMSubRedStack.app
    {Γ : Ctx} {bound arg u u' v : Term} {s : Stack}
    (hArgBound : WSubMStar Γ arg bound)
    (hOp :
      MSubRed Γ (Term.instantiate 0 arg v :: Stack.instantiate 0 arg s)
        (Term.instantiate 0 arg u) (Term.instantiate 0 arg u'))
    (hv : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) v) :
    MSubRed Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg (.app u v))
      (Term.instantiate 0 arg (.app u' v)) := by
  have hv' : Term.Scoped Γ.depth (Term.instantiate 0 arg v) :=
    Term.instantiate_scoped 0 Γ.depth arg v (Nat.zero_le Γ.depth)
      hArgBound.scoped_left (by
        simpa [Ctx.depth, Nat.succ_eq_add_one] using hv)
  simpa [Term.instantiate] using MSubRed.app hOp hv'

/-- The `MSubRed.app` constructor reassembles a stack-parametric
β-instantiated subtype step at the diagrammatic-star layer. -/
noncomputable def BetaInstantiationPreservesMSubRedStack.app_msubstar
    {Γ : Ctx} {bound arg u u' v : Term} {s : Stack}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) s)
    (hOp :
      MSubStar Γ (Term.instantiate 0 arg v :: Stack.instantiate 0 arg s)
        (Term.instantiate 0 arg u) (Term.instantiate 0 arg u'))
    (hv : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) v) :
    MSubStar Γ (Stack.instantiate 0 arg s)
      (Term.instantiate 0 arg (.app u v))
      (Term.instantiate 0 arg (.app u' v)) := by
  have hpvTail : PrevalidExt Γ (Stack.instantiate 0 arg s) :=
    BetaInstantiationPreservesPrevalidExtStack hArgBound hpv
  have hv' : Term.Scoped Γ.depth (Term.instantiate 0 arg v) :=
    Term.instantiate_scoped 0 Γ.depth arg v (Nat.zero_le Γ.depth)
      hArgBound.scoped_left (by
        simpa [Ctx.depth, Nat.succ_eq_add_one] using hv)
  simpa [Term.instantiate] using
    msubStar_app_fixed_arg hpvTail hv' hOp

/-- The `MSubRed.fOp` constructor reassembles a stack-parametric
β-instantiated subtype step at the diagrammatic-star layer once the
body-level transformed chain under the instantiated `.equ` head is available.
-/
noncomputable def BetaInstantiationPreservesMSubRedStack.fOp_msubstar
    {Γ : Ctx} {bound arg t α body body' : Term} {s : Stack}
    (hArgBound : WSubMStar Γ arg bound)
    (hpv : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) (α :: s))
    (ht : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) t)
    (hBody :
      MSubStar ({ bound := Term.instantiate 0 arg α, kind := .equ } :: Γ)
        (Stack.shift 0 (Stack.instantiate 0 arg s))
        (Term.instantiate 1 (Term.shift 0 arg) body)
        (Term.instantiate 1 (Term.shift 0 arg) body')) :
    MSubStar Γ (Stack.instantiate 0 arg (α :: s))
      (Term.instantiate 0 arg (.abs t body))
      (Term.instantiate 0 arg (.abs t body')) := by
  have hpvTail : PrevalidExt Γ (Stack.instantiate 0 arg s) :=
    BetaInstantiationPreservesPrevalidExtStack hArgBound (PrevalidExt.tail hpv)
  have ht' : Term.Scoped Γ.depth (Term.instantiate 0 arg t) :=
    Term.instantiate_scoped 0 Γ.depth arg t (Nat.zero_le Γ.depth)
      hArgBound.scoped_left (by
        simpa [Ctx.depth, Nat.succ_eq_add_one] using ht)
  have hα :
      Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) α :=
    PrevalidExt.head_scoped hpv
  have hα' : Term.Scoped Γ.depth (Term.instantiate 0 arg α) :=
    Term.instantiate_scoped 0 Γ.depth arg α (Nat.zero_le Γ.depth)
      hArgBound.scoped_left (by
        simpa [Ctx.depth, Nat.succ_eq_add_one] using hα)
  simpa [Term.instantiate, Stack.instantiate] using
    msubStar_abs_fOp_body_fixed_bound hpvTail ht' hα' hBody

/-- The `MSubRed.fun_` constructor reassembles an empty-stack
β-instantiated subtype step at the diagrammatic-star layer once the
transformed bound equivalence and transformed body chain are available. -/
noncomputable def BetaInstantiationPreservesMSubRed.fun_msubstar
    {Γ : Ctx} {bound arg t t' body body' : Term}
    (hArgBound : WSubMStar Γ arg bound)
    (hBound :
      MEqRed Γ [] (Term.instantiate 0 arg t) (Term.instantiate 0 arg t'))
    (hBodyScoped :
      Term.Scoped
        (Ctx.depth ({ bound := t, kind := .sub } ::
          { bound := bound, kind := .sub } :: Γ)) body)
    (hBody :
      MSubStar ({ bound := Term.instantiate 0 arg t', kind := .sub } :: Γ)
        [] (Term.instantiate 1 (Term.shift 0 arg) body)
        (Term.instantiate 1 (Term.shift 0 arg) body')) :
    MSubStar Γ [] (Term.instantiate 0 arg (.abs t body))
      (Term.instantiate 0 arg (.abs t' body')) := by
  have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil hArgBound.prevalid
  have hArgShiftScoped : Term.Scoped (Γ.depth + 1) (Term.shift 0 arg) :=
    Term.shift_scoped 0 Γ.depth arg (Nat.zero_le Γ.depth)
      hArgBound.scoped_left
  have hBodyScoped' :
      Term.Scoped (Ctx.depth
        ({ bound := Term.instantiate 0 arg t, kind := .sub } :: Γ))
        (Term.instantiate 1 (Term.shift 0 arg) body) :=
    Term.instantiate_scoped 1 (Γ.depth + 1) (Term.shift 0 arg) body
      (by omega) hArgShiftScoped (by
        simpa [Ctx.depth, Nat.succ_eq_add_one, Nat.add_assoc] using
          hBodyScoped)
  simpa [Term.instantiate] using
    msubStar_abs_fun_equ_bound_body hpvNil hBound hBodyScoped' hBody

/-- Assemble the stack-parametric star-targeted subtype-substitution payload
from constructor-local payloads. The `pro` head, `fun_` body, and `fOp` body
cases are the non-structural obligations; the other constructors reassemble
directly. -/
noncomputable def BetaInstantiationPreservesMSubRedStackMSubStar.of_constructors
    (hHead : BetaInstantiationPreservesMSubRedProHeadMSubStarPayload)
    (hEq : BetaInstantiationPreservesMEqRedStack)
    (hFunBody : BetaInstantiationPreservesMSubRedFunBodyMSubStarPayload)
    (hFOpBody : BetaInstantiationPreservesMSubRedFOpBodyMSubStarPayload) :
    BetaInstantiationPreservesMSubRedStackMSubStar := by
  intro Γ bound arg lhs rhs s hArgBound hred
  generalize hC : ({ bound := bound, kind := .sub } :: Γ) = C at hred
  induction hred generalizing Γ bound arg with
  | pro hpv hb =>
      subst hC
      exact BetaInstantiationPreservesMSubRedStack.pro_msubstar
        hHead hArgBound hpv hb
  | top hpv hu =>
      subst hC
      exact BetaInstantiationPreservesMSubRedStack.top_msubstar
        hArgBound hpv hu
  | equ hpv heq =>
      subst hC
      exact BetaInstantiationPreservesMSubRedStack.equ_msubstar
        (hEq hArgBound heq)
  | app hOp hv ih =>
      subst hC
      exact BetaInstantiationPreservesMSubRedStack.app_msubstar
        hArgBound (PrevalidExt.tail hOp.prevalidExt)
        (ih hArgBound rfl) hv
  | fun_ ht hBound hBody =>
      subst hC
      exact BetaInstantiationPreservesMSubRed.fun_msubstar
        hArgBound (hEq hArgBound hBound) hBody.scoped_left
        (hFunBody hArgBound (hEq hArgBound hBound) hBody)
  | fOp ht hα hBody =>
      subst hC
      have hpv : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) (_ :: _) :=
        PrevalidExt.cons (PrevalidExt.weaken_head_inv hBody.prevalidExt) hα
      exact BetaInstantiationPreservesMSubRedStack.fOp_msubstar
        hArgBound hpv ht (hFOpBody hArgBound hBody)

/-- Assemble the generic under-head star-targeted subtype-substitution payload
from constructor-local under-head frontiers. This is the recursive body
substitution needed by the outer `Ms-Fun`/`Ms-FOp` adapters. -/
noncomputable def BetaInstantiationPreservesMSubRedUnderHeadMSubStarPayload.of_constructors
    (hPro : BetaInstantiationPreservesMSubRedUnderHeadProMSubStarPayload)
    (hEq : BetaInstantiationPreservesMEqRedUnderHeadStack)
    (hFun : BetaInstantiationPreservesMSubRedUnderHeadFunMSubStarPayload)
    (hFOp : BetaInstantiationPreservesMSubRedUnderHeadFOpMSubStarPayload) :
    BetaInstantiationPreservesMSubRedUnderHeadMSubStarPayload := by
  intro Γ bound arg head body body' kind s hArgBound hred
  generalize hC : ({ bound := head, kind := kind } ::
      { bound := bound, kind := .sub } :: Γ) = C at hred
  induction hred generalizing Γ bound arg head kind with
  | pro hpv hb =>
      subst hC
      exact hPro hArgBound hpv hb
  | @top _ _ u hpv hu =>
      subst hC
      have hArgShiftScoped : Term.Scoped (Γ.depth + 1) (Term.shift 0 arg) :=
        Term.shift_scoped 0 Γ.depth arg (Nat.zero_le Γ.depth)
          hArgBound.scoped_left
      have hu' :
          Term.Scoped
            (Ctx.depth ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ))
            (Term.instantiate 1 (Term.shift 0 arg) u) := by
        have huInst :
            Term.Scoped (Γ.depth + 1)
              (Term.instantiate 1 (Term.shift 0 arg) u) :=
          Term.instantiate_scoped 1 (Γ.depth + 1) (Term.shift 0 arg) u
            (by omega) hArgShiftScoped (by
              simpa [Ctx.depth, Nat.succ_eq_add_one, Nat.add_assoc] using hu)
        simpa [Ctx.depth, Nat.succ_eq_add_one] using huInst
      exact MSubStar.of_MSubRed
        (MSubRed.top
          (BetaInstantiationPreservesPrevalidExtUnderHead hArgBound hpv) hu')
  | equ hpv heq =>
      subst hC
      exact MSubStar.of_MSubRed
        (MSubRed.equ
          (BetaInstantiationPreservesPrevalidExtUnderHead hArgBound hpv)
          (hEq hArgBound heq))
  | @app _ sApp _ _ v hOp hv ih =>
      subst hC
      have hArgShiftScoped : Term.Scoped (Γ.depth + 1) (Term.shift 0 arg) :=
        Term.shift_scoped 0 Γ.depth arg (Nat.zero_le Γ.depth)
          hArgBound.scoped_left
      have hpvTail :
          PrevalidExt ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
            (Stack.instantiate 1 (Term.shift 0 arg) sApp) :=
        BetaInstantiationPreservesPrevalidExtUnderHead hArgBound
          (PrevalidExt.tail (s := sApp) (α := v) hOp.prevalidExt)
      have hv' :
          Term.Scoped
            (Ctx.depth ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ))
            (Term.instantiate 1 (Term.shift 0 arg) v) := by
        have hvInst :
            Term.Scoped (Γ.depth + 1)
              (Term.instantiate 1 (Term.shift 0 arg) v) :=
          Term.instantiate_scoped 1 (Γ.depth + 1) (Term.shift 0 arg) v
            (by omega) hArgShiftScoped (by
              simpa [Ctx.depth, Nat.succ_eq_add_one, Nat.add_assoc] using hv)
        simpa [Ctx.depth, Nat.succ_eq_add_one] using hvInst
      simpa [Term.instantiate, Stack.instantiate] using
        msubStar_app_fixed_arg hpvTail hv' (ih hArgBound rfl)
  | fun_ ht hBound hBody =>
      subst hC
      exact hFun hArgBound ht hBound hBody
  | fOp ht hα hBody =>
      subst hC
      exact hFOp hArgBound ht hα hBody

/-- The generic under-head body substitution payload specializes to the
`MSubRed.fOp` body frontier; the only additional work is rewriting the
instantiated shifted stack to shifted instantiated tail form. -/
noncomputable def BetaInstantiationPreservesMSubRedFOpBodyMSubStarPayload.of_under_head
    (hUnder : BetaInstantiationPreservesMSubRedUnderHeadMSubStarPayload) :
    BetaInstantiationPreservesMSubRedFOpBodyMSubStarPayload := by
  intro Γ bound arg α body body' s hArgBound hBody
  have h := hUnder (Γ := Γ) (bound := bound) (arg := arg)
    (head := α) (kind := CtxEntryKind.equ) (s := Stack.shift 0 s)
    hArgBound hBody
  simpa [Stack.instantiate_one_shift_zero] using h

/-- The generic under-head body substitution payload plus the changed-bound
transport payload specializes to the `MSubRed.fun_` body frontier. -/
noncomputable def BetaInstantiationPreservesMSubRedFunBodyMSubStarPayload.of_under_head
    (hUnder : BetaInstantiationPreservesMSubRedUnderHeadMSubStarPayload)
    (hChange : BetaInstantiationPreservesMSubRedFunBodyHeadChangeMSubStarPayload) :
    BetaInstantiationPreservesMSubRedFunBodyMSubStarPayload := by
  intro Γ bound arg t t' body body' hArgBound hBound hBody
  have hBodyUnder := hUnder (Γ := Γ) (bound := bound) (arg := arg)
    (head := t) (kind := CtxEntryKind.sub) (s := []) hArgBound hBody
  exact hChange hArgBound hBound hBodyUnder

/-- Constructor assembler specialized to the generic under-head body payload.
The only remaining non-structural inputs are the equivalence substitution
payload, the `Ms-Pro` head star payload, and the changed-bound `Ms-Fun` body
transport. -/
noncomputable def BetaInstantiationPreservesMSubRedStackMSubStar.of_under_head_constructors
    (hHead : BetaInstantiationPreservesMSubRedProHeadMSubStarPayload)
    (hEq : BetaInstantiationPreservesMEqRedStack)
    (hUnder : BetaInstantiationPreservesMSubRedUnderHeadMSubStarPayload)
    (hChange : BetaInstantiationPreservesMSubRedFunBodyHeadChangeMSubStarPayload) :
    BetaInstantiationPreservesMSubRedStackMSubStar :=
  BetaInstantiationPreservesMSubRedStackMSubStar.of_constructors
    hHead hEq
    (BetaInstantiationPreservesMSubRedFunBodyMSubStarPayload.of_under_head
      hUnder hChange)
    (BetaInstantiationPreservesMSubRedFOpBodyMSubStarPayload.of_under_head
      hUnder)

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

/-- Generalized stack append transports an empty-stack diagrammatic chain
through every operand of a scoped stack. -/
def MSubStarStackAppendPayload.iterate_scoped
    (hAppend : MSubStarStackAppendPayload)
    {Γ : Ctx} {source target : Term} {s : Stack}
    (hs : Stack.Scoped Γ.depth s)
    (hStar : MSubStar Γ [] source target) :
    MSubStar Γ s source target := by
  have aux :
      ∀ {base tail : Stack},
        Stack.Scoped Γ.depth tail →
          MSubStar Γ base source target →
            MSubStar Γ (base ++ tail) source target := by
    intro base tail htail hbase
    induction htail generalizing base with
    | nil =>
        simpa using hbase
    | @cons α s hα hrest ih =>
        have hbase' : MSubStar Γ (base ++ [α]) source target :=
          hAppend (Γ := Γ) (s := base) hbase hα
        have htail' : MSubStar Γ ((base ++ [α]) ++ s) source target :=
          ih hbase'
        simpa [List.append_assoc] using htail'
  simpa using aux (base := []) hs hStar

/-! ## MSubRed → MSubStar universal β-instantiation under preserved heads -/

/-- Lift an empty-stack diagrammatic-star chain through the β-instantiation
prefix. The chain `MSubStar Γ [] arg bound` (typically obtained from
`WSubMStar.toMSubStar`) is reweakened through every preserved head, with
each head's stored bound instantiated and source/target endpoints shifted.
This is the prefix-lift building block used by the `Ms-Pro` head case of the
universal `∀n` MSubRed→MSubStar β-instantiation theorem. -/
noncomputable def MSubStar.lift_through_instantiateBetaPrefix
    {Γ : Ctx} {bound arg : Term} (heads : Ctx)
    (hArgBound : WSubMStar Γ arg bound)
    (hpvCtxOuter : Prevalid (heads ++ { bound := bound, kind := .sub } :: Γ))
    (hStarBase : MSubStar Γ [] arg bound) :
    MSubStar (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ) []
      (Term.shiftBy 0 heads.length arg)
      (Term.shiftBy 0 heads.length bound) := by
  induction heads with
  | nil =>
      simpa [Ctx.instantiateBetaPrefix, Term.shiftBy_zero_id] using hStarBase
  | cons head heads ih =>
      have hpvTailCtx :
          Prevalid (heads ++ { bound := bound, kind := .sub } :: Γ) :=
        Prevalid.tail hpvCtxOuter
      have hHeadScoped :
          Term.Scoped (Γ.depth + heads.length + 1) head.bound := by
        simpa [Ctx.depth, List.length_append, Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc] using
          prevalid_head_scoped hpvCtxOuter
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgBound.scoped_left
      have hPrevalidTail :
          Prevalid
            (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ) :=
        BetaInstantiationPreservesPrevalidPrefix heads hArgBound hpvTailCtx
      have hpvNilTail :
          PrevalidExt
            (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ) [] :=
        PrevalidExt.nil hPrevalidTail
      have hStarTail :
          MSubStar
            (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ) []
            (Term.shiftBy 0 heads.length arg)
            (Term.shiftBy 0 heads.length bound) :=
        ih hpvTailCtx
      have hHeadInstScoped :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) head.bound) := by
        have hInst := Term.instantiate_scoped heads.length
          (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg) head.bound (by omega)
          hArgShiftScoped hHeadScoped
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInst
      have hNewEntryPrevalid :
          Prevalid
            ({ bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) head.bound,
                kind := head.kind } ::
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)) := by
        cases head with
        | mk hbb hk =>
            cases hk with
            | sub => exact Prevalid.sub hPrevalidTail hHeadInstScoped
            | equ => exact Prevalid.equ hPrevalidTail hHeadInstScoped
      have hWeakened :
          MSubStar
            ({ bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) head.bound,
                kind := head.kind } ::
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Stack.shift 0 [])
            (Term.shift 0 (Term.shiftBy 0 heads.length arg))
            (Term.shift 0 (Term.shiftBy 0 heads.length bound)) :=
        MSubStar.weaken_head hpvNilTail hNewEntryPrevalid hStarTail
      have hShiftCompose : ∀ (t : Term),
          Term.shift 0 (Term.shiftBy 0 heads.length t) =
            Term.shiftBy 0 (heads.length + 1) t := by
        intro t
        have h := Term.shiftBy_compose 0 heads.length 1 t
        simpa [Term.shift] using h
      simpa [Ctx.instantiateBetaPrefix, Stack.shift, hShiftCompose]
        using hWeakened

/-- **Universal MSubRed→MSubStar β-instantiation under any number of preserved
context heads, conditional on diagrammatic stack append.**

Mirrors `BetaInstantiationPreservesMEqRedUnderHeadsStack_universal` but on
`MSubRed` with `MSubStar` output. The conditional `MSubStarStackAppendPayload`
premise discharges the `Ms-Pro` head case at non-empty instantiated stack,
which is the structural obstruction inherited from
`BetaInstantiationPreservesMSubRedProHeadMSubStarPayload.of_stack_append`.

The other constructors close locally:
- `top`/`equ`/`app`: rebuild via `MSubRed.top`/`equ`/`app` and embed via
  `MSubStar.of_MSubRed`/`msubStar_app_fixed_arg`.
- `fun_`: uses `msubStar_abs_fun_body_equ_bound` (final `Ms-Fun` refl-body
  step absorbs the bound change without needing a head-change payload).
- `fOp`: uses `msubStar_abs_fOp_body_fixed_bound` after recursing on the body
  under one extra `.equ` head.

The equivalence-substitution sub-derivation in the `equ` constructor
delegates to `BetaInstantiationPreservesMEqRedUnderHeadsStack_universal`,
which is closed unconditionally. -/
noncomputable def BetaInstantiationPreservesMSubRedUnderHeadsStackMSubStar_universal_of_stack_append
    (hAppend : MSubStarStackAppendPayload) :
    ∀ n, BetaInstantiationPreservesMSubRedUnderHeadsStackMSubStar n := by
  intro n Γ bound arg lhs rhs heads s hlen hArgBound hRed
  subst hlen
  generalize hC : (heads ++ ({ bound := bound, kind := .sub } :: Γ : Ctx)) =
    C at hRed
  induction hRed generalizing heads with
  | pro hpv hb =>
      subst hC
      have hpvTarget := BetaInstantiationPreservesPrevalidExtUnderHeads
        (n := heads.length) rfl hArgBound hpv
      cases Ctx.subBinds_instantiateBetaPrefix
          (Γ := Γ) (bound := bound) (arg := arg) (heads := heads) hb with
      | preserved j hvar hbind =>
          rw [hvar]
          exact MSubStar.of_MSubRed (MSubRed.pro hpvTarget hbind)
      | argHead heq hvar htarget_eq =>
          rw [hvar, htarget_eq]
          have hStarBase : MSubStar Γ [] arg bound :=
            hArgBound.toMSubStar
          have hStarAtPrefix :
              MSubStar
                (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ) []
                (Term.shiftBy 0 heads.length arg)
                (Term.shiftBy 0 heads.length bound) :=
            MSubStar.lift_through_instantiateBetaPrefix heads hArgBound
              (PrevalidExt.ctx hpv) hStarBase
          have hStackScoped :=
            PrevalidExt.stack_scoped hpvTarget
          exact hAppend.iterate_scoped hStackScoped hStarAtPrefix
  | @top Γ' s' u hpv hu =>
      subst hC
      have hpvTarget := BetaInstantiationPreservesPrevalidExtUnderHeads
        (n := heads.length) rfl hArgBound hpv
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgBound.scoped_left
      have hu' : Term.Scoped (Γ.depth + heads.length + 1) u := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := bound, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at hu
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hu
      have huInstScoped :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) u) := by
        have hInst := Term.instantiate_scoped heads.length
          (Γ.depth + heads.length) (Term.shiftBy 0 heads.length arg) u
          (by omega) hArgShiftScoped hu'
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInst
      simpa [Term.instantiate] using
        MSubStar.of_MSubRed (MSubRed.top hpvTarget huInstScoped)
  | @equ Γ' s' u v hpv heq =>
      subst hC
      have hMEq :=
        BetaInstantiationPreservesMEqRedUnderHeadsStack_universal heads.length
          (heads := heads) rfl hArgBound heq
      have hpvTarget := BetaInstantiationPreservesPrevalidExtUnderHeads
        (n := heads.length) rfl hArgBound hpv
      exact MSubStar.of_MSubRed (MSubRed.equ hpvTarget hMEq)
  | @app Γ' s' u u' v hOp hv ihOp =>
      subst hC
      have hOp' := ihOp (heads := heads) rfl
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgBound.scoped_left
      have hv' : Term.Scoped (Γ.depth + heads.length + 1) v := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := bound, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at hv
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hv
      have hvInstScoped :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) v) := by
        have hInst := Term.instantiate_scoped heads.length
          (Γ.depth + heads.length) (Term.shiftBy 0 heads.length arg) v
          (by omega) hArgShiftScoped hv'
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInst
      have hpvTail :
          PrevalidExt
            (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
            (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) s') := by
        have hpvOp : PrevalidExt
            (heads ++ { bound := bound, kind := .sub } :: Γ) (v :: s') :=
          hOp.prevalidExt
        exact BetaInstantiationPreservesPrevalidExtUnderHeads
          (n := heads.length) rfl hArgBound (PrevalidExt.tail hpvOp)
      have hOpReady :
          MSubStar
            (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
            (Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) v ::
              Stack.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) s')
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) u)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) u') := by
        simpa [Stack.instantiate] using hOp'
      simpa [Term.instantiate, Stack.instantiate] using
        msubStar_app_fixed_arg hpvTail hvInstScoped hOpReady
  | @fun_ Γ' t t' body body' ht hT hBody ihBody =>
      subst hC
      have hT' :=
        BetaInstantiationPreservesMEqRedUnderHeadsStack_universal heads.length
          (heads := heads) rfl hArgBound hT
      have hBody' :=
        ihBody (heads := { bound := t, kind := .sub } :: heads)
          (by simp [List.cons_append])
      have hCtx_succ :
          Ctx.instantiateBetaPrefix arg (heads.length + 1)
              ({ bound := t, kind := .sub } :: heads) =
            { bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) t,
                kind := .sub } ::
              Ctx.instantiateBetaPrefix arg heads.length heads := by
        simp [Ctx.instantiateBetaPrefix]
      have hshift_succ :
          Term.shiftBy 0 (heads.length + 1) arg =
            Term.shift 0 (Term.shiftBy 0 heads.length arg) := by
        have h := Term.shiftBy_compose 0 heads.length 1 arg
        simpa [Term.shift] using h.symm
      have hBodyReady :
          MSubStar
            ({ bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) t,
                kind := .sub } ::
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)) []
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body)
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body') := by
        simp only [List.length_cons] at hBody'
        rw [hCtx_succ] at hBody'
        simpa using hBody'
      have hpvBodyOuter :
          Prevalid ({ bound := t, kind := .sub } ::
              (heads ++ { bound := bound, kind := .sub } :: Γ)) :=
        hBody.prevalid
      have hpvNil :
          PrevalidExt
            (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ) [] :=
        PrevalidExt.nil
          (BetaInstantiationPreservesPrevalidPrefix heads hArgBound
            (Prevalid.tail hpvBodyOuter))
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgBound.scoped_left
      have hArgSuccScoped :
          Term.Scoped (Γ.depth + heads.length + 1)
            (Term.shiftBy 0 (heads.length + 1) arg) := by
        have h := Term.shiftBy_scoped 0 (heads.length + 1) Γ.depth arg
          (Nat.zero_le Γ.depth) hArgBound.scoped_left
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
      have hBodyOriginal :
          Term.Scoped (Γ.depth + heads.length + 1 + 1) body := by
        have hbodyScoped := hBody.scoped_left
        have hd_eq : Ctx.depth
            ({ bound := t, kind := .sub } ::
              (heads ++ { bound := bound, kind := .sub } :: Γ)) =
            Γ.depth + heads.length + 1 + 1 := by
          simp [Ctx.depth, List.length_append]; omega
        rw [hd_eq] at hbodyScoped
        exact hbodyScoped
      have hbodyOriginalScopedRaw :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ) + 1)
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body) := by
        have hInst := Term.instantiate_scoped (heads.length + 1)
          (Γ.depth + heads.length + 1)
          (Term.shiftBy 0 (heads.length + 1) arg) body (by omega)
          hArgSuccScoped hBodyOriginal
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInst
      have hbodyOriginalScoped : Term.Scoped
          (Ctx.depth
            ({ bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) t,
                kind := .sub } ::
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)))
          (Term.instantiate (heads.length + 1)
            (Term.shiftBy 0 (heads.length + 1) arg) body) := by
        simpa [Ctx.depth, Nat.add_comm] using hbodyOriginalScopedRaw
      have hFunBound :
          MSubStar
            (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ) []
            (.abs
              (Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) t)
              (Term.instantiate (heads.length + 1)
                (Term.shiftBy 0 (heads.length + 1) arg) body))
            (.abs
              (Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) t')
              (Term.instantiate (heads.length + 1)
                (Term.shiftBy 0 (heads.length + 1) arg) body')) :=
        msubStar_abs_fun_body_equ_bound hpvNil hT' hbodyOriginalScoped
          hBodyReady
      simpa [Term.instantiate, hshift_succ] using hFunBound
  | @fOp Γ' s' t α body body' ht hα hBody ihBody =>
      subst hC
      have hBody' :=
        ihBody (heads := { bound := α, kind := .equ } :: heads)
          (by simp [List.cons_append])
      have hshift_succ :
          Term.shiftBy 0 (heads.length + 1) arg =
            Term.shift 0 (Term.shiftBy 0 heads.length arg) := by
        have h := Term.shiftBy_compose 0 heads.length 1 arg
        simpa [Term.shift] using h.symm
      have hStack_succ :
          Stack.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) (Stack.shift 0 s') =
            Stack.shift 0 (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) s') := by
        rw [hshift_succ]
        exact Stack.instantiate_succ_shift_zero heads.length
          (Term.shiftBy 0 heads.length arg) s'
      have hCtx_succ :
          Ctx.instantiateBetaPrefix arg (heads.length + 1)
              ({ bound := α, kind := .equ } :: heads) =
            { bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) α,
                kind := .equ } ::
              Ctx.instantiateBetaPrefix arg heads.length heads := by
        simp [Ctx.instantiateBetaPrefix]
      have hArgShiftScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.shiftBy 0 heads.length arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 heads.length Γ.depth arg
            (Nat.zero_le Γ.depth) hArgBound.scoped_left
      have htOriginal : Term.Scoped (Γ.depth + heads.length + 1) t := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := bound, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at ht
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht
      have hαOriginal : Term.Scoped (Γ.depth + heads.length + 1) α := by
        have hheads_depth :
            Ctx.depth (heads ++ { bound := bound, kind := .sub } :: Γ) =
              heads.length + 1 + Γ.depth := by
          simp [Ctx.depth, List.length_append, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        rw [hheads_depth] at hα
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hα
      have htInstScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) t) :=
        Term.instantiate_scoped heads.length (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg) t (by omega)
          hArgShiftScoped htOriginal
      have htInstScoped' :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) t) := by
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htInstScoped
      have hαInstScoped :
          Term.Scoped (Γ.depth + heads.length)
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) α) :=
        Term.instantiate_scoped heads.length (Γ.depth + heads.length)
          (Term.shiftBy 0 heads.length arg) α (by omega)
          hArgShiftScoped hαOriginal
      have hαInstScoped' :
          Term.Scoped
            (Ctx.depth
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Term.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) α) := by
        simpa [Ctx.depth, List.length_append,
          Ctx.length_instantiateBetaPrefix,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hαInstScoped
      have hBodyReady :
          MSubStar
            ({ bound := Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) α,
                kind := .equ } ::
              (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ))
            (Stack.shift 0 (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) s'))
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body)
            (Term.instantiate (heads.length + 1)
              (Term.shiftBy 0 (heads.length + 1) arg) body') := by
        simp only [List.length_cons] at hBody'
        rw [hCtx_succ] at hBody'
        rw [hStack_succ] at hBody'
        simpa using hBody'
      have hpvFOpExt :
          PrevalidExt
            (heads ++ { bound := bound, kind := .sub } :: Γ) (α :: s') :=
        PrevalidExt.cons hBody.prevalidExt.weaken_head_inv hα
      have hpvTail :
          PrevalidExt
            (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
            (Stack.instantiate heads.length
              (Term.shiftBy 0 heads.length arg) s') :=
        BetaInstantiationPreservesPrevalidExtUnderHeads
          (n := heads.length) rfl hArgBound (PrevalidExt.tail hpvFOpExt)
      have hFOp :
          MSubStar
            (Ctx.instantiateBetaPrefix arg heads.length heads ++ Γ)
            (Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) α ::
              Stack.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) s')
            (.abs
              (Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) t)
              (Term.instantiate (heads.length + 1)
                (Term.shiftBy 0 (heads.length + 1) arg) body))
            (.abs
              (Term.instantiate heads.length
                (Term.shiftBy 0 heads.length arg) t)
              (Term.instantiate (heads.length + 1)
                (Term.shiftBy 0 (heads.length + 1) arg) body')) :=
        msubStar_abs_fOp_body_fixed_bound hpvTail htInstScoped'
          hαInstScoped' hBodyReady
      simpa [Term.instantiate, Stack.instantiate, hshift_succ] using hFOp

/-- Closed stack-parametric MSubRed→MSubStar β-instantiation, conditional on
the diagrammatic stack-append payload. This is the empty-prefix specialization
of the universal `∀n` theorem. -/
noncomputable def BetaInstantiationPreservesMSubRedStackMSubStar_of_stack_append
    (hAppend : MSubStarStackAppendPayload) :
    BetaInstantiationPreservesMSubRedStackMSubStar :=
  BetaInstantiationPreservesMSubRedStackMSubStar.of_underHeads_zero
    (BetaInstantiationPreservesMSubRedUnderHeadsStackMSubStar_universal_of_stack_append
      hAppend 0)

/-- Closed empty-stack MSubRed→MSubStar β-instantiation, conditional on the
diagrammatic stack-append payload. -/
noncomputable def BetaInstantiationPreservesMSubRedMSubStar_of_stack_append
    (hAppend : MSubStarStackAppendPayload) :
    BetaInstantiationPreservesMSubRedMSubStar :=
  BetaInstantiationPreservesMSubRedMSubStar.of_stack
    (BetaInstantiationPreservesMSubRedStackMSubStar_of_stack_append hAppend)

noncomputable def BetaInstantiationPreservesMSubRedProHeadMSubStarPayload.of_stack_append
    (hAppend : MSubStarStackAppendPayload) :
    BetaInstantiationPreservesMSubRedProHeadMSubStarPayload := by
  intro Γ bound arg s hArgBound hpv
  have hpvInst : PrevalidExt Γ (Stack.instantiate 0 arg s) :=
    BetaInstantiationPreservesPrevalidExtStack hArgBound hpv
  have hStar : MSubStar Γ [] arg bound :=
    hArgBound.toMSubStar
  have hStack : MSubStar Γ (Stack.instantiate 0 arg s) arg bound :=
    hAppend.iterate_scoped (PrevalidExt.stack_scoped hpvInst) hStar
  simpa [Term.instantiate, Term.instantiate_shift_id] using hStack

/-- The under-head `Ms-Pro` frontier follows from lookup analysis plus the
existing diagrammatic stack-append lift. The changed index-`1` case is exactly
the lifted `WSubMStar` premise; the preserved head and true-tail lookups are
raw `Ms-Pro` steps in the target context. -/
noncomputable def BetaInstantiationPreservesMSubRedUnderHeadProMSubStarPayload.of_stack_append
    (hAppend : MSubStarStackAppendPayload) :
    BetaInstantiationPreservesMSubRedUnderHeadProMSubStarPayload := by
  intro Γ bound arg head target kind s i hArgBound hpv hb
  have hpvTarget :
      PrevalidExt ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
        (Stack.instantiate 1 (Term.shift 0 arg) s) :=
    BetaInstantiationPreservesPrevalidExtUnderHead hArgBound hpv
  cases i with
  | zero =>
      cases kind with
      | sub =>
          have htarget :
              target = Term.shift 0 head := by
            have h : Term.shift 0 head = target := by
              simpa [Ctx.subBinds] using hb
            exact h.symm
          have hbind :
              Ctx.subBinds
                ({ bound := Term.instantiate 0 arg head, kind := CtxEntryKind.sub } :: Γ)
                0 (Term.shift 0 (Term.instantiate 0 arg head)) := by
            simp [Ctx.subBinds]
          have htargetInst :
              Term.instantiate 1 (Term.shift 0 arg) target =
                Term.shift 0 (Term.instantiate 0 arg head) := by
            rw [htarget]
            exact (Term.shiftBy_instantiate 0 1 0 arg head (Nat.le_refl 0)).symm
          simpa [Term.instantiate, htargetInst] using
            MSubStar.of_MSubRed (MSubRed.pro hpvTarget hbind)
      | equ =>
          simp [Ctx.subBinds] at hb
  | succ i =>
      cases i with
      | zero =>
          have htarget :
              target = Term.shift 0 (Term.shift 0 bound) := by
            cases kind <;>
              (have h : Term.shift 0 (Term.shift 0 bound) = target := by
                simpa [Ctx.subBinds] using hb
               exact h.symm)
          have hNew : Prevalid
              ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ) :=
            PrevalidExt.ctx hpvTarget
          have hBase :
              MSubStar ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
                [] (Term.shift 0 arg) (Term.shift 0 bound) :=
            MSubStar.weaken_head
              (PrevalidExt.nil hArgBound.prevalid) hNew hArgBound.toMSubStar
          have hStack :
              MSubStar ({ bound := Term.instantiate 0 arg head, kind := kind } :: Γ)
                (Stack.instantiate 1 (Term.shift 0 arg) s)
                (Term.shift 0 arg) (Term.shift 0 bound) :=
            hAppend.iterate_scoped (PrevalidExt.stack_scoped hpvTarget) hBase
          have htargetInst :
              Term.instantiate 1 (Term.shift 0 arg) target = Term.shift 0 bound := by
            rw [htarget]
            simpa [Term.shift_shift_zero] using
              Term.instantiate_shift_id 1 (Term.shift 0 arg) (Term.shift 0 bound)
          simpa [Term.instantiate, htargetInst] using hStack
      | succ j =>
          cases kind with
          | sub =>
              simp [Ctx.subBinds] at hb
              rcases hb with ⟨tailTarget, htail, htarget⟩
              subst htarget
              have hbind :
                  Ctx.subBinds
                    ({ bound := Term.instantiate 0 arg head, kind := CtxEntryKind.sub } :: Γ)
                    (j + 1) (Term.shift 0 tailTarget) := by
                exact Ctx.subBinds_weaken_head
                  ({ bound := Term.instantiate 0 arg head, kind := CtxEntryKind.sub } : CtxEntry)
                  htail
              have htargetInst :
                  Term.instantiate 1 (Term.shift 0 arg)
                    (Term.shift 0 (Term.shift 0 tailTarget)) =
                    Term.shift 0 tailTarget := by
                simpa [Term.shift_shift_zero] using
                  Term.instantiate_shift_id 1 (Term.shift 0 arg)
                    (Term.shift 0 tailTarget)
              simpa [Term.instantiate, htargetInst] using
                MSubStar.of_MSubRed (MSubRed.pro hpvTarget hbind)
          | equ =>
              simp [Ctx.subBinds] at hb
              rcases hb with ⟨tailTarget, htail, htarget⟩
              subst htarget
              have hbind :
                  Ctx.subBinds
                    ({ bound := Term.instantiate 0 arg head, kind := CtxEntryKind.equ } :: Γ)
                    (j + 1) (Term.shift 0 tailTarget) := by
                exact Ctx.subBinds_weaken_head
                  ({ bound := Term.instantiate 0 arg head, kind := CtxEntryKind.equ } : CtxEntry)
                  htail
              have htargetInst :
                  Term.instantiate 1 (Term.shift 0 arg)
                    (Term.shift 0 (Term.shift 0 tailTarget)) =
                    Term.shift 0 tailTarget := by
                simpa [Term.shift_shift_zero] using
                  Term.instantiate_shift_id 1 (Term.shift 0 arg)
                    (Term.shift 0 tailTarget)
              simpa [Term.instantiate, htargetInst] using
                MSubStar.of_MSubRed (MSubRed.pro hpvTarget hbind)

/-- Convenience assembler once the under-head `Ms-Pro` frontier is supplied
by the general diagrammatic stack-append lift. The remaining inputs are the
under-head equivalence substitution and body frontiers. -/
noncomputable def BetaInstantiationPreservesMSubRedUnderHeadMSubStarPayload.of_stack_append_constructors
    (hAppend : MSubStarStackAppendPayload)
    (hEq : BetaInstantiationPreservesMEqRedUnderHeadStack)
    (hFun : BetaInstantiationPreservesMSubRedUnderHeadFunMSubStarPayload)
    (hFOp : BetaInstantiationPreservesMSubRedUnderHeadFOpMSubStarPayload) :
    BetaInstantiationPreservesMSubRedUnderHeadMSubStarPayload :=
  BetaInstantiationPreservesMSubRedUnderHeadMSubStarPayload.of_constructors
    (BetaInstantiationPreservesMSubRedUnderHeadProMSubStarPayload.of_stack_append
      hAppend)
    hEq hFun hFOp

/-- Convenience assembler that expands the under-head equivalence
substitution premise into its three remaining binder frontiers. Together with
stack append, this leaves no opaque under-head `MEqRed` substitution input. -/
noncomputable def BetaInstantiationPreservesMSubRedUnderHeadMSubStarPayload.of_stack_append_eq_constructors
    (hAppend : MSubStarStackAppendPayload)
    (hEqFun : BetaInstantiationPreservesMEqRedUnderHeadFunStackPayload)
    (hEqBet : BetaInstantiationPreservesMEqRedUnderHeadBetStackPayload)
    (hEqFOp : BetaInstantiationPreservesMEqRedUnderHeadFOpStackPayload)
    (hFun : BetaInstantiationPreservesMSubRedUnderHeadFunMSubStarPayload)
    (hFOp : BetaInstantiationPreservesMSubRedUnderHeadFOpMSubStarPayload) :
    BetaInstantiationPreservesMSubRedUnderHeadMSubStarPayload :=
  BetaInstantiationPreservesMSubRedUnderHeadMSubStarPayload.of_stack_append_constructors
    hAppend
    (BetaInstantiationPreservesMEqRedUnderHeadStack.of_constructors
      hEqFun hEqBet hEqFOp)
    hFun hFOp

/-- Stack-targeted subtype β-instantiation assembled from stack append and
under-head constructor frontiers. This packages both `Ms-Pro` obligations
through `MSubStarStackAppendPayload`, leaving only equivalence substitution,
under-head body frontiers, and changed-bound `Ms-Fun` transport explicit. -/
noncomputable def BetaInstantiationPreservesMSubRedStackMSubStar.of_stack_append_under_head_constructors
    (hAppend : MSubStarStackAppendPayload)
    (hEq : BetaInstantiationPreservesMEqRedStack)
    (hEqUnder : BetaInstantiationPreservesMEqRedUnderHeadStack)
    (hFunUnder : BetaInstantiationPreservesMSubRedUnderHeadFunMSubStarPayload)
    (hFOpUnder : BetaInstantiationPreservesMSubRedUnderHeadFOpMSubStarPayload)
    (hChange : BetaInstantiationPreservesMSubRedFunBodyHeadChangeMSubStarPayload) :
    BetaInstantiationPreservesMSubRedStackMSubStar :=
  BetaInstantiationPreservesMSubRedStackMSubStar.of_under_head_constructors
    (BetaInstantiationPreservesMSubRedProHeadMSubStarPayload.of_stack_append
      hAppend)
    hEq
    (BetaInstantiationPreservesMSubRedUnderHeadMSubStarPayload.of_stack_append_constructors
      hAppend hEqUnder hFunUnder hFOpUnder)
    hChange

/-- Stack-targeted subtype β-instantiation with both `Ms-Pro` frontiers
derived from stack append and under-head equivalence substitution expanded to
the three binder frontiers. -/
noncomputable def BetaInstantiationPreservesMSubRedStackMSubStar.of_stack_append_under_head_eq_constructors
    (hAppend : MSubStarStackAppendPayload)
    (hEq : BetaInstantiationPreservesMEqRedStack)
    (hEqFunUnder : BetaInstantiationPreservesMEqRedUnderHeadFunStackPayload)
    (hEqBetUnder : BetaInstantiationPreservesMEqRedUnderHeadBetStackPayload)
    (hEqFOpUnder : BetaInstantiationPreservesMEqRedUnderHeadFOpStackPayload)
    (hFunUnder : BetaInstantiationPreservesMSubRedUnderHeadFunMSubStarPayload)
    (hFOpUnder : BetaInstantiationPreservesMSubRedUnderHeadFOpMSubStarPayload)
    (hChange : BetaInstantiationPreservesMSubRedFunBodyHeadChangeMSubStarPayload) :
    BetaInstantiationPreservesMSubRedStackMSubStar :=
  BetaInstantiationPreservesMSubRedStackMSubStar.of_stack_append_under_head_constructors
    hAppend hEq
    (BetaInstantiationPreservesMEqRedUnderHeadStack.of_constructors
      hEqFunUnder hEqBetUnder hEqFOpUnder)
    hFunUnder hFOpUnder hChange

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

/-- The `WfCtxEqu`-parametric β preservation payload follows from
function-bound inversion under that same invariant and exact de Bruijn
body-instantiation preservation. -/
noncomputable def StepBetaPreservesWfMUnderWfCtx_of
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx) :
    StepBetaPreservesWfMUnderWfCtx := by
  intro Γ bound body arg hΓ hwf
  obtain ⟨result, hFun, hArg⟩ := hwf.app_inv
  have hEquBoundResult : WEquMStar Γ bound result := hInv hΓ hFun
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

/-- Direct `.sub` replacement payload entry point for the typed-`FOp` direct
split-beta target-application machine assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_sub_replace
    hSubst hAppend hBridge hInv hBetaBody hFOpBody hTargetApp hTailCons
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- Immediate/factored `.sub` replacement payload entry point for the
typed-`FOp` direct split-beta target-application machine assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_sub_replace
    hSubst hAppend hBridge hInv hBetaBody hFOpBody hTargetApp hTailCons
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- Body-transport entry point for the typed-`FOp` direct split-beta
target-application machine assembly, using direct `.sub` replacement
payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_direct_sub_payloads
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
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_sub_replace
    hSubst hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody
    hTargetApp hTailCons
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- Body-transport entry point for the typed-`FOp` direct split-beta
target-application machine assembly, using immediate/factored `.sub`
replacement payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_immediate_sub_payloads_and_under
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
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_sub_replace
    hSubst hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody
    hTargetApp hTailCons
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- Direct `.sub` replacement payload entry point for the native-`FOp`
direct split-beta target-application machine assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons_sub_replace
    hSubst hAppend hBridge hInv hBetaBody hFOpBody hTargetApp hTailCons
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- Immediate/factored `.sub` replacement payload entry point for the
native-`FOp` direct split-beta target-application machine assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons_sub_replace
    hSubst hAppend hBridge hInv hBetaBody hFOpBody hTargetApp hTailCons
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- Body-transport entry point for the native-`FOp` direct split-beta
target-application machine assembly, using direct `.sub` replacement
payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons_direct_sub_payloads
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
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons_sub_replace
    hSubst hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody
    hTargetApp hTailCons
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- Body-transport entry point for the native-`FOp` direct split-beta
target-application machine assembly, using immediate/factored `.sub`
replacement payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons_immediate_sub_payloads_and_under
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
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_target_app_machine_tail_cons_sub_replace
    hSubst hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody
    hTargetApp hTailCons
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- Direct `.sub` replacement payload entry point for the typed-operator
typed-`FOp` direct split-beta machine assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_operator_machine_tail_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_operator_machine_tail_sub_replace
    hSubst hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- Immediate/factored `.sub` replacement payload entry point for the
typed-operator typed-`FOp` direct split-beta machine assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_operator_machine_tail_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_operator_machine_tail_sub_replace
    hSubst hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- Body-transport entry point for the typed-operator typed-`FOp` direct
split-beta machine assembly, using direct `.sub` replacement payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_operator_machine_tail_direct_sub_payloads
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
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_operator_machine_tail_sub_replace
    hSubst hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- Body-transport entry point for the typed-operator typed-`FOp` direct
split-beta machine assembly, using immediate/factored `.sub` replacement
payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_operator_machine_tail_immediate_sub_payloads_and_under
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
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_operator_machine_tail_sub_replace
    hSubst hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- Direct `.sub` replacement payload entry point for the machine-operator
typed-`FOp` direct split-beta machine assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_machine_operator_machine_tail_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_machine_operator_machine_tail_sub_replace
    hSubst hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- Immediate/factored `.sub` replacement payload entry point for the
machine-operator typed-`FOp` direct split-beta machine assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_machine_operator_machine_tail_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_typed_fop_machine_operator_machine_tail_sub_replace
    hSubst hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- Body-transport entry point for the machine-operator typed-`FOp` direct
split-beta machine assembly, using direct `.sub` replacement payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_machine_operator_machine_tail_direct_sub_payloads
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
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_machine_operator_machine_tail_sub_replace
    hSubst hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- Body-transport entry point for the machine-operator typed-`FOp` direct
split-beta machine assembly, using immediate/factored `.sub` replacement
payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_machine_operator_machine_tail_immediate_sub_payloads_and_under
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
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_typed_fop_machine_operator_machine_tail_sub_replace
    hSubst hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- Direct `.sub` replacement payload entry point for the typed-operator
native-`FOp` direct split-beta machine assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_operator_machine_tail_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_operator_machine_tail_sub_replace
    hSubst hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- Immediate/factored `.sub` replacement payload entry point for the
typed-operator native-`FOp` direct split-beta machine assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_operator_machine_tail_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_operator_machine_tail_sub_replace
    hSubst hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- Body-transport entry point for the typed-operator native-`FOp` direct
split-beta machine assembly, using direct `.sub` replacement payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_operator_machine_tail_direct_sub_payloads
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
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_operator_machine_tail_sub_replace
    hSubst hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- Body-transport entry point for the typed-operator native-`FOp` direct
split-beta machine assembly, using immediate/factored `.sub` replacement
payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_operator_machine_tail_immediate_sub_payloads_and_under
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
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_operator_machine_tail_sub_replace
    hSubst hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- Direct `.sub` replacement payload entry point for the machine-operator
native-`FOp` direct split-beta machine assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_machine_operator_machine_tail_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_machine_operator_machine_tail_sub_replace
    hSubst hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- Immediate/factored `.sub` replacement payload entry point for the
machine-operator native-`FOp` direct split-beta machine assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_machine_operator_machine_tail_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_no_empty_and_direct_split_beta_fop_machine_operator_machine_tail_sub_replace
    hSubst hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- Body-transport entry point for the machine-operator native-`FOp` direct
split-beta machine assembly, using direct `.sub` replacement payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_machine_operator_machine_tail_direct_sub_payloads
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
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_machine_operator_machine_tail_sub_replace
    hSubst hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- Body-transport entry point for the machine-operator native-`FOp` direct
split-beta machine assembly, using immediate/factored `.sub` replacement
payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_machine_operator_machine_tail_immediate_sub_payloads_and_under
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
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_fop_machine_operator_machine_tail_sub_replace
    hSubst hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- External-empty direct `.sub` replacement payload entry point for the
typed-`FOp` direct split-beta target-application assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_sub_replace
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hTargetApp hTailCons
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- External-empty immediate/factored `.sub` replacement payload entry point
for the typed-`FOp` direct split-beta target-application assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_sub_replace
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hTargetApp hTailCons
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- External-empty body-transport entry point for the typed-`FOp` direct
split-beta target-application assembly, using direct `.sub` replacement
payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_direct_sub_payloads
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
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_sub_replace
    hSubst hEmpty hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody
    hTargetApp hTailCons
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- External-empty body-transport entry point for the typed-`FOp` direct
split-beta target-application assembly, using immediate/factored `.sub`
replacement payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_immediate_sub_payloads_and_under
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
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_target_app_machine_tail_cons_sub_replace
    hSubst hEmpty hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody
    hTargetApp hTailCons
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- External-empty direct `.sub` replacement payload entry point for the
native-`FOp` direct split-beta target-application assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_target_app_machine_tail_cons_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_target_app_machine_tail_cons_sub_replace
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hTargetApp hTailCons
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- External-empty immediate/factored `.sub` replacement payload entry point
for the native-`FOp` direct split-beta target-application assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_target_app_machine_tail_cons_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hTargetApp : MEqRedAppTargetPreservesWfMPayload)
    (hTailCons : MEqRedMachineTailStepPreservesConsPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_target_app_machine_tail_cons_sub_replace
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hTargetApp hTailCons
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- External-empty body-transport entry point for the native-`FOp` direct
split-beta target-application assembly, using direct `.sub` replacement
payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_target_app_machine_tail_cons_direct_sub_payloads
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
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_target_app_machine_tail_cons_sub_replace
    hSubst hEmpty hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody
    hTargetApp hTailCons
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- External-empty body-transport entry point for the native-`FOp` direct
split-beta target-application assembly, using immediate/factored `.sub`
replacement payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_target_app_machine_tail_cons_immediate_sub_payloads_and_under
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
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_target_app_machine_tail_cons_sub_replace
    hSubst hEmpty hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody
    hTargetApp hTailCons
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- External-empty direct `.sub` replacement payload entry point for the
typed-operator typed-`FOp` direct split-beta assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_operator_machine_tail_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_operator_machine_tail_sub_replace
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- External-empty immediate/factored `.sub` replacement payload entry point
for the typed-operator typed-`FOp` direct split-beta assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_operator_machine_tail_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_operator_machine_tail_sub_replace
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- External-empty body-transport entry point for the typed-operator
typed-`FOp` direct split-beta assembly, using direct `.sub` replacement
payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_operator_machine_tail_direct_sub_payloads
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
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_operator_machine_tail_sub_replace
    hSubst hEmpty hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- External-empty body-transport entry point for the typed-operator
typed-`FOp` direct split-beta assembly, using immediate/factored `.sub`
replacement payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_operator_machine_tail_immediate_sub_payloads_and_under
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
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_operator_machine_tail_sub_replace
    hSubst hEmpty hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- External-empty direct `.sub` replacement payload entry point for the
machine-operator typed-`FOp` direct split-beta assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_machine_operator_machine_tail_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_machine_operator_machine_tail_sub_replace
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- External-empty immediate/factored `.sub` replacement payload entry point
for the machine-operator typed-`FOp` direct split-beta assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_machine_operator_machine_tail_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyTypedPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_typed_fop_machine_operator_machine_tail_sub_replace
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- External-empty body-transport entry point for the machine-operator
typed-`FOp` direct split-beta assembly, using direct `.sub` replacement
payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_machine_operator_machine_tail_direct_sub_payloads
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
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_machine_operator_machine_tail_sub_replace
    hSubst hEmpty hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- External-empty body-transport entry point for the machine-operator
typed-`FOp` direct split-beta assembly, using immediate/factored `.sub`
replacement payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_machine_operator_machine_tail_immediate_sub_payloads_and_under
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
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_typed_fop_machine_operator_machine_tail_sub_replace
    hSubst hEmpty hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- External-empty direct `.sub` replacement payload entry point for the
typed-operator native-`FOp` direct split-beta assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_operator_machine_tail_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_operator_machine_tail_sub_replace
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- External-empty immediate/factored `.sub` replacement payload entry point
for the typed-operator native-`FOp` direct split-beta assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_operator_machine_tail_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeTypedPayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_operator_machine_tail_sub_replace
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- External-empty body-transport entry point for the typed-operator
native-`FOp` direct split-beta assembly, using direct `.sub` replacement
payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_operator_machine_tail_direct_sub_payloads
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
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_operator_machine_tail_sub_replace
    hSubst hEmpty hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- External-empty body-transport entry point for the typed-operator
native-`FOp` direct split-beta assembly, using immediate/factored `.sub`
replacement payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_operator_machine_tail_immediate_sub_payloads_and_under
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
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_operator_machine_tail_sub_replace
    hSubst hEmpty hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- External-empty direct `.sub` replacement payload entry point for the
machine-operator native-`FOp` direct split-beta assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_machine_operator_machine_tail_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_machine_operator_machine_tail_sub_replace
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- External-empty immediate/factored `.sub` replacement payload entry point
for the machine-operator native-`FOp` direct split-beta assembly. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_machine_operator_machine_tail_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hAppend : MSubStarStackAppendPayload)
    (hBridge : MSubStarToWSubMStarPayload)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hBetaBody : MEqRedBetaBodyPreservesWfMPayload)
    (hFOpBody : MEqRedFOpBodyPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_msubstar_stack_append_and_direct_split_beta_fop_machine_operator_machine_tail_sub_replace
    hSubst hEmpty hAppend hBridge hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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

/-- External-empty body-transport entry point for the machine-operator
native-`FOp` direct split-beta assembly, using direct `.sub` replacement
payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_machine_operator_machine_tail_direct_sub_payloads
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
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_machine_operator_machine_tail_sub_replace
    hSubst hEmpty hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads) hNoTop

/-- External-empty body-transport entry point for the machine-operator
native-`FOp` direct split-beta assembly, using immediate/factored `.sub`
replacement payloads. -/
noncomputable def
    MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_machine_operator_machine_tail_immediate_sub_payloads_and_under
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
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt) :
    MEqRedPreservesWfMachineState :=
  MEqRedPreservesWfMachineState.of_body_transports_and_direct_split_beta_fop_machine_operator_machine_tail_sub_replace
    hSubst hEmpty hEqBody hSubBody hPres hStep hInv hBetaBody hFOpBody hOpFun hTail
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hNoTop

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
payload, direct `.sub` replacement residuals, and the two directional
`Me-FOp` head/body transports. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_direct_sub_payloads_and_head_transports
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_sub_replace_and_head_transports
    hSubst hShape hShapeWf hOpFun
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)
    hSubToEqu hEquToSub

/-- Contextual preservation from a shape-only function-bound chain payload,
joined-bound well-formedness under `WfCtxEqu`, the native `Me-App` operator
payload, immediate top-level `.sub` replacement residuals plus the named
preserved-head replacement payload, and the two directional `Me-FOp`
head/body transports. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_immediate_sub_payloads_and_under_and_head_transports
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_sub_replace_and_head_transports
    hSubst hShape hShapeWf hOpFun
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hSubToEqu hEquToSub

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

/-- Diagnostic head-kind contextual route using direct `.sub` replacement
residual payloads for `Me-Fun`. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_direct_sub_payloads_and_head_kind_transport
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hHeadTransport : WfMHeadKindTransportPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_sub_replace_and_head_kind_transport
    hSubst hShape hShapeWf hOpFun
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)
    hHeadTransport

/-- Diagnostic head-kind contextual route using immediate top-level `.sub`
replacement residuals plus the named preserved-head replacement payload for
`Me-Fun`. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_immediate_sub_payloads_and_under_and_head_kind_transport
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hHeadTransport : WfMHeadKindTransportPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_wfctx_no_beta_and_sub_replace_and_head_kind_transport
    hSubst hShape hShapeWf hOpFun
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hHeadTransport

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

/-- Left-factored contextual route using direct `.sub` replacement residual
payloads for `Me-Fun`. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_left_factored_no_beta_and_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_wfctx_left_factored_no_beta_and_sub_replace
    hSubst hShape hShapeWf hLeft
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)
    hFOpBody

/-- Left-factored contextual route using immediate top-level `.sub`
replacement residuals plus the named preserved-head replacement payload for
`Me-Fun`. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_left_factored_no_beta_and_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hFOpBody : MEqRedFOpBodyPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_wfctx_left_factored_no_beta_and_sub_replace
    hSubst hShape hShapeWf hLeft
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hFOpBody

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

/-- Factored contextual route using direct `.sub` replacement residual
payloads and the two directional `Me-FOp` head/body transports. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_factored_no_beta_and_direct_sub_payloads_and_head_transports
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_wfctx_factored_no_beta_and_sub_replace_and_head_transports
    hSubst hShape hShapeWf hLeft
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)
    hSubToEqu hEquToSub

/-- Factored contextual route using immediate top-level `.sub` replacement
residuals plus the named preserved-head replacement payload and the two
directional `Me-FOp` head/body transports. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_factored_no_beta_and_immediate_sub_payloads_and_under_and_head_transports
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_wfctx_factored_no_beta_and_sub_replace_and_head_transports
    hSubst hShape hShapeWf hLeft
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hSubToEqu hEquToSub

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

/-- Factored head-kind contextual route using direct `.sub` replacement
residual payloads for `Me-Fun`. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_factored_no_beta_and_direct_sub_payloads
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hHeadTransport : WfMHeadKindTransportPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_wfctx_factored_no_beta_and_sub_replace
    hSubst hShape hShapeWf hLeft
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)
    hHeadTransport

/-- Factored head-kind contextual route using immediate top-level `.sub`
replacement residuals plus the named preserved-head replacement payload for
`Me-Fun`. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_wfctx_factored_no_beta_and_immediate_sub_payloads_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hHeadTransport : WfMHeadKindTransportPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_wfctx_factored_no_beta_and_sub_replace
    hSubst hShape hShapeWf hLeft
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hHeadTransport

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

/-- Machine-state-derived contextual preservation using direct `.sub`
replacement residual payloads and split `Me-FOp` head/body transports. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_machine_state_no_beta_and_direct_sub_payloads_and_head_transports
    (hMachine : MEqRedPreservesWfMachineState)
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_machine_state_no_beta_and_sub_replace_and_head_transports
    hMachine hSubst hShape hOpFun
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)
    hSubToEqu hEquToSub

/-- Machine-state-derived contextual preservation using immediate top-level
`.sub` replacement residuals plus the named preserved-head replacement
payload and split `Me-FOp` head/body transports. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_machine_state_no_beta_and_immediate_sub_payloads_and_under_and_head_transports
    (hMachine : MEqRedPreservesWfMachineState)
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hOpFun : MEqRedAppFunctionSupertypePayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_machine_state_no_beta_and_sub_replace_and_head_transports
    hMachine hSubst hShape hOpFun
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hSubToEqu hEquToSub

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

/-- Factored machine-state-derived contextual preservation using direct
`.sub` replacement residual payloads and split `Me-FOp` head/body transports. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_machine_state_factored_no_beta_and_direct_sub_payloads_and_head_transports
    (hMachine : MEqRedPreservesWfMachineState)
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_machine_state_factored_no_beta_and_sub_replace_and_head_transports
    hMachine hSubst hShape hLeft
    (WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads)
    hSubToEqu hEquToSub

/-- Factored machine-state-derived contextual preservation using immediate
top-level `.sub` replacement residuals plus the named preserved-head
replacement payload and split `Me-FOp` head/body transports. -/
noncomputable def
    MEqRedPreservesWfMContextual.of_chain_shape_machine_state_factored_no_beta_and_immediate_sub_payloads_and_under_and_head_transports
    (hMachine : MEqRedPreservesWfMachineState)
    (hSubst : BetaInstantiationPreservesWfM)
    (hShape : AbsFunctionBoundChainShapePayload)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload) :
    MEqRedPreservesWfMContextual :=
  MEqRedPreservesWfMContextual.of_chain_shape_machine_state_factored_no_beta_and_sub_replace_and_head_transports
    hMachine hSubst hShape hLeft
    (WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads)
    hSubToEqu hEquToSub

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

/-- `WfCtxEqu`-parametric variant of `wf_right_nonempty_of_new_wf`. The
recursive abstraction-body case extends the invariant with the body `.sub`
head, matching the de Bruijn binder discipline. -/
theorem wf_right_under_wfctx_nonempty_of_new_wf
    (hBeta : StepBetaPreservesWfMUnderWfCtx)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf)
    {depth : Nat} {t t' : Term} (hstep : StepAt depth t t') :
    Nonempty (∀ {Γ : Ctx}, Γ.depth = depth → WfCtxEqu Γ →
      WfM Γ t → WfM Γ t') := by
  induction hstep with
  | beta =>
      exact ⟨fun {Γ} _hdepth hΓ hwf => hBeta hΓ hwf⟩
  | @appL depth op op' arg hOp _hArgScoped ih =>
      exact ⟨fun {Γ} hdepth hΓ hwf =>
        let ⟨funBound, hFun, hArg⟩ := hwf.app_inv
        let hwfOp' : WfM Γ op' := ih.some hdepth hΓ hFun.wf_left
        let hBack : WSubMStar Γ op' op :=
          WSubMStar.of_StepAt_back (by simpa [hdepth] using hOp)
            hFun.wf_left hwfOp'
        WfM.app (WSubMStar.trans hFun.wf_left hBack hFun) hArg⟩
  | @appR depth op arg arg' _hOpScoped hArgStep ih =>
      exact ⟨fun {Γ} hdepth hΓ hwf =>
        let ⟨funBound, hFun, hArg⟩ := hwf.app_inv
        let hwfArg' : WfM Γ arg' := ih.some hdepth hΓ hArg.wf_left
        let hBack : WSubMStar Γ arg' arg :=
          WSubMStar.of_StepAt_back (by simpa [hdepth] using hArgStep)
            hArg.wf_left hwfArg'
        WfM.app hFun (WSubMStar.trans hArg.wf_left hBack hArg)⟩
  | @absBound depth bound bound' body hBound _hBodyScoped _ih =>
      exact ⟨fun {Γ} hdepth hΓ hwf =>
        let hParts := hwf.fun_inv
        let hwfBound' : WfM Γ bound' := _ih.some hdepth hΓ hParts.1
        let hEqBound : MEqRed Γ [] bound bound' :=
          MEqRed.of_StepAt (by simpa [hdepth] using hBound) rfl
            (PrevalidExt.nil hParts.1.prevalid)
        WfM.fun_ hwfBound'
          (hSubHeadReplace hEqBound hwfBound' hParts.2)⟩
  | @absBody depth bound body body' _hBoundScoped hBody ih =>
      exact ⟨fun {Γ} hdepth hΓ hwf =>
        let hParts := hwf.fun_inv
        let hBody' : WfM ({ bound := bound, kind := .sub } :: Γ) body' :=
          ih.some (by simpa [Ctx.depth, hdepth]) (WfCtxEqu.sub hΓ) hParts.2
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

/-- `WfCtxEqu`-parametric operational well-formedness preservation reduced to
β instantiation and the sharpened `.sub` head replacement payload. -/
noncomputable def StepPreservesWfMUnderWfCtx_of_new_wf
    (hBeta : StepBetaPreservesWfMUnderWfCtx)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf) :
    StepPreservesWfMUnderWfCtx := by
  intro Γ t t' hΓ hstep hwf
  exact (StepAt.wf_right_under_wfctx_nonempty_of_new_wf
    hBeta hSubHeadReplace hstep).some rfl hΓ hwf

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

/-- `WfCtxEqu`-parametric operational preservation from the lower-level β
components and sharpened `.sub` head replacement. -/
noncomputable def StepPreservesWfMUnderWfCtx_of_components
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hSubHeadReplace : WfMSubHeadReplaceOfNewWf) :
    StepPreservesWfMUnderWfCtx :=
  StepPreservesWfMUnderWfCtx_of_new_wf
    (StepBetaPreservesWfMUnderWfCtx_of hSubst hInv)
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

/-- `WfCtxEqu`-parametric operational preservation from direct `.sub` head
replacement residuals. -/
noncomputable def StepPreservesWfMUnderWfCtx_of_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new) :
    StepPreservesWfMUnderWfCtx :=
  StepPreservesWfMUnderWfCtx_of_components hSubst hInv
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

/-- `WfCtxEqu`-parametric operational preservation from immediate top-level
direct `.sub` replacement residuals and a factored preserved-head replacement
payload. -/
noncomputable def
    StepPreservesWfMUnderWfCtx_of_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hInv : AbsFunctionBoundInversionUnderWfCtx)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new) :
    StepPreservesWfMUnderWfCtx :=
  StepPreservesWfMUnderWfCtx_of_components hSubst hInv
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

/-- De Bruijn preservation with the function-bound chain-shape payload derived
directly from global strong commutativity. This exposes the remaining
Theorem 5 frontier after Theorem 3 has supplied the abstraction-shape
collapse: beta instantiation, empty-stack equivalence preservation, and
`.sub` replacement. -/
noncomputable def
    Theorem_5_DeBruijn_Preservation_of_comm_meq_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ [])
    (hMEqPres : MEqRedPreservesWfM)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  Theorem_5_DeBruijn_Preservation_of_chain_shape_meq_components_and_direct_sub_replace
    hSubst (Theorem_3_DeBruijn_AbsFunctionBoundChainShapePayload_of hcomm)
    hMEqPres hSubPayloads hwf hstep

/-- De Bruijn preservation with Theorem 3's strong-commutativity payload
already consumed, and with top-level `.sub` replacement factored into
immediate and preserved-head residual packages. -/
noncomputable def
    Theorem_5_DeBruijn_Preservation_of_comm_meq_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ [])
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
  Theorem_5_DeBruijn_Preservation_of_chain_shape_meq_components_and_immediate_sub_replace_and_under
    hSubst (Theorem_3_DeBruijn_AbsFunctionBoundChainShapePayload_of hcomm)
    hMEqPres hUnder hSubPayloads hwf hstep

/-- Closed-term specialization of the strong-commutativity-driven de Bruijn
preservation surface over the direct `.sub` replacement residual package. -/
noncomputable def
    Theorem_5_DeBruijn_ClosedPreservation_of_comm_meq_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ [])
    (hMEqPres : MEqRedPreservesWfM)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_ClosedPreservation_of_chain_shape_meq_components_and_direct_sub_replace
    hSubst (Theorem_3_DeBruijn_AbsFunctionBoundChainShapePayload_of hcomm)
    hMEqPres hSubPayloads hwf hstep

/-- Closed-term specialization of the strong-commutativity-driven de Bruijn
preservation surface over immediate plus preserved-head `.sub` replacement
residuals. -/
noncomputable def
    Theorem_5_DeBruijn_ClosedPreservation_of_comm_meq_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ [])
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
  Theorem_5_DeBruijn_ClosedPreservation_of_chain_shape_meq_components_and_immediate_sub_replace_and_under
    hSubst (Theorem_3_DeBruijn_AbsFunctionBoundChainShapePayload_of hcomm)
    hMEqPres hUnder hSubPayloads hwf hstep

/-- De Bruijn preservation under `WfCtxEqu`, conditional on operational
well-formedness preservation under the same invariant. This avoids requiring
global empty-stack equivalence preservation in contexts where the machine-state
route already supplies the stronger context invariant. -/
noncomputable def Theorem_5_DeBruijn_Preservation_under_wfctx_of
    (hStepPres : StepPreservesWfMUnderWfCtx)
    {Γ : Ctx} {t t' u : Term}
    (hΓ : WfCtxEqu Γ)
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u := by
  have hwfT : WfM Γ t := hwf.wf_left
  have hwfT' : WfM Γ t' := hStepPres hΓ hstep hwfT
  have hBack : WSubMStar Γ t' t :=
    WSubMStar.of_StepAt_back hstep hwfT hwfT'
  exact WSubMStar.trans hwfT hBack hwf

/-- Closed-term specialization of the `WfCtxEqu`-parametric de Bruijn
preservation theorem. -/
noncomputable def Theorem_5_DeBruijn_ClosedPreservation_under_wfctx_of
    (hStepPres : StepPreservesWfMUnderWfCtx)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_Preservation_under_wfctx_of hStepPres
    WfCtxEqu.empty hwf hstep

/-- `WfCtxEqu`-parametric de Bruijn preservation with Theorem 3's
strong-commutativity payload consumed, joined-bound well-formedness supplied
by machine-state preservation, and direct `.sub` replacement residuals. -/
noncomputable def
    Theorem_5_DeBruijn_Preservation_under_wfctx_of_comm_machine_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ [])
    (hMachine : MEqRedPreservesWfMachineState)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    {Γ : Ctx} {t t' u : Term}
    (hΓ : WfCtxEqu Γ)
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  let hShape : AbsFunctionBoundChainShapePayload :=
    Theorem_3_DeBruijn_AbsFunctionBoundChainShapePayload_of hcomm
  let hInv : AbsFunctionBoundInversionUnderWfCtx :=
    AbsFunctionBoundInversionUnderWfCtx_of_chain_shape_machine_state
    hShape hMachine
  Theorem_5_DeBruijn_Preservation_under_wfctx_of
    (StepPreservesWfMUnderWfCtx_of_components_and_direct_sub_replace
      hSubst hInv hSubPayloads)
    hΓ hwf hstep

/-- `WfCtxEqu`-parametric de Bruijn preservation with Theorem 3's
strong-commutativity payload consumed, joined-bound well-formedness supplied
by machine-state preservation, and immediate plus preserved-head `.sub`
replacement residuals. -/
noncomputable def
    Theorem_5_DeBruijn_Preservation_under_wfctx_of_comm_machine_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ [])
    (hMachine : MEqRedPreservesWfMachineState)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    {Γ : Ctx} {t t' u : Term}
    (hΓ : WfCtxEqu Γ)
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  let hShape : AbsFunctionBoundChainShapePayload :=
    Theorem_3_DeBruijn_AbsFunctionBoundChainShapePayload_of hcomm
  let hInv : AbsFunctionBoundInversionUnderWfCtx :=
    AbsFunctionBoundInversionUnderWfCtx_of_chain_shape_machine_state
    hShape hMachine
  Theorem_5_DeBruijn_Preservation_under_wfctx_of
    (StepPreservesWfMUnderWfCtx_of_components_and_immediate_sub_replace_and_under
      hSubst hInv hUnder hSubPayloads)
    hΓ hwf hstep

/-- Closed-term specialization of the machine-state driven direct `.sub`
replacement theorem surface. -/
noncomputable def
    Theorem_5_DeBruijn_ClosedPreservation_under_wfctx_of_comm_machine_components_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ [])
    (hMachine : MEqRedPreservesWfMachineState)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_Preservation_under_wfctx_of_comm_machine_components_and_direct_sub_replace
    hSubst hcomm hMachine hSubPayloads WfCtxEqu.empty hwf hstep

/-- Closed-term specialization of the machine-state driven immediate plus
preserved-head `.sub` replacement theorem surface. -/
noncomputable def
    Theorem_5_DeBruijn_ClosedPreservation_under_wfctx_of_comm_machine_components_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ [])
    (hMachine : MEqRedPreservesWfMachineState)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_Preservation_under_wfctx_of_comm_machine_components_and_immediate_sub_replace_and_under
    hSubst hcomm hMachine hUnder hSubPayloads WfCtxEqu.empty hwf hstep

/-- `WfCtxEqu`-parametric de Bruijn preservation with the machine-state
premise assembled from the no-external-empty, body-transport, factored
machine-operator route. This exposes the remaining machine preservation
frontier directly at the Theorem 5 surface. -/
noncomputable def
    Theorem_5_DeBruijn_Preservation_under_wfctx_of_comm_body_transports_no_empty_factored_machine_operator_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ [])
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt)
    {Γ : Ctx} {t t' u : Term}
    (hΓ : WfCtxEqu Γ)
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  let hShape : AbsFunctionBoundChainShapePayload :=
    Theorem_3_DeBruijn_AbsFunctionBoundChainShapePayload_of hcomm
  let hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape :=
    AbsFunctionBoundChainShapeWfUnderWfCtxPayload_of_meq hShape hEmpty
  let hReplace : WfMSubHeadReplaceOfNewWf :=
    WfMSubHeadReplaceOfNewWf.of_direct_payloads hSubPayloads
  let hMachine : MEqRedPreservesWfMachineState :=
    MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_machine_operator_machine_tail
      hSubst hEqBody hSubBody hPres hStep hShape hShapeWf hLeft
      hSubToEqu hEquToSub hOpFun hTail hReplace hNoTop
  Theorem_5_DeBruijn_Preservation_under_wfctx_of_comm_machine_components_and_direct_sub_replace
    hSubst hcomm hMachine hSubPayloads hΓ hwf hstep

/-- Immediate plus preserved-head `.sub` replacement variant of the
body-transport, no-external-empty, factored machine-operator Theorem 5
surface. -/
noncomputable def
    Theorem_5_DeBruijn_Preservation_under_wfctx_of_comm_body_transports_no_empty_factored_machine_operator_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ [])
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt)
    {Γ : Ctx} {t t' u : Term}
    (hΓ : WfCtxEqu Γ)
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u :=
  let hShape : AbsFunctionBoundChainShapePayload :=
    Theorem_3_DeBruijn_AbsFunctionBoundChainShapePayload_of hcomm
  let hShapeWf : AbsFunctionBoundChainShapeWfUnderWfCtxPayload hShape :=
    AbsFunctionBoundChainShapeWfUnderWfCtxPayload_of_meq hShape hEmpty
  let hReplace : WfMSubHeadReplaceOfNewWf :=
    WfMSubHeadReplaceOfNewWf.of_immediate_payloads_and_under
      hUnder hSubPayloads
  let hMachine : MEqRedPreservesWfMachineState :=
    MEqRedPreservesWfMachineState.of_body_transports_no_empty_and_direct_split_beta_chain_shape_wfctx_factored_machine_operator_machine_tail
      hSubst hEqBody hSubBody hPres hStep hShape hShapeWf hLeft
      hSubToEqu hEquToSub hOpFun hTail hReplace hNoTop
  Theorem_5_DeBruijn_Preservation_under_wfctx_of_comm_machine_components_and_immediate_sub_replace_and_under
    hSubst hcomm hMachine hUnder hSubPayloads hΓ hwf hstep

/-- Closed-context specialization of the body-transport, no-external-empty,
factored machine-operator direct `.sub` replacement Theorem 5 surface. -/
noncomputable def
    Theorem_5_DeBruijn_ClosedPreservation_under_wfctx_of_comm_body_transports_no_empty_factored_machine_operator_and_direct_sub_replace
    (hSubst : BetaInstantiationPreservesWfM)
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ [])
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_Preservation_under_wfctx_of_comm_body_transports_no_empty_factored_machine_operator_and_direct_sub_replace
    hSubst hcomm hEmpty hEqBody hSubBody hPres hStep hLeft hSubToEqu hEquToSub
    hOpFun hTail hSubPayloads hNoTop WfCtxEqu.empty hwf hstep

/-- Closed-context specialization of the body-transport, no-external-empty,
factored machine-operator immediate plus preserved-head `.sub` replacement
Theorem 5 surface. -/
noncomputable def
    Theorem_5_DeBruijn_ClosedPreservation_under_wfctx_of_comm_body_transports_no_empty_factored_machine_operator_and_immediate_sub_replace_and_under
    (hSubst : BetaInstantiationPreservesWfM)
    (hcomm : ∀ {Γ : Ctx}, StrongCommutes Γ [])
    (hEmpty : MEqRedPreservesWfMUnderWfCtx)
    (hEqBody : MEqRedSubHeadToEquHeadPayload)
    (hSubBody : MSubRedSubHeadToEquHeadAsMEqPayload)
    (hPres : MSubPreservesWfMPayload)
    (hStep : MSubToWSubMStarPayload)
    (hLeft : MEqRedStackPreservesWSubMStarLeft)
    (hSubToEqu : WfMSubHeadToEquHeadPayload)
    (hEquToSub : WfMEquHeadToSubHeadPayload)
    (hOpFun : MEqRedAppFunctionSupertypeMachinePayload)
    (hTail : MEqRedMachineTailStepPreservesPayload)
    (hUnder : WfMSubUnderHeadReplaceOfNewWf)
    (hSubPayloads : ∀ {Γ : Ctx} {old new : Term},
      MEqRed Γ [] old new →
        WfM Γ new →
          WfMSubHeadReplaceImmediateDirectPayloads Γ old new)
    (hNoTop : NoTopFunctionSupertypesAt)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_Preservation_under_wfctx_of_comm_body_transports_no_empty_factored_machine_operator_and_immediate_sub_replace_and_under
    hSubst hcomm hEmpty hEqBody hSubBody hPres hStep hLeft hSubToEqu hEquToSub
    hOpFun hTail hUnder hSubPayloads hNoTop WfCtxEqu.empty hwf hstep

/-! ## Argument-transport lemma (Path 3, restricted form)

The `bet × bet` diamond cell needs to bridge two β-fires that disagree on the
post-step argument: one β fires with the original `arg`, the other with the
post-step `arg'`. The bridge takes the form

  `MEqRedStar Γ s (instantiate 0 arg body) (instantiate 0 arg' body)`,

asking to step from a body-instantiated-by-`arg` reduct to one
body-instantiated-by-`arg'`, at any prevalid stack.

**The wall.** A direct attack via `MEqRed Γ [] arg arg'` walls at
`body = .bvar 0`: both sides reduce to `arg` and `arg'` respectively, and we
need `MEqRedStar Γ s arg arg'`. When `s` is non-empty and `arg` is
abstraction-rooted, the `MEqRed` step **cannot lift** to non-empty stack
because `Me-Fun` requires empty stack and `Me-FOp` requires a specific
operand-shaped stack head. This is the **stack-extension wall** documented
across the de Bruijn refactor: `MEqRedStackAppendPayload.of_fun` shows that
the only outstanding case in the lift induction is precisely the `Me-Fun`
case.

**Restricted form shipped here.** We package the wall as an explicit
**precondition**: the caller must supply a chain
`MEqRedStar Γ s' arg arg'` at every prevalid stack `s'` they might encounter.
For non-abstraction `arg` this lifts trivially via stack-append (because
`MEqRedStar Γ s arg arg'` decomposes into constructors that all admit stack
extension); for abstraction `arg` the caller must produce the lift externally
or arrange for the relevant stacks to be empty.

This is the closest provable surface short of solving the general lift
problem. The downstream `bet × bet` cell composes this with the body-side
`MEqRedFusedKindNarrowedBetaSubstStack_proved` and an outer chain.

**Wall analysis for an unconditional version.** The genuine obstruction is
at `body = .bvar 0`, stack non-empty, `arg` abstraction-rooted. There is no
known workaround at the de Bruijn level: the substituted `bvar 0` must
literally become `arg`, which has the wrong abstraction shape for the
ambient stack. The restricted form is therefore not a stop-gap — it is the
form the lemma admits at this encoding. -/

/-- Single-step equivalence-reduction congruence at the operator (function)
position of an application. The operator step lives at the stack with the
operand pushed on top, so `Me-App` directly applies. -/
noncomputable def MEqRed.app_left {Γ : Ctx} {s : Stack} {u u' v : Term}
    (hStep : MEqRed Γ (v :: s) u u')
    (hv : Term.Scoped Γ.depth v) : MEqRed Γ s (.app u v) (.app u' v) :=
  MEqRed.app hStep
    (MEqRed.refl (PrevalidExt.nil hStep.prevalid) hv)

/-- Chain-level operator-position congruence: a chain of operator-position
equivalence steps lifts to a chain of `Me-App` steps, leaving the operand
untouched. -/
theorem MEqRedStar.app_left {Γ : Ctx} {s : Stack} {u u' v : Term}
    (hStar : MEqRedStar Γ (v :: s) u u')
    (hv : Term.Scoped Γ.depth v) :
    MEqRedStar Γ s (.app u v) (.app u' v) := by
  induction hStar with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _hPrefix hStep ih =>
      exact Relation.ReflTransGen.tail ih
        ⟨MEqRed.app_left hStep.some hv⟩

/-- Single-step equivalence-reduction congruence at the operand (argument)
position of an application. The operand step lives at the empty stack and
is pushed into the application via `Me-App`'s operand premise; the operator
position uses reflexivity at the appropriate stack. -/
noncomputable def MEqRed.app_right {Γ : Ctx} {s : Stack} {u v v' : Term}
    (hu : Term.Scoped Γ.depth u)
    (hStep : MEqRed Γ [] v v')
    (hpv : PrevalidExt Γ s) :
    MEqRed Γ s (.app u v) (.app u v') := by
  have hv : Term.Scoped Γ.depth v := hStep.scoped_left
  have hpvOp : PrevalidExt Γ (v :: s) := PrevalidExt.cons hpv hv
  exact MEqRed.app (MEqRed.refl hpvOp hu) hStep

/-- Chain-level operand-position congruence: a chain of operand-position
equivalence steps lifts to a chain of `Me-App` steps, leaving the operator
untouched but advancing the operand. -/
theorem MEqRedStar.app_right {Γ : Ctx} {s : Stack} {u v v' : Term}
    (hu : Term.Scoped Γ.depth u)
    (hStar : MEqRedStar Γ [] v v')
    (hpv : PrevalidExt Γ s) :
    MEqRedStar Γ s (.app u v) (.app u v') := by
  induction hStar with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _hPrefix hStep ih =>
      exact Relation.ReflTransGen.tail ih
        ⟨MEqRed.app_right hu hStep.some hpv⟩

/-- Predicate: a term has no `.abs` constructor anywhere along its
structural spine (top-level only, so applications can have abstractions
inside their subterms — but the term being instantiated is not directly
an abstraction at the top of any of its app-spine positions).

Concretely: `top`/`bvar` are abs-free; `app f x` is abs-free iff both `f`
and `x` are; `abs _ _` is never abs-free. This precisely characterizes the
sublanguage that the index-0 restricted argument-transport lemma covers.

The body case where `body = .abs bound innerBody` is excluded because the
recursion under the binder would require an index-1 instantiation lemma,
which the index-0 surface does not supply. -/
inductive Term.AbsFree : Term → Prop
  | bvar (i : Nat) : Term.AbsFree (.bvar i)
  | top : Term.AbsFree .top
  | app {f x : Term} : Term.AbsFree f → Term.AbsFree x →
      Term.AbsFree (.app f x)

/-- Argument-transport lemma in **restricted form**: when the argument step
already lifts to a chain at every prevalid stack and the body is abs-free,
the chain transports through the body's instantiation by induction on body
shape.

**Two restrictions:**

1. **Argument-side lift.** The wall is at `body = .bvar 0` with non-empty
   stack: there we need `MEqRedStar Γ s arg arg'`, which the caller supplies
   via `hLift`. Non-abstraction `arg`s admit `hLift` trivially via
   stack-append; abstraction `arg`s require an external supply or
   arrangement that the relevant stacks are empty.

2. **Body-side abs-freedom.** The body case `body = .abs bound innerBody`
   would require recursion at index 1 (the innerBody substitution becomes
   `instantiate 1 (shift 0 arg) innerBody`), which the index-0 IH cannot
   supply directly. The generalized under-heads form (analogous to
   `MEqRedRespectsBetaInstantiateUnderHeadsStack`) would discharge this,
   but at substantially more proof complexity. The abs-free restriction
   captures the sublanguage where the lemma closes cleanly.

The downstream `bet × bet` cell can use this for body shapes that are
abs-free at the top level, composing with the body-side
`MEqRedFusedKindNarrowedBetaSubstStack_proved` for the abs-shaped
subderivations. -/
noncomputable def MEqRedStar.argTransportRestricted
    {Γ : Ctx} {arg arg' body : Term} {s : Stack}
    (hBody : Term.Scoped (Γ.depth + 1) body)
    (hAbsFree : Term.AbsFree body)
    (hArg : Term.Scoped Γ.depth arg)
    (hArg' : Term.Scoped Γ.depth arg')
    (hpv : PrevalidExt Γ s)
    (hLift : ∀ {s' : Stack}, PrevalidExt Γ s' →
      MEqRedStar Γ s' arg arg') :
    MEqRedStar Γ s
      (Term.instantiate 0 arg body) (Term.instantiate 0 arg' body) := by
  induction body generalizing s with
  | bvar i =>
      have hi : i < Γ.depth + 1 := hBody.bvar_lt
      by_cases heq : i = 0
      · subst heq
        simpa [Term.instantiate] using hLift hpv
      · -- i ≥ 1; both sides reduce to .bvar (i - 1); chain is refl
        have hnotlt : ¬ i < 0 := Nat.not_lt_zero _
        simp [Term.instantiate, hnotlt, heq]
        exact Relation.ReflTransGen.refl
  | top =>
      simpa [Term.instantiate] using
        (Relation.ReflTransGen.refl :
          MEqRedStar Γ s .top .top)
  | app f x ihF ihX =>
      have ⟨hF, hX⟩ : Term.Scoped (Γ.depth + 1) f ×
          Term.Scoped (Γ.depth + 1) x := Term.Scoped.app_inv hBody
      have hAbsFreeF : Term.AbsFree f := by
        cases hAbsFree with | app hf _ => exact hf
      have hAbsFreeX : Term.AbsFree x := by
        cases hAbsFree with | app _ hx => exact hx
      have hFInst' : Term.Scoped Γ.depth (Term.instantiate 0 arg' f) :=
        Term.instantiate_scoped 0 Γ.depth arg' f (Nat.zero_le _) hArg' hF
      have hXInst : Term.Scoped Γ.depth (Term.instantiate 0 arg x) :=
        Term.instantiate_scoped 0 Γ.depth arg x (Nat.zero_le _) hArg hX
      -- IH on operator at extended stack: chain of operator-position changes
      have hpvOp : PrevalidExt Γ (Term.instantiate 0 arg x :: s) :=
        PrevalidExt.cons hpv hXInst
      have hOpStar :
          MEqRedStar Γ (Term.instantiate 0 arg x :: s)
            (Term.instantiate 0 arg f) (Term.instantiate 0 arg' f) :=
        ihF hF hAbsFreeF hpvOp
      -- IH on operand at empty stack: chain of operand-position changes
      have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil (PrevalidExt.ctx hpv)
      have hArgStar :
          MEqRedStar Γ []
            (Term.instantiate 0 arg x) (Term.instantiate 0 arg' x) :=
        ihX hX hAbsFreeX hpvNil
      -- Compose: first move operator at extended stack, then move operand
      have hStarOp :
          MEqRedStar Γ s
            (.app (Term.instantiate 0 arg f) (Term.instantiate 0 arg x))
            (.app (Term.instantiate 0 arg' f) (Term.instantiate 0 arg x)) :=
        MEqRedStar.app_left hOpStar hXInst
      have hStarArg :
          MEqRedStar Γ s
            (.app (Term.instantiate 0 arg' f) (Term.instantiate 0 arg x))
            (.app (Term.instantiate 0 arg' f) (Term.instantiate 0 arg' x)) :=
        MEqRedStar.app_right hFInst' hArgStar hpv
      simpa [Term.instantiate] using
        Relation.ReflTransGen.trans hStarOp hStarArg
  | abs bound innerBody _ihBound _ihInner =>
      -- Excluded by `Term.AbsFree`: the abstraction case requires recursion
      -- at depth 1, which the index-0 form does not supply. See the lemma
      -- docstring for the wall analysis.
      exact (by cases hAbsFree)

/-- Statement of the restricted argument-transport surface. The body is
required to be abs-free (top-level, with abstractions allowed only inside
applications' subterms — see `Term.AbsFree`), and the caller supplies the
argument-side stack lift via `hLift`. The conclusion lives in `Prop`
because `MEqRedStar` does. -/
def MEqRedStarArgTransportRestricted : Prop :=
  ∀ {Γ : Ctx} {arg arg' body : Term} {s : Stack},
    Term.Scoped (Γ.depth + 1) body →
      Term.AbsFree body →
        Term.Scoped Γ.depth arg →
          Term.Scoped Γ.depth arg' →
            PrevalidExt Γ s →
              (∀ {s' : Stack}, PrevalidExt Γ s' →
                MEqRedStar Γ s' arg arg') →
                MEqRedStar Γ s
                  (Term.instantiate 0 arg body)
                  (Term.instantiate 0 arg' body)

/-- Closed proof of the restricted argument-transport surface. -/
theorem MEqRedStarArgTransportRestricted_proved :
    MEqRedStarArgTransportRestricted := by
  intro Γ arg arg' body s hBody hAbsFree hArg hArg' hpv hLift
  exact MEqRedStar.argTransportRestricted hBody hAbsFree hArg hArg' hpv hLift

/-! ## Restricted argument-side stack lift via `Term.NoBinders`

The `argTransportRestricted` surface above is parameterized by a caller-
supplied lift `hLift : ∀ s', PrevalidExt Γ s' → MEqRedStar Γ s' arg arg'`.
For abstraction `arg` this lift cannot be discharged at the de Bruijn level
(the wall analyzed in the docstring above the lemma). For non-abstraction
`arg` the prompt envisioned a structural discharge inducting on `MEqRed`
with `Term.AbsFree arg` excluding the `fun_` constructor.

That structural discharge **walls at the `pro` constructor**: when the
single step is `MEqRed.pro hpv hb hred` from source `.bvar i` to target `α'`,
rebuilding the step at a new stack `s_new` requires lifting the inner
`hred : MEqRed Γ [] α α'` to `MEqRed Γ s_new α α'`, where `α` (the equ-
binding) need not be `AbsFree`. Iteratively recursing on the inner
derivation hits the `fun_` case if `α = .abs t body`, which is precisely
the wall of `MEqRedFunStackAppendPayload` (open since the syntax pivot).

The provable strict restriction excludes both `.bvar` and `.abs` from
source `arg`: with no bvar source, `pro` and `var` are excluded, and with
no abstraction source, `bet`, `fun_`, `fOp` are excluded. Only `top`,
`tAp`, `app` remain — all admit direct stack rebuild.

The predicate `Term.NoBinders` captures exactly this sublanguage, and the
`MEqRedStar.lift_to_any_stack_of_NoBinders` helper provides the required
`hLift` from a single-step `MEqRed Γ [] arg arg'` with `NoBinders arg`.
The `bet × bet` cell consequently closes for the strict shape combination
`Term.AbsFree body ∧ Term.NoBinders arg` (with `NoBinders` understood as
the `arg`-restriction stronger than the body's `AbsFree`). -/

/-- A term has no binder constructs (`.bvar` or `.abs`) anywhere in its
structural tree. The defined cases are `.top` and `.app` (recursive on
both subterms). This is strictly stronger than `Term.AbsFree` (which
permits `.bvar` and abstractions inside `.app` subterms) and is the
precise sublanguage on which de Bruijn `MEqRed` admits a structural
stack-lift to an arbitrary prevalid stack. -/
inductive Term.NoBinders : Term → Prop
  | top : Term.NoBinders .top
  | app {f x : Term} : Term.NoBinders f → Term.NoBinders x →
      Term.NoBinders (.app f x)

/-- `Term.NoBinders` is preserved under the structural decomposition of
applications. -/
theorem Term.NoBinders.app_inv {f x : Term}
    (h : Term.NoBinders (.app f x)) :
    Term.NoBinders f ∧ Term.NoBinders x := by
  cases h with
  | app hf hx => exact ⟨hf, hx⟩

/-- Stack lift for a single de Bruijn equivalence-reduction step from any
stack `s_old` to any prevalid stack `s_new`, restricted to `NoBinders`
sources.

Inducts on the `MEqRed` derivation. The constructor cases:
- `pro`/`var`: source is `.bvar i`, excluded by `NoBinders`.
- `bet`: source is `.app (.abs ..) v`, the `.abs` factor excluded.
- `fun_`/`fOp`: source is `.abs ..`, excluded.
- `top`: rebuild at `s_new` via `MEqRed.top` of the new prevalidity.
- `tAp`: rebuild at `s_new` via `MEqRed.tAp` of the new prevalidity and
  the (preserved) operand scoping.
- `app`: induct on the operator at the operand-pushed new stack and the
  operand at the empty new stack, then recombine via the chain-level
  `app_left`/`app_right` congruences.

The output is a chain (`MEqRedStar`) rather than a single step because
the `app` case combines two sub-chains via transitivity. The `top`/`tAp`
cases would alone admit a single-step output but the unified statement
returns the chain form. -/
theorem MEqRedStar.lift_to_any_stack_of_NoBinders
    {Γ : Ctx} {arg arg' : Term} :
    ∀ {s_old s_new : Stack},
      MEqRed Γ s_old arg arg' →
      Term.NoBinders arg →
      PrevalidExt Γ s_new →
      MEqRedStar Γ s_new arg arg' := by
  intro s_old s_new hStep hNoBinders hpv
  induction hStep generalizing s_new with
  | pro _ _ _ _ =>
      -- Source is `.bvar i`, excluded by `Term.NoBinders`.
      cases hNoBinders
  | @bet Γp sp t v v' body body' _ _ _ _ _ =>
      -- Source is `.app (.abs t body) v`; the `.abs t body` factor is
      -- excluded by `Term.NoBinders.app`'s left premise.
      have ⟨hAbs, _hV⟩ := hNoBinders.app_inv
      cases hAbs
  | top _ =>
      exact MEqRedStar.single (MEqRed.top hpv)
  | @app Γp sp u u' v v' hOp hArg ihOp ihArg =>
      -- Source `.app u v`: NoBinders gives both `u` and `v` NoBinders.
      have ⟨hNoBindersU, hNoBindersV⟩ := hNoBinders.app_inv
      -- Operator advance: from `MEqRed Γ (v :: s_old) u u'` to chain at
      -- `v :: s_new`.
      have hVScoped : Term.Scoped Γp.depth v := hArg.scoped_left
      have hpvOp : PrevalidExt Γp (v :: s_new) := PrevalidExt.cons hpv hVScoped
      have hOpStar : MEqRedStar Γp (v :: s_new) u u' :=
        ihOp hNoBindersU hpvOp
      have hStarOp :
          MEqRedStar Γp s_new (.app u v) (.app u' v) :=
        MEqRedStar.app_left hOpStar hVScoped
      -- Operand advance: from `MEqRed Γ [] v v'` to chain at `[]`, then
      -- push back to `s_new` via app_right (which keeps the operand step
      -- empty-stack but rebuilds the application at any stack).
      have hpvNil : PrevalidExt Γp [] := PrevalidExt.nil (PrevalidExt.ctx hpv)
      have hArgStar : MEqRedStar Γp [] v v' :=
        ihArg hNoBindersV hpvNil
      -- Right scoping of `u'` from the original operator subderivation.
      have hUtgtScoped : Term.Scoped Γp.depth u' := hOp.scoped_right
      have hStarArg :
          MEqRedStar Γp s_new (.app u' v) (.app u' v') :=
        MEqRedStar.app_right hUtgtScoped hArgStar hpv
      exact Relation.ReflTransGen.trans hStarOp hStarArg
  | var _ _ =>
      -- Source `.bvar i`, excluded by NoBinders.
      cases hNoBinders
  | fun_ _ _ _ _ =>
      -- Source `.abs t body`, excluded by NoBinders (no `Term.NoBinders.abs`).
      cases hNoBinders
  | tAp _ hu =>
      exact MEqRedStar.single (MEqRed.tAp hpv hu)
  | fOp _ _ _ _ _ =>
      -- Source `.abs t body`, excluded by NoBinders.
      cases hNoBinders

/-- `Term.NoBinders` immediately implies `Term.AbsFree`: the predicates
agree on `.top` and `.app` cases, and `NoBinders` rules out `.bvar` and
`.abs` (the only point of disagreement, where `AbsFree` allows `.bvar` and
`.abs`-in-app-subterm but `NoBinders` rules them all out). -/
theorem Term.NoBinders.absFree {t : Term} :
    Term.NoBinders t → Term.AbsFree t := by
  intro h
  induction h with
  | top => exact Term.AbsFree.top
  | app _ _ ihF ihX => exact Term.AbsFree.app ihF ihX

/-- `NoBinders` terms are scoped at every depth, in `Nonempty` form to stay
within Prop elimination. -/
theorem Term.NoBinders.scoped_nonempty {t : Term} (h : Term.NoBinders t)
    (depth : Nat) : Nonempty (Term.Scoped depth t) := by
  induction h with
  | top => exact ⟨Term.Scoped.top⟩
  | app _ _ ihF ihX =>
      exact ⟨Term.Scoped.app ihF.some ihX.some⟩

/-- Shifting leaves `NoBinders` terms unchanged. -/
theorem Term.NoBinders.shiftBy_eq {t : Term} (h : Term.NoBinders t)
    (cutoff amount : Nat) :
    Term.shiftBy cutoff amount t = t := by
  induction h generalizing cutoff amount with
  | top =>
      simp [Term.shiftBy]
  | app _ _ ihF ihX =>
      simp [Term.shiftBy, ihF cutoff amount, ihX cutoff amount]

/-- Restricted argument-transport payload: a strictly stronger form of
`MEqRedArgTransportPayload` with `Term.AbsFree body` and `Term.NoBinders
arg` premises added. The body's abs-freedom is needed for the index-0
instantiation lemma to recurse cleanly under the body shape; the arg's
binder-freedom enables the structural stack lift required at the
`body = .bvar 0` case (the only spot the original payload uses the
chain-output of the argument step). -/
def MEqRedArgTransportPayloadRestricted : Prop :=
  ∀ {Γ : Ctx} {arg arg' body : Term} {s : Stack},
    Term.Scoped (Γ.depth + 1) body →
    Term.AbsFree body →
    Term.NoBinders arg →
    MEqRed Γ [] arg arg' →
    PrevalidExt Γ s →
    MEqRedStar Γ s
      (Term.instantiate 0 arg body)
      (Term.instantiate 0 arg' body)

/-- Closed proof of the restricted argument-transport payload, composing
the restricted argument-transport surface (`argTransportRestricted`) with
the structural stack lift for `NoBinders` argument shapes. -/
theorem MEqRedArgTransportPayloadRestricted_proved :
    MEqRedArgTransportPayloadRestricted := by
  intro Γ arg arg' body s hBody hAbsFreeBody hNoBindersArg hArgStep hpv
  have hArgScoped : Term.Scoped Γ.depth arg := hArgStep.scoped_left
  have hArgScoped' : Term.Scoped Γ.depth arg' := hArgStep.scoped_right
  have hLift : ∀ {s' : Stack}, PrevalidExt Γ s' →
      MEqRedStar Γ s' arg arg' := fun hpv' =>
    MEqRedStar.lift_to_any_stack_of_NoBinders hArgStep hNoBindersArg hpv'
  exact MEqRedStar.argTransportRestricted hBody hAbsFreeBody hArgScoped
    hArgScoped' hpv hLift

/-- `Term.NoBinders` is preserved under a single de Bruijn equivalence-
reduction step. The constructor cases `pro`, `var`, `bet`, `fun_`, `fOp`
have sources excluded by `NoBinders`; the remaining `top`, `tAp`, `app`
cases produce `NoBinders` targets directly (`top`/`tAp` go to `.top`,
`app` recurses).

Notice this preservation is **single-step on the source**, not on the
target — that is, `NoBinders` flows from the source to the target through
the constructor structure, with no use of the inverse direction. -/
theorem MEqRed.preserves_noBinders {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) (hu : Term.NoBinders u) : Term.NoBinders v := by
  induction h with
  | pro _ _ _ _ =>
      cases hu
  | bet _ _ _ _ _ =>
      have ⟨hAbs, _⟩ := hu.app_inv
      cases hAbs
  | top _ =>
      exact Term.NoBinders.top
  | @app Γp sp u u' v v' _ _ ihOp ihArg =>
      have ⟨hOpNoBinders, hArgNoBinders⟩ := hu.app_inv
      exact Term.NoBinders.app (ihOp hOpNoBinders) (ihArg hArgNoBinders)
  | var _ _ =>
      cases hu
  | fun_ _ _ _ _ =>
      cases hu
  | tAp _ _ =>
      exact Term.NoBinders.top
  | fOp _ _ _ _ _ =>
      cases hu

/-- `Term.NoBinders` preservation lifted to the `Prop`-wrapped reduction. -/
theorem MEqRedJ.preserves_noBinders {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRedJ Γ s u v) (hu : Term.NoBinders u) : Term.NoBinders v :=
  h.some.preserves_noBinders hu

/-- `Term.NoBinders` preservation lifted to equivalence-reduction chains. -/
theorem MEqRedStar.preserves_noBinders {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRedStar Γ s u v) (hu : Term.NoBinders u) : Term.NoBinders v := by
  induction h with
  | refl => exact hu
  | tail _ hStep ih => exact hStep.some.preserves_noBinders ih

/-- `Term.NoBinders` is preserved under a single de Bruijn subtype-reduction
step. This is similar to the equivalence-reduction preservation lemma, except
`Ms-Top` can target `.top` from any scoped source. -/
theorem MSubRed.preserves_noBinders {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRed Γ s u v) (hu : Term.NoBinders u) : Term.NoBinders v := by
  induction h with
  | pro _ _ =>
      cases hu
  | top _ _ =>
      exact Term.NoBinders.top
  | equ _ hEq =>
      exact hEq.preserves_noBinders hu
  | @app Γp sp u u' v _ _ ih =>
      have ⟨hOpNoBinders, hArgNoBinders⟩ := hu.app_inv
      exact Term.NoBinders.app (ih hOpNoBinders) hArgNoBinders
  | fun_ _ _ _ _ =>
      cases hu
  | fOp _ _ _ _ =>
      cases hu

/-- `Term.NoBinders` preservation lifted to the Prop-wrapped subtype
reduction. -/
theorem MSubRedJ.preserves_noBinders {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRedJ Γ s u v) (hu : Term.NoBinders u) : Term.NoBinders v :=
  h.some.preserves_noBinders hu

/-- `Term.NoBinders` preservation lifted to subtype-reduction chains. -/
theorem MSubRedStar.preserves_noBinders {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRedStar Γ s u v) (hu : Term.NoBinders u) :
    Term.NoBinders v := by
  induction h with
  | refl => exact hu
  | tail _ hStep ih => exact hStep.some.preserves_noBinders ih

/-- Single-step stack/context retargeting for de Bruijn equivalence
reduction, restricted to `NoBinders` sources.

This is stronger than the chain-valued retargeting below. The `NoBinders`
restriction excludes all stack/context-sensitive source constructors
(`pro`, `var`, `bet`, `fun_`, `fOp`), and the remaining constructors
(`top`, `tAp`, `app`) can be rebuilt as one step in the target context and
stack. -/
theorem MEqRed.lift_to_any_context_stack_of_NoBinders_nonempty
    {Γ_old Γ_new : Ctx} {arg arg' : Term} :
    ∀ {s_old s_new : Stack},
      MEqRed Γ_old s_old arg arg' →
      Term.NoBinders arg →
      PrevalidExt Γ_new s_new →
      Nonempty (MEqRed Γ_new s_new arg arg') := by
  intro s_old s_new hStep hNoBinders hpv
  induction hStep generalizing Γ_new s_new with
  | pro _ _ _ _ =>
      cases hNoBinders
  | @bet _ _ _ _ _ _ _ _ _ _ _ =>
      have ⟨hAbs, _hV⟩ := hNoBinders.app_inv
      cases hAbs
  | top _ =>
      exact ⟨MEqRed.top hpv⟩
  | @app Γp sp u u' v v' hOp hArg ihOp ihArg =>
      have ⟨hNoBindersU, hNoBindersV⟩ := hNoBinders.app_inv
      have hVScopedNew : Term.Scoped Γ_new.depth v :=
        (hNoBindersV.scoped_nonempty Γ_new.depth).some
      have hpvOp : PrevalidExt Γ_new (v :: s_new) :=
        PrevalidExt.cons hpv hVScopedNew
      have hOpNew : MEqRed Γ_new (v :: s_new) u u' :=
        (ihOp hNoBindersU hpvOp).some
      have hpvNil : PrevalidExt Γ_new [] :=
        PrevalidExt.nil (PrevalidExt.ctx hpv)
      have hArgNew : MEqRed Γ_new [] v v' :=
        (ihArg hNoBindersV hpvNil).some
      exact ⟨MEqRed.app hOpNew hArgNew⟩
  | var _ _ =>
      cases hNoBinders
  | fun_ _ _ _ _ =>
      cases hNoBinders
  | @tAp _ _ u _ _ =>
      have hArgNoBinders : Term.NoBinders u := hNoBinders.app_inv.2
      exact ⟨MEqRed.tAp hpv
        (hArgNoBinders.scoped_nonempty Γ_new.depth).some⟩
  | fOp _ _ _ _ _ =>
      cases hNoBinders

/-- Stack lift for a single de Bruijn equivalence-reduction step into any
prevalid target context and stack, restricted to `NoBinders` sources.

Compared with `MEqRedStar.lift_to_any_stack_of_NoBinders`, this also changes
the context. The restriction is what makes that sound: `NoBinders` excludes
the context-sensitive constructors (`pro`, `var`, `fun_`, `bet`, `fOp`),
leaving only `top`, `tAp`, and structural `app` steps, which can be rebuilt
from the target prevalidity and `NoBinders.scoped_nonempty`. -/
theorem MEqRedStar.lift_to_any_context_stack_of_NoBinders
    {Γ_old Γ_new : Ctx} {arg arg' : Term} :
    ∀ {s_old s_new : Stack},
      MEqRed Γ_old s_old arg arg' →
      Term.NoBinders arg →
      PrevalidExt Γ_new s_new →
      MEqRedStar Γ_new s_new arg arg' := by
  intro s_old s_new hStep hNoBinders hpv
  induction hStep generalizing Γ_new s_new with
  | pro _ _ _ _ =>
      cases hNoBinders
  | @bet _ _ _ _ _ _ _ _ _ _ _ =>
      have ⟨hAbs, _hV⟩ := hNoBinders.app_inv
      cases hAbs
  | top _ =>
      exact MEqRedStar.single (MEqRed.top hpv)
  | @app Γp sp u u' v v' hOp hArg ihOp ihArg =>
      have ⟨hNoBindersU, hNoBindersV⟩ := hNoBinders.app_inv
      have hVScopedNew : Term.Scoped Γ_new.depth v :=
        (hNoBindersV.scoped_nonempty Γ_new.depth).some
      have hpvOp : PrevalidExt Γ_new (v :: s_new) :=
        PrevalidExt.cons hpv hVScopedNew
      have hOpStar : MEqRedStar Γ_new (v :: s_new) u u' :=
        ihOp hNoBindersU hpvOp
      have hStarOp :
          MEqRedStar Γ_new s_new (.app u v) (.app u' v) :=
        MEqRedStar.app_left hOpStar hVScopedNew
      have hpvNil : PrevalidExt Γ_new [] :=
        PrevalidExt.nil (PrevalidExt.ctx hpv)
      have hArgStar : MEqRedStar Γ_new [] v v' :=
        ihArg hNoBindersV hpvNil
      have hUNoBinders' : Term.NoBinders u' :=
        hOp.preserves_noBinders hNoBindersU
      have hUScopedNew' : Term.Scoped Γ_new.depth u' :=
        (hUNoBinders'.scoped_nonempty Γ_new.depth).some
      have hStarArg :
          MEqRedStar Γ_new s_new (.app u' v) (.app u' v') :=
        MEqRedStar.app_right hUScopedNew' hArgStar hpv
      exact Relation.ReflTransGen.trans hStarOp hStarArg
  | var _ _ =>
      cases hNoBinders
  | fun_ _ _ _ _ =>
      cases hNoBinders
  | @tAp _ _ u _ _ =>
      have hArgNoBinders : Term.NoBinders u := hNoBinders.app_inv.2
      exact MEqRedStar.single
        (MEqRed.tAp hpv (hArgNoBinders.scoped_nonempty Γ_new.depth).some)
  | fOp _ _ _ _ _ =>
      cases hNoBinders

/-- Chain-level stack/context retargeting for de Bruijn equivalence
reduction, restricted to `NoBinders` sources. This lifts an entire
`MEqRedStar` chain into any prevalid target context and stack by retargeting
each single step and using `MEqRedStar.preserves_noBinders` to keep the
restriction available at intermediate sources. -/
theorem MEqRedStar.lift_chain_to_any_context_stack_of_NoBinders
    {Γ_old Γ_new : Ctx} {arg arg' : Term} {s_old s_new : Stack}
    (h : MEqRedStar Γ_old s_old arg arg')
    (hNoBinders : Term.NoBinders arg)
    (hpv : PrevalidExt Γ_new s_new) :
    MEqRedStar Γ_new s_new arg arg' := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | @tail mid target hChain hStep ih =>
      have hMidNoBinders : Term.NoBinders mid :=
        MEqRedStar.preserves_noBinders hChain hNoBinders
      have hStepNew : MEqRedStar Γ_new s_new mid target :=
        MEqRedStar.lift_to_any_context_stack_of_NoBinders
          hStep.some hMidNoBinders hpv
      exact Relation.ReflTransGen.trans ih hStepNew

/-- Scoped, binder-free `.equ`-head to `.sub`-head bridge. This is not the
general `MEqRedSubBridgePayload`: it is the provable sublanguage where the
body source cannot observe the head kind or annotation. -/
noncomputable def MEqRedSubBridgePayloadNoBinders_proved
    {Γ : Ctx} {t v body body' : Term} {s : Stack}
    (ht : Term.Scoped Γ.depth t)
    (hBodyNoBinders : Term.NoBinders body)
    (hBody :
      MEqRed ({bound := v, kind := .equ} :: Γ) (Stack.shift 0 s) body body') :
    MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body' := by
  have hpvOld : PrevalidExt ({bound := v, kind := .equ} :: Γ)
      (Stack.shift 0 s) := hBody.prevalidExt
  have hΓ : Prevalid Γ := Prevalid.tail (PrevalidExt.ctx hpvOld)
  have hPrevalidSub : Prevalid ({bound := t, kind := .sub} :: Γ) :=
    Prevalid.sub hΓ ht
  have hStackScoped : Stack.Scoped (Γ.depth + 1) (Stack.shift 0 s) :=
    PrevalidExt.stack_scoped hpvOld
  have hpvNew :
      PrevalidExt ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) :=
    PrevalidExt.of_stack_scoped hPrevalidSub (by
      simpa [Ctx.depth] using hStackScoped)
  exact (MEqRed.lift_to_any_context_stack_of_NoBinders_nonempty hBody
    hBodyNoBinders hpvNew).some

/-- Single-step stack/context retargeting for de Bruijn subtype reduction,
restricted to `NoBinders` sources.

Unlike the equivalence version, this does **not** convert subtype reduction
to equivalence reduction: the `Ms-Top` constructor remains a genuine
subtype-only step even when the source is binder-free. -/
theorem MSubRed.lift_to_any_context_stack_of_NoBinders_nonempty
    {Γ_old Γ_new : Ctx} {arg arg' : Term} :
    ∀ {s_old s_new : Stack},
      MSubRed Γ_old s_old arg arg' →
      Term.NoBinders arg →
      PrevalidExt Γ_new s_new →
      Nonempty (MSubRed Γ_new s_new arg arg') := by
  intro s_old s_new hStep hNoBinders hpv
  induction hStep generalizing Γ_new s_new with
  | pro _ _ =>
      cases hNoBinders
  | top _ _ =>
      exact ⟨MSubRed.top hpv
        (hNoBinders.scoped_nonempty Γ_new.depth).some⟩
  | @equ Γp sp u v hpvOld hEq =>
      have hEqNew : MEqRed Γ_new s_new u v :=
        (MEqRed.lift_to_any_context_stack_of_NoBinders_nonempty hEq
          hNoBinders hpv).some
      exact ⟨MSubRed.equ hpv hEqNew⟩
  | @app Γp sp u u' v hOp hVScoped ihOp =>
      have ⟨hNoBindersU, hNoBindersV⟩ := hNoBinders.app_inv
      have hVScopedNew : Term.Scoped Γ_new.depth v :=
        (hNoBindersV.scoped_nonempty Γ_new.depth).some
      have hpvOp : PrevalidExt Γ_new (v :: s_new) :=
        PrevalidExt.cons hpv hVScopedNew
      have hOpNew : MSubRed Γ_new (v :: s_new) u u' :=
        (ihOp hNoBindersU hpvOp).some
      exact ⟨MSubRed.app hOpNew hVScopedNew⟩
  | fun_ _ _ _ _ =>
      cases hNoBinders
  | fOp _ _ _ _ =>
      cases hNoBinders

/-- Chain-level stack/context retargeting for de Bruijn subtype reduction,
restricted to `NoBinders` sources. Each source along the chain remains
`NoBinders` by `MSubRedStar.preserves_noBinders`, so the single-step
retargeting lemma applies at every hop. -/
theorem MSubRedStar.lift_to_any_context_stack_of_NoBinders
    {Γ_old Γ_new : Ctx} {arg arg' : Term} {s_old s_new : Stack}
    (h : MSubRedStar Γ_old s_old arg arg')
    (hNoBinders : Term.NoBinders arg)
    (hpv : PrevalidExt Γ_new s_new) :
    MSubRedStar Γ_new s_new arg arg' := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | @tail mid target hChain hStep ih =>
      have hMidNoBinders : Term.NoBinders mid :=
        MSubRedStar.preserves_noBinders hChain hNoBinders
      have hStepNew : MSubRed Γ_new s_new mid target :=
        (MSubRed.lift_to_any_context_stack_of_NoBinders_nonempty
          hStep.some hMidNoBinders hpv).some
      exact Relation.ReflTransGen.trans ih
        (MSubRedStar.single hStepNew)

/-- Scoped, binder-free `.equ`-head to `.sub`-head bridge for subtype
reduction. This preserves the subtype-reduction judgment; it is not a
conversion to `MEqRed`. -/
noncomputable def MSubRedSubBridgePayloadNoBinders_proved
    {Γ : Ctx} {t v body body' : Term} {s : Stack}
    (ht : Term.Scoped Γ.depth t)
    (hBodyNoBinders : Term.NoBinders body)
    (hBody :
      MSubRed ({bound := v, kind := .equ} :: Γ) (Stack.shift 0 s) body body') :
    MSubRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body' := by
  have hpvOld : PrevalidExt ({bound := v, kind := .equ} :: Γ)
      (Stack.shift 0 s) := hBody.prevalidExt
  have hΓ : Prevalid Γ := Prevalid.tail (PrevalidExt.ctx hpvOld)
  have hPrevalidSub : Prevalid ({bound := t, kind := .sub} :: Γ) :=
    Prevalid.sub hΓ ht
  have hStackScoped : Stack.Scoped (Γ.depth + 1) (Stack.shift 0 s) :=
    PrevalidExt.stack_scoped hpvOld
  have hpvNew :
      PrevalidExt ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) :=
    PrevalidExt.of_stack_scoped hPrevalidSub (by
      simpa [Ctx.depth] using hStackScoped)
  exact (MSubRed.lift_to_any_context_stack_of_NoBinders_nonempty hBody
    hBodyNoBinders hpvNew).some

namespace EqDiamonds

/-- The `Me-Bet × Me-Bet` source cell of de Bruijn Lemma 2 in **restricted
form**: closed unconditionally (modulo kernel axioms) for the case
combination

- `Term.AbsFree body` (top-level body has no abstraction; abstractions
  permitted only inside `.app` subterms — see `Term.AbsFree`),
- `Term.NoBinders v` (β-argument has no `.bvar` and no `.abs` anywhere).

The restriction on the body matches the wall analysis of
`MEqRedStar.argTransportRestricted`: index-0 instantiation cannot recurse
under a top-level abstraction without an index-1 instantiation lemma.

The restriction on `v` matches the wall analysis of
`MEqRedStar.lift_to_any_stack_of_NoBinders`: the `pro` constructor case
of the single-step stack lift requires lifting an inner equ-binding
derivation whose source `α` may be `.abs`-rooted, hitting the
`MEqRedFunStackAppendPayload` wall. Excluding `.bvar` and `.abs` from `v`
excludes the relevant constructors entirely.

`NoBinders` is preserved by `MEqRed` (`MEqRed.preserves_noBinders`), so
the post-step joined arguments `v₁'`, `v₂'`, and the diamond reduct `v₃`
are all `NoBinders` once `v` is. The body's `AbsFree` premise on the
diamond reduct `body₃` is supplied separately because `MEqRed` does
**not** preserve `AbsFree` (a `pro` step on a body `bvar` can promote to
an abstraction). For body shapes where this preservation does hold —
e.g. `body` is itself `NoBinders` — the caller can derive `AbsFree
body₃` by composing `NoBinders`-preservation with `NoBinders.absFree`.

This cell discharges the partial form of `MEqRedArgTransportPayload` for
the `bet × bet` source of de Bruijn Lemma 2 without reliance on any
unproven payload — it is **unconditional modulo kernel axioms** for the
restricted shape. -/
theorem bet_bet_chain_AbsFree_of
    {Γ : Ctx} {s : Stack} {t v body body₁' body₂' v₁' v₂' : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hVNoBinders : Term.NoBinders v)
    (hAbsFreeBody₃ : ∀ {body₃ : Term},
      MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body₁' body₃ →
      Term.AbsFree body₃)
    (hBody₁ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₁')
    (hArg₁ : MEqRed Γ [] v v₁')
    (hBody₂ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂')
    (hArg₂ : MEqRed Γ [] v v₂') :
    ∃ t₃,
      MEqRedStar Γ s (Term.instantiate 0 v₁' body₁') t₃
      ∧ MEqRedStar Γ s (Term.instantiate 0 v₂' body₂') t₃ := by
  -- Body diamond closure: body₁' / body₂' join at body₃.
  obtain ⟨body₃, hBody₁₃J, hBody₂₃J⟩ := hBodyDiamond hBody₁ hBody₂
  -- Arg diamond closure: v₁' / v₂' join at v₃ at the empty stack.
  obtain ⟨v₃, hArg₁₃J, hArg₂₃J⟩ := hArgDiamond hArg₁ hArg₂
  -- Extract Type-valued MEqRed derivations.
  let hBody₁₃ : MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
    body₁' body₃ := hBody₁₃J.some
  let hBody₂₃ : MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
    body₂' body₃ := hBody₂₃J.some
  let hArg₁₃ : MEqRed Γ [] v₁' v₃ := hArg₁₃J.some
  let hArg₂₃ : MEqRed Γ [] v₂' v₃ := hArg₂₃J.some
  -- NoBinders propagation through the diamond's argument path.
  have hV₁'NoBinders : Term.NoBinders v₁' :=
    hArg₁.preserves_noBinders hVNoBinders
  have hV₂'NoBinders : Term.NoBinders v₂' :=
    hArg₂.preserves_noBinders hVNoBinders
  -- AbsFree on the joined body (caller-supplied).
  have hBody₃AbsFree : Term.AbsFree body₃ := hAbsFreeBody₃ hBody₁₃J
  refine ⟨Term.instantiate 0 v₃ body₃, ?_, ?_⟩
  · -- LHS chain: instantiate 0 v₁' body₁' →* instantiate 0 v₃ body₃.
    have hv₁'Scoped : Term.Scoped Γ.depth v₁' := hArg₁.scoped_right
    have hBodyProgress :
        MEqRed Γ (Stack.instantiate 0 v₁' (Stack.shift 0 s))
          (Term.instantiate 0 v₁' body₁')
          (Term.instantiate 0 v₁' body₃) :=
      MEqRedFusedKindNarrowedBetaSubstStack_proved
        (arg := t) (arg' := v₁') ht hv₁'Scoped hBody₁₃
    have hStackEq :
        Stack.instantiate 0 v₁' (Stack.shift 0 s) = s :=
      Stack.instantiate_zero_shift_zero_id v₁' s
    have hBodyProgress' :
        MEqRed Γ s
          (Term.instantiate 0 v₁' body₁')
          (Term.instantiate 0 v₁' body₃) := by
      simpa [hStackEq] using hBodyProgress
    have hBody₃Scoped : Term.Scoped (Γ.depth + 1) body₃ := by
      simpa [Ctx.depth] using hBody₁₃.scoped_right
    have hpvΓs : PrevalidExt Γ s :=
      PrevalidExt.weaken_head_inv hBody₁.prevalidExt
    have hArgChain :
        MEqRedStar Γ s
          (Term.instantiate 0 v₁' body₃)
          (Term.instantiate 0 v₃ body₃) :=
      MEqRedArgTransportPayloadRestricted_proved
        hBody₃Scoped hBody₃AbsFree hV₁'NoBinders hArg₁₃ hpvΓs
    exact (MEqRedStar.single hBodyProgress').trans hArgChain
  · -- RHS chain: instantiate 0 v₂' body₂' →* instantiate 0 v₃ body₃.
    have hv₂'Scoped : Term.Scoped Γ.depth v₂' := hArg₂.scoped_right
    have hBodyProgress :
        MEqRed Γ (Stack.instantiate 0 v₂' (Stack.shift 0 s))
          (Term.instantiate 0 v₂' body₂')
          (Term.instantiate 0 v₂' body₃) :=
      MEqRedFusedKindNarrowedBetaSubstStack_proved
        (arg := t) (arg' := v₂') ht hv₂'Scoped hBody₂₃
    have hStackEq :
        Stack.instantiate 0 v₂' (Stack.shift 0 s) = s :=
      Stack.instantiate_zero_shift_zero_id v₂' s
    have hBodyProgress' :
        MEqRed Γ s
          (Term.instantiate 0 v₂' body₂')
          (Term.instantiate 0 v₂' body₃) := by
      simpa [hStackEq] using hBodyProgress
    have hBody₃Scoped : Term.Scoped (Γ.depth + 1) body₃ := by
      simpa [Ctx.depth] using hBody₂₃.scoped_right
    have hpvΓs : PrevalidExt Γ s :=
      PrevalidExt.weaken_head_inv hBody₂.prevalidExt
    have hArgChain :
        MEqRedStar Γ s
          (Term.instantiate 0 v₂' body₃)
          (Term.instantiate 0 v₃ body₃) :=
      MEqRedArgTransportPayloadRestricted_proved
        hBody₃Scoped hBody₃AbsFree hV₂'NoBinders hArg₂₃ hpvΓs
    exact (MEqRedStar.single hBodyProgress').trans hArgChain

/-- Restricted `Me-Bet × Me-Bet` source cell with an easier body side
condition: if the body branch used for the joined-body proof is itself
`NoBinders`, then the `AbsFree` side condition of
`bet_bet_chain_AbsFree_of` follows by `MEqRedJ.preserves_noBinders`. -/
theorem bet_bet_chain_NoBinders_of
    {Γ : Ctx} {s : Stack} {t v body body₁' body₂' v₁' v₂' : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hVNoBinders : Term.NoBinders v)
    (hBody₁'NoBinders : Term.NoBinders body₁')
    (hBody₁ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₁')
    (hArg₁ : MEqRed Γ [] v v₁')
    (hBody₂ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂')
    (hArg₂ : MEqRed Γ [] v v₂') :
    ∃ t₃,
      MEqRedStar Γ s (Term.instantiate 0 v₁' body₁') t₃
      ∧ MEqRedStar Γ s (Term.instantiate 0 v₂' body₂') t₃ :=
  bet_bet_chain_AbsFree_of hBodyDiamond hArgDiamond ht hVNoBinders
    (fun h => (h.preserves_noBinders hBody₁'NoBinders).absFree)
    hBody₁ hArg₁ hBody₂ hArg₂

end EqDiamonds

/-! ## `Me-App × Me-App` chain-output cell (conditional on operator
stack-head transport)

The single-step approach to this cell walls because `MEqRed.app`'s operator
sub-step lives at the operand-as-stack-head, and the post-arg-step operand
differs from the pre-arg-step operand. With chain output via
`MEqRedStar.app_left/app_right`, we can decompose into "arg first then
operator" or "operator first then arg" — but in either case, the chain
congruence requires the operator chain to live at the stack head matching
the operand at that point, and the operator-diamond's output lives at the
*pre-step* operand's stack head.

This is structurally identical to the wall observed in the iter-32 Lever A
counterexample at `tAp`: stack-head transport of an arbitrary `MEqRed`
operator step from `(v :: s)` to `(v' :: s)` is the open problem.

The closed form here threads an explicit **operator stack-head transport
hypothesis** as a Prop premise, mirroring how `bet_bet_chain_of` threads
`MEqRedArgTransportPayload`. This is not a new axiom — callers must supply
the transport from elsewhere (or arrange that the relevant operator steps
fall in the stack-insensitive sublanguage where transport is provable). -/

/-- Operator stack-head transport: given an arg-side equivalence chain
`v →* v'`, lift any operator step at stack `(v :: s)` to a chain at stack
`(v' :: s)`. This is the structurally missing ingredient for the
`Me-App × Me-App` chain-output cell.

`MEqRed.app`'s recursive operator premise is at stack `(v :: s)` where `v`
is the operand. After an arg-side chain `v →* v'`, the application's
operand has progressed to `v'`, and a follow-on operator chain needs to
live at stack `(v' :: s)`.

Stated with a chain (`MEqRedStar`) on the arg side rather than a single
step so that callers can compose multi-hop arg progressions (e.g. the
diamond's two-hop `v → v_i → v₃` factoring) without repeated invocation. -/
def MEqRedOpStackHeadTransportPayload : Prop :=
  ∀ {Γ : Ctx} {s : Stack} {v v' u u' : Term},
    MEqRedStar Γ [] v v' →
      MEqRed Γ (v :: s) u u' →
        MEqRedStar Γ (v' :: s) u u'

/-- Restricted operator stack-head transport for binder-free operator
sources. The general transport is false for abstraction-rooted operators
because `Me-Fun` requires an empty stack, but `Term.NoBinders` excludes
the stack-sensitive and lookup-sensitive source shapes. -/
def MEqRedOpStackHeadTransportPayloadRestricted : Prop :=
  ∀ {Γ : Ctx} {s : Stack} {v v' u u' : Term},
    MEqRedStar Γ [] v v' →
      Term.NoBinders u →
        MEqRed Γ (v :: s) u u' →
          MEqRedStar Γ (v' :: s) u u'

/-- Closed proof of the restricted operator stack-head transport surface,
obtained by retargeting the operator step to the post-argument stack with
`MEqRedStar.lift_to_any_stack_of_NoBinders`. -/
theorem MEqRedOpStackHeadTransportPayloadRestricted_proved :
    MEqRedOpStackHeadTransportPayloadRestricted := by
  intro Γ s v v' u u' hArgStar hNoBinders hOpStep
  have hpvCons : PrevalidExt Γ (v :: s) := hOpStep.prevalidExt
  have hpvTail : PrevalidExt Γ s := PrevalidExt.tail hpvCons
  have hv : Term.Scoped Γ.depth v := PrevalidExt.head_scoped hpvCons
  have hv' : Term.Scoped Γ.depth v' := hArgStar.scoped_right hv
  have hpvNew : PrevalidExt Γ (v' :: s) := PrevalidExt.cons hpvTail hv'
  exact MEqRedStar.lift_to_any_stack_of_NoBinders hOpStep hNoBinders hpvNew

namespace EqDiamonds

/-- The `Me-App × Me-App` source cell of de Bruijn Lemma 2 with chain
output. Closes via "first step the arg, then step the operator at the new
arg-stack" using `MEqRedStar.app_right` and `MEqRedStar.app_left`,
threading the operator stack-head transport for the second leg. -/
theorem app_app_chain_of
    (hOpTransport : MEqRedOpStackHeadTransportPayload)
    {Γ : Ctx} {s : Stack} {u u₁ u₂ v v₁ v₂ : Term}
    (hOpDiamond :
      ∀ {a b : Term},
        MEqRed Γ (v :: s) u a → MEqRed Γ (v :: s) u b →
        ∃ c, MEqRedJ Γ (v :: s) a c ∧ MEqRedJ Γ (v :: s) b c)
    (hArgDiamond :
      ∀ {a b : Term},
        MEqRed Γ [] v a → MEqRed Γ [] v b →
        ∃ c, MEqRedJ Γ [] a c ∧ MEqRedJ Γ [] b c)
    (hOp₁ : MEqRed Γ (v :: s) u u₁) (hArg₁ : MEqRed Γ [] v v₁)
    (hOp₂ : MEqRed Γ (v :: s) u u₂) (hArg₂ : MEqRed Γ [] v v₂) :
    ∃ t₃, MEqRedStar Γ s (.app u₁ v₁) t₃ ∧ MEqRedStar Γ s (.app u₂ v₂) t₃ := by
  -- Op diamond closure: u₁ / u₂ join at u₃ at stack (v :: s).
  obtain ⟨u₃, hOp₁₃J, hOp₂₃J⟩ := hOpDiamond hOp₁ hOp₂
  -- Arg diamond closure: v₁ / v₂ join at v₃ at empty stack.
  obtain ⟨v₃, hArg₁₃J, hArg₂₃J⟩ := hArgDiamond hArg₁ hArg₂
  -- Extract the underlying Type-valued derivations.
  let hOp₁₃ : MEqRed Γ (v :: s) u₁ u₃ := hOp₁₃J.some
  let hOp₂₃ : MEqRed Γ (v :: s) u₂ u₃ := hOp₂₃J.some
  let hArg₁₃ : MEqRed Γ [] v₁ v₃ := hArg₁₃J.some
  let hArg₂₃ : MEqRed Γ [] v₂ v₃ := hArg₂₃J.some
  -- Recover prevalidities and scopings.
  have hpvCons : PrevalidExt Γ (v :: s) := hOp₁.prevalidExt
  have hpv : PrevalidExt Γ s := PrevalidExt.tail hpvCons
  have hu₁ : Term.Scoped Γ.depth u₁ := hOp₁.scoped_right
  have hu₂ : Term.Scoped Γ.depth u₂ := hOp₂.scoped_right
  have hv₃ : Term.Scoped Γ.depth v₃ := hArg₁₃.scoped_right
  -- The arg-side two-hop chain `v →* v_i →* v₃` for each branch.
  have hArgChain₁_full : MEqRedStar Γ [] v v₃ :=
    (MEqRedStar.single hArg₁).trans (MEqRedStar.single hArg₁₃)
  have hArgChain₂_full : MEqRedStar Γ [] v v₃ :=
    (MEqRedStar.single hArg₂).trans (MEqRedStar.single hArg₂₃)
  refine ⟨.app u₃ v₃, ?_, ?_⟩
  · -- LHS chain: (.app u₁ v₁) →* (.app u₁ v₃) →* (.app u₃ v₃).
    have hArgStep₁ : MEqRedStar Γ [] v₁ v₃ := MEqRedStar.single hArg₁₃
    have hArgChain₁ : MEqRedStar Γ s (.app u₁ v₁) (.app u₁ v₃) :=
      MEqRedStar.app_right hu₁ hArgStep₁ hpv
    -- Transport the operator step from stack (v :: s) to (v₃ :: s)
    -- using the supplied stack-head transport. The transport's `v`
    -- is the *original* `v` (matching `hOp₁₃`'s stack), with target
    -- `v₃` reached via the two-hop arg chain.
    have hOpAtNewStack : MEqRedStar Γ (v₃ :: s) u₁ u₃ :=
      hOpTransport hArgChain₁_full hOp₁₃
    have hOpChain₁ : MEqRedStar Γ s (.app u₁ v₃) (.app u₃ v₃) :=
      MEqRedStar.app_left hOpAtNewStack hv₃
    exact hArgChain₁.trans hOpChain₁
  · -- RHS chain: (.app u₂ v₂) →* (.app u₂ v₃) →* (.app u₃ v₃).
    have hArgStep₂ : MEqRedStar Γ [] v₂ v₃ := MEqRedStar.single hArg₂₃
    have hArgChain₂ : MEqRedStar Γ s (.app u₂ v₂) (.app u₂ v₃) :=
      MEqRedStar.app_right hu₂ hArgStep₂ hpv
    have hOpAtNewStack : MEqRedStar Γ (v₃ :: s) u₂ u₃ :=
      hOpTransport hArgChain₂_full hOp₂₃
    have hOpChain₂ : MEqRedStar Γ s (.app u₂ v₃) (.app u₃ v₃) :=
      MEqRedStar.app_left hOpAtNewStack hv₃
    exact hArgChain₂.trans hOpChain₂

/-- Restricted `Me-App × Me-App` source cell: the conditional operator
stack-head transport is discharged when the original operator source is
`Term.NoBinders`. The premise propagates to both operator diamond branches
by `MEqRed.preserves_noBinders`. -/
theorem app_app_chain_NoBinders_of
    {Γ : Ctx} {s : Stack} {u u₁ u₂ v v₁ v₂ : Term}
    (hNoBindersOp : Term.NoBinders u)
    (hOpDiamond :
      ∀ {a b : Term},
        MEqRed Γ (v :: s) u a → MEqRed Γ (v :: s) u b →
        ∃ c, MEqRedJ Γ (v :: s) a c ∧ MEqRedJ Γ (v :: s) b c)
    (hArgDiamond :
      ∀ {a b : Term},
        MEqRed Γ [] v a → MEqRed Γ [] v b →
        ∃ c, MEqRedJ Γ [] a c ∧ MEqRedJ Γ [] b c)
    (hOp₁ : MEqRed Γ (v :: s) u u₁) (hArg₁ : MEqRed Γ [] v v₁)
    (hOp₂ : MEqRed Γ (v :: s) u u₂) (hArg₂ : MEqRed Γ [] v v₂) :
    ∃ t₃, MEqRedStar Γ s (.app u₁ v₁) t₃ ∧ MEqRedStar Γ s (.app u₂ v₂) t₃ := by
  have hOp₁NoBinders : Term.NoBinders u₁ :=
    hOp₁.preserves_noBinders hNoBindersOp
  have hOp₂NoBinders : Term.NoBinders u₂ :=
    hOp₂.preserves_noBinders hNoBindersOp
  obtain ⟨u₃, hOp₁₃J, hOp₂₃J⟩ := hOpDiamond hOp₁ hOp₂
  obtain ⟨v₃, hArg₁₃J, hArg₂₃J⟩ := hArgDiamond hArg₁ hArg₂
  let hOp₁₃ : MEqRed Γ (v :: s) u₁ u₃ := hOp₁₃J.some
  let hOp₂₃ : MEqRed Γ (v :: s) u₂ u₃ := hOp₂₃J.some
  let hArg₁₃ : MEqRed Γ [] v₁ v₃ := hArg₁₃J.some
  let hArg₂₃ : MEqRed Γ [] v₂ v₃ := hArg₂₃J.some
  have hpvCons : PrevalidExt Γ (v :: s) := hOp₁.prevalidExt
  have hpv : PrevalidExt Γ s := PrevalidExt.tail hpvCons
  have hu₁ : Term.Scoped Γ.depth u₁ := hOp₁.scoped_right
  have hu₂ : Term.Scoped Γ.depth u₂ := hOp₂.scoped_right
  have hv₃ : Term.Scoped Γ.depth v₃ := hArg₁₃.scoped_right
  have hArgChain₁_full : MEqRedStar Γ [] v v₃ :=
    (MEqRedStar.single hArg₁).trans (MEqRedStar.single hArg₁₃)
  have hArgChain₂_full : MEqRedStar Γ [] v v₃ :=
    (MEqRedStar.single hArg₂).trans (MEqRedStar.single hArg₂₃)
  refine ⟨.app u₃ v₃, ?_, ?_⟩
  · have hArgStep₁ : MEqRedStar Γ [] v₁ v₃ := MEqRedStar.single hArg₁₃
    have hArgChain₁ : MEqRedStar Γ s (.app u₁ v₁) (.app u₁ v₃) :=
      MEqRedStar.app_right hu₁ hArgStep₁ hpv
    have hOpAtNewStack : MEqRedStar Γ (v₃ :: s) u₁ u₃ :=
      MEqRedOpStackHeadTransportPayloadRestricted_proved
        hArgChain₁_full hOp₁NoBinders hOp₁₃
    have hOpChain₁ : MEqRedStar Γ s (.app u₁ v₃) (.app u₃ v₃) :=
      MEqRedStar.app_left hOpAtNewStack hv₃
    exact hArgChain₁.trans hOpChain₁
  · have hArgStep₂ : MEqRedStar Γ [] v₂ v₃ := MEqRedStar.single hArg₂₃
    have hArgChain₂ : MEqRedStar Γ s (.app u₂ v₂) (.app u₂ v₃) :=
      MEqRedStar.app_right hu₂ hArgStep₂ hpv
    have hOpAtNewStack : MEqRedStar Γ (v₃ :: s) u₂ u₃ :=
      MEqRedOpStackHeadTransportPayloadRestricted_proved
        hArgChain₂_full hOp₂NoBinders hOp₂₃
    have hOpChain₂ : MEqRedStar Γ s (.app u₂ v₃) (.app u₃ v₃) :=
      MEqRedStar.app_left hOpAtNewStack hv₃
    exact hArgChain₂.trans hOpChain₂

/-- Restricted `Me-Bet × Me-App` source cell: the general argument-transport
payload is discharged for binder-free arguments, matching the restricted
`bet × bet` surface. The `.sub`-head bridge for the `Me-FOp`-inverted body
remains explicit. -/
theorem bet_app_chain_AbsFree_of
    {Γ : Ctx} {s : Stack} {t v body body₁' v₁' v₂' hOp₂_target : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hVNoBinders : Term.NoBinders v)
    (hAbsFreeBody₃ : ∀ {body₃ : Term},
      MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body₁' body₃ →
      Term.AbsFree body₃)
    (hBody₁ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₁')
    (hArg₁ : MEqRed Γ [] v v₁')
    (hOp₂ : MEqRed Γ (v :: s) (.abs t body) hOp₂_target)
    (hArg₂ : MEqRed Γ [] v v₂')
    (hBody₂Sub :
      ∀ {body₂' t' : Term},
        hOp₂_target = .abs t' body₂' →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂') :
    ∃ t₃,
      MEqRedStar Γ s (Term.instantiate 0 v₁' body₁') t₃
      ∧ MEqRedStar Γ s (.app hOp₂_target v₂') t₃ := by
  cases hOp₂ with
  | fOp hT₂ hα₂ hBody₂equ =>
    rename_i t' body₂'
    have hBody₂sub :
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂' :=
      hBody₂Sub rfl
    obtain ⟨body₃, hBody₁₃J, hBody₂₃J⟩ := hBodyDiamond hBody₁ hBody₂sub
    obtain ⟨v₃, hArg₁₃J, hArg₂₃J⟩ := hArgDiamond hArg₁ hArg₂
    let hBody₁₃ :
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
          body₁' body₃ := hBody₁₃J.some
    let hBody₂₃ :
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
          body₂' body₃ := hBody₂₃J.some
    let hArg₁₃ : MEqRed Γ [] v₁' v₃ := hArg₁₃J.some
    let hArg₂₃ : MEqRed Γ [] v₂' v₃ := hArg₂₃J.some
    have hV₁'NoBinders : Term.NoBinders v₁' :=
      hArg₁.preserves_noBinders hVNoBinders
    have hV₂'NoBinders : Term.NoBinders v₂' :=
      hArg₂.preserves_noBinders hVNoBinders
    have hBody₃AbsFree : Term.AbsFree body₃ := hAbsFreeBody₃ hBody₁₃J
    refine ⟨Term.instantiate 0 v₃ body₃, ?_, ?_⟩
    · have hv₁'Scoped : Term.Scoped Γ.depth v₁' := hArg₁.scoped_right
      have hBodyProgress :
          MEqRed Γ (Stack.instantiate 0 v₁' (Stack.shift 0 s))
            (Term.instantiate 0 v₁' body₁')
            (Term.instantiate 0 v₁' body₃) :=
        MEqRedFusedKindNarrowedBetaSubstStack_proved
          (arg := t) (arg' := v₁') ht hv₁'Scoped hBody₁₃
      have hStackEq :
          Stack.instantiate 0 v₁' (Stack.shift 0 s) = s :=
        Stack.instantiate_zero_shift_zero_id v₁' s
      have hBodyProgress' :
          MEqRed Γ s
            (Term.instantiate 0 v₁' body₁')
            (Term.instantiate 0 v₁' body₃) := by
        simpa [hStackEq] using hBodyProgress
      have hBody₃Scoped : Term.Scoped (Γ.depth + 1) body₃ := by
        simpa [Ctx.depth] using hBody₁₃.scoped_right
      have hpvΓs : PrevalidExt Γ s :=
        PrevalidExt.weaken_head_inv hBody₁.prevalidExt
      have hArgChain :
          MEqRedStar Γ s
            (Term.instantiate 0 v₁' body₃)
            (Term.instantiate 0 v₃ body₃) :=
        MEqRedArgTransportPayloadRestricted_proved
          hBody₃Scoped hBody₃AbsFree hV₁'NoBinders hArg₁₃ hpvΓs
      exact (MEqRedStar.single hBodyProgress').trans hArgChain
    · have hpvΓs : PrevalidExt Γ s :=
        PrevalidExt.weaken_head_inv hBody₁.prevalidExt
      have ht' : Term.Scoped Γ.depth t' := hT₂.scoped_right
      have hPrevalidT' :
          Prevalid ({bound := t', kind := .sub} :: Γ) :=
        Prevalid.sub (PrevalidExt.ctx hpvΓs) ht'
      have hpvBody₂t' :
          PrevalidExt ({bound := t', kind := .sub} :: Γ) (Stack.shift 0 s) :=
        PrevalidExt.weaken_head hpvΓs hPrevalidT'
      have hBody₂'Scoped : Term.Scoped (Γ.depth + 1) body₂' := by
        simpa [Ctx.depth] using hBody₂equ.scoped_right
      have hBody₂'Scoped_t' :
          Term.Scoped
            (Ctx.depth ({bound := t', kind := .sub} :: Γ)) body₂' := by
        simpa [Ctx.depth, Nat.succ_eq_add_one] using hBody₂'Scoped
      have hBodyReflT' :
          MEqRed ({bound := t', kind := .sub} :: Γ) (Stack.shift 0 s)
            body₂' body₂' :=
        MEqRed.refl hpvBody₂t' hBody₂'Scoped_t'
      have hv₂'Scoped : Term.Scoped Γ.depth v₂' := hArg₂.scoped_right
      have hpvNil : PrevalidExt Γ [] :=
        PrevalidExt.nil (PrevalidExt.ctx hpvΓs)
      have hArgReflv₂' : MEqRed Γ [] v₂' v₂' :=
        MEqRed.refl hpvNil hv₂'Scoped
      have hβStep :
          MEqRed Γ s (.app (.abs t' body₂') v₂')
            (Term.instantiate 0 v₂' body₂') :=
        MEqRed.bet ht' hBodyReflT' hArgReflv₂'
      have hBodyProgress :
          MEqRed Γ (Stack.instantiate 0 v₂' (Stack.shift 0 s))
            (Term.instantiate 0 v₂' body₂')
            (Term.instantiate 0 v₂' body₃) :=
        MEqRedFusedKindNarrowedBetaSubstStack_proved
          (arg := t) (arg' := v₂') ht hv₂'Scoped hBody₂₃
      have hStackEq :
          Stack.instantiate 0 v₂' (Stack.shift 0 s) = s :=
        Stack.instantiate_zero_shift_zero_id v₂' s
      have hBodyProgress' :
          MEqRed Γ s
            (Term.instantiate 0 v₂' body₂')
            (Term.instantiate 0 v₂' body₃) := by
        simpa [hStackEq] using hBodyProgress
      have hBody₃Scoped : Term.Scoped (Γ.depth + 1) body₃ := by
        simpa [Ctx.depth] using hBody₂₃.scoped_right
      have hArgChain :
          MEqRedStar Γ s
            (Term.instantiate 0 v₂' body₃)
            (Term.instantiate 0 v₃ body₃) :=
        MEqRedArgTransportPayloadRestricted_proved
          hBody₃Scoped hBody₃AbsFree hV₂'NoBinders hArg₂₃ hpvΓs
      exact ((MEqRedStar.single hβStep).trans
        (MEqRedStar.single hBodyProgress')).trans hArgChain

/-- Restricted `Me-App × Me-Bet` source cell, symmetric to
`bet_app_chain_AbsFree_of`. -/
theorem app_bet_chain_AbsFree_of
    {Γ : Ctx} {s : Stack} {t v body body₂' v₁' v₂' hOp₁_target : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hVNoBinders : Term.NoBinders v)
    (hAbsFreeBody₃ : ∀ {body₃ : Term},
      MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body₂' body₃ →
      Term.AbsFree body₃)
    (hOp₁ : MEqRed Γ (v :: s) (.abs t body) hOp₁_target)
    (hArg₁ : MEqRed Γ [] v v₁')
    (hBody₂ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂')
    (hArg₂ : MEqRed Γ [] v v₂')
    (hBody₁Sub :
      ∀ {body₁' t' : Term},
        hOp₁_target = .abs t' body₁' →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₁') :
    ∃ t₃,
      MEqRedStar Γ s (.app hOp₁_target v₁') t₃
      ∧ MEqRedStar Γ s (Term.instantiate 0 v₂' body₂') t₃ := by
  obtain ⟨t₃, hLeft, hRight⟩ :=
    bet_app_chain_AbsFree_of hBodyDiamond hArgDiamond ht hVNoBinders
      hAbsFreeBody₃ hBody₂ hArg₂ hOp₁ hArg₁ hBody₁Sub
  exact ⟨t₃, hRight, hLeft⟩

/-- Restricted `Me-Bet × Me-App` source cell with the joined-body
`AbsFree` side condition discharged from a `NoBinders` body branch. -/
theorem bet_app_chain_NoBinders_of
    {Γ : Ctx} {s : Stack} {t v body body₁' v₁' v₂' hOp₂_target : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hVNoBinders : Term.NoBinders v)
    (hBody₁'NoBinders : Term.NoBinders body₁')
    (hBody₁ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₁')
    (hArg₁ : MEqRed Γ [] v v₁')
    (hOp₂ : MEqRed Γ (v :: s) (.abs t body) hOp₂_target)
    (hArg₂ : MEqRed Γ [] v v₂')
    (hBody₂Sub :
      ∀ {body₂' t' : Term},
        hOp₂_target = .abs t' body₂' →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂') :
    ∃ t₃,
      MEqRedStar Γ s (Term.instantiate 0 v₁' body₁') t₃
      ∧ MEqRedStar Γ s (.app hOp₂_target v₂') t₃ :=
  bet_app_chain_AbsFree_of hBodyDiamond hArgDiamond ht hVNoBinders
    (fun h => (h.preserves_noBinders hBody₁'NoBinders).absFree)
    hBody₁ hArg₁ hOp₂ hArg₂ hBody₂Sub

/-- Restricted `Me-App × Me-Bet` source cell with the joined-body
`AbsFree` side condition discharged from a `NoBinders` body branch. -/
theorem app_bet_chain_NoBinders_of
    {Γ : Ctx} {s : Stack} {t v body body₂' v₁' v₂' hOp₁_target : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hVNoBinders : Term.NoBinders v)
    (hBody₂'NoBinders : Term.NoBinders body₂')
    (hOp₁ : MEqRed Γ (v :: s) (.abs t body) hOp₁_target)
    (hArg₁ : MEqRed Γ [] v v₁')
    (hBody₂ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂')
    (hArg₂ : MEqRed Γ [] v v₂')
    (hBody₁Sub :
      ∀ {body₁' t' : Term},
        hOp₁_target = .abs t' body₁' →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₁') :
    ∃ t₃,
      MEqRedStar Γ s (.app hOp₁_target v₁') t₃
      ∧ MEqRedStar Γ s (Term.instantiate 0 v₂' body₂') t₃ :=
  app_bet_chain_AbsFree_of hBodyDiamond hArgDiamond ht hVNoBinders
    (fun h => (h.preserves_noBinders hBody₂'NoBinders).absFree)
    hOp₁ hArg₁ hBody₂ hArg₂ hBody₁Sub

end EqDiamonds
/-! ## Argument-transport under preserved heads (universal form)

The body-shape recursion in `argTransportRestricted` stalls at
`body = .abs bound innerBody` because the inner body's substitution is
at index 1, not index 0. The fix is the standard under-heads pattern
(mirroring `MEqRedRespectsBetaInstantiateUnderHeadsStack_universal`):
generalize the substitution index `k` from a fixed `0` to a `Nat`-indexed
family, where the dropped binder has been pushed under `n` preserved
heads above.

In this form the body's recursion descends into abstractions structurally:
- `body = .bvar i` with `i = n` is the only case that fires the
  substitution (substituting `shiftBy 0 n arg` for the dropped binder).
- `body = .abs bound innerBody` recurses on `innerBody` at `n + 1`. The
  inner body's `bvar 0` then refers to the new abstraction binder (no
  substitution); `bvar (n + 1)` refers to the lifted dropped binder
  (substitution fires there only if the inner body references it).

The argument-side stack lift is still packaged as a hypothesis `hLift`
because the underlying `MEqRed` step `arg → arg'` may not lift to
arbitrary stacks even with `Term.AbsFree arg` (the `Me-Pro` case on
`arg = .bvar i` recurses on the looked-up annotation, which is not
constrained). The caller (typically the bet × bet diamond cell)
discharges this externally.

The substantive gain over `MEqRedStar.argTransportRestricted` is that
the body need not be `Term.AbsFree`: the abstraction case closes via
the under-heads recursion at `n + 1` and the `Me-Fun`/`Me-FOp` chain
congruences (`meqRedStar_abs_fun_body_fixed_bound` and
`meqRedStar_abs_fOp_body_fixed_bound`). -/

/-- Universal under-heads argument-transport. The "lift" hypothesis is
quantified over `n'`, `heads'`, and `s'` so that recursive descent into
abstraction bodies (which increases `n` to `n' + 1`) and into application
operators (which extends the stack) can both reuse the same lift surface.
-/
def MEqRedStarArgTransportUnderHeadsStack (n : Nat) : Prop :=
  ∀ {Γ : Ctx} {arg arg' body : Term} {heads : Ctx} {s : Stack},
    heads.length = n →
    Term.Scoped (Γ.depth + n + 1) body →
    Term.Scoped Γ.depth arg →
    Term.Scoped Γ.depth arg' →
    PrevalidExt (heads ++ { bound := arg, kind := .sub } :: Γ) s →
    (∀ {n' : Nat} {heads' : Ctx} {s' : Stack},
      heads'.length = n' →
      PrevalidExt (heads' ++ { bound := arg, kind := .sub } :: Γ) s' →
      MEqRedStar (Ctx.instantiateBetaPrefix arg n' heads' ++ Γ)
        (Stack.instantiate n' (Term.shiftBy 0 n' arg) s')
        (Term.shiftBy 0 n' arg) (Term.shiftBy 0 n' arg')) →
    MEqRedStar (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
      (Stack.instantiate n (Term.shiftBy 0 n arg) s)
      (Term.instantiate n (Term.shiftBy 0 n arg) body)
      (Term.instantiate n (Term.shiftBy 0 n arg') body)

/-- Closed-stack universal argument-transport: the body can be any shape,
including abstractions. The argument-side stack lift `hLift` is universally
quantified over preserved-head prefixes to support the under-heads
recursion. -/
def MEqRedStarArgTransportStack : Prop :=
  ∀ {Γ : Ctx} {arg arg' body : Term} {s : Stack},
    Term.Scoped (Γ.depth + 1) body →
    Term.Scoped Γ.depth arg →
    Term.Scoped Γ.depth arg' →
    PrevalidExt Γ s →
    (∀ {n' : Nat} {heads' : Ctx} {s' : Stack},
      heads'.length = n' →
      PrevalidExt (heads' ++ { bound := arg, kind := .sub } :: Γ) s' →
      MEqRedStar (Ctx.instantiateBetaPrefix arg n' heads' ++ Γ)
        (Stack.instantiate n' (Term.shiftBy 0 n' arg) s')
        (Term.shiftBy 0 n' arg) (Term.shiftBy 0 n' arg')) →
    MEqRedStar Γ s
      (Term.instantiate 0 arg body) (Term.instantiate 0 arg' body)

/-- Pointwise stack-level monotonicity for `Stack.Scoped`. Used to lift a
stack scoped at `Γ.depth` to one scoped at `Γ.depth + 1` after adding a
preserved head. -/
private noncomputable def Stack.Scoped.mono_succ
    {depth : Nat} {s : Stack}
    (h : Stack.Scoped depth s) : Stack.Scoped (depth + 1) s := by
  induction h with
  | nil => exact Stack.Scoped.nil
  | cons hα _ ih => exact Stack.Scoped.cons (Term.scoped_mono (Nat.le_succ _) hα) ih

/-- The closed-stack universal argument-transport reduces to the universal
under-heads form at `n = 0`. We feed the under-heads form a source-side
stack `Stack.shift 0 s` (one shift to bring `s` into the source context
with the extra `.sub` head), and then `Stack.instantiate 0 arg (Stack.shift 0 s)`
collapses back to `s`. -/
theorem MEqRedStarArgTransportStack.of_generic
    (h : MEqRedStarArgTransportUnderHeadsStack 0) :
    MEqRedStarArgTransportStack := by
  intro Γ arg arg' body s hBody hArg hArg' hpv hLift
  have hBody0 : Term.Scoped (Γ.depth + 0 + 1) body := by
    simpa using hBody
  -- Source-side prevalid: shift the conclusion stack into the source context.
  have hpvΓ : Prevalid Γ := PrevalidExt.ctx hpv
  have hSubCtx : Prevalid ({ bound := arg, kind := .sub } :: Γ) :=
    Prevalid.sub hpvΓ hArg
  have hpvSrc : PrevalidExt
      ([] ++ { bound := arg, kind := .sub } :: Γ) (Stack.shift 0 s) := by
    have hShifted : PrevalidExt ({ bound := arg, kind := .sub } :: Γ)
        (Stack.shift 0 s) :=
      PrevalidExt.weaken_head hpv hSubCtx
    simpa using hShifted
  have h0 := h (Γ := Γ) (arg := arg) (arg' := arg') (body := body)
    (heads := []) (s := Stack.shift 0 s) rfl hBody0 hArg hArg' hpvSrc hLift
  simpa [Ctx.instantiateBetaPrefix, Term.shiftBy_zero_id,
    Stack.instantiate_zero_shift_zero_id] using h0

/-- Chain version of `MEqRed.sub_to_equ_head_replace`. -/
private theorem MEqRedStar.argTransport_sub_to_equ_head_replace
    {Γ : Ctx} {s : Stack} {u v : Term} {old new : Term}
    (h : MEqRedStar ({ bound := old, kind := .sub } :: Γ) s u v)
    (hnew : Term.Scoped Γ.depth new) :
    MEqRedStar ({ bound := new, kind := .equ } :: Γ) s u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hStep ih =>
      exact Relation.ReflTransGen.tail ih
        ⟨hStep.some.sub_to_equ_head_replace hnew⟩

/-- **Universal under-heads argument-transport.**

By induction on the body shape (not on a derivation). Each constructor case
either resolves trivially (`.top`, `.bvar i` with `i ≠ n`) or recurses
structurally:

- `.bvar n` (the dropped binder): the substituted endpoints are the shifted
  arg and arg'. Discharge via the `hLift` premise specialized at the
  current `(n, heads, s)` shape.
- `.app f x`: the post-substitution is `.app (inst f) (inst x)`. The
  operator step lives at the extended stack `(inst x) :: post_stack`; the
  operand step lives at empty stack. Compose via `MEqRedStar.app_left` and
  `MEqRedStar.app_right` (both shipped at commit `2a2b143`).
- `.abs bound innerBody`: recurse on `bound` at level `n` with empty stack
  to obtain a chain on the bound annotation; recurse on `innerBody` at
  level `n + 1` with `Stack.shift 0 (post_stack)` to obtain a chain on the
  inner body. Transport the inner-body chain across the bound's annotation
  swap via `MEqRedStar.sub_head_replace_star`. Assemble using
  `meqRedStar_abs_fun_bound_fixed_body` /
  `meqRedStar_abs_fun_body_fixed_bound` (empty outer stack) or
  `meqRedStar_abs_fOp_bound_fixed_body` /
  `meqRedStar_abs_fOp_body_fixed_bound` (non-empty outer stack).

The body's `.abs` case is the substantive gain over
`MEqRedStar.argTransportRestricted` (which excluded `.abs` bodies via
`Term.AbsFree`). -/
theorem MEqRedStarArgTransportUnderHeadsStack_universal :
    ∀ n, MEqRedStarArgTransportUnderHeadsStack n := by
  -- The structural recursion is on `body`, not `n`, so we shift the
  -- quantification accordingly.
  suffices key : ∀ (body : Term) (n : Nat) {Γ : Ctx} {arg arg' : Term}
      {heads : Ctx} {s : Stack},
      heads.length = n →
      Term.Scoped (Γ.depth + n + 1) body →
      Term.Scoped Γ.depth arg →
      Term.Scoped Γ.depth arg' →
      PrevalidExt (heads ++ { bound := arg, kind := .sub } :: Γ) s →
      (∀ {n' : Nat} {heads' : Ctx} {s' : Stack},
        heads'.length = n' →
        PrevalidExt (heads' ++ { bound := arg, kind := .sub } :: Γ) s' →
        MEqRedStar (Ctx.instantiateBetaPrefix arg n' heads' ++ Γ)
          (Stack.instantiate n' (Term.shiftBy 0 n' arg) s')
          (Term.shiftBy 0 n' arg) (Term.shiftBy 0 n' arg')) →
      MEqRedStar (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
        (Stack.instantiate n (Term.shiftBy 0 n arg) s)
        (Term.instantiate n (Term.shiftBy 0 n arg) body)
        (Term.instantiate n (Term.shiftBy 0 n arg') body) by
    intro n Γ arg arg' body heads s hlen hBody hArg hArg' hpvSrc hLift
    exact key body n hlen hBody hArg hArg' hpvSrc hLift
  intro body
  induction body with
  | top =>
      intro n Γ arg arg' heads s _hlen _hBody _hArg _hArg' _hpvSrc _hLift
      simpa [Term.instantiate] using
        (Relation.ReflTransGen.refl :
          MEqRedStar (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
            (Stack.instantiate n (Term.shiftBy 0 n arg) s) .top .top)
  | bvar i =>
      intro n Γ arg arg' heads s hlen hBody hArg hArg' hpvSrc hLift
      have hi : i < Γ.depth + n + 1 := hBody.bvar_lt
      by_cases hlt : i < n
      · -- i < n: bvar stays as bvar (heads slot, untouched by substitution)
        have hne : i ≠ n := Nat.ne_of_lt hlt
        have hnotgt : ¬ n < i := Nat.not_lt_of_lt hlt
        simp [Term.instantiate, hlt, hne]
        exact Relation.ReflTransGen.refl
      by_cases heq : i = n
      · -- i = n: bvar is the dropped binder, substituted by arg/arg'
        subst heq
        have hLifted := hLift (n' := i) (heads' := heads) (s' := s) hlen hpvSrc
        simpa [Term.instantiate] using hLifted
      · -- i > n: bvar references original Γ, decremented by 1 in conclusion
        have hge : n ≤ i := Nat.le_of_not_lt hlt
        have hne : i ≠ n := heq
        have hgt : n < i := lt_of_le_of_ne hge (fun h => hne h.symm)
        have hnotlt : ¬ i < n := Nat.not_lt_of_lt hgt
        simp [Term.instantiate, hnotlt, heq]
        exact Relation.ReflTransGen.refl
  | app f x ihF ihX =>
      intro n Γ arg arg' heads s hlen hBody hArg hArg' hpvSrc hLift
      have hF : Term.Scoped (Γ.depth + n + 1) f := (Term.Scoped.app_inv hBody).1
      have hX : Term.Scoped (Γ.depth + n + 1) x := (Term.Scoped.app_inv hBody).2
      -- Conclusion-side prevalid (after substitution).
      have hpvConc :
          PrevalidExt (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
            (Stack.instantiate n (Term.shiftBy 0 n arg) s) :=
        BetaInstantiationPreservesPrevalidExtUnderHeadsOfScoped
          (n := n) hlen hArg hpvSrc
      -- The substituted argument-shifted by n.
      have hArgShifted : Term.Scoped (Γ.depth + n)
          (Term.shiftBy 0 n arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 n Γ.depth arg (Nat.zero_le _) hArg
      have hArg'Shifted : Term.Scoped (Γ.depth + n)
          (Term.shiftBy 0 n arg') := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 n Γ.depth arg' (Nat.zero_le _) hArg'
      -- Scoping of substituted f and x in the conclusion context.
      have hConcDepth :
          Ctx.depth (Ctx.instantiateBetaPrefix arg n heads ++ Γ) =
            Γ.depth + n := by
        show List.length (Ctx.instantiateBetaPrefix arg n heads ++ Γ) =
          List.length Γ + n
        rw [List.length_append, Ctx.length_instantiateBetaPrefix, hlen]
        omega
      have hFInst : Term.Scoped (Γ.depth + n)
          (Term.instantiate n (Term.shiftBy 0 n arg) f) :=
        Term.instantiate_scoped n (Γ.depth + n)
          (Term.shiftBy 0 n arg) f (by omega) hArgShifted hF
      have hFInst' : Term.Scoped (Γ.depth + n)
          (Term.instantiate n (Term.shiftBy 0 n arg') f) :=
        Term.instantiate_scoped n (Γ.depth + n)
          (Term.shiftBy 0 n arg') f (by omega) hArg'Shifted hF
      have hXInst : Term.Scoped (Γ.depth + n)
          (Term.instantiate n (Term.shiftBy 0 n arg) x) :=
        Term.instantiate_scoped n (Γ.depth + n)
          (Term.shiftBy 0 n arg) x (by omega) hArgShifted hX
      have hXInst' : Term.Scoped (Γ.depth + n)
          (Term.instantiate n (Term.shiftBy 0 n arg') x) :=
        Term.instantiate_scoped n (Γ.depth + n)
          (Term.shiftBy 0 n arg') x (by omega) hArg'Shifted hX
      have hFInstConc : Term.Scoped
          (Ctx.depth (Ctx.instantiateBetaPrefix arg n heads ++ Γ))
          (Term.instantiate n (Term.shiftBy 0 n arg) f) := by
        simpa [hConcDepth] using hFInst
      have hFInstConc' : Term.Scoped
          (Ctx.depth (Ctx.instantiateBetaPrefix arg n heads ++ Γ))
          (Term.instantiate n (Term.shiftBy 0 n arg') f) := by
        simpa [hConcDepth] using hFInst'
      have hXInstConc : Term.Scoped
          (Ctx.depth (Ctx.instantiateBetaPrefix arg n heads ++ Γ))
          (Term.instantiate n (Term.shiftBy 0 n arg) x) := by
        simpa [hConcDepth] using hXInst
      -- Source-side prevalid for the operator IH at extended stack `x :: s`.
      have hSrcDepth :
          Ctx.depth (heads ++ { bound := arg, kind := .sub } :: Γ) =
            Γ.depth + n + 1 := by
        simp [Ctx.depth, List.length_append, hlen, Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc]
      have hxSrc : Term.Scoped
          (Ctx.depth (heads ++ { bound := arg, kind := .sub } :: Γ)) x := by
        simpa [hSrcDepth] using hX
      have hpvSrcOp :
          PrevalidExt (heads ++ { bound := arg, kind := .sub } :: Γ)
            (x :: s) :=
        PrevalidExt.cons hpvSrc hxSrc
      -- IH on operator at extended stack.
      have hOpStar :
          MEqRedStar (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
            (Stack.instantiate n (Term.shiftBy 0 n arg) (x :: s))
            (Term.instantiate n (Term.shiftBy 0 n arg) f)
            (Term.instantiate n (Term.shiftBy 0 n arg') f) :=
        ihF n hlen hF hArg hArg' hpvSrcOp hLift
      -- Source-side prevalid for the operand IH at empty stack.
      have hpvSrcNil :
          PrevalidExt (heads ++ { bound := arg, kind := .sub } :: Γ) [] :=
        PrevalidExt.nil (PrevalidExt.ctx hpvSrc)
      have hOpStarFlat :
          MEqRedStar (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
            (Term.instantiate n (Term.shiftBy 0 n arg) x ::
              Stack.instantiate n (Term.shiftBy 0 n arg) s)
            (Term.instantiate n (Term.shiftBy 0 n arg) f)
            (Term.instantiate n (Term.shiftBy 0 n arg') f) := by
        simpa [Stack.instantiate] using hOpStar
      -- IH on operand at empty stack.
      have hArgChain :
          MEqRedStar (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
            (Stack.instantiate n (Term.shiftBy 0 n arg) [])
            (Term.instantiate n (Term.shiftBy 0 n arg) x)
            (Term.instantiate n (Term.shiftBy 0 n arg') x) :=
        ihX n hlen hX hArg hArg' hpvSrcNil hLift
      have hArgChainFlat :
          MEqRedStar (Ctx.instantiateBetaPrefix arg n heads ++ Γ) []
            (Term.instantiate n (Term.shiftBy 0 n arg) x)
            (Term.instantiate n (Term.shiftBy 0 n arg') x) := by
        simpa [Stack.instantiate] using hArgChain
      -- Compose: first move operator (at extended stack), then move operand.
      have hStarOp :
          MEqRedStar (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
            (Stack.instantiate n (Term.shiftBy 0 n arg) s)
            (.app (Term.instantiate n (Term.shiftBy 0 n arg) f)
              (Term.instantiate n (Term.shiftBy 0 n arg) x))
            (.app (Term.instantiate n (Term.shiftBy 0 n arg') f)
              (Term.instantiate n (Term.shiftBy 0 n arg) x)) :=
        MEqRedStar.app_left hOpStarFlat hXInstConc
      have hStarArg :
          MEqRedStar (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
            (Stack.instantiate n (Term.shiftBy 0 n arg) s)
            (.app (Term.instantiate n (Term.shiftBy 0 n arg') f)
              (Term.instantiate n (Term.shiftBy 0 n arg) x))
            (.app (Term.instantiate n (Term.shiftBy 0 n arg') f)
              (Term.instantiate n (Term.shiftBy 0 n arg') x)) :=
        MEqRedStar.app_right hFInstConc' hArgChainFlat hpvConc
      simpa [Term.instantiate] using
        Relation.ReflTransGen.trans hStarOp hStarArg
  | abs b0 innerBody ihBound ihInner =>
      intro n Γ arg arg' heads s hlen hBody hArg hArg' hpvSrc hLift
      have hBoundScoped : Term.Scoped (Γ.depth + n + 1) b0 :=
        (Term.Scoped.abs_inv hBody).1
      have hInnerScoped : Term.Scoped (Γ.depth + n + 1 + 1) innerBody :=
        (Term.Scoped.abs_inv hBody).2
      have hInnerScoped' : Term.Scoped (Γ.depth + (n + 1) + 1) innerBody := by
        simpa [Nat.add_assoc] using hInnerScoped
      -- Conclusion-side prevalid (after substitution).
      have hpvConc :
          PrevalidExt (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
            (Stack.instantiate n (Term.shiftBy 0 n arg) s) :=
        BetaInstantiationPreservesPrevalidExtUnderHeadsOfScoped
          (n := n) hlen hArg hpvSrc
      -- Shifted argument scoping.
      have hArgShifted : Term.Scoped (Γ.depth + n)
          (Term.shiftBy 0 n arg) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 n Γ.depth arg (Nat.zero_le _) hArg
      have hArg'Shifted : Term.Scoped (Γ.depth + n)
          (Term.shiftBy 0 n arg') := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Term.shiftBy_scoped 0 n Γ.depth arg' (Nat.zero_le _) hArg'
      -- Substituted bound scoping.
      have hBoundInst : Term.Scoped (Γ.depth + n)
          (Term.instantiate n (Term.shiftBy 0 n arg) b0) :=
        Term.instantiate_scoped n (Γ.depth + n)
          (Term.shiftBy 0 n arg) b0 (by omega) hArgShifted hBoundScoped
      have hBoundInst' : Term.Scoped (Γ.depth + n)
          (Term.instantiate n (Term.shiftBy 0 n arg') b0) :=
        Term.instantiate_scoped n (Γ.depth + n)
          (Term.shiftBy 0 n arg') b0 (by omega) hArg'Shifted hBoundScoped
      have hConcDepth :
          Ctx.depth (Ctx.instantiateBetaPrefix arg n heads ++ Γ) =
            Γ.depth + n := by
        show List.length (Ctx.instantiateBetaPrefix arg n heads ++ Γ) =
          List.length Γ + n
        rw [List.length_append, Ctx.length_instantiateBetaPrefix, hlen]
        omega
      have hBoundInstConc : Term.Scoped
          (Ctx.depth (Ctx.instantiateBetaPrefix arg n heads ++ Γ))
          (Term.instantiate n (Term.shiftBy 0 n arg) b0) := by
        simpa [hConcDepth] using hBoundInst
      have hBoundInstConc' : Term.Scoped
          (Ctx.depth (Ctx.instantiateBetaPrefix arg n heads ++ Γ))
          (Term.instantiate n (Term.shiftBy 0 n arg') b0) := by
        simpa [hConcDepth] using hBoundInst'
      -- Source-side prevalid for the bound IH at empty stack.
      have hpvSrcNil :
          PrevalidExt (heads ++ { bound := arg, kind := .sub } :: Γ) [] :=
        PrevalidExt.nil (PrevalidExt.ctx hpvSrc)
      -- IH on bound at level n with empty stack.
      have hBoundChain :
          MEqRedStar (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
            (Stack.instantiate n (Term.shiftBy 0 n arg) [])
            (Term.instantiate n (Term.shiftBy 0 n arg) b0)
            (Term.instantiate n (Term.shiftBy 0 n arg') b0) :=
        ihBound n hlen hBoundScoped hArg hArg' hpvSrcNil hLift
      have hBoundChainFlat :
          MEqRedStar (Ctx.instantiateBetaPrefix arg n heads ++ Γ) []
            (Term.instantiate n (Term.shiftBy 0 n arg) b0)
            (Term.instantiate n (Term.shiftBy 0 n arg') b0) := by
        simpa [Stack.instantiate] using hBoundChain
      -- Source-side prevalid setup for the innerBody IH.
      have hpvSrcCtx : Prevalid (heads ++ { bound := arg, kind := .sub } :: Γ) :=
        PrevalidExt.ctx hpvSrc
      have hSrcDepth :
          Ctx.depth (heads ++ { bound := arg, kind := .sub } :: Γ) =
            Γ.depth + n + 1 := by
        show List.length (heads ++ { bound := arg, kind := .sub } :: Γ) =
          List.length Γ + n + 1
        rw [List.length_append, List.length_cons, hlen]; omega
      have hpvSrcCtxBound :
          Prevalid ({ bound := b0, kind := .sub } ::
            heads ++ { bound := arg, kind := .sub } :: Γ) := by
        have hBoundInSrc : Term.Scoped
            (Ctx.depth (heads ++ { bound := arg, kind := .sub } :: Γ)) b0 := by
          rw [hSrcDepth]; exact hBoundScoped
        exact Prevalid.sub hpvSrcCtx hBoundInSrc
      have hHeadsInnerLen :
          ({ bound := b0, kind := .sub } :: heads : Ctx).length = n + 1 := by
        simp [hlen]
      have hShiftSucc :
          Term.shiftBy 0 (n + 1) arg =
            Term.shift 0 (Term.shiftBy 0 n arg) := by
        have h := Term.shiftBy_compose 0 n 1 arg
        simpa [Term.shift] using h.symm
      have hShiftSucc' :
          Term.shiftBy 0 (n + 1) arg' =
            Term.shift 0 (Term.shiftBy 0 n arg') := by
        have h := Term.shiftBy_compose 0 n 1 arg'
        simpa [Term.shift] using h.symm
      have hCtxSucc :
          Ctx.instantiateBetaPrefix arg (n + 1)
            ({ bound := b0, kind := .sub } :: heads) =
          { bound := Term.instantiate n (Term.shiftBy 0 n arg) b0,
            kind := .sub } ::
            Ctx.instantiateBetaPrefix arg n heads := by
        simp [Ctx.instantiateBetaPrefix]
      -- Source stack split: outer empty vs cons.
      cases s with
      | nil =>
          -- Outer empty: use Me-Fun chain congruences.
          have hpvNil :
              PrevalidExt (Ctx.instantiateBetaPrefix arg n heads ++ Γ) [] := by
            simpa [Stack.instantiate] using hpvConc
          have hpvSrcInner :
              PrevalidExt
                (({ bound := b0, kind := .sub } :: heads) ++
                  { bound := arg, kind := .sub } :: Γ) [] := by
            have h : Prevalid ({ bound := b0, kind := .sub } ::
                heads ++ { bound := arg, kind := .sub } :: Γ) :=
              hpvSrcCtxBound
            have : PrevalidExt
                ({ bound := b0, kind := .sub } ::
                  heads ++ { bound := arg, kind := .sub } :: Γ) [] :=
              PrevalidExt.nil h
            simpa [List.cons_append] using this
          have hInnerChain := ihInner (n + 1)
            (heads := { bound := b0, kind := .sub } :: heads)
            (s := [])
            hHeadsInnerLen hInnerScoped' hArg hArg' hpvSrcInner hLift
          have hInnerReady :
              MEqRedStar
                  (({ bound := Term.instantiate n (Term.shiftBy 0 n arg) b0, kind := .sub } : CtxEntry) ::
                    (Ctx.instantiateBetaPrefix arg n heads ++ Γ))
                []
                (Term.instantiate (n + 1)
                  (Term.shiftBy 0 (n + 1) arg) innerBody)
                (Term.instantiate (n + 1)
                  (Term.shiftBy 0 (n + 1) arg') innerBody) := by
            rw [hCtxSucc] at hInnerChain
            simpa [Stack.instantiate, List.cons_append] using hInnerChain
          have hInnerReady' :
              MEqRedStar
                  (({ bound := Term.instantiate n (Term.shiftBy 0 n arg') b0, kind := .sub } : CtxEntry) ::
                    (Ctx.instantiateBetaPrefix arg n heads ++ Γ))
                []
                (Term.instantiate (n + 1)
                  (Term.shiftBy 0 (n + 1) arg) innerBody)
                (Term.instantiate (n + 1)
                  (Term.shiftBy 0 (n + 1) arg') innerBody) :=
            MEqRedStar.sub_head_replace_star hInnerReady hBoundChainFlat
          have hInnerInstScoped : Term.Scoped (Γ.depth + n + 1)
              (Term.instantiate (n + 1)
                (Term.shiftBy 0 (n + 1) arg) innerBody) := by
            have hShiftScoped : Term.Scoped (Γ.depth + n + 1)
                (Term.shiftBy 0 (n + 1) arg) := by
              have h := Term.shiftBy_scoped 0 (n + 1) Γ.depth arg
                (Nat.zero_le _) hArg
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
            exact Term.instantiate_scoped (n + 1) (Γ.depth + n + 1)
              (Term.shiftBy 0 (n + 1) arg) innerBody (by omega)
              hShiftScoped (by simpa [Nat.add_assoc] using hInnerScoped')
          have hBoundFixedBody :
              MEqRedStar (Ctx.instantiateBetaPrefix arg n heads ++ Γ) []
                (.abs (Term.instantiate n (Term.shiftBy 0 n arg) b0)
                  (Term.instantiate (n + 1)
                    (Term.shiftBy 0 (n + 1) arg) innerBody))
                (.abs (Term.instantiate n (Term.shiftBy 0 n arg') b0)
                  (Term.instantiate (n + 1)
                    (Term.shiftBy 0 (n + 1) arg) innerBody)) := by
            apply meqRedStar_abs_fun_bound_fixed_body
              (Γ := Ctx.instantiateBetaPrefix arg n heads ++ Γ)
              (bound := Term.instantiate n (Term.shiftBy 0 n arg) b0)
              (bound' := Term.instantiate n (Term.shiftBy 0 n arg') b0)
              (body := Term.instantiate (n + 1)
                (Term.shiftBy 0 (n + 1) arg) innerBody)
              hpvNil ?_ hBoundChainFlat
            show Term.Scoped
                (Ctx.depth ({bound := Term.instantiate n (Term.shiftBy 0 n arg) b0,
                             kind := .sub} ::
                  (Ctx.instantiateBetaPrefix arg n heads ++ Γ)))
                (Term.instantiate (n + 1)
                  (Term.shiftBy 0 (n + 1) arg) innerBody)
            have hDepthEq :
                Ctx.depth ({bound := Term.instantiate n (Term.shiftBy 0 n arg) b0,
                            kind := .sub} ::
                  (Ctx.instantiateBetaPrefix arg n heads ++ Γ)) =
                  Γ.depth + n + 1 := by
              show List.length _ = _
              simp [Ctx.depth, hConcDepth]; omega
            rw [hDepthEq]
            exact hInnerInstScoped
          have hBodyFixedBound :
              MEqRedStar (Ctx.instantiateBetaPrefix arg n heads ++ Γ) []
                (.abs (Term.instantiate n (Term.shiftBy 0 n arg') b0)
                  (Term.instantiate (n + 1)
                    (Term.shiftBy 0 (n + 1) arg) innerBody))
                (.abs (Term.instantiate n (Term.shiftBy 0 n arg') b0)
                  (Term.instantiate (n + 1)
                    (Term.shiftBy 0 (n + 1) arg') innerBody)) :=
            meqRedStar_abs_fun_body_fixed_bound hpvNil hBoundInstConc'
              hInnerReady'
          have hStarOuter :
              MEqRedStar (Ctx.instantiateBetaPrefix arg n heads ++ Γ) []
                (.abs (Term.instantiate n (Term.shiftBy 0 n arg) b0)
                  (Term.instantiate (n + 1)
                    (Term.shiftBy 0 (n + 1) arg) innerBody))
                (.abs (Term.instantiate n (Term.shiftBy 0 n arg') b0)
                  (Term.instantiate (n + 1)
                    (Term.shiftBy 0 (n + 1) arg') innerBody)) :=
            Relation.ReflTransGen.trans hBoundFixedBody hBodyFixedBound
          simpa [Term.instantiate, Stack.instantiate, hShiftSucc, hShiftSucc']
            using hStarOuter
      | cons αSrc restSrc =>
          -- Outer source stack `αSrc :: restSrc`. Conclusion is
          -- `inst-α :: inst-rest`. Use Me-FOp chain congruences.
          have hαSrcScoped : Term.Scoped
              (Ctx.depth (heads ++ { bound := arg, kind := .sub } :: Γ))
              αSrc := PrevalidExt.head_scoped hpvSrc
          have hpvSrcRest : PrevalidExt
              (heads ++ { bound := arg, kind := .sub } :: Γ) restSrc :=
            PrevalidExt.tail hpvSrc
          have hαSrcScopedSrc : Term.Scoped (Γ.depth + n + 1) αSrc := by
            rw [hSrcDepth] at hαSrcScoped; exact hαSrcScoped
          -- Body source stack at level n+1: shift 0 of restSrc, kept in
          -- the augmented context (.sub bound :: heads ++ ...).
          have hpvSrcInner :
              PrevalidExt
                (({ bound := b0, kind := .sub } :: heads) ++
                  { bound := arg, kind := .sub } :: Γ)
                (Stack.shift 0 restSrc) := by
            have h : PrevalidExt
                ({ bound := b0, kind := .sub } ::
                  heads ++ { bound := arg, kind := .sub } :: Γ)
                (Stack.shift 0 restSrc) :=
              PrevalidExt.weaken_head hpvSrcRest hpvSrcCtxBound
            simpa [List.cons_append] using h
          have hInnerChain := ihInner (n + 1)
            (heads := { bound := b0, kind := .sub } :: heads)
            (s := Stack.shift 0 restSrc)
            hHeadsInnerLen hInnerScoped' hArg hArg' hpvSrcInner hLift
          -- Reshape stack: instantiate (n+1) (shift 0 (shifted arg)) (shift 0 restSrc)
          -- = shift 0 (instantiate n (shifted arg) restSrc).
          have hStackBodyEq :
              Stack.instantiate (n + 1)
                  (Term.shiftBy 0 (n + 1) arg) (Stack.shift 0 restSrc) =
                Stack.shift 0
                  (Stack.instantiate n (Term.shiftBy 0 n arg) restSrc) := by
            rw [hShiftSucc]
            exact Stack.instantiate_succ_shift_zero n
              (Term.shiftBy 0 n arg) restSrc
          have hInnerReady :
              MEqRedStar
                  (({ bound := Term.instantiate n (Term.shiftBy 0 n arg) b0, kind := .sub } : CtxEntry) ::
                    (Ctx.instantiateBetaPrefix arg n heads ++ Γ))
                (Stack.shift 0
                  (Stack.instantiate n (Term.shiftBy 0 n arg) restSrc))
                (Term.instantiate (n + 1)
                  (Term.shiftBy 0 (n + 1) arg) innerBody)
                (Term.instantiate (n + 1)
                  (Term.shiftBy 0 (n + 1) arg') innerBody) := by
            rw [hCtxSucc] at hInnerChain
            rw [hStackBodyEq] at hInnerChain
            simpa [List.cons_append] using hInnerChain
          have hInnerReady' :
              MEqRedStar
                  (({ bound := Term.instantiate n (Term.shiftBy 0 n arg') b0, kind := .sub } : CtxEntry) ::
                    (Ctx.instantiateBetaPrefix arg n heads ++ Γ))
                (Stack.shift 0
                  (Stack.instantiate n (Term.shiftBy 0 n arg) restSrc))
                (Term.instantiate (n + 1)
                  (Term.shiftBy 0 (n + 1) arg) innerBody)
                (Term.instantiate (n + 1)
                  (Term.shiftBy 0 (n + 1) arg') innerBody) :=
            MEqRedStar.sub_head_replace_star hInnerReady hBoundChainFlat
          -- Conclusion-stack outer prevalids.
          have hpvConcCons : PrevalidExt
              (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
              (Term.instantiate n (Term.shiftBy 0 n arg) αSrc ::
                Stack.instantiate n (Term.shiftBy 0 n arg) restSrc) := by
            simpa [Stack.instantiate] using hpvConc
          have hαConc : Term.Scoped
              (Ctx.depth (Ctx.instantiateBetaPrefix arg n heads ++ Γ))
              (Term.instantiate n (Term.shiftBy 0 n arg) αSrc) :=
            PrevalidExt.head_scoped hpvConcCons
          have hpvConcTail : PrevalidExt
              (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
              (Stack.instantiate n (Term.shiftBy 0 n arg) restSrc) :=
            PrevalidExt.tail hpvConcCons
          have hInnerInstScoped : Term.Scoped (Γ.depth + n + 1)
              (Term.instantiate (n + 1)
                (Term.shiftBy 0 (n + 1) arg) innerBody) := by
            have hShiftScoped : Term.Scoped (Γ.depth + n + 1)
                (Term.shiftBy 0 (n + 1) arg) := by
              have h := Term.shiftBy_scoped 0 (n + 1) Γ.depth arg
                (Nat.zero_le _) hArg
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
            exact Term.instantiate_scoped (n + 1) (Γ.depth + n + 1)
              (Term.shiftBy 0 (n + 1) arg) innerBody (by omega)
              hShiftScoped (by simpa [Nat.add_assoc] using hInnerScoped')
          -- meqRedStar_abs_fOp_bound_fixed_body wants stack rest, body fixed.
          have hBoundFixedBodyFOp :
              MEqRedStar (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
                (Term.instantiate n (Term.shiftBy 0 n arg) αSrc ::
                  Stack.instantiate n (Term.shiftBy 0 n arg) restSrc)
                (.abs (Term.instantiate n (Term.shiftBy 0 n arg) b0)
                  (Term.instantiate (n + 1)
                    (Term.shiftBy 0 (n + 1) arg) innerBody))
                (.abs (Term.instantiate n (Term.shiftBy 0 n arg') b0)
                  (Term.instantiate (n + 1)
                    (Term.shiftBy 0 (n + 1) arg) innerBody)) := by
            apply meqRedStar_abs_fOp_bound_fixed_body
              (Γ := Ctx.instantiateBetaPrefix arg n heads ++ Γ)
              (s := Stack.instantiate n (Term.shiftBy 0 n arg) restSrc)
              (α := Term.instantiate n (Term.shiftBy 0 n arg) αSrc)
              (bound := Term.instantiate n (Term.shiftBy 0 n arg) b0)
              (bound' := Term.instantiate n (Term.shiftBy 0 n arg') b0)
              (body := Term.instantiate (n + 1)
                (Term.shiftBy 0 (n + 1) arg) innerBody)
              hpvConcTail hαConc ?_ hBoundChainFlat
            have hDepthEq :
                Ctx.depth ({bound := Term.instantiate n (Term.shiftBy 0 n arg) αSrc,
                            kind := .equ} ::
                  (Ctx.instantiateBetaPrefix arg n heads ++ Γ)) =
                  Γ.depth + n + 1 := by
              show List.length _ = _
              simp [Ctx.depth, hConcDepth]; omega
            rw [hDepthEq]
            exact hInnerInstScoped
          -- Convert the body chain from `.sub b0` head to `.equ αSrc` head
          -- via kind narrowing + bound replacement. The kind narrowing is
          -- sound because `.sub`-head Me-Pro at index 0 is impossible (no
          -- equBinds match), so no chain step references the dropped binder
          -- via Me-Pro at index 0.
          have hαSrcInstConc : Term.Scoped
              (Ctx.depth (Ctx.instantiateBetaPrefix arg n heads ++ Γ))
              (Term.instantiate n (Term.shiftBy 0 n arg) αSrc) := hαConc
          -- Star version of MEqRed.sub_to_equ_head_replace.
          have hInnerReadyEqu :
              MEqRedStar
                  (({ bound := Term.instantiate n (Term.shiftBy 0 n arg) αSrc,
                      kind := .equ } : CtxEntry) ::
                    (Ctx.instantiateBetaPrefix arg n heads ++ Γ))
                (Stack.shift 0
                  (Stack.instantiate n (Term.shiftBy 0 n arg) restSrc))
                (Term.instantiate (n + 1)
                  (Term.shiftBy 0 (n + 1) arg) innerBody)
                (Term.instantiate (n + 1)
                  (Term.shiftBy 0 (n + 1) arg') innerBody) :=
            MEqRedStar.argTransport_sub_to_equ_head_replace hInnerReady'
              hαSrcInstConc
          have hBodyFixedBoundFOp :
              MEqRedStar (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
                (Term.instantiate n (Term.shiftBy 0 n arg) αSrc ::
                  Stack.instantiate n (Term.shiftBy 0 n arg) restSrc)
                (.abs (Term.instantiate n (Term.shiftBy 0 n arg') b0)
                  (Term.instantiate (n + 1)
                    (Term.shiftBy 0 (n + 1) arg) innerBody))
                (.abs (Term.instantiate n (Term.shiftBy 0 n arg') b0)
                  (Term.instantiate (n + 1)
                    (Term.shiftBy 0 (n + 1) arg') innerBody)) :=
            meqRedStar_abs_fOp_body_fixed_bound hpvConcTail hBoundInstConc'
              hαConc hInnerReadyEqu
          have hStarOuter :
              MEqRedStar (Ctx.instantiateBetaPrefix arg n heads ++ Γ)
                (Term.instantiate n (Term.shiftBy 0 n arg) αSrc ::
                  Stack.instantiate n (Term.shiftBy 0 n arg) restSrc)
                (.abs (Term.instantiate n (Term.shiftBy 0 n arg) b0)
                  (Term.instantiate (n + 1)
                    (Term.shiftBy 0 (n + 1) arg) innerBody))
                (.abs (Term.instantiate n (Term.shiftBy 0 n arg') b0)
                  (Term.instantiate (n + 1)
                    (Term.shiftBy 0 (n + 1) arg') innerBody)) :=
            Relation.ReflTransGen.trans hBoundFixedBodyFOp hBodyFixedBoundFOp
          simpa [Term.instantiate, Stack.instantiate, hShiftSucc, hShiftSucc']
            using hStarOuter

/-! ## `StrongCommutes` β-position chain-output cells

These are the de Bruijn Lemma 1 (`StrongCommutes`) β-position cells with
chain output, the analog of `EqDiamonds.bet_*_chain_of` cells but for the
asymmetric `MSubRed × MEqRed` shape.

`MSubRed`'s constructors at an `.app (.abs t body) v` source are:
- `Ms-Top` (target `.top`)
- `Ms-Equ` (wraps an `MEqRed` step at the source)
- `Ms-App` (operator step at stack `(v :: s)`)

There is no direct `Ms-Bet` constructor — β-fires on the subtype side go
through `Ms-Equ` wrapping `Me-Bet`. So the β-position cells here are:

- `equ_bet_chain_of`: `Ms-Equ` wrapping a source `Me-*` step paired with
  `Me-Bet`. Delegates to `EqDiamonds.bet_bet_chain_of` /
  `app_bet_chain_of` based on which `Me-*` constructor the wrap holds.

- `app_bet_chain_of`: `Ms-App` (genuine subtype operator progression at
  stack `(v :: s)`) paired with `Me-Bet`. The operator step is one of
  `Ms-Top` (target `.top`, closes at `.top`), `Ms-Equ` (delegates to
  `EqDiamonds.app_bet_chain_of`), or `Ms-FOp` (β-fire LHS post-step
  via `Me-Bet` and use a `.sub`-head bridging hypothesis).

Both cells return `MEqRedStar t₁ t₃ ∧ MSubRedStar t₂ t₃` (the
`StrongCommutesChain` shape), which mirrors `EqDiamonds`'s chain output
but with `MSubRedStar` on the second component (the RHS-side post-step
chain). The Me-side chain is recovered directly from the EqDiamonds
delegate; the Ms-side chain is converted from the EqDiamonds chain via
`MSubRedStar.of_MEqRedStar`. -/

/-- Chain-output strong commutativity at a fixed extended context. The
de Bruijn Lemma 1 shape needed by chain-output close arguments
analogous to the `EqDiamonds` chain-output cells. -/
abbrev StrongCommutesChain (Γ : Ctx) (s : Stack) : Prop :=
  ∀ {t₀ t₁ t₂ : Term},
    MSubRed Γ s t₀ t₁ →
    MEqRed Γ s t₀ t₂ →
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃

namespace StrongCommutes

/-- The `Ms-Equ × Me-Bet` β-position cell of de Bruijn Lemma 1 with
chain output. The LHS subtype step wraps an `MEqRed` step from the
β-redex source; the RHS is `Me-Bet`. The wrapped `MEqRed` step at
source `.app (.abs t body) v` can only be `Me-Bet` or `Me-App`
(structurally — `.app` heads do not match `Me-Pro`/`Me-Var`/`Me-Top`/
`Me-Fun`/`Me-FOp`/`Me-TAp` here). Each sub-case delegates to the
matching `EqDiamonds.*_chain_of` cell, and the RHS `MEqRedStar` chain
is wrapped into `MSubRedStar` via `MSubRedStar.of_MEqRedStar`.

Conditional on the same payloads as the underlying `EqDiamonds.bet_bet_chain_of`
and `EqDiamonds.app_bet_chain_of` cells. The bridge `hBody₁Sub` matches
`EqDiamonds.app_bet_chain_of`'s `hBody₁Sub` shape exactly, parameterised
in the post-step operator-application target. -/
theorem equ_bet_chain_of
    (hArgTransport : MEqRedArgTransportPayload)
    {Γ : Ctx} {s : Stack} {t v body body₂' v₂' t₁ : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hpv : PrevalidExt Γ s)
    (hMEqLHS : MEqRed Γ s (.app (.abs t body) v) t₁)
    (hBody₂ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂')
    (hArg₂ : MEqRed Γ [] v v₂')
    (hAppBodyOpSubBridge :
      ∀ {hOp₁_target body₁' t' : Term},
        MEqRed Γ (v :: s) (.abs t body) hOp₁_target →
        hOp₁_target = .abs t' body₁' →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₁') :
    ∃ t₃,
      MEqRedStar Γ s t₁ t₃
      ∧ MSubRedStar Γ s (Term.instantiate 0 v₂' body₂') t₃ := by
  cases hMEqLHS with
  | bet ht₁ hBody₁ hArg₁ =>
    -- LHS β-fires too: delegate to EqDiamonds.bet_bet_chain_of.
    obtain ⟨t₃, hLeft, hRight⟩ :=
      EqDiamonds.bet_bet_chain_of hArgTransport hBodyDiamond hArgDiamond
        ht hBody₁ hArg₁ hBody₂ hArg₂
    refine ⟨t₃, hLeft, ?_⟩
    exact MSubRedStar.of_MEqRedStar hpv hRight
  | app hOp₁ hArg₁ =>
    -- LHS app-fires: delegate to EqDiamonds.app_bet_chain_of.
    obtain ⟨t₃, hLeft, hRight⟩ :=
      EqDiamonds.app_bet_chain_of hArgTransport hBodyDiamond hArgDiamond
        ht hOp₁ hArg₁ hBody₂ hArg₂
        (fun {body₁' t'} hShape => hAppBodyOpSubBridge hOp₁ hShape)
    refine ⟨t₃, hLeft, ?_⟩
    exact MSubRedStar.of_MEqRedStar hpv hRight

/-- The `Ms-App × Me-Bet` β-position cell of de Bruijn Lemma 1 with
chain output. The LHS is a genuine subtype operator-progression step
at stack `(v :: s)`; the RHS β-fires.

Cases on the operator-step constructor (`MSubRed Γ (v :: s) (.abs t body) op'`):

- `Ms-Top`: `op' = .top`. Both sides reach `.top`: LHS `.app .top v` via
  `Me-TAp`; RHS `Term.instantiate 0 v₂' body₂'` via `Ms-Top` at
  scope `Γ.depth`.
- `Ms-Equ`: wraps an `MEqRed` operator step. Combined with refl on
  the operand, this is an `Me-App × Me-Bet` source — delegate to
  `EqDiamonds.app_bet_chain_of` and convert RHS via
  `MSubRedStar.of_MEqRedStar`.
- `Ms-FOp`: `op' = .abs t bodyOp'` with body in `.equ`-head bound `v`.
  β-fire LHS post-step `.app (.abs t bodyOp') v` directly; close via
  the body diamond + arg diamond + transport bridges, using the
  caller-supplied `.sub`-head bridge for the operator step's `.equ`-head
  body derivation.

Conditional on:
- `MEqRedArgTransportPayload`,
- A body diamond (at `.sub`-head bound `t`) and arg diamond,
- A general `.sub`-head bridging hypothesis matching
  `EqDiamonds.app_bet_chain_of`'s `hBody₁Sub`. This handles BOTH the
  `Ms-FOp` case (where the post-step bound is `t` since `Ms-FOp` keeps
  the bound fixed) and the `Ms-Equ` case wrapping `Me-FOp` (where the
  post-step bound `t'` may differ from `t`).

The bridge hypothesis is parametric in the post-step bound and body so
the bridging works uniformly across the two `.abs`-shape cases. -/
theorem app_bet_chain_of
    (hArgTransport : MEqRedArgTransportPayload)
    {Γ : Ctx} {s : Stack} {t v body body₂' v₂' op' : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hv : Term.Scoped Γ.depth v)
    (hOp : MSubRed Γ (v :: s) (.abs t body) op')
    (hBody₂ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂')
    (hArg₂ : MEqRed Γ [] v v₂')
    (hBodyOpSubBridge :
      ∀ {body' t' : Term},
        op' = .abs t' body' →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
          body body') :
    ∃ t₃,
      MEqRedStar Γ s (.app op' v) t₃
      ∧ MSubRedStar Γ s (Term.instantiate 0 v₂' body₂') t₃ := by
  -- Recover prevalidities and scopings.
  have hpvCons : PrevalidExt Γ (v :: s) := hOp.prevalidExt
  have hpv : PrevalidExt Γ s := PrevalidExt.tail hpvCons
  cases hOp with
  | top _ _ =>
    -- op' = .top. Both sides reach .top.
    -- LHS chain: .app .top v →[Me-TAp] .top.
    have hMeTAp : MEqRed Γ s (.app .top v) .top := MEqRed.tAp hpv hv
    -- RHS chain: instantiate 0 v₂' body₂' →[Ms-Top] .top.
    have hv₂' : Term.Scoped Γ.depth v₂' := hArg₂.scoped_right
    have hBody₂Scoped : Term.Scoped (Γ.depth + 1) body₂' := by
      simpa [Ctx.depth] using hBody₂.scoped_right
    have hInstScoped :
        Term.Scoped Γ.depth (Term.instantiate 0 v₂' body₂') :=
      Term.instantiate_scoped 0 _ _ _ (Nat.zero_le _) hv₂' hBody₂Scoped
    have hMsTop :
        MSubRed Γ s (Term.instantiate 0 v₂' body₂') .top :=
      MSubRed.top hpv hInstScoped
    refine ⟨.top, MEqRedStar.single hMeTAp, MSubRedStar.single hMsTop⟩
  | equ _ hMEqOp =>
    -- op' is the target of an MEqRed operator step. Build an Me-App on
    -- LHS via refl on the operand and delegate to
    -- EqDiamonds.app_bet_chain_of. The bridge hypothesis flows through
    -- unchanged: it has the EqDiamonds shape `op' = .abs t' body' →
    -- MEqRed (.sub-head bound t) body body'`.
    have hpvNil : PrevalidExt Γ [] :=
      PrevalidExt.nil (PrevalidExt.ctx hpv)
    have hArgRefl : MEqRed Γ [] v v := MEqRed.refl hpvNil hv
    obtain ⟨t₃, hLeft, hRight⟩ :=
      EqDiamonds.app_bet_chain_of hArgTransport hBodyDiamond hArgDiamond
        ht hMEqOp hArgRefl hBody₂ hArg₂
        (fun {body₁' t'} hShape => hBodyOpSubBridge hShape)
    refine ⟨t₃, hLeft, ?_⟩
    exact MSubRedStar.of_MEqRedStar hpv hRight
  | fOp htOp hαOp hBodySub =>
    -- op' = .abs t bodyOp', body sub-chain at `.equ`-head bound `v`
    -- (Ms-FOp keeps the bound `t` fixed). The bridge hypothesis at
    -- shape `op' = .abs t bodyOp'` provides a `.sub`-head MEqRed
    -- derivation `body → bodyOp'`.
    rename_i bodyOp'
    have hBodyOpSubBridged :
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
          body bodyOp' :=
      hBodyOpSubBridge rfl
    -- Body diamond: bodyOp' joins body₂' at body₃ in `.sub`-head.
    obtain ⟨body₃, hBody₁₃J, hBody₂₃J⟩ :=
      hBodyDiamond hBodyOpSubBridged hBody₂
    let hBody₁₃ :
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
          bodyOp' body₃ := hBody₁₃J.some
    let hBody₂₃ :
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
          body₂' body₃ := hBody₂₃J.some
    -- Arg diamond: refl(v) and `v → v₂'` join at some v₃.
    have hpvNil : PrevalidExt Γ [] :=
      PrevalidExt.nil (PrevalidExt.ctx hpv)
    have hArgRefl : MEqRed Γ [] v v := MEqRed.refl hpvNil hv
    obtain ⟨v₃, hArg₁₃J, hArg₂₃J⟩ := hArgDiamond hArgRefl hArg₂
    let hArg₁₃ : MEqRed Γ [] v v₃ := hArg₁₃J.some
    let hArg₂₃ : MEqRed Γ [] v₂' v₃ := hArg₂₃J.some
    refine ⟨Term.instantiate 0 v₃ body₃, ?_, ?_⟩
    · -- LHS chain: .app (.abs t bodyOp') v →[Me-Bet]
      --              instantiate 0 v bodyOp'
      --            →[fused-narrow] instantiate 0 v body₃
      --            →* instantiate 0 v₃ body₃ (via arg-transport).
      have hPrevalidT :
          Prevalid ({bound := t, kind := .sub} :: Γ) :=
        Prevalid.sub (PrevalidExt.ctx hpv) ht
      have hpvBodyT :
          PrevalidExt ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) :=
        PrevalidExt.weaken_head hpv hPrevalidT
      have hBodyOp'Scoped : Term.Scoped (Γ.depth + 1) bodyOp' := by
        simpa [Ctx.depth] using hBodyOpSubBridged.scoped_right
      have hBodyOp'Scoped_t :
          Term.Scoped
            (Ctx.depth ({bound := t, kind := .sub} :: Γ)) bodyOp' := by
        simpa [Ctx.depth, Nat.succ_eq_add_one] using hBodyOp'Scoped
      have hBodyReflT :
          MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
            bodyOp' bodyOp' :=
        MEqRed.refl hpvBodyT hBodyOp'Scoped_t
      have hArgReflv : MEqRed Γ [] v v := MEqRed.refl hpvNil hv
      have hβStep :
          MEqRed Γ s (.app (.abs t bodyOp') v)
            (Term.instantiate 0 v bodyOp') :=
        MEqRed.bet ht hBodyReflT hArgReflv
      have hBodyProgress :
          MEqRed Γ (Stack.instantiate 0 v (Stack.shift 0 s))
            (Term.instantiate 0 v bodyOp')
            (Term.instantiate 0 v body₃) :=
        MEqRedFusedKindNarrowedBetaSubstStack_proved
          (arg := t) (arg' := v) ht hv hBody₁₃
      have hStackEq :
          Stack.instantiate 0 v (Stack.shift 0 s) = s :=
        Stack.instantiate_zero_shift_zero_id v s
      have hBodyProgress' :
          MEqRed Γ s
            (Term.instantiate 0 v bodyOp')
            (Term.instantiate 0 v body₃) := by
        simpa [hStackEq] using hBodyProgress
      have hBody₃Scoped : Term.Scoped (Γ.depth + 1) body₃ := by
        simpa [Ctx.depth] using hBody₁₃.scoped_right
      have hArgChain :
          MEqRedStar Γ s
            (Term.instantiate 0 v body₃)
            (Term.instantiate 0 v₃ body₃) :=
        hArgTransport hBody₃Scoped hArg₁₃ hpv
      exact ((MEqRedStar.single hβStep).trans
        (MEqRedStar.single hBodyProgress')).trans hArgChain
    · -- RHS chain: instantiate 0 v₂' body₂' →[fused-narrow]
      --               instantiate 0 v₂' body₃
      --            →* instantiate 0 v₃ body₃ (via arg-transport),
      -- then wrap into MSubRedStar via Ms-Equ.
      have hv₂'Scoped : Term.Scoped Γ.depth v₂' := hArg₂.scoped_right
      have hBodyProgress :
          MEqRed Γ (Stack.instantiate 0 v₂' (Stack.shift 0 s))
            (Term.instantiate 0 v₂' body₂')
            (Term.instantiate 0 v₂' body₃) :=
        MEqRedFusedKindNarrowedBetaSubstStack_proved
          (arg := t) (arg' := v₂') ht hv₂'Scoped hBody₂₃
      have hStackEq :
          Stack.instantiate 0 v₂' (Stack.shift 0 s) = s :=
        Stack.instantiate_zero_shift_zero_id v₂' s
      have hBodyProgress' :
          MEqRed Γ s
            (Term.instantiate 0 v₂' body₂')
            (Term.instantiate 0 v₂' body₃) := by
        simpa [hStackEq] using hBodyProgress
      have hBody₃Scoped : Term.Scoped (Γ.depth + 1) body₃ := by
        simpa [Ctx.depth] using hBody₂₃.scoped_right
      have hArgChain :
          MEqRedStar Γ s
            (Term.instantiate 0 v₂' body₃)
            (Term.instantiate 0 v₃ body₃) :=
        hArgTransport hBody₃Scoped hArg₂₃ hpv
      have hMeRHS :
          MEqRedStar Γ s
            (Term.instantiate 0 v₂' body₂')
            (Term.instantiate 0 v₃ body₃) :=
        (MEqRedStar.single hBodyProgress').trans hArgChain
      exact MSubRedStar.of_MEqRedStar hpv hMeRHS

end StrongCommutes

/-- Argument-transport payload for `NoBinders` arguments with no body-shape
restriction. This is stronger than `MEqRedArgTransportPayloadRestricted` on
the body side: the under-heads argument-transport proof handles abstraction
bodies, while `NoBinders` still supplies the context/stack-parametric lift
for the argument step. -/
def MEqRedArgTransportPayloadNoBinders : Prop :=
  ∀ {Γ : Ctx} {arg arg' body : Term} {s : Stack},
    Term.Scoped (Γ.depth + 1) body →
    Term.NoBinders arg →
    MEqRed Γ [] arg arg' →
    PrevalidExt Γ s →
    MEqRedStar Γ s
      (Term.instantiate 0 arg body)
      (Term.instantiate 0 arg' body)

/-- Closed proof of `MEqRedArgTransportPayloadNoBinders`. -/
theorem MEqRedArgTransportPayloadNoBinders_proved :
    MEqRedArgTransportPayloadNoBinders := by
  intro Γ arg arg' body s hBody hNoBindersArg hArgStep hpv
  have hArgScoped : Term.Scoped Γ.depth arg := hArgStep.scoped_left
  have hArgScoped' : Term.Scoped Γ.depth arg' := hArgStep.scoped_right
  have hNoBindersArg' : Term.NoBinders arg' :=
    hArgStep.preserves_noBinders hNoBindersArg
  have hLift :
      ∀ {n' : Nat} {heads' : Ctx} {s' : Stack},
        heads'.length = n' →
        PrevalidExt (heads' ++ { bound := arg, kind := .sub } :: Γ) s' →
        MEqRedStar (Ctx.instantiateBetaPrefix arg n' heads' ++ Γ)
          (Stack.instantiate n' (Term.shiftBy 0 n' arg) s')
          (Term.shiftBy 0 n' arg) (Term.shiftBy 0 n' arg') := by
    intro n' heads' s' hlen hpvSrc
    have hNoBindersShiftArg :
        Term.shiftBy 0 n' arg = arg :=
      hNoBindersArg.shiftBy_eq 0 n'
    have hNoBindersShiftArg' :
        Term.shiftBy 0 n' arg' = arg' :=
      hNoBindersArg'.shiftBy_eq 0 n'
    have hpvTarget :
        PrevalidExt (Ctx.instantiateBetaPrefix arg n' heads' ++ Γ)
          (Stack.instantiate n' (Term.shiftBy 0 n' arg) s') :=
      BetaInstantiationPreservesPrevalidExtUnderHeadsOfScoped
        (n := n') hlen hArgScoped hpvSrc
    have hLifted :
        MEqRedStar (Ctx.instantiateBetaPrefix arg n' heads' ++ Γ)
          (Stack.instantiate n' (Term.shiftBy 0 n' arg) s')
          arg arg' :=
      MEqRedStar.lift_to_any_context_stack_of_NoBinders
        hArgStep hNoBindersArg hpvTarget
    simpa [hNoBindersShiftArg, hNoBindersShiftArg'] using hLifted
  exact
    MEqRedStarArgTransportStack.of_generic
      (MEqRedStarArgTransportUnderHeadsStack_universal 0)
      hBody hArgScoped hArgScoped' hpv hLift

namespace EqDiamonds

/-- Restricted `Me-Bet × Me-Bet` source cell with only a binder-free
argument-side condition. Unlike `bet_bet_chain_AbsFree_of`, this does not
require an `AbsFree` proof for the joined body: abstraction bodies are
handled by `MEqRedArgTransportPayloadNoBinders_proved`. -/
theorem bet_bet_chain_ArgNoBinders_of
    {Γ : Ctx} {s : Stack} {t v body body₁' body₂' v₁' v₂' : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hVNoBinders : Term.NoBinders v)
    (hBody₁ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₁')
    (hArg₁ : MEqRed Γ [] v v₁')
    (hBody₂ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂')
    (hArg₂ : MEqRed Γ [] v v₂') :
    ∃ t₃,
      MEqRedStar Γ s (Term.instantiate 0 v₁' body₁') t₃
      ∧ MEqRedStar Γ s (Term.instantiate 0 v₂' body₂') t₃ := by
  obtain ⟨body₃, hBody₁₃J, hBody₂₃J⟩ := hBodyDiamond hBody₁ hBody₂
  obtain ⟨v₃, hArg₁₃J, hArg₂₃J⟩ := hArgDiamond hArg₁ hArg₂
  let hBody₁₃ : MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
    body₁' body₃ := hBody₁₃J.some
  let hBody₂₃ : MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
    body₂' body₃ := hBody₂₃J.some
  let hArg₁₃ : MEqRed Γ [] v₁' v₃ := hArg₁₃J.some
  let hArg₂₃ : MEqRed Γ [] v₂' v₃ := hArg₂₃J.some
  have hV₁'NoBinders : Term.NoBinders v₁' :=
    hArg₁.preserves_noBinders hVNoBinders
  have hV₂'NoBinders : Term.NoBinders v₂' :=
    hArg₂.preserves_noBinders hVNoBinders
  refine ⟨Term.instantiate 0 v₃ body₃, ?_, ?_⟩
  · have hv₁'Scoped : Term.Scoped Γ.depth v₁' := hArg₁.scoped_right
    have hBodyProgress :
        MEqRed Γ (Stack.instantiate 0 v₁' (Stack.shift 0 s))
          (Term.instantiate 0 v₁' body₁')
          (Term.instantiate 0 v₁' body₃) :=
      MEqRedFusedKindNarrowedBetaSubstStack_proved
        (arg := t) (arg' := v₁') ht hv₁'Scoped hBody₁₃
    have hStackEq :
        Stack.instantiate 0 v₁' (Stack.shift 0 s) = s :=
      Stack.instantiate_zero_shift_zero_id v₁' s
    have hBodyProgress' :
        MEqRed Γ s
          (Term.instantiate 0 v₁' body₁')
          (Term.instantiate 0 v₁' body₃) := by
      simpa [hStackEq] using hBodyProgress
    have hBody₃Scoped : Term.Scoped (Γ.depth + 1) body₃ := by
      simpa [Ctx.depth] using hBody₁₃.scoped_right
    have hpvΓs : PrevalidExt Γ s :=
      PrevalidExt.weaken_head_inv hBody₁.prevalidExt
    have hArgChain :
        MEqRedStar Γ s
          (Term.instantiate 0 v₁' body₃)
          (Term.instantiate 0 v₃ body₃) :=
      MEqRedArgTransportPayloadNoBinders_proved
        hBody₃Scoped hV₁'NoBinders hArg₁₃ hpvΓs
    exact (MEqRedStar.single hBodyProgress').trans hArgChain
  · have hv₂'Scoped : Term.Scoped Γ.depth v₂' := hArg₂.scoped_right
    have hBodyProgress :
        MEqRed Γ (Stack.instantiate 0 v₂' (Stack.shift 0 s))
          (Term.instantiate 0 v₂' body₂')
          (Term.instantiate 0 v₂' body₃) :=
      MEqRedFusedKindNarrowedBetaSubstStack_proved
        (arg := t) (arg' := v₂') ht hv₂'Scoped hBody₂₃
    have hStackEq :
        Stack.instantiate 0 v₂' (Stack.shift 0 s) = s :=
      Stack.instantiate_zero_shift_zero_id v₂' s
    have hBodyProgress' :
        MEqRed Γ s
          (Term.instantiate 0 v₂' body₂')
          (Term.instantiate 0 v₂' body₃) := by
      simpa [hStackEq] using hBodyProgress
    have hBody₃Scoped : Term.Scoped (Γ.depth + 1) body₃ := by
      simpa [Ctx.depth] using hBody₂₃.scoped_right
    have hpvΓs : PrevalidExt Γ s :=
      PrevalidExt.weaken_head_inv hBody₂.prevalidExt
    have hArgChain :
        MEqRedStar Γ s
          (Term.instantiate 0 v₂' body₃)
          (Term.instantiate 0 v₃ body₃) :=
      MEqRedArgTransportPayloadNoBinders_proved
        hBody₃Scoped hV₂'NoBinders hArg₂₃ hpvΓs
    exact (MEqRedStar.single hBodyProgress').trans hArgChain

/- Restricted `Me-Bet × Me-App` source cell with only a binder-free
argument-side condition. Unlike `bet_app_chain_AbsFree_of`, this does not
require an `AbsFree` proof for the joined body: abstraction bodies are
handled by `MEqRedArgTransportPayloadNoBinders_proved`. -/
theorem bet_app_chain_ArgNoBinders_of
    {Γ : Ctx} {s : Stack} {t v body body₁' v₁' v₂' hOp₂_target : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hVNoBinders : Term.NoBinders v)
    (hBody₁ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₁')
    (hArg₁ : MEqRed Γ [] v v₁')
    (hOp₂ : MEqRed Γ (v :: s) (.abs t body) hOp₂_target)
    (hArg₂ : MEqRed Γ [] v v₂')
    (hBody₂Sub :
      ∀ {body₂' t' : Term},
        hOp₂_target = .abs t' body₂' →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂') :
    ∃ t₃,
      MEqRedStar Γ s (Term.instantiate 0 v₁' body₁') t₃
      ∧ MEqRedStar Γ s (.app hOp₂_target v₂') t₃ := by
  cases hOp₂ with
  | fOp hT₂ hα₂ hBody₂equ =>
    rename_i t' body₂'
    have hBody₂sub :
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂' :=
      hBody₂Sub rfl
    obtain ⟨body₃, hBody₁₃J, hBody₂₃J⟩ := hBodyDiamond hBody₁ hBody₂sub
    obtain ⟨v₃, hArg₁₃J, hArg₂₃J⟩ := hArgDiamond hArg₁ hArg₂
    let hBody₁₃ :
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
          body₁' body₃ := hBody₁₃J.some
    let hBody₂₃ :
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
          body₂' body₃ := hBody₂₃J.some
    let hArg₁₃ : MEqRed Γ [] v₁' v₃ := hArg₁₃J.some
    let hArg₂₃ : MEqRed Γ [] v₂' v₃ := hArg₂₃J.some
    have hV₁'NoBinders : Term.NoBinders v₁' :=
      hArg₁.preserves_noBinders hVNoBinders
    have hV₂'NoBinders : Term.NoBinders v₂' :=
      hArg₂.preserves_noBinders hVNoBinders
    refine ⟨Term.instantiate 0 v₃ body₃, ?_, ?_⟩
    · have hv₁'Scoped : Term.Scoped Γ.depth v₁' := hArg₁.scoped_right
      have hBodyProgress :
          MEqRed Γ (Stack.instantiate 0 v₁' (Stack.shift 0 s))
            (Term.instantiate 0 v₁' body₁')
            (Term.instantiate 0 v₁' body₃) :=
        MEqRedFusedKindNarrowedBetaSubstStack_proved
          (arg := t) (arg' := v₁') ht hv₁'Scoped hBody₁₃
      have hStackEq :
          Stack.instantiate 0 v₁' (Stack.shift 0 s) = s :=
        Stack.instantiate_zero_shift_zero_id v₁' s
      have hBodyProgress' :
          MEqRed Γ s
            (Term.instantiate 0 v₁' body₁')
            (Term.instantiate 0 v₁' body₃) := by
        simpa [hStackEq] using hBodyProgress
      have hBody₃Scoped : Term.Scoped (Γ.depth + 1) body₃ := by
        simpa [Ctx.depth] using hBody₁₃.scoped_right
      have hpvΓs : PrevalidExt Γ s :=
        PrevalidExt.weaken_head_inv hBody₁.prevalidExt
      have hArgChain :
          MEqRedStar Γ s
            (Term.instantiate 0 v₁' body₃)
            (Term.instantiate 0 v₃ body₃) :=
        MEqRedArgTransportPayloadNoBinders_proved
          hBody₃Scoped hV₁'NoBinders hArg₁₃ hpvΓs
      exact (MEqRedStar.single hBodyProgress').trans hArgChain
    · have hpvΓs : PrevalidExt Γ s :=
        PrevalidExt.weaken_head_inv hBody₁.prevalidExt
      have ht' : Term.Scoped Γ.depth t' := hT₂.scoped_right
      have hPrevalidT' :
          Prevalid ({bound := t', kind := .sub} :: Γ) :=
        Prevalid.sub (PrevalidExt.ctx hpvΓs) ht'
      have hpvBody₂t' :
          PrevalidExt ({bound := t', kind := .sub} :: Γ) (Stack.shift 0 s) :=
        PrevalidExt.weaken_head hpvΓs hPrevalidT'
      have hBody₂'Scoped : Term.Scoped (Γ.depth + 1) body₂' := by
        simpa [Ctx.depth] using hBody₂equ.scoped_right
      have hBody₂'Scoped_t' :
          Term.Scoped
            (Ctx.depth ({bound := t', kind := .sub} :: Γ)) body₂' := by
        simpa [Ctx.depth, Nat.succ_eq_add_one] using hBody₂'Scoped
      have hBodyReflT' :
          MEqRed ({bound := t', kind := .sub} :: Γ) (Stack.shift 0 s)
            body₂' body₂' :=
        MEqRed.refl hpvBody₂t' hBody₂'Scoped_t'
      have hv₂'Scoped : Term.Scoped Γ.depth v₂' := hArg₂.scoped_right
      have hpvNil : PrevalidExt Γ [] :=
        PrevalidExt.nil (PrevalidExt.ctx hpvΓs)
      have hArgReflv₂' : MEqRed Γ [] v₂' v₂' :=
        MEqRed.refl hpvNil hv₂'Scoped
      have hβStep :
          MEqRed Γ s (.app (.abs t' body₂') v₂')
            (Term.instantiate 0 v₂' body₂') :=
        MEqRed.bet ht' hBodyReflT' hArgReflv₂'
      have hBodyProgress :
          MEqRed Γ (Stack.instantiate 0 v₂' (Stack.shift 0 s))
            (Term.instantiate 0 v₂' body₂')
            (Term.instantiate 0 v₂' body₃) :=
        MEqRedFusedKindNarrowedBetaSubstStack_proved
          (arg := t) (arg' := v₂') ht hv₂'Scoped hBody₂₃
      have hStackEq :
          Stack.instantiate 0 v₂' (Stack.shift 0 s) = s :=
        Stack.instantiate_zero_shift_zero_id v₂' s
      have hBodyProgress' :
          MEqRed Γ s
            (Term.instantiate 0 v₂' body₂')
            (Term.instantiate 0 v₂' body₃) := by
        simpa [hStackEq] using hBodyProgress
      have hBody₃Scoped : Term.Scoped (Γ.depth + 1) body₃ := by
        simpa [Ctx.depth] using hBody₂₃.scoped_right
      have hArgChain :
          MEqRedStar Γ s
            (Term.instantiate 0 v₂' body₃)
            (Term.instantiate 0 v₃ body₃) :=
        MEqRedArgTransportPayloadNoBinders_proved
          hBody₃Scoped hV₂'NoBinders hArg₂₃ hpvΓs
      exact ((MEqRedStar.single hβStep).trans
        (MEqRedStar.single hBodyProgress')).trans hArgChain

/- Restricted `Me-App × Me-Bet` source cell with only a binder-free
argument-side condition, symmetric to `bet_app_chain_ArgNoBinders_of`. -/
theorem app_bet_chain_ArgNoBinders_of
    {Γ : Ctx} {s : Stack} {t v body body₂' v₁' v₂' hOp₁_target : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hVNoBinders : Term.NoBinders v)
    (hOp₁ : MEqRed Γ (v :: s) (.abs t body) hOp₁_target)
    (hArg₁ : MEqRed Γ [] v v₁')
    (hBody₂ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂')
    (hArg₂ : MEqRed Γ [] v v₂')
    (hBody₁Sub :
      ∀ {body₁' t' : Term},
        hOp₁_target = .abs t' body₁' →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₁') :
    ∃ t₃,
      MEqRedStar Γ s (.app hOp₁_target v₁') t₃
      ∧ MEqRedStar Γ s (Term.instantiate 0 v₂' body₂') t₃ := by
  obtain ⟨t₃, hLeft, hRight⟩ :=
    bet_app_chain_ArgNoBinders_of hBodyDiamond hArgDiamond ht hVNoBinders
      hBody₂ hArg₂ hOp₁ hArg₁ hBody₁Sub
  exact ⟨t₃, hRight, hLeft⟩

/- Restricted `Me-Bet × Me-App` source cell where both the β argument and
the abstraction body are binder-free. The body-side `NoBinders` premise
discharges the `.equ`-head to `.sub`-head bridge for the `Me-FOp` operator
inversion. -/
theorem bet_app_chain_ArgBodyNoBinders_of
    {Γ : Ctx} {s : Stack} {t v body body₁' v₁' v₂' hOp₂_target : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hVNoBinders : Term.NoBinders v)
    (hBodyNoBinders : Term.NoBinders body)
    (hBody₁ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₁')
    (hArg₁ : MEqRed Γ [] v v₁')
    (hOp₂ : MEqRed Γ (v :: s) (.abs t body) hOp₂_target)
    (hArg₂ : MEqRed Γ [] v v₂') :
    ∃ t₃,
      MEqRedStar Γ s (Term.instantiate 0 v₁' body₁') t₃
      ∧ MEqRedStar Γ s (.app hOp₂_target v₂') t₃ :=
  bet_app_chain_ArgNoBinders_of hBodyDiamond hArgDiamond ht hVNoBinders
    hBody₁ hArg₁ hOp₂ hArg₂
    (fun {body₂' t'} hShape => by
      cases hOp₂ with
      | fOp hT₂ hα₂ hBody₂equ =>
          cases hShape
          exact MEqRedSubBridgePayloadNoBinders_proved ht hBodyNoBinders
            hBody₂equ)

/- Restricted `Me-App × Me-Bet` source cell where both the β argument and
the abstraction body are binder-free. Symmetric to
`bet_app_chain_ArgBodyNoBinders_of`. -/
theorem app_bet_chain_ArgBodyNoBinders_of
    {Γ : Ctx} {s : Stack} {t v body body₂' v₁' v₂' hOp₁_target : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hVNoBinders : Term.NoBinders v)
    (hBodyNoBinders : Term.NoBinders body)
    (hOp₁ : MEqRed Γ (v :: s) (.abs t body) hOp₁_target)
    (hArg₁ : MEqRed Γ [] v v₁')
    (hBody₂ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂')
    (hArg₂ : MEqRed Γ [] v v₂') :
    ∃ t₃,
      MEqRedStar Γ s (.app hOp₁_target v₁') t₃
      ∧ MEqRedStar Γ s (Term.instantiate 0 v₂' body₂') t₃ :=
  app_bet_chain_ArgNoBinders_of hBodyDiamond hArgDiamond ht hVNoBinders
    hOp₁ hArg₁ hBody₂ hArg₂
    (fun {body₁' t'} hShape => by
      cases hOp₁ with
      | fOp hT₁ hα₁ hBody₁equ =>
          cases hShape
          exact MEqRedSubBridgePayloadNoBinders_proved ht hBodyNoBinders
            hBody₁equ)

end EqDiamonds

namespace StrongCommutes

/- Restricted `Ms-Equ × Me-Bet` β-position cell with only a binder-free
argument-side condition. This is the `StrongCommutes` analog of the
`EqDiamonds.*_ArgNoBinders_of` cells. -/
theorem equ_bet_chain_ArgNoBinders_of
    {Γ : Ctx} {s : Stack} {t v body body₂' v₂' t₁ : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hVNoBinders : Term.NoBinders v)
    (hpv : PrevalidExt Γ s)
    (hMEqLHS : MEqRed Γ s (.app (.abs t body) v) t₁)
    (hBody₂ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂')
    (hArg₂ : MEqRed Γ [] v v₂')
    (hAppBodyOpSubBridge :
      ∀ {hOp₁_target body₁' t' : Term},
        MEqRed Γ (v :: s) (.abs t body) hOp₁_target →
        hOp₁_target = .abs t' body₁' →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₁') :
    ∃ t₃,
      MEqRedStar Γ s t₁ t₃
      ∧ MSubRedStar Γ s (Term.instantiate 0 v₂' body₂') t₃ := by
  cases hMEqLHS with
  | bet ht₁ hBody₁ hArg₁ =>
    obtain ⟨t₃, hLeft, hRight⟩ :=
      EqDiamonds.bet_bet_chain_ArgNoBinders_of hBodyDiamond hArgDiamond
        ht hVNoBinders hBody₁ hArg₁ hBody₂ hArg₂
    refine ⟨t₃, hLeft, ?_⟩
    exact MSubRedStar.of_MEqRedStar hpv hRight
  | app hOp₁ hArg₁ =>
    obtain ⟨t₃, hLeft, hRight⟩ :=
      EqDiamonds.app_bet_chain_ArgNoBinders_of hBodyDiamond hArgDiamond
        ht hVNoBinders hOp₁ hArg₁ hBody₂ hArg₂
        (fun {body₁' t'} hShape => hAppBodyOpSubBridge hOp₁ hShape)
    refine ⟨t₃, hLeft, ?_⟩
    exact MSubRedStar.of_MEqRedStar hpv hRight

/- Restricted `Ms-Equ × Me-Bet` β-position cell where both the β argument
and abstraction body are binder-free. The body-side `NoBinders` premise
discharges the `.equ`-head to `.sub`-head bridge for wrapped `Me-FOp`
operator steps. -/
theorem equ_bet_chain_ArgBodyNoBinders_of
    {Γ : Ctx} {s : Stack} {t v body body₂' v₂' t₁ : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hVNoBinders : Term.NoBinders v)
    (hBodyNoBinders : Term.NoBinders body)
    (hpv : PrevalidExt Γ s)
    (hMEqLHS : MEqRed Γ s (.app (.abs t body) v) t₁)
    (hBody₂ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂')
    (hArg₂ : MEqRed Γ [] v v₂') :
    ∃ t₃,
      MEqRedStar Γ s t₁ t₃
      ∧ MSubRedStar Γ s (Term.instantiate 0 v₂' body₂') t₃ :=
  equ_bet_chain_ArgNoBinders_of hBodyDiamond hArgDiamond ht hVNoBinders
    hpv hMEqLHS hBody₂ hArg₂
    (fun {hOp₁_target body₁' t'} hOp₁ hShape => by
      cases hOp₁ with
      | fOp hT₁ hα₁ hBody₁equ =>
          cases hShape
          exact MEqRedSubBridgePayloadNoBinders_proved ht hBodyNoBinders
            hBody₁equ)

/- Restricted `Ms-App × Me-Bet` β-position cell with only a binder-free
argument-side condition. The `Ms-Equ` operator case delegates to the
restricted EqDiamonds app/bet cell; the `Ms-FOp` operator case uses
`MEqRedArgTransportPayloadNoBinders_proved` directly. -/
theorem app_bet_chain_ArgNoBinders_of
    {Γ : Ctx} {s : Stack} {t v body body₂' v₂' op' : Term}
    (hBodyDiamond :
      ∀ {b₁ b₂ : Term},
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
        ∃ b₃,
          MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
          ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              b₂ b₃)
    (hArgDiamond :
      ∀ {a₁ a₂ : Term},
        MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
        ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃)
    (ht : Term.Scoped Γ.depth t)
    (hv : Term.Scoped Γ.depth v)
    (hVNoBinders : Term.NoBinders v)
    (hOp : MSubRed Γ (v :: s) (.abs t body) op')
    (hBody₂ :
      MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body₂')
    (hArg₂ : MEqRed Γ [] v v₂')
    (hBodyOpSubBridge :
      ∀ {body' t' : Term},
        op' = .abs t' body' →
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
          body body') :
    ∃ t₃,
      MEqRedStar Γ s (.app op' v) t₃
      ∧ MSubRedStar Γ s (Term.instantiate 0 v₂' body₂') t₃ := by
  have hpvCons : PrevalidExt Γ (v :: s) := hOp.prevalidExt
  have hpv : PrevalidExt Γ s := PrevalidExt.tail hpvCons
  cases hOp with
  | top _ _ =>
    have hMeTAp : MEqRed Γ s (.app .top v) .top := MEqRed.tAp hpv hv
    have hv₂' : Term.Scoped Γ.depth v₂' := hArg₂.scoped_right
    have hBody₂Scoped : Term.Scoped (Γ.depth + 1) body₂' := by
      simpa [Ctx.depth] using hBody₂.scoped_right
    have hInstScoped :
        Term.Scoped Γ.depth (Term.instantiate 0 v₂' body₂') :=
      Term.instantiate_scoped 0 _ _ _ (Nat.zero_le _) hv₂' hBody₂Scoped
    have hMsTop :
        MSubRed Γ s (Term.instantiate 0 v₂' body₂') .top :=
      MSubRed.top hpv hInstScoped
    refine ⟨.top, MEqRedStar.single hMeTAp, MSubRedStar.single hMsTop⟩
  | equ _ hMEqOp =>
    have hpvNil : PrevalidExt Γ [] :=
      PrevalidExt.nil (PrevalidExt.ctx hpv)
    have hArgRefl : MEqRed Γ [] v v := MEqRed.refl hpvNil hv
    obtain ⟨t₃, hLeft, hRight⟩ :=
      EqDiamonds.app_bet_chain_ArgNoBinders_of hBodyDiamond hArgDiamond
        ht hVNoBinders hMEqOp hArgRefl hBody₂ hArg₂
        (fun {body₁' t'} hShape => hBodyOpSubBridge hShape)
    refine ⟨t₃, hLeft, ?_⟩
    exact MSubRedStar.of_MEqRedStar hpv hRight
  | fOp htOp hαOp hBodySub =>
    rename_i bodyOp'
    have hBodyOpSubBridged :
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
          body bodyOp' :=
      hBodyOpSubBridge rfl
    obtain ⟨body₃, hBody₁₃J, hBody₂₃J⟩ :=
      hBodyDiamond hBodyOpSubBridged hBody₂
    let hBody₁₃ :
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
          bodyOp' body₃ := hBody₁₃J.some
    let hBody₂₃ :
        MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
          body₂' body₃ := hBody₂₃J.some
    have hpvNil : PrevalidExt Γ [] :=
      PrevalidExt.nil (PrevalidExt.ctx hpv)
    have hArgRefl : MEqRed Γ [] v v := MEqRed.refl hpvNil hv
    obtain ⟨v₃, hArg₁₃J, hArg₂₃J⟩ := hArgDiamond hArgRefl hArg₂
    let hArg₁₃ : MEqRed Γ [] v v₃ := hArg₁₃J.some
    let hArg₂₃ : MEqRed Γ [] v₂' v₃ := hArg₂₃J.some
    have hV₂'NoBinders : Term.NoBinders v₂' :=
      hArg₂.preserves_noBinders hVNoBinders
    refine ⟨Term.instantiate 0 v₃ body₃, ?_, ?_⟩
    · have hPrevalidT :
          Prevalid ({bound := t, kind := .sub} :: Γ) :=
        Prevalid.sub (PrevalidExt.ctx hpv) ht
      have hpvBodyT :
          PrevalidExt ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) :=
        PrevalidExt.weaken_head hpv hPrevalidT
      have hBodyOp'Scoped : Term.Scoped (Γ.depth + 1) bodyOp' := by
        simpa [Ctx.depth] using hBodyOpSubBridged.scoped_right
      have hBodyOp'Scoped_t :
          Term.Scoped
            (Ctx.depth ({bound := t, kind := .sub} :: Γ)) bodyOp' := by
        simpa [Ctx.depth, Nat.succ_eq_add_one] using hBodyOp'Scoped
      have hBodyReflT :
          MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
            bodyOp' bodyOp' :=
        MEqRed.refl hpvBodyT hBodyOp'Scoped_t
      have hArgReflv : MEqRed Γ [] v v := MEqRed.refl hpvNil hv
      have hβStep :
          MEqRed Γ s (.app (.abs t bodyOp') v)
            (Term.instantiate 0 v bodyOp') :=
        MEqRed.bet ht hBodyReflT hArgReflv
      have hBodyProgress :
          MEqRed Γ (Stack.instantiate 0 v (Stack.shift 0 s))
            (Term.instantiate 0 v bodyOp')
            (Term.instantiate 0 v body₃) :=
        MEqRedFusedKindNarrowedBetaSubstStack_proved
          (arg := t) (arg' := v) ht hv hBody₁₃
      have hStackEq :
          Stack.instantiate 0 v (Stack.shift 0 s) = s :=
        Stack.instantiate_zero_shift_zero_id v s
      have hBodyProgress' :
          MEqRed Γ s
            (Term.instantiate 0 v bodyOp')
            (Term.instantiate 0 v body₃) := by
        simpa [hStackEq] using hBodyProgress
      have hBody₃Scoped : Term.Scoped (Γ.depth + 1) body₃ := by
        simpa [Ctx.depth] using hBody₁₃.scoped_right
      have hArgChain :
          MEqRedStar Γ s
            (Term.instantiate 0 v body₃)
            (Term.instantiate 0 v₃ body₃) :=
        MEqRedArgTransportPayloadNoBinders_proved
          hBody₃Scoped hVNoBinders hArg₁₃ hpv
      exact ((MEqRedStar.single hβStep).trans
        (MEqRedStar.single hBodyProgress')).trans hArgChain
    · have hv₂'Scoped : Term.Scoped Γ.depth v₂' := hArg₂.scoped_right
      have hBodyProgress :
          MEqRed Γ (Stack.instantiate 0 v₂' (Stack.shift 0 s))
            (Term.instantiate 0 v₂' body₂')
            (Term.instantiate 0 v₂' body₃) :=
        MEqRedFusedKindNarrowedBetaSubstStack_proved
          (arg := t) (arg' := v₂') ht hv₂'Scoped hBody₂₃
      have hStackEq :
          Stack.instantiate 0 v₂' (Stack.shift 0 s) = s :=
        Stack.instantiate_zero_shift_zero_id v₂' s
      have hBodyProgress' :
          MEqRed Γ s
            (Term.instantiate 0 v₂' body₂')
            (Term.instantiate 0 v₂' body₃) := by
        simpa [hStackEq] using hBodyProgress
      have hBody₃Scoped : Term.Scoped (Γ.depth + 1) body₃ := by
        simpa [Ctx.depth] using hBody₂₃.scoped_right
      have hArgChain :
          MEqRedStar Γ s
            (Term.instantiate 0 v₂' body₃)
            (Term.instantiate 0 v₃ body₃) :=
        MEqRedArgTransportPayloadNoBinders_proved
          hBody₃Scoped hV₂'NoBinders hArg₂₃ hpv
      have hMeRHS :
          MEqRedStar Γ s
            (Term.instantiate 0 v₂' body₂')
            (Term.instantiate 0 v₃ body₃) :=
        (MEqRedStar.single hBodyProgress').trans hArgChain
      exact MSubRedStar.of_MEqRedStar hpv hMeRHS

end StrongCommutes

/-! ## Top-level chain-output Lemma 2 closure assembly

This section assembles the per-cell EqDiamonds theorems into a single
chain-output closure `EqDiamonds_proved`. The closure is structured as a
case-dispatch tree on the two input `MEqRed` derivations. Each cell is
invoked with the appropriate residual hypotheses.

### Residual hypotheses

The closure is **conditional** on four residuals:

1. `MEqRedArgTransportPayload` — the argument-position transport lemma
   used by the `bet × bet`, `bet × app`, and `app × bet` chain cells.
2. `MEqRedOpStackHeadTransportPayload` — the operator stack-head
   transport lemma used by the `app × app` chain cell.
3. `hSubBridge` — the `.equ → .sub` head bridge for FOp-inverted bodies,
   used in the cross-β `bet × app` and `app × bet` cells.
4. `hUniformDiamond` — universal single-step `EqDiamonds Γ' s'` at every
   extended context. The single-step body/arg/operator diamonds required
   by the chain cells (which take `MEqRedJ` body diamonds, not chains)
   are obtained by specializing this hypothesis. This residual is
   **necessary** because chain cells like `bet_bet_chain_of` accept
   only single-step body diamonds — recursive descent through the
   closure cannot produce single-step output for body sub-derivations
   in general (e.g. body sub-derivation diamonds for `bet × bet` need
   chain output, not single-step). Discharging this residual is
   itself the open transitivity-elimination problem. -/

/-- Chain-output equivalence diamond at a fixed extended context. The
chain-output form is essential because the `bet × bet`, `bet × app`,
`app × bet`, and `app × app` source cells produce chain reducts at
their joins. -/
abbrev EqDiamondsChain (Γ : Ctx) (s : Stack) : Prop :=
  ∀ {t₀ t₁ t₂ : Term},
    MEqRed Γ s t₀ t₁ → MEqRed Γ s t₀ t₂ →
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MEqRedStar Γ s t₂ t₃

/-- The `.equ → .sub` head bridge residual: convert an equivalence step
in an `.equ`-head context (with bound `v`) to one in a `.sub`-head
context (with bound `t`), preserving the body source/target and the
shifted stack. Required by the cross-β `bet × app` and `app × bet`
cells whose `Me-FOp` inversion produces `.equ`-head body derivations
that need to live in `.sub`-head context to be diamonded against the
abstraction's `.sub`-head body.

Defined in `Type` because `MEqRed` is `Type`-valued; reducible so the
closure body can apply it as a function directly. -/
@[reducible] def MEqRedSubBridgePayload : Type :=
  ∀ {Γ : Ctx} {t v body body' : Term} {s : Stack},
    MEqRed ({bound := v, kind := .equ} :: Γ) (Stack.shift 0 s) body body' →
    MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body body'

/-- Universal single-step equivalence diamond at every extended context.
This is the residual for body/arg/op single-step diamond hypotheses
required by the chain cells. -/
def UniformEqDiamonds : Prop :=
  ∀ {Γ : Ctx} {s : Stack}, EqDiamonds Γ s

/-- Top-level chain-output equivalence diamond closure for de Bruijn
Lemma 2, conditional on:
- `MEqRedArgTransportPayload` (argument-position transport)
- `MEqRedOpStackHeadTransportPayload` (operator stack-head transport)
- `MEqRedSubBridgePayload` (`.equ → .sub` head bridge)
- `UniformEqDiamonds` (single-step diamond at every extended context;
  the standing transitivity-elimination residual)

The closure is assembled by case-splitting on both input reductions:
single-step output cells (`top`, `bvar_any_of`, `tAp_*`, `appTop_*`,
`fun_fun_of`, `fOp_fOp_of`) are wrapped with `MEqRedStar.single`;
chain-output cells (`bet_bet_chain_of`, `bet_app_chain_of`,
`app_bet_chain_of`, `app_app_chain_of`) compose directly. -/
theorem EqDiamonds_proved
    (hArgTransport : MEqRedArgTransportPayload)
    (hOpTransport : MEqRedOpStackHeadTransportPayload)
    (hSubBridge : MEqRedSubBridgePayload)
    (hUniformDiamond : UniformEqDiamonds) :
    ∀ {Γ : Ctx} {s : Stack}, EqDiamondsChain Γ s := by
  intro Γ s t₀ t₁ t₂ hRed₁ hRed₂
  -- Adapter to wrap a single-step diamond cell as a chain-output diamond.
  have wrapSingle :
      ∀ {a b : Term},
        (∃ c, MEqRedJ Γ s a c ∧ MEqRedJ Γ s b c) →
        ∃ c, MEqRedStar Γ s a c ∧ MEqRedStar Γ s b c := by
    intro a b ⟨c, hac, hbc⟩
    exact ⟨c, Relation.ReflTransGen.single hac, Relation.ReflTransGen.single hbc⟩
  -- Case-split on hRed₁'s constructor.
  cases hRed₁ with
  | top hpv =>
    -- Source `.top`: hRed₂ also reduces from `.top`, target is `.top`.
    cases hRed₂ with
    | top hpv₂ =>
      exact ⟨.top,
        Relation.ReflTransGen.refl,
        Relation.ReflTransGen.refl⟩
  | @pro _ _ i α α' hpv hαb hα =>
    -- Source `.bvar i` via `Me-Pro`. Use `EqDiamonds.bvar_any_of`.
    refine wrapSingle ?_
    exact EqDiamonds.bvar_any_of (@hUniformDiamond Γ s) hpv
      (MEqRed.pro hpv hαb hα) hRed₂
  | @var _ _ i hpv hi =>
    -- Source `.bvar i` via `Me-Var`.
    refine wrapSingle ?_
    exact EqDiamonds.bvar_any_of (@hUniformDiamond Γ s) hpv
      (MEqRed.var hpv hi) hRed₂
  | @tAp _ _ u hpv hu =>
    -- Source `.app .top u`: use `EqDiamonds.tAp_any`.
    refine wrapSingle ?_
    exact EqDiamonds.tAp_any hpv hu hRed₂
  | @app _ _ u u' v v' hOp₁ hArg₁ =>
    -- Source `.app u v`. hRed₂ may be: app, bet (if u = .abs ...),
    -- or tAp (if u = .top). Case-split on hRed₂.
    cases hRed₂ with
    | @app _ _ _ u₂ _ v₂ hOp₂ hArg₂ =>
      -- app × app
      have hOpDiamond :
          ∀ {a b : Term},
            MEqRed Γ (v :: s) u a → MEqRed Γ (v :: s) u b →
            ∃ c, MEqRedJ Γ (v :: s) a c ∧ MEqRedJ Γ (v :: s) b c :=
        fun ha hb => @hUniformDiamond Γ (v :: s) _ _ _ ha hb
      have hArgDiamond :
          ∀ {a b : Term},
            MEqRed Γ [] v a → MEqRed Γ [] v b →
            ∃ c, MEqRedJ Γ [] a c ∧ MEqRedJ Γ [] b c :=
        fun ha hb => @hUniformDiamond Γ [] _ _ _ ha hb
      exact EqDiamonds.app_app_chain_of hOpTransport hOpDiamond
        hArgDiamond hOp₁ hArg₁ hOp₂ hArg₂
    | @bet _ _ t _ _ body _ ht hBody₂ hArg₂ =>
      -- app × bet: source is .app (.abs t body) v, h₁ = app, h₂ = bet.
      -- Use `app_bet_chain_of`.
      have hBodyDiamond :
          ∀ {b₁ b₂ : Term},
            MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
            MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
            ∃ b₃,
              MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
              ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
                  b₂ b₃ := fun ha hb =>
        @hUniformDiamond ({bound := t, kind := .sub} :: Γ)
          (Stack.shift 0 s) _ _ _ ha hb
      have hArgDiamond :
          ∀ {a₁ a₂ : Term},
            MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
            ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃ := fun ha hb =>
        @hUniformDiamond Γ [] _ _ _ ha hb
      have hBody₁Sub :
          ∀ {body₁' t' : Term},
            u' = .abs t' body₁' →
            MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              body body₁' := by
        intro body₁' t' heq
        cases hOp₁ with
        | fOp hT₁ hα₁ hBody₁equ =>
          rename_i body₁'_inv
          injection heq with heq1 heq2
          subst heq1
          subst heq2
          exact hSubBridge hBody₁equ
      exact EqDiamonds.app_bet_chain_of hArgTransport hBodyDiamond
        hArgDiamond ht hOp₁ hArg₁ hBody₂ hArg₂ hBody₁Sub
    | @tAp _ _ u_t hpv hu =>
      -- App × tAp: source is .app .top u, h₁ = app with u = .top.
      refine wrapSingle ?_
      exact EqDiamonds.any_tAp hpv hu (MEqRed.app hOp₁ hArg₁)
  | @bet _ _ t v vDst body bodyDst ht hBody₁ hArg₁ =>
    -- Source `.app (.abs t body) v`. hRed₂ may be bet or app.
    cases hRed₂ with
    | @bet _ _ _ _ _ _ _ ht₂ hBody₂ hArg₂ =>
      -- bet × bet
      have hBodyDiamond :
          ∀ {b₁ b₂ : Term},
            MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
            MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
            ∃ b₃,
              MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
              ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
                  b₂ b₃ := fun ha hb =>
        @hUniformDiamond ({bound := t, kind := .sub} :: Γ)
          (Stack.shift 0 s) _ _ _ ha hb
      have hArgDiamond :
          ∀ {a₁ a₂ : Term},
            MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
            ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃ := fun ha hb =>
        @hUniformDiamond Γ [] _ _ _ ha hb
      exact EqDiamonds.bet_bet_chain_of hArgTransport hBodyDiamond
        hArgDiamond ht hBody₁ hArg₁ hBody₂ hArg₂
    | @app _ _ _ uDst₂ _ vDst₂ hOp₂ hArg₂ =>
      -- bet × app: source is .app (.abs t body) v, h₁ = bet, h₂ = app.
      -- Use `bet_app_chain_of`.
      have hBodyDiamond :
          ∀ {b₁ b₂ : Term},
            MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₁ →
            MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) body b₂ →
            ∃ b₃,
              MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) b₁ b₃
              ∧ MEqRedJ ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
                  b₂ b₃ := fun ha hb =>
        @hUniformDiamond ({bound := t, kind := .sub} :: Γ)
          (Stack.shift 0 s) _ _ _ ha hb
      have hArgDiamond :
          ∀ {a₁ a₂ : Term},
            MEqRed Γ [] v a₁ → MEqRed Γ [] v a₂ →
            ∃ a₃, MEqRedJ Γ [] a₁ a₃ ∧ MEqRedJ Γ [] a₂ a₃ := fun ha hb =>
        @hUniformDiamond Γ [] _ _ _ ha hb
      have hBody₂Sub :
          ∀ {body₂' t' : Term},
            uDst₂ = .abs t' body₂' →
            MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s)
              body body₂' := by
        intro body₂' t' heq
        cases hOp₂ with
        | fOp hT₂ hα₂ hBody₂equ =>
          rename_i body₂'_inv
          injection heq with heq1 heq2
          subst heq1
          subst heq2
          exact hSubBridge hBody₂equ
      exact EqDiamonds.bet_app_chain_of hArgTransport hBodyDiamond
        hArgDiamond ht hBody₁ hArg₁ hOp₂ hArg₂ hBody₂Sub
  | @fun_ _ t tDst body bodyDst hT₁ hBody₁ =>
    -- Source `.abs t body`, stack `[]`. hRed₂ must be `fun_`.
    cases hRed₂ with
    | @fun_ _ _ tDst₂ _ bodyDst₂ hT₂ hBody₂ =>
      refine wrapSingle ?_
      exact EqDiamonds.fun_fun_of (@hUniformDiamond Γ [])
        (@hUniformDiamond ({bound := t, kind := .sub} :: Γ) [])
        hT₁ hBody₁ hT₂ hBody₂
  | @fOp _ s_inner t tDst α body bodyDst hT₁ hα hBody₁ =>
    -- Source `.abs t body`, stack `α :: s_inner`. hRed₂ must be `fOp`.
    cases hRed₂ with
    | @fOp _ _ _ tDst₂ _ _ bodyDst₂ hT₂ hα₂ hBody₂ =>
      refine wrapSingle ?_
      exact EqDiamonds.fOp_fOp_of (@hUniformDiamond Γ [])
        (@hUniformDiamond ({bound := α, kind := .equ} :: Γ)
          (Stack.shift 0 s_inner))
        hα hT₁ hBody₁ hT₂ hBody₂
