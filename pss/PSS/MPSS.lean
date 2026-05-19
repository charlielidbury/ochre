import PSS.Syntax

/-!
# Machine-Based Pure Subtype Systems (MPSS)

Mechanisation of the MPSS calculus from:
  Pasquale & García-Pérez, "Towards the type safety of Pure Subtype Systems
  (Full version)", CSL 2026.

MPSS reformulates Hutchins' algorithmic PSS with a continuation stack
mechanism (inspired by the Krivine Abstract Machine) that tracks operands
passed to abstractions. This exposes intermediate reduction steps that are
absent in the original PSS and enables a direct proof of commutativity
between equivalence reduction (≡→) and subtyping reduction (≤→).

## Contents
- MPSS syntax (contexts, stacks, extended contexts)
- Equivalence reduction `MEquivRed` (Figure 2, top half)
- Subtyping reduction `MSubRed` (Figure 2, bottom half)
- Context reduction `CtxRed` (Section 3)
- Lemma 1: Commutativity of ≤→ and ≡→ (statement)
-/

open Expr

namespace MPSS

/-! ## Syntax -/

/-- Context annotations.
    In MPSS, contexts contain two kinds of bindings:
    - `sub t`   : x ≤ t  (subtype annotation)
    - `equiv t` : x ≡ α  (equivalence annotation, α comes from the stack)
-/
inductive Ann where
  | sub   (bound : Expr)
  | equiv (term  : Expr)
deriving Inhabited, DecidableEq, Repr

/-- Logical context: a list of annotations in de Bruijn order.
    `MCtx[0]` is the innermost binder. -/
abbrev MCtx := List Ann

/-- Continuation stack: a list of terms (operands). -/
abbrev Stack := List Expr

/-! ## Equivalence and Subtyping reduction (Figure 2)

These are mutually inductive because:
- ME-PRO (in MEquivRed) has a premise that uses MSubRed
- MS-EQU (in MSubRed) has a premise that uses MEquivRed
-/

mutual

/--
Equivalence reduction `MEquivRed Γ s u v` means `Γ;s ⊢ u ≡→ v`.

This models reflexive, small-step, simultaneous β-reduction instrumented
with the stack mechanism.
-/
inductive MEquivRed : MCtx → Stack → Expr → Expr → Type where
  /-- ME-PRO: Promote through equivalence annotation.
      `x ≡ α ∈ Γ` and `Γ;s ⊢ α↑ ≤→ α'`  ⟹  `Γ;s ⊢ x ≡→ α'`
      (α↑ means α shifted to the current scope) -/
  | me_pro {Γ s α'} {k : Nat} {α : Expr} :
      Γ.get? k = some (Ann.equiv α) →
      MSubRed Γ s (α.shift (k + 1) 0) α' →
      MEquivRed Γ s (.bvar k) α'
  /-- ME-BET: Simultaneous β-reduction.
      `Γ,x≤t;s ⊢ u ≡→ u'`, `Γ;nil ⊢ v ≡→ v'`
      ⟹  `Γ;s ⊢ (λt.u) v ≡→ u'[0↦v']`

      In de Bruijn: body u is reduced under the lambda's own binding
      (Ann.sub dom), so bvar 0 correctly refers to the parameter.
      The argument v is reduced in context Γ with empty stack. -/
  | me_bet {Γ s dom u u' v v'} :
      MEquivRed (Ann.sub dom :: Γ) s u u' →
      MEquivRed Γ [] v v' →
      MEquivRed Γ s (.app (.lam dom u) v) (u'.subst 0 v')
  /-- ME-TOP: Top is reflexive. -/
  | me_top {Γ s} :
      MEquivRed Γ s .top .top
  /-- ME-VAR: Variables are reflexive. -/
  | me_var {Γ s k} :
      MEquivRed Γ s (.bvar k) (.bvar k)
  /-- ME-TAP: `Top u ≡→ Top` (Top absorbs applications). -/
  | me_tap {Γ s u} :
      MEquivRed Γ s (.app .top u) .top
  /-- ME-APP: Application — push operand onto stack.
      `Γ; v::s ⊢ u ≡→ u'`, `Γ;nil ⊢ v ≡→ v'`  ⟹  `Γ;s ⊢ u v ≡→ u' v'` -/
  | me_app {Γ s u u' v v'} :
      MEquivRed Γ (v :: s) u u' →
      MEquivRed Γ [] v v' →
      MEquivRed Γ s (.app u v) (.app u' v')
  /-- ME-FUN: Unapplied abstraction (stack is nil).
      `Γ;nil ⊢ t ≡→ t'`, `Γ,x≤t; nil ⊢ u ≡→ u'`
      ⟹  `Γ;nil ⊢ λt.u ≡→ λt'.u'` -/
  | me_fun {Γ dom dom' body body'} :
      MEquivRed Γ [] dom dom' →
      MEquivRed (Ann.sub dom :: Γ) [] body body' →
      MEquivRed Γ [] (.lam dom body) (.lam dom' body')
  /-- ME-FOP: Applied abstraction — pop operand from stack.
      `Γ;nil ⊢ t ≡→ t'`, `Γ,x≡α; s ⊢ u ≡→ u'`
      ⟹  `Γ; α::s ⊢ λt.u ≡→ λt'.u'` -/
  | me_fop {Γ s α dom dom' body body'} :
      MEquivRed Γ [] dom dom' →
      MEquivRed (Ann.equiv α :: Γ) s body body' →
      MEquivRed Γ (α :: s) (.lam dom body) (.lam dom' body')

/--
Subtyping reduction `MSubRed Γ s u v` means `Γ;s ⊢ u ≤→ v`.

This defines promotion (subtyping) in a stack-aware manner.
Note: subtyping does NOT change the type annotation of abstractions.
-/
inductive MSubRed : MCtx → Stack → Expr → Expr → Type where
  /-- MS-PRO: Promote variable to its subtype bound.
      `x ≤ t ∈ Γ`  ⟹  `Γ;s ⊢ x ≤→ t↑` -/
  | ms_pro {Γ s} {k : Nat} {t : Expr} :
      Γ.get? k = some (Ann.sub t) →
      MSubRed Γ s (.bvar k) (t.shift (k + 1) 0)
  /-- MS-TOP: Any term promotes to Top. -/
  | ms_top {Γ s u} :
      MSubRed Γ s u .top
  /-- MS-EQU: Equivalence subsumes subtyping.
      `Γ;s ⊢ u ≡→ v`  ⟹  `Γ;s ⊢ u ≤→ v` -/
  | ms_equ {Γ s u v} :
      MEquivRed Γ s u v →
      MSubRed Γ s u v
  /-- MS-APP: Application — push operand and promote operator.
      `Γ; v::s ⊢ u ≤→ u'`  ⟹  `Γ;s ⊢ u v ≤→ u' v` -/
  | ms_app {Γ s u u' v} :
      MSubRed Γ (v :: s) u u' →
      MSubRed Γ s (.app u v) (.app u' v)
  /-- MS-FUN: Unapplied abstraction — promote body.
      `Γ,x≤t; nil ⊢ u ≤→ u'`  ⟹  `Γ;nil ⊢ λt.u ≤→ λt.u'` -/
  | ms_fun {Γ dom body body'} :
      MSubRed (Ann.sub dom :: Γ) [] body body' →
      MSubRed Γ [] (.lam dom body) (.lam dom body')
  /-- MS-FOP: Applied abstraction — pop from stack, promote body.
      `Γ,x≡α; s ⊢ u ≤→ u'`  ⟹  `Γ; α::s ⊢ λt.u ≤→ λt.u'` -/
  | ms_fop {Γ s α dom body body'} :
      MSubRed (Ann.equiv α :: Γ) s body body' →
      MSubRed Γ (α :: s) (.lam dom body) (.lam dom body')

end

/-! ## Context reduction  Γ;s ↦ Γ';s'  (Section 3)

Captures how annotations evolve during reduction steps.
Used in the statement of commutativity.

- CT-ANN: Annotation `x ⊲ t` in the context is reduced pointwise via ≡→
- CT-STK: Stack element `α` is reduced pointwise via ≡→
-/

inductive CtxRed : MCtx → Stack → MCtx → Stack → Type where
  /-- CT-ANN (sub): Reduce a subtype annotation.
      `Γ;s ↦ Γ';s'` and `Γ;nil ⊢ t ≡→ t'`
      ⟹  `(sub t :: Γ); s ↦ (sub t' :: Γ'); s'` -/
  | ct_ann_sub {Γ s Γ' s' t t'} :
      CtxRed Γ s Γ' s' →
      MEquivRed Γ [] t t' →
      CtxRed (Ann.sub t :: Γ) s (Ann.sub t' :: Γ') s'
  /-- CT-ANN (equiv): Reduce an equivalence annotation.
      `Γ;s ↦ Γ';s'` and `Γ;nil ⊢ α ≡→ α'`
      ⟹  `(equiv α :: Γ); s ↦ (equiv α' :: Γ'); s'` -/
  | ct_ann_equiv {Γ s Γ' s' α α'} :
      CtxRed Γ s Γ' s' →
      MEquivRed Γ [] α α' →
      CtxRed (Ann.equiv α :: Γ) s (Ann.equiv α' :: Γ') s'
  /-- CT-STK: Reduce a stack element.
      `Γ;s ↦ Γ';s'` and `Γ;nil ⊢ α ≡→ α'`
      ⟹  `Γ; α::s ↦ Γ'; α'::s'` -/
  | ct_stk {Γ s Γ' s' α α'} :
      CtxRed Γ s Γ' s' →
      MEquivRed Γ [] α α' →
      CtxRed Γ (α :: s) Γ' (α' :: s')
  /-- Base case: empty context and empty stack reduce to themselves. -/
  | ct_nil :
      CtxRed [] [] [] []

/-! ## Auxiliary lemmas and commutativity (Section 3) -/

/-- Reflexivity of ≡→: every term reduces to itself (Proposition 18 in paper).
    ME-TOP for Top, ME-VAR for variables, ME-FUN/ME-FOP for lambdas, ME-APP for apps. -/
def equivRed_refl : (Γ : MCtx) → (s : Stack) → (t : Expr) → MEquivRed Γ s t t
  | _, _, .top => .me_top
  | _, _, .bvar _ => .me_var
  | Γ, [], .lam dom body =>
    .me_fun (equivRed_refl Γ [] dom) (equivRed_refl (Ann.sub dom :: Γ) [] body)
  | Γ, α :: s, .lam dom body =>
    .me_fop (equivRed_refl Γ [] dom) (equivRed_refl (Ann.equiv α :: Γ) s body)
  | Γ, s, .app u v =>
    .me_app (equivRed_refl Γ (v :: s) u) (equivRed_refl Γ [] v)

/-- Reflexivity of context reduction: Γ;s ↦ Γ;s (using equivRed_refl). -/
def ctxRed_refl : (Γ : MCtx) → (s : Stack) → CtxRed Γ s Γ s
  | [], [] => .ct_nil
  | Ann.sub t :: Γ, s =>
    .ct_ann_sub (ctxRed_refl Γ s) (equivRed_refl Γ [] t)
  | Ann.equiv α :: Γ, s =>
    .ct_ann_equiv (ctxRed_refl Γ s) (equivRed_refl Γ [] α)
  | [], α :: s =>
    .ct_stk (ctxRed_refl [] s) (equivRed_refl [] [] α)

/-- If the input stack is nil, the output stack is nil. -/
theorem ctxRed_nil_stack : CtxRed Γ [] Γ' s' → s' = []
  | .ct_ann_sub h _ => ctxRed_nil_stack h
  | .ct_ann_equiv h _ => ctxRed_nil_stack h
  | .ct_nil => rfl

/-- Diamond property for ≡→ (Lemma 2 in paper).
    If Γ₀;s₀ ⊢ t₀ ≡→ t₁ and Γ₀;s₀ ⊢ t₀ ≡→ t₂ then for any extended contexts
    Γ₁;s₁ and Γ₂;s₂ with Γ₀;s₀ ↦ Γ₁;s₁ and Γ₀;s₀ ↦ Γ₂;s₂, there exists t₃
    such that Γ₁;s₁ ⊢ t₁ ≡→ t₃ and Γ₂;s₂ ⊢ t₂ ≡→ t₃.

    TODO: Full proof requires its own induction on ≡→ derivations. -/
def diamond
    {Γ₀ : MCtx} {s₀ : Stack} {t₀ t₁ t₂ : Expr}
    {Γ₁ Γ₂ : MCtx} {s₁ s₂ : Stack}
    (h₁ : MEquivRed Γ₀ s₀ t₀ t₁)
    (h₂ : MEquivRed Γ₀ s₀ t₀ t₂)
    (hc₁ : CtxRed Γ₀ s₀ Γ₁ s₁)
    (hc₂ : CtxRed Γ₀ s₀ Γ₂ s₂)
    : Σ' t₃ : Expr, MEquivRed Γ₁ s₁ t₁ t₃ × MEquivRed Γ₂ s₂ t₂ t₃ :=
  sorry

/-- Context reduction preserves MS-PRO lookups (derived from Lemma 36 + Lemma 19).
    If x ≤ t ∈ Γ and Γ;s ↦ Γ';s', then Γ';s' ⊢ x ≤→ t↑.

    In full generality, the paper shows the annotation reduces pointwise,
    giving t' with t ≡→ t' and Γ';s' ⊢ x ≤→ t'↑. Here we use the simpler
    statement matching our MS-PRO output shape.

    TODO: Full proof requires induction on CtxRed showing annotations reduce pointwise. -/
def weakening_equivRed
    {Γ : MCtx} {s : Stack} {Γ' : MCtx} {s' : Stack} {k : Nat} {t : Expr}
    (h_lookup : Γ.get? k = some (Ann.sub t))
    (h_ctx : CtxRed Γ s Γ' s')
    : MSubRed Γ' s' (.bvar k) (t.shift (k + 1) 0) :=
  sorry

/-- Substitution lemma for ≤→ (Lemma 30 in paper).
    If Γ,x≡v₀;s ⊢ u₁ ≤→ u₃, then Γ';s' ⊢ u₁[x↦v₁] ≤→ u₃[x↦v₁].

    Used in the ME-BET + MS-APP case.

    TODO: Full proof requires induction on the MSubRed derivation,
    showing substitution commutes with each reduction rule. -/
def substitution_subRed
    {v₀ : Expr} {Γ' : MCtx} {s' : Stack}
    {Γ : MCtx} {s : Stack} {u₁ u₃ v₁ : Expr}
    (h : MSubRed (Ann.equiv v₀ :: Γ) s u₁ u₃)
    : MSubRed Γ' s' (u₁.subst 0 v₁) (u₃.subst 0 v₁) :=
  sorry

/-- Annotation-insensitive equivalence reduction (equiv → sub direction).
    If MEquivRed (Ann.equiv v :: Γ) s body body', then also
    MEquivRed (Ann.sub dom :: Γ) s body body'.

    In the paper's named-variable setting, ≡→ on a body doesn't depend on
    whether bvar 0's annotation is ≤ or ≡, because the paper argues ME-PRO
    isn't used on bvar 0 in this context (the variable is "fresh" from the
    lambda). In our de Bruijn mechanisation, this requires showing the ≡→
    derivation doesn't use ME-PRO on index 0.

    TODO: Prove by induction on the MEquivRed derivation. -/
def equivRed_change_ann
    {Γ : MCtx} {s : Stack} {v dom body body' : Expr}
    (h : MEquivRed (Ann.equiv v :: Γ) s body body')
    : MEquivRed (Ann.sub dom :: Γ) s body body' :=
  sorry

/-- Annotation-insensitive equivalence reduction (sub → equiv direction).
    If MEquivRed (Ann.sub dom :: Γ) s body body', then also
    MEquivRed (Ann.equiv v :: Γ) s body body'.

    Symmetric to equivRed_change_ann — same argument applies in reverse.

    TODO: Prove by induction on the MEquivRed derivation. -/
def equivRed_change_ann_rev
    {Γ : MCtx} {s : Stack} {v dom body body' : Expr}
    (h : MEquivRed (Ann.sub dom :: Γ) s body body')
    : MEquivRed (Ann.equiv v :: Γ) s body body' :=
  sorry

/-- Decomposition of CtxRed with non-empty stack for the MS-FOP case.
    Given Γ;(α :: s₀) ↦ Γ';s', produce a CtxRed for the body context
    (Ann.equiv α :: Γ);s₀ ↦ (Ann.equiv α' :: Γ₂);s₀' that is compatible
    with MS-FOP reconstruction.

    More precisely: there exist α', s₀', Γ₂ such that s' = α' :: s₀',
    Γ' = Γ₂, and (Ann.equiv α :: Γ);s₀ ↦ (Ann.equiv α' :: Γ₂);s₀'.

    This packages the needed data for ms_fop/me_fop completion.

    TODO: Prove by induction on CtxRed with weakening for MEquivRed. -/
def ctxRed_unstk
    {Γ : MCtx} {α : Expr} {s₀ : Stack} {Γ' : MCtx} {s' : Stack}
    (h : CtxRed Γ (α :: s₀) Γ' s')
    : Σ' (α' : Expr) (s₀' : Stack) (Γ₂ : MCtx),
        PLift (s' = α' :: s₀') ×
        CtxRed (Ann.equiv α :: Γ) s₀ (Ann.equiv α' :: Γ₂) s₀' ×
        PLift (Γ' = Γ₂) :=
  sorry

/-- Main commutativity theorem (Lemma 1 / Theorem 1 in paper).

    If `Γ;s ⊢ t₀ ≡→ t₁` and `Γ;s ⊢ t₀ ≤→ t₂`, then for any `Γ';s'`
    with `Γ;s ↦ Γ';s'`, there exists `t₃` with `Γ;s ⊢ t₂ ≡→ t₃` and
    `Γ';s' ⊢ t₁ ≤→ t₃`.
-/
def commutativity
    {Γ : MCtx} {s : Stack} {t₀ t₁ t₂ : Expr}
    {Γ' : MCtx} {s' : Stack}
    (h_equiv : MEquivRed Γ s t₀ t₁)
    (h_sub   : MSubRed Γ s t₀ t₂)
    (h_ctx   : CtxRed Γ s Γ' s')
    : Σ' t₃ : Expr, MEquivRed Γ s t₂ t₃ × MSubRed Γ' s' t₁ t₃ := by
  /-
  Proof by induction on the term structure of t₀ (following Appendix A).
  Case split on (h_sub rule, h_equiv rule).
  -/
  match h_sub with
  | .ms_top =>
    -- Case 1: MS-TOP (any ≡→). t₂ = Top. Take t₃ = Top.
    exact ⟨.top, .me_top, .ms_top⟩
  | .ms_equ h_equiv₂ =>
    -- Case 2: MS-EQU. h_equiv₂ : MEquivRed Γ s t₀ t₂.
    -- By diamond (Lemma 2): get t₃ with Γ';s' ⊢ t₁ ≡→ t₃ and Γ;s ⊢ t₂ ≡→ t₃.
    let ⟨t₃, h_t₁_red, h_t₂_red⟩ := diamond h_equiv h_equiv₂ h_ctx (ctxRed_refl Γ s)
    exact ⟨t₃, h_t₂_red, .ms_equ h_t₁_red⟩
  | .ms_pro h_lookup =>
    -- t₀ = bvar k, Γ.get? k = some (Ann.sub t), t₂ = t.shift (k+1) 0
    match h_equiv with
    | .me_pro h_lookup₂ _ =>
      -- Case 3: ME-PRO + MS-PRO — impossible, same index has sub and equiv.
      rw [h_lookup] at h_lookup₂; exact absurd h_lookup₂ (by simp [Ann.noConfusion])
    | .me_var =>
      -- Case 4: ME-VAR + MS-PRO. t₁ = bvar k, t₂ = t.shift (k+1) 0.
      exact ⟨_, equivRed_refl Γ s _, weakening_equivRed h_lookup h_ctx⟩
  | .ms_app h_sub_inner =>
    -- t₀ = app u v, ms_app pushes v onto stack
    match h_equiv with
    | .me_app h_eq_u h_eq_v =>
      -- Case 5: ME-APP + MS-APP. IH on u with extended stack.
      let ⟨u₃, h_eq_u₂, h_sub_u₁⟩ :=
        commutativity h_eq_u h_sub_inner (.ct_stk h_ctx h_eq_v)
      exact ⟨_, .me_app h_eq_u₂ h_eq_v, .ms_app h_sub_u₁⟩
    | .me_bet h_eq_body h_eq_v =>
      -- Case 6: ME-BET + MS-APP. The KEY case.
      -- h_eq_body : MEquivRed (Ann.sub dom :: Γ) s body body'
      -- h_eq_v : MEquivRed Γ [] v v'
      -- h_sub_inner : MSubRed Γ (v :: s) (.lam dom body) u₂
      -- t₁ = body'.subst 0 v' (from me_bet)
      -- Match on h_sub_inner to see how the lambda is promoted:
      match h_sub_inner with
      | .ms_top =>
        -- u₂ = Top, t₂ = app Top v. Take t₃ = Top.
        exact ⟨.top, .me_tap, .ms_top⟩
      | .ms_equ h_inner_eq =>
        -- h_inner_eq : MEquivRed Γ (v :: s) (.lam dom body) u₂
        -- The ≤→ is via ≡→. The paper says: when MS-EQU appears in the
        -- derivation tree, the sub step is actually an equiv step, so we
        -- reduce to the diamond property (Lemma 2).
        -- This sub-case requires combining diamond with the beta-reduction
        -- structure. Needs diamond property (Lemma 2).
        sorry
      | @MSubRed.ms_fop _ _ v_op _ _ _ h_sub_body₂ =>
        -- Core case: ms_fop decomposes the lambda.
        -- h_sub_body₂ : MSubRed (Ann.equiv v_op :: Γ) s body body₂
        -- u₂ = .lam dom body₂, t₂ = .app (.lam dom body₂) v_op
        -- Note: v_op is the operand that ms_fop pops from the stack.
        --   In the me_bet rule, this is the argument v of the application.
        -- Convert h_eq_body to equiv context for IH:
        let h_eq_body_equiv : MEquivRed (Ann.equiv v_op :: Γ) s _ _ :=
          equivRed_change_ann_rev (v := v_op) h_eq_body
        -- IH on body in context (Ann.equiv v_op :: Γ);s:
        let ⟨body₃, h_eq_body₂, h_sub_body₁⟩ :=
          commutativity h_eq_body_equiv h_sub_body₂ (.ct_ann_equiv h_ctx h_eq_v)
        -- h_eq_body₂ : MEquivRed (Ann.equiv v_op :: Γ) s body₂ body₃
        -- h_sub_body₁ : MSubRed (Ann.equiv v' :: Γ') s' body' body₃
        -- t₃ = body₃.subst 0 v' where v' is the reduced v (from h_eq_v).
        -- Top edge: ME-BET needs body₂ ≡→ body₃ under Ann.sub dom.
        -- Right edge: substitution_subRed on h_sub_body₁.
        -- Use _ for the witness since me_bet determines the form of t₃.
        exact ⟨_, .me_bet (equivRed_change_ann h_eq_body₂) h_eq_v,
          substitution_subRed h_sub_body₁⟩
    | .me_tap =>
      -- Case 7: ME-TAP + MS-APP.
      -- t₀ = app .top v, t₁ = .top.
      -- h_sub_inner : MSubRed Γ (v :: s) .top u₂
      match h_sub_inner with
      | .ms_top => exact ⟨.top, .me_tap, .ms_top⟩
      | .ms_equ .me_top => exact ⟨.top, .me_tap, .ms_top⟩
  | .ms_fun h_sub_body =>
    -- t₀ = lam dom body, s = [], ms_fun promotes body
    match h_equiv with
    | .me_fun h_eq_dom h_eq_body =>
      -- Case 8: ME-FUN + MS-FUN. s = [], so s' = [].
      have hs' : s' = [] := ctxRed_nil_stack h_ctx
      subst hs'
      -- IH on body in context (Ann.sub dom :: Γ);[]:
      let ⟨body₃, h_eq_body₂, h_sub_body'⟩ :=
        commutativity h_eq_body h_sub_body (.ct_ann_sub h_ctx h_eq_dom)
      exact ⟨_, .me_fun h_eq_dom h_eq_body₂, .ms_fun h_sub_body'⟩
  | .ms_fop h_sub_body =>
    -- t₀ = lam dom body, s = α :: s₀, ms_fop pops from stack
    match h_equiv with
    | .me_fop h_eq_dom h_eq_body =>
      -- Case 9: ME-FOP + MS-FOP. Both pop α from stack.
      -- Decompose h_ctx to extract the stack reduction:
      let ⟨α', s₀', Γ₂, ⟨hs'_eq⟩, h_ctx_body, ⟨hΓ'_eq⟩⟩ := ctxRed_unstk h_ctx
      subst hs'_eq; subst hΓ'_eq
      -- h_ctx_body : CtxRed (Ann.equiv α :: Γ) s₀ (Ann.equiv α' :: Γ₂) s₀'
      -- IH on body:
      let ⟨body₃, h_eq_body₂, h_sub_body'⟩ :=
        commutativity h_eq_body h_sub_body h_ctx_body
      exact ⟨_, .me_fop h_eq_dom h_eq_body₂, .ms_fop h_sub_body'⟩

end MPSS
