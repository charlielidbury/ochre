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
  Proof sketch (following Appendix A):
  Case split on (h_sub rule, h_equiv rule). Handle:

  1. MS-TOP (any ≡→): trivial, t₃ = Top
  2. MS-EQU (any ≡→): reduces to diamond property of ≡→ (Lemma 2)
  3. MS-PRO + ME-PRO: impossible (contradictory lookups)
  4. MS-PRO + ME-VAR: uses context reduction + weakening
  5. MS-APP + ME-APP: IH on operator with extended stack
  6. MS-APP + ME-BET: complex case involving MS-FOP decomposition
  7. MS-APP + ME-TAP: top absorbs, t₃ = Top
  8. MS-FUN + ME-FUN: IH on domain and body
  9. MS-FOP + ME-FOP: IH on domain, body, and stack element
  -/
  match h_sub with
  | .ms_top =>
    -- Case 1: t₂ = Top. Take t₃ = Top.
    exact ⟨.top, .me_top, .ms_top⟩
  | .ms_equ h_equiv₂ =>
    -- Case 2: MS-EQU gives t₂ from ≡→ reduction.
    -- Requires diamond property of ≡→ (Lemma 2).
    sorry
  | .ms_pro h_lookup =>
    -- t₀ = bvar k with sub annotation
    match h_equiv with
    | .me_pro h_lookup₂ _ =>
      -- Case 3: Impossible — same index has both sub and equiv annotation.
      rw [h_lookup] at h_lookup₂; exact absurd h_lookup₂ (by simp [Ann.noConfusion])
    | .me_var =>
      -- Case 4: ME-VAR + MS-PRO. t₁ = bvar k, t₂ = t↑.
      -- Requires context reduction and weakening lemmas.
      sorry
  | .ms_app h_sub_inner =>
    -- t₀ = app u v, ms_app pushes v onto stack
    match h_equiv with
    | .me_app h_eq_u h_eq_v =>
      -- Case 5: ME-APP + MS-APP. Both push operand.
      -- By IH on u₀ with stack v₀::s.
      sorry
    | .me_bet h_eq_body h_eq_v =>
      -- Case 6: ME-BET + MS-APP. Beta vs application decomposition.
      sorry
    | .me_tap =>
      -- Case 7: ME-TAP + MS-APP. t₀ = app top u, t₁ = top.
      sorry
  | .ms_fun h_sub_body =>
    -- t₀ = lam dom body, s = [], ms_fun promotes body
    match h_equiv with
    | .me_fun h_eq_dom h_eq_body =>
      -- Case 8: ME-FUN + MS-FUN. Both reduce unapplied lambda.
      -- By IH on body.
      sorry
  | .ms_fop h_sub_body =>
    -- t₀ = lam dom body, s = α :: s₀, ms_fop pops from stack
    match h_equiv with
    | .me_fop h_eq_dom h_eq_body =>
      -- Case 9: ME-FOP + MS-FOP. Both pop from stack.
      -- By IH on body.
      sorry

end MPSS
