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

/-! ## Shift / substitution infrastructure lemmas
    These are used by the substitution and weakening lemmas below. -/

theorem Expr.shift_shift (e : Expr) (d d' c : Nat) :
    (e.shift d c).shift d' c = e.shift (d + d') c := by
  induction e generalizing c with
  | bvar k =>
    simp only [Expr.shift]
    by_cases hkc : k < c
    · simp only [if_pos hkc, Expr.shift, if_pos hkc]
    · simp only [if_neg hkc, Expr.shift, if_neg (show ¬ (k + d < c) by omega), if_neg hkc]
      congr 1; omega
  | top => rfl
  | lam dom body ih_dom ih_body =>
    simp only [Expr.shift]
    exact congr (congrArg Expr.lam (ih_dom c)) (ih_body (c + 1))
  | app f a ih_f ih_a =>
    simp only [Expr.shift]
    exact congr (congrArg Expr.app (ih_f c)) (ih_a c)

/-- `(e.shift 1 c).subst c s = e` — shifting by 1 then substituting cancels. -/
theorem Expr.shift_subst_cancel (e s : Expr) (c : Nat) :
    (e.shift 1 c).subst c s = e := by
  induction e generalizing s c with
  | bvar k =>
    simp only [Expr.shift]
    by_cases hk : k < c
    · simp only [if_pos hk, Expr.subst, beq_iff_eq,
                  if_neg (show ¬(k = c) by omega), if_neg (show ¬(k > c) by omega)]
    · simp only [if_neg hk, Expr.subst, beq_iff_eq,
                  if_neg (show ¬(k + 1 = c) by omega), if_pos (show k + 1 > c by omega)]
      simp only [Expr.bvar.injEq]; omega
  | top => rfl
  | lam dom body ih_dom ih_body =>
    simp only [Expr.shift, Expr.subst]
    exact congr (congrArg Expr.lam (ih_dom s c)) (ih_body (s.shift 1 0) (c + 1))
  | app f a ih_f ih_a =>
    simp only [Expr.shift, Expr.subst]
    exact congr (congrArg Expr.app (ih_f s c)) (ih_a s c)

/-- Generalized shift-subst cancellation:
    `(e.shift (d+1) c).subst (d + c) s = e.shift d c` for any `s`. -/
theorem Expr.shift_subst_cancel_gen (e s : Expr) (d c : Nat) :
    (e.shift (d + 1) c).subst (d + c) s = e.shift d c := by
  induction e generalizing s d c with
  | bvar k =>
    simp only [Expr.shift]
    by_cases hk : k < c
    · simp only [if_pos hk, Expr.subst, beq_iff_eq,
                  if_neg (show ¬(k = d + c) by omega), if_neg (show ¬(k > d + c) by omega),
                  if_pos hk]
    · simp only [if_neg hk, Expr.subst, beq_iff_eq,
                  if_neg (show ¬(k + (d + 1) = d + c) by omega),
                  if_pos (show k + (d + 1) > d + c by omega),
                  if_neg hk]
      simp only [Expr.bvar.injEq]; omega
  | top => rfl
  | lam dom body ih_dom ih_body =>
    simp only [Expr.shift, Expr.subst]
    have hd := ih_dom s d c
    have hb := ih_body (s.shift 1 0) d (c + 1)
    rw [show d + (c + 1) = d + c + 1 from by omega] at hb
    exact congr (congrArg Expr.lam hd) hb
  | app f a ih_f ih_a =>
    simp only [Expr.shift, Expr.subst]
    exact congr (congrArg Expr.app (ih_f s d c)) (ih_a s d c)

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

Note on de Bruijn scoping: ct_stk's MEquivRed uses the context Γ at
the level where ct_stk appears in the derivation. If ct_stk is nested
inside ct_ann_sub, the MEquivRed uses the inner context. Stack elements
are therefore scoped to the context level at which they were reduced.
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

/-! ## Non-promotion predicate (Section 2.2 of MPSS_REDESIGN.md)

`noPromoAt k h` asserts that derivation `h` does not use ME-PRO or MS-PRO
to look up the context annotation at de Bruijn index `k`. This predicate
enables the annotation-change lemma: if a derivation doesn't consult the
annotation at index `k`, the annotation there can be replaced freely. -/

mutual

/-- A `MEquivRed` derivation does not promote (ME-PRO) at index `k`. -/
def MEquivRed.noPromoAt (k : Nat) : MEquivRed Γ s t t' → Prop
  | .me_pro (k := j) _hlook hsub => j ≠ k ∧ hsub.noPromoAt k
  | .me_bet hbody harg => hbody.noPromoAt (k + 1) ∧ harg.noPromoAt k
  | .me_top => True
  | .me_var => True
  | .me_tap => True
  | .me_app hu hv => hu.noPromoAt k ∧ hv.noPromoAt k
  | .me_fun hdom hbody => hdom.noPromoAt k ∧ hbody.noPromoAt (k + 1)
  | .me_fop hdom hbody => hdom.noPromoAt k ∧ hbody.noPromoAt (k + 1)

/-- A `MSubRed` derivation does not promote (MS-PRO) at index `k`. -/
def MSubRed.noPromoAt (k : Nat) : MSubRed Γ s t t' → Prop
  | .ms_pro (k := j) _hlook => j ≠ k
  | .ms_top => True
  | .ms_equ h => h.noPromoAt k
  | .ms_app h => h.noPromoAt k
  | .ms_fun h => h.noPromoAt (k + 1)
  | .ms_fop h => h.noPromoAt (k + 1)

end

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

/-- Weakening for MEquivRed under context reduction (Lemma 22 in paper).
    If Γ₀;s₀ ⊢ t ≡→ t' and Γ₀;s₀ ↦ Γ₁;s₁, then Γ₁;s₁ ⊢ t ≡→ t'.

    BLOCKER: This lemma requires that ≡→ is stable under context reduction.
    In the paper (named variables), this is Lemma 19/22 and follows from
    prevalidity. In de Bruijn, the proof requires showing that ME-PRO
    lookups remain valid after annotation reduction — i.e., if Γ has
    x ≡ α and the annotation reduces to α', then the promotion result
    is unchanged. This needs commutativity-like reasoning (α ≤→ α₁ and
    α ≡→ α' implies α' ≤→ α₁), creating a potential circularity.

    An alternative approach: reformulate this as a "weakening under
    context extension" lemma (adding new bindings, not reducing
    existing ones), which is simpler and avoids the circularity. -/
def weakening_equivRed_ctx
    {Γ₀ : MCtx} {s₀ : Stack} {Γ₁ : MCtx} {s₁ : Stack} {t t' : Expr}
    (h : MEquivRed Γ₀ s₀ t t')
    (hc : CtxRed Γ₀ s₀ Γ₁ s₁)
    : MEquivRed Γ₁ s₁ t t' :=
  sorry

/-! ### Substitution lemmas for ≡→ and ≤→

Proved by mutual structural induction on the derivation.
The generalized version substitutes at arbitrary de Bruijn index j
(needed for under-binder cases) and also substitutes in the stack
(needed for me_app). The specialized index-0 version is derived from it.

Remaining sorrys:
- ME-VAR at target index: needs α ≡→ v' under non-empty stack
- ME-PRO at target index: gives MSubRed but needs MEquivRed
- ME-PRO at k < j and k > j: needs lookup lemmas for adjusted context -/

/-- Adjust context prefix when removing Ann.equiv α at position j.
    Entry at position i < j has its annotation substituted at index (j-i-1)
    with α shifted appropriately. -/
def adjustPrefix : List Ann → Expr → List Ann
  | [], _ => []
  | Ann.sub dom :: rest, α =>
    Ann.sub (dom.subst rest.length (α.shift rest.length 0)) :: adjustPrefix rest α
  | Ann.equiv β :: rest, α =>
    Ann.equiv (β.subst rest.length (α.shift rest.length 0)) :: adjustPrefix rest α

mutual

def substitution_equivRed_gen
    {α : Expr}
    {Γ_above : List Ann} {Γ : MCtx} {s : Stack} {u u' v' : Expr}
    (h_body : MEquivRed (Γ_above ++ Ann.equiv α :: Γ) s u u')
    (h_arg  : MEquivRed Γ [] α v')
    : let j := Γ_above.length
      MEquivRed (adjustPrefix Γ_above α ++ Γ)
                (s.map (·.subst j (α.shift j 0)))
                (u.subst j (α.shift j 0))
                (u'.subst j (v'.shift j 0)) := by
  let j := Γ_above.length
  match h_body with
  | .me_top => exact .me_top
  | @MEquivRed.me_tap _ _ u_arg => exact .me_tap
  | @MEquivRed.me_var _ _ k =>
    show MEquivRed _ _ ((Expr.bvar k).subst j _) ((Expr.bvar k).subst j _)
    simp only [Expr.subst]
    by_cases hkj : k = j
    · subst hkj; simp only [beq_self_eq_true, ite_true]
      sorry  -- STUCK: need α ≡→ v' under stack s.map
    · simp only [show (k == j) = false from by simp [beq_iff_eq, hkj]]
      by_cases hkj' : k > j
      · simp only [if_pos hkj']; exact .me_var
      · simp only [if_neg hkj']; exact .me_var
  | @MEquivRed.me_pro _ _ _ k α_ann hlook hsub =>
    show MEquivRed _ _ ((Expr.bvar k).subst j _) _
    simp only [Expr.subst]
    by_cases hkj : k = j
    · subst hkj; simp only [beq_self_eq_true, ite_true]
      sorry  -- STUCK: MSubRed → MEquivRed conversion
    · simp only [show (k == j) = false from by simp [beq_iff_eq, hkj]]
      by_cases hkj' : k > j
      · simp only [if_pos hkj']
        sorry  -- needs lookup lemma for k > j in adjusted context
      · simp only [if_neg hkj']
        sorry  -- needs lookup lemma for k < j in adjusted context
  | @MEquivRed.me_app _ _ _ u₁ _ v₁ h_u h_v =>
    -- me_app: IH on operator with v₁::s stack, IH on operand with [] stack
    have h_u' := substitution_equivRed_gen h_u h_arg
    simp only [List.map_cons] at h_u'
    have h_v' := substitution_equivRed_gen h_v h_arg
    simp only [List.map_nil] at h_v'
    exact .me_app h_u' h_v'
  | @MEquivRed.me_bet _ _ dom body _ v₁ _ h_body_inner h_v =>
    -- me_bet: body under (Ann.sub dom :: Γ_above ++ Ann.equiv α :: Γ)
    -- Use IH with extended Γ_above' = Ann.sub dom :: Γ_above
    have h_v' := substitution_equivRed_gen h_v h_arg
    simp only [List.map_nil] at h_v'
    have h_body' := @substitution_equivRed_gen α (Ann.sub dom :: Γ_above) Γ _ _ _ _ h_body_inner h_arg
    simp only [List.length_cons] at h_body'
    -- Need to show output equation: (body'.subst 0 v₁').subst j (v'.shift j 0)
    -- = (body'.subst (j+1) (v'.shift (j+1) 0)).subst 0 (v₁'.subst j (v'.shift j 0))
    -- This is subst_subst_comm_zero applied appropriately.
    sorry  -- STUCK: needs subst_subst_comm for me_bet output
  | @MEquivRed.me_fun _ dom _ body' _ h_dom h_body_inner =>
    -- me_fun: s = [], body under (Ann.sub dom :: Γ_above ++ Ann.equiv α :: Γ)
    simp only [List.map_nil]
    have h_dom' := substitution_equivRed_gen h_dom h_arg
    simp only [List.map_nil] at h_dom'
    have h_body' := @substitution_equivRed_gen α (Ann.sub dom :: Γ_above) Γ [] _ _ _ h_body_inner h_arg
    simp only [List.map_nil, List.length_cons, adjustPrefix] at h_body'
    -- Unfold subst on lam to expose the shift pattern
    simp only [Expr.subst]
    rw [@Expr.shift_shift α Γ_above.length 1 0, @Expr.shift_shift v' Γ_above.length 1 0]
    exact .me_fun h_dom' h_body'
  | @MEquivRed.me_fop _ _ α_stk dom _ body' _ h_dom h_body_inner =>
    -- STUCK: the body IH substitutes the stack at index j+1 (body scope),
    -- but me_fop needs the stack substituted at index j (outer scope).
    -- These differ because stack elements are at the outer scope.
    sorry

def substitution_subRed_gen
    {α : Expr}
    {Γ_above : List Ann} {Γ : MCtx} {s : Stack} {u u' : Expr}
    (h : MSubRed (Γ_above ++ Ann.equiv α :: Γ) s u u')
    : let j := Γ_above.length
      MSubRed (adjustPrefix Γ_above α ++ Γ)
              (s.map (·.subst j (α.shift j 0)))
              (u.subst j (α.shift j 0))
              (u'.subst j (α.shift j 0)) := by
  let j := Γ_above.length
  match h with
  | .ms_top => exact .ms_top
  | @MSubRed.ms_pro _ _ k bound hlook =>
    show MSubRed _ _ ((Expr.bvar k).subst j _) _
    simp only [Expr.subst]
    by_cases hkj : k = j
    · -- k = j: impossible! Position j is Ann.equiv α, but ms_pro needs Ann.sub.
      subst hkj
      have : (Γ_above ++ Ann.equiv α :: Γ).get? Γ_above.length = some (Ann.equiv α) := by
        rw [List.get?_append_right (Nat.le_refl _)]; simp
      rw [this] at hlook; cases hlook
    · simp only [show (k == j) = false from by simp [beq_iff_eq, hkj]]
      by_cases hkj' : k > j
      · simp only [if_pos hkj']
        sorry  -- needs lookup lemma for k > j
      · simp only [if_neg hkj']
        sorry  -- needs lookup lemma for k < j
  | @MSubRed.ms_equ _ _ _ _ h_eq =>
    exact .ms_equ (substitution_equivRed_gen h_eq (equivRed_refl Γ [] α))
  | @MSubRed.ms_app _ _ _ _ v₁ h_inner =>
    simp only [List.map_cons]
    exact .ms_app (substitution_subRed_gen h_inner)
  | @MSubRed.ms_fun _ dom _ _ h_body =>
    simp only [List.map_nil, Expr.subst]
    have h_body' := @substitution_subRed_gen α (Ann.sub dom :: Γ_above) Γ [] _ _ h_body
    simp only [List.map_nil, List.length_cons, adjustPrefix] at h_body'
    rw [@Expr.shift_shift α Γ_above.length 1 0]
    exact .ms_fun h_body'
  | @MSubRed.ms_fop _ _ α_stk _ _ _ h_body =>
    -- STUCK: same stack scope mismatch as me_fop
    sorry

end

/-- Substitution lemma for ≡→ (Lemma 32, specialized to index 0).
    The generalized version outputs stack `s.map (·.subst 0 α)`, but at call
    sites the stack is at the outer scope (no bvar 0 refs), so the map is id.
    This is sorry'd pending a formal well-scopedness argument. -/
def substitution_equivRed
    {α : Expr}
    {Γ : MCtx} {s : Stack} {u u' v' : Expr}
    (h_body : MEquivRed (Ann.equiv α :: Γ) s u u')
    (h_arg  : MEquivRed Γ [] α v')
    : MEquivRed Γ s (u.subst 0 α) (u'.subst 0 v') := by
  have h := @substitution_equivRed_gen α [] Γ s u u' v' h_body h_arg
  simp only [adjustPrefix, List.nil_append, List.length_nil, Expr.shift_zero] at h
  -- h has s.map (·.subst 0 α) but we need s. At call sites, stack is at outer
  -- scope so map is identity, but this needs a well-scopedness proof.
  exact sorry

/-- Substitution lemma for ≤→ (Lemma 30, specialized to index 0). -/
def substitution_subRed
    {v₀ : Expr}
    {Γ : MCtx} {s : Stack} {u₁ u₃ : Expr}
    (h : MSubRed (Ann.equiv v₀ :: Γ) s u₁ u₃)
    : MSubRed Γ s (u₁.subst 0 v₀) (u₃.subst 0 v₀) := by
  have h' := @substitution_subRed_gen v₀ [] Γ s u₁ u₃ h
  simp only [adjustPrefix, List.nil_append, List.length_nil, Expr.shift_zero] at h'
  exact sorry

/-- Replace the element at position `n` in a list.
    Returns the list unchanged if `n` is out of bounds. -/
def setAnnAt (l : List Ann) (n : Nat) (a : Ann) : List Ann :=
  match l, n with
  | [], _ => []
  | _ :: xs, 0 => a :: xs
  | x :: xs, n + 1 => x :: setAnnAt xs n a

/-- setAnnAt at a different position preserves get?. -/
theorem setAnnAt_get?_ne {l : List Ann} {i n : Nat} {a : Ann} (h : i ≠ n) :
    (setAnnAt l n a).get? i = l.get? i := by
  induction l generalizing n i with
  | nil => simp [setAnnAt]
  | cons x xs ih =>
    cases n with
    | zero =>
      cases i with
      | zero => exact absurd rfl h
      | succ i => simp [setAnnAt]
    | succ n =>
      cases i with
      | zero => simp [setAnnAt]
      | succ i =>
        simp only [setAnnAt, List.get?]
        exact ih (fun heq => h (by omega))

/-- setAnnAt with a cons: setting at position n+1 is the same as setting in the tail. -/
theorem setAnnAt_cons_succ {x : Ann} {xs : List Ann} {n : Nat} {a : Ann} :
    setAnnAt (x :: xs) (n + 1) a = x :: setAnnAt xs n a := by
  simp [setAnnAt]

/-! ### Annotation-change lemma (replaces false `equivRed_change_ann`)

If a derivation under `Γ` does not promote at index `n`, then the
annotation at position `n` is never consulted, so we can replace it
with any other annotation `ann2`. We prove the generalized version
for arbitrary `n`, then specialise to `n = 0`.

The proof is mutual structural induction on `MEquivRed`/`MSubRed`.
Under binders (`me_bet`, `me_fun`, `me_fop`, `ms_fun`, `ms_fop`) the
index shifts by 1, matching the `noPromoAt (k + 1)` in the predicate.
For `me_pro`/`ms_pro` at index `j`, the hypothesis `j ≠ n` (from
`noPromoAt`) ensures the lookup `Γ.get? j` is unaffected by the
replacement at position `n`. -/

mutual

def equivRed_no_promo_change_ann_at
    {Γ : MCtx} {s : Stack} {t t' : Expr} (n : Nat) (ann2 : Ann)
    (h : MEquivRed Γ s t t')
    (hnp : h.noPromoAt n) :
    MEquivRed (setAnnAt Γ n ann2) s t t' := by
  match h with
  | .me_top => exact .me_top
  | .me_var => exact .me_var
  | .me_tap => exact .me_tap
  | @MEquivRed.me_pro _ _ _ j α hlook hsub =>
    simp only [MEquivRed.noPromoAt] at hnp
    obtain ⟨hne, hnp_sub⟩ := hnp
    have hlook' : (setAnnAt Γ n ann2).get? j = some (Ann.equiv α) := by
      rw [setAnnAt_get?_ne hne]; exact hlook
    exact .me_pro hlook' (subRed_no_promo_change_ann_at n ann2 hsub hnp_sub)
  | .me_app hu hv =>
    simp only [MEquivRed.noPromoAt] at hnp
    obtain ⟨hnp_u, hnp_v⟩ := hnp
    exact .me_app (equivRed_no_promo_change_ann_at n ann2 hu hnp_u)
                  (equivRed_no_promo_change_ann_at n ann2 hv hnp_v)
  | @MEquivRed.me_bet _ _ dom _ _ _ _ hbody harg =>
    simp only [MEquivRed.noPromoAt] at hnp
    obtain ⟨hnp_body, hnp_arg⟩ := hnp
    have heq : setAnnAt (Ann.sub dom :: Γ) (n + 1) ann2 = Ann.sub dom :: setAnnAt Γ n ann2 := by
      simp [setAnnAt]
    exact .me_bet (heq ▸ equivRed_no_promo_change_ann_at (n + 1) ann2 hbody hnp_body)
                  (equivRed_no_promo_change_ann_at n ann2 harg hnp_arg)
  | @MEquivRed.me_fun _ dom _ _ _ hdom hbody =>
    simp only [MEquivRed.noPromoAt] at hnp
    obtain ⟨hnp_dom, hnp_body⟩ := hnp
    have heq : setAnnAt (Ann.sub dom :: Γ) (n + 1) ann2 = Ann.sub dom :: setAnnAt Γ n ann2 := by
      simp [setAnnAt]
    exact .me_fun (equivRed_no_promo_change_ann_at n ann2 hdom hnp_dom)
                  (heq ▸ equivRed_no_promo_change_ann_at (n + 1) ann2 hbody hnp_body)
  | @MEquivRed.me_fop _ _ α _ _ _ _ hdom hbody =>
    simp only [MEquivRed.noPromoAt] at hnp
    obtain ⟨hnp_dom, hnp_body⟩ := hnp
    have heq : setAnnAt (Ann.equiv α :: Γ) (n + 1) ann2 = Ann.equiv α :: setAnnAt Γ n ann2 := by
      simp [setAnnAt]
    exact .me_fop (equivRed_no_promo_change_ann_at n ann2 hdom hnp_dom)
                  (heq ▸ equivRed_no_promo_change_ann_at (n + 1) ann2 hbody hnp_body)

def subRed_no_promo_change_ann_at
    {Γ : MCtx} {s : Stack} {t t' : Expr} (n : Nat) (ann2 : Ann)
    (h : MSubRed Γ s t t')
    (hnp : h.noPromoAt n) :
    MSubRed (setAnnAt Γ n ann2) s t t' := by
  match h with
  | .ms_top => exact .ms_top
  | @MSubRed.ms_pro _ _ j bound hlook =>
    simp only [MSubRed.noPromoAt] at hnp
    have hlook' : (setAnnAt Γ n ann2).get? j = some (Ann.sub bound) := by
      rw [setAnnAt_get?_ne hnp]; exact hlook
    exact .ms_pro hlook'
  | .ms_equ heq =>
    simp only [MSubRed.noPromoAt] at hnp
    exact .ms_equ (equivRed_no_promo_change_ann_at n ann2 heq hnp)
  | .ms_app hinner =>
    simp only [MSubRed.noPromoAt] at hnp
    exact .ms_app (subRed_no_promo_change_ann_at n ann2 hinner hnp)
  | @MSubRed.ms_fun _ dom _ _ hbody =>
    simp only [MSubRed.noPromoAt] at hnp
    have heq : setAnnAt (Ann.sub dom :: Γ) (n + 1) ann2 = Ann.sub dom :: setAnnAt Γ n ann2 := by
      simp [setAnnAt]
    exact .ms_fun (heq ▸ subRed_no_promo_change_ann_at (n + 1) ann2 hbody hnp)
  | @MSubRed.ms_fop _ _ α _ _ _ hbody =>
    simp only [MSubRed.noPromoAt] at hnp
    have heq : setAnnAt (Ann.equiv α :: Γ) (n + 1) ann2 = Ann.equiv α :: setAnnAt Γ n ann2 := by
      simp [setAnnAt]
    exact .ms_fop (heq ▸ subRed_no_promo_change_ann_at (n + 1) ann2 hbody hnp)

end

/-- Specialization: if a derivation under `(ann1 :: Γ)` does not promote at
    index 0, the head annotation can be replaced by any `ann2`. -/
def equivRed_no_promo_change_ann_at_zero
    {Γ : MCtx} {s : Stack} {t t' : Expr} {ann1 ann2 : Ann}
    (h : MEquivRed (ann1 :: Γ) s t t')
    (hnp : h.noPromoAt 0) :
    MEquivRed (ann2 :: Γ) s t t' :=
  have heq : setAnnAt (ann1 :: Γ) 0 ann2 = ann2 :: Γ := by simp [setAnnAt]
  heq ▸ equivRed_no_promo_change_ann_at 0 ann2 h hnp

/-- Specialization for MSubRed: if a derivation under `(ann1 :: Γ)` does not
    promote at index 0, the head annotation can be replaced by any `ann2`. -/
def subRed_no_promo_change_ann_at_zero
    {Γ : MCtx} {s : Stack} {t t' : Expr} {ann1 ann2 : Ann}
    (h : MSubRed (ann1 :: Γ) s t t')
    (hnp : h.noPromoAt 0) :
    MSubRed (ann2 :: Γ) s t t' :=
  have heq : setAnnAt (ann1 :: Γ) 0 ann2 = ann2 :: Γ := by simp [setAnnAt]
  heq ▸ subRed_no_promo_change_ann_at 0 ann2 h hnp

-- Generalized annotation change: replace a sub annotation at any position n
-- with any other annotation. The key property is that ME-PRO cannot fire
-- on Ann.sub annotations, so the derivation never depends on this position
-- for promotion. MS-PRO at this position is also unreachable because shifted
-- annotations from ME-PRO never reference the target position.
--
-- We prove both MEquivRed and MSubRed variants mutually.
mutual

private def equivRed_change_sub_at
    {Γ : MCtx} {s : Stack} {t t' : Expr} (n : Nat) (a : Ann)
    (h_sub : ∃ d, Γ.get? n = some (Ann.sub d))
    (h : MEquivRed Γ s t t')
    : MEquivRed (setAnnAt Γ n a) s t t' := by
  match h with
  | .me_top => exact .me_top
  | .me_var => exact .me_var
  | .me_tap => exact .me_tap
  | @MEquivRed.me_pro _ _ _ k α hlook hsub' =>
    have hne : k ≠ n := by
      obtain ⟨d, hd⟩ := h_sub
      intro heq; subst heq; rw [hlook] at hd; cases hd
    have hlook' : (setAnnAt Γ n a).get? k = some (Ann.equiv α) := by
      rw [setAnnAt_get?_ne hne]; exact hlook
    exact .me_pro hlook' (subRed_change_sub_at n a h_sub hsub')
  | .me_app h_u h_v =>
    exact .me_app (equivRed_change_sub_at n a h_sub h_u)
                  (equivRed_change_sub_at n a h_sub h_v)
  | @MEquivRed.me_bet _ _ dom _ _ _ _ h_body h_arg =>
    have h_sub' : ∃ d, (Ann.sub dom :: Γ).get? (n + 1) = some (Ann.sub d) := by
      exact h_sub
    have heq : setAnnAt (Ann.sub dom :: Γ) (n + 1) a = Ann.sub dom :: setAnnAt Γ n a := by
      simp [setAnnAt]
    rw [heq] at *
    exact .me_bet (equivRed_change_sub_at (n + 1) a h_sub' h_body)
                  (equivRed_change_sub_at n a h_sub h_arg)
  | @MEquivRed.me_fun _ dom _ _ _ h_dom h_body =>
    have h_sub' : ∃ d, (Ann.sub dom :: Γ).get? (n + 1) = some (Ann.sub d) := by
      exact h_sub
    have heq : setAnnAt (Ann.sub dom :: Γ) (n + 1) a = Ann.sub dom :: setAnnAt Γ n a := by
      simp [setAnnAt]
    exact .me_fun (equivRed_change_sub_at n a h_sub h_dom)
                  (heq ▸ equivRed_change_sub_at (n + 1) a h_sub' h_body)
  | @MEquivRed.me_fop _ _ α _ _ _ _ h_dom h_body =>
    have h_sub' : ∃ d, (Ann.equiv α :: Γ).get? (n + 1) = some (Ann.sub d) := by
      exact h_sub
    have heq : setAnnAt (Ann.equiv α :: Γ) (n + 1) a = Ann.equiv α :: setAnnAt Γ n a := by
      simp [setAnnAt]
    exact .me_fop (equivRed_change_sub_at n a h_sub h_dom)
                  (heq ▸ equivRed_change_sub_at (n + 1) a h_sub' h_body)

private def subRed_change_sub_at
    {Γ : MCtx} {s : Stack} {t t' : Expr} (n : Nat) (a : Ann)
    (h_sub_ann : ∃ d, Γ.get? n = some (Ann.sub d))
    (h : MSubRed Γ s t t')
    : MSubRed (setAnnAt Γ n a) s t t' := by
  match h with
  | .ms_top => exact .ms_top
  | @MSubRed.ms_pro _ _ k bound hlook =>
    by_cases hne : k = n
    · -- k = n: the derivation promotes bvar n using the sub annotation.
      -- This case should be unreachable from the call sites.
      exact sorry
    · have hlook' : (setAnnAt Γ n a).get? k = some (Ann.sub bound) := by
        rw [setAnnAt_get?_ne hne]; exact hlook
      exact .ms_pro hlook'
  | .ms_equ h_eq =>
    exact .ms_equ (equivRed_change_sub_at n a h_sub_ann h_eq)
  | .ms_app h_inner =>
    exact .ms_app (subRed_change_sub_at n a h_sub_ann h_inner)
  | @MSubRed.ms_fun _ dom _ _ h_body =>
    have h_sub' : ∃ d, (Ann.sub dom :: Γ).get? (n + 1) = some (Ann.sub d) := by
      exact h_sub_ann
    have heq : setAnnAt (Ann.sub dom :: Γ) (n + 1) a = Ann.sub dom :: setAnnAt Γ n a := by
      simp [setAnnAt]
    rw [heq] at *
    exact .ms_fun (subRed_change_sub_at (n + 1) a h_sub' h_body)
  | @MSubRed.ms_fop _ _ α _ _ _ h_body =>
    have h_sub' : ∃ d, (Ann.equiv α :: Γ).get? (n + 1) = some (Ann.sub d) := by
      exact h_sub_ann
    have heq : setAnnAt (Ann.equiv α :: Γ) (n + 1) a = Ann.equiv α :: setAnnAt Γ n a := by
      simp [setAnnAt]
    rw [heq] at *
    exact .ms_fop (subRed_change_sub_at (n + 1) a h_sub' h_body)

end

-- NOTE: The false lemma `equivRed_change_ann` (equiv → sub direction)
-- has been DELETED. It was disproved: ME-PRO CAN fire on Ann.equiv
-- at index 0, so the annotation cannot be freely changed from equiv
-- to sub. Use `equivRed_no_promo_change_ann_at_zero` instead, which
-- requires proving that the derivation does not promote at index 0.

/-- Annotation-insensitive equivalence reduction (sub → equiv direction).
    If MEquivRed (Ann.sub dom :: Γ) s body body', then also
    MEquivRed (Ann.equiv v :: Γ) s body body'.

    Proved via the generalized equivRed_change_sub_at: the source has
    Ann.sub at position 0, which we replace with Ann.equiv v. ME-PRO
    cannot fire on Ann.sub annotations, so the derivation doesn't
    depend on the specific annotation at position 0.

    MS-PRO at position 0 is blocked by a sorry in the generalized
    helper (the k=n case of subRed_change_sub_at). This case should
    be unreachable from the call chain but hasn't been formally proven. -/
def equivRed_change_ann_rev
    {Γ : MCtx} {s : Stack} {v dom body body' : Expr}
    (h : MEquivRed (Ann.sub dom :: Γ) s body body')
    : MEquivRed (Ann.equiv v :: Γ) s body body' :=
  have h_sub : ∃ d, (Ann.sub dom :: Γ).get? 0 = some (Ann.sub d) := ⟨dom, by simp [List.get?]⟩
  have heq : setAnnAt (Ann.sub dom :: Γ) 0 (Ann.equiv v) = Ann.equiv v :: Γ := by simp [setAnnAt]
  heq ▸ equivRed_change_sub_at 0 (Ann.equiv v) h_sub h

/-- Decomposition of CtxRed with non-empty stack for the ME-FOP case.
    Given Γ;(α :: s₀) ↦ Γ';s', decompose into:
    1. The output stack is α' :: s₀' (non-empty)
    2. The body CtxRed: (Ann.equiv α :: Γ);s₀ ↦ (Ann.equiv α' :: Γ₂);s₀'
    3. Γ' = Γ₂

    The ct_stk case is closed: ct_ann_equiv hc hα directly gives
    the desired body CtxRed.

    The ct_ann_sub/ct_ann_equiv cases are BLOCKED. When ct_stk is nested
    inside ct_ann_sub, the stack element's MEquivRed uses the inner context
    Γ_tail, but we need a CtxRed in the extended context (Ann.sub t :: Γ_tail).
    Building the body CtxRed requires:
      MEquivRed (Ann.sub t :: Γ_tail) [] α α'
    from MEquivRed Γ_tail [] α α' — a weakening-under-context-extension lemma.
    In de Bruijn, this requires shifting (α, α') and proving:
      equivRed_weaken_one : MEquivRed Γ s t t' → MEquivRed (a :: Γ) s (t.shift 1 0) (t'.shift 1 0)
    But the stack elements are stored UNSHIFTED in CtxRed, so the shifted
    version doesn't match the expected type. This is a fundamental encoding
    issue: the paper uses named variables where context extension doesn't
    affect term representations.

    Possible fixes:
    1. Prove equivRed_weaken_one (using shift_comm from Syntax.lean) and
       store SHIFTED stack elements in CtxRed.
    2. Restructure CtxRed so ct_stk is always outermost (but then extending
       with ct_ann_sub also needs weakening for ct_stk's MEquivRed).
    3. Add a separate "stack reduction" layer decoupled from context reduction. -/
def ctxRed_unstk
    {Γ : MCtx} {α : Expr} {s₀ : Stack} {Γ' : MCtx} {s' : Stack}
    (h : CtxRed Γ (α :: s₀) Γ' s')
    : Σ' (α' : Expr) (s₀' : Stack) (Γ₂ : MCtx),
        PLift (s' = α' :: s₀') ×
        CtxRed (Ann.equiv α :: Γ) s₀ (Ann.equiv α' :: Γ₂) s₀' ×
        PLift (Γ' = Γ₂) :=
  match h with
  | .ct_stk hc hα =>
    -- Direct: hc : CtxRed Γ s₀ Γ' s₀', hα : MEquivRed Γ [] α α'
    ⟨_, _, _, ⟨rfl⟩, .ct_ann_equiv hc hα, ⟨rfl⟩⟩
  | .ct_ann_sub hc_inner _ => by
    -- Γ = Ann.sub t :: Γ_tail. Recurse on the inner CtxRed.
    obtain ⟨α', s₀', Γ₂, ⟨hs'_eq⟩, hc_body, ⟨hΓ_eq⟩⟩ := ctxRed_unstk hc_inner
    subst hs'_eq; subst hΓ_eq
    -- hc_body : CtxRed (Ann.equiv α :: Γ_tail) s₀ (Ann.equiv α' :: Γ₂) s₀'
    -- Need: CtxRed (Ann.equiv α :: Ann.sub t :: Γ_tail) s₀ (Ann.equiv α' :: Ann.sub t' :: Γ₂) s₀'
    -- BLOCKED: needs MEquivRed weakening under context extension.
    exact ⟨α', s₀', _, ⟨rfl⟩, sorry, ⟨rfl⟩⟩
  | .ct_ann_equiv hc_inner _ => by
    -- Same blocker as ct_ann_sub.
    obtain ⟨α', s₀', Γ₂, ⟨hs'_eq⟩, _, ⟨hΓ_eq⟩⟩ := ctxRed_unstk hc_inner
    subst hs'_eq; subst hΓ_eq
    exact ⟨α', s₀', _, ⟨rfl⟩, sorry, ⟨rfl⟩⟩

/-- Lemma 36 in the paper: strip the stack component from a CtxRed.
    If Γ;s ↦ Γ';s', then Γ;nil ↦ Γ';nil.
    Proved by induction on CtxRed. -/
def ctxRed_nil_of_ctxRed : CtxRed Γ s Γ' s' → CtxRed Γ [] Γ' []
  | .ct_nil => .ct_nil
  | .ct_ann_sub hc hd => .ct_ann_sub (ctxRed_nil_of_ctxRed hc) hd
  | .ct_ann_equiv hc hα => .ct_ann_equiv (ctxRed_nil_of_ctxRed hc) hα
  | .ct_stk hc _ => ctxRed_nil_of_ctxRed hc

/-- Diamond property for ≡→ (Lemma 2 in paper).
    If Γ₀;s₀ ⊢ t₀ ≡→ t₁ and Γ₀;s₀ ⊢ t₀ ≡→ t₂ then for any extended contexts
    Γ₁;s₁ and Γ₂;s₂ with Γ₀;s₀ ↦ Γ₁;s₁ and Γ₀;s₀ ↦ Γ₂;s₂, there exists t₃
    such that Γ₁;s₁ ⊢ t₁ ≡→ t₃ and Γ₂;s₂ ⊢ t₂ ≡→ t₃.

    Proof by case analysis on (h₁, h₂). Recursive calls provide the IH. -/
def diamond
    {Γ₀ : MCtx} {s₀ : Stack} {t₀ t₁ t₂ : Expr}
    {Γ₁ Γ₂ : MCtx} {s₁ s₂ : Stack}
    (h₁ : MEquivRed Γ₀ s₀ t₀ t₁)
    (h₂ : MEquivRed Γ₀ s₀ t₀ t₂)
    (hc₁ : CtxRed Γ₀ s₀ Γ₁ s₁)
    (hc₂ : CtxRed Γ₀ s₀ Γ₂ s₂)
    : Σ' t₃ : Expr, MEquivRed Γ₁ s₁ t₁ t₃ × MEquivRed Γ₂ s₂ t₂ t₃ :=
  match h₁, h₂ with
  /-=== Case ME-TOP + ME-TOP: t₀ = Top, t₁ = Top, t₂ = Top ===-/
  | .me_top, .me_top =>
    ⟨.top, .me_top, .me_top⟩

  /-=== Case ME-VAR + ME-VAR: t₀ = bvar k, t₁ = bvar k, t₂ = bvar k ===-/
  | .me_var, .me_var =>
    ⟨.bvar _, .me_var, .me_var⟩

  /-=== Case ME-VAR + ME-PRO: t₀ = bvar k, t₁ = bvar k, t₂ = α' ===-/
  | .me_var, @MEquivRed.me_pro _ _ α' k α hlook₂ hsub₂ =>
    -- h₂ promotes x to α'. By weakening, Γ₁;s₁ ⊢ bvar k ≡→ α'.
    ⟨α', weakening_equivRed_ctx (.me_pro hlook₂ hsub₂) hc₁, equivRed_refl Γ₂ s₂ α'⟩

  /-=== Case ME-PRO + ME-VAR: symmetric ===-/
  | @MEquivRed.me_pro _ _ α' k α hlook₁ hsub₁, .me_var =>
    ⟨α', equivRed_refl Γ₁ s₁ α', weakening_equivRed_ctx (.me_pro hlook₁ hsub₁) hc₂⟩

  /-=== Case ME-PRO + ME-PRO: both promote bvar k ===-/
  -- Both look up x ≡ α₀ ∈ Γ₀. The annotation is unique, so α₀ is the same.
  -- h₁ : Γ₀;s₀ ⊢ α₀↑ ≤→ α₁  and  h₂ : Γ₀;s₀ ⊢ α₀↑ ≤→ α₂
  -- The IH would be on α₀ (which is structurally smaller), but this requires
  -- a diamond property for MSubRed or a combined mutual diamond.
  -- For now, sorry this case.
  | .me_pro _ _, .me_pro _ _ =>
    sorry

  /-=== Case ME-TAP + ME-TAP: t₀ = app Top u, both give Top ===-/
  | .me_tap, .me_tap =>
    ⟨.top, .me_top, .me_top⟩

  /-=== Case ME-TAP + ME-APP: t₀ = app Top u ===-/
  -- h₁ = ME-TAP gives t₁ = Top
  -- h₂ = ME-APP: the operator reduction on Top must be ME-TOP.
  | .me_tap, .me_app h₂_u _ =>
    match h₂_u with
    | .me_top => ⟨.top, .me_top, .me_tap⟩

  /-=== Case ME-APP + ME-TAP: symmetric ===-/
  | .me_app h₁_u _, .me_tap =>
    match h₁_u with
    | .me_top => ⟨.top, .me_tap, .me_top⟩

  /-=== Case ME-APP + ME-APP: t₀ = app u₀ v₀ ===-/
  | @MEquivRed.me_app _ _ u₀ u₁ v₀ v₁ h₁_u h₁_v,
    @MEquivRed.me_app _ _ _ u₂ _ v₂ h₂_u h₂_v =>
    -- Build extended context reductions with v on stack
    let hc₁' := CtxRed.ct_stk hc₁ h₁_v
    let hc₂' := CtxRed.ct_stk hc₂ h₂_v
    -- IH on operator u₀ with stack v₀::s₀
    let ⟨u₃, hu₁, hu₂⟩ := diamond h₁_u h₂_u hc₁' hc₂'
    -- IH on operand v₀ with nil stack (using Lemma 36)
    let ⟨v₃, hv₁, hv₂⟩ := diamond h₁_v h₂_v
      (ctxRed_nil_of_ctxRed hc₁) (ctxRed_nil_of_ctxRed hc₂)
    ⟨.app u₃ v₃,
      .me_app hu₁ hv₁,
      .me_app hu₂ hv₂⟩

  /-=== Case ME-APP + ME-BET: t₀ = app (lam dom body) v₀ ===-/
  -- h₁ = ME-APP with ME-FOP on the lambda
  -- h₂ = ME-BET: β-reduces
  -- This is the key case from the paper (ME-App with ME-Bet).
  -- For now, sorry this case as it requires careful unification of
  -- the operand variable across both patterns.
  | .me_app h₁_u h₁_v, .me_bet h₂_body h₂_v =>
    match h₁_u with
    | .me_fop h₁_dom h₁_body =>
      -- h₁_body : MEquivRed (Ann.equiv v :: Γ₀) s₀ body body₁'
      --   where v is the operand from the stack
      -- h₂_body : MEquivRed (Ann.sub dom :: Γ₀) s₀ body body₂'
      -- Convert h₂_body to equiv context:
      let h₂_body_equiv := equivRed_change_ann_rev h₂_body
      -- Build context reductions for (Ann.equiv v :: Γ₀);s₀
      let hc₁_body := CtxRed.ct_ann_equiv hc₁ h₁_v
      let hc₂_body := CtxRed.ct_ann_equiv hc₂ h₂_v
      -- IH on body
      let ⟨body₃, hbody₁, hbody₂⟩ := diamond h₁_body h₂_body_equiv hc₁_body hc₂_body
      -- IH on operand
      let ⟨v₃, hv₁, hv₂⟩ := diamond h₁_v h₂_v
        (ctxRed_nil_of_ctxRed hc₁) (ctxRed_nil_of_ctxRed hc₂)
      -- Left completion: ME-BET on t₁ = app (lam dom₁' body₁') v₁
      -- hbody₁ : MEquivRed (Ann.equiv v₁' :: Γ₁) s₁ ... body₃
      -- Need to change annotation from equiv to sub for ME-BET.
      -- The diamond (Lemma 2) guarantees noPromoAt for the output
      -- when the input doesn't promote at that variable (paper p.9:20).
      let hbody₁_np : hbody₁.noPromoAt 0 := sorry
      let hbody₁_sub := equivRed_no_promo_change_ann_at_zero hbody₁ hbody₁_np
      -- Right completion: substitution on t₂ = u'[0↦v₂]
      -- hbody₂ : MEquivRed (Ann.equiv v₂' :: Γ₂) s₂ body₂'_equiv body₃
      -- hv₂ : MEquivRed Γ₂ [] v₂ v₃
      ⟨body₃.subst 0 v₃,
        .me_bet hbody₁_sub hv₁,
        substitution_equivRed hbody₂ hv₂⟩

  /-=== Case ME-BET + ME-APP: symmetric ===-/
  | .me_bet h₁_body h₁_v, .me_app h₂_u h₂_v =>
    match h₂_u with
    | .me_fop h₂_dom h₂_body =>
      let h₁_body_equiv := equivRed_change_ann_rev h₁_body
      let hc₁_body := CtxRed.ct_ann_equiv hc₁ h₁_v
      let hc₂_body := CtxRed.ct_ann_equiv hc₂ h₂_v
      let ⟨body₃, hbody₁, hbody₂⟩ := diamond h₁_body_equiv h₂_body hc₁_body hc₂_body
      let ⟨v₃, hv₁, hv₂⟩ := diamond h₁_v h₂_v
        (ctxRed_nil_of_ctxRed hc₁) (ctxRed_nil_of_ctxRed hc₂)
      let hbody₂_np : hbody₂.noPromoAt 0 := sorry
      let hbody₂_sub := equivRed_no_promo_change_ann_at_zero hbody₂ hbody₂_np
      ⟨body₃.subst 0 v₃,
        substitution_equivRed hbody₁ hv₁,
        .me_bet hbody₂_sub hv₂⟩

  /-=== Case ME-BET + ME-BET: t₀ = app (lam dom body) v₀ ===-/
  | .me_bet h₁_body h₁_v, .me_bet h₂_body h₂_v =>
    -- Convert body reductions to equiv context
    let h₁_body_equiv := equivRed_change_ann_rev h₁_body
    let h₂_body_equiv := equivRed_change_ann_rev h₂_body
    -- Build context reductions for body
    let hc₁_body := CtxRed.ct_ann_equiv hc₁ h₁_v
    let hc₂_body := CtxRed.ct_ann_equiv hc₂ h₂_v
    -- IH on body and operand
    let ⟨body₃, hbody₁, hbody₂⟩ := diamond h₁_body_equiv h₂_body_equiv hc₁_body hc₂_body
    let ⟨v₃, hv₁, hv₂⟩ := diamond h₁_v h₂_v
      (ctxRed_nil_of_ctxRed hc₁) (ctxRed_nil_of_ctxRed hc₂)
    -- Substitution lemma for both sides
    ⟨body₃.subst 0 v₃,
      substitution_equivRed hbody₁ hv₁,
      substitution_equivRed hbody₂ hv₂⟩

  /-=== Case ME-FUN + ME-FUN: t₀ = lam dom body, s₀ = [] ===-/
  | .me_fun h₁_dom h₁_body, .me_fun h₂_dom h₂_body => by
    -- s₀ = nil, so s₁ = nil and s₂ = nil
    have hs₁ : s₁ = [] := ctxRed_nil_stack hc₁
    have hs₂ : s₂ = [] := ctxRed_nil_stack hc₂
    subst hs₁; subst hs₂
    -- IH on dom
    obtain ⟨dom₃, hdom₁, hdom₂⟩ := diamond h₁_dom h₂_dom hc₁ hc₂
    -- Build context reduction for body context: (Ann.sub dom :: Γ₀);nil ↦ ...
    have hc₁_body := CtxRed.ct_ann_sub hc₁ h₁_dom
    have hc₂_body := CtxRed.ct_ann_sub hc₂ h₂_dom
    -- IH on body
    obtain ⟨body₃, hbody₁, hbody₂⟩ := diamond h₁_body h₂_body hc₁_body hc₂_body
    exact ⟨.lam dom₃ body₃, .me_fun hdom₁ hbody₁, .me_fun hdom₂ hbody₂⟩

  /-=== Case ME-FOP + ME-FOP: t₀ = lam dom body, s₀ = α :: s₀' ===-/
  | .me_fop h₁_dom h₁_body, .me_fop h₂_dom h₂_body => by
    -- Decompose the context reduction: Γ₀;(α :: s₀') ↦ Γ₁;s₁
    obtain ⟨α₁', s₁', Γ₁', ⟨hs₁_eq⟩, hc₁_body_raw, ⟨hΓ₁_eq⟩⟩ := ctxRed_unstk hc₁
    obtain ⟨α₂', s₂', Γ₂', ⟨hs₂_eq⟩, hc₂_body_raw, ⟨hΓ₂_eq⟩⟩ := ctxRed_unstk hc₂
    subst hs₁_eq; subst hΓ₁_eq; subst hs₂_eq; subst hΓ₂_eq
    -- IH on dom: need CtxRed Γ₀ [] Γ₁' [] and CtxRed Γ₀ [] Γ₂' []
    -- ctxRed_nil_of_ctxRed hc₁ : CtxRed Γ₀ [] Γ₁' [] (after subst)
    obtain ⟨dom₃, hdom₁, hdom₂⟩ := diamond h₁_dom h₂_dom
      (ctxRed_nil_of_ctxRed hc₁) (ctxRed_nil_of_ctxRed hc₂)
    -- IH on body
    obtain ⟨body₃, hbody₁, hbody₂⟩ := diamond h₁_body h₂_body hc₁_body_raw hc₂_body_raw
    exact ⟨.lam dom₃ body₃, .me_fop hdom₁ hbody₁, .me_fop hdom₂ hbody₂⟩

/-- Helper: CtxRed preserves annotation structure — if Γ has Ann.sub t
    at position k, then Γ' has Ann.sub t' for some t'. -/
def ctxRed_lookup_sub
    {Γ : MCtx} {s : Stack} {Γ' : MCtx} {s' : Stack}
    (h_ctx : CtxRed Γ s Γ' s')
    {k : Nat} {t : Expr}
    (h_lookup : Γ.get? k = some (Ann.sub t))
    : Σ' t' : Expr, PLift (Γ'.get? k = some (Ann.sub t')) :=
  match h_ctx, k, h_lookup with
  | .ct_ann_sub _ _, 0, _ => ⟨_, ⟨rfl⟩⟩
  | .ct_ann_sub h_inner _, k + 1, h => ctxRed_lookup_sub h_inner h
  | .ct_ann_equiv _ _, 0, h => absurd h (by simp [List.get?])
  | .ct_ann_equiv h_inner _, k + 1, h => ctxRed_lookup_sub h_inner h
  | .ct_stk h_inner _, _, h => ctxRed_lookup_sub h_inner h
  | .ct_nil, _, h => absurd h (by simp [List.get?])

/-- Context reduction preserves MS-PRO lookups (Lemma 19 / weakening in paper).
    If x ≤ t ∈ Γ and Γ;s ↦ Γ';s', then there exists t' such that:
    - Γ';s' ⊢ x ≤→ t'↑  (MS-PRO with the REDUCED annotation)
    - Γ;s ⊢ t↑ ≡→ t'↑  (the shifted annotation reduces, for the top edge)

    The old statement was FALSE because it claimed MS-PRO gives t↑ (the
    ORIGINAL annotation), but CtxRed reduces annotations pointwise: if Γ
    has Ann.sub t at position k, then Γ' has Ann.sub t' where t ≡→ t'.
    So MS-PRO in Γ' gives t'↑, not t↑. -/
def weakening_equivRed
    {Γ : MCtx} {s : Stack} {Γ' : MCtx} {s' : Stack} {k : Nat} {t : Expr}
    (h_lookup : Γ.get? k = some (Ann.sub t))
    (h_ctx : CtxRed Γ s Γ' s')
    : Σ' t' : Expr,
        MSubRed Γ' s' (.bvar k) (t'.shift (k + 1) 0) ×
        MEquivRed Γ s (t.shift (k + 1) 0) (t'.shift (k + 1) 0) := by
  -- Extract the reduced annotation from CtxRed
  obtain ⟨t', ⟨h_lookup'⟩⟩ := ctxRed_lookup_sub h_ctx h_lookup
  -- MS-PRO gives us the right edge using the reduced annotation
  -- The top edge (equiv reduction of the shifted annotation) requires
  -- a weakening/shift lemma for MEquivRed which is non-trivial in de Bruijn.
  exact ⟨t', .ms_pro h_lookup', sorry⟩

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
      -- After CtxRed, the annotation may have reduced from t to t'.
      -- weakening_equivRed gives us t' and proofs for both edges.
      let ⟨t', h_sub_pro, h_equiv_shift⟩ := weakening_equivRed h_lookup h_ctx
      exact ⟨t'.shift (_ + 1) 0, h_equiv_shift, h_sub_pro⟩
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
          commutativity h_eq_body_equiv h_sub_body₂ (CtxRed.ct_ann_equiv h_ctx h_eq_v)
        -- h_eq_body₂ : MEquivRed (Ann.equiv v_op :: Γ) s body₂ body₃
        -- h_sub_body₁ : MSubRed (Ann.equiv v' :: Γ') s' body' body₃
        -- t₃ = body₃.subst 0 v' where v' is the reduced v (from h_eq_v).
        -- Top edge: ME-BET needs body₂ ≡→ body₃ under Ann.sub dom.
        -- Right edge: substitution_subRed on h_sub_body₁.
        -- Use _ for the witness since me_bet determines the form of t₃.
        let h_eq_body₂_np : h_eq_body₂.noPromoAt 0 := sorry
        exact ⟨_, .me_bet (equivRed_no_promo_change_ann_at_zero h_eq_body₂ h_eq_body₂_np) h_eq_v,
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
        commutativity h_eq_body h_sub_body (CtxRed.ct_ann_sub h_ctx h_eq_dom)
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
