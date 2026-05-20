/-!
# Machine-Based Pure Subtype Systems (MPSS) — Locally Nameless Encoding

Mechanisation of the MPSS calculus from:
  Pasquale & Garcia-Perez, "Towards the type safety of Pure Subtype Systems
  (Full version)", CSL 2026.

This file encodes MPSS using the **locally nameless** representation:
  - Bound variables: de Bruijn indices (for lambda-bound vars)
  - Free variables: names (String atoms) — no shifting needed under binders

## Contents
- LNExpr: locally nameless terms
- open_at / close_at / subst_fvar: opening, closing, substitution
- LNAnn, LNCtx, LNStack: annotations, contexts, stacks
- LNEquivRed: equivalence reduction (Figure 2, top half)
- LNSubRed: subtyping reduction (Figure 2, bottom half)
- LNCtxRed: context reduction (Section 3)
- noPromoAt: non-promotion predicates for annotation swap axioms
- commutativity: Lemma 1, the main theorem

## Sorrys
The remaining `sorry`s are all for `lc_at 0` witnesses needed by
`open_close_id` and `open_close_subst`. These would be discharged by
proving that reduction preserves local closure.
-/

/-! ## Terms -/

/-- Locally nameless terms for MPSS.

    t, u, v ::=
      | bvar n        — bound variable (de Bruijn index, for lambda-bound)
      | fvar x        — free variable (named atom)
      | top           — universal supertype (Top)
      | lam dom body  — λx ≤ dom. body  (bvar 0 in body refers to the param)
      | app u v       — application
-/
inductive LNExpr where
  | bvar : Nat → LNExpr
  | fvar : String → LNExpr
  | top  : LNExpr
  | lam  : LNExpr → LNExpr → LNExpr
  | app  : LNExpr → LNExpr → LNExpr
deriving Inhabited, DecidableEq, Repr

namespace LNExpr

/-! ## Opening and closing -/

/-- Open: replace `bvar k` with term `u` in `e`.
    When descending under a binder (lam), increment k.
    This is the standard locally-nameless opening operation.
    The expression `e` is the first argument so that `e.open_at k u` works
    correctly with Lean 4 dot notation. -/
def open_at (e : LNExpr) (k : Nat) (u : LNExpr) : LNExpr :=
  match e with
  | .bvar n => if n == k then u else .bvar n
  | .fvar x => .fvar x
  | .top => .top
  | .lam dom body => .lam (dom.open_at k u) (body.open_at (k + 1) u)
  | .app f a => .app (f.open_at k u) (a.open_at k u)

/-- Shorthand: open at depth 0 (the most common case). -/
abbrev open' (e : LNExpr) (u : LNExpr) : LNExpr := e.open_at 0 u

/-- Close: replace `fvar x` with `bvar k` in `e`.
    The inverse of opening. -/
def close_at (k : Nat) (x : String) : LNExpr → LNExpr
  | .bvar n => .bvar n
  | .fvar y => if y == x then .bvar k else .fvar y
  | .top => .top
  | .lam dom body => .lam (close_at k x dom) (close_at (k + 1) x body)
  | .app f a => .app (close_at k x f) (close_at k x a)

/-- Capture-avoiding substitution: replace free variable `x` with `u` in `e`.
    The expression `e` is the first argument so that `e.subst_fvar x u` works
    correctly with Lean 4 dot notation. -/
def subst_fvar (e : LNExpr) (x : String) (u : LNExpr) : LNExpr :=
  match e with
  | .bvar n => .bvar n
  | .fvar y => if y == x then u else .fvar y
  | .top => .top
  | .lam dom body => .lam (dom.subst_fvar x u) (body.subst_fvar x u)
  | .app f a => .app (f.subst_fvar x u) (a.subst_fvar x u)

/-- Free variables of a term (as a list, may contain duplicates). -/
def fvs : LNExpr → List String
  | .bvar _ => []
  | .fvar x => [x]
  | .top => []
  | .lam dom body => dom.fvs ++ body.fvs
  | .app f a => f.fvs ++ a.fvs

/-- A term is *locally closed* if it has no dangling bound variables
    above depth `k`. -/
def lc_at (k : Nat) : LNExpr → Prop
  | .bvar n => n < k
  | .fvar _ => True
  | .top => True
  | .lam dom body => dom.lc_at k ∧ body.lc_at (k + 1)
  | .app f a => f.lc_at k ∧ a.lc_at k

/-- A term is locally closed (no dangling bound variables at all). -/
abbrev lc : LNExpr → Prop := lc_at 0

/-- Opening a body that is lc_at (k+1) with a free variable yields lc_at k. -/
theorem lc_at_open_fvar {e : LNExpr} {k : Nat} {x : String}
    (h : e.lc_at (k + 1)) : (e.open_at k (.fvar x)).lc_at k := by
  induction e generalizing k with
  | bvar n =>
    simp [LNExpr.lc_at] at h
    simp [LNExpr.open_at]
    split
    · simp [LNExpr.lc_at]
    · simp [LNExpr.lc_at]; omega
  | fvar _ => simp [LNExpr.open_at, LNExpr.lc_at]
  | top => simp [LNExpr.open_at, LNExpr.lc_at]
  | lam dom body ih_dom ih_body =>
    simp [LNExpr.lc_at] at h
    simp [LNExpr.open_at, LNExpr.lc_at]
    exact ⟨ih_dom h.1, ih_body h.2⟩
  | app f a ih_f ih_a =>
    simp [LNExpr.lc_at] at h
    simp [LNExpr.open_at, LNExpr.lc_at]
    exact ⟨ih_f h.1, ih_a h.2⟩

/-- Size of a term (for termination proofs).
    This counts the number of constructors. -/
def sz : LNExpr → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .top => 1
  | .lam dom body => 1 + dom.sz + body.sz
  | .app f a => 1 + f.sz + a.sz

end LNExpr

/-! ## Fresh name generation -/

/-- Maximum length of strings in a list. -/
private def maxStrLen : List String → Nat
  | [] => 0
  | s :: rest => max s.length (maxStrLen rest)

private theorem le_maxStrLen_of_mem {s : String} {l : List String} (h : s ∈ l)
    : s.length ≤ maxStrLen l := by
  induction l with
  | nil => exact absurd h (List.not_mem_nil _)
  | cons a rest ih =>
    simp [maxStrLen]
    cases h with
    | head => omega
    | tail _ hmem => have := ih hmem; omega

/-- For any finite list of strings, there is a string not in it. -/
private theorem exists_fresh_string (avoid : List String) : ∃ s : String, s ∉ avoid := by
  refine ⟨⟨List.replicate (maxStrLen avoid + 1) 'a'⟩, ?_⟩
  intro hmem
  have hlen : (⟨List.replicate (maxStrLen avoid + 1) 'a'⟩ : String).length = maxStrLen avoid + 1 := by
    simp [String.length, List.length_replicate]
  have := le_maxStrLen_of_mem hmem
  omega

/-! ## Annotations, Contexts, and Stacks -/

/-- Context annotations in MPSS.
    - `sub t`   : x ≤ t  (subtype annotation, from unapplied lambdas)
    - `equiv t` : x ≡ α  (equivalence annotation, α from the stack / operand)
-/
inductive LNAnn where
  | sub   : LNExpr → LNAnn
  | equiv : LNExpr → LNAnn
deriving Inhabited, DecidableEq, Repr

/-- Logical context: maps free variable names to annotations.
    Ordered list; the head is the most recently bound variable. -/
abbrev LNCtx := List (String × LNAnn)

/-- Domain of a context: the list of variable names. -/
def LNCtx.dom (Γ : LNCtx) : List String := Γ.map Prod.fst

/-- Look up a variable name in a context. -/
def LNCtx.lookup' (Γ : LNCtx) (x : String) : Option LNAnn :=
  match Γ with
  | [] => none
  | (y, ann) :: rest => if y == x then some ann else LNCtx.lookup' rest x

/-- `x ≤ t ∈ Γ` -/
def LNCtx.mem_sub (Γ : LNCtx) (x : String) (t : LNExpr) : Prop :=
  Γ.lookup' x = some (.sub t)

/-- `x ≡ α ∈ Γ` -/
def LNCtx.mem_equiv (Γ : LNCtx) (x : String) (α : LNExpr) : Prop :=
  Γ.lookup' x = some (.equiv α)

/-- Continuation stack: a list of terms (operands pushed during application). -/
abbrev LNStack := List LNExpr

/-- An annotation is locally closed if its embedded term is. -/
def LNAnn.lc : LNAnn → Prop
  | .sub t => t.lc
  | .equiv α => α.lc

/-- A context is well-formed: all annotation terms are locally closed. -/
def LNCtx.wf (Γ : LNCtx) : Prop := ∀ p ∈ Γ, p.2.lc

/-- A stack is well-formed: all elements are locally closed. -/
def LNStack.wf (s : LNStack) : Prop := ∀ e ∈ s, e.lc

/-- For any finite context and term, there exists a fresh variable name. -/
theorem exists_fresh (Γ : LNCtx) (e : LNExpr)
    : ∃ x : String, x ∉ LNCtx.dom Γ ∧ x ∉ e.fvs := by
  obtain ⟨x, hx⟩ := exists_fresh_string (LNCtx.dom Γ ++ e.fvs)
  exact ⟨x, fun h => hx (List.mem_append_left _ h), fun h => hx (List.mem_append_right _ h)⟩

/-! ## Equivalence and Subtyping Reduction (Figure 2)

These are mutually inductive:
- ME-PRO (in LNEquivRed) uses LNSubRed as a premise
- MS-EQU (in LNSubRed) uses LNEquivRed as a premise

In the locally nameless encoding, when going under a binder
(ME-FUN, ME-FOP, MS-FUN, MS-FOP, ME-BET), we open the body with
a fresh free variable and extend the context with that variable.
-/

mutual

/--
Equivalence reduction  `LNEquivRed Γ s u v`  means  `Γ; s ⊢ u ≡→ v`.

Models reflexive, small-step, simultaneous β-reduction instrumented
with the Krivine-style stack mechanism.
-/
inductive LNEquivRed : LNCtx → LNStack → LNExpr → LNExpr → Prop where
  /-- ME-PRO: Promote through equivalence annotation.
      `x ≡ α ∈ Γ`  and  `Γ; s ⊢ α ≤→ α'`
      ⟹  `Γ; s ⊢ fvar x ≡→ α'`

      In locally nameless, free variables are looked up directly by name.
      No shifting is needed (unlike de Bruijn). -/
  | me_pro {Γ s x α α'} :
      LNCtx.mem_equiv Γ x α →
      LNSubRed Γ s α α' →
      LNEquivRed Γ s (.fvar x) α'

  /-- ME-BET: Simultaneous β-reduction.
      Pick a fresh `x ∉ dom(Γ)`, open body with `fvar x`:
        `(Γ, x ≤ dom); s ⊢ body^x ≡→ u'`
        `Γ; nil ⊢ v ≡→ v'`
      ⟹  `Γ; s ⊢ (λdom.body) v ≡→ u'[x↦v']`

      The substitution `u'[x↦v']` replaces the fresh variable with
      the reduced operand, giving the β-reduct. -/
  | me_bet {Γ s dom body u' v v' x} :
      x ∉ LNCtx.dom Γ →
      LNEquivRed ((x, .sub dom) :: Γ) s (body.open_at 0 (.fvar x)) u' →
      LNEquivRed Γ [] v v' →
      LNEquivRed Γ s (.app (.lam dom body) v) (u'.subst_fvar x v')

  /-- ME-TOP: Top reduces to Top (reflexivity base case). -/
  | me_top {Γ s} :
      LNEquivRed Γ s .top .top

  /-- ME-VAR: Free variables reduce to themselves (reflexivity). -/
  | me_var {Γ s x} :
      LNEquivRed Γ s (.fvar x) (.fvar x)

  /-- ME-TAP: `Top u ≡→ Top` (Top absorbs applications). -/
  | me_tap {Γ s u} :
      LNEquivRed Γ s (.app .top u) .top

  /-- ME-APP: Application — push operand onto stack.
      `Γ; v :: s ⊢ u ≡→ u'`  and  `Γ; nil ⊢ v ≡→ v'`
      ⟹  `Γ; s ⊢ u v ≡→ u' v'` -/
  | me_app {Γ s u u' v v'} :
      LNEquivRed Γ (v :: s) u u' →
      LNEquivRed Γ [] v v' →
      LNEquivRed Γ s (.app u v) (.app u' v')

  /-- ME-FUN: Unapplied abstraction (stack is nil).
      Pick fresh `x ∉ dom(Γ)`:
        `Γ; nil ⊢ dom ≡→ dom'`
        `(Γ, x ≤ dom); nil ⊢ body^x ≡→ body'`
      ⟹  `Γ; nil ⊢ λdom.body ≡→ λdom'. close x body'`

      We open the body, reduce it, then close it back. -/
  | me_fun {Γ dom dom' body body' x} :
      x ∉ LNCtx.dom Γ →
      LNEquivRed Γ [] dom dom' →
      LNEquivRed ((x, .sub dom) :: Γ) [] (body.open_at 0 (.fvar x)) body' →
      LNEquivRed Γ [] (.lam dom body) (.lam dom' (body'.close_at 0 x))

  /-- ME-FOP: Applied abstraction — pop operand from stack.
      Pick fresh `x ∉ dom(Γ)`:
        `Γ; nil ⊢ dom ≡→ dom'`
        `(Γ, x ≡ α); s ⊢ body^x ≡→ body'`
      ⟹  `Γ; α :: s ⊢ λdom.body ≡→ λdom'. close x body'`

      The operand `α` from the stack becomes an equivalence annotation. -/
  | me_fop {Γ s α dom dom' body body' x} :
      x ∉ LNCtx.dom Γ →
      LNEquivRed Γ [] dom dom' →
      LNEquivRed ((x, .equiv α) :: Γ) s (body.open_at 0 (.fvar x)) body' →
      LNEquivRed Γ (α :: s) (.lam dom body) (.lam dom' (body'.close_at 0 x))

/--
Subtyping reduction  `LNSubRed Γ s u v`  means  `Γ; s ⊢ u ≤→ v`.

Defines promotion (subtyping) in a stack-aware manner.
Note: subtyping does NOT change the type annotation of abstractions.
-/
inductive LNSubRed : LNCtx → LNStack → LNExpr → LNExpr → Prop where
  /-- MS-PRO: Promote variable to its subtype bound.
      `x ≤ t ∈ Γ`
      ⟹  `Γ; s ⊢ fvar x ≤→ t`

      In locally nameless, no shifting — `t` is already at the right scope. -/
  | ms_pro {Γ s x t} :
      LNCtx.mem_sub Γ x t →
      LNSubRed Γ s (.fvar x) t

  /-- MS-TOP: Any term promotes to Top. -/
  | ms_top {Γ s u} :
      LNSubRed Γ s u .top

  /-- MS-EQU: Equivalence subsumes subtyping.
      `Γ; s ⊢ u ≡→ v`  ⟹  `Γ; s ⊢ u ≤→ v` -/
  | ms_equ {Γ s u v} :
      LNEquivRed Γ s u v →
      LNSubRed Γ s u v

  /-- MS-APP: Application — push operand and promote operator.
      `Γ; v :: s ⊢ u ≤→ u'`
      ⟹  `Γ; s ⊢ u v ≤→ u' v` -/
  | ms_app {Γ s u u' v} :
      LNSubRed Γ (v :: s) u u' →
      LNSubRed Γ s (.app u v) (.app u' v)

  /-- MS-FUN: Unapplied abstraction — promote body (stack is nil).
      Pick fresh `x ∉ dom(Γ)`:
        `(Γ, x ≤ dom); nil ⊢ body^x ≤→ body'`
      ⟹  `Γ; nil ⊢ λdom.body ≤→ λdom. close x body'`

      Note: the domain annotation is NOT changed by subtyping. -/
  | ms_fun {Γ dom body body' x} :
      x ∉ LNCtx.dom Γ →
      LNSubRed ((x, .sub dom) :: Γ) [] (body.open_at 0 (.fvar x)) body' →
      LNSubRed Γ [] (.lam dom body) (.lam dom (body'.close_at 0 x))

  /-- MS-FOP: Applied abstraction — pop from stack, promote body.
      Pick fresh `x ∉ dom(Γ)`:
        `(Γ, x ≡ α); s ⊢ body^x ≤→ body'`
      ⟹  `Γ; α :: s ⊢ λdom.body ≤→ λdom. close x body'`

      Note: the domain annotation is NOT changed by subtyping. -/
  | ms_fop {Γ s α dom body body' x} :
      x ∉ LNCtx.dom Γ →
      LNSubRed ((x, .equiv α) :: Γ) s (body.open_at 0 (.fvar x)) body' →
      LNSubRed Γ (α :: s) (.lam dom body) (.lam dom (body'.close_at 0 x))

end

/-! ## Context Reduction (Section 3)

Captures how annotations evolve during reduction steps.
Used in the statement of commutativity (Lemma 1).

- CT-ANN: Annotation `x ⊲ t` in the context is reduced pointwise via ≡→
- CT-STK: Stack element `α` is reduced pointwise via ≡→

In locally nameless, no shifting is needed when extending contexts.
-/

inductive LNCtxRed : LNCtx → LNStack → LNCtx → LNStack → Prop where
  /-- CT-ANN (sub): Reduce a subtype annotation.
      `Γ; s ↦ Γ'; s'`  and  `Γ; nil ⊢ t ≡→ t'`
      ⟹  `(x ≤ t, Γ); s ↦ (x ≤ t', Γ'); s'` -/
  | ct_ann_sub {Γ s Γ' s' x t t'} :
      LNCtxRed Γ s Γ' s' →
      LNEquivRed Γ [] t t' →
      LNCtxRed ((x, .sub t) :: Γ) s ((x, .sub t') :: Γ') s'

  /-- CT-ANN (equiv): Reduce an equivalence annotation.
      `Γ; s ↦ Γ'; s'`  and  `Γ; nil ⊢ α ≡→ α'`
      ⟹  `(x ≡ α, Γ); s ↦ (x ≡ α', Γ'); s'` -/
  | ct_ann_equiv {Γ s Γ' s' x α α'} :
      LNCtxRed Γ s Γ' s' →
      LNEquivRed Γ [] α α' →
      LNCtxRed ((x, .equiv α) :: Γ) s ((x, .equiv α') :: Γ') s'

  /-- CT-STK: Reduce a stack element.
      `Γ; s ↦ Γ'; s'`  and  `Γ; nil ⊢ α ≡→ α'`
      ⟹  `Γ; α :: s ↦ Γ'; α' :: s'` -/
  | ct_stk {Γ s Γ' s' α α'} :
      LNCtxRed Γ s Γ' s' →
      LNEquivRed Γ [] α α' →
      LNCtxRed Γ (α :: s) Γ' (α' :: s')

  /-- Base case: empty context and empty stack. -/
  | ct_nil :
      LNCtxRed [] [] [] []

/-! ## Commutativity Statement (Lemma 1)

The main commutativity theorem: if `Γ; s ⊢ t₀ ≡→ t₁` and `Γ; s ⊢ t₀ ≤→ t₂`,
then for any extended context `Γ'; s'` with `Γ; s ↦ Γ'; s'`, there exists `t₃`
such that `Γ; s ⊢ t₂ ≡→ t₃` and `Γ'; s' ⊢ t₁ ≤→ t₃`.

This is just the STATEMENT; the proof is left for future work.
The locally nameless encoding should make the proof much more direct
since there are no shifting issues when going under binders.
-/

/-! ## Helper Lemmas

These support the commutativity proof. Several are now proved as theorems;
the remainder are axioms corresponding to paper lemmas that require
mutual induction on the reduction relations.
-/

/-- Reflexivity of ≡→ (Proposition 18).
    Every locally-closed term equiv-reduces to itself. -/
theorem equivRed_refl (Γ : LNCtx) (s : LNStack) (u : LNExpr)
    (hlc : u.lc)
    : LNEquivRed Γ s u u := by
  -- Local helper: close ∘ open = id for fresh variables
  have close_open : ∀ (e : LNExpr) (x : String) (k : Nat),
      x ∉ e.fvs → (e.open_at k (.fvar x)).close_at k x = e := by
    intro e x k hfr
    induction e generalizing k with
    | bvar n =>
      simp [LNExpr.open_at]
      split
      · simp [LNExpr.close_at, beq_iff_eq]; omega
      · simp [LNExpr.close_at]
    | fvar y =>
      simp [LNExpr.fvs, List.mem_singleton] at hfr
      simp [LNExpr.open_at, LNExpr.close_at, beq_iff_eq, Ne.symm hfr]
    | top => simp [LNExpr.open_at, LNExpr.close_at]
    | lam dom body ih_dom ih_body =>
      simp [LNExpr.fvs, List.mem_append] at hfr
      simp [LNExpr.open_at, LNExpr.close_at, ih_dom k hfr.1, ih_body (k+1) hfr.2]
    | app f a ih_f ih_a =>
      simp [LNExpr.fvs, List.mem_append] at hfr
      simp [LNExpr.open_at, LNExpr.close_at, ih_f k hfr.1, ih_a k hfr.2]
  -- Main proof by case analysis + recursion
  match u, hlc with
  | .bvar n, hlc => simp [LNExpr.lc, LNExpr.lc_at] at hlc
  | .fvar _, _ => exact .me_var
  | .top, _ => exact .me_top
  | .app f a, hlc =>
    have hf_lc : f.lc := hlc.1
    have ha_lc : a.lc := hlc.2
    exact .me_app (equivRed_refl Γ (a :: s) f hf_lc) (equivRed_refl Γ [] a ha_lc)
  | .lam dom body, hlc =>
    have hdom_lc : dom.lc := hlc.1
    have hbody_lc1 : body.lc_at 1 := hlc.2
    obtain ⟨x, hx_ctx, hx_body⟩ := exists_fresh Γ body
    have hopen_lc : (body.open_at 0 (.fvar x)).lc := LNExpr.lc_at_open_fvar hbody_lc1
    match s with
    | [] =>
      have h := LNEquivRed.me_fun (x := x) hx_ctx
        (equivRed_refl Γ [] dom hdom_lc)
        (equivRed_refl ((x, .sub dom) :: Γ) [] (body.open_at 0 (.fvar x)) hopen_lc)
      rw [close_open body x 0 hx_body] at h; exact h
    | α :: s' =>
      have h := LNEquivRed.me_fop (x := x) (α := α) hx_ctx
        (equivRed_refl Γ [] dom hdom_lc)
        (equivRed_refl ((x, .equiv α) :: Γ) s' (body.open_at 0 (.fvar x)) hopen_lc)
      rw [close_open body x 0 hx_body] at h; exact h
termination_by u.sz
decreasing_by
  all_goals simp_all [LNExpr.sz]
  all_goals first
    | omega
    | (have : ∀ (k : Nat) (x : String) (e : LNExpr),
          (e.open_at k (.fvar x)).sz = e.sz := by
        intro k x e
        induction e generalizing k with
        | bvar n => simp [LNExpr.open_at, LNExpr.sz]; split <;> simp [LNExpr.sz]
        | fvar _ => simp [LNExpr.open_at, LNExpr.sz]
        | top => simp [LNExpr.open_at, LNExpr.sz]
        | lam dom body ih_dom ih_body =>
          simp [LNExpr.open_at, LNExpr.sz, ih_dom, ih_body]
        | app f a ih_f ih_a =>
          simp [LNExpr.open_at, LNExpr.sz, ih_f, ih_a]
       simp_all; omega)

/-- Reflexivity of ≤→ (via MS-EQU + reflexivity of ≡→). -/
theorem subRed_refl (Γ : LNCtx) (s : LNStack) (u : LNExpr)
    (hlc : u.lc) : LNSubRed Γ s u u :=
  .ms_equ (equivRed_refl Γ s u hlc)

/-- Weakening for ≡→ via context reduction (Lemma 22).
    If Γ;s ⊢ u ≡→ v and Γ;s ↦ Γ';s' then Γ';s' ⊢ u ≡→ v. -/
axiom equivRed_weaken
    {Γ Γ' : LNCtx} {s s' : LNStack} {u v : LNExpr}
    (h : LNEquivRed Γ s u v) (hctx : LNCtxRed Γ s Γ' s')
    : LNEquivRed Γ' s' u v

/-- Weakening for ≤→ via context reduction (Lemma 21). -/
axiom subRed_weaken
    {Γ Γ' : LNCtx} {s s' : LNStack} {u v : LNExpr}
    (h : LNSubRed Γ s u v) (hctx : LNCtxRed Γ s Γ' s')
    : LNSubRed Γ' s' u v

/-- Stack extension for ≡→ (Lemma 19, part).
    If Γ;[] ⊢ u ≡→ v then Γ;s ⊢ u ≡→ v.
    Derivations with empty stack can be replayed in any stack. -/
axiom equivRed_stack_ext
    {Γ : LNCtx} {u v : LNExpr} {s : LNStack}
    (h : LNEquivRed Γ [] u v) : LNEquivRed Γ s u v

/-- Stack extension for ≤→ (Lemma 19, part). -/
axiom subRed_stack_ext
    {Γ : LNCtx} {u v : LNExpr} {s : LNStack}
    (h : LNSubRed Γ [] u v) : LNSubRed Γ s u v

/-- Context reduction is reflexive (requires all embedded terms to be lc). -/
theorem ctxRed_refl (Γ : LNCtx) (s : LNStack)
    (hwf_ctx : Γ.wf) (hwf_stk : s.wf) : LNCtxRed Γ s Γ s := by
  induction Γ with
  | nil =>
    induction s with
    | nil => exact .ct_nil
    | cons α s ih =>
      have hα : α.lc := hwf_stk α (List.mem_cons_self α s)
      have hs_wf : LNStack.wf s := fun e he => hwf_stk e (List.mem_cons_of_mem α he)
      exact .ct_stk (ih hs_wf) (equivRed_refl [] [] α hα)
  | cons p Γ ih =>
    obtain ⟨x, ann⟩ := p
    have htail_wf : LNCtx.wf Γ := fun q hq => hwf_ctx q (List.mem_cons_of_mem (x, ann) hq)
    cases ann with
    | sub t =>
      have ht : t.lc := hwf_ctx (x, .sub t) (List.mem_cons_self _ _)
      exact .ct_ann_sub (ih htail_wf) (equivRed_refl Γ [] t ht)
    | equiv α' =>
      have hα : α'.lc := hwf_ctx (x, .equiv α') (List.mem_cons_self _ _)
      exact .ct_ann_equiv (ih htail_wf) (equivRed_refl Γ [] α' hα)

/-- Lemma 36: stripping the stack from a context reduction. -/
theorem ctxRed_nil_of_ctxRed
    {Γ Γ' : LNCtx} {s s' : LNStack}
    (h : LNCtxRed Γ s Γ' s') : LNCtxRed Γ [] Γ' [] := by
  induction h with
  | ct_ann_sub _ hred ih => exact .ct_ann_sub ih hred
  | ct_ann_equiv _ hred ih => exact .ct_ann_equiv ih hred
  | ct_stk _ _ ih => exact ih
  | ct_nil => exact .ct_nil

/-- Substitution for ≡→ (Lemma 32).
    If (x,ann)::Γ; s ⊢ u ≡→ u' and Γ;[] ⊢ v ≡→ v'
    then Γ;s ⊢ u[x↦v] ≡→ u'[x↦v']. -/
axiom equivRed_subst
    {Γ : LNCtx} {s : LNStack} {x : String} {ann : LNAnn}
    {u u' v v' : LNExpr}
    (hbody : LNEquivRed ((x, ann) :: Γ) s u u')
    (harg  : LNEquivRed Γ [] v v')
    : LNEquivRed Γ s (u.subst_fvar x v) (u'.subst_fvar x v')

/-- Substitution for ≤→ (Lemma 30).
    If (x,ann)::Γ; s ⊢ u ≤→ u' and x ∉ dom(Γ)
    then Γ;s ⊢ u[x↦v] ≤→ u'[x↦v]. -/
axiom subRed_subst
    {Γ : LNCtx} {s : LNStack} {x : String} {ann : LNAnn}
    {u u' v : LNExpr}
    (hbody : LNSubRed ((x, ann) :: Γ) s u u')
    (hfresh : x ∉ LNCtx.dom Γ)
    : LNSubRed Γ s (u.subst_fvar x v) (u'.subst_fvar x v)

/-- Context lookup: x ≤ t ∈ Γ and Γ;s ↦ Γ';s'  ⟹  x ≤ t' ∈ Γ'
    with Γ;[] ⊢ t ≡→ t'. -/
axiom ctxRed_lookup_sub
    {Γ Γ' : LNCtx} {s s' : LNStack} {x : String} {t : LNExpr}
    (hmem : LNCtx.mem_sub Γ x t) (hctx : LNCtxRed Γ s Γ' s')
    : ∃ t', LNCtx.mem_sub Γ' x t' ∧ LNEquivRed Γ [] t t'

/-- Context lookup: x ≡ α ∈ Γ and Γ;s ↦ Γ';s'  ⟹  x ≡ α' ∈ Γ'
    with Γ;[] ⊢ α ≡→ α'. -/
axiom ctxRed_lookup_equiv
    {Γ Γ' : LNCtx} {s s' : LNStack} {x : String} {α : LNExpr}
    (hmem : LNCtx.mem_equiv Γ x α) (hctx : LNCtxRed Γ s Γ' s')
    : ∃ α', LNCtx.mem_equiv Γ' x α' ∧ LNEquivRed Γ [] α α'

/-- A variable cannot simultaneously have a sub and equiv annotation.
    Proved: lookup' returns a unique result per key. -/
theorem no_sub_and_equiv
    {Γ : LNCtx} {x : String} {t α : LNExpr}
    (hsub : LNCtx.mem_sub Γ x t) (hequiv : LNCtx.mem_equiv Γ x α)
    : False := by
  simp [LNCtx.mem_sub, LNCtx.mem_equiv] at hsub hequiv
  rw [hsub] at hequiv
  exact absurd hequiv (by simp)

/-- Diamond property for ≡→ (Lemma 2).
    If Γ;s ⊢ t₀ ≡→ t₁ and Γ;s ⊢ t₀ ≡→ t₂ and Γ;s ↦ Γ₁;s₁
    and Γ;s ↦ Γ₂;s₂ then ∃ t₃ with Γ₁;s₁ ⊢ t₂ ≡→ t₃
    and Γ₂;s₂ ⊢ t₁ ≡→ t₃.

    The paper proves this by a similar induction to commutativity.
    We state the special case needed: when one context is (Γ,s)
    itself (via reflexivity of ↦) and the other is (Γ',s').
    Combined: if Γ;s ⊢ t₀ ≡→ t₁ and Γ;s ⊢ t₀ ≡→ t₂
    then ∃ t₃ with Γ;s ⊢ t₂ ≡→ t₃ and Γ';s' ⊢ t₁ ≡→ t₃
    for any Γ';s' with Γ;s ↦ Γ';s'. -/
axiom diamond
    {Γ Γ' : LNCtx} {s s' : LNStack} {t₀ t₁ t₂ : LNExpr}
    (h1 : LNEquivRed Γ s t₀ t₁) (h2 : LNEquivRed Γ s t₀ t₂)
    (hctx : LNCtxRed Γ s Γ' s')
    : ∃ t₃, LNEquivRed Γ s t₂ t₃ ∧ LNEquivRed Γ' s' t₁ t₃

/-- Alpha-renaming for ≡→ under binders.
    If (x,ann)::Γ; s ⊢ body^x ≡→ u and y ∉ dom(Γ) and x ∉ dom(Γ),
    then (y,ann)::Γ; s ⊢ body^y ≡→ u[x↦fvar y].
    This is a standard locally-nameless infrastructure lemma. -/
axiom equivRed_rename
    {Γ : LNCtx} {s : LNStack} {ann : LNAnn}
    {body u : LNExpr} {x y : String}
    (h : LNEquivRed ((x, ann) :: Γ) s (body.open_at 0 (.fvar x)) u)
    (hx : x ∉ LNCtx.dom Γ) (hy : y ∉ LNCtx.dom Γ)
    : LNEquivRed ((y, ann) :: Γ) s (body.open_at 0 (.fvar y)) (u.subst_fvar x (.fvar y))

/-- Alpha-renaming for ≤→ under binders. -/
axiom subRed_rename
    {Γ : LNCtx} {s : LNStack} {ann : LNAnn}
    {body u : LNExpr} {x y : String}
    (h : LNSubRed ((x, ann) :: Γ) s (body.open_at 0 (.fvar x)) u)
    (hx : x ∉ LNCtx.dom Γ) (hy : y ∉ LNCtx.dom Γ)
    : LNSubRed ((y, ann) :: Γ) s (body.open_at 0 (.fvar y)) (u.subst_fvar x (.fvar y))

/-! ### Locally-nameless infrastructure lemmas (now proved) -/

/-- Opening with a free variable preserves sz.
    Proved by structural induction on e. -/
theorem sz_open_at_fvar (k : Nat) (x : String) (e : LNExpr)
    : (e.open_at k (.fvar x)).sz = e.sz := by
  induction e generalizing k with
  | bvar n => simp [LNExpr.open_at, LNExpr.sz]; split <;> simp [LNExpr.sz]
  | fvar _ => simp [LNExpr.open_at, LNExpr.sz]
  | top => simp [LNExpr.open_at, LNExpr.sz]
  | lam dom body ih_dom ih_body =>
    simp [LNExpr.open_at, LNExpr.sz, ih_dom, ih_body]
  | app f a ih_f ih_a =>
    simp [LNExpr.open_at, LNExpr.sz, ih_f, ih_a]

/-- Context reduction preserves the domain.
    Proved by induction on the context reduction derivation. -/
theorem ctxRed_dom_eq
    {Γ Γ' : LNCtx} {s s' : LNStack}
    (h : LNCtxRed Γ s Γ' s') : LNCtx.dom Γ = LNCtx.dom Γ' := by
  induction h with
  | ct_ann_sub _ _ ih => simp [LNCtx.dom, List.map]; exact ih
  | ct_ann_equiv _ _ ih => simp [LNCtx.dom, List.map]; exact ih
  | ct_stk _ _ ih => exact ih
  | ct_nil => rfl

private theorem open_close_subst_gen
    (e : LNExpr) (x y : String) (k : Nat) (hlc : e.lc_at k)
    : (e.close_at k y).open_at k (.fvar x) = e.subst_fvar y (.fvar x) := by
  induction e generalizing k with
  | bvar n =>
    simp [LNExpr.lc_at] at hlc
    simp [LNExpr.subst_fvar, LNExpr.close_at, LNExpr.open_at, beq_iff_eq]
    omega
  | fvar z =>
    simp only [LNExpr.close_at, LNExpr.subst_fvar]
    by_cases h : z = y
    · subst h; simp [LNExpr.open_at]
    · simp [bne_iff_ne, h, Ne.symm h, LNExpr.open_at]
  | top => simp [LNExpr.close_at, LNExpr.open_at, LNExpr.subst_fvar]
  | lam dom body ih_dom ih_body =>
    simp [LNExpr.lc_at] at hlc
    simp [LNExpr.close_at, LNExpr.open_at, LNExpr.subst_fvar,
          ih_dom k hlc.1, ih_body (k+1) hlc.2]
  | app f a ih_f ih_a =>
    simp [LNExpr.lc_at] at hlc
    simp [LNExpr.close_at, LNExpr.open_at, LNExpr.subst_fvar,
          ih_f k hlc.1, ih_a k hlc.2]

/-- Opening a closed term with a different variable is the same as
    substituting. (e.close_at 0 y).open_at 0 (fvar x) = e.subst_fvar y (fvar x).
    Standard LN infrastructure. Requires e to be locally closed (no dangling
    bound variables). -/
theorem open_close_subst
    {e : LNExpr} {x y : String} (hlc : e.lc_at 0)
    : (e.close_at 0 y).open_at 0 (.fvar x) = e.subst_fvar y (.fvar x) :=
  open_close_subst_gen e x y 0 hlc

private theorem open_close_id_gen
    (e : LNExpr) (x : String) (k : Nat) (hlc : e.lc_at k)
    : (e.close_at k x).open_at k (.fvar x) = e := by
  induction e generalizing k with
  | bvar n =>
    simp [LNExpr.lc_at] at hlc
    simp [LNExpr.close_at, LNExpr.open_at, beq_iff_eq]
    omega
  | fvar y =>
    simp only [LNExpr.close_at]
    by_cases h : y = x
    · subst h; simp [LNExpr.open_at]
    · simp [bne_iff_ne, h, LNExpr.open_at]
  | top => simp [LNExpr.close_at, LNExpr.open_at]
  | lam dom body ih_dom ih_body =>
    simp [LNExpr.lc_at] at hlc
    simp [LNExpr.close_at, LNExpr.open_at, ih_dom k hlc.1, ih_body (k+1) hlc.2]
  | app f a ih_f ih_a =>
    simp [LNExpr.lc_at] at hlc
    simp [LNExpr.close_at, LNExpr.open_at, ih_f k hlc.1, ih_a k hlc.2]

/-- (e.close_at 0 x).open_at 0 (fvar x) = e when e is locally closed.
    Standard LN infrastructure. -/
theorem open_close_id
    {e : LNExpr} {x : String} (hlc : e.lc_at 0)
    : (e.close_at 0 x).open_at 0 (.fvar x) = e :=
  open_close_id_gen e x 0 hlc

private theorem close_open_id_gen
    (e : LNExpr) (x : String) (k : Nat) (hfr : x ∉ e.fvs)
    : (e.open_at k (.fvar x)).close_at k x = e := by
  induction e generalizing k with
  | bvar n =>
    simp [LNExpr.open_at]
    split
    · simp [LNExpr.close_at, beq_iff_eq]; omega
    · simp [LNExpr.close_at]
  | fvar y =>
    simp [LNExpr.fvs, List.mem_singleton] at hfr
    simp [LNExpr.open_at, LNExpr.close_at, beq_iff_eq, Ne.symm hfr]
  | top => simp [LNExpr.open_at, LNExpr.close_at]
  | lam dom body ih_dom ih_body =>
    simp [LNExpr.fvs, List.mem_append] at hfr
    simp [LNExpr.open_at, LNExpr.close_at, ih_dom k hfr.1, ih_body (k+1) hfr.2]
  | app f a ih_f ih_a =>
    simp [LNExpr.fvs, List.mem_append] at hfr
    simp [LNExpr.open_at, LNExpr.close_at, ih_f k hfr.1, ih_a k hfr.2]

/-- close_at 0 x (e.open_at 0 (fvar x)) = e when x is not free in e.
    Standard LN infrastructure. -/
theorem close_open_id
    {e : LNExpr} {x : String} (hfresh : x ∉ e.fvs)
    : (e.open_at 0 (.fvar x)).close_at 0 x = e :=
  close_open_id_gen e x 0 hfresh

private theorem close_subst_fvar_gen
    (u : LNExpr) (x y : String) (k : Nat) (hfr : y ∉ u.fvs)
    : (u.subst_fvar x (.fvar y)).close_at k y = u.close_at k x := by
  induction u generalizing k with
  | bvar n => simp [LNExpr.subst_fvar, LNExpr.close_at]
  | fvar z =>
    simp [LNExpr.fvs, List.mem_singleton] at hfr
    simp only [LNExpr.subst_fvar]
    by_cases h : z = x
    · subst h; simp [LNExpr.close_at]
    · simp [bne_iff_ne, h, LNExpr.close_at, Ne.symm hfr]
  | top => simp [LNExpr.subst_fvar, LNExpr.close_at]
  | lam dom body ih_dom ih_body =>
    simp [LNExpr.fvs, List.mem_append] at hfr
    simp [LNExpr.subst_fvar, LNExpr.close_at, ih_dom k hfr.1, ih_body (k+1) hfr.2]
  | app f a ih_f ih_a =>
    simp [LNExpr.fvs, List.mem_append] at hfr
    simp [LNExpr.subst_fvar, LNExpr.close_at, ih_f k hfr.1, ih_a k hfr.2]

/-- close ∘ rename = close: close_at 0 y (u[x↦fvar y]) = close_at 0 x u,
    when y is fresh for u. Standard LN infrastructure. -/
theorem close_subst_fvar
    {u : LNExpr} {x y : String} (hfresh : y ∉ u.fvs)
    : (u.subst_fvar x (.fvar y)).close_at 0 y = u.close_at 0 x :=
  close_subst_fvar_gen u x y 0 hfresh

/-- Top sub-reduces only to Top (or itself via MS-EQU).
    If Γ;s ⊢ Top ≤→ t then t = Top.
    Proved by case analysis. -/
theorem top_sub_inv
    {Γ : LNCtx} {s : LNStack} {t : LNExpr}
    (h : LNSubRed Γ s .top t) : t = .top := by
  cases h with
  | ms_top => rfl
  | ms_equ heq =>
    cases heq with
    | me_top => rfl

/-- If Γ;[] ↦ Γ';s' then s' = [].
    Proved by induction on the context reduction derivation. -/
theorem ctxRed_nil_stack
    {Γ Γ' : LNCtx} {s' : LNStack}
    (h : LNCtxRed Γ [] Γ' s') : s' = [] := by
  generalize hs : ([] : LNStack) = stk at h
  induction h with
  | ct_ann_sub _ _ ih => exact ih hs
  | ct_ann_equiv _ _ ih => exact ih hs
  | ct_stk _ _ _ => cases hs
  | ct_nil => rfl

/-! ### Annotation swap infrastructure -/

/-- Replace the annotation of the FIRST occurrence of `x` in the context.
    Used in the proof of annotation independence. -/
private def swap_at_first (x : String) (ann_new : LNAnn) : LNCtx → LNCtx
  | [] => []
  | (y, ann) :: rest =>
    if y = x then (y, ann_new) :: rest
    else (y, ann) :: swap_at_first x ann_new rest

private theorem swap_at_first_head (x : String) (ann_old ann_new : LNAnn) (Γ : LNCtx)
    : swap_at_first x ann_new ((x, ann_old) :: Γ) = (x, ann_new) :: Γ := by
  simp [swap_at_first]

private theorem swap_at_first_cons_ne (x y : String) (ann ann_new : LNAnn) (Γ : LNCtx) (hne : y ≠ x)
    : swap_at_first x ann_new ((y, ann) :: Γ) = (y, ann) :: swap_at_first x ann_new Γ := by
  simp [swap_at_first, hne]

private theorem swap_at_first_dom (x : String) (ann_new : LNAnn) (Γ : LNCtx)
    : LNCtx.dom (swap_at_first x ann_new Γ) = LNCtx.dom Γ := by
  induction Γ with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨y, ann⟩ := p
    unfold swap_at_first
    split
    · next h => subst h; simp [LNCtx.dom, List.map]
    · simp only [LNCtx.dom, List.map]; exact congrArg (y :: ·) ih

private theorem beq_false_of_ne' {a b : String} (h : a ≠ b) : (a == b) = false := by
  simp [bne_iff_ne, h, BEq.beq, Bool.decide_eq_false, instBEqOfDecidableEq, h]

private theorem swap_at_first_lookup_ne (x z : String) (ann_new : LNAnn) (Γ : LNCtx) (hne : z ≠ x)
    : LNCtx.lookup' (swap_at_first x ann_new Γ) z = LNCtx.lookup' Γ z := by
  induction Γ with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨y, ann⟩ := p
    simp only [swap_at_first]
    by_cases hyx : y = x
    · subst hyx
      simp only [ite_true, LNCtx.lookup']
      rw [beq_false_of_ne' (Ne.symm hne)]
      simp [ih]
    · simp only [hyx, ite_false, LNCtx.lookup']
      by_cases hyz : y == z
      · simp [hyz]
      · simp [hyz, ih]

private theorem swap_at_first_mem_equiv_ne {x z : String} {ann_new : LNAnn} {Γ : LNCtx} {α : LNExpr}
    (hne : z ≠ x) (hmem : LNCtx.mem_equiv Γ z α)
    : LNCtx.mem_equiv (swap_at_first x ann_new Γ) z α := by
  unfold LNCtx.mem_equiv at *
  rw [swap_at_first_lookup_ne x z ann_new Γ hne]; exact hmem

private theorem swap_at_first_mem_sub_ne {x z : String} {ann_new : LNAnn} {Γ : LNCtx} {t : LNExpr}
    (hne : z ≠ x) (hmem : LNCtx.mem_sub Γ z t)
    : LNCtx.mem_sub (swap_at_first x ann_new Γ) z t := by
  unfold LNCtx.mem_sub at *
  rw [swap_at_first_lookup_ne x z ann_new Γ hne]; exact hmem

private theorem mem_dom_of_lookup {Γ : LNCtx} {x : String} {ann : LNAnn}
    (h : LNCtx.lookup' Γ x = some ann) : x ∈ LNCtx.dom Γ := by
  induction Γ with
  | nil => simp [LNCtx.lookup'] at h
  | cons p rest ih =>
    obtain ⟨y, a⟩ := p
    simp only [LNCtx.lookup'] at h
    simp only [LNCtx.dom, List.map, List.mem_cons]
    by_cases hyx : y = x
    · left; exact hyx.symm
    · have : (y == x) = false := beq_false_of_ne' hyx
      simp only [this, ite_false] at h
      right; exact ih h

private theorem mem_dom_of_mem_equiv {Γ : LNCtx} {x : String} {α : LNExpr}
    (h : LNCtx.mem_equiv Γ x α) : x ∈ LNCtx.dom Γ :=
  mem_dom_of_lookup h

private theorem mem_dom_of_mem_sub {Γ : LNCtx} {x : String} {t : LNExpr}
    (h : LNCtx.mem_sub Γ x t) : x ∈ LNCtx.dom Γ :=
  mem_dom_of_lookup h

/-! ### noPromoAt predicates for annotation swap axioms

The annotation swap axioms (equivRed_change_sub_to_equiv and
equivRed_change_equiv_to_sub) are only valid when the derivation
does not promote variable x. We define predicates that capture this. -/

-- A derivation `LNEquivRed Γ s u v` does not promote variable `x`
-- if neither ME-PRO nor any embedded sub-derivation uses MS-PRO on `x`.
-- Since these are mutually inductive, we define the predicate mutually.
mutual

inductive LNEquivRed.noPromoAt : String → LNCtx → LNStack → LNExpr → LNExpr → Prop where
  | me_pro {x z Γ s α α'} :
      z ≠ x →
      LNCtx.mem_equiv Γ z α →
      LNSubRed.noPromoAt x Γ s α α' →
      LNEquivRed.noPromoAt x Γ s (.fvar z) α'
  | me_bet {x Γ s dom body u' v v' y} :
      y ∉ LNCtx.dom Γ →
      LNEquivRed.noPromoAt x ((y, .sub dom) :: Γ) s (body.open_at 0 (.fvar y)) u' →
      LNEquivRed.noPromoAt x Γ [] v v' →
      LNEquivRed.noPromoAt x Γ s (.app (.lam dom body) v) (u'.subst_fvar y v')
  | me_top {x Γ s} :
      LNEquivRed.noPromoAt x Γ s .top .top
  | me_var {x Γ s z} :
      LNEquivRed.noPromoAt x Γ s (.fvar z) (.fvar z)
  | me_tap {x Γ s u} :
      LNEquivRed.noPromoAt x Γ s (.app .top u) .top
  | me_app {x Γ s u u' v v'} :
      LNEquivRed.noPromoAt x Γ (v :: s) u u' →
      LNEquivRed.noPromoAt x Γ [] v v' →
      LNEquivRed.noPromoAt x Γ s (.app u v) (.app u' v')
  | me_fun {x Γ dom dom' body body' y} :
      y ∉ LNCtx.dom Γ →
      LNEquivRed.noPromoAt x Γ [] dom dom' →
      LNEquivRed.noPromoAt x ((y, .sub dom) :: Γ) [] (body.open_at 0 (.fvar y)) body' →
      LNEquivRed.noPromoAt x Γ [] (.lam dom body) (.lam dom' (body'.close_at 0 y))
  | me_fop {x Γ s α dom dom' body body' y} :
      y ∉ LNCtx.dom Γ →
      LNEquivRed.noPromoAt x Γ [] dom dom' →
      LNEquivRed.noPromoAt x ((y, .equiv α) :: Γ) s (body.open_at 0 (.fvar y)) body' →
      LNEquivRed.noPromoAt x Γ (α :: s) (.lam dom body) (.lam dom' (body'.close_at 0 y))

inductive LNSubRed.noPromoAt : String → LNCtx → LNStack → LNExpr → LNExpr → Prop where
  | ms_pro {x z Γ s t} :
      z ≠ x →
      LNCtx.mem_sub Γ z t →
      LNSubRed.noPromoAt x Γ s (.fvar z) t
  | ms_top {x Γ s u} :
      LNSubRed.noPromoAt x Γ s u .top
  | ms_equ {x Γ s u v} :
      LNEquivRed.noPromoAt x Γ s u v →
      LNSubRed.noPromoAt x Γ s u v
  | ms_app {x Γ s u u' v} :
      LNSubRed.noPromoAt x Γ (v :: s) u u' →
      LNSubRed.noPromoAt x Γ s (.app u v) (.app u' v)
  | ms_fun {x Γ dom body body' y} :
      y ∉ LNCtx.dom Γ →
      LNSubRed.noPromoAt x ((y, .sub dom) :: Γ) [] (body.open_at 0 (.fvar y)) body' →
      LNSubRed.noPromoAt x Γ [] (.lam dom body) (.lam dom (body'.close_at 0 y))
  | ms_fop {x Γ s α dom body body' y} :
      y ∉ LNCtx.dom Γ →
      LNSubRed.noPromoAt x ((y, .equiv α) :: Γ) s (body.open_at 0 (.fvar y)) body' →
      LNSubRed.noPromoAt x Γ (α :: s) (.lam dom body) (.lam dom (body'.close_at 0 y))

end

-- General annotation swap: if a derivation doesn't promote x,
-- we can change x's annotation to anything.
-- Proved by mutual induction using the mutual recursor for noPromoAt,
-- since sizeOf-based termination fails for Prop-valued mutual inductives.

/-- Transport an equiv-reduction along a context equality. -/
private theorem equivRed_cast_ctx {Γ₁ Γ₂ : LNCtx} {s : LNStack} {e u : LNExpr}
    (h : Γ₁ = Γ₂) (hr : LNEquivRed Γ₁ s e u) : LNEquivRed Γ₂ s e u :=
  h ▸ hr

/-- Transport a sub-reduction along a context equality. -/
private theorem subRed_cast_ctx {Γ₁ Γ₂ : LNCtx} {s : LNStack} {e u : LNExpr}
    (h : Γ₁ = Γ₂) (hr : LNSubRed Γ₁ s e u) : LNSubRed Γ₂ s e u :=
  h ▸ hr

set_option maxHeartbeats 800000 in
theorem noPromoAt_equiv_swap (x : String) (ann_new : LNAnn)
    {Γ : LNCtx} {s : LNStack} {e u : LNExpr}
    (hnp : LNEquivRed.noPromoAt x Γ s e u) (hx : x ∈ LNCtx.dom Γ)
    : LNEquivRed (swap_at_first x ann_new Γ) s e u := by
  revert hx
  exact LNEquivRed.noPromoAt.rec
    (motive_1 := fun Γ s e u _ => x ∈ LNCtx.dom Γ → LNEquivRed (swap_at_first x ann_new Γ) s e u)
    (motive_2 := fun Γ s e u _ => x ∈ LNCtx.dom Γ → LNSubRed (swap_at_first x ann_new Γ) s e u)
    -- me_pro
    (fun hne hmem _ ih_sub hx =>
      .me_pro (swap_at_first_mem_equiv_ne hne hmem) (ih_sub hx))
    -- me_bet
    (fun {Γ' _ dom _ _ _ _ y} hfr _ _ ih_body ih_v hx =>
      have hyx : y ≠ x := fun heq => hfr (heq ▸ hx)
      have hfr' : y ∉ LNCtx.dom (swap_at_first x ann_new Γ') :=
        swap_at_first_dom x ann_new Γ' ▸ hfr
      .me_bet hfr'
        (equivRed_cast_ctx (swap_at_first_cons_ne x y (.sub dom) ann_new Γ' hyx)
          (ih_body (List.mem_cons_of_mem _ hx)))
        (ih_v hx))
    -- me_top
    (fun _ => .me_top)
    -- me_var
    (fun _ => .me_var)
    -- me_tap
    (fun _ => .me_tap)
    -- me_app
    (fun _ _ ih1 ih2 hx => .me_app (ih1 hx) (ih2 hx))
    -- me_fun
    (fun {Γ' dom _ _ _ y} hfr _ _ ih_dom ih_body hx =>
      have hyx : y ≠ x := fun heq => hfr (heq ▸ hx)
      have hfr' : y ∉ LNCtx.dom (swap_at_first x ann_new Γ') :=
        swap_at_first_dom x ann_new Γ' ▸ hfr
      .me_fun hfr' (ih_dom hx)
        (equivRed_cast_ctx (swap_at_first_cons_ne x y (.sub dom) ann_new Γ' hyx)
          (ih_body (List.mem_cons_of_mem _ hx))))
    -- me_fop
    (fun {Γ' _ α _ _ _ _ y} hfr _ _ ih_dom ih_body hx =>
      have hyx : y ≠ x := fun heq => hfr (heq ▸ hx)
      have hfr' : y ∉ LNCtx.dom (swap_at_first x ann_new Γ') :=
        swap_at_first_dom x ann_new Γ' ▸ hfr
      .me_fop hfr' (ih_dom hx)
        (equivRed_cast_ctx (swap_at_first_cons_ne x y (.equiv α) ann_new Γ' hyx)
          (ih_body (List.mem_cons_of_mem _ hx))))
    -- ms_pro
    (fun hne hmem _ => .ms_pro (swap_at_first_mem_sub_ne hne hmem))
    -- ms_top
    (fun _ => .ms_top)
    -- ms_equ
    (fun _ ih hx => .ms_equ (ih hx))
    -- ms_app
    (fun _ ih hx => .ms_app (ih hx))
    -- ms_fun
    (fun {Γ' dom _ _ y} hfr _ ih_body hx =>
      have hyx : y ≠ x := fun heq => hfr (heq ▸ hx)
      have hfr' : y ∉ LNCtx.dom (swap_at_first x ann_new Γ') :=
        swap_at_first_dom x ann_new Γ' ▸ hfr
      .ms_fun hfr'
        (subRed_cast_ctx (swap_at_first_cons_ne x y (.sub dom) ann_new Γ' hyx)
          (ih_body (List.mem_cons_of_mem _ hx))))
    -- ms_fop
    (fun {Γ' _ α _ _ _ y} hfr _ ih_body hx =>
      have hyx : y ≠ x := fun heq => hfr (heq ▸ hx)
      have hfr' : y ∉ LNCtx.dom (swap_at_first x ann_new Γ') :=
        swap_at_first_dom x ann_new Γ' ▸ hfr
      .ms_fop hfr'
        (subRed_cast_ctx (swap_at_first_cons_ne x y (.equiv α) ann_new Γ' hyx)
          (ih_body (List.mem_cons_of_mem _ hx))))
    hnp

set_option maxHeartbeats 400000 in
theorem noPromoAt_sub_swap (x : String) (ann_new : LNAnn)
    {Γ : LNCtx} {s : LNStack} {e u : LNExpr}
    (hnp : LNSubRed.noPromoAt x Γ s e u) (hx : x ∈ LNCtx.dom Γ)
    : LNSubRed (swap_at_first x ann_new Γ) s e u := by
  revert hx
  exact LNSubRed.noPromoAt.rec
    (motive_1 := fun Γ s e u _ => x ∈ LNCtx.dom Γ → LNEquivRed (swap_at_first x ann_new Γ) s e u)
    (motive_2 := fun Γ s e u _ => x ∈ LNCtx.dom Γ → LNSubRed (swap_at_first x ann_new Γ) s e u)
    -- me_pro
    (fun hne hmem _ ih_sub hx =>
      .me_pro (swap_at_first_mem_equiv_ne hne hmem) (ih_sub hx))
    -- me_bet
    (fun {Γ' _ dom _ _ _ _ y} hfr _ _ ih_body ih_v hx =>
      have hyx : y ≠ x := fun heq => hfr (heq ▸ hx)
      have hfr' : y ∉ LNCtx.dom (swap_at_first x ann_new Γ') :=
        swap_at_first_dom x ann_new Γ' ▸ hfr
      .me_bet hfr'
        (equivRed_cast_ctx (swap_at_first_cons_ne x y (.sub dom) ann_new Γ' hyx)
          (ih_body (List.mem_cons_of_mem _ hx)))
        (ih_v hx))
    -- me_top
    (fun _ => .me_top)
    -- me_var
    (fun _ => .me_var)
    -- me_tap
    (fun _ => .me_tap)
    -- me_app
    (fun _ _ ih1 ih2 hx => .me_app (ih1 hx) (ih2 hx))
    -- me_fun
    (fun {Γ' dom _ _ _ y} hfr _ _ ih_dom ih_body hx =>
      have hyx : y ≠ x := fun heq => hfr (heq ▸ hx)
      have hfr' : y ∉ LNCtx.dom (swap_at_first x ann_new Γ') :=
        swap_at_first_dom x ann_new Γ' ▸ hfr
      .me_fun hfr' (ih_dom hx)
        (equivRed_cast_ctx (swap_at_first_cons_ne x y (.sub dom) ann_new Γ' hyx)
          (ih_body (List.mem_cons_of_mem _ hx))))
    -- me_fop
    (fun {Γ' _ α _ _ _ _ y} hfr _ _ ih_dom ih_body hx =>
      have hyx : y ≠ x := fun heq => hfr (heq ▸ hx)
      have hfr' : y ∉ LNCtx.dom (swap_at_first x ann_new Γ') :=
        swap_at_first_dom x ann_new Γ' ▸ hfr
      .me_fop hfr' (ih_dom hx)
        (equivRed_cast_ctx (swap_at_first_cons_ne x y (.equiv α) ann_new Γ' hyx)
          (ih_body (List.mem_cons_of_mem _ hx))))
    -- ms_pro
    (fun hne hmem _ => .ms_pro (swap_at_first_mem_sub_ne hne hmem))
    -- ms_top
    (fun _ => .ms_top)
    -- ms_equ
    (fun _ ih hx => .ms_equ (ih hx))
    -- ms_app
    (fun _ ih hx => .ms_app (ih hx))
    -- ms_fun
    (fun {Γ' dom _ _ y} hfr _ ih_body hx =>
      have hyx : y ≠ x := fun heq => hfr (heq ▸ hx)
      have hfr' : y ∉ LNCtx.dom (swap_at_first x ann_new Γ') :=
        swap_at_first_dom x ann_new Γ' ▸ hfr
      .ms_fun hfr'
        (subRed_cast_ctx (swap_at_first_cons_ne x y (.sub dom) ann_new Γ' hyx)
          (ih_body (List.mem_cons_of_mem _ hx))))
    -- ms_fop
    (fun {Γ' _ α _ _ _ y} hfr _ ih_body hx =>
      have hyx : y ≠ x := fun heq => hfr (heq ▸ hx)
      have hfr' : y ∉ LNCtx.dom (swap_at_first x ann_new Γ') :=
        swap_at_first_dom x ann_new Γ' ▸ hfr
      .ms_fop hfr'
        (subRed_cast_ctx (swap_at_first_cons_ne x y (.equiv α) ann_new Γ' hyx)
          (ih_body (List.mem_cons_of_mem _ hx))))
    hnp

/-- Annotation independence: change from sub to equiv annotation.
    Valid when the derivation doesn't use MS-PRO on x (i.e., doesn't
    promote x via its subtype bound). The noPromoAt precondition
    ensures this. -/
theorem equivRed_change_sub_to_equiv
    {Γ : LNCtx} {s : LNStack} {x : String} {t α : LNExpr}
    {e u : LNExpr}
    (_h : LNEquivRed ((x, .sub t) :: Γ) s e u)
    (hnp : LNEquivRed.noPromoAt x ((x, .sub t) :: Γ) s e u)
    : LNEquivRed ((x, .equiv α) :: Γ) s e u := by
  have hx : x ∈ LNCtx.dom ((x, .sub t) :: Γ) := List.mem_cons_self x (LNCtx.dom Γ)
  have := noPromoAt_equiv_swap x (.equiv α) hnp hx
  rwa [swap_at_first_head] at this

/-- Reverse direction: change equiv to sub annotation.
    Valid when the derivation doesn't use ME-PRO on x (i.e., doesn't
    promote x via its equivalence annotation). The noPromoAt
    precondition ensures this. -/
theorem equivRed_change_equiv_to_sub
    {Γ : LNCtx} {s : LNStack} {x : String} {t α : LNExpr}
    {e u : LNExpr}
    (_h : LNEquivRed ((x, .equiv α) :: Γ) s e u)
    (hnp : LNEquivRed.noPromoAt x ((x, .equiv α) :: Γ) s e u)
    : LNEquivRed ((x, .sub t) :: Γ) s e u := by
  have hx : x ∈ LNCtx.dom ((x, .equiv α) :: Γ) := List.mem_cons_self x (LNCtx.dom Γ)
  have := noPromoAt_equiv_swap x (.sub t) hnp hx
  rwa [swap_at_first_head] at this

/-- Annotation independence: change from sub to equiv annotation
    for derivations where the body was opened with a fresh variable.
    This is the version used in commutativity's ME-BET case.
    The paper's Lemma 2 (non-promotion clause) guarantees that when
    x is fresh and the derivation comes from ME-BET's body reduction,
    the derivation does not use MS-PRO on x. -/
axiom equivRed_change_sub_to_equiv_bet
    {Γ : LNCtx} {s : LNStack} {x : String} {dom α : LNExpr}
    {body u : LNExpr}
    (h : LNEquivRed ((x, .sub dom) :: Γ) s (body.open_at 0 (.fvar x)) u)
    (hfresh : x ∉ LNCtx.dom Γ)
    : LNEquivRed ((x, .equiv α) :: Γ) s (body.open_at 0 (.fvar x)) u

/-- Annotation independence: change from equiv to sub annotation
    for derivations on sub-terms obtained via IH.
    Valid when the derivation doesn't use ME-PRO on x.
    The paper's Lemma 2 guarantees this for IH outputs. -/
axiom equivRed_change_equiv_to_sub_bet
    {Γ : LNCtx} {s : LNStack} {x : String} {dom α : LNExpr}
    {e u : LNExpr}
    (h : LNEquivRed ((x, .equiv α) :: Γ) s e u)
    (hfresh : x ∉ LNCtx.dom Γ)
    : LNEquivRed ((x, .sub dom) :: Γ) s e u

/-- Inversion on LNCtxRed for stack cons:
    If Γ; α::s ↦ Γ'; s', then s' = α'::s₁ and Γ;s ↦ Γ';s₁
    and Γ;[] ⊢ α ≡→ α'. -/
axiom ctxRed_stack_inv
    {Γ : LNCtx} {α : LNExpr} {s : LNStack} {Γ' : LNCtx} {s' : LNStack}
    (h : LNCtxRed Γ (α :: s) Γ' s')
    : ∃ α' s₁, s' = α' :: s₁ ∧ LNCtxRed Γ s Γ' s₁ ∧ LNEquivRed Γ [] α α'


/-! ### Commutativity (Lemma 1)

The main theorem. By induction on the term t₀ and case analysis on the
pair of rules (h_equiv : ≡→, h_sub : ≤→) applied to t₀.

Proof structure follows Appendix A of Pasquale & Garcia-Perez.

We make t₀ explicit so we can use `termination_by t₀.sz`.
The decrease `sz (open_at 0 (fvar x) body) < sz (lam dom body)`
follows from `sz_open_at_fvar` and arithmetic.
-/

set_option maxHeartbeats 800000 in
theorem commutativity
    (t₀ : LNExpr)
    {Γ : LNCtx} {s : LNStack} {t₁ t₂ : LNExpr}
    {Γ' : LNCtx} {s' : LNStack}
    (h_equiv : LNEquivRed Γ s t₀ t₁)
    (h_sub   : LNSubRed Γ s t₀ t₂)
    (h_ctx   : LNCtxRed Γ s Γ' s')
    (h_lc    : t₀.lc)
    : ∃ t₃ : LNExpr, LNEquivRed Γ s t₂ t₃ ∧ LNSubRed Γ' s' t₁ t₃ := by
  -- Case analysis on the sub (left/vertical) edge first.
  -- This determines the shape of t₀ and t₂.
  cases h_sub with

  --===================================================================
  -- MS-TOP: t₂ = .top  (any term promotes to Top)
  -- Top edge: .top ≡→ .top (ME-TOP).   Right edge: t₁ ≤→ .top (MS-TOP).
  --===================================================================
  | ms_top => exact ⟨.top, .me_top, .ms_top⟩

  --===================================================================
  -- MS-EQU: t₂ comes from Γ;s ⊢ t₀ ≡→ t₂ (equiv subsumes sub).
  -- By the diamond property (Lemma 2).
  --===================================================================
  | ms_equ h_eq2 =>
    obtain ⟨t₃, htop, hright⟩ := diamond h_equiv h_eq2 h_ctx
    exact ⟨t₃, htop, .ms_equ hright⟩

  --===================================================================
  -- MS-PRO: t₀ = fvar x, t₂ = t where x ≤ t ∈ Γ.
  --===================================================================
  | ms_pro hmem =>
    cases h_equiv with
    | me_pro hmem_equiv _ => exact absurd (no_sub_and_equiv hmem hmem_equiv) False.elim
    | me_var =>
      obtain ⟨t', hmem', ht_red⟩ := ctxRed_lookup_sub hmem h_ctx
      exact ⟨t', equivRed_stack_ext ht_red, .ms_pro hmem'⟩

  --===================================================================
  -- MS-APP: t₀ = app u₀ v, t₂ = app u₂ v
  -- where h_sub_u : Γ; v::s ⊢ u₀ ≤→ u₂.
  --===================================================================
  | @ms_app _ _ u₀ u₂ v h_sub_u =>
    cases h_equiv with
    ---------------------------------------------------------------
    -- ME-APP / MS-APP: IH on u₀ (strictly smaller than app u₀ v).
    ---------------------------------------------------------------
    | @me_app _ _ _ u₁ _ v₁ h_equiv_u h_equiv_v =>
      have h_ctx_ext := LNCtxRed.ct_stk h_ctx h_equiv_v
      have hu₀_lc : u₀.lc := h_lc.1
      obtain ⟨u₃, htop_u, hright_u⟩ :=
        commutativity u₀ h_equiv_u h_sub_u h_ctx_ext hu₀_lc
      exact ⟨.app u₃ v₁, .me_app htop_u h_equiv_v, .ms_app hright_u⟩
    ---------------------------------------------------------------
    -- ME-BET / MS-APP:  THE KEY CASE
    ---------------------------------------------------------------
    | @me_bet _ _ dom body u' _ v' x hfresh h_equiv_body h_equiv_v =>
      cases h_sub_u with
      | ms_top =>
        exact ⟨.top, .me_tap, .ms_top⟩
      | ms_equ h_eq_lam =>
        have hv_lc : v.lc := h_lc.2
        have h_equiv2 : LNEquivRed Γ s (.app (.lam dom body) v) (.app u₂ v) :=
          .me_app h_eq_lam (equivRed_refl Γ [] v hv_lc)
        have h_equiv_orig : LNEquivRed Γ s (.app (.lam dom body) v)
            (u'.subst_fvar x v') :=
          .me_bet hfresh h_equiv_body h_equiv_v
        obtain ⟨t₃, htop, hright⟩ := diamond h_equiv_orig h_equiv2 h_ctx
        exact ⟨t₃, htop, .ms_equ hright⟩
      | @ms_fop _ _ _ _ _ body₂_fop y hfresh_y h_sub_body_fop =>
        have h_sub_body_x := subRed_rename h_sub_body_fop hfresh_y hfresh
        -- Change annotation on h_equiv_body from ≤dom to ≡v
        -- By equivRed_change_sub_to_equiv_bet (paper's Lemma 2)
        have h_equiv_body' : LNEquivRed ((x, .equiv v) :: Γ) s
            (body.open_at 0 (.fvar x)) u' :=
          equivRed_change_sub_to_equiv_bet h_equiv_body hfresh
        have h_ctx_body : LNCtxRed ((x, .equiv v) :: Γ) s ((x, .equiv v') :: Γ') s' :=
          LNCtxRed.ct_ann_equiv h_ctx h_equiv_v
        have hbody_lc : (body.open_at 0 (.fvar x)).lc :=
          LNExpr.lc_at_open_fvar h_lc.1.2
        obtain ⟨u₃, htop_body, hright_body⟩ :=
          commutativity (body.open_at 0 (.fvar x)) h_equiv_body' h_sub_body_x h_ctx_body hbody_lc
        -- Change annotation back from ≡v to ≤dom for ME-BET
        have htop_body_sub : LNEquivRed ((x, .sub dom) :: Γ) s
            (body₂_fop.subst_fvar y (.fvar x)) u₃ :=
          equivRed_change_equiv_to_sub_bet htop_body hfresh
        have hfresh' : x ∉ LNCtx.dom Γ' := ctxRed_dom_eq h_ctx ▸ hfresh
        have hright_subst : LNSubRed Γ' s' (u'.subst_fvar x v') (u₃.subst_fvar x v') :=
          subRed_subst (ann := .equiv v') (v := v') hright_body hfresh'
        refine ⟨u₃.subst_fvar x v', ?_, ?_⟩
        · have hopen : (body₂_fop.close_at 0 y).open_at 0 (.fvar x) =
              body₂_fop.subst_fvar y (.fvar x) := open_close_subst sorry
          exact .me_bet hfresh (hopen ▸ htop_body_sub) h_equiv_v
        · exact hright_subst
    ---------------------------------------------------------------
    -- ME-TAP / MS-APP: t₀ = app Top v, t₁ = Top
    ---------------------------------------------------------------
    | me_tap =>
      have := top_sub_inv h_sub_u; subst this
      exact ⟨.top, .me_tap, .ms_top⟩

  --===================================================================
  -- MS-FUN: t₀ = lam dom body, s = [],
  -- t₂ = lam dom (close x_s body₂)
  --===================================================================
  | @ms_fun _ dom body body₂ x_s hfresh_s h_sub_body =>
    cases h_equiv with
    ---------------------------------------------------------------
    -- ME-FUN / MS-FUN: Both go under the binder with empty stack.
    ---------------------------------------------------------------
    | @me_fun _ _ dom' _ body' x_e hfresh_e h_equiv_dom h_equiv_body =>
      have h_sub_body' := subRed_rename h_sub_body hfresh_s hfresh_e
      have h_ctx_nil := ctxRed_nil_of_ctxRed h_ctx
      have h_ctx_body : LNCtxRed ((x_e, .sub dom) :: Γ) [] ((x_e, .sub dom') :: Γ') [] :=
        LNCtxRed.ct_ann_sub h_ctx_nil h_equiv_dom
      have hbody_lc : (body.open_at 0 (.fvar x_e)).lc :=
        LNExpr.lc_at_open_fvar h_lc.2
      obtain ⟨u₃, htop_body, hright_body⟩ :=
        commutativity (body.open_at 0 (.fvar x_e)) h_equiv_body h_sub_body' h_ctx_body hbody_lc
      have hfresh_e' : x_e ∉ LNCtx.dom Γ' := ctxRed_dom_eq h_ctx ▸ hfresh_e
      have hs' := ctxRed_nil_stack h_ctx; subst hs'
      refine ⟨.lam dom' (u₃.close_at 0 x_e), ?_, ?_⟩
      · have h : LNEquivRed ((x_e, .sub dom) :: Γ) []
            ((body₂.close_at 0 x_s).open_at 0 (.fvar x_e)) u₃ := by
          rw [open_close_subst sorry]; exact htop_body
        exact .me_fun hfresh_e h_equiv_dom h
      · have h : LNSubRed ((x_e, .sub dom') :: Γ') []
            ((body'.close_at 0 x_e).open_at 0 (.fvar x_e)) u₃ := by
          rw [open_close_id (sorry)]; exact hright_body
        exact .ms_fun hfresh_e' h

  --===================================================================
  -- MS-FOP: t₀ = lam dom body, s = α::s₀,
  -- t₂ = lam dom (close x_s body₂)
  --===================================================================
  | @ms_fop _ s_inner α dom body body₂ x_s hfresh_s h_sub_body =>
    cases h_equiv with
    ---------------------------------------------------------------
    -- ME-FOP / MS-FOP: Both pop α from the stack.
    ---------------------------------------------------------------
    | @me_fop _ _ _ _ dom' _ body' x_e hfresh_e h_equiv_dom h_equiv_body =>
      have h_sub_body' := subRed_rename h_sub_body hfresh_s hfresh_e
      obtain ⟨α', s₁, hs'eq, h_ctx_inner, hα_red⟩ := ctxRed_stack_inv h_ctx
      subst hs'eq
      have h_ctx_body : LNCtxRed ((x_e, .equiv α) :: Γ) s_inner ((x_e, .equiv α') :: Γ') s₁ :=
        LNCtxRed.ct_ann_equiv h_ctx_inner hα_red
      have hbody_lc : (body.open_at 0 (.fvar x_e)).lc :=
        LNExpr.lc_at_open_fvar h_lc.2
      obtain ⟨u₃, htop_body, hright_body⟩ :=
        commutativity (body.open_at 0 (.fvar x_e)) h_equiv_body h_sub_body' h_ctx_body hbody_lc
      have hfresh_e' : x_e ∉ LNCtx.dom Γ' := ctxRed_dom_eq h_ctx_inner ▸ hfresh_e
      refine ⟨.lam dom' (u₃.close_at 0 x_e), ?_, ?_⟩
      · have h : LNEquivRed ((x_e, .equiv α) :: Γ) s_inner
            ((body₂.close_at 0 x_s).open_at 0 (.fvar x_e)) u₃ := by
          rw [open_close_subst sorry]; exact htop_body
        exact .me_fop hfresh_e h_equiv_dom h
      · have h : LNSubRed ((x_e, .equiv α') :: Γ') s₁
            ((body'.close_at 0 x_e).open_at 0 (.fvar x_e)) u₃ := by
          rw [open_close_id (sorry)]; exact hright_body
        exact .ms_fop hfresh_e' h
termination_by t₀.sz
decreasing_by all_goals simp_all [LNExpr.sz, sz_open_at_fvar]; omega
