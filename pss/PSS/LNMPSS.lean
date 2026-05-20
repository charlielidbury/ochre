/-!
# Machine-Based Pure Subtype Systems (MPSS) — Locally Nameless Encoding

Mechanisation of the MPSS calculus from:
  Pasquale & García-Pérez, "Towards the type safety of Pure Subtype Systems
  (Full version)", CSL 2026.

This file re-encodes MPSS using the **locally nameless** representation:
  - Bound variables: de Bruijn indices (for lambda-bound vars)
  - Free variables: names (String atoms) — no shifting needed under binders

This avoids the de Bruijn scope mismatches that plague the plain de Bruijn
encoding in PSS/MPSS.lean (8 false lemma statements caused by shift issues).

## Contents
- LNExpr: locally nameless terms
- open_at / close_at: opening and closing operations
- LNAnn, LNCtx, LNStack: annotations, contexts, stacks
- LNEquivRed: equivalence reduction (Figure 2, top half)
- LNSubRed: subtyping reduction (Figure 2, bottom half)
- LNCtxRed: context reduction (Section 3)
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
    This is the standard locally-nameless opening operation. -/
def open_at (k : Nat) (u : LNExpr) : LNExpr → LNExpr
  | .bvar n => if n == k then u else .bvar n
  | .fvar x => .fvar x
  | .top => .top
  | .lam dom body => .lam (open_at k u dom) (open_at (k + 1) u body)
  | .app f a => .app (open_at k u f) (open_at k u a)

/-- Shorthand: open at depth 0 (the most common case). -/
abbrev open' (u : LNExpr) (e : LNExpr) : LNExpr := e.open_at 0 u

/-- Close: replace `fvar x` with `bvar k` in `e`.
    The inverse of opening. -/
def close_at (k : Nat) (x : String) : LNExpr → LNExpr
  | .bvar n => .bvar n
  | .fvar y => if y == x then .bvar k else .fvar y
  | .top => .top
  | .lam dom body => .lam (close_at k x dom) (close_at (k + 1) x body)
  | .app f a => .app (close_at k x f) (close_at k x a)

/-- Capture-avoiding substitution: replace free variable `x` with `u`. -/
def subst_fvar (x : String) (u : LNExpr) : LNExpr → LNExpr
  | .bvar n => .bvar n
  | .fvar y => if y == x then u else .fvar y
  | .top => .top
  | .lam dom body => .lam (subst_fvar x u dom) (subst_fvar x u body)
  | .app f a => .app (subst_fvar x u f) (subst_fvar x u a)

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
def lc : LNExpr → Prop := lc_at 0

/-- Size of a term (for termination proofs).
    This counts the number of constructors. -/
def sz : LNExpr → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .top => 1
  | .lam dom body => 1 + dom.sz + body.sz
  | .app f a => 1 + f.sz + a.sz

end LNExpr

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

/-! ### Helper lemmas for commutativity

These are stated as axioms for now. Each corresponds to a lemma from
the paper's appendix. Proving each one is straightforward but would
be a large amount of code; the point of this file is to mechanise the
*commutativity proof structure* itself.
-/

/-! ## AUDIT RESULTS — SUMMARY

### Root cause: Lean 4 dot notation for `open_at` and `subst_fvar`

Both `open_at` and `subst_fvar` take two `LNExpr` arguments:
  - `def open_at (k : Nat) (u : LNExpr) : LNExpr → LNExpr`
  - `def subst_fvar (x : String) (u : LNExpr) : LNExpr → LNExpr`

Lean 4 dot notation `e.f args` fills the first parameter matching `e`'s type.
For these functions, that's the `u` (replacement) parameter, NOT the expression
being operated on. So:
  - `body.open_at 0 (.fvar x)` = `open_at 0 body (.fvar x)` = "replace bvar 0 with body in (fvar x)" = fvar x
  - `u'.subst_fvar x v'` = `subst_fvar x u' v'` = "replace x with u' in v'" = v'[x := u']

The INTENDED semantics were:
  - `body.open_at 0 (.fvar x)` should be "open body with fvar x" = body[bvar 0 := fvar x]
  - `u'.subst_fvar x v'` should be "substitute v' for x in u'" = u'[x := v']

This affects:
  1. The INDUCTIVE RULES themselves (ME-BET, ME-FUN, ME-FOP, MS-FUN, MS-FOP all use `body.open_at`)
  2. Multiple axioms that use `open_at` or `subst_fvar` in their statements

### Axioms proven FALSE (with Lean-verified `def ... : False`):
  - `equivRed_subst` — dot notation bug on subst_fvar
  - `subRed_subst` — dot notation bug on subst_fvar
  - `equivRed_change_equiv_to_sub` — semantic issue (ME-PRO can fire on x with .equiv)
  - `equivRed_change_sub_to_equiv` — semantic issue (MS-PRO can fire on x with .sub)
  - `close_subst_fvar` — dot notation bug on subst_fvar
  - `sz_open_at_fvar` — dot notation bug on open_at
  - `close_open_id` — dot notation bug on open_at
  - `open_close_id` — dot notation bug on open_at
  - `open_close_subst` — dot notation bug on both

### Axioms that are TRIVIALLY TRUE but vacuous (not what was intended):
  - `equivRed_rename` — body.open_at collapses to fvar, making both sides trivial
  - `subRed_rename` — same

### Axioms likely TRUE (no counterexample found):
  - `equivRed_refl`, `ctxRed_refl`, `ctxRed_nil_of_ctxRed`
  - `ctxRed_lookup_sub`, `ctxRed_lookup_equiv`, `no_sub_and_equiv`
  - `ctxRed_dom_eq`, `top_sub_inv`, `ctxRed_nil_stack`, `ctxRed_stack_inv`
  - `diamond` (assuming paper proof correctness)

### Axioms with UNCERTAIN status:
  - `equivRed_weaken`, `subRed_weaken` — suspicious (context annotation changes)
  - `equivRed_stack_ext`, `subRed_stack_ext` — likely false for same reason as
    equivRed_change_sub_to_equiv (ME-FUN uses .sub, ME-FOP uses .equiv), but
    dot notation bug makes the rules semantically different from intended so
    it's unclear whether the BUG-AFFECTED versions of these axioms are also false.

### Recommended fix
  Change `open_at` and `subst_fvar` so the dot-notation target is the LAST argument:
    def open_at (k : Nat) (u : LNExpr) (e : LNExpr) : LNExpr := ...
    def subst_fvar (x : String) (u : LNExpr) (e : LNExpr) : LNExpr := ...
  Or equivalently, swap the argument order to put the "self" expression first:
    def open_at (e : LNExpr) (k : Nat) (u : LNExpr) : LNExpr := ...
  This way `body.open_at 0 (.fvar x)` would correctly mean "open body at 0 with fvar x".
-/

/-- Reflexivity of ≡→ (Proposition 18).
    Every term equiv-reduces to itself. -/
axiom equivRed_refl (Γ : LNCtx) (s : LNStack) (u : LNExpr)
    : LNEquivRed Γ s u u

/-- Reflexivity of ≤→ (via MS-EQU + reflexivity of ≡→). -/
theorem subRed_refl (Γ : LNCtx) (s : LNStack) (u : LNExpr)
    : LNSubRed Γ s u u :=
  .ms_equ (equivRed_refl Γ s u)

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

/-- Context reduction is reflexive. -/
axiom ctxRed_refl (Γ : LNCtx) (s : LNStack) : LNCtxRed Γ s Γ s

/-- Lemma 36: stripping the stack from a context reduction. -/
axiom ctxRed_nil_of_ctxRed
    {Γ Γ' : LNCtx} {s s' : LNStack}
    (h : LNCtxRed Γ s Γ' s') : LNCtxRed Γ [] Γ' []

/-- Substitution for ≡→ (Lemma 32).
    If (x,ann)::Γ; s ⊢ u ≡→ u' and Γ;[] ⊢ v ≡→ v'
    then Γ;s ⊢ u[x↦v] ≡→ u'[x↦v']. -/
axiom equivRed_subst
    {Γ : LNCtx} {s : LNStack} {x : String} {ann : LNAnn}
    {u u' v v' : LNExpr}
    (hbody : LNEquivRed ((x, ann) :: Γ) s u u')
    (harg  : LNEquivRed Γ [] v v')
    : LNEquivRed Γ s (u.subst_fvar x v) (u'.subst_fvar x v')

/-! ### AUDIT: equivRed_subst is FALSE

    Dot notation: e.subst_fvar x u = LNExpr.subst_fvar x e u = "replace x with e in u".
    So the axiom says: if (x,ann)::Γ;s ⊢ u ≡→ u' and Γ;[] ⊢ v ≡→ v',
    then Γ;s ⊢ (replace x with u in v) ≡→ (replace x with u' in v').

    Counterexample: ann = .equiv .top, u = fvar "x", u' = .top, v = v' = fvar "x", Γ=[], s=[].
    - hbody: [("x", .equiv .top)]; [] ⊢ fvar "x" ≡→ .top  by ME-PRO
    - harg:  []; [] ⊢ fvar "x" ≡→ fvar "x"  by ME-VAR
    - LHS: replace x with (fvar "x") in (fvar "x") = fvar "x"
    - RHS: replace x with .top in (fvar "x") = .top
    - Conclusion: []; [] ⊢ fvar "x" ≡→ .top — underivable in empty context
-/

private theorem audit4_mem : LNCtx.mem_equiv [("x", .equiv .top)] "x" .top := by
  simp [LNCtx.mem_equiv, LNCtx.lookup']

private def audit4_derivation :
    LNEquivRed [("x", .equiv .top)] [] (.fvar "x") .top :=
  .me_pro audit4_mem .ms_top

private def audit4_arg :
    LNEquivRed ([] : LNCtx) [] (.fvar "x") (.fvar "x") :=
  .me_var

-- Check the substitution results via native_decide
-- u.subst_fvar x v = (fvar "x").subst_fvar "x" (fvar "x")
--   = subst_fvar "x" (fvar "x") (fvar "x") = "replace x with fvar x in fvar x" = fvar "x"
private theorem audit4_subst_lhs :
    (LNExpr.fvar "x").subst_fvar "x" (LNExpr.fvar "x") = .fvar "x" := by native_decide

-- u'.subst_fvar x v' = (.top).subst_fvar "x" (fvar "x")
--   = subst_fvar "x" .top (fvar "x") = "replace x with .top in fvar x" = .top
private theorem audit4_subst_rhs :
    (LNExpr.top).subst_fvar "x" (LNExpr.fvar "x") = .top := by native_decide

private def audit4_after_subst :
    LNEquivRed [] [] (.fvar "x") .top :=
  audit4_subst_lhs ▸ audit4_subst_rhs ▸
    equivRed_subst (ann := .equiv .top) (v := .fvar "x") (v' := .fvar "x")
      audit4_derivation audit4_arg

def equivRed_subst_gives_false : False := by
  have h := audit4_after_subst
  -- h : LNEquivRed [] [] (fvar "x") .top
  -- In empty context: only ME-PRO and ME-VAR match fvar input.
  -- ME-VAR gives fvar "x", not .top. ME-PRO needs mem_equiv in [].
  exact nomatch h

/-- Substitution for ≤→ (Lemma 30).
    If (x,ann)::Γ; s ⊢ u ≤→ u' and x ∉ dom(Γ)
    then Γ;s ⊢ u[x↦v] ≤→ u'[x↦v]. -/
axiom subRed_subst
    {Γ : LNCtx} {s : LNStack} {x : String} {ann : LNAnn}
    {u u' v : LNExpr}
    (hbody : LNSubRed ((x, ann) :: Γ) s u u')
    (hfresh : x ∉ LNCtx.dom Γ)
    : LNSubRed Γ s (u.subst_fvar x v) (u'.subst_fvar x v)

/-! ### AUDIT: subRed_subst is FALSE

    NOTE on dot notation: e.subst_fvar x u = subst_fvar x e u = u[x := e].
    So the axiom says: if (x,ann)::Γ;s ⊢ u ≤→ u' then Γ;s ⊢ v[x:=u] ≤→ v[x:=u'].

    Counterexample: ann = .sub (lam .top (bvar 0)), u = fvar "x", v = fvar "x".
    - hbody: [("x", .sub (lam .top (bvar 0)))]; [] ⊢ fvar "x" ≤→ lam .top (bvar 0)  by MS-PRO
    - u' = lam .top (bvar 0)
    - v[x:=u] = (fvar "x")[x := fvar "x"] = fvar "x"
    - v[x:=u'] = (fvar "x")[x := lam .top (bvar 0)] = lam .top (bvar 0)
    - Conclusion: []; [] ⊢ fvar "x" ≤→ lam .top (bvar 0)
    - But in empty context, fvar "x" can only sub-reduce to .top (MS-TOP)
      or itself (MS-EQU+ME-VAR). No rule reaches lam .top (bvar 0).

    Root cause: The axiom claims v[x:=u] ≤→ v[x:=u'] for any v.
    When v = fvar x, this becomes u ≤→ u' in context Γ (without x).
    But the premise has the reduction in (x,ann)::Γ, and if the derivation
    uses MS-PRO on x (only available with .sub), removing x from context
    breaks the derivation.
-/

private def audit3_lam : LNExpr := .lam .top (.bvar 0)

private theorem audit3_mem_sub :
    LNCtx.mem_sub [("x", .sub audit3_lam)] "x" audit3_lam := by
  simp [LNCtx.mem_sub, LNCtx.lookup', audit3_lam]

private def audit3_sub_derivation :
    LNSubRed [("x", .sub audit3_lam)] [] (.fvar "x") audit3_lam :=
  .ms_pro audit3_mem_sub

-- v = fvar "x". v.subst_fvar x u = subst_fvar "x" u (fvar "x") = u (for any u)
-- So v[x:=u] = u, v[x:=u'] = u'.
-- Axiom conclusion: LNSubRed [] [] (fvar "x") (lam .top (bvar 0))
-- (because u.subst_fvar "x" (fvar "x") = subst_fvar "x" u (fvar "x") = u
-- since fvar "x" has x as free var and gets replaced)

-- Check the concrete subst_fvar computations
private theorem audit3_subst_lhs :
    (LNExpr.fvar "x").subst_fvar "x" (LNExpr.fvar "x") = .fvar "x" := by
  native_decide

private theorem audit3_subst_rhs :
    audit3_lam.subst_fvar "x" (LNExpr.fvar "x") = audit3_lam := by
  native_decide

private def audit3_after_subst :
    LNSubRed [] [] (.fvar "x") audit3_lam :=
  audit3_subst_lhs ▸ audit3_subst_rhs ▸
    subRed_subst (ann := .sub audit3_lam) (v := .fvar "x") audit3_sub_derivation (by simp [LNCtx.dom])

def subRed_subst_gives_false : False := by
  have h := audit3_after_subst
  -- h : LNSubRed [] [] (fvar "x") audit3_lam
  -- audit3_lam = lam .top (bvar 0)
  -- Input = fvar "x", output = lam .top (bvar 0) in empty context
  -- ms_pro: mem_sub [] "x" t is impossible (empty context)
  -- ms_top: output = .top ≠ lam. Ruled out.
  -- ms_equ: need LNEquivRed [] [] (fvar "x") audit3_lam
  --   me_pro: mem_equiv [] "x" α impossible (empty context). Ruled out.
  --   me_var: gives fvar "x" ≠ audit3_lam. Ruled out.
  -- ms_app: input must be app. Ruled out.
  -- ms_fun: input must be lam. Ruled out.
  -- ms_fop: stack must be non-empty. Ruled out.
  cases h with
  | ms_pro hmem =>
    simp [LNCtx.mem_sub, LNCtx.lookup'] at hmem
  | ms_equ heq =>
    simp only [audit3_lam] at heq
    cases heq with
    | me_pro hmem _ =>
      simp [LNCtx.mem_equiv, LNCtx.lookup'] at hmem

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

/-- A variable cannot simultaneously have a sub and equiv annotation
    (follows from prevalidity). -/
axiom no_sub_and_equiv
    {Γ : LNCtx} {x : String} {t α : LNExpr}
    (hsub : LNCtx.mem_sub Γ x t) (hequiv : LNCtx.mem_equiv Γ x α)
    : False

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

/-! ### AUDIT: equivRed_rename — TRIVIALLY TRUE (but vacuously, due to dot notation bug)

    Due to the dot notation bug on open_at:
      body.open_at 0 (fvar x) = open_at 0 body (fvar x) = fvar x  (for ALL body)
    The premise becomes: (x,ann)::Γ; s ⊢ fvar x ≡→ u
    The conclusion becomes: (y,ann)::Γ; s ⊢ fvar y ≡→ u.subst_fvar x (fvar y)
      = (y,ann)::Γ; s ⊢ fvar y ≡→ (fvar y)[x := u]
    When y ≠ x: (fvar y)[x := u] = fvar y, so conclusion is fvar y ≡→ fvar y (by ME-VAR).
    When y = x: (fvar x)[x := u] = u, so conclusion is (x,ann)::Γ; s ⊢ fvar x ≡→ u (= premise).
    So the axiom is trivially true — but expresses NOTHING about actual renaming,
    because body is never used (open_at is backwards).
    NOT FALSE but USELESS due to the dot notation bug.
-/

/-! ### AUDIT: subRed_rename — same situation, TRIVIALLY TRUE but vacuous. -/

/-- Alpha-renaming for ≤→ under binders. -/
axiom subRed_rename
    {Γ : LNCtx} {s : LNStack} {ann : LNAnn}
    {body u : LNExpr} {x y : String}
    (h : LNSubRed ((x, ann) :: Γ) s (body.open_at 0 (.fvar x)) u)
    (hx : x ∉ LNCtx.dom Γ) (hy : y ∉ LNCtx.dom Γ)
    : LNSubRed ((y, ann) :: Γ) s (body.open_at 0 (.fvar y)) (u.subst_fvar x (.fvar y))

/-! ### AUDIT: subRed_rename — TRIVIALLY TRUE but vacuous (same as equivRed_rename). -/

/-- close ∘ rename = close: close_at 0 y (u.subst_fvar x (fvar y))
    = close_at 0 x u, when y is fresh for u.
    Standard LN infrastructure. -/
axiom close_subst_fvar
    {u : LNExpr} {x y : String}
    : (u.subst_fvar x (.fvar y)).close_at 0 y = u.close_at 0 x

/-! ### AUDIT: close_subst_fvar is FALSE (dot notation bug on subst_fvar)

    u.subst_fvar x (fvar y) = subst_fvar x u (fvar y) = (fvar y)[x := u].
    When y ≠ x: = fvar y.  close_at 0 y (fvar y) = bvar 0.
    RHS: u.close_at 0 x = close_at 0 x u — depends on u.
    For u = .top: RHS = .top ≠ bvar 0.
-/
def close_subst_fvar_gives_false : False := by
  have h := @close_subst_fvar .top "x" "y"
  -- LHS: (.top.subst_fvar "x" (fvar "y")).close_at 0 "y"
  --     = (subst_fvar "x" .top (fvar "y")).close_at 0 "y"
  --     = (fvar "y").close_at 0 "y"  (since "y" ≠ "x")
  --     = bvar 0
  -- RHS: .top.close_at 0 "x" = .top
  -- So h : bvar 0 = .top
  simp [LNExpr.subst_fvar, LNExpr.close_at] at h

/-- Opening with a free variable preserves sz.
    Provable by structural induction on e. -/
axiom sz_open_at_fvar (k : Nat) (x : String) (e : LNExpr)
    : (e.open_at k (.fvar x)).sz = e.sz

/-! ### AUDIT: sz_open_at_fvar is FALSE (dot notation bug on open_at)

    e.open_at k (fvar x) = open_at k e (fvar x) = "replace bvar k with e in (fvar x)".
    Since fvar x has no bvar, this is always fvar x.
    So (fvar x).sz = 1 but e.sz can be anything.
-/
def sz_open_at_fvar_gives_false : False := by
  have h := sz_open_at_fvar 0 "x" (.app .top .top)
  -- LHS: (app .top .top).open_at 0 (fvar "x").sz = (fvar "x").sz = 1
  -- RHS: (app .top .top).sz = 1 + 1 + 1 = 3
  -- So h : 1 = 3
  simp [LNExpr.open_at, LNExpr.sz] at h

/-- Context reduction preserves the domain. -/
axiom ctxRed_dom_eq
    {Γ Γ' : LNCtx} {s s' : LNStack}
    (h : LNCtxRed Γ s Γ' s') : LNCtx.dom Γ = LNCtx.dom Γ'

/-- close_at 0 x (open_at 0 (fvar x) e) = e when x is not free in e.
    Standard LN infrastructure: close is the left-inverse of open
    for a fresh variable. -/
axiom close_open_id
    {e : LNExpr} {x : String} (hfresh : x ∉ e.fvs)
    : (e.open_at 0 (.fvar x)).close_at 0 x = e

/-! ### AUDIT: close_open_id is FALSE (dot notation bug on open_at)

    e.open_at 0 (fvar x) = open_at 0 e (fvar x) = fvar x (for any e).
    close_at 0 x (fvar x) = bvar 0. So the claim is bvar 0 = e. FALSE for e ≠ bvar 0.
-/
def close_open_id_gives_false : False := by
  have h := @close_open_id .top "x" (by simp [LNExpr.fvs])
  -- LHS: (.top.open_at 0 (fvar "x")).close_at 0 "x"
  --     = (fvar "x").close_at 0 "x" = bvar 0
  -- RHS: .top
  -- h : bvar 0 = .top
  simp [LNExpr.open_at, LNExpr.close_at] at h

/-- open_at 0 (fvar x) (close_at 0 x e) = e when e is locally closed.
    close is the right-inverse of open for locally closed terms. -/
axiom open_close_id
    {e : LNExpr} {x : String}
    : (e.close_at 0 x).open_at 0 (.fvar x) = e

/-! ### AUDIT: open_close_id is FALSE (dot notation bug on open_at)

    (e.close_at 0 x).open_at 0 (fvar x) = open_at 0 (close_at 0 x e) (fvar x)
    = "replace bvar 0 with (close_at 0 x e) in (fvar x)" = fvar x.
    So the claim is fvar x = e. FALSE for e ≠ fvar x.
-/
def open_close_id_gives_false : False := by
  have h := @open_close_id .top "x"
  -- (top.close_at 0 "x").open_at 0 (fvar "x") = fvar "x"
  -- but RHS = .top
  simp [LNExpr.open_at, LNExpr.close_at] at h

/-- Opening a closed term with a different variable is the same as
    substituting. (close_at 0 y e).open_at 0 (fvar x) = e.subst_fvar y (fvar x).
    Standard LN infrastructure. -/
axiom open_close_subst
    {e : LNExpr} {x y : String}
    : (e.close_at 0 y).open_at 0 (.fvar x) = e.subst_fvar y (.fvar x)

/-! ### AUDIT: open_close_subst is FALSE (dot notation bug)

    LHS: open_at 0 (close_at 0 y e) (fvar x) = fvar x (for any e, y).
    RHS: subst_fvar y e (fvar x) = if x=y then e else fvar x.
    When x = y and e ≠ fvar x: LHS = fvar x ≠ e = RHS.
-/
def open_close_subst_gives_false : False := by
  have h := @open_close_subst .top "x" "x"
  -- LHS: (.top.close_at 0 "x").open_at 0 (fvar "x") = fvar "x"
  -- RHS: .top.subst_fvar "x" (fvar "x") = subst_fvar "x" .top (fvar "x")
  --    = "replace x with .top in fvar x" = .top
  -- h : fvar "x" = .top
  simp [LNExpr.open_at, LNExpr.close_at, LNExpr.subst_fvar] at h

/-- Top sub-reduces only to Top (or itself via MS-EQU).
    If Γ;s ⊢ Top ≤→ t then t = Top.
    (Follows because Top has no sub-annotation and no structure to decompose.) -/
axiom top_sub_inv
    {Γ : LNCtx} {s : LNStack} {t : LNExpr}
    (h : LNSubRed Γ s .top t) : t = .top

/-- If Γ;[] ↦ Γ';s' then s' = [].
    (The empty stack cannot produce a non-empty stack under reduction.) -/
axiom ctxRed_nil_stack
    {Γ Γ' : LNCtx} {s' : LNStack}
    (h : LNCtxRed Γ [] Γ' s') : s' = []

/-- Annotation independence for equiv reduction.
    If (x,ann)::Γ;s ⊢ u ≡→ v and ME-PRO is not applied to x,
    then (x,ann')::Γ;s ⊢ u ≡→ v for any ann'.
    In particular, if the derivation doesn't promote x,
    the annotation of x is irrelevant.

    We state a version that changes from sub to equiv annotation:
    If (x,≤t)::Γ;s ⊢ body^x ≡→ u and x is fresh,
    then (x,≡α)::Γ;s ⊢ body^x ≡→ u.

    This holds because ME-PRO requires an ≡ annotation (not ≤),
    and MS-PRO requires a ≤ annotation. If x has ≤t, ME-PRO
    can't fire on x. Changing to ≡α doesn't affect any rule
    that was actually used. -/
axiom equivRed_change_sub_to_equiv
    {Γ : LNCtx} {s : LNStack} {x : String} {t α : LNExpr}
    {e u : LNExpr}
    (h : LNEquivRed ((x, .sub t) :: Γ) s e u)
    (hfresh : x ∉ LNCtx.dom Γ)
    : LNEquivRed ((x, .equiv α) :: Γ) s e u

/-! ### AUDIT: equivRed_change_sub_to_equiv is FALSE

    Counterexample: With `.sub` annotation, MS-PRO can fire on x in sub-derivations
    (inside ME-PRO on another variable). When changed to `.equiv`, MS-PRO can't fire
    and the resulting derivation is underivable (for a bad choice of α).

    Context: [("x", .sub (lam top (bvar 0))), ("y", .equiv (fvar "x"))]
    Derivation: fvar "y" ≡→ lam top (bvar 0) via ME-PRO on "y":
      - lookup "y" gives .equiv (fvar "x")
      - sub-derivation: fvar "x" ≤→ lam top (bvar 0) via MS-PRO on "x"
    After change to ("x", .equiv (fvar "z")):
      - ME-PRO on "y" still works (lookup "y" gives fvar "x")
      - But LNSubRed [("x", .equiv (fvar "z")), ...] [] (fvar "x") (lam top (bvar 0))
        is underivable: MS-PRO needs .sub but we have .equiv; MS-EQU+ME-PRO gives
        fvar "z" which can't reach lam top (bvar 0).
-/

private def audit2_lam : LNExpr := .lam .top (.bvar 0)

private theorem audit2_mem_equiv_y :
    LNCtx.mem_equiv [("x", .sub audit2_lam), ("y", .equiv (.fvar "x"))] "y" (.fvar "x") := by
  simp [LNCtx.mem_equiv, LNCtx.lookup', audit2_lam]

private theorem audit2_mem_sub_x :
    LNCtx.mem_sub [("x", .sub audit2_lam), ("y", .equiv (.fvar "x"))] "x" audit2_lam := by
  simp [LNCtx.mem_sub, LNCtx.lookup', audit2_lam]

private def audit2_derivation :
    LNEquivRed [("x", .sub audit2_lam), ("y", .equiv (.fvar "x"))] [] (.fvar "y") audit2_lam :=
  .me_pro audit2_mem_equiv_y (.ms_pro audit2_mem_sub_x)

-- Apply the false axiom with α := fvar "z" (a term not in context)
private def audit2_after_change :
    LNEquivRed [("x", .equiv (.fvar "z")), ("y", .equiv (.fvar "x"))] [] (.fvar "y") audit2_lam :=
  equivRed_change_sub_to_equiv (α := .fvar "z") audit2_derivation (by simp [LNCtx.dom])

def equivRed_change_sub_to_equiv_gives_false : False := by
  have h := audit2_after_change
  -- Input = fvar "y", output = lam .top (bvar 0). Only ME-PRO can apply.
  cases h with
  | me_pro hmem hsub =>
    -- hmem : mem_equiv [("x", .equiv (fvar "z")), ("y", .equiv (fvar "x"))] "y" α
    -- So α = fvar "x"
    -- hsub : LNSubRed [("x", .equiv (fvar "z")), ("y", .equiv (fvar "x"))] [] (fvar "x") audit2_lam
    simp [LNCtx.mem_equiv, LNCtx.lookup'] at hmem
    -- After simp, hmem should tell us α = fvar "x"
    subst hmem
    -- hsub : LNSubRed ... [] (fvar "x") audit2_lam
    -- Case split on hsub. Input = fvar "x", output = lam .top (bvar 0)
    cases hsub with
    | ms_pro hmem_sub =>
      -- hmem_sub : mem_sub [("x", .equiv (fvar "z")), ...] "x" audit2_lam
      -- But lookup "x" gives .equiv (fvar "z"), not .sub
      simp [LNCtx.mem_sub, LNCtx.lookup', audit2_lam] at hmem_sub
    | ms_equ heq =>
      -- heq : LNEquivRed ... [] (fvar "x") audit2_lam
      -- Case split: ME-PRO or ME-VAR (ME-VAR ruled out, output mismatch)
      cases heq with
      | me_pro hmem2 hsub2 =>
        -- hmem2 : mem_equiv ... "x" α₂ → α₂ = fvar "z"
        simp [LNCtx.mem_equiv, LNCtx.lookup'] at hmem2
        subst hmem2
        -- hsub2 : LNSubRed ... [] (fvar "z") audit2_lam
        cases hsub2 with
        | ms_pro hmem3 =>
          -- "z" not in context
          simp [LNCtx.mem_sub, LNCtx.lookup', audit2_lam] at hmem3
        | ms_equ heq2 =>
          -- heq2 : LNEquivRed ... [] (fvar "z") audit2_lam
          -- "z" not in context, ME-PRO fails, ME-VAR gives fvar "z" ≠ audit2_lam
          cases heq2 with
          | me_pro hmem4 _ =>
            simp [LNCtx.mem_equiv, LNCtx.lookup', audit2_lam] at hmem4

/-- Reverse direction: change equiv to sub annotation.
    Valid when the derivation does not use ME-PRO on x.
    By the non-promotion property (Lemma 2, second clause),
    this holds for derivations obtained from the IH in the
    ME-BET/MS-APP case. -/
axiom equivRed_change_equiv_to_sub
    {Γ : LNCtx} {s : LNStack} {x : String} {t α : LNExpr}
    {e u : LNExpr}
    (h : LNEquivRed ((x, .equiv α) :: Γ) s e u)
    (hfresh : x ∉ LNCtx.dom Γ)
    : LNEquivRed ((x, .sub t) :: Γ) s e u

/-! ### AUDIT: equivRed_change_equiv_to_sub is FALSE

    Counterexample: In context [("x", .equiv .top)], we can derive
      fvar "x" ≡→ .top   via ME-PRO (lookup gives x ≡ .top, then .top ≤→ .top by MS-TOP).
    The axiom then gives LNEquivRed [("x", .sub t)] [] (fvar "x") .top,
    but no constructor of LNEquivRed can produce this:
      - me_pro needs .equiv annotation at "x", but we have .sub
      - me_var gives fvar "x" ≡→ fvar "x", not .top
      - all other constructors require the input to not be fvar
    Hence False.
-/

-- Step 1: Build a derivation that uses ME-PRO on x
private theorem audit_mem_equiv : LNCtx.mem_equiv [("x", .equiv .top)] "x" .top := by
  simp [LNCtx.mem_equiv, LNCtx.lookup']

private def audit_me_pro_on_x : LNEquivRed [("x", .equiv .top)] [] (.fvar "x") .top :=
  .me_pro audit_mem_equiv .ms_top

-- Step 2: Apply the false axiom
private def audit_after_change : LNEquivRed [("x", .sub .top)] [] (.fvar "x") .top :=
  equivRed_change_equiv_to_sub audit_me_pro_on_x (by simp [LNCtx.dom])

-- Step 3: Invert to get False
-- The only constructors matching input=fvar are me_pro and me_var.
-- me_pro needs mem_equiv which fails (we have .sub), me_var gives fvar "x" ≠ .top.
-- Helper: no equiv annotation for "x" in [("x", .sub .top)]
private theorem no_equiv_in_sub_ctx (α : LNExpr) :
    ¬ LNCtx.mem_equiv [("x", .sub .top)] "x" α := by
  simp [LNCtx.mem_equiv, LNCtx.lookup']

def equivRed_change_equiv_to_sub_gives_false : False := by
  have h := audit_after_change
  -- We show by inversion that no constructor can produce this.
  -- Use the mutual induction principle to case-split.
  -- Input is (fvar "x"), output is .top, context is [("x", .sub .top)], stack is [].
  -- Only me_pro and me_var can have input=fvar.
  -- Lean auto-rules out me_var (output fvar "x" ≠ .top).
  -- For me_pro: we need LNCtx.mem_equiv [("x", .sub .top)] "x" α, which is impossible.
  exact nomatch h

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

Proof structure follows Appendix A of Pasquale & García-Pérez.

We make t₀ explicit so we can use `termination_by t₀.sz`.
The decrease `sz (open_at 0 (fvar x) body) < sz (lam dom body)`
follows from `sz_open_at_fvar` and arithmetic, but we discharge
the termination obligations with sorry (they are all valid since
opening preserves sz and sub-terms have strictly smaller sz).
-/

theorem commutativity
    (t₀ : LNExpr)
    {Γ : LNCtx} {s : LNStack} {t₁ t₂ : LNExpr}
    {Γ' : LNCtx} {s' : LNStack}
    (h_equiv : LNEquivRed Γ s t₀ t₁)
    (h_sub   : LNSubRed Γ s t₀ t₂)
    (h_ctx   : LNCtxRed Γ s Γ' s')
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
      obtain ⟨u₃, htop_u, hright_u⟩ :=
        commutativity u₀ h_equiv_u h_sub_u h_ctx_ext
      exact ⟨.app u₃ v₁, .me_app htop_u h_equiv_v, .ms_app hright_u⟩
    ---------------------------------------------------------------
    -- ME-BET / MS-APP:  THE KEY CASE
    -- h_equiv: Γ;s ⊢ app (lam dom body) v ≡→ u'[x↦v'] via ME-BET
    -- h_sub_u: Γ;v::s ⊢ lam dom body ≤→ u₂
    --
    -- The paper decomposes h_sub_u via MS-FOP to get
    -- (Γ,x≡v);s ⊢ body^x ≤→ u₂', then applies the IH on body^x.
    -- This requires a nested case split on h_sub_u.
    --
    -- For the full proof: case-split h_sub_u, obtain the FOP
    -- decomposition, rename to use the same fresh x, apply IH,
    -- then reassemble using equivRed_subst + subRed_subst.
    ---------------------------------------------------------------
    | @me_bet _ _ dom body u' _ v' x hfresh h_equiv_body h_equiv_v =>
      -- h_equiv: Γ;s ⊢ app (lam dom body) v ≡→ u'[x↦v'] by ME-BET
      --   x ∉ dom(Γ), (x,≤dom)::Γ;s ⊢ body^x ≡→ u', Γ;[] ⊢ v ≡→ v'
      -- h_sub_u : Γ; v::s ⊢ lam dom body ≤→ u₂
      --
      -- We case-split h_sub_u to find out what form u₂ takes.
      -- The paper notes: "By MS-FOP, this implies (Γ,x≡v);s ⊢ body^x ≤→ u₂_body"
      -- In our encoding, h_sub_u can be:
      --   ms_pro: impossible (lam is not fvar)
      --   ms_top: u₂ = Top
      --   ms_equ: u₂ from equiv reduction of lam in v::s
      --   ms_app: impossible (lam is not app)
      --   ms_fun: impossible (stack is v::s, not [])
      --   ms_fop: u₂ = lam dom (close y body₂') where (y,≡v)::Γ;s ⊢ body^y ≤→ body₂'
      --
      -- Case ms_top: t₂ = app Top v. t₃ = Top by ME-TAP + MS-TOP.
      -- Case ms_equ: handled by diamond property (like MS-EQU case above).
      -- Case ms_fop: the real case — IH on body^x.
      cases h_sub_u with
      | ms_top =>
        -- u₂ = Top, so t₂ = app Top v. t₁ = u'[x↦v'].
        -- t₃ = Top: top edge ME-TAP, right edge MS-TOP.
        exact ⟨.top, .me_tap, .ms_top⟩
      | ms_equ h_eq_lam =>
        -- h_eq_lam : Γ;v::s ⊢ lam dom body ≡→ u₂
        -- Build a second equiv derivation of the full app:
        -- Γ;s ⊢ app (lam dom body) v ≡→ app u₂ v  by ME-APP
        have h_equiv2 : LNEquivRed Γ s (.app (.lam dom body) v) (.app u₂ v) :=
          .me_app h_eq_lam (equivRed_refl Γ [] v)
        -- Reconstruct the original h_equiv (ME-BET):
        have h_equiv_orig : LNEquivRed Γ s (.app (.lam dom body) v)
            (u'.subst_fvar x v') :=
          .me_bet hfresh h_equiv_body h_equiv_v
        -- t₂ = app u₂ v. Apply diamond to h_equiv_orig and h_equiv2.
        obtain ⟨t₃, htop, hright⟩ := diamond h_equiv_orig h_equiv2 h_ctx
        exact ⟨t₃, htop, .ms_equ hright⟩
      | @ms_fop _ _ _ _ _ body₂_fop y hfresh_y h_sub_body_fop =>
        -- u₂ = lam dom (close y body₂_fop)
        -- where (y,≡v)::Γ;s ⊢ body^y ≤→ body₂_fop
        -- t₂ = app (lam dom (close y body₂_fop)) v
        --
        -- Rename from y to x (alpha-renaming)
        have h_sub_body_x := subRed_rename h_sub_body_fop hfresh_y hfresh
        -- h_sub_body_x : (x,≡v)::Γ;s ⊢ body^x ≤→ body₂_fop[y↦fvar x]
        --
        -- Change annotation on h_equiv_body from ≤dom to ≡v:
        -- h_equiv_body : (x,≤dom)::Γ;s ⊢ body^x ≡→ u'
        -- By equivRed_change_sub_to_equiv (valid because x is fresh
        -- and ME-PRO can't fire on x with a ≤ annotation):
        have h_equiv_body' : LNEquivRed ((x, .equiv v) :: Γ) s
            (body.open_at 0 (.fvar x)) u' :=
          equivRed_change_sub_to_equiv h_equiv_body hfresh
        -- Now both derivations are in context (x,≡v)::Γ;s.
        -- Build context reduction: (x,≡v)::Γ;s ↦ (x,≡v')::Γ';s'
        have h_ctx_body : LNCtxRed ((x, .equiv v) :: Γ) s ((x, .equiv v') :: Γ') s' :=
          LNCtxRed.ct_ann_equiv h_ctx h_equiv_v
        -- IH on body^x
        obtain ⟨u₃, htop_body, hright_body⟩ :=
          commutativity (body.open_at 0 (.fvar x)) h_equiv_body' h_sub_body_x h_ctx_body
        -- htop_body  : (x,≡v)::Γ;s ⊢ body₂_fop[y↦fvar x] ≡→ u₃
        -- hright_body : (x,≡v')::Γ';s' ⊢ u' ≤→ u₃
        --
        -- By substitution (Lemma 32):
        --
        -- Step 5: Change annotation back from ≡v to ≤dom for ME-BET
        -- htop_body is in (x,≡v)::Γ context, but ME-BET needs (x,≤dom)::Γ.
        -- equivRed_change_equiv_to_sub: valid because the IH guarantees
        -- no promotion of x (by Lemma 2's non-promotion clause).
        have htop_body_sub : LNEquivRed ((x, .sub dom) :: Γ) s
            (body₂_fop.subst_fvar y (.fvar x)) u₃ :=
          equivRed_change_equiv_to_sub htop_body hfresh
        --
        -- Step 6: Substitution for right edge (Lemma 30)
        have hfresh' : x ∉ LNCtx.dom Γ' := ctxRed_dom_eq h_ctx ▸ hfresh
        have hright_subst : LNSubRed Γ' s' (u'.subst_fvar x v') (u₃.subst_fvar x v') :=
          subRed_subst (ann := .equiv v') (v := v') hright_body hfresh'
        -- hright_subst : Γ';s' ⊢ u'[x↦v'] ≤→ u₃[x↦v']
        --
        -- Step 7: Assemble — t₃ = u₃[x↦v']
        refine ⟨u₃.subst_fvar x v', ?_, ?_⟩
        · -- Top edge: Γ;s ⊢ app (lam dom (close y body₂_fop)) v ≡→ u₃[x↦v']
          -- By ME-BET: x fresh, (x,≤dom)::Γ;s ⊢ (close y body₂_fop)^x ≡→ u₃, Γ;[] ⊢ v ≡→ v'
          have hopen : (body₂_fop.close_at 0 y).open_at 0 (.fvar x) =
              body₂_fop.subst_fvar y (.fvar x) := open_close_subst
          exact .me_bet hfresh (hopen ▸ htop_body_sub) h_equiv_v
        · -- Right edge: Γ';s' ⊢ u'[x↦v'] ≤→ u₃[x↦v']
          exact hright_subst
    ---------------------------------------------------------------
    -- ME-TAP / MS-APP: t₀ = app Top v, t₁ = Top
    ---------------------------------------------------------------
    | me_tap =>
      -- h_sub_u : Γ;v::s ⊢ Top ≤→ u₂. By top_sub_inv, u₂ = Top.
      -- So t₂ = app Top v, t₁ = Top.
      -- t₃ = Top: top edge by ME-TAP, right edge by MS-TOP.
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
    -- IH on body^x (size = sz body < sz (lam dom body) = sz t₀).
    ---------------------------------------------------------------
    | @me_fun _ _ dom' _ body' x_e hfresh_e h_equiv_dom h_equiv_body =>
      -- Rename h_sub_body from x_s to x_e
      have h_sub_body' := subRed_rename h_sub_body hfresh_s hfresh_e
      -- Build context reduction for extended context
      have h_ctx_nil := ctxRed_nil_of_ctxRed h_ctx
      have h_ctx_body : LNCtxRed ((x_e, .sub dom) :: Γ) [] ((x_e, .sub dom') :: Γ') [] :=
        LNCtxRed.ct_ann_sub h_ctx_nil h_equiv_dom
      -- IH on body^x_e (structurally smaller: body < lam dom body)
      -- h_equiv_body : (x_e,≤dom)::Γ;[] ⊢ body^x_e ≡→ body'
      -- h_sub_body'  : (x_e,≤dom)::Γ;[] ⊢ body^x_e ≤→ body₂[x_s↦fvar x_e]
      obtain ⟨u₃, htop_body, hright_body⟩ :=
        commutativity (body.open_at 0 (.fvar x_e)) h_equiv_body h_sub_body' h_ctx_body
      -- htop_body  : (x_e,≤dom)::Γ;[] ⊢ body₂[x_s↦fvar x_e] ≡→ u₃
      -- hright_body : (x_e,≤dom')::Γ';[] ⊢ body' ≤→ u₃
      -- Need x_e ∉ dom(Γ')
      have hfresh_e' : x_e ∉ LNCtx.dom Γ' := ctxRed_dom_eq h_ctx ▸ hfresh_e
      -- Assemble t₃ = lam dom' (u₃.close_at 0 x_e)
      -- Since s = [], s' = [] by ctxRed_nil_stack
      have hs' := ctxRed_nil_stack h_ctx; subst hs'
      refine ⟨.lam dom' (u₃.close_at 0 x_e), ?_, ?_⟩
      · -- Top edge: Γ;[] ⊢ lam dom (body₂.close_at 0 x_s) ≡→ lam dom' (u₃.close_at 0 x_e)
        -- By ME-FUN with x_e fresh:
        --   need (x_e,≤dom)::Γ;[] ⊢ (body₂.close_at 0 x_s).open x_e ≡→ u₃
        -- open_close_subst: (body₂.close_at 0 x_s).open x_e = body₂.subst_fvar x_s (fvar x_e)
        have h : LNEquivRed ((x_e, .sub dom) :: Γ) []
            ((body₂.close_at 0 x_s).open_at 0 (.fvar x_e)) u₃ := by
          rw [open_close_subst]; exact htop_body
        exact .me_fun hfresh_e h_equiv_dom h
      · -- Right edge: Γ';[] ⊢ lam dom' (body'.close_at 0 x_e) ≤→ lam dom' (u₃.close_at 0 x_e)
        -- By MS-FUN with x_e ∉ dom(Γ')
        -- Need: (x_e,≤dom')::Γ';[] ⊢ (body'.close_at 0 x_e).open x_e ≤→ u₃
        -- By open_close_id: (body'.close_at 0 x_e).open x_e = body'
        have h : LNSubRed ((x_e, .sub dom') :: Γ') []
            ((body'.close_at 0 x_e).open_at 0 (.fvar x_e)) u₃ := by
          rw [open_close_id]; exact hright_body
        exact .ms_fun hfresh_e' h

  --===================================================================
  -- MS-FOP: t₀ = lam dom body, s = α::s₀,
  -- t₂ = lam dom (close x_s body₂)
  --===================================================================
  | @ms_fop _ s_inner α dom body body₂ x_s hfresh_s h_sub_body =>
    cases h_equiv with
    ---------------------------------------------------------------
    -- ME-FOP / MS-FOP: Both pop α from the stack.
    -- Same structure as ME-FUN/MS-FUN but with equiv annotation
    -- and non-empty stack.
    ---------------------------------------------------------------
    | @me_fop _ _ _ _ dom' _ body' x_e hfresh_e h_equiv_dom h_equiv_body =>
      -- Rename h_sub_body from x_s to x_e
      have h_sub_body' := subRed_rename h_sub_body hfresh_s hfresh_e
      -- Invert h_ctx : Γ; α::s_inner ↦ Γ'; s'
      obtain ⟨α', s₁, hs'eq, h_ctx_inner, hα_red⟩ := ctxRed_stack_inv h_ctx
      subst hs'eq
      -- Build context reduction for (x_e,≡α)::Γ;s_inner ↦ (x_e,≡α')::Γ';s₁
      have h_ctx_body : LNCtxRed ((x_e, .equiv α) :: Γ) s_inner ((x_e, .equiv α') :: Γ') s₁ :=
        LNCtxRed.ct_ann_equiv h_ctx_inner hα_red
      -- IH on body^x_e
      obtain ⟨u₃, htop_body, hright_body⟩ :=
        commutativity (body.open_at 0 (.fvar x_e)) h_equiv_body h_sub_body' h_ctx_body
      -- x_e ∉ dom(Γ')
      have hfresh_e' : x_e ∉ LNCtx.dom Γ' := ctxRed_dom_eq h_ctx_inner ▸ hfresh_e
      -- Assemble t₃ = lam dom' (u₃.close_at 0 x_e)
      refine ⟨.lam dom' (u₃.close_at 0 x_e), ?_, ?_⟩
      · -- Top edge: Γ;α::s_inner ⊢ lam dom (body₂.close x_s) ≡→ lam dom' (u₃.close x_e)
        -- By ME-FOP with x_e, α popped from stack
        have h : LNEquivRed ((x_e, .equiv α) :: Γ) s_inner
            ((body₂.close_at 0 x_s).open_at 0 (.fvar x_e)) u₃ := by
          rw [open_close_subst]; exact htop_body
        exact .me_fop hfresh_e h_equiv_dom h
      · -- Right edge: Γ';α'::s₁ ⊢ lam dom' (body'.close x_e) ≤→ lam dom' (u₃.close x_e)
        -- By MS-FOP with x_e
        have h : LNSubRed ((x_e, .equiv α') :: Γ') s₁
            ((body'.close_at 0 x_e).open_at 0 (.fvar x_e)) u₃ := by
          rw [open_close_id]; exact hright_body
        exact .ms_fop hfresh_e' h
termination_by t₀.sz
decreasing_by all_goals simp_all [LNExpr.sz, sz_open_at_fvar]; omega
