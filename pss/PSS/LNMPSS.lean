/-!
# Machine-Based Pure Subtype Systems (MPSS) — Locally Nameless Encoding

Mechanisation of the MPSS calculus from:
  Pasquale & Garcia-Perez, "Towards the type safety of Pure Subtype Systems
  (Full version)", CSL 2026.

This file encodes MPSS using the **locally nameless** representation:
  - Bound variables: de Bruijn indices (for lambda-bound vars)
  - Free variables: names (String atoms) — no shifting needed under binders

## Cofinite Quantification

Binder rules (ME-BET, ME-FUN, ME-FOP, MS-FUN, MS-FOP) and the corresponding
noPromoAt rules use **cofinite quantification**: instead of picking a specific
fresh variable `x ∉ dom(Γ)`, the premise is `∀ x, x ∉ L → P(x)` for a finite
avoidance set `L : List String`. The key advantage: when doing mutual induction,
we can pick `x` fresh for *anything* (not just the context), breaking the
circular dependency between weakening, renaming, and substitution proofs.

The result terms of binder rules use `body'.open_at 0 (.fvar x)` in premises
and `body'` (a term with `bvar 0`) in conclusions, eliminating explicit
`close_at` from the rule conclusions.

## Contents
- LNExpr: locally nameless terms
- open_at / close_at / subst_fvar: opening, closing, substitution
- LNAnn, LNCtx, LNStack: annotations, contexts, stacks
- LNEquivRed: equivalence reduction (Figure 2, top half)
- LNSubRed: subtyping reduction (Figure 2, bottom half)
- LNCtxRed: context reduction (Section 3)
- noPromoAt: non-promotion predicates for annotation swap axioms
- diamond_full / diamond: Lemma 2, the diamond property for ≡→
- commutativity: Lemma 1, the main theorem

## Sorrys
Several kinds of `sorry` remain:
1. CLOSED: `y ∉ dom Γ_inner` freshness witnesses in ctxRed_lookup_sub,
   ctxRed_lookup_equiv, and ctxRed_stack_inv now discharged by adding
   a `(LNCtx.dom Γ).Nodup` hypothesis. Commutativity also takes this
   hypothesis and propagates it to recursive calls via List.nodup_cons.
2. CLOSED: `noPromoAt_equiv_swap` and `noPromoAt_sub_swap` are now fully
   proved using the mutual recursor @LNEquivRed.noPromoAt.rec, with cofinite
   binder cases handled by augmenting avoidance sets with x to ensure y ≠ x.
3. `diamond_full`: sorry'd pending adaptation to cofinite constructor patterns.
   The proof strategy is the same as before (pick common fresh x from
   intersection of avoidance sets) but needs rewriting.
4. `diamond` (wf witnesses for ctxRed_refl): these would be discharged by
   proving that reduction preserves local closure.
5. `u₃.lc` witnesses in commutativity: the IH yields a term u₃ and we need
   it to be locally closed for `open_close_subst`. Would be discharged by
   proving that reduction preserves local closure (mutual induction).
6. `x ∉ t_e.fvs` in commutativity's ME-BET/MS-FOP case: x is chosen fresh
   from avoidance sets, but we also need it fresh for t_e (a binder body).
   This follows from including t_e.fvs in the avoidance set.
7. Stack extension for annotation terms in commutativity's MS-PRO/ME-VAR case:
   `ctxRed_lookup_sub` gives `LNEquivRed Γ [] t t'` (empty stack) but the top
   edge needs `LNEquivRed Γ s t t'` (current stack). This holds for well-formed
   contexts (annotation terms are stack-stable) but requires formalizing
   context well-formedness. Replaces the former FALSE axiom `equivRed_stack_ext`.

## Proved Lemmas
- `equivRed_ctx_mono` / `subRed_ctx_mono`: context monotonicity — if every
  lookup in Γ is preserved in Γ', then any reduction in Γ holds in Γ'. Proved
  by mutual induction using the combined recursor; the cofinite binder cases
  pass through directly via `LNCtx.sub_cons`.
- `equivRed_ctx_ext` / `subRed_ctx_ext`: structural context extension — if
  x ∉ dom(Γ), adding (x,ann) preserves reductions. Derived from ctx_mono.
- `equivRed_rename` / `subRed_rename`: alpha-renaming under binders — if
  (x,ann)::Γ; s ⊢ body^x ≡→ u (resp. ≤→), then (y,ann)::Γ; s ⊢ body^y ≡→
  u[x↦fvar y]. Proved by combining ctx_mono + equivRed_subst (resp. subRed_subst).
  Requires x ∉ fvs(body), which holds at all call sites since x is chosen fresh.
- `noPromoAt_equiv_swap` / `noPromoAt_sub_swap`: annotation swap under
  non-promotion — if a derivation doesn't promote x, changing x's annotation
  in the context preserves the derivation. Proved by mutual induction using
  @LNEquivRed.noPromoAt.rec, with cofinite binder cases handled by
  augmenting avoidance sets with x. Enables `equivRed_change_sub_to_equiv`
  and `equivRed_change_equiv_to_sub` (previously depended on sorry'd swaps).
- `ctxRed_lookup_sub` / `ctxRed_lookup_equiv` / `ctxRed_stack_inv`:
  context lookup and stack inversion through context reduction. Now fully
  proved by adding a `(LNCtx.dom Γ).Nodup` hypothesis (no-shadowing),
  which provides `y ∉ dom Γ_i` at each inductive step.

## Remaining Axioms
None. All former axioms have been removed:
- **stack_ext**: REMOVED (FALSE). Former axioms `equivRed_stack_ext` /
  `subRed_stack_ext` — counterexample at end of file. The commutativity
  MS-PRO case now sorry's a restricted form inline (annotation terms are
  stack-stable under well-formed contexts, but this invariant is not
  formally tracked).
- **weaken**: REMOVED (FALSE). Former axioms `equivRed_weaken` /
  `subRed_weaken` — counterexample at end of file. CtxRed can reduce
  annotations more than the original derivation did, making the original
  output unreachable in the reduced context. The MS-PRO/ME-VAR case now
  uses `equivRed_ctx_ext` (context extension) plus restricted stack
  extension (sorry'd) instead.
- **noPromoAt**: REMOVED (FALSE). The former axioms `me_bet_body_noPromoAt`
  and `commutativity_noPromoAt` were FALSE as standalone statements (formal
  counterexamples preserved in the file). The correct formulation co-proves
  noPromoAt preservation with commutativity: the strengthened return type
  includes `∀ x, LNSubRed.noPromoAt x Γ s t₀ t₂ → LNSubRed.noPromoAt x Γ' s' t₁ t₃`.
  The ME-BET/MS-FOP case now sorry's the annotation swaps inline, to be
  resolved as part of the full mutual induction.

## Sorry'd Theorems (formerly axioms)
- `equivRed_subst` / `subRed_subst`: converted from axioms to sorry'd theorems.
  Full proof requires mutual induction on derivation structure. Key blockers:
  (1) ME-APP case: the stack parameter in the conclusion is not substituted,
      but the me_app constructor pushes an operand onto the stack that DOES
      need substitution. Requires a strengthened motive that substitutes
      stack elements, then a final step showing s.map (subst x v) = s
      when x does not appear free in stack elements (well-formedness).
  (2) Cofinite body cases (ME-BET/ME-FUN/MS-FUN): the body premise has
      context (y,ann_y)::(x,ann)::G where x is not at the head. The recursor
      IH can only peel the head binding. Requires context permutation
      (ctx_swap_sub_ctx, now proved) plus annotation well-formedness
      (dom.subst x v = dom when x not free in dom).
  (3) ME-PRO/MS-PRO cases: need x not free in annotation terms from the
      context (well-formedness invariant not formally tracked).
  Infrastructure lemmas proved toward this: subst_open_at_gen, open_subst_comm,
  ctx_swap_sub_ctx.
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

/-- Free variables of an annotation. -/
def LNAnn.fvs : LNAnn → List String
  | .sub t => t.fvs
  | .equiv α => α.fvs

/-- All free variables in a context: both keys and annotation free variables. -/
def LNCtx.all_fvs (Γ : LNCtx) : List String :=
  Γ.flatMap (fun (x, ann) => x :: ann.fvs)

/-- Context domain is a subset of all_fvs: every key appears in all_fvs. -/
theorem LNCtx.mem_all_fvs_of_mem_dom {Γ : LNCtx} {x : String}
    (h : x ∈ LNCtx.dom Γ) : x ∈ LNCtx.all_fvs Γ := by
  simp only [LNCtx.dom, LNCtx.all_fvs] at *
  induction Γ with
  | nil => exact absurd h (List.not_mem_nil _)
  | cons p rest ih =>
    obtain ⟨y, ann⟩ := p
    simp only [List.map, List.mem_cons] at h
    simp only [List.flatMap_cons, List.mem_append]
    cases h with
    | inl heq => left; simp [heq]
    | inr hmem => right; exact ih hmem

/-- If x ∉ all_fvs Γ then x ∉ dom Γ. -/
theorem LNCtx.not_mem_dom_of_not_mem_all_fvs {Γ : LNCtx} {x : String}
    (h : x ∉ LNCtx.all_fvs Γ) : x ∉ LNCtx.dom Γ :=
  fun hmem => h (LNCtx.mem_all_fvs_of_mem_dom hmem)

/-- An annotation is locally closed if its embedded term is. -/
def LNAnn.lc : LNAnn → Prop
  | .sub t => t.lc
  | .equiv α => α.lc

/-- A context is well-formed: all annotation terms are locally closed. -/
def LNCtx.wf (Γ : LNCtx) : Prop := ∀ p ∈ Γ, p.2.lc

/-- A stack is well-formed: all elements are locally closed. -/
def LNStack.wf (s : LNStack) : Prop := ∀ e ∈ s, e.lc

/-- Context inclusion: every lookup in Γ is preserved in Γ'. -/
def LNCtx.sub_ctx (Γ Γ' : LNCtx) : Prop :=
  ∀ x ann, Γ.lookup' x = some ann → Γ'.lookup' x = some ann

/-- Monotonicity of context inclusion under prepend of the same binding. -/
theorem LNCtx.sub_cons {Γ Γ' : LNCtx} {y : String} {ann : LNAnn}
    (h : LNCtx.sub_ctx Γ Γ') : LNCtx.sub_ctx ((y, ann) :: Γ) ((y, ann) :: Γ') := by
  intro x a hlook
  simp only [LNCtx.lookup'] at *
  split at hlook <;> simp_all
  exact h x a hlook

/-- If x has a binding in Γ, then x is in dom(Γ). -/
private theorem mem_dom_of_lookup' {Γ : LNCtx} {x : String} {a : LNAnn}
    (h : LNCtx.lookup' Γ x = some a) : x ∈ LNCtx.dom Γ := by
  induction Γ with
  | nil => simp [LNCtx.lookup'] at h
  | cons p rest ih =>
    obtain ⟨y, a'⟩ := p
    simp only [LNCtx.lookup'] at h
    simp only [LNCtx.dom, List.map, List.mem_cons]
    by_cases hyx : y == x
    · left; exact (beq_iff_eq.mp hyx).symm
    · simp [hyx] at h; right; exact ih h

/-- A fresh variable's binding can be prepended without affecting existing lookups. -/
theorem LNCtx.sub_of_cons_fresh {Γ : LNCtx} {z : String} {ann : LNAnn}
    (hz : z ∉ LNCtx.dom Γ) : LNCtx.sub_ctx Γ ((z, ann) :: Γ) := by
  intro x a hlook
  simp only [LNCtx.lookup']
  have hne : ¬(z == x) = true := by
    simp [beq_iff_eq]
    intro heq; subst heq; exact hz (mem_dom_of_lookup' hlook)
  simp [hne, hlook]

/-- For any finite context and term, there exists a fresh variable name. -/
theorem exists_fresh (Γ : LNCtx) (e : LNExpr)
    : ∃ x : String, x ∉ LNCtx.dom Γ ∧ x ∉ e.fvs := by
  obtain ⟨x, hx⟩ := exists_fresh_string (LNCtx.dom Γ ++ e.fvs)
  exact ⟨x, fun h => hx (List.mem_append_left _ h), fun h => hx (List.mem_append_right _ h)⟩

/-! ## Equivalence and Subtyping Reduction (Figure 2)

These are mutually inductive:
- ME-PRO (in LNEquivRed) uses LNSubRed as a premise
- MS-EQU (in LNSubRed) uses LNEquivRed as a premise

Binder rules (ME-BET, ME-FUN, ME-FOP, MS-FUN, MS-FOP) use **cofinite
quantification**: instead of existentially quantifying over a fresh variable
`x ∉ dom(Γ)`, the premise universally quantifies: `∀ x, x ∉ L → P(x)` for
a finite avoidance set `L : List String`. The conclusion uses the closed body
term directly (with bvar 0), not `close_at 0 x body'`.

This encoding enables mutual induction proofs of the standard LN infrastructure
lemmas (weakening, renaming, substitution) because the prover can pick `x`
fresh for anything — not just what the rule's existential committed to.
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

  /-- ME-BET: Simultaneous β-reduction (cofinite quantification).
      For all `x` not in a finite set `L`:
        `(Γ, x ≤ dom); s ⊢ body^x ≡→ t^x`
        `Γ; nil ⊢ v ≡→ v'`
      ⟹  `Γ; s ⊢ (λdom.body) v ≡→ t^v'`

      Here `t` is a term with bvar 0 representing the closed body result.
      Opening `t` with `v'` gives the β-reduct. -/
  | me_bet {Γ : LNCtx} {s : LNStack} {dom body t v v' : LNExpr} (L : List String) :
      (∀ x, x ∉ L → LNEquivRed ((x, .sub dom) :: Γ) s (body.open_at 0 (.fvar x)) (t.open_at 0 (.fvar x))) →
      LNEquivRed Γ [] v v' →
      LNEquivRed Γ s (.app (.lam dom body) v) (t.open_at 0 v')

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

  /-- ME-FUN: Unapplied abstraction (cofinite quantification, stack is nil).
      For all `x` not in a finite set `L`:
        `Γ; nil ⊢ dom ≡→ dom'`
        `(Γ, x ≤ dom); nil ⊢ body^x ≡→ body'^x`
      ⟹  `Γ; nil ⊢ λdom.body ≡→ λdom'. body'`

      Here `body'` has bvar 0 for the bound variable. -/
  | me_fun {Γ : LNCtx} {dom dom' body body' : LNExpr} (L : List String) :
      LNEquivRed Γ [] dom dom' →
      (∀ x, x ∉ L → LNEquivRed ((x, .sub dom) :: Γ) [] (body.open_at 0 (.fvar x)) (body'.open_at 0 (.fvar x))) →
      LNEquivRed Γ [] (.lam dom body) (.lam dom' body')

  /-- ME-FOP: Applied abstraction — pop operand from stack (cofinite).
      For all `x` not in a finite set `L`:
        `Γ; nil ⊢ dom ≡→ dom'`
        `(Γ, x ≡ α); s ⊢ body^x ≡→ body'^x`
      ⟹  `Γ; α :: s ⊢ λdom.body ≡→ λdom'. body'`

      The operand `α` from the stack becomes an equivalence annotation.
      Here `body'` has bvar 0 for the bound variable. -/
  | me_fop {Γ : LNCtx} {s : LNStack} {α dom dom' body body' : LNExpr} (L : List String) :
      LNEquivRed Γ [] dom dom' →
      (∀ x, x ∉ L → LNEquivRed ((x, .equiv α) :: Γ) s (body.open_at 0 (.fvar x)) (body'.open_at 0 (.fvar x))) →
      LNEquivRed Γ (α :: s) (.lam dom body) (.lam dom' body')

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

  /-- MS-FUN: Unapplied abstraction — promote body (cofinite, stack is nil).
      For all `x` not in a finite set `L`:
        `(Γ, x ≤ dom); nil ⊢ body^x ≤→ body'^x`
      ⟹  `Γ; nil ⊢ λdom.body ≤→ λdom. body'`

      Note: the domain annotation is NOT changed by subtyping. -/
  | ms_fun {Γ : LNCtx} {dom body body' : LNExpr} (L : List String) :
      (∀ x, x ∉ L → LNSubRed ((x, .sub dom) :: Γ) [] (body.open_at 0 (.fvar x)) (body'.open_at 0 (.fvar x))) →
      LNSubRed Γ [] (.lam dom body) (.lam dom body')

  /-- MS-FOP: Applied abstraction — pop from stack, promote body (cofinite).
      For all `x` not in a finite set `L`:
        `(Γ, x ≡ α); s ⊢ body^x ≤→ body'^x`
      ⟹  `Γ; α :: s ⊢ λdom.body ≤→ λdom. body'`

      Note: the domain annotation is NOT changed by subtyping. -/
  | ms_fop {Γ : LNCtx} {s : LNStack} {α dom body body' : LNExpr} (L : List String) :
      (∀ x, x ∉ L → LNSubRed ((x, .equiv α) :: Γ) s (body.open_at 0 (.fvar x)) (body'.open_at 0 (.fvar x))) →
      LNSubRed Γ (α :: s) (.lam dom body) (.lam dom body')

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
    match s with
    | [] =>
      exact .me_fun (L := LNCtx.dom Γ)
        (equivRed_refl Γ [] dom hdom_lc)
        (fun x hx => equivRed_refl ((x, .sub dom) :: Γ) [] _ (LNExpr.lc_at_open_fvar hbody_lc1))
    | α :: s' =>
      exact .me_fop (L := LNCtx.dom Γ)
        (equivRed_refl Γ [] dom hdom_lc)
        (fun x _ => equivRed_refl ((x, .equiv α) :: Γ) s' _ (LNExpr.lc_at_open_fvar hbody_lc1))
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

set_option maxHeartbeats 800000 in
/-- Context monotonicity for ≡→: if every lookup in Γ is preserved in Γ',
    then any derivation in Γ holds in Γ'. Proved by mutual induction using
    the combined recursor for LNEquivRed/LNSubRed. The cofinite binder cases
    pass through directly via LNCtx.sub_cons (prepending the same binding
    preserves context inclusion). -/
theorem equivRed_ctx_mono
    {Γ : LNCtx} {s : LNStack} {u v : LNExpr}
    (h : LNEquivRed Γ s u v) {Γ' : LNCtx} (hsub : LNCtx.sub_ctx Γ Γ')
    : LNEquivRed Γ' s u v := by
  have go :=
    @LNEquivRed.rec
      (motive_1 := fun Γ s u v _ => ∀ Γ', LNCtx.sub_ctx Γ Γ' → LNEquivRed Γ' s u v)
      (motive_2 := fun Γ s u v _ => ∀ Γ', LNCtx.sub_ctx Γ Γ' → LNSubRed Γ' s u v)
      -- me_pro
      (fun hmem _hsub_red ih_sub Γ' hsc => .me_pro (hsc _ _ hmem) (ih_sub Γ' hsc))
      -- me_bet
      (fun L _hbody _hv ih_body ih_v Γ' hsc =>
        .me_bet L (fun y hy => ih_body y hy ((y, .sub _) :: Γ') (LNCtx.sub_cons hsc)) (ih_v Γ' hsc))
      -- me_top
      (fun Γ' _hsc => .me_top)
      -- me_var
      (fun Γ' _hsc => .me_var)
      -- me_tap
      (fun Γ' _hsc => .me_tap)
      -- me_app
      (fun _hu _hv ih_u ih_v Γ' hsc => .me_app (ih_u Γ' hsc) (ih_v Γ' hsc))
      -- me_fun
      (fun L _hdom _hbody ih_dom ih_body Γ' hsc =>
        .me_fun L (ih_dom Γ' hsc) (fun y hy => ih_body y hy ((y, .sub _) :: Γ') (LNCtx.sub_cons hsc)))
      -- me_fop
      (fun L _hdom _hbody ih_dom ih_body Γ' hsc =>
        .me_fop L (ih_dom Γ' hsc) (fun y hy => ih_body y hy ((y, .equiv _) :: Γ') (LNCtx.sub_cons hsc)))
      -- ms_pro
      (fun hmem Γ' hsc => .ms_pro (hsc _ _ hmem))
      -- ms_top
      (fun Γ' _hsc => .ms_top)
      -- ms_equ
      (fun _hequ ih_equ Γ' hsc => .ms_equ (ih_equ Γ' hsc))
      -- ms_app
      (fun _hsub_u ih_sub_u Γ' hsc => .ms_app (ih_sub_u Γ' hsc))
      -- ms_fun
      (fun L _hbody ih_body Γ' hsc =>
        .ms_fun L (fun y hy => ih_body y hy ((y, .sub _) :: Γ') (LNCtx.sub_cons hsc)))
      -- ms_fop
      (fun L _hbody ih_body Γ' hsc =>
        .ms_fop L (fun y hy => ih_body y hy ((y, .equiv _) :: Γ') (LNCtx.sub_cons hsc)))
  exact go h Γ' hsub

set_option maxHeartbeats 800000 in
/-- Context monotonicity for ≤→. -/
theorem subRed_ctx_mono
    {Γ : LNCtx} {s : LNStack} {u v : LNExpr}
    (h : LNSubRed Γ s u v) {Γ' : LNCtx} (hsub : LNCtx.sub_ctx Γ Γ')
    : LNSubRed Γ' s u v := by
  have go :=
    @LNSubRed.rec
      (motive_1 := fun Γ s u v _ => ∀ Γ', LNCtx.sub_ctx Γ Γ' → LNEquivRed Γ' s u v)
      (motive_2 := fun Γ s u v _ => ∀ Γ', LNCtx.sub_ctx Γ Γ' → LNSubRed Γ' s u v)
      -- me_pro
      (fun hmem _hsub_red ih_sub Γ' hsc => .me_pro (hsc _ _ hmem) (ih_sub Γ' hsc))
      -- me_bet
      (fun L _hbody _hv ih_body ih_v Γ' hsc =>
        .me_bet L (fun y hy => ih_body y hy ((y, .sub _) :: Γ') (LNCtx.sub_cons hsc)) (ih_v Γ' hsc))
      -- me_top
      (fun Γ' _hsc => .me_top)
      -- me_var
      (fun Γ' _hsc => .me_var)
      -- me_tap
      (fun Γ' _hsc => .me_tap)
      -- me_app
      (fun _hu _hv ih_u ih_v Γ' hsc => .me_app (ih_u Γ' hsc) (ih_v Γ' hsc))
      -- me_fun
      (fun L _hdom _hbody ih_dom ih_body Γ' hsc =>
        .me_fun L (ih_dom Γ' hsc) (fun y hy => ih_body y hy ((y, .sub _) :: Γ') (LNCtx.sub_cons hsc)))
      -- me_fop
      (fun L _hdom _hbody ih_dom ih_body Γ' hsc =>
        .me_fop L (ih_dom Γ' hsc) (fun y hy => ih_body y hy ((y, .equiv _) :: Γ') (LNCtx.sub_cons hsc)))
      -- ms_pro
      (fun hmem Γ' hsc => .ms_pro (hsc _ _ hmem))
      -- ms_top
      (fun Γ' _hsc => .ms_top)
      -- ms_equ
      (fun _hequ ih_equ Γ' hsc => .ms_equ (ih_equ Γ' hsc))
      -- ms_app
      (fun _hsub_u ih_sub_u Γ' hsc => .ms_app (ih_sub_u Γ' hsc))
      -- ms_fun
      (fun L _hbody ih_body Γ' hsc =>
        .ms_fun L (fun y hy => ih_body y hy ((y, .sub _) :: Γ') (LNCtx.sub_cons hsc)))
      -- ms_fop
      (fun L _hbody ih_body Γ' hsc =>
        .ms_fop L (fun y hy => ih_body y hy ((y, .equiv _) :: Γ') (LNCtx.sub_cons hsc)))
  exact go h Γ' hsub

/-! ### equivRed_weaken / subRed_weaken: REMOVED (FALSE)

The former axioms `equivRed_weaken` and `subRed_weaken` claimed that
reduction is preserved under context reduction (Γ;s ↦ Γ';s'). This is
FALSE — see the counterexample at the end of this file.

The commutativity MS-PRO/ME-VAR case that previously motivated these
axioms is now handled by `equivRed_ctx_ext` (for the context part)
and a restricted stack-extension sorry for annotation terms (see the
inline comment in the MS-PRO/ME-VAR case).
-/

/-- Structural context extension for ≡→ (standard LN infrastructure).
    If Γ;s ⊢ u ≡→ v and x ∉ dom(Γ), then (x,ann)::Γ; s ⊢ u ≡→ v.
    Derived from context monotonicity (equivRed_ctx_mono) and the fact
    that a fresh binding doesn't affect existing lookups. -/
theorem equivRed_ctx_ext
    {Γ : LNCtx} {s : LNStack} {u v : LNExpr}
    (h : LNEquivRed Γ s u v) {x : String} {ann : LNAnn}
    (hfresh : x ∉ LNCtx.dom Γ)
    : LNEquivRed ((x, ann) :: Γ) s u v :=
  equivRed_ctx_mono h (LNCtx.sub_of_cons_fresh hfresh)

/-- Structural context extension for ≤→ (standard LN infrastructure). -/
theorem subRed_ctx_ext
    {Γ : LNCtx} {s : LNStack} {u v : LNExpr}
    (h : LNSubRed Γ s u v) {x : String} {ann : LNAnn}
    (hfresh : x ∉ LNCtx.dom Γ)
    : LNSubRed ((x, ann) :: Γ) s u v :=
  subRed_ctx_mono h (LNCtx.sub_of_cons_fresh hfresh)

/-! ### Stack extension: FALSE as stated

Stack extension (Lemma 19 in the paper) claims:
  If Γ;[] ⊢ u ≡→ v then Γ;s ⊢ u ≡→ v  (and similarly for ≤→).

This is FALSE in general. Counterexample at end of file. The failure mode:
ME-PRO on variable x (with x ≡ α ∈ Γ where α is a lambda) requires
LNSubRed Γ s α α'. Under empty stack MS-FUN gives the body variable a .sub
annotation (allowing MS-PRO), while under non-empty stack MS-FOP gives .equiv
(blocking MS-PRO), making certain results unreachable.

A restricted form holds for "stack-stable" terms (those whose reduction does
not depend on the stack). Annotation terms in well-formed contexts satisfy
this, but well-formedness is not formally tracked in the current development.
The commutativity proof's MS-PRO case requires this restricted form; the
needed fact is sorry'd inline there.
-/

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
    then Γ;s ⊢ u[x↦v] ≡→ u'[x↦v'].

    Formerly an axiom, now a sorry'd theorem. The proof requires mutual
    induction with `subRed_subst` and a strengthened motive that also
    substitutes stack elements. See the file header for details on blockers.
    Infrastructure lemmas `subst_open_at_gen`, `open_subst_comm`, and
    `ctx_swap_sub_ctx` are proved toward this goal. -/
theorem equivRed_subst
    {Γ : LNCtx} {s : LNStack} {x : String} {ann : LNAnn}
    {u u' v v' : LNExpr}
    (hbody : LNEquivRed ((x, ann) :: Γ) s u u')
    (harg  : LNEquivRed Γ [] v v')
    : LNEquivRed Γ s (u.subst_fvar x v) (u'.subst_fvar x v') := by
  sorry

/-- Substitution for ≤→ (Lemma 30).
    If (x,ann)::Γ; s ⊢ u ≤→ u' and x ∉ dom(Γ)
    then Γ;s ⊢ u[x↦v] ≤→ u'[x↦v].

    Formerly an axiom, now a sorry'd theorem. See `equivRed_subst` for
    proof strategy and blockers. -/
theorem subRed_subst
    {Γ : LNCtx} {s : LNStack} {x : String} {ann : LNAnn}
    {u u' v : LNExpr}
    (hbody : LNSubRed ((x, ann) :: Γ) s u u')
    (hfresh : x ∉ LNCtx.dom Γ)
    : LNSubRed Γ s (u.subst_fvar x v) (u'.subst_fvar x v) := by
  sorry

/-- Context lookup: x ≤ t ∈ Γ and Γ;s ↦ Γ';s'  ⟹  x ≤ t' ∈ Γ'
    with Γ;[] ⊢ t ≡→ t'.
    Proved by induction on the context reduction derivation, using
    equivRed_ctx_ext to lift the equiv-red through context layers. -/
theorem ctxRed_lookup_sub
    {Γ Γ' : LNCtx} {s s' : LNStack} {x : String} {t : LNExpr}
    (hmem : LNCtx.mem_sub Γ x t) (hctx : LNCtxRed Γ s Γ' s')
    (hnd : (LNCtx.dom Γ).Nodup)
    : ∃ t', LNCtx.mem_sub Γ' x t' ∧ LNEquivRed Γ [] t t' := by
  induction hctx with
  | @ct_ann_sub Γ_i _ Γ_i' _ y u u' hctx_i hred_u ih =>
    simp only [LNCtx.mem_sub, LNCtx.lookup'] at hmem
    have hnd_inner : (LNCtx.dom Γ_i).Nodup :=
      (List.nodup_cons.mp hnd).2
    have hy_fresh : y ∉ LNCtx.dom Γ_i :=
      (List.nodup_cons.mp hnd).1
    by_cases hyx : y == x
    · -- y = x: the head entry matches, t = u
      simp only [hyx, ite_true] at hmem; cases hmem
      refine ⟨u', ?_, equivRed_ctx_ext hred_u hy_fresh⟩
      show LNCtx.lookup' ((y, .sub u') :: Γ_i') x = some (.sub u')
      simp only [LNCtx.lookup', hyx, ite_true]
    · -- y ≠ x: the entry is deeper in the context
      simp only [hyx, ite_false] at hmem
      obtain ⟨t', hmem', hred_t⟩ := ih hmem hnd_inner
      refine ⟨t', ?_, equivRed_ctx_ext hred_t hy_fresh⟩
      show LNCtx.lookup' ((y, .sub u') :: Γ_i') x = some (.sub t')
      simp only [LNCtx.lookup', hyx, ite_false]; exact hmem'
  | @ct_ann_equiv Γ_i _ Γ_i' _ y α α' hctx_i hred_α ih =>
    simp only [LNCtx.mem_sub, LNCtx.lookup'] at hmem
    have hnd_inner : (LNCtx.dom Γ_i).Nodup :=
      (List.nodup_cons.mp hnd).2
    have hy_fresh : y ∉ LNCtx.dom Γ_i :=
      (List.nodup_cons.mp hnd).1
    by_cases hyx : y == x
    · -- y = x but has .equiv not .sub: contradiction
      simp only [hyx, ite_true] at hmem; cases hmem
    · simp only [hyx, ite_false] at hmem
      obtain ⟨t', hmem', hred_t⟩ := ih hmem hnd_inner
      refine ⟨t', ?_, equivRed_ctx_ext hred_t hy_fresh⟩
      show LNCtx.lookup' ((y, .equiv α') :: Γ_i') x = some (.sub t')
      simp only [LNCtx.lookup', hyx, ite_false]; exact hmem'
  | ct_stk _ _ ih => exact ih hmem hnd
  | ct_nil => simp [LNCtx.mem_sub, LNCtx.lookup'] at hmem

/-- Context lookup: x ≡ α ∈ Γ and Γ;s ↦ Γ';s'  ⟹  x ≡ α' ∈ Γ'
    with Γ;[] ⊢ α ≡→ α'.
    Proved by induction on the context reduction derivation. -/
theorem ctxRed_lookup_equiv
    {Γ Γ' : LNCtx} {s s' : LNStack} {x : String} {α : LNExpr}
    (hmem : LNCtx.mem_equiv Γ x α) (hctx : LNCtxRed Γ s Γ' s')
    (hnd : (LNCtx.dom Γ).Nodup)
    : ∃ α', LNCtx.mem_equiv Γ' x α' ∧ LNEquivRed Γ [] α α' := by
  induction hctx with
  | @ct_ann_sub Γ_i _ Γ_i' _ y u u' hctx_i hred_u ih =>
    simp only [LNCtx.mem_equiv, LNCtx.lookup'] at hmem
    have hnd_inner : (LNCtx.dom Γ_i).Nodup :=
      (List.nodup_cons.mp hnd).2
    have hy_fresh : y ∉ LNCtx.dom Γ_i :=
      (List.nodup_cons.mp hnd).1
    by_cases hyx : y == x
    · -- y = x but has .sub not .equiv: contradiction
      simp only [hyx, ite_true] at hmem; cases hmem
    · simp only [hyx, ite_false] at hmem
      obtain ⟨α', hmem', hred_α⟩ := ih hmem hnd_inner
      refine ⟨α', ?_, equivRed_ctx_ext hred_α hy_fresh⟩
      show LNCtx.lookup' ((y, .sub u') :: Γ_i') x = some (.equiv α')
      simp only [LNCtx.lookup', hyx, ite_false]; exact hmem'
  | @ct_ann_equiv Γ_i _ Γ_i' _ y β β' hctx_i hred_β ih =>
    simp only [LNCtx.mem_equiv, LNCtx.lookup'] at hmem
    have hnd_inner : (LNCtx.dom Γ_i).Nodup :=
      (List.nodup_cons.mp hnd).2
    have hy_fresh : y ∉ LNCtx.dom Γ_i :=
      (List.nodup_cons.mp hnd).1
    by_cases hyx : y == x
    · -- y = x: the head entry matches, α = β
      simp only [hyx, ite_true] at hmem; cases hmem
      refine ⟨β', ?_, equivRed_ctx_ext hred_β hy_fresh⟩
      show LNCtx.lookup' ((y, .equiv β') :: Γ_i') x = some (.equiv β')
      simp only [LNCtx.lookup', hyx, ite_true]
    · simp only [hyx, ite_false] at hmem
      obtain ⟨α', hmem', hred_α⟩ := ih hmem hnd_inner
      refine ⟨α', ?_, equivRed_ctx_ext hred_α hy_fresh⟩
      show LNCtx.lookup' ((y, .equiv β') :: Γ_i') x = some (.equiv α')
      simp only [LNCtx.lookup', hyx, ite_false]; exact hmem'
  | ct_stk _ _ ih => exact ih hmem hnd
  | ct_nil => simp [LNCtx.mem_equiv, LNCtx.lookup'] at hmem

/-- A variable cannot simultaneously have a sub and equiv annotation.
    Proved: lookup' returns a unique result per key. -/
theorem no_sub_and_equiv
    {Γ : LNCtx} {x : String} {t α : LNExpr}
    (hsub : LNCtx.mem_sub Γ x t) (hequiv : LNCtx.mem_equiv Γ x α)
    : False := by
  simp [LNCtx.mem_sub, LNCtx.mem_equiv] at hsub hequiv
  rw [hsub] at hequiv
  exact absurd hequiv (by simp)

/-- Self-substitution is the identity: e.subst_fvar x (.fvar x) = e. -/
theorem subst_fvar_self (e : LNExpr) (x : String)
    : e.subst_fvar x (.fvar x) = e := by
  induction e with
  | bvar _ => simp [LNExpr.subst_fvar]
  | fvar z =>
    simp only [LNExpr.subst_fvar]
    split <;> simp_all [beq_iff_eq]
  | top => simp [LNExpr.subst_fvar]
  | lam dom body ih_dom ih_body =>
    simp [LNExpr.subst_fvar, ih_dom, ih_body]
  | app f a ih_f ih_a =>
    simp [LNExpr.subst_fvar, ih_f, ih_a]

/-- Substitution is a no-op when the variable doesn't occur free. -/
theorem subst_fvar_notin {e : LNExpr} {x : String} {u : LNExpr}
    (hfr : x ∉ e.fvs) : e.subst_fvar x u = e := by
  induction e with
  | bvar _ => simp [LNExpr.subst_fvar]
  | fvar z =>
    simp [LNExpr.fvs, List.mem_singleton] at hfr
    simp only [LNExpr.subst_fvar]
    have : ¬(z == x) = true := by simp [beq_iff_eq]; exact Ne.symm hfr
    simp [this]
  | top => simp [LNExpr.subst_fvar]
  | lam dom body ih_dom ih_body =>
    simp [LNExpr.fvs, List.mem_append] at hfr
    simp [LNExpr.subst_fvar, ih_dom hfr.1, ih_body hfr.2]
  | app f a ih_f ih_a =>
    simp [LNExpr.fvs, List.mem_append] at hfr
    simp [LNExpr.subst_fvar, ih_f hfr.1, ih_a hfr.2]

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

/-- General version: closing then opening with an arbitrary term equals
    substitution. (e.close_at k y).open_at k u = e.subst_fvar y u when e.lc_at k. -/
private theorem open_close_subst_expr_gen
    (e : LNExpr) (u : LNExpr) (y : String) (k : Nat) (hlc : e.lc_at k)
    : (e.close_at k y).open_at k u = e.subst_fvar y u := by
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

/-- (e.close_at 0 y).open_at 0 u = e.subst_fvar y u when e is locally closed. -/
theorem open_close_subst_expr
    {e : LNExpr} {u : LNExpr} {y : String} (hlc : e.lc_at 0)
    : (e.close_at 0 y).open_at 0 u = e.subst_fvar y u :=
  open_close_subst_expr_gen e u y 0 hlc

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

/-- Opening then substituting the same variable is the same as opening
    directly: (e.open_at k (fvar x)).subst_fvar x u = e.open_at k u
    when x ∉ fvs(e). Standard LN infrastructure. -/
private theorem subst_open_gen (e : LNExpr) (x : String) (u : LNExpr) (k : Nat)
    (hfr : x ∉ e.fvs)
    : (e.open_at k (.fvar x)).subst_fvar x u = e.open_at k u := by
  induction e generalizing k with
  | bvar n =>
    simp [LNExpr.open_at, LNExpr.subst_fvar]
    split
    · simp [LNExpr.subst_fvar]
    · simp [LNExpr.subst_fvar]
  | fvar z =>
    simp [LNExpr.fvs, List.mem_singleton] at hfr
    simp only [LNExpr.open_at, LNExpr.subst_fvar]
    have hne : ¬(z == x) = true := by simp [beq_iff_eq]; exact Ne.symm hfr
    simp [hne]
  | top => simp [LNExpr.open_at, LNExpr.subst_fvar]
  | lam dom body ih_dom ih_body =>
    simp [LNExpr.fvs, List.mem_append] at hfr
    simp [LNExpr.open_at, LNExpr.subst_fvar, ih_dom k hfr.1, ih_body (k+1) hfr.2]
  | app f a ih_f ih_a =>
    simp [LNExpr.fvs, List.mem_append] at hfr
    simp [LNExpr.open_at, LNExpr.subst_fvar, ih_f k hfr.1, ih_a k hfr.2]

/-- (e.open_at 0 (fvar x)).subst_fvar x u = e.open_at 0 u when x ∉ fvs(e). -/
theorem subst_open
    {e : LNExpr} {x : String} {u : LNExpr} (hfr : x ∉ e.fvs)
    : (e.open_at 0 (.fvar x)).subst_fvar x u = e.open_at 0 u :=
  subst_open_gen e x u 0 hfr

/-- subst_fvar with fvar commutes with open_at:
    `(e.open_at k v).subst_fvar x (fvar y) = (e.subst_fvar x (fvar y)).open_at k (v.subst_fvar x (fvar y))`.
    Standard LN infrastructure. -/
theorem subst_fvar_fvar_open_at (e : LNExpr) (x y : String) (k : Nat) (v : LNExpr)
    : (e.open_at k v).subst_fvar x (.fvar y) = (e.subst_fvar x (.fvar y)).open_at k (v.subst_fvar x (.fvar y)) := by
  induction e generalizing k with
  | bvar n =>
    show (if n == k then v else .bvar n).subst_fvar x (.fvar y) =
         if n == k then v.subst_fvar x (.fvar y) else .bvar n
    split <;> rfl
  | fvar z =>
    simp only [LNExpr.open_at, LNExpr.subst_fvar]
    split <;> rfl
  | top => rfl
  | lam dom body ih_dom ih_body =>
    simp only [LNExpr.open_at, LNExpr.subst_fvar, ih_dom k, ih_body (k+1)]
  | app f a ih_f ih_a =>
    simp only [LNExpr.open_at, LNExpr.subst_fvar, ih_f k, ih_a k]

/-- Specialized version: subst_fvar with fvar commutes with open_at when the
    opening variable is different from the substituted variable.
    `(e.open_at k (fvar z)).subst_fvar x (fvar y) = (e.subst_fvar x (fvar y)).open_at k (fvar z)`
    when `x ≠ z`. -/
theorem subst_fvar_fvar_open_fvar (e : LNExpr) (x y z : String) (k : Nat)
    (hxz : x ≠ z)
    : (e.open_at k (.fvar z)).subst_fvar x (.fvar y) = (e.subst_fvar x (.fvar y)).open_at k (.fvar z) := by
  rw [subst_fvar_fvar_open_at]
  have : (LNExpr.fvar z).subst_fvar x (.fvar y) = .fvar z := by
    simp only [LNExpr.subst_fvar]
    have : ¬ (z == x) = true := by simp [beq_iff_eq]; exact Ne.symm hxz
    simp [this]
  rw [this]

/-- Double substitution: (e[x↦fvar y])[y↦v] = e[x↦v] when y ∉ fvs(e).
    Standard locally nameless infrastructure. -/
theorem subst_fvar_double (e : LNExpr) (x y : String) (v : LNExpr)
    (hfresh : y ∉ e.fvs)
    : (e.subst_fvar x (.fvar y)).subst_fvar y v = e.subst_fvar x v := by
  induction e with
  | bvar _ => simp [LNExpr.subst_fvar]
  | fvar z =>
    simp [LNExpr.fvs, List.mem_singleton] at hfresh
    simp only [LNExpr.subst_fvar]
    by_cases hzx : z == x
    · simp [hzx, LNExpr.subst_fvar]
    · simp only [hzx, ite_false, LNExpr.subst_fvar]
      have hzy : ¬(z == y) = true := by simp [beq_iff_eq]; exact Ne.symm hfresh
      simp [hzy, LNExpr.subst_fvar]
  | top => simp [LNExpr.subst_fvar]
  | lam dom body ih_dom ih_body =>
    simp [LNExpr.fvs, List.mem_append] at hfresh
    simp [LNExpr.subst_fvar, ih_dom hfresh.1, ih_body hfresh.2]
  | app f a ih_f ih_a =>
    simp [LNExpr.fvs, List.mem_append] at hfresh
    simp [LNExpr.subst_fvar, ih_f hfresh.1, ih_a hfresh.2]

/-- lc_at is monotone: if lc_at k then lc_at k' for any k' >= k. -/
private theorem lc_at_mono {e : LNExpr} {k k' : Nat} (hle : k ≤ k')
    (h : e.lc_at k) : e.lc_at k' := by
  induction e generalizing k k' with
  | bvar n => simp [LNExpr.lc_at] at *; omega
  | fvar _ => trivial
  | top => trivial
  | lam dom body ih_dom ih_body =>
    simp [LNExpr.lc_at] at *
    exact ⟨ih_dom hle h.1, ih_body (by omega) h.2⟩
  | app f a ih_f ih_a =>
    simp [LNExpr.lc_at] at *
    exact ⟨ih_f hle h.1, ih_a hle h.2⟩

/-- Opening a locally-closed term with any term at any depth is a no-op.
    If `e.lc_at k` then `e.open_at k u = e`. -/
private theorem open_at_lc {e : LNExpr} {k : Nat} {u : LNExpr}
    (hlc : e.lc_at k) : e.open_at k u = e := by
  induction e generalizing k with
  | bvar n =>
    simp [LNExpr.lc_at] at hlc
    simp [LNExpr.open_at]
    omega
  | fvar _ => rfl
  | top => rfl
  | lam dom body ih_dom ih_body =>
    simp [LNExpr.lc_at] at hlc
    simp [LNExpr.open_at, ih_dom hlc.1, ih_body hlc.2]
  | app f a ih_f ih_a =>
    simp [LNExpr.lc_at] at hlc
    simp [LNExpr.open_at, ih_f hlc.1, ih_a hlc.2]

/-- Substitution commutes with opening by a fresh variable:
    `(e.open_at k (fvar y)).subst_fvar x v = (e.subst_fvar x v).open_at k (fvar y)`
    when `y != x` and `v` is locally closed at depth `k`.
    Standard locally nameless infrastructure.
    Proved by structural induction on `e`. -/
theorem open_subst_comm (e : LNExpr) (x y : String) (v : LNExpr) (k : Nat)
    (hyx : y ≠ x) (hlc : v.lc_at k)
    : (e.open_at k (.fvar y)).subst_fvar x v = (e.subst_fvar x v).open_at k (.fvar y) := by
  induction e generalizing k with
  | bvar n =>
    simp only [LNExpr.open_at]
    split
    · -- n == k: LHS = (fvar y).subst_fvar x v = fvar y (since y != x)
      simp only [LNExpr.subst_fvar]
      have : ¬(y == x) = true := by simp [beq_iff_eq]; exact hyx
      simp [this, LNExpr.subst_fvar, LNExpr.open_at, *]
    · simp [LNExpr.subst_fvar, LNExpr.open_at, *]
  | fvar z =>
    simp only [LNExpr.open_at, LNExpr.subst_fvar]
    by_cases hzx : z == x
    · -- z = x: LHS = v, RHS = v.open_at k (fvar y)
      -- v is lc at k, so open_at k is a no-op on v
      simp [hzx, open_at_lc hlc]
    · simp [hzx, LNExpr.open_at]
  | top => simp [LNExpr.open_at, LNExpr.subst_fvar]
  | lam dom body ih_dom ih_body =>
    simp [LNExpr.open_at, LNExpr.subst_fvar, ih_dom k hlc,
      ih_body (k + 1) (lc_at_mono (by omega) hlc)]
  | app f a ih_f ih_a =>
    simp [LNExpr.open_at, LNExpr.subst_fvar, ih_f k hlc, ih_a k hlc]

/-- Context permutation: swapping two bindings with different names
    preserves lookup results. -/
theorem ctx_swap_sub_ctx {x y : String} {ann_x ann_y : LNAnn} {Γ : LNCtx}
    (hne : y ≠ x)
    : LNCtx.sub_ctx ((y, ann_y) :: (x, ann_x) :: Γ) ((x, ann_x) :: (y, ann_y) :: Γ) := by
  intro z a hlook
  simp only [LNCtx.lookup'] at *
  by_cases hyz : y = z
  · -- y = z: in the swapped context, y is second, skip x first
    subst hyz
    have hxny : ¬ x = y := Ne.symm hne
    simp only [beq_self_eq_true, ite_true] at hlook
    simp only [show (x == y) = false from by rw [beq_eq_false_iff_ne]; exact hxny,
      ite_false, beq_self_eq_true, ite_true]
    exact hlook
  · -- y != z: skip y in both
    have hyzf : (y == z) = false := by rw [beq_eq_false_iff_ne]; exact hyz
    simp only [hyzf, ite_false] at hlook
    by_cases hxz : x = z
    · subst hxz
      simp only [beq_self_eq_true, ite_true] at hlook ⊢
      exact hlook
    · have hxzf : (x == z) = false := by rw [beq_eq_false_iff_ne]; exact hxz
      simp only [hxzf, ite_false, hyzf, ite_false] at hlook ⊢
      exact hlook

/-- Alpha-renaming for ≡→ under binders.
    If (x,ann)::Γ; s ⊢ body^x ≡→ u and y ∉ dom(Γ) and x ∉ dom(Γ),
    and x ∉ fvs(body), then (y,ann)::Γ; s ⊢ body^y ≡→ u[x↦fvar y].
    Proved by combining context monotonicity + substitution lemma (equivRed_subst).
    The key steps: (1) lift the derivation to (x,ann)::(y,ann)::Γ via ctx_mono,
    (2) apply equivRed_subst to substitute x for fvar y, (3) rewrite the LHS
    using subst_fvar_fvar_open_at + subst_fvar_notin. -/
theorem equivRed_rename
    {Γ : LNCtx} {s : LNStack} {ann : LNAnn}
    {body u : LNExpr} {x y : String}
    (h : LNEquivRed ((x, ann) :: Γ) s (body.open_at 0 (.fvar x)) u)
    (_hx : x ∉ LNCtx.dom Γ) (hy : y ∉ LNCtx.dom Γ)
    (hfr : x ∉ body.fvs)
    : LNEquivRed ((y, ann) :: Γ) s (body.open_at 0 (.fvar y)) (u.subst_fvar x (.fvar y)) := by
  by_cases hxy : x = y
  · subst hxy; rw [subst_fvar_self]; exact h
  · -- Step 1: lift h into extended context (x,ann)::(y,ann)::Γ via ctx_mono
    have hsub : LNCtx.sub_ctx ((x, ann) :: Γ) ((x, ann) :: (y, ann) :: Γ) :=
      LNCtx.sub_cons (LNCtx.sub_of_cons_fresh hy)
    have h1 := equivRed_ctx_mono h hsub
    -- Step 2: apply equivRed_subst — substitute fvar y for x
    have harg : LNEquivRed ((y, ann) :: Γ) [] (.fvar y) (.fvar y) := .me_var
    have h2 := equivRed_subst h1 harg
    -- h2 : LNEquivRed ((y,ann)::Γ) s ((body^x)[x↦fvar y]) (u[x↦fvar y])
    -- Step 3: rewrite the LHS using (body^x)[x↦fvar y] = body^(fvar y)
    have hlhs : (body.open_at 0 (.fvar x)).subst_fvar x (.fvar y) = body.open_at 0 (.fvar y) := by
      rw [subst_fvar_fvar_open_at]
      simp only [LNExpr.subst_fvar, beq_self_eq_true, ite_true]
      rw [subst_fvar_notin hfr]
    rw [hlhs] at h2
    exact h2

/-- Alpha-renaming for ≤→ under binders.
    Proved by combining context monotonicity + substitution lemma (subRed_subst). -/
theorem subRed_rename
    {Γ : LNCtx} {s : LNStack} {ann : LNAnn}
    {body u : LNExpr} {x y : String}
    (h : LNSubRed ((x, ann) :: Γ) s (body.open_at 0 (.fvar x)) u)
    (hx : x ∉ LNCtx.dom Γ) (hy : y ∉ LNCtx.dom Γ)
    (hfr : x ∉ body.fvs)
    : LNSubRed ((y, ann) :: Γ) s (body.open_at 0 (.fvar y)) (u.subst_fvar x (.fvar y)) := by
  by_cases hxy : x = y
  · subst hxy; rw [subst_fvar_self]; exact h
  · -- Step 1: lift h into extended context (x,ann)::(y,ann)::Γ via ctx_mono
    have hsub : LNCtx.sub_ctx ((x, ann) :: Γ) ((x, ann) :: (y, ann) :: Γ) :=
      LNCtx.sub_cons (LNCtx.sub_of_cons_fresh hy)
    have h1 := subRed_ctx_mono h hsub
    -- Step 2: apply subRed_subst — substitute fvar y for x
    have hx_ext : x ∉ LNCtx.dom ((y, ann) :: Γ) := by
      simp only [LNCtx.dom, List.map, List.mem_cons, not_or]
      exact ⟨hxy, hx⟩
    have h2 := subRed_subst (v := .fvar y) h1 hx_ext
    -- h2 : LNSubRed ((y,ann)::Γ) s ((body^x)[x↦fvar y]) (u[x↦fvar y])
    -- Step 3: rewrite the LHS using (body^x)[x↦fvar y] = body^(fvar y)
    have hlhs : (body.open_at 0 (.fvar x)).subst_fvar x (.fvar y) = body.open_at 0 (.fvar y) := by
      rw [subst_fvar_fvar_open_at]
      simp only [LNExpr.subst_fvar, beq_self_eq_true, ite_true]
      rw [subst_fvar_notin hfr]
    rw [hlhs] at h2
    exact h2

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
  | me_bet {x : String} {Γ : LNCtx} {s : LNStack} {dom body t v v' : LNExpr} (L : List String) :
      (∀ y, y ∉ L → LNEquivRed.noPromoAt x ((y, .sub dom) :: Γ) s (body.open_at 0 (.fvar y)) (t.open_at 0 (.fvar y))) →
      LNEquivRed.noPromoAt x Γ [] v v' →
      LNEquivRed.noPromoAt x Γ s (.app (.lam dom body) v) (t.open_at 0 v')
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
  | me_fun {x : String} {Γ : LNCtx} {dom dom' body body' : LNExpr} (L : List String) :
      LNEquivRed.noPromoAt x Γ [] dom dom' →
      (∀ y, y ∉ L → LNEquivRed.noPromoAt x ((y, .sub dom) :: Γ) [] (body.open_at 0 (.fvar y)) (body'.open_at 0 (.fvar y))) →
      LNEquivRed.noPromoAt x Γ [] (.lam dom body) (.lam dom' body')
  | me_fop {x : String} {Γ : LNCtx} {s : LNStack} {α dom dom' body body' : LNExpr} (L : List String) :
      LNEquivRed.noPromoAt x Γ [] dom dom' →
      (∀ y, y ∉ L → LNEquivRed.noPromoAt x ((y, .equiv α) :: Γ) s (body.open_at 0 (.fvar y)) (body'.open_at 0 (.fvar y))) →
      LNEquivRed.noPromoAt x Γ (α :: s) (.lam dom body) (.lam dom' body')

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
  | ms_fun {x : String} {Γ : LNCtx} {dom body body' : LNExpr} (L : List String) :
      (∀ y, y ∉ L → LNSubRed.noPromoAt x ((y, .sub dom) :: Γ) [] (body.open_at 0 (.fvar y)) (body'.open_at 0 (.fvar y))) →
      LNSubRed.noPromoAt x Γ [] (.lam dom body) (.lam dom body')
  | ms_fop {x : String} {Γ : LNCtx} {s : LNStack} {α dom body body' : LNExpr} (L : List String) :
      (∀ y, y ∉ L → LNSubRed.noPromoAt x ((y, .equiv α) :: Γ) s (body.open_at 0 (.fvar y)) (body'.open_at 0 (.fvar y))) →
      LNSubRed.noPromoAt x Γ (α :: s) (.lam dom body) (.lam dom body')

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

-- noPromoAt_equiv_swap and noPromoAt_sub_swap: proved by mutual induction
-- using @LNEquivRed.noPromoAt.rec / @LNSubRed.noPromoAt.rec. The cofinite
-- binder cases augment the avoidance set L with x (to ensure y ≠ x), then
-- use swap_at_first_cons_ne to rewrite the context and equivRed_cast_ctx /
-- subRed_cast_ctx to transport the IH result.

set_option maxHeartbeats 1600000 in
theorem noPromoAt_equiv_swap (x : String) (ann_new : LNAnn)
    {Γ : LNCtx} {s : LNStack} {e u : LNExpr}
    (hnp : LNEquivRed.noPromoAt x Γ s e u) (hx : x ∈ LNCtx.dom Γ)
    : LNEquivRed (swap_at_first x ann_new Γ) s e u := by
  exact
    @LNEquivRed.noPromoAt.rec x
      (fun Γ s e u _ => LNEquivRed (swap_at_first x ann_new Γ) s e u)
      (fun Γ s e u _ => LNSubRed (swap_at_first x ann_new Γ) s e u)
      -- me_pro: z ≠ x, z ≡ α ∈ Γ, noPromoAt x Γ s α α'
      (fun hne hmem _hnp ih_sub =>
        .me_pro (swap_at_first_mem_equiv_ne hne hmem) ih_sub)
      -- me_bet: L, ∀ y ∉ L, noPromoAt x ((y,.sub dom)::Γ) s body^y t^y, noPromoAt x Γ [] v v'
      (fun L _hbody _hv ih_body ih_v =>
        .me_bet (x :: L)
          (fun y hy => by
            have hy_ne : y ≠ x := by intro heq; exact hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact equivRed_cast_ctx (swap_at_first_cons_ne x y (.sub _) ann_new _ hy_ne) (ih_body y hy_L))
          ih_v)
      -- me_top
      .me_top
      -- me_var
      .me_var
      -- me_tap
      .me_tap
      -- me_app
      (fun _hnp_u _hnp_v ih_u ih_v => .me_app ih_u ih_v)
      -- me_fun: L, noPromoAt dom, ∀ y ∉ L, noPromoAt body
      (fun L _hnp_dom _hnp_body ih_dom ih_body =>
        .me_fun (x :: L) ih_dom
          (fun y hy => by
            have hy_ne : y ≠ x := by intro heq; exact hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact equivRed_cast_ctx (swap_at_first_cons_ne x y (.sub _) ann_new _ hy_ne) (ih_body y hy_L)))
      -- me_fop: L, noPromoAt dom, ∀ y ∉ L, noPromoAt body
      (fun L _hnp_dom _hnp_body ih_dom ih_body =>
        .me_fop (x :: L) ih_dom
          (fun y hy => by
            have hy_ne : y ≠ x := by intro heq; exact hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact equivRed_cast_ctx (swap_at_first_cons_ne x y (.equiv _) ann_new _ hy_ne) (ih_body y hy_L)))
      -- ms_pro: z ≠ x, z ≤ t ∈ Γ
      (fun hne hmem => .ms_pro (swap_at_first_mem_sub_ne hne hmem))
      -- ms_top
      .ms_top
      -- ms_equ: noPromoAt equiv
      (fun _hnp ih_equiv => .ms_equ ih_equiv)
      -- ms_app
      (fun _hnp_u ih_u => .ms_app ih_u)
      -- ms_fun: L, ∀ y ∉ L, noPromoAt body
      (fun L _hnp_body ih_body =>
        .ms_fun (x :: L)
          (fun y hy => by
            have hy_ne : y ≠ x := by intro heq; exact hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact subRed_cast_ctx (swap_at_first_cons_ne x y (.sub _) ann_new _ hy_ne) (ih_body y hy_L)))
      -- ms_fop: L, ∀ y ∉ L, noPromoAt body
      (fun L _hnp_body ih_body =>
        .ms_fop (x :: L)
          (fun y hy => by
            have hy_ne : y ≠ x := by intro heq; exact hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact subRed_cast_ctx (swap_at_first_cons_ne x y (.equiv _) ann_new _ hy_ne) (ih_body y hy_L)))
      Γ s e u hnp

set_option maxHeartbeats 1600000 in
theorem noPromoAt_sub_swap (x : String) (ann_new : LNAnn)
    {Γ : LNCtx} {s : LNStack} {e u : LNExpr}
    (hnp : LNSubRed.noPromoAt x Γ s e u) (hx : x ∈ LNCtx.dom Γ)
    : LNSubRed (swap_at_first x ann_new Γ) s e u := by
  exact
    @LNSubRed.noPromoAt.rec x
      (fun Γ s e u _ => LNEquivRed (swap_at_first x ann_new Γ) s e u)
      (fun Γ s e u _ => LNSubRed (swap_at_first x ann_new Γ) s e u)
      -- me_pro
      (fun hne hmem _hnp ih_sub =>
        .me_pro (swap_at_first_mem_equiv_ne hne hmem) ih_sub)
      -- me_bet
      (fun L _hbody _hv ih_body ih_v =>
        .me_bet (x :: L)
          (fun y hy => by
            have hy_ne : y ≠ x := by intro heq; exact hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact equivRed_cast_ctx (swap_at_first_cons_ne x y (.sub _) ann_new _ hy_ne) (ih_body y hy_L))
          ih_v)
      -- me_top
      .me_top
      -- me_var
      .me_var
      -- me_tap
      .me_tap
      -- me_app
      (fun _hnp_u _hnp_v ih_u ih_v => .me_app ih_u ih_v)
      -- me_fun
      (fun L _hnp_dom _hnp_body ih_dom ih_body =>
        .me_fun (x :: L) ih_dom
          (fun y hy => by
            have hy_ne : y ≠ x := by intro heq; exact hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact equivRed_cast_ctx (swap_at_first_cons_ne x y (.sub _) ann_new _ hy_ne) (ih_body y hy_L)))
      -- me_fop
      (fun L _hnp_dom _hnp_body ih_dom ih_body =>
        .me_fop (x :: L) ih_dom
          (fun y hy => by
            have hy_ne : y ≠ x := by intro heq; exact hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact equivRed_cast_ctx (swap_at_first_cons_ne x y (.equiv _) ann_new _ hy_ne) (ih_body y hy_L)))
      -- ms_pro
      (fun hne hmem => .ms_pro (swap_at_first_mem_sub_ne hne hmem))
      -- ms_top
      .ms_top
      -- ms_equ
      (fun _hnp ih_equiv => .ms_equ ih_equiv)
      -- ms_app
      (fun _hnp_u ih_u => .ms_app ih_u)
      -- ms_fun
      (fun L _hnp_body ih_body =>
        .ms_fun (x :: L)
          (fun y hy => by
            have hy_ne : y ≠ x := by intro heq; exact hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact subRed_cast_ctx (swap_at_first_cons_ne x y (.sub _) ann_new _ hy_ne) (ih_body y hy_L)))
      -- ms_fop
      (fun L _hnp_body ih_body =>
        .ms_fop (x :: L)
          (fun y hy => by
            have hy_ne : y ≠ x := by intro heq; exact hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact subRed_cast_ctx (swap_at_first_cons_ne x y (.equiv _) ann_new _ hy_ne) (ih_body y hy_L)))
      Γ s e u hnp

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
    Requires a noPromoAt witness: the derivation must not promote x.
    Derived from the proved general version `equivRed_change_sub_to_equiv`. -/
theorem equivRed_change_sub_to_equiv_bet
    {Γ : LNCtx} {s : LNStack} {x : String} {dom α : LNExpr}
    {body u : LNExpr}
    (h : LNEquivRed ((x, .sub dom) :: Γ) s (body.open_at 0 (.fvar x)) u)
    (hnp : LNEquivRed.noPromoAt x ((x, .sub dom) :: Γ) s (body.open_at 0 (.fvar x)) u)
    : LNEquivRed ((x, .equiv α) :: Γ) s (body.open_at 0 (.fvar x)) u :=
  equivRed_change_sub_to_equiv h hnp

/-- Annotation independence: change from equiv to sub annotation
    for derivations on sub-terms obtained via IH.
    Requires a noPromoAt witness: the derivation must not promote x.
    Derived from the proved general version `equivRed_change_equiv_to_sub`. -/
theorem equivRed_change_equiv_to_sub_bet
    {Γ : LNCtx} {s : LNStack} {x : String} {dom α : LNExpr}
    {e u : LNExpr}
    (h : LNEquivRed ((x, .equiv α) :: Γ) s e u)
    (hnp : LNEquivRed.noPromoAt x ((x, .equiv α) :: Γ) s e u)
    : LNEquivRed ((x, .sub dom) :: Γ) s e u :=
  equivRed_change_equiv_to_sub h hnp

/-! #### Counterexamples: the old noPromoAt axioms were FALSE

The old `me_bet_body_noPromoAt` and `commutativity_noPromoAt` axioms
required only `x ∉ LNCtx.dom Γ`, which is too weak. The following
counterexamples show that the conclusion can be unprovable even when
the hypothesis is satisfied.

**commutativity_noPromoAt counterexample** (the simpler one):
Let Γ = [], ann = .equiv .top, s = [], e = fvar "x", u = .top.
- Derivation: ME-PRO on "x" (mem_equiv gives .top) then MS-EQU + ME-TOP.
- Freshness: "x" ∉ dom [] trivially.
- Conclusion noPromoAt "x" [("x", .equiv .top)] [] (fvar "x") .top
  is impossible: me_pro needs z ≠ "x" (fails for z = "x"),
  me_var gives fvar "x" → fvar "x" ≠ .top, no other constructor applies.

**me_bet_body_noPromoAt counterexample**:
Let Γ = [("y", .equiv (fvar "x"))], dom = .lam .top .top,
    s = [.top], body = .fvar "y".
- body.open_at 0 (fvar "x") = fvar "y" (no bvar to open).
- Derivation: ME-PRO on "y" gives α = fvar "x", then
  LNSubRed on fvar "x" via MS-PRO on "x" gives .lam .top .top.
  Result: LNEquivRed Γ [.top] (fvar "y") (.lam .top .top).
- Freshness: "x" ∉ dom [("y", ...)] = "x" ∉ ["y"] ✓.
- Conclusion noPromoAt "x" Γ [.top] (fvar "y") (.lam .top .top)
  needs me_pro z="y", z≠"x" ✓, but then needs
  LNSubRed.noPromoAt "x" Γ [.top] (fvar "x") (.lam .top .top),
  which is impossible: ms_pro needs z≠"x" (fails), ms_top needs
  target = .top (target is .lam .top .top), ms_equ needs
  LNEquivRed.noPromoAt "x" Γ [.top] (fvar "x") (.lam .top .top)
  which has no applicable constructor for fvar "x" → .lam .top .top.

Root cause: `x ∉ dom Γ` allows x to appear in Γ's annotations,
so promotion chains through other variables can reach x's annotation.
Fix: strengthen to `x ∉ LNCtx.all_fvs Γ`, which implies both
x ∉ dom Γ AND x does not appear in any annotation in Γ. -/

/-- commutativity_noPromoAt is FALSE: the noPromoAt conclusion is
    underivable even when the hypothesis holds. -/
theorem commutativity_noPromoAt_false :
    ¬ LNEquivRed.noPromoAt "x" [("x", .equiv .top)] [] (.fvar "x") .top := by
  intro h_np
  cases h_np with
  | me_pro hne _ _ => exact hne rfl

/-- The derivation that the old axiom would apply to does exist. -/
theorem commutativity_noPromoAt_false_deriv :
    LNEquivRed [("x", .equiv .top)] [] (.fvar "x") .top :=
  .me_pro (by simp [LNCtx.mem_equiv, LNCtx.lookup']) (.ms_equ .me_top)

/-! #### Counterexample: me_bet_body_noPromoAt (strengthened) is STILL FALSE

The strengthened axiom `me_bet_body_noPromoAt` requires `x ∉ all_fvs(Γ)` and
`x ∉ dom.fvs`, but this is still insufficient. The failure mode:

The body `body^x` may contain `fvar x` (from opening bvar 0). If the body
applies an inner lambda to `fvar x`, ME-APP pushes `fvar x` onto the stack.
ME-FOP then pops it into a fresh variable's `.equiv (fvar x)` annotation.
ME-PRO on that fresh variable triggers SubRed of `fvar x`, which uses MS-PRO
on x (since x has .sub in the context), violating noPromoAt.

Concrete instance:
  Γ = [], dom = lam ⊤ ⊤, x = "x", s = [⊤]
  body = app (lam ⊤ (bvar 0)) (bvar 0)
  body^x = app (lam ⊤ (bvar 0)) (fvar "x")

Derivation: ME-APP pushes fvar "x" onto stack [fvar "x", ⊤].
  Then ME-FOP pops fvar "x", introducing (y, .equiv (fvar "x")).
  Body fvar y reduces via ME-PRO on y: y ≡ fvar "x", then
  SubRed of fvar "x" via MS-PRO on "x": "x" ≤ (lam ⊤ ⊤) → lam ⊤ ⊤.
  Result for fvar y: lam ⊤ ⊤.
  ME-FOP conclusion: lam ⊤ (lam ⊤ ⊤).
  ME-APP conclusion: app (lam ⊤ (lam ⊤ ⊤)) (fvar "x").

noPromoAt is impossible because the only path to the output
  app (lam ⊤ (lam ⊤ ⊤)) (fvar "x")
requires SubRed.noPromoAt for fvar "x" → lam ⊤ ⊤,
which has no applicable constructor:
  ms_pro needs z ≠ x (fails, z = x),
  ms_top needs output ⊤ (output is lam ⊤ ⊤),
  ms_equ needs EquivRed.noPromoAt for fvar "x" → lam ⊤ ⊤ (impossible).
-/

private abbrev cex_dom := LNExpr.lam .top .top
private abbrev cex_body := LNExpr.lam .top (.bvar 0)
private abbrev cex_ctx := [("x", LNAnn.sub cex_dom)]
private abbrev cex_result := LNExpr.lam .top (.lam .top .top)

/-- The body^x term: lam ⊤ (bvar 0) (the inner bvar 0 refers to the inner
    binder, not x, so opening is identity). -/
private theorem cex_body_open :
    cex_body.open_at 0 (.fvar "x") = .lam .top (.bvar 0) := by
  native_decide

/-- The derivation exists: lam ⊤ (bvar 0) ≡→ lam ⊤ (lam ⊤ ⊤) under
    stack [fvar "x"]. ME-FOP pops fvar "x", fresh y gets .equiv (fvar "x"),
    body fvar y ≡→ lam ⊤ ⊤ via ME-PRO on y → SubRed(fvar "x") → MS-PRO → dom. -/
private theorem me_bet_body_noPromoAt_false_deriv :
    LNEquivRed cex_ctx [.fvar "x"]
      (.lam .top (.bvar 0)) (.lam .top (.lam .top .top)) := by
  apply LNEquivRed.me_fop (L := ["x"])
  · exact LNEquivRed.me_top  -- dom: ⊤ ≡→ ⊤
  · intro y hy
    have hne : y ≠ "x" := fun h => hy (h ▸ List.mem_cons_self _ _)
    simp only [LNExpr.open_at]
    -- ME-PRO on y: y ≡ fvar "x"
    apply LNEquivRed.me_pro
    · show LNCtx.mem_equiv ((y, .equiv (.fvar "x")) :: cex_ctx) y (.fvar "x")
      simp [LNCtx.mem_equiv, LNCtx.lookup']
    · -- SubRed of fvar "x" via MS-PRO: "x" ≤ (lam ⊤ ⊤)
      apply LNSubRed.ms_pro
      show LNCtx.mem_sub ((y, .equiv (.fvar "x")) :: cex_ctx) "x" cex_dom
      simp [LNCtx.mem_sub, LNCtx.lookup', cex_ctx, cex_dom, bne_iff_ne, hne, Ne.symm hne]

/-- Freshness: "x" ∉ all_fvs []. -/
private theorem cex_fresh_ctx : "x" ∉ LNCtx.all_fvs ([] : LNCtx) := by
  simp [LNCtx.all_fvs]

/-- Freshness: "x" ∉ fvs(lam ⊤ ⊤). -/
private theorem cex_fresh_dom : "x" ∉ cex_dom.fvs := by
  simp [cex_dom, LNExpr.fvs]

/-- SubRed.noPromoAt "x" for fvar "x" → lam ⊤ ⊤ is impossible
    (regardless of context/stack): ms_pro needs z ≠ x, ms_top needs
    output = ⊤, ms_equ needs equiv_noPromoAt which also fails. -/
private theorem sub_noPromoAt_fvar_x_lam_impossible
    {Γ : LNCtx} {s : LNStack}
    : ¬ LNSubRed.noPromoAt "x" Γ s (.fvar "x") (.lam .top .top) := by
  intro h
  cases h with
  | ms_pro hne _ => exact hne rfl
  | ms_equ h_eq =>
    cases h_eq with
    | me_pro hne _ _ => exact hne rfl

/-- me_bet_body_noPromoAt is FALSE even with the strengthened freshness
    conditions x ∉ all_fvs(Γ) and x ∉ dom.fvs.
    Counterexample: body = lam ⊤ (bvar 0), Γ = [], dom = lam ⊤ ⊤,
    s = [fvar "x"]. The stack carries fvar "x" which ME-FOP captures in a
    fresh variable's .equiv annotation. The fresh variable then promotes via
    ME-PRO, triggering SubRed(fvar "x") → MS-PRO(x) → dom = lam ⊤ ⊤. -/
theorem me_bet_body_noPromoAt_false :
    ¬ LNEquivRed.noPromoAt "x" cex_ctx [.fvar "x"]
      (.lam .top (.bvar 0)) (.lam .top (.lam .top .top)) := by
  intro h
  -- Input .lam .top (.bvar 0), output .lam .top (.lam .top .top), stack [fvar "x"].
  -- Only me_fop matches (lam input with non-empty stack).
  cases h with
  | @me_fop _ _ _ _ _ _ _ L h_dom h_body =>
    -- h_body : ∀ y ∉ L, noPromoAt "x" [(y, .equiv (fvar "x")), ("x", .sub cex_dom)]
    --   [] ((bvar 0)^y) ((lam ⊤ ⊤)^y)
    obtain ⟨y, hy⟩ := exists_fresh_string (L ++ ["x"])
    have hy_L : y ∉ L := fun h => hy (List.mem_append_left _ h)
    have hy_ne_x : y ≠ "x" := fun h => hy (List.mem_append_right _ (h ▸ List.mem_cons_self _ _))
    have h_np := h_body y hy_L
    -- Simplify: (bvar 0)^y = fvar y, (lam ⊤ ⊤)^y = lam ⊤ ⊤
    simp only [LNExpr.open_at] at h_np
    -- h_np : noPromoAt "x" [(y, .equiv (fvar "x")), ...] [] (fvar y) (.lam .top .top)
    -- For fvar y → lam ⊤ ⊤: only me_pro can match (me_var gives fvar y)
    cases h_np with
    | me_pro hne hmem h_sub_np =>
      -- hmem : mem_equiv ((y, .equiv (fvar "x")) :: cex_ctx) z α
      -- z is the promoted variable. Since the context is
      -- [(y, .equiv (fvar "x")), ("x", .sub (lam .top .top))],
      -- and mem_equiv requires .equiv annotation, z must be y and α = fvar "x".
      -- (z = "x" has .sub, z ∉ {y, "x"} gives empty lookup)
      unfold LNCtx.mem_equiv LNCtx.lookup' at hmem
      -- hmem now involves if-then-else on y == z
      -- If y = z, then α = .fvar "x"
      -- If y ≠ z, lookup in cex_ctx for .equiv gives contradiction
      split at hmem
      · -- y = z case: hmem : some (.equiv (fvar "x")) = some (.equiv α)
        cases hmem; exact sub_noPromoAt_fvar_x_lam_impossible h_sub_np
      · -- y ≠ z case: lookup in cex_ctx for .equiv gives contradiction
        -- cex_ctx = [("x", .sub (lam ⊤ ⊤))], so "x" has .sub not .equiv, and
        -- any other variable is not in the context at all.
        simp [cex_ctx, LNCtx.lookup'] at hmem

/-- me_bet_body_noPromoAt (strengthened) is STILL FALSE: there exist
    concrete Γ, s, x, dom, body, u satisfying all premises but violating
    the noPromoAt conclusion. -/
theorem me_bet_body_noPromoAt_strengthened_false :
    ∃ (Γ : LNCtx) (s : LNStack) (x : String) (dom body u : LNExpr),
      LNEquivRed ((x, .sub dom) :: Γ) s (body.open_at 0 (.fvar x)) u ∧
      x ∉ LNCtx.all_fvs Γ ∧
      x ∉ dom.fvs ∧
      ¬ LNEquivRed.noPromoAt x ((x, .sub dom) :: Γ) s (body.open_at 0 (.fvar x)) u :=
  ⟨[], [.fvar "x"], "x", cex_dom, cex_body, cex_result,
   by rw [cex_body_open]; exact me_bet_body_noPromoAt_false_deriv,
   cex_fresh_ctx,
   cex_fresh_dom,
   by rw [cex_body_open]; exact me_bet_body_noPromoAt_false⟩

/-! The former axioms `me_bet_body_noPromoAt` and `commutativity_noPromoAt`
have been REMOVED. They were proved FALSE (see counterexamples above:
`me_bet_body_noPromoAt_false`, `me_bet_body_noPromoAt_strengthened_false`,
`commutativity_noPromoAt_false`, `commutativity_noPromoAt_strengthened_false`).

The correct formulation co-proves noPromoAt preservation WITH commutativity
as part of the strengthened return type (the `∀ x, noPromoAt ...` clause).
The ME-BET/MS-FOP case in commutativity now sorry's the annotation swaps
inline, to be resolved as part of the full mutual induction. -/

/-- commutativity_noPromoAt (strengthened) is STILL FALSE.
    The existing counterexamples `commutativity_noPromoAt_false` and
    `commutativity_noPromoAt_false_deriv` directly refute the strengthened
    version: Γ = [], ann = .equiv .top, x = "x", s = [], e = fvar "x", u = .top.
    The freshness conditions are trivially satisfied:
      "x" ∉ all_fvs [] = "x" ∉ [] ✓
      "x" ∉ (.equiv .top).fvs = "x" ∉ [] ✓
    Yet `noPromoAt "x" [("x", .equiv .top)] [] (fvar "x") .top` is impossible
    because ME-PRO on "x" is the only derivation path (since x has .equiv .top),
    and noPromoAt.me_pro requires z ≠ "x" which fails for z = "x". -/
theorem commutativity_noPromoAt_strengthened_false :
    ∃ (Γ : LNCtx) (s : LNStack) (x : String) (ann : LNAnn) (e u : LNExpr),
      LNEquivRed ((x, ann) :: Γ) s e u ∧
      x ∉ LNCtx.all_fvs Γ ∧
      x ∉ ann.fvs ∧
      ¬ LNEquivRed.noPromoAt x ((x, ann) :: Γ) s e u :=
  ⟨[], [], "x", .equiv .top, .fvar "x", .top,
   commutativity_noPromoAt_false_deriv,
   by simp [LNCtx.all_fvs],
   by simp [LNAnn.fvs, LNExpr.fvs],
   commutativity_noPromoAt_false⟩

/-- Inversion on LNCtxRed for stack cons:
    If Γ; α::s ↦ Γ'; s', then s' = α'::s₁ and Γ;s ↦ Γ';s₁
    and Γ;[] ⊢ α ≡→ α'.
    Proved by induction on the context reduction, using equivRed_ctx_ext
    to lift the equiv-red witness through context annotation layers. -/
theorem ctxRed_stack_inv
    {Γ : LNCtx} {α : LNExpr} {s : LNStack} {Γ' : LNCtx} {s' : LNStack}
    (h : LNCtxRed Γ (α :: s) Γ' s')
    (hnd : (LNCtx.dom Γ).Nodup)
    : ∃ α' s₁, s' = α' :: s₁ ∧ LNCtxRed Γ s Γ' s₁ ∧ LNEquivRed Γ [] α α' := by
  generalize hs : α :: s = stk at h
  induction h with
  | @ct_ann_sub Γ_i _ Γ_i' _ y u u' hctx_i hred_u ih =>
    have hnd_inner : (LNCtx.dom Γ_i).Nodup :=
      (List.nodup_cons.mp hnd).2
    have hy_fresh : y ∉ LNCtx.dom Γ_i :=
      (List.nodup_cons.mp hnd).1
    obtain ⟨α', s₁, hs'eq, hctx', hα_red⟩ := ih hnd_inner hs
    exact ⟨α', s₁, hs'eq,
      .ct_ann_sub hctx' hred_u,
      equivRed_ctx_ext hα_red hy_fresh⟩
  | @ct_ann_equiv Γ_i _ Γ_i' _ y β β' hctx_i hred_β ih =>
    have hnd_inner : (LNCtx.dom Γ_i).Nodup :=
      (List.nodup_cons.mp hnd).2
    have hy_fresh : y ∉ LNCtx.dom Γ_i :=
      (List.nodup_cons.mp hnd).1
    obtain ⟨α', s₁, hs'eq, hctx', hα_red⟩ := ih hnd_inner hs
    exact ⟨α', s₁, hs'eq,
      .ct_ann_equiv hctx' hred_β,
      equivRed_ctx_ext hα_red hy_fresh⟩
  | @ct_stk Γ_i _ Γ_i' s₁ α₀ α₀' hctx_i hred_α _ =>
    cases hs; exact ⟨α₀', s₁, rfl, hctx_i, hred_α⟩
  | ct_nil => cases hs


/-! ### Diamond property (Lemma 2)

Proof by induction on the term structure of t₀, case analysis on the pair
of rules applied by h1 and h2.  Follows Appendix A of Pasquale & Garcia-Perez.
-/

-- diamond_full: this proof does case analysis on pairs of cofinite-quantified
-- constructors. With the refactoring from existential to cofinite quantification,
-- the pattern matching and variable management changes significantly.
-- The proof strategy is the same (pick a common fresh variable from the
-- intersection of the L sets, instantiate both cofinite premises at that x,
-- then proceed as before). Temporarily sorry'd pending adaptation.
-- The key insight enabled by cofinite: when both h1 and h2 use binder rules
-- with sets L₁ and L₂, we pick x ∉ L₁ ∪ L₂ ∪ dom(Γ) ∪ ... and instantiate
-- both, eliminating the need for equivRed_rename entirely.

theorem diamond_full
    (t₀ : LNExpr)
    {Γ Γ₁ Γ₂ : LNCtx} {s s₁ s₂ : LNStack} {t₁ t₂ : LNExpr}
    (h1 : LNEquivRed Γ s t₀ t₁) (h2 : LNEquivRed Γ s t₀ t₂)
    (hctx1 : LNCtxRed Γ s Γ₁ s₁) (hctx2 : LNCtxRed Γ s Γ₂ s₂)
    : ∃ t₃, LNEquivRed Γ₁ s₁ t₁ t₃ ∧ LNEquivRed Γ₂ s₂ t₂ t₃ := by
  sorry

/-- Diamond (one-context version used by commutativity).
    Derived from `diamond_full` by using `ctxRed_refl` for one context. -/
theorem diamond
    {Γ Γ' : LNCtx} {s s' : LNStack} {t₀ t₁ t₂ : LNExpr}
    (h1 : LNEquivRed Γ s t₀ t₁) (h2 : LNEquivRed Γ s t₀ t₂)
    (hctx : LNCtxRed Γ s Γ' s')
    : ∃ t₃, LNEquivRed Γ s t₂ t₃ ∧ LNEquivRed Γ' s' t₁ t₃ := by
  have hid : LNCtxRed Γ s Γ s := ctxRed_refl Γ s sorry sorry  -- sorry: wf witnesses
  obtain ⟨t₃, h_left, h_right⟩ := diamond_full t₀ h2 h1 hid hctx
  exact ⟨t₃, h_left, h_right⟩

/-! ### Commutativity (Lemma 1)

The main theorem. By induction on the term t₀ and case analysis on the
pair of rules (h_equiv : ≡→, h_sub : ≤→) applied to t₀.

Proof structure follows Appendix A of Pasquale & Garcia-Perez.

We make t₀ explicit so we can use `termination_by t₀.sz`.
The decrease `sz (open_at 0 (fvar x) body) < sz (lam dom body)`
follows from `sz_open_at_fvar` and arithmetic.
-/

set_option maxHeartbeats 1600000 in
theorem commutativity
    (t₀ : LNExpr)
    {Γ : LNCtx} {s : LNStack} {t₁ t₂ : LNExpr}
    {Γ' : LNCtx} {s' : LNStack}
    (h_equiv : LNEquivRed Γ s t₀ t₁)
    (h_sub   : LNSubRed Γ s t₀ t₂)
    (h_ctx   : LNCtxRed Γ s Γ' s')
    (h_lc    : t₀.lc)
    (h_nd    : (LNCtx.dom Γ).Nodup)
    : ∃ t₃ : LNExpr, LNEquivRed Γ s t₂ t₃ ∧ LNSubRed Γ' s' t₁ t₃ ∧
        (∀ x, LNSubRed.noPromoAt x Γ s t₀ t₂ → LNSubRed.noPromoAt x Γ' s' t₁ t₃) := by
  -- Case analysis on the sub (left/vertical) edge.
  cases h_sub with

  --===================================================================
  -- MS-TOP: t₂ = .top
  --===================================================================
  | ms_top => exact ⟨.top, .me_top, .ms_top, fun _ _ => .ms_top⟩

  --===================================================================
  -- MS-EQU: t₂ comes from Γ;s ⊢ t₀ ≡→ t₂
  --===================================================================
  | ms_equ h_eq2 =>
    obtain ⟨t₃, htop, hright⟩ := diamond h_equiv h_eq2 h_ctx
    exact ⟨t₃, htop, .ms_equ hright, sorry⟩  -- sorry: noPromoAt preservation for MS-EQU/diamond case

  --===================================================================
  -- MS-PRO: t₀ = fvar x, t₂ = t where x ≤ t ∈ Γ
  --===================================================================
  | ms_pro hmem =>
    cases h_equiv with
    | me_pro hmem_equiv _ => exact absurd (no_sub_and_equiv hmem hmem_equiv) False.elim
    | me_var =>
      -- ctxRed_lookup_sub: from x ≤ t ∈ Γ and Γ;s ↦ Γ';s', get t' with
      -- x ≤ t' ∈ Γ' and LNEquivRed Γ [] t t' (context extension via
      -- equivRed_ctx_ext, empty stack from CT-ANN definition).
      obtain ⟨t', hmem', ht_red⟩ := ctxRed_lookup_sub hmem h_ctx h_nd
      -- Top edge needs: LNEquivRed Γ s t t' (stack s, not [])
      -- Right edge:     LNSubRed Γ' s' (fvar x) t' via ms_pro hmem' ✓
      --
      -- The top edge sorry is restricted stack extension for annotation
      -- terms: we have LNEquivRed Γ [] t t' and need LNEquivRed Γ s t t'.
      -- This holds because annotation terms in well-formed contexts are
      -- "stack-stable" (their reduction doesn't depend on the stack), but
      -- proving this requires formalizing context well-formedness.
      -- Note: this is NOT the false equivRed_weaken (which changes BOTH
      -- context and stack via CtxRed). Here the context stays as Γ; only
      -- the stack changes from [] to s.
      exact ⟨t', sorry, .ms_pro hmem', sorry⟩  -- sorry: stack extension for annotation terms + noPromoAt

  --===================================================================
  -- MS-APP: t₀ = app u₀ v, t₂ = app u₂ v
  --===================================================================
  | @ms_app _ _ u₀ u₂ v h_sub_u =>
    cases h_equiv with
    ---------------------------------------------------------------
    -- ME-APP / MS-APP
    ---------------------------------------------------------------
    | @me_app _ _ _ u₁ _ v₁ h_equiv_u h_equiv_v =>
      have h_ctx_ext := LNCtxRed.ct_stk h_ctx h_equiv_v
      have hu₀_lc : u₀.lc := h_lc.1
      obtain ⟨u₃, htop_u, hright_u, hnp_u⟩ :=
        commutativity u₀ h_equiv_u h_sub_u h_ctx_ext hu₀_lc h_nd
      exact ⟨.app u₃ v₁, .me_app htop_u h_equiv_v, .ms_app hright_u, sorry⟩  -- sorry: noPromoAt preservation for ME-APP/MS-APP
    ---------------------------------------------------------------
    -- ME-BET / MS-APP: the key case
    -- h_equiv: me_bet L_e h_body_e h_v_e
    --   gives Γ;s ⊢ (lam dom body) v ≡→ t_e.open_at 0 v'
    -- h_sub_u: Γ; v::s ⊢ lam dom body ≤→ u₂
    ---------------------------------------------------------------
    | @me_bet _ _ dom body t_e _ v' L_e h_body_e h_v_e =>
      cases h_sub_u with
      | ms_top =>
        exact ⟨.top, .me_tap, .ms_top, fun _ _ => .ms_top⟩
      | ms_equ h_eq_lam =>
        have hv_lc : v.lc := h_lc.2
        have h_equiv2 : LNEquivRed Γ s (.app (.lam dom body) v) (.app u₂ v) :=
          .me_app h_eq_lam (equivRed_refl Γ [] v hv_lc)
        have h_equiv_orig : LNEquivRed Γ s (.app (.lam dom body) v) (t_e.open_at 0 v') :=
          .me_bet L_e h_body_e h_v_e
        obtain ⟨t₃, htop, hright⟩ := diamond h_equiv_orig h_equiv2 h_ctx
        exact ⟨t₃, htop, .ms_equ hright, sorry⟩  -- sorry: noPromoAt preservation for ME-BET/MS-EQU
      | @ms_fop _ _ _ _ _ body₂ L_s h_sub_body_s =>
        -- h_sub_body_s : ∀ y, y ∉ L_s → LNSubRed ((y, .equiv v) :: Γ) s (body^y) (body₂^y)
        -- h_body_e : ∀ x, x ∉ L_e → LNEquivRed ((x, .sub dom) :: Γ) s (body^x) (t_e^x)
        -- Pick x fresh for L_e, L_s, all_fvs(Γ), dom(Γ'), dom.fvs, v.fvs
        obtain ⟨x, hx⟩ := exists_fresh_string (L_e ++ L_s ++ LNCtx.all_fvs Γ ++ LNCtx.dom Γ' ++ dom.fvs ++ v.fvs)
        have hx_Le : x ∉ L_e := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))))
        have hx_Ls : x ∉ L_s := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
        have hx_all_fvs : x ∉ LNCtx.all_fvs Γ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
        have hx_dom' : x ∉ LNCtx.dom Γ' := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
        have _hx_dom_fvs : x ∉ dom.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_right _ h))
        have hx_dom : x ∉ LNCtx.dom Γ := LNCtx.not_mem_dom_of_not_mem_all_fvs hx_all_fvs
        have _hx_v_fvs : x ∉ v.fvs := fun h => hx (List.mem_append_right _ h)
        -- Instantiate the cofinite premises at x
        have h_body_e_x := h_body_e x hx_Le
        -- h_body_e_x : LNEquivRed ((x, .sub dom) :: Γ) s (body^x) (t_e^x)
        have h_sub_body_s_x := h_sub_body_s x hx_Ls
        -- h_sub_body_s_x : LNSubRed ((x, .equiv v) :: Γ) s (body^x) (body₂^x)
        -- Change annotation on h_body_e_x from .sub to .equiv.
        -- The old `me_bet_body_noPromoAt` axiom was FALSE (see counterexamples
        -- above). The correct approach: this annotation swap is sorry'd inline,
        -- to be resolved as part of the mutual induction that co-proves
        -- noPromoAt with commutativity. The key insight is that x is fresh
        -- and has .sub annotation, so ME-PRO on x cannot fire; however,
        -- transitive promotion chains through other variables CAN reach x
        -- via the stack (the counterexample), which is why a standalone axiom
        -- fails but the mutual induction succeeds.
        have h_body_e_eq : LNEquivRed ((x, .equiv v) :: Γ) s
            (body.open_at 0 (.fvar x)) (t_e.open_at 0 (.fvar x)) := by
          sorry  -- annotation swap .sub→.equiv on body; co-proved with noPromoAt in mutual induction
        -- Build context reduction for the body
        have h_ctx_body : LNCtxRed ((x, .equiv v) :: Γ) s ((x, .equiv v') :: Γ') s' :=
          LNCtxRed.ct_ann_equiv h_ctx h_v_e
        have hbody_lc : (body.open_at 0 (.fvar x)).lc :=
          LNExpr.lc_at_open_fvar h_lc.1.2
        -- IH on body^x (strengthened: returns noPromoAt preservation)
        obtain ⟨u₃, htop_body, hright_body, _hnp_ih⟩ :=
          commutativity (body.open_at 0 (.fvar x)) h_body_e_eq h_sub_body_s_x h_ctx_body hbody_lc
            (List.nodup_cons.mpr ⟨hx_dom, h_nd⟩)
        -- Change annotation back from .equiv to .sub for ME-BET.
        -- The old `commutativity_noPromoAt` axiom was FALSE (see counterexamples
        -- above). With the strengthened IH, we can extract noPromoAt from
        -- _hnp_ih: the input sub h_sub_body_s_x doesn't promote x (x is fresh),
        -- so the output sub hright_body also doesn't promote x, and from this
        -- the top edge htop_body also doesn't promote x.
        -- For now this is sorry'd; the noPromoAt transfer from SubRed to EquivRed
        -- requires the full mutual induction.
        have htop_body_sub : LNEquivRed ((x, .sub dom) :: Γ) s
            (body₂.open_at 0 (.fvar x)) u₃ := by
          sorry  -- annotation swap .equiv→.sub on top edge; uses IH noPromoAt preservation
        -- Use t₃ = (u₃.close_at 0 x).open_at 0 v' as the witness
        -- This equals u₃.subst_fvar x v' when u₃ is lc (open_close_subst).
        refine ⟨(u₃.close_at 0 x).open_at 0 v', ?_, ?_, ?_⟩
        · -- Top edge: Γ;s ⊢ app (lam dom body₂) v ≡→ (close x u₃)^v'
          -- By ME-BET with t = u₃.close_at 0 x
          exact .me_bet (L_e ++ L_s ++ LNCtx.dom Γ ++ LNCtx.dom Γ')
            (fun y hy => by
              -- htop_body_sub : Equiv ((x,.sub dom)::Γ) s (body₂^x) u₃
              -- Use equivRed_rename to get it for y
              have hy_dom : y ∉ LNCtx.dom Γ := fun h =>
                hy (List.mem_append_left _ (List.mem_append_right _ h))
              have h := equivRed_rename htop_body_sub hx_dom hy_dom (sorry : x ∉ body₂.fvs)
              -- h : Equiv ((y,.sub dom)::Γ) s (body₂^y) (u₃.subst_fvar x (fvar y))
              -- (close x u₃)^y = u₃.subst_fvar x (fvar y) by open_close_subst
              rw [open_close_subst (sorry : u₃.lc)]  -- sorry: u₃.lc
              exact h)
            h_v_e
        · -- Right edge: Γ';s' ⊢ t_e^v' ≤→ (close x u₃)^v'
          -- hright_body : LNSubRed ((x,.equiv v')::Γ') s' (t_e^x) u₃
          -- By subRed_subst: Γ';s' ⊢ (t_e^x)[x↦v'] ≤→ u₃[x↦v']
          -- (t_e^x)[x↦v'] = t_e^v' when x ∉ fvs(t_e) (standard LN fact)
          -- u₃[x↦v'] = (close x u₃)^v' when u₃ is lc (open_close_subst)
          have hright := subRed_subst (ann := .equiv v') (v := v') hright_body hx_dom'
          -- hright : Γ';s' ⊢ (t_e^x)[x↦v'] ≤→ u₃[x↦v']
          -- Rewrite using subst_open and open_close_subst_expr
          -- sorry: x ∉ fvs(t_e) (x is fresh, t_e is a binder body from the input)
          have heq_lhs : (t_e.open_at 0 (.fvar x)).subst_fvar x v' = t_e.open_at 0 v' :=
            subst_open (sorry : x ∉ t_e.fvs)
          -- sorry: u₃ is locally closed (reduction preserves lc)
          have heq_rhs : u₃.subst_fvar x v' = (u₃.close_at 0 x).open_at 0 v' :=
            (open_close_subst_expr (sorry : u₃.lc)).symm
          rw [heq_lhs, heq_rhs] at hright
          exact hright
        · -- noPromoAt preservation for ME-BET/MS-FOP case
          sorry  -- co-proved with the mutual induction
    ---------------------------------------------------------------
    -- ME-TAP / MS-APP
    ---------------------------------------------------------------
    | me_tap =>
      have := top_sub_inv h_sub_u; subst this
      exact ⟨.top, .me_tap, .ms_top, fun _ _ => .ms_top⟩

  --===================================================================
  -- MS-FUN: t₀ = lam dom body, s = [],
  -- t₂ = lam dom body₂
  --===================================================================
  | @ms_fun _ dom body body₂ L_s h_sub_body_s =>
    cases h_equiv with
    ---------------------------------------------------------------
    -- ME-FUN / MS-FUN: Both go under the binder with empty stack.
    ---------------------------------------------------------------
    | @me_fun _ _ dom' _ body₁ L_e h_equiv_dom h_equiv_body_e =>
      -- Pick x fresh for both avoidance sets and everything else we need
      obtain ⟨x, hx⟩ := exists_fresh_string (L_e ++ L_s ++ LNCtx.dom Γ ++ LNCtx.dom Γ')
      have hx_Le : x ∉ L_e := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
      have hx_Ls : x ∉ L_s := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
      have hx_dom : x ∉ LNCtx.dom Γ := fun h => hx (List.mem_append_left _ (List.mem_append_right _ h))
      have hx_dom' : x ∉ LNCtx.dom Γ' := fun h => hx (List.mem_append_right _ h)
      -- Instantiate both cofinite premises at x
      have h_equiv_body_x := h_equiv_body_e x hx_Le
      have h_sub_body_x := h_sub_body_s x hx_Ls
      -- Build context reduction for the body
      have h_ctx_nil := ctxRed_nil_of_ctxRed h_ctx
      have h_ctx_body : LNCtxRed ((x, .sub dom) :: Γ) [] ((x, .sub dom') :: Γ') [] :=
        LNCtxRed.ct_ann_sub h_ctx_nil h_equiv_dom
      have hbody_lc : (body.open_at 0 (.fvar x)).lc :=
        LNExpr.lc_at_open_fvar h_lc.2
      -- IH on body^x
      obtain ⟨u₃, htop_body, hright_body, _hnp_ih⟩ :=
        commutativity (body.open_at 0 (.fvar x)) h_equiv_body_x h_sub_body_x h_ctx_body hbody_lc
          (List.nodup_cons.mpr ⟨hx_dom, h_nd⟩)
      have hs' := ctxRed_nil_stack h_ctx; subst hs'
      refine ⟨.lam dom' (u₃.close_at 0 x), ?_, ?_, ?_⟩
      · -- Top edge: Γ;[] ⊢ lam dom body₂ ≡→ lam dom' (close x u₃)
        -- htop_body : LNEquivRed ((x,.sub dom)::Γ) [] (body₂^x) u₃
        -- Use equivRed_rename to get the body premise for any y
        exact .me_fun (L_e ++ L_s ++ LNCtx.dom Γ ++ LNCtx.dom Γ')
          h_equiv_dom
          (fun y hy => by
            have hy_dom : y ∉ LNCtx.dom Γ := fun h =>
              hy (List.mem_append_left _ (List.mem_append_right _ h))
            have h := equivRed_rename htop_body hx_dom hy_dom (sorry : x ∉ body₂.fvs)
            -- h : LNEquivRed ((y,.sub dom)::Γ) [] (body₂^y) (u₃.subst_fvar x (fvar y))
            -- Need: ... (body₂^y) ((close x u₃)^y)
            -- (close x u₃)^y = u₃.subst_fvar x (fvar y) by open_close_subst (needs u₃.lc)
            rw [open_close_subst (sorry : u₃.lc)]  -- sorry: u₃.lc (reduction preserves lc)
            exact h)
      · -- Right edge: Γ';[] ⊢ lam dom' body₁ ≤→ lam dom' (close x u₃)
        -- hright_body : LNSubRed ((x,.sub dom')::Γ') [] (body₁^x) u₃
        -- Use subRed_rename to get the body premise for any y
        exact .ms_fun (L_e ++ L_s ++ LNCtx.dom Γ ++ LNCtx.dom Γ')
          (fun y hy => by
            have hy_dom' : y ∉ LNCtx.dom Γ' := fun h =>
              hy (List.mem_append_right _ h)
            have h := subRed_rename hright_body hx_dom' hy_dom' (sorry : x ∉ body₁.fvs)
            -- h : LNSubRed ((y,.sub dom')::Γ') [] (body₁^y) (u₃.subst_fvar x (fvar y))
            rw [open_close_subst (sorry : u₃.lc)]  -- sorry: u₃.lc
            exact h)
      · -- noPromoAt preservation for ME-FUN/MS-FUN
        sorry

  --===================================================================
  -- MS-FOP: t₀ = lam dom body, s = α::s₀,
  -- t₂ = lam dom body₂
  --===================================================================
  | @ms_fop _ s_inner α dom body body₂ L_s h_sub_body_s =>
    cases h_equiv with
    ---------------------------------------------------------------
    -- ME-FOP / MS-FOP: Both pop α from the stack.
    ---------------------------------------------------------------
    | @me_fop _ _ _ _ dom' _ body₁ L_e h_equiv_dom h_equiv_body_e =>
      obtain ⟨x, hx⟩ := exists_fresh_string (L_e ++ L_s ++ LNCtx.dom Γ ++ LNCtx.dom Γ')
      have hx_Le : x ∉ L_e := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
      have hx_Ls : x ∉ L_s := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
      have hx_dom : x ∉ LNCtx.dom Γ := fun h => hx (List.mem_append_left _ (List.mem_append_right _ h))
      have hx_dom' : x ∉ LNCtx.dom Γ' := fun h => hx (List.mem_append_right _ h)
      have h_equiv_body_x := h_equiv_body_e x hx_Le
      have h_sub_body_x := h_sub_body_s x hx_Ls
      obtain ⟨α', s₁, hs'eq, h_ctx_inner, hα_red⟩ := ctxRed_stack_inv h_ctx h_nd
      subst hs'eq
      have h_ctx_body : LNCtxRed ((x, .equiv α) :: Γ) s_inner ((x, .equiv α') :: Γ') s₁ :=
        LNCtxRed.ct_ann_equiv h_ctx_inner hα_red
      have hbody_lc : (body.open_at 0 (.fvar x)).lc :=
        LNExpr.lc_at_open_fvar h_lc.2
      obtain ⟨u₃, htop_body, hright_body, _hnp_ih⟩ :=
        commutativity (body.open_at 0 (.fvar x)) h_equiv_body_x h_sub_body_x h_ctx_body hbody_lc
          (List.nodup_cons.mpr ⟨hx_dom, h_nd⟩)
      have _hfresh_e' : x ∉ LNCtx.dom Γ' := hx_dom'
      refine ⟨.lam dom' (u₃.close_at 0 x), ?_, ?_, ?_⟩
      · -- Top edge: use equivRed_rename on htop_body
        exact .me_fop (L_e ++ L_s ++ LNCtx.dom Γ ++ LNCtx.dom Γ')
          h_equiv_dom
          (fun y hy => by
            have hy_dom : y ∉ LNCtx.dom Γ := fun h =>
              hy (List.mem_append_left _ (List.mem_append_right _ h))
            have h := equivRed_rename htop_body hx_dom hy_dom (sorry : x ∉ body₂.fvs)
            rw [open_close_subst (sorry : u₃.lc)]  -- sorry: u₃.lc
            exact h)
      · -- Right edge: use subRed_rename on hright_body
        exact .ms_fop (L_e ++ L_s ++ LNCtx.dom Γ ++ LNCtx.dom Γ')
          (fun y hy => by
            have hy_dom' : y ∉ LNCtx.dom Γ' := fun h =>
              hy (List.mem_append_right _ h)
            have h := subRed_rename hright_body hx_dom' hy_dom' (sorry : x ∉ body₁.fvs)
            rw [open_close_subst (sorry : u₃.lc)]  -- sorry: u₃.lc
            exact h)
      · -- noPromoAt preservation for ME-FOP/MS-FOP
        sorry
termination_by t₀.sz
decreasing_by all_goals simp_all [LNExpr.sz, sz_open_at_fvar]; omega

/-! ## Investigation: stack extension is FALSE

The former axiom `equivRed_stack_ext` claimed:
  `LNEquivRed Γ [] u v → LNEquivRed Γ s u v`

The critical case is ME-FUN: under `Γ; []`, a lambda `lam dom body` reduces
via ME-FUN with body context `(x, .sub dom) :: Γ; []`. Under `Γ; α :: s`,
ME-FOP fires with body context `(x, .equiv α) :: Γ; s`.

KEY QUESTION: can the body derivation under `.sub dom` always be replayed
under `.equiv α` for arbitrary `α`?

ANALYSIS: YES, because:
1. ME-PRO on `x` requires `.equiv`, so it CANNOT fire under `.sub dom`.
   Therefore the body's EquivRed derivation never promotes `x` via ME-PRO.
2. SubRed on `fvar x` (via MS-PRO) can only be reached through ME-PRO on
   OTHER variables whose annotations contain `fvar x`. But `x` is fresh
   (cofinite quantification), so no annotation in `Γ` contains `fvar x`.
3. Therefore the body derivation is independent of `x`'s annotation.
4. A generalized stack-append lemma would handle the ME-APP case.

The following examples test specific instances to verify consistency.
-/

section StackExtInvestigation

-- Test 1: identity function (lam top (bvar 0))
-- Under []: ME-FUN, body fvar x ≡→ fvar x via ME-VAR
-- Under [α]: ME-FOP, body fvar x ≡→ fvar x via ME-VAR (annotation irrelevant)
example : LNEquivRed [] [] (.lam .top (.bvar 0)) (.lam .top (.bvar 0)) := by
  exact .me_fun (L := [])
    .me_top
    (fun x _ => .me_var)

example : LNEquivRed [] [.top] (.lam .top (.bvar 0)) (.lam .top (.bvar 0)) := by
  exact .me_fop (L := [])
    .me_top
    (fun x _ => .me_var)

-- Test 2: nested lambda, body uses fvar y from outer context (not x)
-- Under []: ME-FUN with (x, .sub top), body fvar y ≡→ fvar y via ME-VAR
-- Under [α]: ME-FOP with (x, .equiv α), body fvar y ≡→ fvar y via ME-VAR
-- Annotation of x is irrelevant because body only references y
example : LNEquivRed [("y", .equiv .top)] []
    (.lam .top (.fvar "y")) (.lam .top (.fvar "y")) := by
  exact .me_fun (L := ["y"])
    .me_top
    (fun x _ => .me_var)

example : LNEquivRed [("y", .equiv .top)] [.top]
    (.lam .top (.fvar "y")) (.lam .top (.fvar "y")) := by
  exact .me_fop (L := ["y"])
    .me_top
    (fun x _ => .me_var)

-- Test 3: ME-PRO on y (not x) in body — annotation of x still irrelevant
-- body: fvar y ≡→ top' via ME-PRO (y ≡ top ∈ Γ, then top ≤→ top via MS-TOP)
-- This works identically regardless of x's annotation
example : LNEquivRed [("y", .equiv .top)] []
    (.lam .top (.fvar "y")) (.lam .top .top) := by
  exact .me_fun (L := ["y"])
    .me_top
    (fun x hx =>
      have hx_ne_y : x ≠ "y" := fun h => hx (h ▸ List.mem_cons_self _ _)
      -- ME-PRO on y: lookup y in ((x, .sub top) :: [(y, .equiv top)])
      .me_pro
        (show LNCtx.mem_equiv ((x, .sub .top) :: [("y", .equiv .top)]) "y" .top by
          unfold LNCtx.mem_equiv LNCtx.lookup'
          simp [hx_ne_y, Ne.symm hx_ne_y]
          native_decide)
        .ms_top)

-- Same derivation under non-empty stack: ME-FOP, same ME-PRO on y
example : LNEquivRed [("y", .equiv .top)] [.top]
    (.lam .top (.fvar "y")) (.lam .top .top) := by
  exact .me_fop (L := ["y"])
    .me_top
    (fun x hx =>
      have hx_ne_y : x ≠ "y" := fun h => hx (h ▸ List.mem_cons_self _ _)
      .me_pro
        (show LNCtx.mem_equiv ((x, .equiv .top) :: [("y", .equiv .top)]) "y" .top by
          unfold LNCtx.mem_equiv LNCtx.lookup'
          simp [hx_ne_y, Ne.symm hx_ne_y]
          native_decide)
        .ms_top)

-- Test 4: application in body — ME-APP pushes onto stack, annotation still irrelevant
-- body = app (fvar y) (fvar x), where y ≡ top ∈ Γ
-- ME-APP: push fvar x, reduce fvar y in stack [fvar x]
-- fvar y ≡→ fvar y via ME-VAR (not using annotation)
-- fvar x ≡→ fvar x via ME-VAR (not using annotation)
-- Result: app (fvar y) (fvar x) ≡→ app (fvar y) (fvar x)
-- body' = app (fvar y) (bvar 0) after closing x

-- Under []:
example : LNEquivRed [("y", .equiv .top)] []
    (.lam .top (.app (.fvar "y") (.bvar 0)))
    (.lam .top (.app (.fvar "y") (.bvar 0))) := by
  exact .me_fun (L := ["y"])
    .me_top
    (fun x _ => .me_app .me_var .me_var)

-- Under [α]:
example : LNEquivRed [("y", .equiv .top)] [.top]
    (.lam .top (.app (.fvar "y") (.bvar 0)))
    (.lam .top (.app (.fvar "y") (.bvar 0))) := by
  exact .me_fop (L := ["y"])
    .me_top
    (fun x _ => .me_app .me_var .me_var)

-- NOTE: Tests 1-4 above are consistent with stack_ext because they never
-- trigger ME-PRO on a variable whose annotation is a lambda that promotes
-- the cofinitely-quantified variable. The counterexample below shows the
-- failure mode.

/-! ### COUNTEREXAMPLE: equivRed_stack_ext and subRed_stack_ext are FALSE

The failure mode involves ME-PRO on a variable x whose annotation α is a lambda.
Under empty stack, SubRed of α uses MS-FUN which gives the cofinitely-quantified
body variable z a `.sub dom` annotation. Under this annotation, MS-PRO on z can
fire, producing `dom` as output. Under non-empty stack, SubRed of α would use
MS-FOP which gives z a `.equiv α_stack` annotation. Under this annotation, MS-PRO
on z CANNOT fire (needs `.sub`), and the result `dom` is unreachable.

Concrete instance:
  Γ = [x ≡ (λy.0), y ≤ ⊤]
  Under Γ;[]: fvar "x" ≡→ λ(fvar "y").(fvar "y")
    via ME-PRO with α = λ(fvar "y").(bvar 0)
    then SubRed via MS-FUN: body z ≤→ fvar "y" via MS-PRO (z ≤ fvar "y")
  Under Γ;[⊤]: ME-PRO would need SubRed Γ [⊤] α α'
    MS-FOP body: z ≡ ⊤, need fvar z ≤→ fvar "y"
    But under .equiv ⊤: MS-PRO fails (need .sub), ME-PRO gives ⊤' not fvar "y"
    Result fvar "y" is UNREACHABLE.
-/

-- The [] derivation EXISTS (verified by Lean):
private def cex_Γ : LNCtx := [("x", .equiv (.lam (.fvar "y") (.bvar 0))), ("y", .sub .top)]

example : LNEquivRed cex_Γ []
    (.fvar "x") (.lam (.fvar "y") (.fvar "y")) := by
  unfold cex_Γ
  exact .me_pro (α := .lam (.fvar "y") (.bvar 0))
    (by simp [LNCtx.mem_equiv, LNCtx.lookup'])
    (.ms_fun (L := ["x", "y"]) (fun z hz => by
      simp [LNExpr.open_at]
      exact .ms_pro (by simp [LNCtx.mem_sub, LNCtx.lookup'])
      ))

-- The [.top] derivation is NOT derivable:
-- LNEquivRed cex_Γ [.top] (.fvar "x") (.lam (.fvar "y") (.fvar "y"))
-- would require LNSubRed cex_Γ [.top] (.lam (.fvar "y") (.bvar 0)) (.lam (.fvar "y") (fvar "y"))
-- which requires MS-FOP body: LNSubRed [(z, .equiv .top), ...] [] (fvar z) (fvar "y")
-- This is unreachable: MS-PRO needs .sub (have .equiv), MS-EQU+ME-PRO gives ⊤' not fvar "y",
-- MS-TOP gives .top not fvar "y", ME-VAR gives fvar z not fvar "y".

-- Similarly, subRed_stack_ext is FALSE:
-- LNSubRed cex_Γ [] (.lam (.fvar "y") (.bvar 0)) (.lam (.fvar "y") (.fvar "y")) holds
-- (via MS-FUN with body MS-PRO), but
-- LNSubRed cex_Γ [.top] (.lam (.fvar "y") (.bvar 0)) (.lam (.fvar "y") (.fvar "y"))
-- does not (MS-FOP body can't reach fvar "y" from fvar z under .equiv .top).

example : LNSubRed cex_Γ []
    (.lam (.fvar "y") (.bvar 0)) (.lam (.fvar "y") (.fvar "y")) := by
  unfold cex_Γ
  exact .ms_fun (L := ["x", "y"]) (fun z hz => by
    simp [LNExpr.open_at]
    exact .ms_pro (by simp [LNCtx.mem_sub, LNCtx.lookup'])
    )

end StackExtInvestigation

/-! ### COUNTEREXAMPLE: equivRed_weaken and subRed_weaken are FALSE

The statement of equivRed_weaken claims: if Γ;s ⊢ u ≡→ v and Γ;s ↦ Γ';s',
then Γ';s' ⊢ u ≡→ v (same u and v). This fails because CtxRed can reduce
an annotation MORE than the original derivation did, making the original
output unreachable in Γ'.

Concrete instance:
  Γ  = [(x ≡ fvar y), (y ≡ ⊤)]
  Γ' = [(x ≡ ⊤),     (y ≡ ⊤)]

  In Γ;[]:  fvar x ≡→ fvar y  via ME-PRO (lookup x → fvar y) + MS-EQU (ME-VAR)
  CtxRed:   x's annotation fvar y reduces to ⊤ via ME-PRO on y, so Γ' has x ≡ ⊤.
  In Γ';[]: Need fvar x ≡→ fvar y. But x ≡ ⊤ now, and:
    - ME-PRO on x gives SubRed of ⊤, which can only reach ⊤ (MS-TOP/ME-TOP),
      never fvar y.
    - ME-VAR gives fvar x, not fvar y.
  So LNEquivRed Γ' [] (fvar x) (fvar y) is NOT derivable.

Root cause: the original derivation used MS-EQU + ME-VAR on the annotation
(α = fvar y ≡→ fvar y, reflexive), but CtxRed non-trivially reduced the
annotation (fvar y → ⊤ via ME-PRO). After this, there is no path from ⊤
back to fvar y.

subRed_weaken is also FALSE by wrapping with MS-EQU.
-/

section WeakenInvestigation

private def weaken_Γ : LNCtx := [("x", .equiv (.fvar "y")), ("y", .equiv .top)]
private def weaken_Γ' : LNCtx := [("x", .equiv .top), ("y", .equiv .top)]

-- Step 1: The original derivation exists.
-- LNEquivRed weaken_Γ [] (fvar "x") (fvar "y")
-- via ME-PRO (lookup x → fvar y) + MS-EQU (ME-VAR on fvar y)
example : LNEquivRed weaken_Γ []
    (.fvar "x") (.fvar "y") := by
  unfold weaken_Γ
  exact .me_pro
    (by simp [LNCtx.mem_equiv, LNCtx.lookup'])
    (.ms_equ .me_var)

-- Step 2: CtxRed from Γ to Γ' is valid.
-- y's annotation ⊤ → ⊤ via ME-TOP.
-- x's annotation fvar y → ⊤ via ME-PRO (lookup y → ⊤) + MS-EQU ME-TOP.
example : LNCtxRed weaken_Γ [] weaken_Γ' [] := by
  unfold weaken_Γ weaken_Γ'
  exact .ct_ann_equiv
    (.ct_ann_equiv .ct_nil .me_top)
    (.me_pro (by simp [LNCtx.mem_equiv, LNCtx.lookup']) (.ms_equ .me_top))

-- Step 3: The weakened conclusion is NOT derivable.
-- LNEquivRed weaken_Γ' [] (fvar "x") (fvar "y") is FALSE.
-- In Γ', x ≡ ⊤. ME-PRO on x can only produce results of SubRed on ⊤,
-- which are ⊤ (MS-TOP, MS-EQU+ME-TOP). ME-VAR gives fvar x.
-- Neither produces fvar y.

-- Similarly for subRed_weaken: LNSubRed weaken_Γ [] (fvar "x") (fvar "y")
-- holds via MS-EQU of the above, but LNSubRed weaken_Γ' [] (fvar "x") (fvar "y")
-- is not derivable for the same reason.
example : LNSubRed weaken_Γ []
    (.fvar "x") (.fvar "y") := by
  unfold weaken_Γ
  exact .ms_equ (.me_pro
    (by simp [LNCtx.mem_equiv, LNCtx.lookup'])
    (.ms_equ .me_var))

end WeakenInvestigation
