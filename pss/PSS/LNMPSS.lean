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
3. `diamond_full`: ME-FUN/ME-FUN and ME-FOP/ME-FOP cases fully proved
   (including Γ₁.wf and s₁'.wf via ctxRed_preserves_ctx_wf/stk_wf).
   Remaining sorry'd cases: ME-PRO (needs commutativity for SubRed diamond),
   ME-APP/ME-BET and ME-BET/ME-BET,ME-APP (structural mismatch between
   me_bet and me_app decompositions of app (lam ..) v).
4. CLOSED: `diamond` now takes Gamma.wf and s.wf hypotheses, which are
   passed to ctxRed_refl. Commutativity propagates these through recursive
   calls by constructing wf for extended contexts/stacks.
5. CLOSED: `u₃.lc` witnesses now discharged by `equivRed_preserves_lc` /
   `subRed_preserves_lc`, proved by mutual induction.
6. CLOSED: `x ∉ t_e.fvs` now discharged by including t_e.fvs in the
   avoidance set when picking x fresh.
8. CLOSED: `promotion_collapse` ms_fun/ms_fop cases now proved using
   classical dichotomy (by_cases on ∃ y₀ giving EquivRed) +
   equivRed_rename to build ME-FUN/ME-FOP from one witness y₀.
9. RESOLVED: Commutativity ME-BET/MS-FOP annotation mismatch. The root
   cause was ME-BET using `.sub dom` for the body context while MS-FOP
   uses `.equiv v`. Fixed by changing ME-BET to use `.equiv v` (matching
   the paper's semantics). Now both premises are in the same context,
   allowing direct application of the IH/diamond.
   Remaining in this case: (a) noPromoAt preservation (same as #10),
   (b) substitution for the `.inr` (EquivRed collapse) right edge: needs
   `subRed_subst_equiv` for .equiv-annotated variables. The `.inl` case
   (noPromoAt) has its main diagram (top + right edges) fully proved.
10. Commutativity noPromoAt preservation sorrys: every case of commutativity
   that produces a result needs noPromoAt z on the output SubRed for any z
   that had noPromoAt z on the input SubRed. Currently sorry'd in MS-EQU,
   MS-PRO (also needs stack extension), ME-APP/MS-APP, ME-BET/MS-EQU,
   and ME-BET/MS-FOP case (a). The general approach requires:
   - Inverting noPromoAt through the input SubRed structure
   - Applying the IH (which co-proves noPromoAt)
   - A noPromoAt_subst lemma (substituting x → v' preserves noPromoAt z
     when z ≠ x) for binder cases
   The z = x special case is easier (noPromoAt_fresh_sub since x ∉ dom Γ').
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
- `equivRed_rename_strong` / `subRed_rename_strong`: fvar renaming for reductions.
  If (x,ann)::G; s |- u =-> u' then (y,ann)::G; s |- u[x:=fvar y] =-> u'[x:=fvar y],
  given freshness of x,y w.r.t. all_fvs(G) and ann.fvs. Replaces the former
  (false) equivRed_subst / subRed_subst. Sorry'd pending mutual induction proof.
- `equivRed_rename` / `subRed_rename`: alpha-renaming under binders — if
  (x,ann)::G; s |- body^x =-> u (resp. <=->), then (y,ann)::G; s |- body^y =->
  u[x:=fvar y]. Derived from equivRed_rename_strong (resp. subRed_rename_strong).
  Requires x not in fvs(body) and x not in all_fvs(G) and x not in ann.fvs.
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
- `promotion_collapse`: if x has .equiv annotation in Γ, any SubRed either
  has noPromoAt x (allowing annotation swap) or is actually an EquivRed.
  All cases fully proved including cofinite binder cases (ms_fun, ms_fop)
  via classical dichotomy + equivRed_rename.
  Enables the ME-BET/MS-FOP case of commutativity: the `.inl` path (noPromoAt)
  is now fully proved using `noPromoAt_sub_swap` without annotation swaps.
- `equivRed_preserves_lc` / `subRed_preserves_lc`: reduction preserves
  local closure. Proved by mutual induction.
- `ctxRed_preserves_ctx_wf` / `ctxRed_preserves_stk_wf`: context reduction
  preserves context and stack well-formedness. Proved by induction on ctxRed.
  Moved before diamond_full to enable closing Γ₁.wf and s₁'.wf sorrys.
- `subRed_subst_noPromo_noPromoAt` ms_pro case: when z's noPromoAt uses
  ms_pro and y's uses ms_equ, the only possible EquivRed on fvar is me_var
  (me_pro contradicts mem_sub via no_sub_and_equiv). After subst, both
  sides are the same term, so reflexivity closes the goal.

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
  The ME-BET/MS-FOP case now uses `.equiv v` annotation (matching the paper),
  so both premises are in the same context. The case splits via
  `promotion_collapse` into:
  (a) noPromoAt holds → apply IH directly, fully proved EXCEPT
      noPromoAt preservation (sorry #10). Main diagram complete.
  (b) SubRed collapses to EquivRed → apply IH via ms_equ. Main diagram
      mostly proved; the right-edge substitution for `.inr` of a second
      promotion_collapse remains sorry'd (needs subRed_subst_equiv).

## Sorry'd Theorems
- `equivRed_rename_strong` / `subRed_rename_strong`: fvar renaming for reductions.
  Replaces the former (false) `equivRed_subst` / `subRed_subst`. The key insight
  is that fvar renaming (specializing substitution to x -> fvar y) avoids the
  blockers that made general substitution false: stacks don't need substituting,
  annotation terms are preserved (since x is fresh for them), and context lookups
  commute with renaming. Sorry'd pending mutual induction proof using the combined
  recursor.
  Infrastructure lemmas available: subst_fvar_fvar_open_at, subst_fvar_notin,
  ctx_swap_sub_ctx, open_subst_comm.
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

/-- lc_at is monotone (local version for use before the private theorem). -/
private theorem lc_at_mono' {e : LNExpr} {k k' : Nat} (hle : k ≤ k')
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

/-- Opening a body that is lc_at (k+1) with an lc_at k term yields lc_at k. -/
theorem lc_at_open {e : LNExpr} {k : Nat} {u : LNExpr}
    (he : e.lc_at (k + 1)) (hu : u.lc_at k) : (e.open_at k u).lc_at k := by
  induction e generalizing k with
  | bvar n =>
    simp [LNExpr.lc_at] at he
    simp [LNExpr.open_at]
    split
    · exact hu
    · simp [LNExpr.lc_at]; omega
  | fvar _ => simp [LNExpr.open_at, LNExpr.lc_at]
  | top => simp [LNExpr.open_at, LNExpr.lc_at]
  | lam dom body ih_dom ih_body =>
    simp [LNExpr.lc_at] at he
    simp [LNExpr.open_at, LNExpr.lc_at]
    exact ⟨ih_dom he.1 hu, ih_body he.2 (lc_at_mono' (by omega) hu)⟩
  | app f a ih_f ih_a =>
    simp [LNExpr.lc_at] at he
    simp [LNExpr.open_at, LNExpr.lc_at]
    exact ⟨ih_f he.1 hu, ih_a he.2 hu⟩

/-- If opening at depth k with fvar x gives lc_at k, then the body is lc_at (k+1).
    Generalized inverse of lc_at_open_fvar. -/
private theorem lc_at_succ_of_open_fvar {body : LNExpr} {k : Nat} {x : String}
    (h : (body.open_at k (.fvar x)).lc_at k) (hfr : x ∉ body.fvs) : body.lc_at (k + 1) := by
  induction body generalizing k with
  | bvar n =>
    simp only [LNExpr.lc_at]
    simp only [LNExpr.open_at] at h
    by_cases hnk : n == k
    · simp [hnk] at h; simp [beq_iff_eq] at hnk; omega
    · simp [hnk, LNExpr.lc_at] at h; omega
  | fvar _ => simp [LNExpr.lc_at]
  | top => simp [LNExpr.lc_at]
  | lam dom body ih_dom ih_body =>
    simp [LNExpr.fvs, List.mem_append] at hfr
    simp only [LNExpr.open_at, LNExpr.lc_at] at h ⊢
    exact ⟨ih_dom h.1 hfr.1, ih_body h.2 hfr.2⟩
  | app f a ih_f ih_a =>
    simp [LNExpr.fvs, List.mem_append] at hfr
    simp only [LNExpr.open_at, LNExpr.lc_at] at h ⊢
    exact ⟨ih_f h.1 hfr.1, ih_a h.2 hfr.2⟩

/-- If for some fresh x, (body^x).lc, then body.lc_at 1.
    Standard LN infrastructure. -/
theorem lc_at_1_of_open_lc {body : LNExpr} {x : String}
    (h : (body.open_at 0 (.fvar x)).lc) (hfr : x ∉ body.fvs) : body.lc_at 1 :=
  lc_at_succ_of_open_fvar h hfr

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

/-- Substitution on annotations: replace fvar x with fvar y in the embedded term. -/
def LNAnn.subst_fvar (ann : LNAnn) (x : String) (u : LNExpr) : LNAnn :=
  match ann with
  | .sub t => .sub (t.subst_fvar x u)
  | .equiv α => .equiv (α.subst_fvar x u)


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

/-- If x ∉ all_fvs Γ and z has annotation ann in Γ, then x ∉ ann.fvs. -/
theorem LNCtx.not_mem_ann_fvs_of_not_mem_all_fvs {Γ : LNCtx} {x z : String} {ann : LNAnn}
    (hfresh : x ∉ LNCtx.all_fvs Γ) (hlook : Γ.lookup' z = some ann) : x ∉ ann.fvs := by
  induction Γ with
  | nil => simp [LNCtx.lookup'] at hlook
  | cons p rest ih =>
    obtain ⟨y, a⟩ := p
    simp only [LNCtx.lookup'] at hlook
    have hfresh_rest : x ∉ LNCtx.all_fvs rest := fun hmem =>
      hfresh (List.mem_append_right _ hmem)
    by_cases hyz : y == z
    · simp [hyz] at hlook; subst hlook
      intro hmem
      apply hfresh
      show x ∈ LNCtx.all_fvs ((y, a) :: rest)
      simp only [LNCtx.all_fvs, List.flatMap_cons]
      exact List.mem_append_left _ (List.mem_cons_of_mem _ hmem)
    · simp [hyz] at hlook; exact ih hfresh_rest hlook

/-- Free variables of opening: if x ∉ e.fvs and x ≠ y, then x ∉ (e.open_at k (fvar y)).fvs. -/
theorem LNExpr.not_mem_fvs_open_at (e : LNExpr) {x y : String} {k : Nat}
    (hfvs : x ∉ e.fvs) (hne : x ≠ y) : x ∉ (e.open_at k (.fvar y)).fvs := by
  match e with
  | .bvar n =>
    unfold open_at; split
    · exact fun h => hne (List.mem_singleton.mp h)
    · exact fun h => (List.not_mem_nil x) h
  | .fvar _ => exact hfvs
  | .top => exact fun h => (List.not_mem_nil x) h
  | .lam dom body =>
    have hdom : x ∉ dom.fvs := fun h => hfvs (List.mem_append_left _ h)
    have hbody : x ∉ body.fvs := fun h => hfvs (List.mem_append_right _ h)
    intro hmem
    simp only [open_at, fvs] at hmem
    cases List.mem_append.mp hmem with
    | inl h => exact not_mem_fvs_open_at dom hdom hne h
    | inr h => exact not_mem_fvs_open_at body hbody hne h
  | .app f a =>
    have hf : x ∉ f.fvs := fun h => hfvs (List.mem_append_left _ h)
    have ha : x ∉ a.fvs := fun h => hfvs (List.mem_append_right _ h)
    intro hmem
    simp only [open_at, fvs] at hmem
    cases List.mem_append.mp hmem with
    | inl h => exact not_mem_fvs_open_at f hf hne h
    | inr h => exact not_mem_fvs_open_at a ha hne h

/-- fvs(e) ⊆ fvs(e.open_at k u): any free variable in e is also in e^u.
    Opening only replaces bound variables, so existing free variables are preserved. -/
theorem LNExpr.mem_fvs_of_mem_fvs_open_at (e : LNExpr) {x : String} {u : LNExpr} {k : Nat}
    (h : x ∈ e.fvs) : x ∈ (e.open_at k u).fvs := by
  match e with
  | .bvar _ => exact absurd h (List.not_mem_nil _)
  | .fvar _ => exact h
  | .top => exact absurd h (List.not_mem_nil _)
  | .lam dom body =>
    simp only [fvs] at h; simp only [open_at, fvs]
    cases List.mem_append.mp h with
    | inl hd => exact List.mem_append_left _ (mem_fvs_of_mem_fvs_open_at dom hd)
    | inr hb => exact List.mem_append_right _ (mem_fvs_of_mem_fvs_open_at body hb)
  | .app f a =>
    simp only [fvs] at h; simp only [open_at, fvs]
    cases List.mem_append.mp h with
    | inl hf => exact List.mem_append_left _ (mem_fvs_of_mem_fvs_open_at f hf)
    | inr ha => exact List.mem_append_right _ (mem_fvs_of_mem_fvs_open_at a ha)

/-- Reverse direction: if x ∉ (e.open_at k u).fvs then x ∉ e.fvs.
    Immediate from mem_fvs_of_mem_fvs_open_at by contraposition. -/
theorem LNExpr.not_mem_fvs_of_not_mem_fvs_open (e : LNExpr) {x : String} {u : LNExpr} {k : Nat}
    (h : x ∉ (e.open_at k u).fvs) : x ∉ e.fvs :=
  fun hmem => h (mem_fvs_of_mem_fvs_open_at e hmem)

/-- General opening with an arbitrary term: if x ∉ e.fvs and x ∉ u.fvs,
    then x ∉ (e.open_at k u).fvs. -/
theorem LNExpr.not_mem_fvs_open_at_term (e : LNExpr) {x : String} {u : LNExpr} {k : Nat}
    (he : x ∉ e.fvs) (hu : x ∉ u.fvs) : x ∉ (e.open_at k u).fvs := by
  match e with
  | .bvar n =>
    simp only [open_at]; split
    · exact hu
    · exact fun hmem => (List.not_mem_nil x) hmem
  | .fvar _ => exact he
  | .top => exact fun hmem => (List.not_mem_nil x) hmem
  | .lam dom body =>
    have hdom : x ∉ dom.fvs := fun h => he (List.mem_append_left _ h)
    have hbody : x ∉ body.fvs := fun h => he (List.mem_append_right _ h)
    intro hmem
    simp only [open_at, fvs] at hmem
    cases List.mem_append.mp hmem with
    | inl h => exact not_mem_fvs_open_at_term dom hdom hu h
    | inr h => exact not_mem_fvs_open_at_term body hbody hu h
  | .app f a =>
    have hf : x ∉ f.fvs := fun h => he (List.mem_append_left _ h)
    have ha : x ∉ a.fvs := fun h => he (List.mem_append_right _ h)
    intro hmem
    simp only [open_at, fvs] at hmem
    cases List.mem_append.mp hmem with
    | inl h => exact not_mem_fvs_open_at_term f hf hu h
    | inr h => exact not_mem_fvs_open_at_term a ha hu h

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
        `(Γ, x ≡ v); s ⊢ body^x ≡→ t^x`
        `Γ; nil ⊢ v ≡→ v'`
      ⟹  `Γ; s ⊢ (λdom.body) v ≡→ t^v'`

      Here `t` is a term with bvar 0 representing the closed body result.
      Opening `t` with `v'` gives the β-reduct. -/
  | me_bet {Γ : LNCtx} {s : LNStack} {dom body t v v' : LNExpr} (L : List String) :
      (∀ x, x ∉ L → LNEquivRed ((x, .equiv v) :: Γ) s (body.open_at 0 (.fvar x)) (t.open_at 0 (.fvar x))) →
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
        .me_bet L (fun y hy => ih_body y hy ((y, .equiv _) :: Γ') (LNCtx.sub_cons hsc)) (ih_v Γ' hsc))
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
        .me_bet L (fun y hy => ih_body y hy ((y, .equiv _) :: Γ') (LNCtx.sub_cons hsc)) (ih_v Γ' hsc))
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

/-! ### Context renaming infrastructure for equivRed_rename_strong / subRed_rename_strong

We define `ctx_rename Γ x y` which renames the variable `x` to `y` throughout
a context (both in binding names and in annotation terms). The mutual induction
proof uses this as its motive's context transformation, which handles binder
cases cleanly: when the derivation extends the context with `(w, .sub dom)`,
the renamed context becomes `(w, .sub (dom[x↦y]))` automatically.
-/

/-- Rename variable `x` to `y` throughout a context: change binding names
    and substitute `x ↦ fvar y` in annotation terms. -/
def ctx_rename (Γ : LNCtx) (x y : String) : LNCtx :=
  Γ.map (fun (z, ann) => (if z == x then y else z, ann.subst_fvar x (.fvar y)))

/-- Substitution is a no-op when the variable doesn't occur free (local copy). -/
private theorem subst_fvar_notin' {e : LNExpr} {x : String} {u : LNExpr}
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

/-- Substitution on annotation is a no-op when the variable doesn't occur free (local copy). -/
private theorem ann_subst_fvar_notin' {ann : LNAnn} {x : String} {u : LNExpr}
    (hfr : x ∉ ann.fvs) : ann.subst_fvar x u = ann := by
  cases ann with
  | sub t => show LNAnn.sub (t.subst_fvar x u) = LNAnn.sub t; congr 1; exact subst_fvar_notin' hfr
  | equiv α => show LNAnn.equiv (α.subst_fvar x u) = LNAnn.equiv α; congr 1; exact subst_fvar_notin' hfr

/-- subst_fvar with fvar commutes with open_at for arbitrary terms (local copy). -/
private theorem subst_fvar_fvar_open_at' (e : LNExpr) (x y : String) (k : Nat) (v : LNExpr)
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

/-- subst_fvar with fvar commutes with open_at (local copy). -/
private theorem subst_fvar_fvar_open_fvar' (e : LNExpr) (x y z : String) (k : Nat)
    (hxz : x ≠ z)
    : (e.open_at k (.fvar z)).subst_fvar x (.fvar y) = (e.subst_fvar x (.fvar y)).open_at k (.fvar z) := by
  induction e generalizing k with
  | bvar n =>
    show (if n == k then LNExpr.fvar z else .bvar n).subst_fvar x (.fvar y) =
         if n == k then .fvar z else .bvar n
    split
    · simp only [LNExpr.subst_fvar]
      have : ¬ (z == x) = true := by simp [beq_iff_eq]; exact Ne.symm hxz
      simp [this]
    · rfl
  | fvar w =>
    simp only [LNExpr.open_at, LNExpr.subst_fvar]
    split <;> rfl
  | top => rfl
  | lam dom body ih_dom ih_body =>
    simp only [LNExpr.open_at, LNExpr.subst_fvar, ih_dom k, ih_body (k+1)]
  | app f a ih_f ih_a =>
    simp only [LNExpr.open_at, LNExpr.subst_fvar, ih_f k, ih_a k]

private theorem ctx_rename_cons (z : String) (ann : LNAnn) (Γ : LNCtx) (x y : String)
    : ctx_rename ((z, ann) :: Γ) x y =
      (if z == x then y else z, ann.subst_fvar x (.fvar y)) :: ctx_rename Γ x y := by
  simp [ctx_rename, List.map]

/-- When `x ∉ all_fvs(Γ)`, renaming `x → y` is the identity on Γ. -/
private theorem ctx_rename_id_fresh {Γ : LNCtx} {x y : String}
    (hfx : x ∉ LNCtx.all_fvs Γ) : ctx_rename Γ x y = Γ := by
  induction Γ with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨z, ann⟩ := p
    have hfx_head : x ∉ (z :: ann.fvs) := by
      intro hmem; apply hfx
      show x ∈ ((z, ann) :: rest).flatMap (fun p => p.1 :: p.2.fvs)
      simp only [List.flatMap_cons]
      exact List.mem_append_left _ hmem
    have hx_ne_z : x ≠ z := fun heq => hfx_head (heq ▸ List.mem_cons_self _ _)
    have hx_ann : x ∉ ann.fvs := fun hmem => hfx_head (List.mem_cons_of_mem _ hmem)
    have hfx_rest : x ∉ LNCtx.all_fvs rest := by
      intro hmem; apply hfx
      show x ∈ ((z, ann) :: rest).flatMap (fun p => p.1 :: p.2.fvs)
      simp only [List.flatMap_cons]
      exact List.mem_append_right _ hmem
    show ctx_rename ((z, ann) :: rest) x y = (z, ann) :: rest
    simp only [ctx_rename, List.map]
    have h1 : ¬(z == x) = true := by rw [beq_iff_eq]; exact Ne.symm hx_ne_z
    simp only [h1, decide_false, ite_false, ann_subst_fvar_notin' hx_ann]
    congr 1; exact ih hfx_rest

/-- Lookup in a renamed context: if `Γ.lookup' z = some ann` and the renaming
    `x → y` is injective on `dom(Γ)` (ensured by `x ≠ y → y ∉ dom(Γ)`),
    then `(ctx_rename Γ x y).lookup' z' = some (ann.subst_fvar x (.fvar y))`
    where `z' = if z == x then y else z`. -/
private theorem ctx_rename_lookup {Γ : LNCtx} {x y z : String} {ann : LNAnn}
    (hlook : LNCtx.lookup' Γ z = some ann)
    (hinj : x ≠ y → y ∉ LNCtx.dom Γ) :
    LNCtx.lookup' (ctx_rename Γ x y) (if z == x then y else z) =
      some (ann.subst_fvar x (.fvar y)) := by
  induction Γ with
  | nil => simp [LNCtx.lookup'] at hlook
  | cons p rest ih =>
    obtain ⟨w, ann_w⟩ := p
    have hinj_rest : x ≠ y → y ∉ LNCtx.dom rest :=
      fun hne hmem => hinj hne (List.mem_cons_of_mem _ hmem)
    simp only [ctx_rename, List.map, LNCtx.lookup']
    simp only [LNCtx.lookup'] at hlook
    by_cases hwz' : (w == z) = true
    · have hwz_eq := beq_iff_eq.mp hwz'; subst hwz_eq
      simp only [beq_self_eq_true, ite_true] at hlook ⊢
      cases hlook; rfl
    · simp only [hwz', ite_false] at hlook
      -- Need: the renamed head doesn't match the renamed key
      have hskip : ¬((if (w == x) = true then y else w) == (if (z == x) = true then y else z)) = true := by
        intro heq_str
        have hw_ne_z : w ≠ z := fun h => by simp [beq_iff_eq, h] at hwz'
        -- heq_str : (if (w == x) = true then y else w) = (if (z == x) = true then y else z)
        -- We derive a contradiction from hw_ne_z and the injectivity hinj.
        by_cases hzx : (z == x) = true <;> by_cases hwx : (w == x) = true
        · -- w = x, z = x: w = z, contradiction
          exact hw_ne_z (by rw [beq_iff_eq.mp hwx, beq_iff_eq.mp hzx])
        · -- w ≠ x, z = x: head = w, target = y. So w = y.
          rw [if_neg hwx, if_pos hzx] at heq_str
          have := beq_iff_eq.mp heq_str  -- w = y
          by_cases hxy : x = y
          · subst hxy; exact hw_ne_z (by rw [this, beq_iff_eq.mp hzx])
          · exact hinj (fun (h : x = y) => hxy h) (this ▸ List.mem_cons_self _ _)
        · -- w = x, z ≠ x: head = y, target = z. So y = z.
          rw [if_pos hwx, if_neg hzx] at heq_str
          have := beq_iff_eq.mp heq_str  -- y = z
          by_cases hxy : x = y
          · subst hxy; exact hw_ne_z (by rw [beq_iff_eq.mp hwx, ← this])
          · exact hinj (fun (h : x = y) => hxy h) (this ▸ List.mem_cons_of_mem _ (mem_dom_of_lookup' hlook))
        · -- w ≠ x, z ≠ x: head = w, target = z. So w = z, contradiction.
          rw [if_neg hwx, if_neg hzx] at heq_str
          exact hw_ne_z (beq_iff_eq.mp heq_str)
      simp only [hskip, ite_false]
      exact ih hlook hinj_rest

set_option maxHeartbeats 6400000 in
private theorem equivRed_rename_gen
    {Γ : LNCtx} {s : LNStack} {u u' : LNExpr}
    (h : LNEquivRed Γ s u u')
    {x y : String}
    (hinj : x ≠ y → y ∉ LNCtx.dom Γ)
    : LNEquivRed (ctx_rename Γ x y)
        (s.map (fun e => e.subst_fvar x (.fvar y)))
        (u.subst_fvar x (.fvar y))
        (u'.subst_fvar x (.fvar y)) := by
  have go :=
    @LNEquivRed.rec
      (motive_1 := fun Γ s u u' _ =>
        ∀ x y, (x ≠ y → y ∉ LNCtx.dom Γ) →
          LNEquivRed (ctx_rename Γ x y)
            (s.map (fun e => e.subst_fvar x (.fvar y)))
            (u.subst_fvar x (.fvar y))
            (u'.subst_fvar x (.fvar y)))
      (motive_2 := fun Γ s u u' _ =>
        ∀ x y, (x ≠ y → y ∉ LNCtx.dom Γ) →
          LNSubRed (ctx_rename Γ x y)
            (s.map (fun e => e.subst_fvar x (.fvar y)))
            (u.subst_fvar x (.fvar y))
            (u'.subst_fvar x (.fvar y)))
      -- ═══════════════════════════════════════════════════════════════
      -- ME-PRO: fvar z with z ≡ α ∈ Γ, SubRed Γ s α α'
      -- ═══════════════════════════════════════════════════════════════
      (fun {Γ_pro s_pro z_pro α_pro α'_pro} hmem _hsub ih_sub x y hinj => by
        simp only [LNExpr.subst_fvar]
        have ih := ih_sub x y hinj
        -- lookup z_pro in the renamed context
        have hlook := ctx_rename_lookup hmem hinj
        by_cases hzx : z_pro == x
        · simp [hzx]; simp [hzx] at hlook; exact .me_pro hlook ih
        · simp [hzx]; simp [hzx] at hlook; exact .me_pro hlook ih)
      -- ═══════════════════════════════════════════════════════════════
      -- ME-BET: app (lam dom body) v ≡→ t^v'
      -- ═══════════════════════════════════════════════════════════════
      (fun {Γ_bet s_bet dom_bet body_bet t_bet v_bet v'_bet}
           L _hbody _hv ih_body ih_v x y hinj => by
        simp only [LNExpr.subst_fvar]
        rw [subst_fvar_fvar_open_at' t_bet x y 0 v'_bet]
        -- Rename body and value
        have ihv := ih_v x y hinj
        simp [List.map] at ihv
        -- Pick fresh w for the body
        let L' := L ++ [x, y] ++ LNCtx.dom Γ_bet ++
                  LNCtx.dom (ctx_rename Γ_bet x y)
        apply LNEquivRed.me_bet (L := L')
        · intro w hw
          have hwL : w ∉ L := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
          have hwx : w ≠ x := by
            intro heq; subst heq
            exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self _ _))))
          have hwy : w ≠ y := by
            intro heq; subst heq
            exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))))
          have hw_dom : w ∉ LNCtx.dom Γ_bet := fun h =>
            hw (List.mem_append_left _ (List.mem_append_right _ h))
          have hw_dom_ren : w ∉ LNCtx.dom (ctx_rename Γ_bet x y) := fun h =>
            hw (List.mem_append_right _ h)
          -- IH at w: operates on context (w, .sub dom) :: Γ_bet
          have ih := ih_body w hwL x y (fun hne hmem => by
            cases List.mem_cons.mp hmem with
            | inl heq => exact hwy heq.symm
            | inr hmem_rest => exact hinj hne hmem_rest)
          -- Rewrite: ctx_rename ((w, .sub dom) :: Γ) x y
          rw [ctx_rename_cons] at ih
          have hwx_f : ¬(w == x) = true := by rw [beq_iff_eq]; exact hwx
          simp only [hwx_f, ite_false, LNAnn.subst_fvar] at ih
          -- Rewrite: (body^w)[x↦y] = (body[x↦y])^w since x ≠ w
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          -- Rewrite: (t^w)[x↦y] = (t[x↦y])^w since x ≠ w
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          exact ih
        · exact ihv)
      -- ═══════════════════════════════════════════════════════════════
      -- ME-TOP
      -- ═══════════════════════════════════════════════════════════════
      (fun x y _hinj => by simp [LNExpr.subst_fvar]; exact .me_top)
      -- ═══════════════════════════════════════════════════════════════
      -- ME-VAR
      -- ═══════════════════════════════════════════════════════════════
      (fun {Γ_var s_var z_var} x y _hinj => by
        simp only [LNExpr.subst_fvar]
        split <;> exact .me_var)
      -- ═══════════════════════════════════════════════════════════════
      -- ME-TAP
      -- ═══════════════════════════════════════════════════════════════
      (fun {Γ_tap s_tap u_tap} x y _hinj => by
        simp only [LNExpr.subst_fvar]; exact .me_tap)
      -- ═══════════════════════════════════════════════════════════════
      -- ME-APP: app u v ≡→ app u' v'
      -- ═══════════════════════════════════════════════════════════════
      (fun {Γ_app s_app u_app u'_app v_app v'_app} _hu _hv ih_u ih_v x y hinj => by
        simp only [LNExpr.subst_fvar]
        have ihu := ih_u x y hinj
        have ihv := ih_v x y hinj
        simp [List.map] at ihu
        simp [List.map] at ihv
        exact .me_app ihu ihv)
      -- ═══════════════════════════════════════════════════════════════
      -- ME-FUN: lam dom body ≡→ lam dom' body' (stack = [])
      -- ═══════════════════════════════════════════════════════════════
      (fun {Γ_fun dom_fun dom'_fun body_fun body'_fun}
           L _hdom _hbody ih_dom ih_body x y hinj => by
        simp only [LNExpr.subst_fvar]
        have ihdom := ih_dom x y hinj
        simp [List.map] at ihdom
        let L' := L ++ [x, y] ++ LNCtx.dom Γ_fun ++
                  LNCtx.dom (ctx_rename Γ_fun x y)
        exact .me_fun L' ihdom (fun w hw => by
          have hwL : w ∉ L := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
          have hwx : w ≠ x := by
            intro heq; subst heq
            exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self _ _))))
          have hwy : w ≠ y := by
            intro heq; subst heq
            exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))))
          have ih := ih_body w hwL x y (fun hne hmem => by
            cases List.mem_cons.mp hmem with
            | inl heq => exact hwy heq.symm
            | inr hmem_rest => exact hinj hne hmem_rest)
          rw [ctx_rename_cons] at ih
          have hwx_f : ¬(w == x) = true := by rw [beq_iff_eq]; exact hwx
          simp only [hwx_f, ite_false, LNAnn.subst_fvar, List.map] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          exact ih))
      -- ═══════════════════════════════════════════════════════════════
      -- ME-FOP: lam dom body ≡→ lam dom' body' (stack = α :: s)
      -- ═══════════════════════════════════════════════════════════════
      (fun {Γ_fop s_fop α_fop dom_fop dom'_fop body_fop body'_fop}
           L _hdom _hbody ih_dom ih_body x y hinj => by
        simp only [LNExpr.subst_fvar, List.map]
        have ihdom := ih_dom x y hinj
        simp [List.map] at ihdom
        let L' := L ++ [x, y] ++ LNCtx.dom Γ_fop ++
                  LNCtx.dom (ctx_rename Γ_fop x y)
        exact .me_fop L' ihdom (fun w hw => by
          have hwL : w ∉ L := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
          have hwx : w ≠ x := by
            intro heq; subst heq
            exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self _ _))))
          have hwy : w ≠ y := by
            intro heq; subst heq
            exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))))
          have ih := ih_body w hwL x y (fun hne hmem => by
            cases List.mem_cons.mp hmem with
            | inl heq => exact hwy heq.symm
            | inr hmem_rest => exact hinj hne hmem_rest)
          rw [ctx_rename_cons] at ih
          have hwx_f : ¬(w == x) = true := by rw [beq_iff_eq]; exact hwx
          simp only [hwx_f, ite_false, LNAnn.subst_fvar] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          exact ih))
      -- ═══════════════════════════════════════════════════════════════
      -- MS-PRO: fvar z with z ≤ t ∈ Γ
      -- ═══════════════════════════════════════════════════════════════
      (fun {Γ_sp s_sp z_sp t_sp} hmem x y hinj => by
        simp only [LNExpr.subst_fvar]
        have hlook := ctx_rename_lookup hmem hinj
        by_cases hzx : z_sp == x
        · simp [hzx]; simp [hzx] at hlook; exact .ms_pro hlook
        · simp [hzx]; simp [hzx] at hlook; exact .ms_pro hlook)
      -- ═══════════════════════════════════════════════════════════════
      -- MS-TOP
      -- ═══════════════════════════════════════════════════════════════
      (fun x y _hinj => by simp [LNExpr.subst_fvar]; exact .ms_top)
      -- ═══════════════════════════════════════════════════════════════
      -- MS-EQU: from EquivRed
      -- ═══════════════════════════════════════════════════════════════
      (fun _hequ ih_equ x y hinj => .ms_equ (ih_equ x y hinj))
      -- ═══════════════════════════════════════════════════════════════
      -- MS-APP: app u v ≤→ app u' v
      -- ═══════════════════════════════════════════════════════════════
      (fun {Γ_sa s_sa u_sa u'_sa v_sa} _hsub ih_sub x y hinj => by
        simp only [LNExpr.subst_fvar, List.map]
        exact .ms_app (ih_sub x y hinj))
      -- ═══════════════════════════════════════════════════════════════
      -- MS-FUN: lam dom body ≤→ lam dom body' (stack = [])
      -- ═══════════════════════════════════════════════════════════════
      (fun {Γ_sf dom_sf body_sf body'_sf}
           L _hbody ih_body x y hinj => by
        simp only [LNExpr.subst_fvar, List.map]
        let L' := L ++ [x, y] ++ LNCtx.dom Γ_sf ++
                  LNCtx.dom (ctx_rename Γ_sf x y)
        exact .ms_fun L' (fun w hw => by
          have hwL : w ∉ L := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
          have hwx : w ≠ x := by
            intro heq; subst heq
            exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self _ _))))
          have hwy : w ≠ y := by
            intro heq; subst heq
            exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))))
          have ih := ih_body w hwL x y (fun hne hmem => by
            cases List.mem_cons.mp hmem with
            | inl heq => exact hwy heq.symm
            | inr hmem_rest => exact hinj hne hmem_rest)
          rw [ctx_rename_cons] at ih
          have hwx_f : ¬(w == x) = true := by rw [beq_iff_eq]; exact hwx
          simp only [hwx_f, ite_false, LNAnn.subst_fvar, List.map] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          exact ih))
      -- ═══════════════════════════════════════════════════════════════
      -- MS-FOP: lam dom body ≤→ lam dom body' (stack = α :: s)
      -- ═══════════════════════════════════════════════════════════════
      (fun {Γ_sfop s_sfop α_sfop dom_sfop body_sfop body'_sfop}
           L _hbody ih_body x y hinj => by
        simp only [LNExpr.subst_fvar, List.map]
        let L' := L ++ [x, y] ++ LNCtx.dom Γ_sfop ++
                  LNCtx.dom (ctx_rename Γ_sfop x y)
        exact .ms_fop L' (fun w hw => by
          have hwL : w ∉ L := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
          have hwx : w ≠ x := by
            intro heq; subst heq
            exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self _ _))))
          have hwy : w ≠ y := by
            intro heq; subst heq
            exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))))
          have ih := ih_body w hwL x y (fun hne hmem => by
            cases List.mem_cons.mp hmem with
            | inl heq => exact hwy heq.symm
            | inr hmem_rest => exact hinj hne hmem_rest)
          rw [ctx_rename_cons] at ih
          have hwx_f : ¬(w == x) = true := by rw [beq_iff_eq]; exact hwx
          simp only [hwx_f, ite_false, LNAnn.subst_fvar] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          exact ih))
  exact go h x y hinj

set_option maxHeartbeats 6400000 in
private theorem subRed_rename_gen
    {Γ : LNCtx} {s : LNStack} {u u' : LNExpr}
    (h : LNSubRed Γ s u u')
    {x y : String}
    (hinj : x ≠ y → y ∉ LNCtx.dom Γ)
    : LNSubRed (ctx_rename Γ x y)
        (s.map (fun e => e.subst_fvar x (.fvar y)))
        (u.subst_fvar x (.fvar y))
        (u'.subst_fvar x (.fvar y)) := by
  have go :=
    @LNSubRed.rec
      (motive_1 := fun Γ s u u' _ =>
        ∀ x y, (x ≠ y → y ∉ LNCtx.dom Γ) →
          LNEquivRed (ctx_rename Γ x y)
            (s.map (fun e => e.subst_fvar x (.fvar y)))
            (u.subst_fvar x (.fvar y))
            (u'.subst_fvar x (.fvar y)))
      (motive_2 := fun Γ s u u' _ =>
        ∀ x y, (x ≠ y → y ∉ LNCtx.dom Γ) →
          LNSubRed (ctx_rename Γ x y)
            (s.map (fun e => e.subst_fvar x (.fvar y)))
            (u.subst_fvar x (.fvar y))
            (u'.subst_fvar x (.fvar y)))
      -- ME-PRO
      (fun {Γ_pro s_pro z_pro α_pro α'_pro} hmem _hsub ih_sub x y hinj => by
        simp only [LNExpr.subst_fvar]
        have ih := ih_sub x y hinj
        have hlook := ctx_rename_lookup hmem hinj
        by_cases hzx : z_pro == x
        · simp [hzx]; simp [hzx] at hlook; exact .me_pro hlook ih
        · simp [hzx]; simp [hzx] at hlook; exact .me_pro hlook ih)
      -- ME-BET
      (fun {Γ_bet s_bet dom_bet body_bet t_bet v_bet v'_bet}
           L _hbody _hv ih_body ih_v x y hinj => by
        simp only [LNExpr.subst_fvar]
        rw [subst_fvar_fvar_open_at' t_bet x y 0 v'_bet]
        have ihv := ih_v x y hinj
        simp [List.map] at ihv
        let L' := L ++ [x, y] ++ LNCtx.dom Γ_bet ++ LNCtx.dom (ctx_rename Γ_bet x y)
        apply LNEquivRed.me_bet (L := L')
        · intro w hw
          have hwL : w ∉ L := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
          have hwx : w ≠ x := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self _ _))))
          have hwy : w ≠ y := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))))
          have ih := ih_body w hwL x y (fun hne hmem => by
            cases List.mem_cons.mp hmem with
            | inl heq => exact hwy heq.symm
            | inr hmem_rest => exact hinj hne hmem_rest)
          rw [ctx_rename_cons] at ih
          have hwx_f : ¬(w == x) = true := by rw [beq_iff_eq]; exact hwx
          simp only [hwx_f, ite_false, LNAnn.subst_fvar] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          exact ih
        · exact ihv)
      -- ME-TOP
      (fun x y _hinj => by simp [LNExpr.subst_fvar]; exact .me_top)
      -- ME-VAR
      (fun {Γ_var s_var z_var} x y _hinj => by
        simp only [LNExpr.subst_fvar]; split <;> exact .me_var)
      -- ME-TAP
      (fun {Γ_tap s_tap u_tap} x y _hinj => by simp only [LNExpr.subst_fvar]; exact .me_tap)
      -- ME-APP
      (fun {Γ_app s_app u_app u'_app v_app v'_app} _hu _hv ih_u ih_v x y hinj => by
        simp only [LNExpr.subst_fvar]
        have ihu := ih_u x y hinj
        have ihv := ih_v x y hinj
        simp [List.map] at ihu ihv
        exact .me_app ihu ihv)
      -- ME-FUN
      (fun {Γ_fun dom_fun dom'_fun body_fun body'_fun}
           L _hdom _hbody ih_dom ih_body x y hinj => by
        simp only [LNExpr.subst_fvar]
        have ihdom := ih_dom x y hinj
        simp [List.map] at ihdom
        let L' := L ++ [x, y] ++ LNCtx.dom Γ_fun ++ LNCtx.dom (ctx_rename Γ_fun x y)
        exact .me_fun L' ihdom (fun w hw => by
          have hwL : w ∉ L := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
          have hwx : w ≠ x := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self _ _))))
          have hwy : w ≠ y := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))))
          have ih := ih_body w hwL x y (fun hne hmem => by
            cases List.mem_cons.mp hmem with
            | inl heq => exact hwy heq.symm
            | inr hmem_rest => exact hinj hne hmem_rest)
          rw [ctx_rename_cons] at ih
          have hwx_f : ¬(w == x) = true := by rw [beq_iff_eq]; exact hwx
          simp only [hwx_f, ite_false, LNAnn.subst_fvar, List.map] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          exact ih))
      -- ME-FOP
      (fun {Γ_fop s_fop α_fop dom_fop dom'_fop body_fop body'_fop}
           L _hdom _hbody ih_dom ih_body x y hinj => by
        simp only [LNExpr.subst_fvar, List.map]
        have ihdom := ih_dom x y hinj
        simp [List.map] at ihdom
        let L' := L ++ [x, y] ++ LNCtx.dom Γ_fop ++ LNCtx.dom (ctx_rename Γ_fop x y)
        exact .me_fop L' ihdom (fun w hw => by
          have hwL : w ∉ L := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
          have hwx : w ≠ x := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self _ _))))
          have hwy : w ≠ y := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))))
          have ih := ih_body w hwL x y (fun hne hmem => by
            cases List.mem_cons.mp hmem with
            | inl heq => exact hwy heq.symm
            | inr hmem_rest => exact hinj hne hmem_rest)
          rw [ctx_rename_cons] at ih
          have hwx_f : ¬(w == x) = true := by rw [beq_iff_eq]; exact hwx
          simp only [hwx_f, ite_false, LNAnn.subst_fvar] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          exact ih))
      -- MS-PRO
      (fun {Γ_sp s_sp z_sp t_sp} hmem x y hinj => by
        simp only [LNExpr.subst_fvar]
        have hlook := ctx_rename_lookup hmem hinj
        by_cases hzx : z_sp == x
        · simp [hzx]; simp [hzx] at hlook; exact .ms_pro hlook
        · simp [hzx]; simp [hzx] at hlook; exact .ms_pro hlook)
      -- MS-TOP
      (fun x y _hinj => by simp [LNExpr.subst_fvar]; exact .ms_top)
      -- MS-EQU
      (fun _hequ ih_equ x y hinj => .ms_equ (ih_equ x y hinj))
      -- MS-APP
      (fun {Γ_sa s_sa u_sa u'_sa v_sa} _hsub ih_sub x y hinj => by
        simp only [LNExpr.subst_fvar, List.map]
        exact .ms_app (ih_sub x y hinj))
      -- MS-FUN
      (fun {Γ_sf dom_sf body_sf body'_sf}
           L _hbody ih_body x y hinj => by
        simp only [LNExpr.subst_fvar, List.map]
        let L' := L ++ [x, y] ++ LNCtx.dom Γ_sf ++ LNCtx.dom (ctx_rename Γ_sf x y)
        exact .ms_fun L' (fun w hw => by
          have hwL : w ∉ L := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
          have hwx : w ≠ x := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self _ _))))
          have hwy : w ≠ y := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))))
          have ih := ih_body w hwL x y (fun hne hmem => by
            cases List.mem_cons.mp hmem with
            | inl heq => exact hwy heq.symm
            | inr hmem_rest => exact hinj hne hmem_rest)
          rw [ctx_rename_cons] at ih
          have hwx_f : ¬(w == x) = true := by rw [beq_iff_eq]; exact hwx
          simp only [hwx_f, ite_false, LNAnn.subst_fvar, List.map] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          exact ih))
      -- MS-FOP
      (fun {Γ_sfop s_sfop α_sfop dom_sfop body_sfop body'_sfop}
           L _hbody ih_body x y hinj => by
        simp only [LNExpr.subst_fvar, List.map]
        let L' := L ++ [x, y] ++ LNCtx.dom Γ_sfop ++ LNCtx.dom (ctx_rename Γ_sfop x y)
        exact .ms_fop L' (fun w hw => by
          have hwL : w ∉ L := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
          have hwx : w ≠ x := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self _ _))))
          have hwy : w ≠ y := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))))
          have ih := ih_body w hwL x y (fun hne hmem => by
            cases List.mem_cons.mp hmem with
            | inl heq => exact hwy heq.symm
            | inr hmem_rest => exact hinj hne hmem_rest)
          rw [ctx_rename_cons] at ih
          have hwx_f : ¬(w == x) = true := by rw [beq_iff_eq]; exact hwx
          simp only [hwx_f, ite_false, LNAnn.subst_fvar] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          exact ih))
  exact go h x y hinj

/-- Stack substitution simplification: when `x` is not free in any element
    of the stack, `s.map (subst_fvar x (fvar y)) = s`. -/
private theorem stack_map_subst_id {s : LNStack} {x y : String}
    (hfresh : ∀ e ∈ s, x ∉ e.fvs) : s.map (fun e => e.subst_fvar x (.fvar y)) = s := by
  induction s with
  | nil => rfl
  | cons a rest ih =>
    simp [List.map]
    constructor
    · exact subst_fvar_notin' (hfresh a (List.mem_cons_self _ _))
    · exact ih (fun e he => hfresh e (List.mem_cons_of_mem _ he))

set_option maxHeartbeats 1600000 in
theorem equivRed_rename_strong
    {Γ : LNCtx} {s : LNStack} {x y : String} {ann : LNAnn}
    {u u' : LNExpr}
    (h : LNEquivRed ((x, ann) :: Γ) s u u')
    (hfx : x ∉ LNCtx.all_fvs Γ)
    (hfy : y ∉ LNCtx.all_fvs Γ)
    (hfx_ann : x ∉ ann.fvs)
    (hx_ne_y : x ≠ y → y ∉ LNCtx.dom Γ)
    (hsfresh : ∀ e ∈ s, x ∉ e.fvs)
    : LNEquivRed ((y, ann) :: Γ) s (u.subst_fvar x (.fvar y)) (u'.subst_fvar x (.fvar y)) := by
  have hgen := equivRed_rename_gen h (x := x) (y := y) (fun hne hmem => by
    cases List.mem_cons.mp hmem with
    | inl heq => exact hne heq.symm
    | inr hmem_rest => exact hx_ne_y hne hmem_rest)
  rw [ctx_rename_cons, show (x == x) = true from beq_self_eq_true x,
      ann_subst_fvar_notin' hfx_ann, ctx_rename_id_fresh hfx,
      stack_map_subst_id hsfresh] at hgen
  simpa using hgen

set_option maxHeartbeats 1600000 in
theorem subRed_rename_strong
    {Γ : LNCtx} {s : LNStack} {x y : String} {ann : LNAnn}
    {u u' : LNExpr}
    (h : LNSubRed ((x, ann) :: Γ) s u u')
    (hfx : x ∉ LNCtx.all_fvs Γ)
    (hfy : y ∉ LNCtx.all_fvs Γ)
    (hfx_ann : x ∉ ann.fvs)
    (hx_ne_y : x ≠ y → y ∉ LNCtx.dom Γ)
    (hsfresh : ∀ e ∈ s, x ∉ e.fvs)
    : LNSubRed ((y, ann) :: Γ) s (u.subst_fvar x (.fvar y)) (u'.subst_fvar x (.fvar y)) := by
  have hgen := subRed_rename_gen h (x := x) (y := y) (fun hne hmem => by
    cases List.mem_cons.mp hmem with
    | inl heq => exact hne heq.symm
    | inr hmem_rest => exact hx_ne_y hne hmem_rest)
  rw [ctx_rename_cons, show (x == x) = true from beq_self_eq_true x,
      ann_subst_fvar_notin' hfx_ann, ctx_rename_id_fresh hfx,
      stack_map_subst_id hsfresh] at hgen
  simpa using hgen

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

/-- Substitution on annotation is a no-op when the variable doesn't occur free. -/
theorem ann_subst_fvar_notin {ann : LNAnn} {x : String} {u : LNExpr}
    (hfr : x ∉ ann.fvs) : ann.subst_fvar x u = ann := by
  cases ann with
  | sub t =>
    show LNAnn.sub (t.subst_fvar x u) = LNAnn.sub t
    congr 1; exact subst_fvar_notin hfr
  | equiv α =>
    show LNAnn.equiv (α.subst_fvar x u) = LNAnn.equiv α
    congr 1; exact subst_fvar_notin hfr

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
    If (x,ann)::Γ; s ⊢ body^x ≡→ u and x,y are fresh for Γ and ann,
    then (y,ann)::Γ; s ⊢ body^y ≡→ u[x↦fvar y].
    Derived from equivRed_rename_strong by rewriting the LHS using
    subst_fvar_fvar_open_at + subst_fvar_notin. -/
theorem equivRed_rename
    {Γ : LNCtx} {s : LNStack} {ann : LNAnn}
    {body u : LNExpr} {x y : String}
    (h : LNEquivRed ((x, ann) :: Γ) s (body.open_at 0 (.fvar x)) u)
    (hfx : x ∉ LNCtx.all_fvs Γ) (hfy : y ∉ LNCtx.all_fvs Γ)
    (hfr : x ∉ body.fvs)
    (hfx_ann : x ∉ ann.fvs)
    (hsfresh : ∀ e ∈ s, x ∉ e.fvs)
    : LNEquivRed ((y, ann) :: Γ) s (body.open_at 0 (.fvar y)) (u.subst_fvar x (.fvar y)) := by
  have h1 := equivRed_rename_strong h hfx hfy hfx_ann
    (fun hne => LNCtx.not_mem_dom_of_not_mem_all_fvs hfy) hsfresh
  -- Rewrite LHS: (body^x)[x↦fvar y] = body^y
  have hlhs : (body.open_at 0 (.fvar x)).subst_fvar x (.fvar y) = body.open_at 0 (.fvar y) := by
    rw [subst_fvar_fvar_open_at]
    simp only [LNExpr.subst_fvar, beq_self_eq_true, ite_true]
    rw [subst_fvar_notin hfr]
  rw [hlhs] at h1
  exact h1

/-- Alpha-renaming for ≤→ under binders.
    Derived from subRed_rename_strong by rewriting the LHS. -/
theorem subRed_rename
    {Γ : LNCtx} {s : LNStack} {ann : LNAnn}
    {body u : LNExpr} {x y : String}
    (h : LNSubRed ((x, ann) :: Γ) s (body.open_at 0 (.fvar x)) u)
    (hfx : x ∉ LNCtx.all_fvs Γ) (hfy : y ∉ LNCtx.all_fvs Γ)
    (hfr : x ∉ body.fvs)
    (hfx_ann : x ∉ ann.fvs)
    (hsfresh : ∀ e ∈ s, x ∉ e.fvs)
    : LNSubRed ((y, ann) :: Γ) s (body.open_at 0 (.fvar y)) (u.subst_fvar x (.fvar y)) := by
  have h1 := subRed_rename_strong h hfx hfy hfx_ann
    (fun hne => LNCtx.not_mem_dom_of_not_mem_all_fvs hfy) hsfresh
  -- Rewrite LHS: (body^x)[x↦fvar y] = body^y
  have hlhs : (body.open_at 0 (.fvar x)).subst_fvar x (.fvar y) = body.open_at 0 (.fvar y) := by
    rw [subst_fvar_fvar_open_at]
    simp only [LNExpr.subst_fvar, beq_self_eq_true, ite_true]
    rw [subst_fvar_notin hfr]
  rw [hlhs] at h1
  exact h1

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
      (∀ y, y ∉ L → LNEquivRed.noPromoAt x ((y, .equiv v) :: Γ) s (body.open_at 0 (.fvar y)) (t.open_at 0 (.fvar y))) →
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

/-- Reflexivity is always non-promoting: for any z, Γ, s, u, the reflexive
    EquivRed (corresponding to equivRed_refl) satisfies noPromoAt z.
    This is because equivRed_refl never uses me_pro. -/
theorem equivRed_refl_noPromoAt (z : String) (Γ : LNCtx) (s : LNStack) (u : LNExpr)
    (hlc : u.lc)
    : LNEquivRed.noPromoAt z Γ s u u := by
  match u, hlc with
  | .bvar n, hlc => simp [LNExpr.lc, LNExpr.lc_at] at hlc
  | .fvar _, _ => exact .me_var
  | .top, _ => exact .me_top
  | .app f a, hlc =>
    have hf_lc : f.lc := hlc.1
    have ha_lc : a.lc := hlc.2
    exact .me_app (equivRed_refl_noPromoAt z Γ (a :: s) f hf_lc) (equivRed_refl_noPromoAt z Γ [] a ha_lc)
  | .lam dom body, hlc =>
    have hdom_lc : dom.lc := hlc.1
    have hbody_lc1 : body.lc_at 1 := hlc.2
    match s with
    | [] =>
      exact .me_fun (L := LNCtx.dom Γ)
        (equivRed_refl_noPromoAt z Γ [] dom hdom_lc)
        (fun x hx => equivRed_refl_noPromoAt z ((x, .sub dom) :: Γ) [] _ (LNExpr.lc_at_open_fvar hbody_lc1))
    | α :: s' =>
      exact .me_fop (L := LNCtx.dom Γ)
        (equivRed_refl_noPromoAt z Γ [] dom hdom_lc)
        (fun x _ => equivRed_refl_noPromoAt z ((x, .equiv α) :: Γ) s' _ (LNExpr.lc_at_open_fvar hbody_lc1))
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

/-- SubRed reflexivity is always non-promoting: ms_equ wrapping equivRed_refl_noPromoAt. -/
theorem subRed_refl_noPromoAt (z : String) (Γ : LNCtx) (s : LNStack) (u : LNExpr)
    (hlc : u.lc)
    : LNSubRed.noPromoAt z Γ s u u :=
  .ms_equ (equivRed_refl_noPromoAt z Γ s u hlc)

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
      -- me_bet: L, ∀ y ∉ L, noPromoAt x ((y,.equiv v)::Γ) s body^y t^y, noPromoAt x Γ [] v v'
      (fun L _hbody _hv ih_body ih_v =>
        .me_bet (x :: L)
          (fun y hy => by
            have hy_ne : y ≠ x := by intro heq; exact hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact equivRed_cast_ctx (swap_at_first_cons_ne x y (.equiv _) ann_new _ hy_ne) (ih_body y hy_L))
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
            exact equivRed_cast_ctx (swap_at_first_cons_ne x y (.equiv _) ann_new _ hy_ne) (ih_body y hy_L))
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

private theorem not_mem_dom_cons {x y : String} {ann : LNAnn} {Γ : LNCtx}
    (hne : x ≠ y) (hx : x ∉ LNCtx.dom Γ) : x ∉ LNCtx.dom ((y, ann) :: Γ) :=
  fun hmem => by
    have : LNCtx.dom ((y, ann) :: Γ) = y :: LNCtx.dom Γ := rfl
    rw [this] at hmem
    exact (List.mem_cons.mp hmem).elim (fun h => hne h) (fun h => hx h)

-- noPromoAt_fresh: if x is not in dom(Γ), any derivation satisfies noPromoAt x.
set_option maxHeartbeats 12800000 in
theorem noPromoAt_fresh_equiv
    {x : String} {Γ : LNCtx} {s : LNStack} {u v : LNExpr}
    (h : LNEquivRed Γ s u v) (hx : x ∉ LNCtx.dom Γ)
    : LNEquivRed.noPromoAt x Γ s u v := by
  have go :=
    @LNEquivRed.rec
      (motive_1 := fun Γ s u v _ =>
        ∀ x, x ∉ LNCtx.dom Γ → LNEquivRed.noPromoAt x Γ s u v)
      (motive_2 := fun Γ s u v _ =>
        ∀ x, x ∉ LNCtx.dom Γ → LNSubRed.noPromoAt x Γ s u v)
      -- ME-PRO
      (fun hmem _hsub ih_sub x hx =>
        .me_pro (fun heq => hx (heq ▸ mem_dom_of_mem_equiv hmem)) hmem (ih_sub x hx))
      -- ME-BET
      (fun L _hbody _hv ih_body ih_v x hx =>
        .me_bet (x :: L)
          (fun y hy =>
            ih_body y (fun h => hy (List.mem_cons_of_mem _ h)) x
              (not_mem_dom_cons (Ne.symm (fun heq => hy (heq ▸ List.mem_cons_self _ _))) hx))
          (ih_v x hx))
      -- ME-TOP
      (fun x _hx => .me_top)
      -- ME-VAR
      (fun x _hx => .me_var)
      -- ME-TAP
      (fun x _hx => .me_tap)
      -- ME-APP
      (fun _hu _hv ih_u ih_v x hx => .me_app (ih_u x hx) (ih_v x hx))
      -- ME-FUN
      (fun L _hdom _hbody ih_dom ih_body x hx =>
        .me_fun (x :: L) (ih_dom x hx)
          (fun y hy =>
            ih_body y (fun h => hy (List.mem_cons_of_mem _ h)) x
              (not_mem_dom_cons (Ne.symm (fun heq => hy (heq ▸ List.mem_cons_self _ _))) hx)))
      -- ME-FOP
      (fun L _hdom _hbody ih_dom ih_body x hx =>
        .me_fop (x :: L) (ih_dom x hx)
          (fun y hy =>
            ih_body y (fun h => hy (List.mem_cons_of_mem _ h)) x
              (not_mem_dom_cons (Ne.symm (fun heq => hy (heq ▸ List.mem_cons_self _ _))) hx)))
      -- MS-PRO
      (fun hmem x hx =>
        .ms_pro (fun heq => hx (heq ▸ mem_dom_of_mem_sub hmem)) hmem)
      -- MS-TOP
      (fun x _hx => .ms_top)
      -- MS-EQU
      (fun _hequ ih_equ x hx => .ms_equ (ih_equ x hx))
      -- MS-APP
      (fun _hsub ih_sub x hx => .ms_app (ih_sub x hx))
      -- MS-FUN
      (fun L _hbody ih_body x hx =>
        .ms_fun (x :: L)
          (fun y hy =>
            ih_body y (fun h => hy (List.mem_cons_of_mem _ h)) x
              (not_mem_dom_cons (Ne.symm (fun heq => hy (heq ▸ List.mem_cons_self _ _))) hx)))
      -- MS-FOP
      (fun L _hbody ih_body x hx =>
        .ms_fop (x :: L)
          (fun y hy =>
            ih_body y (fun h => hy (List.mem_cons_of_mem _ h)) x
              (not_mem_dom_cons (Ne.symm (fun heq => hy (heq ▸ List.mem_cons_self _ _))) hx)))
  exact go h x hx

-- noPromoAt_fresh_sub: same for SubRed
set_option maxHeartbeats 3200000 in
theorem noPromoAt_fresh_sub
    {x : String} {Γ : LNCtx} {s : LNStack} {u v : LNExpr}
    (h : LNSubRed Γ s u v) (hx : x ∉ LNCtx.dom Γ)
    : LNSubRed.noPromoAt x Γ s u v := by
  have go :=
    @LNSubRed.rec
      (motive_1 := fun Γ s u v _ =>
        ∀ x, x ∉ LNCtx.dom Γ → LNEquivRed.noPromoAt x Γ s u v)
      (motive_2 := fun Γ s u v _ =>
        ∀ x, x ∉ LNCtx.dom Γ → LNSubRed.noPromoAt x Γ s u v)
      -- ME-PRO
      (fun hmem _hsub ih_sub x hx =>
        .me_pro (fun heq => hx (heq ▸ mem_dom_of_mem_equiv hmem)) hmem (ih_sub x hx))
      -- ME-BET
      (fun L _hbody _hv ih_body ih_v x hx =>
        .me_bet (x :: L)
          (fun y hy =>
            ih_body y (fun h => hy (List.mem_cons_of_mem _ h)) x
              (not_mem_dom_cons (Ne.symm (fun heq => hy (heq ▸ List.mem_cons_self _ _))) hx))
          (ih_v x hx))
      -- ME-TOP
      (fun x _hx => .me_top)
      -- ME-VAR
      (fun x _hx => .me_var)
      -- ME-TAP
      (fun x _hx => .me_tap)
      -- ME-APP
      (fun _hu _hv ih_u ih_v x hx => .me_app (ih_u x hx) (ih_v x hx))
      -- ME-FUN
      (fun L _hdom _hbody ih_dom ih_body x hx =>
        .me_fun (x :: L) (ih_dom x hx)
          (fun y hy =>
            ih_body y (fun h => hy (List.mem_cons_of_mem _ h)) x
              (not_mem_dom_cons (Ne.symm (fun heq => hy (heq ▸ List.mem_cons_self _ _))) hx)))
      -- ME-FOP
      (fun L _hdom _hbody ih_dom ih_body x hx =>
        .me_fop (x :: L) (ih_dom x hx)
          (fun y hy =>
            ih_body y (fun h => hy (List.mem_cons_of_mem _ h)) x
              (not_mem_dom_cons (Ne.symm (fun heq => hy (heq ▸ List.mem_cons_self _ _))) hx)))
      -- MS-PRO
      (fun hmem x hx =>
        .ms_pro (fun heq => hx (heq ▸ mem_dom_of_mem_sub hmem)) hmem)
      -- MS-TOP
      (fun x _hx => .ms_top)
      -- MS-EQU
      (fun _hequ ih_equ x hx => .ms_equ (ih_equ x hx))
      -- MS-APP
      (fun _hsub ih_sub x hx => .ms_app (ih_sub x hx))
      -- MS-FUN
      (fun L _hbody ih_body x hx =>
        .ms_fun (x :: L)
          (fun y hy =>
            ih_body y (fun h => hy (List.mem_cons_of_mem _ h)) x
              (not_mem_dom_cons (Ne.symm (fun heq => hy (heq ▸ List.mem_cons_self _ _))) hx)))
      -- MS-FOP
      (fun L _hbody ih_body x hx =>
        .ms_fop (x :: L)
          (fun y hy =>
            ih_body y (fun h => hy (List.mem_cons_of_mem _ h)) x
              (not_mem_dom_cons (Ne.symm (fun heq => hy (heq ▸ List.mem_cons_self _ _))) hx)))
  exact go h x hx

-- noPromoAt rename: binder rename x → y preserves noPromoAt z (when z ≠ y or x = y)
-- Proved by mutual induction on noPromoAt using the mutual recursor.
set_option maxHeartbeats 12800000 in
private theorem noPromoAt_sub_rename_gen
    {z : String} {Γ : LNCtx} {s : LNStack} {u u' : LNExpr}
    (hnp : LNSubRed.noPromoAt z Γ s u u')
    {x y : String}
    (hinj : x ≠ y → y ∉ LNCtx.dom Γ)
    (hzy : x ≠ y → z ≠ y)
    : LNSubRed.noPromoAt z (ctx_rename Γ x y)
        (s.map (fun e => e.subst_fvar x (.fvar y)))
        (u.subst_fvar x (.fvar y))
        (u'.subst_fvar x (.fvar y)) := by
  -- We prove both motives simultaneously via @LNSubRed.noPromoAt.rec
  exact
    @LNSubRed.noPromoAt.rec z
      (fun Γ s u u' _ =>
        ∀ x y, (x ≠ y → y ∉ LNCtx.dom Γ) → (x ≠ y → z ≠ y) →
          LNEquivRed.noPromoAt z (ctx_rename Γ x y)
            (s.map (fun e => e.subst_fvar x (.fvar y)))
            (u.subst_fvar x (.fvar y))
            (u'.subst_fvar x (.fvar y)))
      (fun Γ s u u' _ =>
        ∀ x y, (x ≠ y → y ∉ LNCtx.dom Γ) → (x ≠ y → z ≠ y) →
          LNSubRed.noPromoAt z (ctx_rename Γ x y)
            (s.map (fun e => e.subst_fvar x (.fvar y)))
            (u.subst_fvar x (.fvar y))
            (u'.subst_fvar x (.fvar y)))
      -- me_pro: z_pro ≠ z, z_pro ≡ α ∈ Γ, sub noPromoAt z on α
      (fun {z_pro Γ_pro s_pro α_pro α'_pro} hne hmem _hnp ih_sub x y hinj hzy => by
        simp only [LNExpr.subst_fvar]
        have ih := ih_sub x y hinj hzy
        have hlook := ctx_rename_lookup hmem hinj
        by_cases hzx : z_pro == x
        · simp [hzx]; simp [hzx] at hlook
          have hne' : y ≠ z := fun heq => by
            by_cases hxy : x = y
            · exact hne (((beq_iff_eq.mp hzx).trans hxy).trans heq)
            · exact hzy hxy heq.symm
          exact .me_pro hne' hlook ih
        · simp [hzx]; simp [hzx] at hlook; exact .me_pro hne hlook ih)
      -- me_bet
      (fun L _hbody _hv ih_body ih_v x y hinj hzy => by
        simp only [LNExpr.subst_fvar]
        rw [subst_fvar_fvar_open_at' _ x y 0 _]
        have ihv := ih_v x y hinj hzy
        simp [List.map] at ihv
        let L' := L ++ [x, y] ++ LNCtx.dom Γ ++ LNCtx.dom (ctx_rename Γ x y)
        apply LNEquivRed.noPromoAt.me_bet (L := L')
        · intro w hw
          have hwL : w ∉ L := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
          have hwx : w ≠ x := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self _ _))))
          have hwy : w ≠ y := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))))
          have ih := ih_body w hwL x y (fun hne hmem => by cases List.mem_cons.mp hmem with | inl heq => exact hwy heq.symm | inr h => exact hinj hne h) hzy
          rw [ctx_rename_cons] at ih
          have hwx_f : ¬(w == x) = true := by rw [beq_iff_eq]; exact hwx
          simp only [hwx_f, ite_false, LNAnn.subst_fvar] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm, subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih
          exact ih
        · exact ihv)
      -- me_top
      (fun _ _ _ _ => by simp [LNExpr.subst_fvar]; exact .me_top)
      -- me_var
      (fun x y _ _ => by simp only [LNExpr.subst_fvar]; split <;> exact .me_var)
      -- me_tap
      (fun _ _ _ _ => by simp only [LNExpr.subst_fvar]; exact .me_tap)
      -- me_app
      (fun _hnp_u _hnp_v ih_u ih_v x y hinj hzy => by
        simp only [LNExpr.subst_fvar]; have ihu := ih_u x y hinj hzy; have ihv := ih_v x y hinj hzy
        simp [List.map] at ihu ihv; exact .me_app ihu ihv)
      -- me_fun
      (fun L _hnp_dom _hnp_body ih_dom ih_body x y hinj hzy => by
        simp only [LNExpr.subst_fvar]
        have ihdom := ih_dom x y hinj hzy; simp [List.map] at ihdom
        let L' := L ++ [x, y] ++ LNCtx.dom Γ ++ LNCtx.dom (ctx_rename Γ x y)
        exact .me_fun L' ihdom (fun w hw => by
          have hwL : w ∉ L := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
          have hwx : w ≠ x := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self _ _))))
          have hwy : w ≠ y := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))))
          have ih := ih_body w hwL x y (fun hne hmem => by cases List.mem_cons.mp hmem with | inl heq => exact hwy heq.symm | inr h => exact hinj hne h) hzy
          rw [ctx_rename_cons] at ih; have hwx_f : ¬(w == x) = true := by rw [beq_iff_eq]; exact hwx
          simp only [hwx_f, ite_false, LNAnn.subst_fvar, List.map] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm, subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih; exact ih))
      -- me_fop
      (fun L _hnp_dom _hnp_body ih_dom ih_body x y hinj hzy => by
        simp only [LNExpr.subst_fvar, List.map]
        have ihdom := ih_dom x y hinj hzy; simp [List.map] at ihdom
        let L' := L ++ [x, y] ++ LNCtx.dom Γ ++ LNCtx.dom (ctx_rename Γ x y)
        exact .me_fop L' ihdom (fun w hw => by
          have hwL : w ∉ L := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
          have hwx : w ≠ x := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self _ _))))
          have hwy : w ≠ y := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))))
          have ih := ih_body w hwL x y (fun hne hmem => by cases List.mem_cons.mp hmem with | inl heq => exact hwy heq.symm | inr h => exact hinj hne h) hzy
          rw [ctx_rename_cons] at ih; have hwx_f : ¬(w == x) = true := by rw [beq_iff_eq]; exact hwx
          simp only [hwx_f, ite_false, LNAnn.subst_fvar] at ih
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm, subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ih; exact ih))
      -- ms_pro: z_pro ≠ z, z_pro ≤ t ∈ Γ
      (fun {z_pro Γ_sp s_sp t_sp} hne hmem x y hinj hzy => by
        simp only [LNExpr.subst_fvar]
        have hlook := ctx_rename_lookup hmem hinj
        by_cases hzx : z_pro == x
        · simp [hzx]; simp [hzx] at hlook
          have hne' : y ≠ z := fun heq => by
            by_cases hxy : x = y
            · exact hne (((beq_iff_eq.mp hzx).trans hxy).trans heq)
            · exact hzy hxy heq.symm
          exact .ms_pro hne' hlook
        · simp [hzx]; simp [hzx] at hlook; exact .ms_pro hne hlook)
      -- ms_top
      (fun _ _ _ _ => by simp [LNExpr.subst_fvar]; exact .ms_top)
      -- ms_equ
      (fun _hnp ih x y hinj hzy => .ms_equ (ih x y hinj hzy))
      -- ms_app
      (fun _hnp ih x y hinj hzy => by simp only [LNExpr.subst_fvar, List.map]; exact .ms_app (ih x y hinj hzy))
      -- ms_fun
      (fun L _hnp ih x y hinj hzy => by
        simp only [LNExpr.subst_fvar, List.map]
        let L' := L ++ [x, y] ++ LNCtx.dom Γ ++ LNCtx.dom (ctx_rename Γ x y)
        exact .ms_fun L' (fun w hw => by
          have hwL : w ∉ L := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
          have hwx : w ≠ x := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self _ _))))
          have hwy : w ≠ y := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))))
          have ihw := ih w hwL x y (fun hne hmem => by cases List.mem_cons.mp hmem with | inl heq => exact hwy heq.symm | inr h => exact hinj hne h) hzy
          rw [ctx_rename_cons] at ihw; have hwx_f : ¬(w == x) = true := by rw [beq_iff_eq]; exact hwx
          simp only [hwx_f, ite_false, LNAnn.subst_fvar, List.map] at ihw
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm, subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ihw; exact ihw))
      -- ms_fop
      (fun L _hnp ih x y hinj hzy => by
        simp only [LNExpr.subst_fvar, List.map]
        let L' := L ++ [x, y] ++ LNCtx.dom Γ ++ LNCtx.dom (ctx_rename Γ x y)
        exact .ms_fop L' (fun w hw => by
          have hwL : w ∉ L := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
          have hwx : w ≠ x := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self _ _))))
          have hwy : w ≠ y := by intro heq; subst heq; exact hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))))
          have ihw := ih w hwL x y (fun hne hmem => by cases List.mem_cons.mp hmem with | inl heq => exact hwy heq.symm | inr h => exact hinj hne h) hzy
          rw [ctx_rename_cons] at ihw; have hwx_f : ¬(w == x) = true := by rw [beq_iff_eq]; exact hwx
          simp only [hwx_f, ite_false, LNAnn.subst_fvar] at ihw
          rw [subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm, subst_fvar_fvar_open_fvar' _ x y w 0 hwx.symm] at ihw; exact ihw))
      Γ s u u' hnp x y hinj hzy

-- Convenience: rename binder x → y in SubRed.noPromoAt under a head entry.
set_option maxHeartbeats 6400000 in
theorem noPromoAt_sub_rename
    {z : String} {Γ : LNCtx} {s : LNStack} {ann : LNAnn}
    {body u : LNExpr} {x y : String}
    (hnp : LNSubRed.noPromoAt z ((x, ann) :: Γ) s (body.open_at 0 (.fvar x)) u)
    (hfx : x ∉ LNCtx.all_fvs Γ) (hfy : y ∉ LNCtx.all_fvs Γ)
    (hfr : x ∉ body.fvs)
    (hfx_ann : x ∉ ann.fvs)
    (hsfresh : ∀ e ∈ s, x ∉ e.fvs)
    (hzy : x ≠ y → z ≠ y)
    : LNSubRed.noPromoAt z ((y, ann) :: Γ) s (body.open_at 0 (.fvar y)) (u.subst_fvar x (.fvar y)) := by
  have h1 := noPromoAt_sub_rename_gen hnp (x := x) (y := y) (fun hne hmem => by
    cases List.mem_cons.mp hmem with
    | inl heq => exact hne heq.symm
    | inr hmem_rest => exact (fun hne => LNCtx.not_mem_dom_of_not_mem_all_fvs hfy) hne hmem_rest) hzy
  rw [ctx_rename_cons, show (x == x) = true from beq_self_eq_true x,
      ann_subst_fvar_notin' hfx_ann, ctx_rename_id_fresh hfx,
      stack_map_subst_id hsfresh] at h1
  have hlhs : (body.open_at 0 (.fvar x)).subst_fvar x (.fvar y) = body.open_at 0 (.fvar y) := by
    rw [subst_fvar_fvar_open_at]
    simp only [LNExpr.subst_fvar, beq_self_eq_true, ite_true]
    rw [subst_fvar_notin hfr]
  rw [hlhs] at h1
  exact h1

/-! #### General substitution infrastructure for subRed_subst_noPromo -/

/-- open_at is a no-op on terms that are already locally closed at depth k. -/
private theorem LNExpr.open_at_lc_at {e : LNExpr} {k : Nat} {u : LNExpr}
    (h : e.lc_at k) : e.open_at k u = e := by
  induction e generalizing k with
  | bvar n => simp [LNExpr.lc_at] at h; simp [LNExpr.open_at, beq_iff_eq]; omega
  | fvar _ => rfl
  | top => rfl
  | lam dom body ih_dom ih_body =>
    simp [LNExpr.lc_at] at h
    simp [LNExpr.open_at, ih_dom h.1, ih_body h.2]
  | app f a ih_f ih_a =>
    simp [LNExpr.lc_at] at h
    simp [LNExpr.open_at, ih_f h.1, ih_a h.2]

/-- General subst_fvar commutes with open_at by fvar, provided the substituted variable
    differs from the opening variable and the replacement term is locally closed at the
    appropriate depth. -/
private theorem subst_fvar_open_fvar_comm (e : LNExpr) (y : String) (v : LNExpr)
    (w : String) (k : Nat)
    (hyw : y ≠ w) (hlc : v.lc_at k)
    : (e.subst_fvar y v).open_at k (.fvar w)
    = (e.open_at k (.fvar w)).subst_fvar y v := by
  induction e generalizing k with
  | bvar n =>
    simp only [LNExpr.subst_fvar, LNExpr.open_at]
    split
    · -- n == k: LHS is (fvar w).subst y v = fvar w (since y ≠ w)
      simp only [LNExpr.subst_fvar]
      have : ¬(w == y) = true := by simp [beq_iff_eq]; exact Ne.symm hyw
      simp [this]
    · -- n ≠ k: both sides are bvar n
      simp [LNExpr.open_at, LNExpr.subst_fvar]
  | fvar z =>
    simp only [LNExpr.subst_fvar]
    split
    · -- z == y: LHS is v.open_at k (fvar w) = v (since v.lc_at k)
      -- RHS is (fvar z).open = fvar z, then subst z → v
      simp only [LNExpr.open_at, LNExpr.subst_fvar]
      rename_i hzy; simp [hzy]
      exact LNExpr.open_at_lc_at hlc
    · -- z ≠ y: both sides pass through
      simp only [LNExpr.open_at, LNExpr.subst_fvar]
      rename_i hzy; simp [hzy]
  | top => rfl
  | lam dom body ih_dom ih_body =>
    simp only [LNExpr.subst_fvar, LNExpr.open_at,
               ih_dom k hlc, ih_body (k+1) (LNExpr.lc_at_mono' (by omega) hlc)]
  | app f a ih_f ih_a =>
    simp only [LNExpr.subst_fvar, LNExpr.open_at, ih_f k hlc, ih_a k hlc]

/-- General commutation: (e.open_at k u).subst_fvar x r = (e.subst_fvar x r).open_at k (u.subst_fvar x r)
    when r is locally closed at the appropriate depth.
    This generalizes subst_fvar_fvar_open_at to arbitrary replacement terms. -/
private theorem subst_fvar_gen_open_at (e : LNExpr) (x : String) (r u : LNExpr) (k : Nat)
    (hlc : r.lc_at k)
    : (e.open_at k u).subst_fvar x r = (e.subst_fvar x r).open_at k (u.subst_fvar x r) := by
  induction e generalizing k with
  | bvar n =>
    simp only [LNExpr.open_at, LNExpr.subst_fvar]
    split <;> rfl
  | fvar z =>
    simp only [LNExpr.open_at, LNExpr.subst_fvar]
    split
    · -- z == x: LHS = r, RHS = r.open_at k (u.subst x r) = r (since r.lc_at k)
      exact (LNExpr.open_at_lc_at hlc).symm
    · rfl
  | top => rfl
  | lam dom body ih_dom ih_body =>
    simp only [LNExpr.open_at, LNExpr.subst_fvar,
               ih_dom k hlc, ih_body (k+1) (LNExpr.lc_at_mono' (by omega) hlc)]
  | app f a ih_f ih_a =>
    simp only [LNExpr.open_at, LNExpr.subst_fvar, ih_f k hlc, ih_a k hlc]

/-- Context with y's entry removed and y substituted by v in all remaining annotations. -/
private def ctx_subst_drop (Γ : LNCtx) (y : String) (v : LNExpr) : LNCtx :=
  Γ.filterMap (fun (z, ann) => if z == y then none else some (z, ann.subst_fvar y v))

private theorem ctx_subst_drop_cons_eq (y : String) (ann : LNAnn) (Γ : LNCtx) (v : LNExpr)
    : ctx_subst_drop ((y, ann) :: Γ) y v = ctx_subst_drop Γ y v := by
  simp [ctx_subst_drop, List.filterMap, beq_self_eq_true]

private theorem ctx_subst_drop_cons_ne {y w : String} (hne : w ≠ y) (ann : LNAnn) (Γ : LNCtx) (v : LNExpr)
    : ctx_subst_drop ((w, ann) :: Γ) y v = (w, ann.subst_fvar y v) :: ctx_subst_drop Γ y v := by
  unfold ctx_subst_drop
  simp only [List.filterMap_cons]
  have : ¬(w == y) = true := by simp [beq_iff_eq]; exact hne
  simp [this]

/-- Lookup in ctx_subst_drop: if z ≠ y and z has annotation ann in Γ,
    then z has annotation ann.subst_fvar y v in ctx_subst_drop Γ y v. -/
private theorem ctx_subst_drop_mem_sub {Γ : LNCtx} {z y : String} {t v : LNExpr}
    (hne : z ≠ y) (hmem : LNCtx.mem_sub Γ z t)
    : LNCtx.mem_sub (ctx_subst_drop Γ y v) z (t.subst_fvar y v) := by
  induction Γ with
  | nil => exact absurd hmem (by simp [LNCtx.mem_sub, LNCtx.lookup'])
  | cons p rest ih =>
    obtain ⟨w, ann_w⟩ := p
    unfold LNCtx.mem_sub LNCtx.lookup' at hmem
    by_cases hwy : w = y
    · subst hwy
      rw [ctx_subst_drop_cons_eq]
      by_cases hwz : w = z
      · subst hwz; exact absurd rfl hne
      · have : ¬(w == z) = true := by simp [beq_iff_eq]; exact hwz
        rw [if_neg (by simp [beq_iff_eq]; exact hwz)] at hmem
        exact ih hmem
    · rw [ctx_subst_drop_cons_ne hwy]
      unfold LNCtx.mem_sub LNCtx.lookup'
      by_cases hwz : w = z
      · subst hwz
        have : (w == w) = true := beq_self_eq_true w
        rw [if_pos this] at hmem ⊢
        cases hmem; rfl
      · have hf : ¬(w == z) = true := by simp [beq_iff_eq]; exact hwz
        rw [if_neg (by simp [beq_iff_eq]; exact hwz)] at hmem
        rw [if_neg (by simp [beq_iff_eq]; exact hwz)]
        exact ih hmem

private theorem ctx_subst_drop_mem_equiv {Γ : LNCtx} {z y : String} {α v : LNExpr}
    (hne : z ≠ y) (hmem : LNCtx.mem_equiv Γ z α)
    : LNCtx.mem_equiv (ctx_subst_drop Γ y v) z (α.subst_fvar y v) := by
  induction Γ with
  | nil => exact absurd hmem (by simp [LNCtx.mem_equiv, LNCtx.lookup'])
  | cons p rest ih =>
    obtain ⟨w, ann_w⟩ := p
    unfold LNCtx.mem_equiv LNCtx.lookup' at hmem
    by_cases hwy : w = y
    · subst hwy
      rw [ctx_subst_drop_cons_eq]
      by_cases hwz : w = z
      · subst hwz; exact absurd rfl hne
      · rw [if_neg (by simp [beq_iff_eq]; exact hwz)] at hmem
        exact ih hmem
    · rw [ctx_subst_drop_cons_ne hwy]
      unfold LNCtx.mem_equiv LNCtx.lookup'
      by_cases hwz : w = z
      · subst hwz
        rw [if_pos (beq_self_eq_true w)] at hmem ⊢
        cases hmem; rfl
      · rw [if_neg (by simp [beq_iff_eq]; exact hwz)] at hmem
        rw [if_neg (by simp [beq_iff_eq]; exact hwz)]
        exact ih hmem

/-- If y ∉ all_fvs Γ, then ctx_subst_drop Γ y v = Γ (no entry for y, annotations don't contain y). -/
private theorem ctx_subst_drop_id {Γ : LNCtx} {y : String} {v : LNExpr}
    (hfresh : y ∉ LNCtx.all_fvs Γ) : ctx_subst_drop Γ y v = Γ := by
  induction Γ with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨z, ann⟩ := p
    have hz : z ≠ y := by
      intro heq; subst heq
      exact hfresh (List.mem_flatMap.mpr ⟨(z, ann), List.mem_cons_self _ _, List.mem_cons_self _ _⟩)
    have hfresh_rest : y ∉ LNCtx.all_fvs rest := fun h =>
      hfresh (List.mem_append_right _ h)
    have hann : y ∉ ann.fvs := by
      intro h; exact hfresh (List.mem_flatMap.mpr ⟨(z, ann), List.mem_cons_self _ _, List.mem_cons_of_mem _ h⟩)
    rw [ctx_subst_drop_cons_ne hz]
    congr 1
    · congr 1; cases ann with
      | sub t => show LNAnn.sub (t.subst_fvar y v) = .sub t; congr 1; exact subst_fvar_notin' hann
      | equiv α => show LNAnn.equiv (α.subst_fvar y v) = .equiv α; congr 1; exact subst_fvar_notin' hann
    · exact ih hfresh_rest

/-- Stack map subst is identity when the variable is fresh. -/
private theorem stack_map_subst_gen_id {s : LNStack} {y : String} {v : LNExpr}
    (hfresh : ∀ e ∈ s, y ∉ e.fvs) : s.map (fun e => e.subst_fvar y v) = s := by
  induction s with
  | nil => rfl
  | cons a rest ih =>
    simp [List.map]
    constructor
    · exact subst_fvar_notin' (hfresh a (List.mem_cons_self _ _))
    · exact ih (fun e he => hfresh e (List.mem_cons_of_mem _ he))

/-! #### noPromoAt annotation swap: change x's annotation without affecting noPromoAt -/

private theorem equivRed_noPromoAt_cast_ctx {x : String} {Γ₁ Γ₂ : LNCtx} {s : LNStack} {e u : LNExpr}
    (h : Γ₁ = Γ₂) (hr : LNEquivRed.noPromoAt x Γ₁ s e u) : LNEquivRed.noPromoAt x Γ₂ s e u :=
  h ▸ hr

private theorem subRed_noPromoAt_cast_ctx {x : String} {Γ₁ Γ₂ : LNCtx} {s : LNStack} {e u : LNExpr}
    (h : Γ₁ = Γ₂) (hr : LNSubRed.noPromoAt x Γ₁ s e u) : LNSubRed.noPromoAt x Γ₂ s e u :=
  h ▸ hr

-- noPromoAt x is independent of x's own annotation: change the head annotation.
-- Since noPromoAt never accesses x's annotation (ms_pro/me_pro both require z ≠ x),
-- the same derivation structure works in any annotation for x.
-- Proved by mutual induction on the noPromoAt using the existing swap_at_first
-- machinery (same approach as noPromoAt_equiv_swap/noPromoAt_sub_swap).
set_option maxHeartbeats 12800000 in
theorem noPromoAt_sub_head_ann_swap
    {x : String} {ann₁ ann₂ : LNAnn} {Γ : LNCtx} {s : LNStack} {u u' : LNExpr}
    (hnp : LNSubRed.noPromoAt x ((x, ann₁) :: Γ) s u u')
    : LNSubRed.noPromoAt x ((x, ann₂) :: Γ) s u u' := by
  -- swap_at_first x ann₂ ((x, ann₁) :: Γ) = (x, ann₂) :: Γ
  -- We use the recursor with motive that outputs noPromoAt in the swapped context
  suffices h : LNSubRed.noPromoAt x (swap_at_first x ann₂ ((x, ann₁) :: Γ)) s u u' by
    rwa [swap_at_first_head] at h
  exact
    @LNSubRed.noPromoAt.rec x
      (fun Γ_full s_full u_full u'_full _ =>
        LNEquivRed.noPromoAt x (swap_at_first x ann₂ Γ_full) s_full u_full u'_full)
      (fun Γ_full s_full u_full u'_full _ =>
        LNSubRed.noPromoAt x (swap_at_first x ann₂ Γ_full) s_full u_full u'_full)
      -- me_pro: z ≠ x, z ≡ α ∈ Γ_full, noPromoAt x on SubRed α → α'
      (fun hne hmem _hnp ih_sub =>
        .me_pro hne (swap_at_first_mem_equiv_ne hne hmem) ih_sub)
      -- me_bet: L, body, v
      (fun L _hbody _hv ih_body ih_v =>
        .me_bet (x :: L)
          (fun y hy => by
            have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact equivRed_noPromoAt_cast_ctx (swap_at_first_cons_ne x y (.equiv _) ann₂ _ hy_ne) (ih_body y hy_L))
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
        .me_fun (x :: L) ih_dom (fun y hy => by
          have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
          have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
          exact equivRed_noPromoAt_cast_ctx (swap_at_first_cons_ne x y (.sub _) ann₂ _ hy_ne) (ih_body y hy_L)))
      -- me_fop
      (fun L _hnp_dom _hnp_body ih_dom ih_body =>
        .me_fop (x :: L) ih_dom (fun y hy => by
          have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
          have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
          exact equivRed_noPromoAt_cast_ctx (swap_at_first_cons_ne x y (.equiv _) ann₂ _ hy_ne) (ih_body y hy_L)))
      -- ms_pro: z ≠ x, z ≤ t ∈ Γ_full
      (fun hne hmem => .ms_pro hne (swap_at_first_mem_sub_ne hne hmem))
      -- ms_top
      .ms_top
      -- ms_equ
      (fun _hnp ih => .ms_equ ih)
      -- ms_app
      (fun _hnp ih => .ms_app ih)
      -- ms_fun
      (fun L _hnp ih =>
        .ms_fun (x :: L) (fun y hy => by
          have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
          have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
          exact subRed_noPromoAt_cast_ctx (swap_at_first_cons_ne x y (.sub _) ann₂ _ hy_ne) (ih y hy_L)))
      -- ms_fop
      (fun L _hnp ih =>
        .ms_fop (x :: L) (fun y hy => by
          have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
          have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
          exact subRed_noPromoAt_cast_ctx (swap_at_first_cons_ne x y (.equiv _) ann₂ _ hy_ne) (ih y hy_L)))
      ((x, ann₁) :: Γ) s u u' hnp

-- noPromoAt when x has no .equiv in the context and x ∉ u.fvs.
-- Generalisation of noPromoAt_fresh_equiv: handles contexts where x IS in dom(Γ)
-- (e.g. with .sub annotation) as long as x ∉ u.fvs.
-- The key case (x at the head with .sub) is the main intended application:
-- `(x, .sub dom) :: Γ_tail` where x ∉ all_fvs(Γ_tail), x ∉ dom.fvs, x ∉ u.fvs.
--
-- NOTE: the `x ∉ u.fvs` condition is NECESSARY for the EquivRed motive.
-- Counterexample without it: context `[(x, .sub .top)]`, stack `[]`,
-- term `app (lam .top (bvar 0)) (fvar x)`.
-- ME-APP pushes (fvar x) onto the stack; ME-FOP pops it into an .equiv
-- annotation for a fresh y; ME-PRO on y triggers SubRed on (fvar x);
-- MS-PRO on x fires (x has .sub .top) → noPromoAt x FAILS.
set_option maxHeartbeats 12800000 in
theorem noPromoAt_no_equiv_fresh
    {x : String} {Γ : LNCtx} {s : LNStack} {u v : LNExpr}
    (h : LNEquivRed Γ s u v)
    (hA : ∀ α, ¬ LNCtx.mem_equiv Γ x α)
    (hB : ∀ z α, LNCtx.mem_equiv Γ z α → x ∉ α.fvs)
    (hC : ∀ e ∈ s, x ∉ e.fvs)
    (hD : x ∉ u.fvs)
    : LNEquivRed.noPromoAt x Γ s u v := by
  have go :=
    @LNEquivRed.rec
      (motive_1 := fun Γ s u v _ =>
        ∀ x,
        (∀ α, ¬ LNCtx.mem_equiv Γ x α) →
        (∀ z α, LNCtx.mem_equiv Γ z α → x ∉ α.fvs) →
        (∀ e ∈ s, x ∉ e.fvs) →
        x ∉ u.fvs →
        LNEquivRed.noPromoAt x Γ s u v)
      (motive_2 := fun Γ s u v _ =>
        ∀ x,
        (∀ α, ¬ LNCtx.mem_equiv Γ x α) →
        (∀ z α, LNCtx.mem_equiv Γ z α → x ∉ α.fvs) →
        (∀ e ∈ s, x ∉ e.fvs) →
        x ∉ u.fvs →
        LNSubRed.noPromoAt x Γ s u v)
      -- ME-PRO: z ≡ α ∈ Γ, SubRed Γ s α α'
      (fun hmem _hsub ih_sub x hA hB hC hD =>
        .me_pro (fun heq => hA _ (heq ▸ hmem)) hmem (ih_sub x hA hB hC (hB _ _ hmem)))
      -- ME-BET: L, body, v; input = app (lam dom body) v
      (fun L _hbody _hv ih_body ih_v x hA hB hC hD =>
        have hD_v : x ∉ LNExpr.fvs _ := fun h => hD (List.mem_append_right _ h)
        have hD_lam : x ∉ LNExpr.fvs _ := fun h => hD (List.mem_append_left _ h)
        have hD_body : x ∉ LNExpr.fvs _ := fun h => hD_lam (List.mem_append_right _ h)
        .me_bet (x :: L)
          (fun y hy =>
            have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            ih_body y hy_L x
              (fun α hmem => by
                simp only [LNCtx.mem_equiv, LNCtx.lookup'] at hmem
                by_cases hyx : y == x
                · exact absurd (beq_iff_eq.mp hyx) hy_ne
                · simp [hyx] at hmem; exact hA α hmem)
              (fun z α hmem => by
                simp only [LNCtx.mem_equiv, LNCtx.lookup'] at hmem
                by_cases hzy : y == z
                · simp [hzy] at hmem; rw [← hmem]; exact hD_v
                · simp [hzy] at hmem; exact hB z α hmem)
              hC
              (LNExpr.not_mem_fvs_open_at _ hD_body (Ne.symm hy_ne)))
          (ih_v x hA hB (fun _ he => absurd he (List.not_mem_nil _)) hD_v))
      -- ME-TOP
      (fun _ _ _ _ _ => .me_top)
      -- ME-VAR
      (fun _ _ _ _ _ => .me_var)
      -- ME-TAP
      (fun _ _ _ _ _ => .me_tap)
      -- ME-APP: app u v
      (fun _hu _hv ih_u ih_v x hA hB hC hD => by
        have hD_u : x ∉ LNExpr.fvs _ := fun h => hD (List.mem_append_left _ h)
        have hD_v : x ∉ LNExpr.fvs _ := fun h => hD (List.mem_append_right _ h)
        exact .me_app
          (ih_u x hA hB (fun e he => by
            cases List.mem_cons.mp he with
            | inl heq => exact heq ▸ hD_v
            | inr hmem => exact hC e hmem) hD_u)
          (ih_v x hA hB (fun _ he => absurd he (List.not_mem_nil _)) hD_v))
      -- ME-FUN: L, dom, body; input = lam dom body, stack = []
      (fun L _hdom _hbody ih_dom ih_body x hA hB hC hD =>
        have hD_dom : x ∉ LNExpr.fvs _ := fun h => hD (List.mem_append_left _ h)
        have hD_body : x ∉ LNExpr.fvs _ := fun h => hD (List.mem_append_right _ h)
        .me_fun (x :: L)
          (ih_dom x hA hB (fun _ he => absurd he (List.not_mem_nil _)) hD_dom)
          (fun y hy =>
            have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
            ih_body y (fun h => hy (List.mem_cons_of_mem _ h)) x
              (fun α hmem => by
                simp only [LNCtx.mem_equiv, LNCtx.lookup'] at hmem
                simp [show ¬(y == x) = true from by simp [beq_iff_eq]; exact hy_ne] at hmem
                exact hA α hmem)
              (fun z α hmem => by
                simp only [LNCtx.mem_equiv, LNCtx.lookup'] at hmem
                by_cases hzy : y == z
                · simp [hzy] at hmem
                · simp [hzy] at hmem; exact hB z α hmem)
              (fun _ he => absurd he (List.not_mem_nil _))
              (LNExpr.not_mem_fvs_open_at _ hD_body (Ne.symm hy_ne))))
      -- ME-FOP: L, dom, body, stack α :: s_rest; input = lam dom body
      (fun L _hdom _hbody ih_dom ih_body x hA hB hC hD =>
        have hD_dom : x ∉ LNExpr.fvs _ := fun h => hD (List.mem_append_left _ h)
        have hD_body : x ∉ LNExpr.fvs _ := fun h => hD (List.mem_append_right _ h)
        have hC_head : x ∉ LNExpr.fvs _ := hC _ (List.mem_cons_self _ _)
        .me_fop (x :: L)
          (ih_dom x hA hB (fun _ he => absurd he (List.not_mem_nil _)) hD_dom)
          (fun y hy =>
            have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
            ih_body y (fun h => hy (List.mem_cons_of_mem _ h)) x
              (fun α hmem => by
                simp only [LNCtx.mem_equiv, LNCtx.lookup'] at hmem
                simp [show ¬(y == x) = true from by simp [beq_iff_eq]; exact hy_ne] at hmem
                exact hA α hmem)
              (fun z α hmem => by
                simp only [LNCtx.mem_equiv, LNCtx.lookup'] at hmem
                by_cases hzy : y == z
                · simp [hzy] at hmem; subst hmem; exact hC_head
                · simp [hzy] at hmem; exact hB z α hmem)
              (fun e he => hC e (List.mem_cons_of_mem _ he))
              (LNExpr.not_mem_fvs_open_at _ hD_body (Ne.symm hy_ne))))
      -- MS-PRO: z ≤ t ∈ Γ
      (fun hmem x _hA _hB _hC hD =>
        .ms_pro (fun heq => by simp only [LNExpr.fvs] at hD; exact hD (heq ▸ List.mem_cons_self _ _)) hmem)
      -- MS-TOP
      (fun _ _ _ _ _ => .ms_top)
      -- MS-EQU
      (fun _hequ ih_equ x hA hB hC hD => .ms_equ (ih_equ x hA hB hC hD))
      -- MS-APP: app u v
      (fun _hsub ih_sub x hA hB hC hD => by
        have hD_u : x ∉ LNExpr.fvs _ := fun h => hD (List.mem_append_left _ h)
        have hD_v : x ∉ LNExpr.fvs _ := fun h => hD (List.mem_append_right _ h)
        exact .ms_app (ih_sub x hA hB (fun e he => by
            cases List.mem_cons.mp he with
            | inl heq => exact heq ▸ hD_v
            | inr hmem => exact hC e hmem) hD_u))
      -- MS-FUN: L, body; input = lam dom body, stack = []
      (fun L _hbody ih_body x hA hB _hC hD =>
        have hD_body : x ∉ LNExpr.fvs _ := fun h => hD (List.mem_append_right _ h)
        .ms_fun (x :: L)
          (fun y hy =>
            have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
            ih_body y (fun h => hy (List.mem_cons_of_mem _ h)) x
              (fun α hmem => by
                simp only [LNCtx.mem_equiv, LNCtx.lookup'] at hmem
                simp [show ¬(y == x) = true from by simp [beq_iff_eq]; exact hy_ne] at hmem
                exact hA α hmem)
              (fun z α hmem => by
                simp only [LNCtx.mem_equiv, LNCtx.lookup'] at hmem
                by_cases hzy : y == z
                · simp [hzy] at hmem
                · simp [hzy] at hmem; exact hB z α hmem)
              (fun _ he => absurd he (List.not_mem_nil _))
              (LNExpr.not_mem_fvs_open_at _ hD_body (Ne.symm hy_ne))))
      -- MS-FOP: L, body, stack α :: s_rest; input = lam dom body
      (fun L _hbody ih_body x hA hB hC hD =>
        have hD_body : x ∉ LNExpr.fvs _ := fun h => hD (List.mem_append_right _ h)
        have hC_head : x ∉ LNExpr.fvs _ := hC _ (List.mem_cons_self _ _)
        .ms_fop (x :: L)
          (fun y hy =>
            have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
            ih_body y (fun h => hy (List.mem_cons_of_mem _ h)) x
              (fun α hmem => by
                simp only [LNCtx.mem_equiv, LNCtx.lookup'] at hmem
                simp [show ¬(y == x) = true from by simp [beq_iff_eq]; exact hy_ne] at hmem
                exact hA α hmem)
              (fun z α hmem => by
                simp only [LNCtx.mem_equiv, LNCtx.lookup'] at hmem
                by_cases hzy : y == z
                · simp [hzy] at hmem; subst hmem; exact hC_head
                · simp [hzy] at hmem; exact hB z α hmem)
              (fun e he => hC e (List.mem_cons_of_mem _ he))
              (LNExpr.not_mem_fvs_open_at _ hD_body (Ne.symm hy_ne))))
  exact go h x hA hB hC hD

/-! #### subRed_subst_noPromo: substitute a general term for a non-promoted variable

By mutual induction on the noPromoAt derivation. The context transformation
is `ctx_subst_drop` (remove y's entry and substitute y → v in remaining annotations)
and the stack transformation is `s.map (subst_fvar y v)`. -/

set_option maxHeartbeats 12800000 in
theorem subRed_subst_noPromo
    {y : String} {Γ : LNCtx} {s : LNStack} {u u' : LNExpr}
    (hnp : LNSubRed.noPromoAt y Γ s u u')
    {v : LNExpr} (hlc_v : v.lc)
    : LNSubRed (ctx_subst_drop Γ y v) (s.map (fun e => e.subst_fvar y v))
               (u.subst_fvar y v) (u'.subst_fvar y v) := by
  exact
    (@LNSubRed.noPromoAt.rec y
      (fun Γ s u u' _ =>
        ∀ v : LNExpr, v.lc →
          LNEquivRed (ctx_subst_drop Γ y v) (s.map (fun e => e.subst_fvar y v))
                     (u.subst_fvar y v) (u'.subst_fvar y v))
      (fun Γ s u u' _ =>
        ∀ v : LNExpr, v.lc →
          LNSubRed (ctx_subst_drop Γ y v) (s.map (fun e => e.subst_fvar y v))
                   (u.subst_fvar y v) (u'.subst_fvar y v))
      -- ═══════════════════ EquivRed cases ═══════════════════
      -- me_pro: z ≠ y, z ≡ α ∈ Γ, SubRed.noPromoAt y Γ s α α'
      (fun {z Γ_pro s_pro α α'} hne hmem _hnp ih_sub v hlcv => by
        simp only [LNExpr.subst_fvar]
        have hne_beq : ¬(z == y) = true := by simp [beq_iff_eq]; exact hne
        simp [hne_beq]
        exact .me_pro (ctx_subst_drop_mem_equiv hne hmem) (ih_sub v hlcv))
      -- me_bet: L, body, v_bet
      (fun {Γ_bet s_bet dom body t v_bet v'_bet} L _hbody _hv ih_body ih_v v hlcv => by
        simp only [LNExpr.subst_fvar]
        rw [subst_fvar_gen_open_at t y v v'_bet 0 hlcv]
        let L' := y :: L
        apply LNEquivRed.me_bet (L := L')
        · intro w hw
          have hwL : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have ih := ih_body w hwL v hlcv
          rw [ctx_subst_drop_cons_ne hwy] at ih
          rw [← subst_fvar_open_fvar_comm body y v w 0 hwy.symm hlcv,
              ← subst_fvar_open_fvar_comm t y v w 0 hwy.symm hlcv] at ih
          exact ih
        · have ihv := ih_v v hlcv
          simp [List.map] at ihv
          exact ihv)
      -- me_top
      (fun v _hlcv => by simp [LNExpr.subst_fvar]; exact .me_top)
      -- me_var
      (fun {_ _ z} v hlcv => by
        simp only [LNExpr.subst_fvar]
        by_cases hzy : z == y
        · simp [hzy]; exact equivRed_refl _ _ v hlcv
        · simp [hzy]; exact .me_var)
      -- me_tap
      (fun v _hlcv => by simp only [LNExpr.subst_fvar]; exact .me_tap)
      -- me_app
      (fun _hnp_u _hnp_v ih_u ih_v v hlcv => by
        simp only [LNExpr.subst_fvar, List.map]
        exact .me_app (ih_u v hlcv) (ih_v v hlcv))
      -- me_fun
      (fun {Γ_fun dom dom' body body'} L _hnp_dom _hnp_body ih_dom ih_body v hlcv => by
        simp only [LNExpr.subst_fvar, List.map]
        let L' := y :: L
        exact .me_fun L' (ih_dom v hlcv) (fun w hw => by
          have hwL : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have ih := ih_body w hwL v hlcv
          rw [ctx_subst_drop_cons_ne hwy] at ih
          simp [List.map] at ih
          rw [← subst_fvar_open_fvar_comm body y v w 0 hwy.symm (by exact hlcv),
              ← subst_fvar_open_fvar_comm body' y v w 0 hwy.symm (by exact hlcv)] at ih
          exact ih))
      -- me_fop
      (fun {Γ_fop s_fop α dom dom' body body'} L _hnp_dom _hnp_body ih_dom ih_body v hlcv => by
        simp only [LNExpr.subst_fvar, List.map]
        let L' := y :: L
        exact .me_fop L' (ih_dom v hlcv) (fun w hw => by
          have hwL : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have ih := ih_body w hwL v hlcv
          rw [ctx_subst_drop_cons_ne hwy] at ih
          rw [← subst_fvar_open_fvar_comm body y v w 0 hwy.symm (by exact hlcv),
              ← subst_fvar_open_fvar_comm body' y v w 0 hwy.symm (by exact hlcv)] at ih
          exact ih))
      -- ═══════════════════ SubRed cases ═══════════════════
      -- ms_pro: z ≠ y, z ≤ t ∈ Γ
      (fun {z Γ_sp s_sp t_sp} hne hmem v _hlcv => by
        simp only [LNExpr.subst_fvar]
        have hne_beq : ¬(z == y) = true := by simp [beq_iff_eq]; exact hne
        simp [hne_beq]
        exact .ms_pro (ctx_subst_drop_mem_sub hne hmem))
      -- ms_top
      (fun v _hlcv => by simp [LNExpr.subst_fvar]; exact .ms_top)
      -- ms_equ
      (fun _hnp ih v hlcv => .ms_equ (ih v hlcv))
      -- ms_app
      (fun _hnp ih v hlcv => by
        simp only [LNExpr.subst_fvar, List.map]; exact .ms_app (ih v hlcv))
      -- ms_fun
      (fun {Γ_sf dom body body'} L _hnp ih v hlcv => by
        simp only [LNExpr.subst_fvar, List.map]
        let L' := y :: L
        exact .ms_fun L' (fun w hw => by
          have hwL : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have ihw := ih w hwL v hlcv
          rw [ctx_subst_drop_cons_ne hwy, show List.map (fun e => LNExpr.subst_fvar e y v) [] = [] from rfl] at ihw
          rw [← subst_fvar_open_fvar_comm body y v w 0 hwy.symm (by exact hlcv),
              ← subst_fvar_open_fvar_comm body' y v w 0 hwy.symm (by exact hlcv)] at ihw
          exact ihw))
      -- ms_fop
      (fun {Γ_sf s_sf α dom body body'} L _hnp ih v hlcv => by
        simp only [LNExpr.subst_fvar, List.map]
        let L' := y :: L
        exact .ms_fop L' (fun w hw => by
          have hwL : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have ihw := ih w hwL v hlcv
          rw [ctx_subst_drop_cons_ne hwy] at ihw
          rw [← subst_fvar_open_fvar_comm body y v w 0 hwy.symm (by exact hlcv),
              ← subst_fvar_open_fvar_comm body' y v w 0 hwy.symm (by exact hlcv)] at ihw
          exact ihw))
      Γ s u u' hnp) v hlc_v

/-- Lookup uniqueness for equiv annotations. -/
private theorem mem_equiv_unique {Γ : LNCtx} {x : String} {α α₂ : LNExpr}
    (h1 : LNCtx.mem_equiv Γ x α) (h2 : LNCtx.mem_equiv Γ x α₂) : α = α₂ := by
  simp [LNCtx.mem_equiv] at h1 h2; rw [h1] at h2; cases h2; rfl

-- Substitution preserves noPromoAt z: if y is not promoted and z is not promoted,
-- then substituting y -> v preserves noPromoAt z.
-- Proved by mutual induction on noPromoAt y, carrying noPromoAt z and decomposing
-- it at each case. The EquivRed/SubRed output is co-proved alongside noPromoAt z.
set_option maxHeartbeats 25600000 in
theorem subRed_subst_noPromo_noPromoAt
    {y : String} {Γ : LNCtx} {s : LNStack} {u u' : LNExpr}
    (hnp : LNSubRed.noPromoAt y Γ s u u')
    {z : String} (hzy : z ≠ y)
    (hnp_z : LNSubRed.noPromoAt z Γ s u u')
    {v : LNExpr} (hlc_v : v.lc)
    : LNSubRed.noPromoAt z (ctx_subst_drop Γ y v) (s.map (fun e => e.subst_fvar y v))
               (u.subst_fvar y v) (u'.subst_fvar y v) := by
  exact
    (@LNSubRed.noPromoAt.rec y
      -- motive_1: EquivRed.noPromoAt y -> produces EquivRed.noPromoAt z after subst
      (fun Γ s u u' _ =>
        ∀ z, z ≠ y → LNEquivRed.noPromoAt z Γ s u u' → ∀ v : LNExpr, v.lc →
          LNEquivRed.noPromoAt z (ctx_subst_drop Γ y v) (s.map (fun e => e.subst_fvar y v))
                     (u.subst_fvar y v) (u'.subst_fvar y v))
      -- motive_2: SubRed.noPromoAt y -> produces SubRed.noPromoAt z after subst
      (fun Γ s u u' _ =>
        ∀ z, z ≠ y → LNSubRed.noPromoAt z Γ s u u' → ∀ v : LNExpr, v.lc →
          LNSubRed.noPromoAt z (ctx_subst_drop Γ y v) (s.map (fun e => e.subst_fvar y v))
                   (u.subst_fvar y v) (u'.subst_fvar y v))
      -- ═══════════════════ EquivRed cases ═══════════════════
      -- me_pro: z_pro ≠ y, z_pro ≡ α ∈ Γ, SubRed.noPromoAt y Γ s α α'
      (fun {z_pro Γ_pro s_pro α α'} hne hmem _hnp ih_sub z hzy hnp_z v hlcv => by
        simp only [LNExpr.subst_fvar]
        have hne_beq : ¬(z_pro == y) = true := by simp [beq_iff_eq]; exact hne
        simp [hne_beq]
        -- hnp_z on (fvar z_pro, α'): must be me_pro or me_var
        cases hnp_z with
        | me_pro hne_z hmem_z hnp_z_sub =>
          have hα_eq := mem_equiv_unique hmem hmem_z; subst hα_eq
          exact .me_pro hne_z (ctx_subst_drop_mem_equiv hne hmem_z) (ih_sub z hzy hnp_z_sub v hlcv)
        | me_var =>
          simp only [LNExpr.subst_fvar, hne_beq]; exact .me_var)
      -- me_bet: sorry for dependent elimination issues
      (fun _ _ _ _ _ _ _ _ _ _ => sorry)
      -- me_top
      (fun z _hzy _hnp_z v _hlcv => by simp [LNExpr.subst_fvar]; exact .me_top)
      -- me_var
      (fun {_ _ w} z hzy _hnp_z v hlcv => by
        simp only [LNExpr.subst_fvar]
        by_cases hwy : w == y
        · simp [hwy]; exact equivRed_refl_noPromoAt z _ _ v hlcv
        · simp [hwy]; exact .me_var)
      -- me_tap
      (fun z _hzy _hnp_z v _hlcv => by simp only [LNExpr.subst_fvar]; exact .me_tap)
      -- me_app
      (fun {Γ_a s_a u_a u'_a v_a v'_a} _hnp_u _hnp_v ih_u ih_v z hzy hnp_z v hlcv => by
        simp only [LNExpr.subst_fvar, List.map]
        -- hnp_z : noPromoAt z Γ_a s_a (.app u_a v_a) (.app u'_a v'_a)
        -- We need to invert hnp_z. Cases fails for me_bet due to dependent elimination.
        -- Use generalize to abstract the output before cases.
        revert ih_u ih_v
        generalize he : LNExpr.app u'_a v'_a = out at hnp_z
        intro ih_u ih_v
        cases hnp_z with
        | me_app hnp_z_u hnp_z_v =>
          cases he
          exact .me_app (ih_u z hzy hnp_z_u v hlcv) (ih_v z hzy hnp_z_v v hlcv)
        | me_bet L_z hbody_z hv_z =>
          -- The z-derivation used me_bet while y used me_app. To apply ih_u/ih_v we
          -- need the me_app decomposition of hnp_z, i.e., an inversion lemma
          -- (noPromoAt_app_app_inv) converting a me_bet derivation into me_app pieces.
          -- This requires proving that any noPromoAt on (.app (.lam ..) v) (.app u' v')
          -- admits an me_app factorization when u' is a lambda (guaranteed by the
          -- y-derivation via me_fop). Deferred pending a dedicated inversion lemma.
          simp only [← he, LNExpr.subst_fvar, List.map]
          exact .me_app (ih_u z hzy sorry v hlcv) (ih_v z hzy sorry v hlcv)
        | me_tap =>
          exact absurd he (by simp [LNExpr.app]))
      -- me_fun
      (fun {Γ_fun dom dom' body body'} L _hnp_dom _hnp_body ih_dom ih_body z hzy hnp_z v hlcv => by
        simp only [LNExpr.subst_fvar, List.map]
        cases hnp_z with
        | me_fun L_z hnp_z_dom hnp_z_body =>
          let L' := y :: L ++ L_z
          exact .me_fun L' (ih_dom z hzy hnp_z_dom v hlcv) (fun w hw => by
            have hwL : w ∉ L := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_left _ h))
            have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
            have hwLz : w ∉ L_z := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_right _ h))
            have ih := ih_body w hwL z hzy (hnp_z_body w hwLz) v hlcv
            rw [ctx_subst_drop_cons_ne hwy] at ih
            simp [List.map] at ih
            rw [← subst_fvar_open_fvar_comm body y v w 0 hwy.symm (by exact hlcv),
                ← subst_fvar_open_fvar_comm body' y v w 0 hwy.symm (by exact hlcv)] at ih
            exact ih))
      -- me_fop
      (fun {Γ_fop s_fop α dom dom' body body'} L _hnp_dom _hnp_body ih_dom ih_body z hzy hnp_z v hlcv => by
        simp only [LNExpr.subst_fvar, List.map]
        cases hnp_z with
        | me_fop L_z hnp_z_dom hnp_z_body =>
          let L' := y :: L ++ L_z
          exact .me_fop L' (ih_dom z hzy hnp_z_dom v hlcv) (fun w hw => by
            have hwL : w ∉ L := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_left _ h))
            have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
            have hwLz : w ∉ L_z := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_right _ h))
            have ih := ih_body w hwL z hzy (hnp_z_body w hwLz) v hlcv
            rw [ctx_subst_drop_cons_ne hwy] at ih
            rw [← subst_fvar_open_fvar_comm body y v w 0 hwy.symm (by exact hlcv),
                ← subst_fvar_open_fvar_comm body' y v w 0 hwy.symm (by exact hlcv)] at ih
            exact ih))
      -- ═══════════════════ SubRed cases ═══════════════════
      -- ms_pro: z_pro ≠ y, z_pro ≤ t ∈ Γ
      (fun {z_pro Γ_sp s_sp t_sp} hne hmem z hzy hnp_z v _hlcv => by
        simp only [LNExpr.subst_fvar]
        have hne_beq : ¬(z_pro == y) = true := by simp [beq_iff_eq]; exact hne
        simp [hne_beq]
        cases hnp_z with
        | ms_pro hne_z hmem_z => exact .ms_pro hne_z (ctx_subst_drop_mem_sub hne hmem_z)
        | ms_top => exact .ms_top
        | ms_equ hnp_z_eq =>
          cases hnp_z_eq with
          | me_pro hne_z hmem_z _ =>
            exact absurd (no_sub_and_equiv hmem hmem_z) False.elim
          | me_var => simp only [LNExpr.subst_fvar, hne_beq]; exact .ms_equ .me_var)
      -- ms_top
      (fun z _hzy _hnp_z v _hlcv => by simp [LNExpr.subst_fvar]; exact .ms_top)
      -- ms_equ
      (fun hnp_y ih z hzy hnp_z v hlcv => by
        cases hnp_z with
        | ms_equ hnp_z_eq => exact .ms_equ (ih z hzy hnp_z_eq v hlcv)
        | ms_top => exact .ms_top
        | ms_pro hne_z hmem_z =>
          -- u = fvar z_pro, u' = t from mem_sub. hnp_y : EquivRed.noPromoAt y ... (fvar z_pro) t
          -- me_pro on z_pro would give mem_equiv, contradicting mem_sub (no_sub_and_equiv).
          -- So hnp_y must be me_var, hence t = fvar z_pro, hence u = u' after subst.
          cases hnp_y with
          | me_var =>
            -- u = u' = fvar z_pro. After subst both sides are the same.
            simp only [LNExpr.subst_fvar]
            exact subRed_refl_noPromoAt z _ _ _ (by
              show (LNExpr.subst_fvar (.fvar _) y v).lc
              simp only [LNExpr.subst_fvar]
              split
              · exact hlcv
              · exact True.intro)
          | me_pro hne_y hmem_equiv _ =>
            exact absurd (no_sub_and_equiv hmem_z hmem_equiv) False.elim
        | _ => sorry -- ms_app/ms_fun/ms_fop: structural mismatch (y used ms_equ, z used SubRed decomposition)
        )
      -- ms_app
      (fun _hnp ih z hzy hnp_z v hlcv => by
        simp only [LNExpr.subst_fvar, List.map]
        cases hnp_z with
        | ms_app hnp_z_sub => exact .ms_app (ih z hzy hnp_z_sub v hlcv)
        | ms_equ hnp_z_eq => sorry) -- structural mismatch: y used ms_app, z used ms_equ; needs me_bet inversion
      -- ms_fun
      (fun {Γ_sf dom body body'} L _hnp ih z hzy hnp_z v hlcv => by
        simp only [LNExpr.subst_fvar, List.map]
        cases hnp_z with
        | ms_fun L_z h_z =>
          let L' := y :: L ++ L_z
          exact .ms_fun L' (fun w hw => by
            have hwL : w ∉ L := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_left _ h))
            have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
            have hwLz : w ∉ L_z := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_right _ h))
            have ihw := ih w hwL z hzy (h_z w hwLz) v hlcv
            rw [ctx_subst_drop_cons_ne hwy, show List.map (fun e => LNExpr.subst_fvar e y v) [] = [] from rfl] at ihw
            rw [← subst_fvar_open_fvar_comm body y v w 0 hwy.symm (by exact hlcv),
                ← subst_fvar_open_fvar_comm body' y v w 0 hwy.symm (by exact hlcv)] at ihw
            exact ihw)
        | ms_equ hnp_z_eq =>
          cases hnp_z_eq with
          | me_fun L_z hnp_z_dom hnp_z_body =>
            let L' := y :: L ++ L_z
            exact .ms_fun L' (fun w hw => by
              have hwL : w ∉ L := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_left _ h))
              have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
              have hwLz : w ∉ L_z := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_right _ h))
              have ihw := ih w hwL z hzy (.ms_equ (hnp_z_body w hwLz)) v hlcv
              rw [ctx_subst_drop_cons_ne hwy, show List.map (fun e => LNExpr.subst_fvar e y v) [] = [] from rfl] at ihw
              rw [← subst_fvar_open_fvar_comm body y v w 0 hwy.symm (by exact hlcv),
                  ← subst_fvar_open_fvar_comm body' y v w 0 hwy.symm (by exact hlcv)] at ihw
              exact ihw))
      -- ms_fop
      (fun {Γ_sf s_sf α dom body body'} L _hnp ih z hzy hnp_z v hlcv => by
        simp only [LNExpr.subst_fvar, List.map]
        cases hnp_z with
        | ms_fop L_z h_z =>
          let L' := y :: L ++ L_z
          exact .ms_fop L' (fun w hw => by
            have hwL : w ∉ L := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_left _ h))
            have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
            have hwLz : w ∉ L_z := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_right _ h))
            have ihw := ih w hwL z hzy (h_z w hwLz) v hlcv
            rw [ctx_subst_drop_cons_ne hwy] at ihw
            rw [← subst_fvar_open_fvar_comm body y v w 0 hwy.symm (by exact hlcv),
                ← subst_fvar_open_fvar_comm body' y v w 0 hwy.symm (by exact hlcv)] at ihw
            exact ihw)
        | ms_equ hnp_z_eq =>
          cases hnp_z_eq with
          | me_fop L_z hnp_z_dom hnp_z_body =>
            let L' := y :: L ++ L_z
            exact .ms_fop L' (fun w hw => by
              have hwL : w ∉ L := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_left _ h))
              have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
              have hwLz : w ∉ L_z := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_right _ h))
              have ihw := ih w hwL z hzy (.ms_equ (hnp_z_body w hwLz)) v hlcv
              rw [ctx_subst_drop_cons_ne hwy] at ihw
              rw [← subst_fvar_open_fvar_comm body y v w 0 hwy.symm (by exact hlcv),
                  ← subst_fvar_open_fvar_comm body' y v w 0 hwy.symm (by exact hlcv)] at ihw
              exact ihw))
      Γ s u u' hnp) z hzy hnp_z v hlc_v

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
Note: ME-BET now uses `.equiv v` (not `.sub dom`) for the body context,
matching the paper's semantics. This eliminates the annotation mismatch
that previously blocked the ME-BET/MS-FOP case. -/

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

/-! ### Reduction preserves local closure -/

/-- Extract lc from context membership (equiv). -/
private theorem mem_equiv_lc {Γ : LNCtx} {x : String} {α : LNExpr}
    (hmem : LNCtx.mem_equiv Γ x α) (hwf : Γ.wf) : α.lc := by
  induction Γ with
  | nil => simp [LNCtx.mem_equiv, LNCtx.lookup'] at hmem
  | cons p rest ih =>
    obtain ⟨y, ann⟩ := p
    simp only [LNCtx.mem_equiv, LNCtx.lookup'] at hmem
    by_cases h : y == x
    · simp [h] at hmem; cases hmem
      exact hwf (y, .equiv α) (List.mem_cons_self _ _)
    · simp [h] at hmem
      exact ih hmem (fun q hq => hwf q (List.mem_cons_of_mem _ hq))

/-- Extract lc from context membership (sub). -/
private theorem mem_sub_lc {Γ : LNCtx} {x : String} {t : LNExpr}
    (hmem : LNCtx.mem_sub Γ x t) (hwf : Γ.wf) : t.lc := by
  induction Γ with
  | nil => simp [LNCtx.mem_sub, LNCtx.lookup'] at hmem
  | cons p rest ih =>
    obtain ⟨y, ann⟩ := p
    simp only [LNCtx.mem_sub, LNCtx.lookup'] at hmem
    by_cases h : y == x
    · simp [h] at hmem; cases hmem
      exact hwf (y, .sub t) (List.mem_cons_self _ _)
    · simp [h] at hmem
      exact ih hmem (fun q hq => hwf q (List.mem_cons_of_mem _ hq))

set_option maxHeartbeats 1600000 in
/-- Equivalence reduction preserves local closure. -/
theorem equivRed_preserves_lc
    {Γ : LNCtx} {s : LNStack} {u v : LNExpr}
    (h : LNEquivRed Γ s u v) (hlc : u.lc) (hwf : Γ.wf) (hswf : s.wf)
    : v.lc := by
  have go :=
    @LNEquivRed.rec
      (motive_1 := fun Γ s u v _ => Γ.wf → s.wf → u.lc → v.lc)
      (motive_2 := fun Γ s u v _ => Γ.wf → s.wf → u.lc → v.lc)
      -- me_pro: result is α' from SubRed Γ s α α'
      (fun hmem _hsub ih_sub hwf hswf _hlc =>
        ih_sub hwf hswf (mem_equiv_lc hmem hwf))
      -- me_bet: result is t.open_at 0 v'
      (fun (L : List String) _hbody _hv ih_body ih_v hwf hswf hlc => by
        rename_i Γ_i s_i dom_i body_i t_i v_i v'_i
        have hv'_lc := ih_v hwf (fun _ he => absurd he (List.not_mem_nil _)) hlc.2
        obtain ⟨x, hx_fresh⟩ := exists_fresh_string (L ++ t_i.fvs)
        have hx_L : x ∉ L := fun h => hx_fresh (List.mem_append_left _ h)
        have hx_t : x ∉ t_i.fvs := fun h => hx_fresh (List.mem_append_right _ h)
        have hwf_ext : LNCtx.wf ((x, .equiv v_i) :: Γ_i) :=
          fun p hp => by cases hp with
          | head => exact hlc.2
          | tail _ hmem => exact hwf p hmem
        have ht_x_lc := ih_body x hx_L hwf_ext hswf (LNExpr.lc_at_open_fvar hlc.1.2)
        have ht_lc1 := LNExpr.lc_at_1_of_open_lc ht_x_lc hx_t
        exact LNExpr.lc_at_open ht_lc1 hv'_lc)
      -- me_top
      (fun _hwf _hswf _hlc => trivial)
      -- me_var
      (fun _hwf _hswf _hlc => trivial)
      -- me_tap
      (fun _hwf _hswf _hlc => trivial)
      -- me_app
      (fun _hu _hv ih_u ih_v hwf hswf hlc =>
        ⟨ih_u hwf (fun e he => by cases he with | head => exact hlc.2 | tail _ h => exact hswf e h) hlc.1,
         ih_v hwf (fun _ he => absurd he (List.not_mem_nil _)) hlc.2⟩)
      -- me_fun: goal shape is (lam dom' body').lc = dom'.lc ∧ body'.lc_at 1
      (fun (L : List String) _hdom _hbody ih_dom ih_body hwf hswf hlc => by
        rename_i Γ_i dom_i dom'_i body_i body'_i
        constructor
        · exact ih_dom hwf hswf hlc.1
        · obtain ⟨x, hx_fresh⟩ := exists_fresh_string (L ++ body'_i.fvs)
          have hx_L : x ∉ L := fun h => hx_fresh (List.mem_append_left _ h)
          have hx_body' : x ∉ body'_i.fvs := fun h => hx_fresh (List.mem_append_right _ h)
          have hwf_ext : LNCtx.wf ((x, .sub dom_i) :: Γ_i) :=
            fun p hp => by cases hp with
            | head => exact hlc.1
            | tail _ hmem => exact hwf p hmem
          have hbody'_x_lc := ih_body x hx_L hwf_ext hswf (LNExpr.lc_at_open_fvar hlc.2)
          exact LNExpr.lc_at_1_of_open_lc hbody'_x_lc hx_body')
      -- me_fop: stack is α :: s_i
      (fun (L : List String) _hdom _hbody ih_dom ih_body hwf hswf hlc => by
        rename_i Γ_i s_i α_i dom_i dom'_i body_i body'_i
        have hα_lc : α_i.lc := hswf _ (List.mem_cons_self _ _)
        have hs_wf : LNStack.wf s_i := fun e he => hswf e (List.mem_cons_of_mem _ he)
        constructor
        · exact ih_dom hwf (fun _ he => absurd he (List.not_mem_nil _)) hlc.1
        · obtain ⟨x, hx_fresh⟩ := exists_fresh_string (L ++ body'_i.fvs)
          have hx_L : x ∉ L := fun h => hx_fresh (List.mem_append_left _ h)
          have hx_body' : x ∉ body'_i.fvs := fun h => hx_fresh (List.mem_append_right _ h)
          have hwf_ext : LNCtx.wf ((x, .equiv α_i) :: Γ_i) :=
            fun p hp => by cases hp with
            | head => exact hα_lc
            | tail _ hmem => exact hwf p hmem
          have hbody'_x_lc := ih_body x hx_L hwf_ext hs_wf (LNExpr.lc_at_open_fvar hlc.2)
          exact LNExpr.lc_at_1_of_open_lc hbody'_x_lc hx_body')
      -- ms_pro
      (fun hmem hwf _hswf _hlc => mem_sub_lc hmem hwf)
      -- ms_top
      (fun _hwf _hswf _hlc => trivial)
      -- ms_equ
      (fun _hequ ih_equ hwf hswf hlc => ih_equ hwf hswf hlc)
      -- ms_app
      (fun _hsub ih_sub hwf hswf hlc =>
        ⟨ih_sub hwf (fun e he => by cases he with | head => exact hlc.2 | tail _ h => exact hswf e h) hlc.1, hlc.2⟩)
      -- ms_fun: stack is [], result is lam dom body'
      (fun (L : List String) _hbody ih_body hwf _hswf hlc => by
        rename_i Γ_i dom_i body_i body'_i
        constructor
        · exact hlc.1
        · obtain ⟨x, hx_fresh⟩ := exists_fresh_string (L ++ body'_i.fvs)
          have hx_L : x ∉ L := fun h => hx_fresh (List.mem_append_left _ h)
          have hx_body' : x ∉ body'_i.fvs := fun h => hx_fresh (List.mem_append_right _ h)
          have hwf_ext : LNCtx.wf ((x, .sub dom_i) :: Γ_i) :=
            fun p hp => by cases hp with
            | head => exact hlc.1
            | tail _ hmem => exact hwf p hmem
          have hbody'_x_lc := ih_body x hx_L hwf_ext (fun _ he => absurd he (List.not_mem_nil _)) (LNExpr.lc_at_open_fvar hlc.2)
          exact LNExpr.lc_at_1_of_open_lc hbody'_x_lc hx_body')
      -- ms_fop: stack is α :: s_i
      (fun (L : List String) _hbody ih_body hwf hswf hlc => by
        rename_i Γ_i s_i α_i dom_i body_i body'_i
        have hα_lc : α_i.lc := hswf _ (List.mem_cons_self _ _)
        have hs_wf : LNStack.wf s_i := fun e he => hswf e (List.mem_cons_of_mem _ he)
        constructor
        · exact hlc.1
        · obtain ⟨x, hx_fresh⟩ := exists_fresh_string (L ++ body'_i.fvs)
          have hx_L : x ∉ L := fun h => hx_fresh (List.mem_append_left _ h)
          have hx_body' : x ∉ body'_i.fvs := fun h => hx_fresh (List.mem_append_right _ h)
          have hwf_ext : LNCtx.wf ((x, .equiv α_i) :: Γ_i) :=
            fun p hp => by cases hp with
            | head => exact hα_lc
            | tail _ hmem => exact hwf p hmem
          have hbody'_x_lc := ih_body x hx_L hwf_ext hs_wf (LNExpr.lc_at_open_fvar hlc.2)
          exact LNExpr.lc_at_1_of_open_lc hbody'_x_lc hx_body')
  exact go h hwf hswf hlc

set_option maxHeartbeats 1600000 in
/-- Subtyping reduction preserves local closure. Derived from the same mutual
    induction as equivRed_preserves_lc, using @LNSubRed.rec. -/
theorem subRed_preserves_lc
    {Γ : LNCtx} {s : LNStack} {u v : LNExpr}
    (h : LNSubRed Γ s u v) (hlc : u.lc) (hwf : Γ.wf) (hswf : s.wf)
    : v.lc := by
  have go :=
    @LNSubRed.rec
      (motive_1 := fun Γ s u v _ => Γ.wf → s.wf → u.lc → v.lc)
      (motive_2 := fun Γ s u v _ => Γ.wf → s.wf → u.lc → v.lc)
      -- me_pro
      (fun hmem _hsub ih_sub hwf hswf _hlc =>
        ih_sub hwf hswf (mem_equiv_lc hmem hwf))
      -- me_bet
      (fun (L : List String) _hbody _hv ih_body ih_v hwf hswf hlc => by
        rename_i Γ_i s_i dom_i body_i t_i v_i v'_i
        have hv'_lc := ih_v hwf (fun _ he => absurd he (List.not_mem_nil _)) hlc.2
        obtain ⟨x, hx_fresh⟩ := exists_fresh_string (L ++ t_i.fvs)
        have hx_L : x ∉ L := fun h => hx_fresh (List.mem_append_left _ h)
        have hx_t : x ∉ t_i.fvs := fun h => hx_fresh (List.mem_append_right _ h)
        have hwf_ext : LNCtx.wf ((x, .equiv v_i) :: Γ_i) :=
          fun p hp => by cases hp with
          | head => exact hlc.2
          | tail _ hmem => exact hwf p hmem
        have ht_x_lc := ih_body x hx_L hwf_ext hswf (LNExpr.lc_at_open_fvar hlc.1.2)
        have ht_lc1 := LNExpr.lc_at_1_of_open_lc ht_x_lc hx_t
        exact LNExpr.lc_at_open ht_lc1 hv'_lc)
      -- me_top
      (fun _hwf _hswf _hlc => trivial)
      -- me_var
      (fun _hwf _hswf _hlc => trivial)
      -- me_tap
      (fun _hwf _hswf _hlc => trivial)
      -- me_app
      (fun _hu _hv ih_u ih_v hwf hswf hlc =>
        ⟨ih_u hwf (fun e he => by cases he with | head => exact hlc.2 | tail _ h => exact hswf e h) hlc.1,
         ih_v hwf (fun _ he => absurd he (List.not_mem_nil _)) hlc.2⟩)
      -- me_fun
      (fun (L : List String) _hdom _hbody ih_dom ih_body hwf hswf hlc => by
        rename_i Γ_i dom_i dom'_i body_i body'_i
        constructor
        · exact ih_dom hwf hswf hlc.1
        · obtain ⟨x, hx_fresh⟩ := exists_fresh_string (L ++ body'_i.fvs)
          have hx_L : x ∉ L := fun h => hx_fresh (List.mem_append_left _ h)
          have hx_body' : x ∉ body'_i.fvs := fun h => hx_fresh (List.mem_append_right _ h)
          have hwf_ext : LNCtx.wf ((x, .sub dom_i) :: Γ_i) :=
            fun p hp => by cases hp with
            | head => exact hlc.1
            | tail _ hmem => exact hwf p hmem
          have hbody'_x_lc := ih_body x hx_L hwf_ext hswf (LNExpr.lc_at_open_fvar hlc.2)
          exact LNExpr.lc_at_1_of_open_lc hbody'_x_lc hx_body')
      -- me_fop
      (fun (L : List String) _hdom _hbody ih_dom ih_body hwf hswf hlc => by
        rename_i Γ_i s_i α_i dom_i dom'_i body_i body'_i
        have hα_lc : α_i.lc := hswf _ (List.mem_cons_self _ _)
        have hs_wf : LNStack.wf s_i := fun e he => hswf e (List.mem_cons_of_mem _ he)
        constructor
        · exact ih_dom hwf (fun _ he => absurd he (List.not_mem_nil _)) hlc.1
        · obtain ⟨x, hx_fresh⟩ := exists_fresh_string (L ++ body'_i.fvs)
          have hx_L : x ∉ L := fun h => hx_fresh (List.mem_append_left _ h)
          have hx_body' : x ∉ body'_i.fvs := fun h => hx_fresh (List.mem_append_right _ h)
          have hwf_ext : LNCtx.wf ((x, .equiv α_i) :: Γ_i) :=
            fun p hp => by cases hp with
            | head => exact hα_lc
            | tail _ hmem => exact hwf p hmem
          have hbody'_x_lc := ih_body x hx_L hwf_ext hs_wf (LNExpr.lc_at_open_fvar hlc.2)
          exact LNExpr.lc_at_1_of_open_lc hbody'_x_lc hx_body')
      -- ms_pro
      (fun hmem hwf _hswf _hlc => mem_sub_lc hmem hwf)
      -- ms_top
      (fun _hwf _hswf _hlc => trivial)
      -- ms_equ
      (fun _hequ ih_equ hwf hswf hlc => ih_equ hwf hswf hlc)
      -- ms_app
      (fun _hsub ih_sub hwf hswf hlc =>
        ⟨ih_sub hwf (fun e he => by cases he with | head => exact hlc.2 | tail _ h => exact hswf e h) hlc.1, hlc.2⟩)
      -- ms_fun
      (fun (L : List String) _hbody ih_body hwf _hswf hlc => by
        rename_i Γ_i dom_i body_i body'_i
        constructor
        · exact hlc.1
        · obtain ⟨x, hx_fresh⟩ := exists_fresh_string (L ++ body'_i.fvs)
          have hx_L : x ∉ L := fun h => hx_fresh (List.mem_append_left _ h)
          have hx_body' : x ∉ body'_i.fvs := fun h => hx_fresh (List.mem_append_right _ h)
          have hwf_ext : LNCtx.wf ((x, .sub dom_i) :: Γ_i) :=
            fun p hp => by cases hp with
            | head => exact hlc.1
            | tail _ hmem => exact hwf p hmem
          have hbody'_x_lc := ih_body x hx_L hwf_ext (fun _ he => absurd he (List.not_mem_nil _)) (LNExpr.lc_at_open_fvar hlc.2)
          exact LNExpr.lc_at_1_of_open_lc hbody'_x_lc hx_body')
      -- ms_fop
      (fun (L : List String) _hbody ih_body hwf hswf hlc => by
        rename_i Γ_i s_i α_i dom_i body_i body'_i
        have hα_lc : α_i.lc := hswf _ (List.mem_cons_self _ _)
        have hs_wf : LNStack.wf s_i := fun e he => hswf e (List.mem_cons_of_mem _ he)
        constructor
        · exact hlc.1
        · obtain ⟨x, hx_fresh⟩ := exists_fresh_string (L ++ body'_i.fvs)
          have hx_L : x ∉ L := fun h => hx_fresh (List.mem_append_left _ h)
          have hx_body' : x ∉ body'_i.fvs := fun h => hx_fresh (List.mem_append_right _ h)
          have hwf_ext : LNCtx.wf ((x, .equiv α_i) :: Γ_i) :=
            fun p hp => by cases hp with
            | head => exact hα_lc
            | tail _ hmem => exact hwf p hmem
          have hbody'_x_lc := ih_body x hx_L hwf_ext hs_wf (LNExpr.lc_at_open_fvar hlc.2)
          exact LNExpr.lc_at_1_of_open_lc hbody'_x_lc hx_body')
  exact go h hwf hswf hlc

/-! ### Reduction preserves freshness -/

/-- Extract x ∉ α.fvs from mem_equiv and x ∉ all_fvs Γ. -/
private theorem not_mem_fvs_of_mem_equiv {Γ : LNCtx} {x z : String} {α : LNExpr}
    (hmem : LNCtx.mem_equiv Γ z α) (hfresh : x ∉ LNCtx.all_fvs Γ) : x ∉ α.fvs := by
  have := LNCtx.not_mem_ann_fvs_of_not_mem_all_fvs hfresh hmem
  simp only [LNAnn.fvs] at this; exact this

/-- Extract x ∉ t.fvs from mem_sub and x ∉ all_fvs Γ. -/
private theorem not_mem_fvs_of_mem_sub {Γ : LNCtx} {x z : String} {t : LNExpr}
    (hmem : LNCtx.mem_sub Γ z t) (hfresh : x ∉ LNCtx.all_fvs Γ) : x ∉ t.fvs := by
  have := LNCtx.not_mem_ann_fvs_of_not_mem_all_fvs hfresh hmem
  simp only [LNAnn.fvs] at this; exact this

/-- Helper: x ∉ all_fvs ((y, ann) :: Γ) when x ≠ y, x ∉ ann.fvs, x ∉ all_fvs Γ. -/
private theorem not_mem_all_fvs_cons {x y : String} {ann : LNAnn} {Γ : LNCtx}
    (hne : x ≠ y) (hann : x ∉ ann.fvs) (hΓ : x ∉ LNCtx.all_fvs Γ)
    : x ∉ LNCtx.all_fvs ((y, ann) :: Γ) := by
  simp only [LNCtx.all_fvs, List.flatMap_cons]
  intro hmem
  cases List.mem_append.mp hmem with
  | inl h =>
    cases List.mem_cons.mp h with
    | inl heq => exact hne heq
    | inr hfvs => exact hann hfvs
  | inr h => exact hΓ h

set_option maxHeartbeats 1600000 in
/-- Equivalence reduction preserves freshness of free variables.
    If Γ;s ⊢ u ≡→ v and x ∉ u.fvs and x ∉ all_fvs(Γ) and x ∉ stack fvs,
    then x ∉ v.fvs. Reduction can only introduce variables from the context
    (ME-PRO) or stack (ME-FOP), so if x is absent from both, it stays absent. -/
theorem equivRed_preserves_not_mem_fvs
    {Γ : LNCtx} {s : LNStack} {u v : LNExpr} {x : String}
    (h : LNEquivRed Γ s u v)
    (hfvs : x ∉ u.fvs)
    (hctx : x ∉ LNCtx.all_fvs Γ)
    (hstk : ∀ e ∈ s, x ∉ e.fvs)
    : x ∉ v.fvs := by
  have go :=
    @LNEquivRed.rec
      (motive_1 := fun Γ s u v _ =>
        x ∉ u.fvs → x ∉ LNCtx.all_fvs Γ → (∀ e ∈ s, x ∉ e.fvs) → x ∉ v.fvs)
      (motive_2 := fun Γ s u v _ =>
        x ∉ u.fvs → x ∉ LNCtx.all_fvs Γ → (∀ e ∈ s, x ∉ e.fvs) → x ∉ v.fvs)
      -- me_pro: output is α' from SubRed Γ s α α'; x ∉ α.fvs from context freshness
      (fun hmem _hsub ih_sub _hfvs hctx hstk =>
        ih_sub (not_mem_fvs_of_mem_equiv hmem hctx) hctx hstk)
      -- me_bet: output is t.open_at 0 v'
      (fun (L : List String) _hbody _hv ih_body ih_v hfvs hctx hstk => by
        rename_i Γ_i s_i dom_i body_i t_i v_i v'_i
        -- fvs(app (lam dom body) v) = (dom.fvs ++ body.fvs) ++ v.fvs
        have hlam_fvs : x ∉ (LNExpr.lam dom_i body_i).fvs := fun h => hfvs (List.mem_append_left _ h)
        have hv_fvs : x ∉ v_i.fvs := fun h => hfvs (List.mem_append_right _ h)
        have hdom_fvs : x ∉ dom_i.fvs := fun h => hlam_fvs (List.mem_append_left _ h)
        have hbody_fvs : x ∉ body_i.fvs := fun h => hlam_fvs (List.mem_append_right _ h)
        -- Get x ∉ v'.fvs from IH on v
        have hv'_fvs := ih_v hv_fvs hctx (fun _ he => absurd he (List.not_mem_nil _))
        -- Pick y fresh for L ++ [x]
        obtain ⟨y, hy_fresh⟩ := exists_fresh_string (L ++ [x])
        have hy_L : y ∉ L := fun h => hy_fresh (List.mem_append_left _ h)
        have hx_ne_y : x ≠ y := fun h => by subst h; exact hy_fresh (List.mem_append_right _ (List.mem_cons_self _ _))
        -- x ∉ (body^y).fvs
        have hbody_y_fvs : x ∉ (body_i.open_at 0 (.fvar y)).fvs :=
          LNExpr.not_mem_fvs_open_at body_i hbody_fvs hx_ne_y
        -- x ∉ all_fvs((y, .equiv v) :: Γ)
        have hctx_ext : x ∉ LNCtx.all_fvs ((y, .equiv v_i) :: Γ_i) :=
          not_mem_all_fvs_cons hx_ne_y (by simp [LNAnn.fvs]; exact hv_fvs) hctx
        -- IH on body gives x ∉ (t^y).fvs
        have ht_y_fvs := ih_body y hy_L hbody_y_fvs hctx_ext hstk
        -- From x ∉ (t^y).fvs, get x ∉ t.fvs
        have ht_fvs : x ∉ t_i.fvs := LNExpr.not_mem_fvs_of_not_mem_fvs_open t_i ht_y_fvs
        -- x ∉ (t.open_at 0 v').fvs
        exact LNExpr.not_mem_fvs_open_at_term t_i ht_fvs hv'_fvs)
      -- me_top
      (fun _hfvs _hctx _hstk => fun hmem => (List.not_mem_nil _) hmem)
      -- me_var
      (fun hfvs _hctx _hstk => hfvs)
      -- me_tap
      (fun _hfvs _hctx _hstk => fun hmem => (List.not_mem_nil _) hmem)
      -- me_app: output is app u' v'
      (fun _hu _hv ih_u ih_v hfvs hctx hstk => by
        rename_i Γ_i s_i u_i u'_i v_i v'_i
        have hu_fvs : x ∉ u_i.fvs := fun h => hfvs (List.mem_append_left _ h)
        have hv_fvs : x ∉ v_i.fvs := fun h => hfvs (List.mem_append_right _ h)
        have hu'_fvs := ih_u hu_fvs hctx
          (fun e he => by cases he with | head => exact hv_fvs | tail _ h => exact hstk e h)
        have hv'_fvs := ih_v hv_fvs hctx (fun _ he => absurd he (List.not_mem_nil _))
        exact fun hmem => by
          simp only [LNExpr.fvs] at hmem
          cases List.mem_append.mp hmem with
          | inl h => exact hu'_fvs h
          | inr h => exact hv'_fvs h)
      -- me_fun: output is lam dom' body', stack is []
      (fun (L : List String) _hdom _hbody ih_dom ih_body hfvs hctx _hstk => by
        rename_i Γ_i dom_i dom'_i body_i body'_i
        have hdom_fvs : x ∉ dom_i.fvs := fun h => hfvs (List.mem_append_left _ h)
        have hbody_fvs : x ∉ body_i.fvs := fun h => hfvs (List.mem_append_right _ h)
        have hdom'_fvs := ih_dom hdom_fvs hctx (fun _ he => absurd he (List.not_mem_nil _))
        -- Pick y fresh
        obtain ⟨y, hy_fresh⟩ := exists_fresh_string (L ++ [x])
        have hy_L : y ∉ L := fun h => hy_fresh (List.mem_append_left _ h)
        have hx_ne_y : x ≠ y := fun h => by subst h; exact hy_fresh (List.mem_append_right _ (List.mem_cons_self _ _))
        have hbody_y_fvs : x ∉ (body_i.open_at 0 (.fvar y)).fvs :=
          LNExpr.not_mem_fvs_open_at body_i hbody_fvs hx_ne_y
        have hctx_ext : x ∉ LNCtx.all_fvs ((y, .sub dom_i) :: Γ_i) :=
          not_mem_all_fvs_cons hx_ne_y (by simp [LNAnn.fvs]; exact hdom_fvs) hctx
        have hbody'_y_fvs := ih_body y hy_L hbody_y_fvs hctx_ext
          (fun _ he => absurd he (List.not_mem_nil _))
        have hbody'_fvs : x ∉ body'_i.fvs :=
          LNExpr.not_mem_fvs_of_not_mem_fvs_open body'_i hbody'_y_fvs
        exact fun hmem => by
          simp only [LNExpr.fvs] at hmem
          cases List.mem_append.mp hmem with
          | inl h => exact hdom'_fvs h
          | inr h => exact hbody'_fvs h)
      -- me_fop: output is lam dom' body', stack is α :: s_i
      (fun (L : List String) _hdom _hbody ih_dom ih_body hfvs hctx hstk => by
        rename_i Γ_i s_i α_i dom_i dom'_i body_i body'_i
        have hdom_fvs : x ∉ dom_i.fvs := fun h => hfvs (List.mem_append_left _ h)
        have hbody_fvs : x ∉ body_i.fvs := fun h => hfvs (List.mem_append_right _ h)
        have hα_fvs : x ∉ α_i.fvs := hstk _ (List.mem_cons_self _ _)
        have hs_fvs : ∀ e ∈ s_i, x ∉ e.fvs := fun e he => hstk e (List.mem_cons_of_mem _ he)
        have hdom'_fvs := ih_dom hdom_fvs hctx (fun _ he => absurd he (List.not_mem_nil _))
        -- Pick y fresh
        obtain ⟨y, hy_fresh⟩ := exists_fresh_string (L ++ [x])
        have hy_L : y ∉ L := fun h => hy_fresh (List.mem_append_left _ h)
        have hx_ne_y : x ≠ y := fun h => by subst h; exact hy_fresh (List.mem_append_right _ (List.mem_cons_self _ _))
        have hbody_y_fvs : x ∉ (body_i.open_at 0 (.fvar y)).fvs :=
          LNExpr.not_mem_fvs_open_at body_i hbody_fvs hx_ne_y
        have hctx_ext : x ∉ LNCtx.all_fvs ((y, .equiv α_i) :: Γ_i) :=
          not_mem_all_fvs_cons hx_ne_y (by simp [LNAnn.fvs]; exact hα_fvs) hctx
        have hbody'_y_fvs := ih_body y hy_L hbody_y_fvs hctx_ext hs_fvs
        have hbody'_fvs : x ∉ body'_i.fvs :=
          LNExpr.not_mem_fvs_of_not_mem_fvs_open body'_i hbody'_y_fvs
        exact fun hmem => by
          simp only [LNExpr.fvs] at hmem
          cases List.mem_append.mp hmem with
          | inl h => exact hdom'_fvs h
          | inr h => exact hbody'_fvs h)
      -- ms_pro: output is t from context
      (fun hmem _hfvs hctx _hstk => not_mem_fvs_of_mem_sub hmem hctx)
      -- ms_top
      (fun _hfvs _hctx _hstk => fun hmem => (List.not_mem_nil _) hmem)
      -- ms_equ
      (fun _hequ ih_equ hfvs hctx hstk => ih_equ hfvs hctx hstk)
      -- ms_app: output is app u' v (v unchanged)
      (fun _hsub ih_sub hfvs hctx hstk => by
        rename_i Γ_i s_i u_i u'_i v_i
        have hu_fvs : x ∉ u_i.fvs := fun h => hfvs (List.mem_append_left _ h)
        have hv_fvs : x ∉ v_i.fvs := fun h => hfvs (List.mem_append_right _ h)
        have hu'_fvs := ih_sub hu_fvs hctx
          (fun e he => by cases he with | head => exact hv_fvs | tail _ h => exact hstk e h)
        exact fun hmem => by
          simp only [LNExpr.fvs] at hmem
          cases List.mem_append.mp hmem with
          | inl h => exact hu'_fvs h
          | inr h => exact hv_fvs h)
      -- ms_fun: output is lam dom body', stack is []
      (fun (L : List String) _hbody ih_body hfvs hctx _hstk => by
        rename_i Γ_i dom_i body_i body'_i
        have hdom_fvs : x ∉ dom_i.fvs := fun h => hfvs (List.mem_append_left _ h)
        have hbody_fvs : x ∉ body_i.fvs := fun h => hfvs (List.mem_append_right _ h)
        -- Pick y fresh
        obtain ⟨y, hy_fresh⟩ := exists_fresh_string (L ++ [x])
        have hy_L : y ∉ L := fun h => hy_fresh (List.mem_append_left _ h)
        have hx_ne_y : x ≠ y := fun h => by subst h; exact hy_fresh (List.mem_append_right _ (List.mem_cons_self _ _))
        have hbody_y_fvs : x ∉ (body_i.open_at 0 (.fvar y)).fvs :=
          LNExpr.not_mem_fvs_open_at body_i hbody_fvs hx_ne_y
        have hctx_ext : x ∉ LNCtx.all_fvs ((y, .sub dom_i) :: Γ_i) :=
          not_mem_all_fvs_cons hx_ne_y (by simp [LNAnn.fvs]; exact hdom_fvs) hctx
        have hbody'_y_fvs := ih_body y hy_L hbody_y_fvs hctx_ext
          (fun _ he => absurd he (List.not_mem_nil _))
        have hbody'_fvs : x ∉ body'_i.fvs :=
          LNExpr.not_mem_fvs_of_not_mem_fvs_open body'_i hbody'_y_fvs
        exact fun hmem => by
          simp only [LNExpr.fvs] at hmem
          cases List.mem_append.mp hmem with
          | inl h => exact hdom_fvs h
          | inr h => exact hbody'_fvs h)
      -- ms_fop: output is lam dom body', stack is α :: s_i
      (fun (L : List String) _hbody ih_body hfvs hctx hstk => by
        rename_i Γ_i s_i α_i dom_i body_i body'_i
        have hdom_fvs : x ∉ dom_i.fvs := fun h => hfvs (List.mem_append_left _ h)
        have hbody_fvs : x ∉ body_i.fvs := fun h => hfvs (List.mem_append_right _ h)
        have hα_fvs : x ∉ α_i.fvs := hstk _ (List.mem_cons_self _ _)
        have hs_fvs : ∀ e ∈ s_i, x ∉ e.fvs := fun e he => hstk e (List.mem_cons_of_mem _ he)
        -- Pick y fresh
        obtain ⟨y, hy_fresh⟩ := exists_fresh_string (L ++ [x])
        have hy_L : y ∉ L := fun h => hy_fresh (List.mem_append_left _ h)
        have hx_ne_y : x ≠ y := fun h => by subst h; exact hy_fresh (List.mem_append_right _ (List.mem_cons_self _ _))
        have hbody_y_fvs : x ∉ (body_i.open_at 0 (.fvar y)).fvs :=
          LNExpr.not_mem_fvs_open_at body_i hbody_fvs hx_ne_y
        have hctx_ext : x ∉ LNCtx.all_fvs ((y, .equiv α_i) :: Γ_i) :=
          not_mem_all_fvs_cons hx_ne_y (by simp [LNAnn.fvs]; exact hα_fvs) hctx
        have hbody'_y_fvs := ih_body y hy_L hbody_y_fvs hctx_ext hs_fvs
        have hbody'_fvs : x ∉ body'_i.fvs :=
          LNExpr.not_mem_fvs_of_not_mem_fvs_open body'_i hbody'_y_fvs
        exact fun hmem => by
          simp only [LNExpr.fvs] at hmem
          cases List.mem_append.mp hmem with
          | inl h => exact hdom_fvs h
          | inr h => exact hbody'_fvs h)
  exact go h hfvs hctx hstk

set_option maxHeartbeats 1600000 in
/-- Subtyping reduction preserves freshness of free variables.
    Derived from the same mutual induction as equivRed_preserves_not_mem_fvs. -/
theorem subRed_preserves_not_mem_fvs
    {Γ : LNCtx} {s : LNStack} {u v : LNExpr} {x : String}
    (h : LNSubRed Γ s u v)
    (hfvs : x ∉ u.fvs)
    (hctx : x ∉ LNCtx.all_fvs Γ)
    (hstk : ∀ e ∈ s, x ∉ e.fvs)
    : x ∉ v.fvs := by
  have go :=
    @LNSubRed.rec
      (motive_1 := fun Γ s u v _ =>
        x ∉ u.fvs → x ∉ LNCtx.all_fvs Γ → (∀ e ∈ s, x ∉ e.fvs) → x ∉ v.fvs)
      (motive_2 := fun Γ s u v _ =>
        x ∉ u.fvs → x ∉ LNCtx.all_fvs Γ → (∀ e ∈ s, x ∉ e.fvs) → x ∉ v.fvs)
      -- me_pro
      (fun hmem _hsub ih_sub _hfvs hctx hstk =>
        ih_sub (not_mem_fvs_of_mem_equiv hmem hctx) hctx hstk)
      -- me_bet
      (fun (L : List String) _hbody _hv ih_body ih_v hfvs hctx hstk => by
        rename_i Γ_i s_i dom_i body_i t_i v_i v'_i
        -- fvs(app (lam dom body) v) = (dom.fvs ++ body.fvs) ++ v.fvs
        have hlam_fvs : x ∉ (LNExpr.lam dom_i body_i).fvs := fun h => hfvs (List.mem_append_left _ h)
        have hv_fvs : x ∉ v_i.fvs := fun h => hfvs (List.mem_append_right _ h)
        have hdom_fvs : x ∉ dom_i.fvs := fun h => hlam_fvs (List.mem_append_left _ h)
        have hbody_fvs : x ∉ body_i.fvs := fun h => hlam_fvs (List.mem_append_right _ h)
        have hv'_fvs := ih_v hv_fvs hctx (fun _ he => absurd he (List.not_mem_nil _))
        obtain ⟨y, hy_fresh⟩ := exists_fresh_string (L ++ [x])
        have hy_L : y ∉ L := fun h => hy_fresh (List.mem_append_left _ h)
        have hx_ne_y : x ≠ y := fun h => by subst h; exact hy_fresh (List.mem_append_right _ (List.mem_cons_self _ _))
        have hbody_y_fvs : x ∉ (body_i.open_at 0 (.fvar y)).fvs :=
          LNExpr.not_mem_fvs_open_at body_i hbody_fvs hx_ne_y
        have hctx_ext : x ∉ LNCtx.all_fvs ((y, .equiv v_i) :: Γ_i) :=
          not_mem_all_fvs_cons hx_ne_y (by simp [LNAnn.fvs]; exact hv_fvs) hctx
        have ht_y_fvs := ih_body y hy_L hbody_y_fvs hctx_ext hstk
        have ht_fvs : x ∉ t_i.fvs := LNExpr.not_mem_fvs_of_not_mem_fvs_open t_i ht_y_fvs
        exact LNExpr.not_mem_fvs_open_at_term t_i ht_fvs hv'_fvs)
      -- me_top
      (fun _hfvs _hctx _hstk => fun hmem => (List.not_mem_nil _) hmem)
      -- me_var
      (fun hfvs _hctx _hstk => hfvs)
      -- me_tap
      (fun _hfvs _hctx _hstk => fun hmem => (List.not_mem_nil _) hmem)
      -- me_app
      (fun _hu _hv ih_u ih_v hfvs hctx hstk => by
        rename_i Γ_i s_i u_i u'_i v_i v'_i
        have hu_fvs : x ∉ u_i.fvs := fun h => hfvs (List.mem_append_left _ h)
        have hv_fvs : x ∉ v_i.fvs := fun h => hfvs (List.mem_append_right _ h)
        have hu'_fvs := ih_u hu_fvs hctx
          (fun e he => by cases he with | head => exact hv_fvs | tail _ h => exact hstk e h)
        have hv'_fvs := ih_v hv_fvs hctx (fun _ he => absurd he (List.not_mem_nil _))
        exact fun hmem => by
          simp only [LNExpr.fvs] at hmem
          cases List.mem_append.mp hmem with
          | inl h => exact hu'_fvs h
          | inr h => exact hv'_fvs h)
      -- me_fun
      (fun (L : List String) _hdom _hbody ih_dom ih_body hfvs hctx _hstk => by
        rename_i Γ_i dom_i dom'_i body_i body'_i
        have hdom_fvs : x ∉ dom_i.fvs := fun h => hfvs (List.mem_append_left _ h)
        have hbody_fvs : x ∉ body_i.fvs := fun h => hfvs (List.mem_append_right _ h)
        have hdom'_fvs := ih_dom hdom_fvs hctx (fun _ he => absurd he (List.not_mem_nil _))
        obtain ⟨y, hy_fresh⟩ := exists_fresh_string (L ++ [x])
        have hy_L : y ∉ L := fun h => hy_fresh (List.mem_append_left _ h)
        have hx_ne_y : x ≠ y := fun h => by subst h; exact hy_fresh (List.mem_append_right _ (List.mem_cons_self _ _))
        have hbody_y_fvs : x ∉ (body_i.open_at 0 (.fvar y)).fvs :=
          LNExpr.not_mem_fvs_open_at body_i hbody_fvs hx_ne_y
        have hctx_ext : x ∉ LNCtx.all_fvs ((y, .sub dom_i) :: Γ_i) :=
          not_mem_all_fvs_cons hx_ne_y (by simp [LNAnn.fvs]; exact hdom_fvs) hctx
        have hbody'_y_fvs := ih_body y hy_L hbody_y_fvs hctx_ext
          (fun _ he => absurd he (List.not_mem_nil _))
        have hbody'_fvs : x ∉ body'_i.fvs :=
          LNExpr.not_mem_fvs_of_not_mem_fvs_open body'_i hbody'_y_fvs
        exact fun hmem => by
          simp only [LNExpr.fvs] at hmem
          cases List.mem_append.mp hmem with
          | inl h => exact hdom'_fvs h
          | inr h => exact hbody'_fvs h)
      -- me_fop
      (fun (L : List String) _hdom _hbody ih_dom ih_body hfvs hctx hstk => by
        rename_i Γ_i s_i α_i dom_i dom'_i body_i body'_i
        have hdom_fvs : x ∉ dom_i.fvs := fun h => hfvs (List.mem_append_left _ h)
        have hbody_fvs : x ∉ body_i.fvs := fun h => hfvs (List.mem_append_right _ h)
        have hα_fvs : x ∉ α_i.fvs := hstk _ (List.mem_cons_self _ _)
        have hs_fvs : ∀ e ∈ s_i, x ∉ e.fvs := fun e he => hstk e (List.mem_cons_of_mem _ he)
        have hdom'_fvs := ih_dom hdom_fvs hctx (fun _ he => absurd he (List.not_mem_nil _))
        obtain ⟨y, hy_fresh⟩ := exists_fresh_string (L ++ [x])
        have hy_L : y ∉ L := fun h => hy_fresh (List.mem_append_left _ h)
        have hx_ne_y : x ≠ y := fun h => by subst h; exact hy_fresh (List.mem_append_right _ (List.mem_cons_self _ _))
        have hbody_y_fvs : x ∉ (body_i.open_at 0 (.fvar y)).fvs :=
          LNExpr.not_mem_fvs_open_at body_i hbody_fvs hx_ne_y
        have hctx_ext : x ∉ LNCtx.all_fvs ((y, .equiv α_i) :: Γ_i) :=
          not_mem_all_fvs_cons hx_ne_y (by simp [LNAnn.fvs]; exact hα_fvs) hctx
        have hbody'_y_fvs := ih_body y hy_L hbody_y_fvs hctx_ext hs_fvs
        have hbody'_fvs : x ∉ body'_i.fvs :=
          LNExpr.not_mem_fvs_of_not_mem_fvs_open body'_i hbody'_y_fvs
        exact fun hmem => by
          simp only [LNExpr.fvs] at hmem
          cases List.mem_append.mp hmem with
          | inl h => exact hdom'_fvs h
          | inr h => exact hbody'_fvs h)
      -- ms_pro
      (fun hmem _hfvs hctx _hstk => not_mem_fvs_of_mem_sub hmem hctx)
      -- ms_top
      (fun _hfvs _hctx _hstk => fun hmem => (List.not_mem_nil _) hmem)
      -- ms_equ
      (fun _hequ ih_equ hfvs hctx hstk => ih_equ hfvs hctx hstk)
      -- ms_app
      (fun _hsub ih_sub hfvs hctx hstk => by
        rename_i Γ_i s_i u_i u'_i v_i
        have hu_fvs : x ∉ u_i.fvs := fun h => hfvs (List.mem_append_left _ h)
        have hv_fvs : x ∉ v_i.fvs := fun h => hfvs (List.mem_append_right _ h)
        have hu'_fvs := ih_sub hu_fvs hctx
          (fun e he => by cases he with | head => exact hv_fvs | tail _ h => exact hstk e h)
        exact fun hmem => by
          simp only [LNExpr.fvs] at hmem
          cases List.mem_append.mp hmem with
          | inl h => exact hu'_fvs h
          | inr h => exact hv_fvs h)
      -- ms_fun
      (fun (L : List String) _hbody ih_body hfvs hctx _hstk => by
        rename_i Γ_i dom_i body_i body'_i
        have hdom_fvs : x ∉ dom_i.fvs := fun h => hfvs (List.mem_append_left _ h)
        have hbody_fvs : x ∉ body_i.fvs := fun h => hfvs (List.mem_append_right _ h)
        obtain ⟨y, hy_fresh⟩ := exists_fresh_string (L ++ [x])
        have hy_L : y ∉ L := fun h => hy_fresh (List.mem_append_left _ h)
        have hx_ne_y : x ≠ y := fun h => by subst h; exact hy_fresh (List.mem_append_right _ (List.mem_cons_self _ _))
        have hbody_y_fvs : x ∉ (body_i.open_at 0 (.fvar y)).fvs :=
          LNExpr.not_mem_fvs_open_at body_i hbody_fvs hx_ne_y
        have hctx_ext : x ∉ LNCtx.all_fvs ((y, .sub dom_i) :: Γ_i) :=
          not_mem_all_fvs_cons hx_ne_y (by simp [LNAnn.fvs]; exact hdom_fvs) hctx
        have hbody'_y_fvs := ih_body y hy_L hbody_y_fvs hctx_ext
          (fun _ he => absurd he (List.not_mem_nil _))
        have hbody'_fvs : x ∉ body'_i.fvs :=
          LNExpr.not_mem_fvs_of_not_mem_fvs_open body'_i hbody'_y_fvs
        exact fun hmem => by
          simp only [LNExpr.fvs] at hmem
          cases List.mem_append.mp hmem with
          | inl h => exact hdom_fvs h
          | inr h => exact hbody'_fvs h)
      -- ms_fop
      (fun (L : List String) _hbody ih_body hfvs hctx hstk => by
        rename_i Γ_i s_i α_i dom_i body_i body'_i
        have hdom_fvs : x ∉ dom_i.fvs := fun h => hfvs (List.mem_append_left _ h)
        have hbody_fvs : x ∉ body_i.fvs := fun h => hfvs (List.mem_append_right _ h)
        have hα_fvs : x ∉ α_i.fvs := hstk _ (List.mem_cons_self _ _)
        have hs_fvs : ∀ e ∈ s_i, x ∉ e.fvs := fun e he => hstk e (List.mem_cons_of_mem _ he)
        obtain ⟨y, hy_fresh⟩ := exists_fresh_string (L ++ [x])
        have hy_L : y ∉ L := fun h => hy_fresh (List.mem_append_left _ h)
        have hx_ne_y : x ≠ y := fun h => by subst h; exact hy_fresh (List.mem_append_right _ (List.mem_cons_self _ _))
        have hbody_y_fvs : x ∉ (body_i.open_at 0 (.fvar y)).fvs :=
          LNExpr.not_mem_fvs_open_at body_i hbody_fvs hx_ne_y
        have hctx_ext : x ∉ LNCtx.all_fvs ((y, .equiv α_i) :: Γ_i) :=
          not_mem_all_fvs_cons hx_ne_y (by simp [LNAnn.fvs]; exact hα_fvs) hctx
        have hbody'_y_fvs := ih_body y hy_L hbody_y_fvs hctx_ext hs_fvs
        have hbody'_fvs : x ∉ body'_i.fvs :=
          LNExpr.not_mem_fvs_of_not_mem_fvs_open body'_i hbody'_y_fvs
        exact fun hmem => by
          simp only [LNExpr.fvs] at hmem
          cases List.mem_append.mp hmem with
          | inl h => exact hdom_fvs h
          | inr h => exact hbody'_fvs h)
  exact go h hfvs hctx hstk

/-- Context reduction preserves stack freshness.
    If Γ;s ↦ Γ';s' and x ∉ all_fvs Γ and ∀ e ∈ s, x ∉ e.fvs,
    then ∀ e ∈ s', x ∉ e.fvs. -/
theorem ctxRed_preserves_stack_freshness
    {Γ : LNCtx} {s : LNStack} {Γ' : LNCtx} {s' : LNStack} {x : String}
    (h : LNCtxRed Γ s Γ' s')
    (hctx : x ∉ LNCtx.all_fvs Γ)
    (hstk : ∀ e ∈ s, x ∉ e.fvs)
    : ∀ e ∈ s', x ∉ e.fvs := by
  induction h with
  | ct_ann_sub _ _ ih =>
    exact ih (fun hmem => hctx (List.mem_append_right _ hmem))
      hstk
  | ct_ann_equiv _ _ ih =>
    exact ih (fun hmem => hctx (List.mem_append_right _ hmem))
      hstk
  | ct_stk hctx_inner hred ih =>
    intro e he
    cases he with
    | head =>
      -- e = α', the reduced stack head
      exact equivRed_preserves_not_mem_fvs hred
        (hstk _ (List.mem_cons_self _ _))
        hctx
        (fun _ he => absurd he (List.not_mem_nil _))
    | tail _ hmem =>
      exact ih hctx (fun e' he' => hstk e' (List.mem_cons_of_mem _ he')) e hmem
  | ct_nil => intro _ he; exact absurd he (List.not_mem_nil _)

/-! ### Promotion Collapse Lemma

From the paper (p.9:20, ME-BET/MS-APP case):
"If the rule ME-PRO appears in the derivation tree of the SubRed, then we have
in fact an EquivRed, and the result follows from the diamond lemma."

Given a SubRed in a context where x has .equiv annotation, either:
(a) noPromoAt x holds (the derivation doesn't promote x), or
(b) the SubRed is actually an EquivRed (it collapses).

Key insight: MS-PRO on x requires mem_sub, which fails when x has .equiv.
So the only way x gets "promoted" is via ME-PRO inside an MS-EQU. When that
happens, the MS-EQU wrapper is redundant — the derivation was an EquivRed
all along.

Proved by mutual induction using @LNSubRed.rec with motives:
  motive_1 (EquivRed): noPromoAt x ∨ EquivRed  (`.inr` is always trivially h itself)
  motive_2 (SubRed):   noPromoAt x ∨ EquivRed  (`.inr` means SubRed collapses)

The lc / wf hypotheses are needed for the ms_app → ME-APP collapse (equivRed_refl
on the operand) and ms_fun/ms_fop → ME-FUN/ME-FOP collapse (equivRed_refl on domain).
-/

/-- Helper: if x has .equiv annotation in Γ, then ms_pro on x gives contradiction. -/
private theorem ms_pro_ne_of_equiv {Γ : LNCtx} {x z : String} {t : LNExpr} {α : LNExpr}
    (hlook : Γ.lookup' x = some (.equiv α))
    (hmem : LNCtx.mem_sub Γ z t)
    (hzx : z = x) : False := by
  subst hzx
  simp [LNCtx.mem_sub] at hmem
  rw [hlook] at hmem
  exact absurd hmem (by simp)

/-- Promotion collapse for ≡→: trivially `.inr h` since the hypothesis is
    already an EquivRed. Included for documentation — the mutual induction
    in `promotion_collapse` uses `.inr` as the fallback for all EquivRed cases. -/
theorem promotion_collapse_equiv
    {Γ : LNCtx} {s : LNStack} {u w : LNExpr}
    (h : LNEquivRed Γ s u w)
    {x : String} {α : LNExpr}
    (_hlook : Γ.lookup' x = some (.equiv α))
    (_hlc : u.lc) (_hwf : Γ.wf) (_hswf : s.wf)
    : (LNEquivRed.noPromoAt x Γ s u w) ∨ (LNEquivRed Γ s u w) :=
  .inr h

set_option maxHeartbeats 3200000 in
/-- Promotion collapse for ≤→: if x has .equiv annotation in Γ, then any
    sub-reduction either doesn't promote x (noPromoAt) or is actually an
    equiv-reduction.

    This is the key lemma for the ME-BET/MS-FOP case of commutativity.
    When noPromoAt holds, annotation swap lemmas apply directly.
    When the SubRed collapses to EquivRed, the diamond lemma applies. -/
theorem promotion_collapse
    {Γ : LNCtx} {s : LNStack} {u w : LNExpr}
    (h : LNSubRed Γ s u w)
    {x : String} {α : LNExpr}
    (hlook : Γ.lookup' x = some (.equiv α))
    (hlc : u.lc) (hwf : Γ.wf) (hswf : s.wf)
    : (LNSubRed.noPromoAt x Γ s u w) ∨ (LNEquivRed Γ s u w) := by
  have go :=
    @LNSubRed.rec
      -- motive_1 (EquivRed): noPromoAt x ∨ EquivRed (trivially .inr)
      (motive_1 := fun Γ s u w _ =>
        ∀ (x : String) (α : LNExpr),
        Γ.lookup' x = some (.equiv α) →
        u.lc → Γ.wf → s.wf →
        (LNEquivRed.noPromoAt x Γ s u w) ∨ (LNEquivRed Γ s u w))
      -- motive_2 (SubRed): noPromoAt x ∨ EquivRed (the real content)
      (motive_2 := fun Γ s u w _ =>
        ∀ (x : String) (α : LNExpr),
        Γ.lookup' x = some (.equiv α) →
        u.lc → Γ.wf → s.wf →
        (LNSubRed.noPromoAt x Γ s u w) ∨ (LNEquivRed Γ s u w))
      -- ===== EquivRed cases =====
      -- me_pro: z ≡ α_z ∈ Γ, SubRed Γ s α_z α'
      -- The `.inr` fallback is always available (just reconstruct the EquivRed)
      (fun hmem h_sub ih_sub x_var α_var hlk _hlc_e hwf_e hswf_e =>
        .inr (.me_pro hmem h_sub))
      -- me_bet: L, body, v → .inr fallback
      (fun L hbody hv _ih_body _ih_v _x_var _α_var _hlk _hlc_e _hwf_e _hswf_e =>
        .inr (.me_bet L hbody hv))
      -- me_top
      (fun _x_var _α_var _hlk _hlc_e _hwf_e _hswf_e => .inl .me_top)
      -- me_var
      (fun _x_var _α_var _hlk _hlc_e _hwf_e _hswf_e => .inl .me_var)
      -- me_tap
      (fun _x_var _α_var _hlk _hlc_e _hwf_e _hswf_e => .inl .me_tap)
      -- me_app: .inr fallback
      (fun h_u h_v _ih_u _ih_v _x_var _α_var _hlk _hlc_e _hwf_e _hswf_e =>
        .inr (.me_app h_u h_v))
      -- me_fun: .inr fallback
      (fun L h_dom h_body _ih_dom _ih_body _x_var _α_var _hlk _hlc_e _hwf_e _hswf_e =>
        .inr (.me_fun L h_dom h_body))
      -- me_fop: .inr fallback
      (fun L h_dom h_body _ih_dom _ih_body _x_var _α_var _hlk _hlc_e _hwf_e _hswf_e =>
        .inr (.me_fop L h_dom h_body))
      -- ===== SubRed cases =====
      -- ms_pro: z ≤ t ∈ Γ
      -- z cannot be x because x has .equiv, not .sub
      (fun (hmem : LNCtx.mem_sub _ _ _) x_var α_var hlk _hlc_e _hwf_e _hswf_e =>
        .inl (.ms_pro (fun heq => by subst heq; simp [LNCtx.mem_sub] at hmem; rw [hlk] at hmem; exact absurd hmem (by simp)) hmem))
      -- ms_top
      (fun _x_var _α_var _hlk _hlc_e _hwf_e _hswf_e => .inl .ms_top)
      -- ms_equ: EquivRed Γ s u w — delegate to EquivRed IH
      (fun _h_eq ih_eq x_var α_var hlk hlc_e hwf_e hswf_e => by
        cases ih_eq x_var α_var hlk hlc_e hwf_e hswf_e with
        | inl np_eq => exact .inl (.ms_equ np_eq)
        | inr eq => exact .inr eq)
      -- ms_app: SubRed Γ (v::s) u u' ⟹ SubRed Γ s (app u v) (app u' v)
      (fun (h_inner : LNSubRed _ (_ :: _) _ _) ih_inner x_var α_var hlk hlc_e hwf_e hswf_e => by
        have hu_lc := hlc_e.1
        have hv_lc := hlc_e.2
        have hswf_ext : LNStack.wf (_ :: _) :=
          fun e he => by
            rcases List.mem_cons.mp he with heq | h
            · exact heq ▸ hv_lc
            · exact hswf_e e h
        cases ih_inner x_var α_var hlk hu_lc hwf_e hswf_ext with
        | inl np => exact .inl (.ms_app np)
        | inr eq_inner =>
          exact .inr (.me_app eq_inner (equivRed_refl _ [] _ hv_lc)))
      -- ms_fun: L, ∀ y ∉ L, SubRed ((y,.sub dom)::Γ) [] (body^y) (body'^y)
      -- Classical dichotomy: either noPromoAt for all y, or EquivRed via ME-FUN.
      (fun L h_body ih_body x_var α_var hlk hlc_e hwf_e _hswf_e => by
        -- Name the implicit recursor variables
        rename_i Γ_fun dom_fun body_fun body'_fun
        -- L' avoids L, all_fvs(Γ), body.fvs, body'.fvs, dom.fvs, x_var
        let L' := L ++ LNCtx.all_fvs Γ_fun ++ body_fun.fvs ++ body'_fun.fvs ++ dom_fun.fvs ++ [x_var]
        -- Classical: either some y₀ ∉ L' gives EquivRed, or all give noPromoAt
        by_cases hex : ∃ y₀, y₀ ∉ L' ∧ LNEquivRed ((y₀, .sub dom_fun) :: Γ_fun) [] (body_fun.open_at 0 (.fvar y₀)) (body'_fun.open_at 0 (.fvar y₀))
        · -- Case: ∃ y₀ giving EquivRed → build ME-FUN via equivRed_rename
          obtain ⟨y₀, hy₀L', heq_y₀⟩ := hex
          have hy₀Γ : y₀ ∉ LNCtx.all_fvs Γ_fun := fun h => hy₀L' (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
          have hy₀body : y₀ ∉ body_fun.fvs := fun h => hy₀L' (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
          have hy₀body' : y₀ ∉ body'_fun.fvs := fun h => hy₀L' (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
          have hy₀dom : y₀ ∉ dom_fun.fvs := fun h => hy₀L' (List.mem_append_left _ (List.mem_append_right _ h))
          exact .inr (.me_fun L' (equivRed_refl Γ_fun [] dom_fun hlc_e.1) (fun y hyL' => by
            have hyΓ : y ∉ LNCtx.all_fvs Γ_fun := fun h => hyL' (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
            have h_renamed := equivRed_rename heq_y₀ hy₀Γ hyΓ hy₀body hy₀dom (fun _ he => absurd he (List.not_mem_nil _))
            have hrhs : (body'_fun.open_at 0 (.fvar y₀)).subst_fvar y₀ (.fvar y) = body'_fun.open_at 0 (.fvar y) := by
              rw [subst_fvar_fvar_open_at]
              simp only [LNExpr.subst_fvar, beq_self_eq_true, ite_true]
              rw [subst_fvar_notin hy₀body']
            rw [hrhs] at h_renamed
            exact h_renamed))
        · -- Case: ¬∃ y₀ ∉ L' with EquivRed → all y ∉ L' give noPromoAt
          have hall : ∀ y₀, y₀ ∉ L' → ¬ LNEquivRed ((y₀, .sub dom_fun) :: Γ_fun) [] (body_fun.open_at 0 (.fvar y₀)) (body'_fun.open_at 0 (.fvar y₀)) := by
            intro y₀ hy₀ heq; exact hex ⟨y₀, hy₀, heq⟩
          exact .inl (.ms_fun L' (fun y hyL' => by
            have hyL : y ∉ L := fun h => hyL' (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))))
            have hyx' : y ≠ x_var := by
              intro heq; subst heq; exact hyL' (List.mem_append_right _ (List.mem_cons_self _ _))
            have hlk_ext : LNCtx.lookup' ((y, LNAnn.sub dom_fun) :: Γ_fun) x_var = some (.equiv α_var) := by
              simp only [LNCtx.lookup']
              have : ¬(y == x_var) = true := by simp [beq_iff_eq]; exact hyx'
              simp [this, hlk]
            have hlc_body : (body_fun.open_at 0 (.fvar y)).lc := LNExpr.lc_at_open_fvar hlc_e.2
            have hwf_ext : LNCtx.wf ((y, LNAnn.sub dom_fun) :: Γ_fun) :=
              fun p hp => by cases hp with | head => exact hlc_e.1 | tail _ h => exact hwf_e p h
            have hswf_nil : LNStack.wf ([] : LNStack) := fun _ he => absurd he (List.not_mem_nil _)
            have h_ih := ih_body y hyL x_var α_var hlk_ext hlc_body hwf_ext hswf_nil
            cases h_ih with
            | inl np => exact np
            | inr heq => exact absurd heq (hall y hyL'))))
      -- ms_fop: L, ∀ y ∉ L, SubRed ((y,.equiv α_fop)::Γ) s (body^y) (body'^y)
      -- Same classical argument as ms_fun, but with .equiv annotation and stack s.
      (fun L h_body ih_body x_var α_var hlk hlc_e hwf_e hswf_e => by
        -- Name the implicit recursor variables
        rename_i Γ_fop s_fop α_fop dom_fop body_fop body'_fop
        -- L' avoids L, all_fvs(Γ), body.fvs, body'.fvs, α_fop.fvs, x_var, s_fop.fvs
        let L' := L ++ LNCtx.all_fvs Γ_fop ++ body_fop.fvs ++ body'_fop.fvs ++ α_fop.fvs ++ [x_var] ++ s_fop.flatMap LNExpr.fvs
        -- α_fop is lc from the stack wf hypothesis
        have hα_lc : α_fop.lc := hswf_e α_fop (List.mem_cons_self _ _)
        have hs_wf : LNStack.wf s_fop := fun e he => hswf_e e (List.mem_cons_of_mem α_fop he)
        -- Classical: either some y₀ ∉ L' gives EquivRed, or all give noPromoAt
        by_cases hex : ∃ y₀, y₀ ∉ L' ∧ LNEquivRed ((y₀, .equiv α_fop) :: Γ_fop) s_fop (body_fop.open_at 0 (.fvar y₀)) (body'_fop.open_at 0 (.fvar y₀))
        · -- Case: ∃ y₀ giving EquivRed → build ME-FOP via equivRed_rename
          obtain ⟨y₀, hy₀L', heq_y₀⟩ := hex
          have hy₀Γ : y₀ ∉ LNCtx.all_fvs Γ_fop := fun h => hy₀L' (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))
          have hy₀body : y₀ ∉ body_fop.fvs := fun h => hy₀L' (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
          have hy₀body' : y₀ ∉ body'_fop.fvs := fun h => hy₀L' (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
          have hy₀α : y₀ ∉ α_fop.fvs := fun h => hy₀L' (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
          have hy₀s : ∀ e ∈ s_fop, y₀ ∉ e.fvs := fun e he hfv =>
            hy₀L' (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hfv⟩))
          exact .inr (.me_fop L' (equivRed_refl Γ_fop [] dom_fop hlc_e.1) (fun y hyL' => by
            have hyΓ : y ∉ LNCtx.all_fvs Γ_fop := fun h => hyL' (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))
            have h_renamed := equivRed_rename heq_y₀ hy₀Γ hyΓ hy₀body hy₀α hy₀s
            have hrhs : (body'_fop.open_at 0 (.fvar y₀)).subst_fvar y₀ (.fvar y) = body'_fop.open_at 0 (.fvar y) := by
              rw [subst_fvar_fvar_open_at]
              simp only [LNExpr.subst_fvar, beq_self_eq_true, ite_true]
              rw [subst_fvar_notin hy₀body']
            rw [hrhs] at h_renamed
            exact h_renamed))
        · -- Case: ¬∃ y₀ ∉ L' with EquivRed → all y ∉ L' give noPromoAt
          have hall : ∀ y₀, y₀ ∉ L' → ¬ LNEquivRed ((y₀, .equiv α_fop) :: Γ_fop) s_fop (body_fop.open_at 0 (.fvar y₀)) (body'_fop.open_at 0 (.fvar y₀)) := by
            intro y₀ hy₀ heq; exact hex ⟨y₀, hy₀, heq⟩
          exact .inl (.ms_fop L' (fun y hyL' => by
            have hyL : y ∉ L := fun h => hyL' (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))))
            have hyx' : y ≠ x_var := by
              intro heq; subst heq; exact hyL' (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self _ _)))
            have hlk_ext : LNCtx.lookup' ((y, LNAnn.equiv α_fop) :: Γ_fop) x_var = some (.equiv α_var) := by
              simp only [LNCtx.lookup']
              have : ¬(y == x_var) = true := by simp [beq_iff_eq]; exact hyx'
              simp [this, hlk]
            have hlc_body : (body_fop.open_at 0 (.fvar y)).lc := LNExpr.lc_at_open_fvar hlc_e.2
            have hwf_ext : LNCtx.wf ((y, LNAnn.equiv α_fop) :: Γ_fop) :=
              fun p hp => by cases hp with | head => exact hα_lc | tail _ h => exact hwf_e p h
            have h_ih := ih_body y hyL x_var α_var hlk_ext hlc_body hwf_ext hs_wf
            cases h_ih with
            | inl np => exact np
            | inr heq => exact absurd heq (hall y hyL'))))
  exact go h x α hlook hlc hwf hswf

/-- Context reduction preserves context well-formedness:
    if `Γ` is wf and `Γ; s ↦ Γ'; s'`, then `Γ'` is wf. -/
theorem ctxRed_preserves_ctx_wf
    {Γ Γ' : LNCtx} {s s' : LNStack}
    (h : LNCtxRed Γ s Γ' s') (hwf : Γ.wf) (hswf : s.wf) : Γ'.wf := by
  induction h with
  | @ct_ann_sub _ _ _ _ x t t' _ hred ih =>
    intro p hp
    cases hp with
    | head =>
      show t'.lc
      have ht_lc : t.lc := hwf (x, .sub t) (List.mem_cons_self _ _)
      exact equivRed_preserves_lc hred ht_lc
        (fun q hq => hwf q (List.mem_cons_of_mem _ hq))
        (fun _ he => absurd he (List.not_mem_nil _))
    | tail _ hmem =>
      exact ih (fun q hq => hwf q (List.mem_cons_of_mem _ hq)) hswf p hmem
  | @ct_ann_equiv _ _ _ _ x α α' _ hred ih =>
    intro p hp
    cases hp with
    | head =>
      show α'.lc
      have hα_lc : α.lc := hwf (x, .equiv α) (List.mem_cons_self _ _)
      exact equivRed_preserves_lc hred hα_lc
        (fun q hq => hwf q (List.mem_cons_of_mem _ hq))
        (fun _ he => absurd he (List.not_mem_nil _))
    | tail _ hmem =>
      exact ih (fun q hq => hwf q (List.mem_cons_of_mem _ hq)) hswf p hmem
  | ct_stk _ _ ih =>
    exact ih hwf (fun e he => hswf e (List.mem_cons_of_mem _ he))
  | ct_nil => intro _ hp; exact absurd hp (List.not_mem_nil _)

/-- Context reduction preserves stack well-formedness:
    if `s` is wf and `Γ; s ↦ Γ'; s'`, then `s'` is wf. -/
theorem ctxRed_preserves_stk_wf
    {Γ Γ' : LNCtx} {s s' : LNStack}
    (h : LNCtxRed Γ s Γ' s') (hwf : Γ.wf) (hswf : s.wf) : s'.wf := by
  induction h with
  | ct_ann_sub _ _ ih => exact ih (fun q hq => hwf q (List.mem_cons_of_mem _ hq)) hswf
  | ct_ann_equiv _ _ ih => exact ih (fun q hq => hwf q (List.mem_cons_of_mem _ hq)) hswf
  | @ct_stk _ s_inner _ s'_inner α α' _ hred ih =>
    -- Goal: (α' :: s'_inner).wf
    -- hswf : (α :: s_inner).wf
    intro e he
    cases he with
    | head =>
      -- e = α', need α'.lc
      exact equivRed_preserves_lc hred (hswf α (List.mem_cons_self _ _)) hwf
        (fun _ he => absurd he (List.not_mem_nil _))
    | tail _ hmem =>
      -- e ∈ s'_inner
      exact ih hwf (fun e' he' => hswf e' (List.mem_cons_of_mem _ he')) e hmem
  | ct_nil => intro _ he; exact absurd he (List.not_mem_nil _)

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

set_option maxHeartbeats 3200000 in
theorem diamond_full
    (t₀ : LNExpr)
    {Γ Γ₁ Γ₂ : LNCtx} {s s₁ s₂ : LNStack} {t₁ t₂ : LNExpr}
    (h1 : LNEquivRed Γ s t₀ t₁) (h2 : LNEquivRed Γ s t₀ t₂)
    (hctx1 : LNCtxRed Γ s Γ₁ s₁) (hctx2 : LNCtxRed Γ s Γ₂ s₂)
    (hlc : t₀.lc) (hwf : Γ.wf) (hswf : s.wf) (hnd : (LNCtx.dom Γ).Nodup)
    : ∃ t₃, LNEquivRed Γ₁ s₁ t₁ t₃ ∧ LNEquivRed Γ₂ s₂ t₂ t₃ := by
  cases h1 with
  | me_pro _ _ => sorry
  | me_top => cases h2 with | me_top => exact ⟨.top, .me_top, .me_top⟩
  | me_var =>
    cases h2 with
    | me_var => exact ⟨.fvar _, .me_var, .me_var⟩
    | me_pro _ _ => sorry
  | me_tap =>
    cases h2 with
    | me_tap => exact ⟨.top, .me_top, .me_top⟩
    | @me_app _ _ _ u₂' _ v₂' h2_u h2_v =>
      cases h2_u with | me_top => exact ⟨.top, .me_top, .me_tap⟩
  | @me_app _ _ u_head u₁' v_head v₁' h1_u h1_v =>
    cases h2 with
    | @me_app _ _ _ u₂' _ v₂' h2_u h2_v =>
      obtain ⟨v₃, hv₃l, hv₃r⟩ := diamond_full v_head h1_v h2_v
        (ctxRed_nil_of_ctxRed hctx1) (ctxRed_nil_of_ctxRed hctx2)
        hlc.2 hwf (fun _ he => absurd he (List.not_mem_nil _)) hnd
      obtain ⟨u₃, hu₃l, hu₃r⟩ := diamond_full u_head h1_u h2_u
        (.ct_stk hctx1 h1_v) (.ct_stk hctx2 h2_v) hlc.1 hwf
        (fun e he => by cases he with | head => exact hlc.2 | tail _ h => exact hswf e h) hnd
      exact ⟨.app u₃ v₃, .me_app hu₃l hv₃l, .me_app hu₃r hv₃r⟩
    | me_tap => cases h1_u with | me_top => exact ⟨.top, .me_tap, .me_top⟩
    | me_bet _ _ => sorry
  | me_bet _ _ =>
    cases h2 with
    | me_bet _ _ => sorry
    | me_app _ _ => sorry
  | @me_fun _ dom₁ dom₁' body₁ body₁' L₁ h1_dom h1_body =>
    cases h2 with
    | @me_fun _ _ dom₂' _ body₂' L₂ h2_dom h2_body =>
      have hdom_lc := hlc.1
      obtain ⟨dom₃, hd₃l, hd₃r⟩ := diamond_full dom₁ h1_dom h2_dom
        (ctxRed_nil_of_ctxRed hctx1) (ctxRed_nil_of_ctxRed hctx2)
        hdom_lc hwf (fun _ he => absurd he (List.not_mem_nil _)) hnd
      obtain ⟨x, hx⟩ := exists_fresh_string
        (L₁ ++ L₂ ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ₁ ++ LNCtx.all_fvs Γ₂ ++ body₁'.fvs ++ body₂'.fvs ++ dom₁.fvs)
      have hxL₁ : x ∉ L₁ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))))))
      have hxL₂ : x ∉ L₂ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))))
      have hxΓ_all : x ∉ LNCtx.all_fvs Γ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))
      have hxΓ : x ∉ LNCtx.dom Γ := LNCtx.not_mem_dom_of_not_mem_all_fvs hxΓ_all
      have hxΓ₁_all : x ∉ LNCtx.all_fvs Γ₁ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
      have hxΓ₂_all : x ∉ LNCtx.all_fvs Γ₂ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
      have hxb₁ : x ∉ body₁'.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
      have hxb₂ : x ∉ body₂'.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_right _ h))
      have hxdom₁ : x ∉ dom₁.fvs := fun h => hx (List.mem_append_right _ h)
      have hs₁ := ctxRed_nil_stack hctx1; subst hs₁
      have hs₂ := ctxRed_nil_stack hctx2; subst hs₂
      have hwf_body : LNCtx.wf ((x, .sub dom₁) :: Γ) :=
        fun p hp => by cases hp with | head => exact hdom_lc | tail _ h => exact hwf p h
      obtain ⟨u₃, hu₃l, hu₃r⟩ := diamond_full (body₁.open_at 0 (.fvar x))
        (h1_body x hxL₁) (h2_body x hxL₂)
        (.ct_ann_sub (ctxRed_nil_of_ctxRed hctx1) h1_dom)
        (.ct_ann_sub (ctxRed_nil_of_ctxRed hctx2) h2_dom)
        (LNExpr.lc_at_open_fvar hlc.2) hwf_body
        (fun _ he => absurd he (List.not_mem_nil _))
        (List.nodup_cons.mpr ⟨hxΓ, hnd⟩)
      have hb₁lc := equivRed_preserves_lc (h1_body x hxL₁) (LNExpr.lc_at_open_fvar hlc.2)
        hwf_body (fun _ he => absurd he (List.not_mem_nil _))
      have hd₁lc := equivRed_preserves_lc h1_dom hdom_lc hwf
        (fun _ he => absurd he (List.not_mem_nil _))
      have hwf_Γ₁ : LNCtx.wf Γ₁ := ctxRed_preserves_ctx_wf (ctxRed_nil_of_ctxRed hctx1) hwf (fun _ he => absurd he (List.not_mem_nil _))
      have u₃lc : u₃.lc := equivRed_preserves_lc hu₃l hb₁lc
        (fun p hp => by cases hp with | head => exact hd₁lc | tail _ h => exact hwf_Γ₁ p h)
        (fun _ he => absurd he (List.not_mem_nil _))
      exact ⟨.lam dom₃ (u₃.close_at 0 x),
        .me_fun (L₁ ++ L₂ ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ₁ ++ LNCtx.all_fvs Γ₂ ++ body₁'.fvs ++ body₂'.fvs ++ dom₁.fvs)
          hd₃l (fun y hy => by
            have hyΓ₁ : y ∉ LNCtx.all_fvs Γ₁ := fun h => hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
            have hxdom₁' : x ∉ (LNAnn.sub dom₁').fvs := by
              simp [LNAnn.fvs]; exact equivRed_preserves_not_mem_fvs h1_dom hxdom₁ hxΓ_all
                (fun _ he => absurd he (List.not_mem_nil _))
            have := equivRed_rename hu₃l hxΓ₁_all hyΓ₁ hxb₁ hxdom₁' (fun _ he => absurd he (List.not_mem_nil _))
            rw [open_close_subst u₃lc]; exact this),
        .me_fun (L₁ ++ L₂ ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ₁ ++ LNCtx.all_fvs Γ₂ ++ body₁'.fvs ++ body₂'.fvs ++ dom₁.fvs)
          hd₃r (fun y hy => by
            have hyΓ₂ : y ∉ LNCtx.all_fvs Γ₂ := fun h => hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
            have hxdom₂' : x ∉ (LNAnn.sub dom₂').fvs := by
              simp [LNAnn.fvs]; exact equivRed_preserves_not_mem_fvs h2_dom hxdom₁ hxΓ_all
                (fun _ he => absurd he (List.not_mem_nil _))
            have := equivRed_rename hu₃r hxΓ₂_all hyΓ₂ hxb₂ hxdom₂' (fun _ he => absurd he (List.not_mem_nil _))
            rw [open_close_subst u₃lc]; exact this)⟩
  | @me_fop _ s' α₁ dom₁ dom₁' body₁ body₁' L₁ h1_dom h1_body =>
    cases h2 with
    | @me_fop _ _ _ _ dom₂' _ body₂' L₂ h2_dom h2_body =>
      have hα_lc := hswf α₁ (List.mem_cons_self _ _)
      have hs'_wf : LNStack.wf s' := fun e he => hswf e (List.mem_cons_of_mem _ he)
      obtain ⟨α', s₁', hs₁eq, hctx1_inner, hα₁_red⟩ := ctxRed_stack_inv hctx1 hnd; subst hs₁eq
      obtain ⟨α'', s₂', hs₂eq, hctx2_inner, hα₂_red⟩ := ctxRed_stack_inv hctx2 hnd; subst hs₂eq
      obtain ⟨dom₃, hd₃l, hd₃r⟩ := diamond_full dom₁ h1_dom h2_dom
        (ctxRed_nil_of_ctxRed hctx1_inner) (ctxRed_nil_of_ctxRed hctx2_inner)
        hlc.1 hwf (fun _ he => absurd he (List.not_mem_nil _)) hnd
      -- Include s' fvs in avoidance set so x is fresh for the entire inner stack
      obtain ⟨x, hx⟩ := exists_fresh_string
        (L₁ ++ L₂ ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ₁ ++ LNCtx.all_fvs Γ₂ ++ body₁'.fvs ++ body₂'.fvs ++ α₁.fvs ++ s'.flatMap LNExpr.fvs)
      have hxL₁ : x ∉ L₁ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))))))
      have hxL₂ : x ∉ L₂ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))))
      have hxΓ_all : x ∉ LNCtx.all_fvs Γ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))))
      have hxΓ : x ∉ LNCtx.dom Γ := LNCtx.not_mem_dom_of_not_mem_all_fvs hxΓ_all
      have hxΓ₁_all : x ∉ LNCtx.all_fvs Γ₁ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))
      have hxΓ₂_all : x ∉ LNCtx.all_fvs Γ₂ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
      have hxb₁ : x ∉ body₁'.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
      have hxb₂ : x ∉ body₂'.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
      have hxα₁ : x ∉ α₁.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_right _ h))
      have hx_s'_fvs : ∀ e ∈ s', x ∉ e.fvs := fun e he hm =>
        hx (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hm⟩))
      have hwf_body : LNCtx.wf ((x, .equiv α₁) :: Γ) :=
        fun p hp => by cases hp with | head => exact hα_lc | tail _ h => exact hwf p h
      obtain ⟨u₃, hu₃l, hu₃r⟩ := diamond_full (body₁.open_at 0 (.fvar x))
        (h1_body x hxL₁) (h2_body x hxL₂)
        (.ct_ann_equiv hctx1_inner hα₁_red) (.ct_ann_equiv hctx2_inner hα₂_red)
        (LNExpr.lc_at_open_fvar hlc.2) hwf_body hs'_wf
        (List.nodup_cons.mpr ⟨hxΓ, hnd⟩)
      have hb₁lc := equivRed_preserves_lc (h1_body x hxL₁)
        (LNExpr.lc_at_open_fvar hlc.2) hwf_body hs'_wf
      have hα'lc := equivRed_preserves_lc hα₁_red hα_lc hwf
        (fun _ he => absurd he (List.not_mem_nil _))
      have hwf_Γ₁_fop : LNCtx.wf Γ₁ := ctxRed_preserves_ctx_wf hctx1_inner hwf hs'_wf
      have hwf_s₁' : LNStack.wf s₁' := ctxRed_preserves_stk_wf hctx1_inner hwf hs'_wf
      have u₃lc : u₃.lc := equivRed_preserves_lc hu₃l hb₁lc
        (fun p hp => by cases hp with | head => exact hα'lc | tail _ h => exact hwf_Γ₁_fop p h)
        hwf_s₁'
      have hxα' : x ∉ α'.fvs := equivRed_preserves_not_mem_fvs hα₁_red hxα₁ hxΓ_all
        (fun _ he => absurd he (List.not_mem_nil _))
      have hxα'' : x ∉ α''.fvs := equivRed_preserves_not_mem_fvs hα₂_red hxα₁ hxΓ_all
        (fun _ he => absurd he (List.not_mem_nil _))
      have hx_s₁'_fvs : ∀ e ∈ s₁', x ∉ e.fvs :=
        ctxRed_preserves_stack_freshness hctx1_inner hxΓ_all hx_s'_fvs
      have hx_s₂'_fvs : ∀ e ∈ s₂', x ∉ e.fvs :=
        ctxRed_preserves_stack_freshness hctx2_inner hxΓ_all hx_s'_fvs
      exact ⟨.lam dom₃ (u₃.close_at 0 x),
        .me_fop (L₁ ++ L₂ ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ₁ ++ LNCtx.all_fvs Γ₂ ++ body₁'.fvs ++ body₂'.fvs ++ α₁.fvs ++ s'.flatMap LNExpr.fvs)
          hd₃l (fun y hy => by
            have hyΓ₁ : y ∉ LNCtx.all_fvs Γ₁ := fun h => hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))
            have := equivRed_rename hu₃l hxΓ₁_all hyΓ₁ hxb₁
              (by simp [LNAnn.fvs]; exact hxα') hx_s₁'_fvs
            rw [open_close_subst u₃lc]; exact this),
        .me_fop (L₁ ++ L₂ ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ₁ ++ LNCtx.all_fvs Γ₂ ++ body₁'.fvs ++ body₂'.fvs ++ α₁.fvs ++ s'.flatMap LNExpr.fvs)
          hd₃r (fun y hy => by
            have hyΓ₂ : y ∉ LNCtx.all_fvs Γ₂ := fun h => hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
            have := equivRed_rename hu₃r hxΓ₂_all hyΓ₂ hxb₂
              (by simp [LNAnn.fvs]; exact hxα'') hx_s₂'_fvs
            rw [open_close_subst u₃lc]; exact this)⟩
termination_by t₀.sz
decreasing_by all_goals simp_all [LNExpr.sz, sz_open_at_fvar]; omega

/-- Diamond (one-context version used by commutativity).
    Derived from `diamond_full` by using `ctxRed_refl` for one context. -/
theorem diamond
    {Γ Γ' : LNCtx} {s s' : LNStack} {t₀ t₁ t₂ : LNExpr}
    (h1 : LNEquivRed Γ s t₀ t₁) (h2 : LNEquivRed Γ s t₀ t₂)
    (hctx : LNCtxRed Γ s Γ' s')
    (hwf_ctx : Γ.wf) (hwf_stk : s.wf)
    (hlc : t₀.lc) (hnd : (LNCtx.dom Γ).Nodup)
    : ∃ t₃, LNEquivRed Γ s t₂ t₃ ∧ LNEquivRed Γ' s' t₁ t₃ := by
  have hid : LNCtxRed Γ s Γ s := ctxRed_refl Γ s hwf_ctx hwf_stk
  obtain ⟨t₃, h_left, h_right⟩ := diamond_full t₀ h2 h1 hid hctx hlc hwf_ctx hwf_stk hnd
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
    (hwf_ctx : Γ.wf)
    (hwf_stk : s.wf)
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
    obtain ⟨t₃, htop, hright⟩ := diamond h_equiv h_eq2 h_ctx hwf_ctx hwf_stk h_lc h_nd
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
        commutativity u₀ h_equiv_u h_sub_u h_ctx_ext hu₀_lc h_nd hwf_ctx
          (fun e he => by cases he with | head => exact h_lc.2 | tail _ hmem => exact hwf_stk e hmem)
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
        obtain ⟨t₃, htop, hright⟩ := diamond h_equiv_orig h_equiv2 h_ctx hwf_ctx hwf_stk h_lc h_nd
        exact ⟨t₃, htop, .ms_equ hright, sorry⟩  -- sorry: noPromoAt preservation for ME-BET/MS-EQU
      | @ms_fop _ _ _ _ _ body₂ L_s h_sub_body_s =>
        -- h_sub_body_s : ∀ y, y ∉ L_s → LNSubRed ((y, .equiv v) :: Γ) s (body^y) (body₂^y)
        -- h_body_e : ∀ x, x ∉ L_e → LNEquivRed ((x, .equiv v) :: Γ) s (body^x) (t_e^x)
        -- BOTH are in the SAME context (x, .equiv v) :: Γ — no annotation mismatch!
        -- Pick x fresh for L_e, L_s, all_fvs(Γ), dom(Γ'), v.fvs, body₂.fvs, t_e.fvs, s fvs, s' fvs, all_fvs(Γ')
        obtain ⟨x, hx⟩ := exists_fresh_string (L_e ++ L_s ++ LNCtx.all_fvs Γ ++ LNCtx.dom Γ' ++ v.fvs ++ body₂.fvs ++ t_e.fvs ++ s.flatMap LNExpr.fvs ++ s'.flatMap LNExpr.fvs ++ LNCtx.all_fvs Γ')
        have hx_Le : x ∉ L_e := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))))))))
        have hx_Ls : x ∉ L_s := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))))))
        have hx_all_fvs : x ∉ LNCtx.all_fvs Γ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))))
        have hx_dom' : x ∉ LNCtx.dom Γ' := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))))
        have hx_dom : x ∉ LNCtx.dom Γ := LNCtx.not_mem_dom_of_not_mem_all_fvs hx_all_fvs
        have hx_v_fvs : x ∉ v.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))
        have hx_body₂_fvs : x ∉ body₂.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
        have hx_t_e_fvs : x ∉ t_e.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
        have hx_s_fvs : ∀ e ∈ s, x ∉ e.fvs := fun e he hfv => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hfv⟩))))
        have hx_s'_fvs : ∀ e ∈ s', x ∉ e.fvs := fun e he hfv => hx (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hfv⟩)))
        have hx_all_fvs' : x ∉ LNCtx.all_fvs Γ' := fun h => hx (List.mem_append_right _ h)
        -- Instantiate the cofinite premises at x
        have h_body_e_x := h_body_e x hx_Le
        -- h_body_e_x : LNEquivRed ((x, .equiv v) :: Γ) s (body^x) (t_e^x)
        have h_sub_body_s_x := h_sub_body_s x hx_Ls
        -- h_sub_body_s_x : LNSubRed ((x, .equiv v) :: Γ) s (body^x) (body₂^x)
        have hbody_lc : (body.open_at 0 (.fvar x)).lc :=
          LNExpr.lc_at_open_fvar h_lc.1.2
        -- ═══════════════════════════════════════════════════════════════
        -- Both EquivRed and SubRed are in the SAME context (x,.equiv v)::Γ
        -- Use promotion_collapse, then handle both branches.
        -- ═══════════════════════════════════════════════════════════════
        have hwf_ctx_ext_equiv : LNCtx.wf ((x, .equiv v) :: Γ) :=
          fun p hp => by cases hp with
          | head => exact h_lc.2
          | tail _ hmem => exact hwf_ctx p hmem
        have hlook_x : LNCtx.lookup' ((x, .equiv v) :: Γ) x = some (.equiv v) := by
          simp [LNCtx.lookup']
        have h_collapse := promotion_collapse h_sub_body_s_x hlook_x hbody_lc hwf_ctx_ext_equiv hwf_stk
        -- Context reduction for the extended context
        have h_ctx_body : LNCtxRed ((x, .equiv v) :: Γ) s ((x, .equiv v') :: Γ') s' :=
          LNCtxRed.ct_ann_equiv h_ctx h_v_e
        -- Helper: derive v'.lc
        have hv'_lc : v'.lc := equivRed_preserves_lc h_v_e h_lc.2 hwf_ctx
          (fun _ he => absurd he (List.not_mem_nil _))
        -- ═══════════════════════════════════════════════════════════════
        -- Unified approach: always use h_sub_body_s_x for the IH.
        -- promotion_collapse on h_sub_body_s_x tells us noPromoAt x holds
        -- or the SubRed is an EquivRed. In both cases, we apply the IH
        -- with h_sub_body_s_x, then use noPromoAt x from the IH to substitute.
        -- ═══════════════════════════════════════════════════════════════
        obtain ⟨u₃, htop_body, hright_body, hnp_ih⟩ :=
          commutativity (body.open_at 0 (.fvar x)) h_body_e_x h_sub_body_s_x h_ctx_body hbody_lc
            (List.nodup_cons.mpr ⟨hx_dom, h_nd⟩)
            hwf_ctx_ext_equiv
            hwf_stk
        -- htop_body : EquivRed ((x,.equiv v)::Γ) s (body₂^x) u₃
        -- hright_body : SubRed ((x,.equiv v')::Γ') s' (t_e^x) u₃
        have hbody₂_x_lc : (body₂.open_at 0 (.fvar x)).lc :=
          subRed_preserves_lc h_sub_body_s_x hbody_lc hwf_ctx_ext_equiv hwf_stk
        have u₃_lc : u₃.lc :=
          equivRed_preserves_lc htop_body hbody₂_x_lc hwf_ctx_ext_equiv hwf_stk
        -- Get noPromoAt x on hright_body from IH + promotion_collapse on INPUT
        -- promotion_collapse on h_sub_body_s_x gives .inl (noPromoAt x) or .inr (EquivRed)
        -- In .inl case: hnp_ih x h_np gives noPromoAt x on hright_body
        -- In .inr case: the input SubRed is also an EquivRed. We wrap it in ms_equ.
        --   noPromoAt x on ms_equ needs EquivRed.noPromoAt x on the EquivRed.
        --   The EquivRed h_eq_body was CONSTRUCTED by promotion_collapse.
        --   TODO: prove noPromoAt x on the constructed EquivRed.
        -- For now, use promotion_collapse on the OUTPUT to get noPromoAt x directly.
        have hlook_x' : LNCtx.lookup' ((x, .equiv v') :: Γ') x = some (.equiv v') := by
          simp [LNCtx.lookup']
        have hte_x_lc : (t_e.open_at 0 (.fvar x)).lc :=
          equivRed_preserves_lc h_body_e_x hbody_lc hwf_ctx_ext_equiv hwf_stk
        have hwf_ctx' : Γ'.wf := ctxRed_preserves_ctx_wf h_ctx hwf_ctx hwf_stk
        have hwf_ctx_ext_equiv' : LNCtx.wf ((x, .equiv v') :: Γ') :=
          fun p hp => by cases hp with
          | head => exact hv'_lc
          | tail _ hmem => exact hwf_ctx' p hmem
        have hwf_stk' : s'.wf := ctxRed_preserves_stk_wf h_ctx hwf_ctx hwf_stk
        -- Get noPromoAt x on hright_body
        have h_np_right : LNSubRed.noPromoAt x ((x, .equiv v') :: Γ') s' (t_e.open_at 0 (.fvar x)) u₃ := by
          cases h_collapse with
          | inl h_np => exact hnp_ih x h_np
          | inr h_eq_body =>
            -- h_eq_body : EquivRed ((x,.equiv v)::Γ) s (body^x) (body₂^x)
            -- The SubRed h_sub_body_s_x is also an EquivRed. But noPromoAt x on
            -- h_sub_body_s_x might hold or not.
            -- Use promotion_collapse on the OUTPUT instead.
            exact (promotion_collapse hright_body hlook_x' hte_x_lc hwf_ctx_ext_equiv' hwf_stk').elim
              (fun h => h)
              (fun h_eq_right => by
                -- h_eq_right : EquivRed ((x,.equiv v')::Γ') s' (t_e^x) u₃
                -- The output SubRed is also an EquivRed. Use noPromoAt_fresh_sub?
                -- No, x IS in dom. But this EquivRed was produced by diamond/commutativity
                -- and x was chosen fresh. Use promotion_collapse recursively... still same issue.
                -- For now, extract from the EquivRed structure.
                exact .ms_equ (sorry))
        -- Apply subRed_subst_noPromo to hright_body
        have h_subst := subRed_subst_noPromo h_np_right (v := v') hv'_lc
        -- Rewrite: ctx_subst_drop ((x,.equiv v')::Γ') x v' = Γ'
        rw [ctx_subst_drop_cons_eq, ctx_subst_drop_id hx_all_fvs',
            stack_map_subst_gen_id hx_s'_fvs] at h_subst
        rw [← open_close_subst_expr (y := x) (u := v') u₃_lc] at h_subst
        have h_te_subst : (t_e.open_at 0 (.fvar x)).subst_fvar x v' = t_e.open_at 0 v' := by
          rw [subst_fvar_gen_open_at t_e x v' (.fvar x) 0 hv'_lc]
          simp only [LNExpr.subst_fvar, beq_self_eq_true, ite_true]
          rw [subst_fvar_notin hx_t_e_fvs]
        rw [h_te_subst] at h_subst
        -- Build the witness t₃ = (u₃.close_at 0 x).open_at 0 v'
        refine ⟨(u₃.close_at 0 x).open_at 0 v', ?_, ?_, ?_⟩
        · -- Top edge: Γ;s ⊢ app (lam dom body₂) v ≡→ (close x u₃)^v'
          exact .me_bet (L_e ++ L_s ++ LNCtx.all_fvs Γ ++ LNCtx.dom Γ' ++ v.fvs)
            (fun y hy => by
              have hy_all_fvs : y ∉ LNCtx.all_fvs Γ := fun h =>
                hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
              have hy_v_fvs : y ∉ v.fvs := fun h =>
                hy (List.mem_append_right _ h)
              have h := equivRed_rename htop_body hx_all_fvs hy_all_fvs hx_body₂_fvs hx_v_fvs hx_s_fvs
              rw [open_close_subst u₃_lc]
              exact h)
            h_v_e
        · -- Right edge: Γ';s' ⊢ t_e^v' ≤→ (close x u₃)^v'
          exact h_subst
        · -- noPromoAt preservation
          intro z hnp_z
          by_cases hzx : z = x
          · -- z = x: x ∉ dom Γ', so noPromoAt x trivially holds
            subst hzx; exact noPromoAt_fresh_sub h_subst hx_dom'
          · -- z ≠ x: invert input noPromoAt, apply IH, then subst preservation
            -- Step 1: invert hnp_z to get body-level noPromoAt z
            obtain ⟨L_np_z, h_body_np_z⟩ : ∃ L_np_z, ∀ w, w ∉ L_np_z →
                LNSubRed.noPromoAt z ((w, .equiv v) :: Γ) s (body.open_at 0 (.fvar w)) (body₂.open_at 0 (.fvar w)) := by
              -- hnp_z : noPromoAt z on (.app (.lam dom body) v, .app (.lam dom body₂) v)
              -- Invert through ms_app then ms_fop/ms_equ(me_fop)
              cases hnp_z with
              | ms_app hnp_inner =>
                cases hnp_inner with
                | ms_fop L_np h_body_np => exact ⟨L_np, h_body_np⟩
                | ms_equ h_equiv_np =>
                  cases h_equiv_np with
                  | me_fop L_np _h_dom_np h_body_np =>
                    exact ⟨L_np, fun w hw => .ms_equ (h_body_np w hw)⟩
              | ms_equ h_equiv_np =>
                -- me_app gives (.app u v, .app u' v') where inner could be me_fop
                -- Generalize the RHS to avoid dependent elimination issues with me_bet
                generalize he : LNExpr.app (.lam dom body₂) v = out at h_equiv_np
                cases h_equiv_np with
                | me_app h_op_np h_arg_np =>
                  -- h_op_np : EquivRed.noPromoAt z Γ (v::s) (lam dom body) u'
                  -- h_arg_np : EquivRed.noPromoAt z Γ [] v v'
                  -- he : app (lam dom body₂) v = app u' v'
                  cases he
                  -- Now u' = lam dom body₂, v' = v
                  -- Stack is non-empty (v::s), term is lambda → must be me_fop
                  cases h_op_np with
                  | me_fop L_np h_dom_np h_body_np =>
                    exact ⟨L_np, fun w hw => .ms_equ (h_body_np w hw)⟩
                | me_bet L_bet h_body_bet h_v_bet =>
                  -- me_bet: body-level noPromoAt has target t^w (not body₂^w).
                  -- Inverting me_bet to extract body₂-targeted noPromoAt requires
                  -- the noPromoAt_app_app_inv lemma (see line ~3457).
                  exact ⟨L_bet, fun w hw => sorry⟩
            -- Step 2: rename to x and apply IH
            -- Pick a fresh w from L_np_z and the avoidance sets
            obtain ⟨w, hw⟩ := exists_fresh_string (L_np_z ++ LNCtx.all_fvs Γ ++ body.fvs ++ body₂.fvs ++ v.fvs ++ s.flatMap LNExpr.fvs ++ [x, z])
            have hw_Lnpz : w ∉ L_np_z := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))))
            have hw_all_fvs : w ∉ LNCtx.all_fvs Γ := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))
            have hw_body_fvs : w ∉ body.fvs := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
            have hw_body₂_fvs : w ∉ body₂.fvs := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
            have hw_v_fvs : w ∉ v.fvs := fun h => hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
            have hw_s_fvs : ∀ e ∈ s, w ∉ e.fvs := fun e he hm => hw (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hm⟩)))
            have hw_ne_x : w ≠ x := fun h => hw (List.mem_append_right _ (h ▸ List.mem_cons_self _ _))
            have hw_ne_z : w ≠ z := fun h => hw (List.mem_append_right _ (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self _ _)))
            have hnp_z_w := h_body_np_z w hw_Lnpz
            -- Rename w → x
            have hnp_z_x := noPromoAt_sub_rename hnp_z_w hw_all_fvs hx_all_fvs hw_body_fvs
              (by simp [LNAnn.fvs]; exact hw_v_fvs) hw_s_fvs
              (fun _ => Ne.symm (fun h => hzx h.symm))
            have hrhs_z : (body₂.open_at 0 (.fvar w)).subst_fvar w (.fvar x) = body₂.open_at 0 (.fvar x) := by
              rw [subst_fvar_fvar_open_at]; simp only [LNExpr.subst_fvar, beq_self_eq_true, ite_true]
              rw [subst_fvar_notin hw_body₂_fvs]
            rw [hrhs_z] at hnp_z_x
            -- Step 3: apply IH
            have hnp_z_output := hnp_ih z hnp_z_x
            -- Step 4: apply subRed_subst_noPromo_noPromoAt
            have h_np_z_subst := subRed_subst_noPromo_noPromoAt h_np_right hzx hnp_z_output hv'_lc
            rw [ctx_subst_drop_cons_eq, ctx_subst_drop_id hx_all_fvs',
                stack_map_subst_gen_id hx_s'_fvs] at h_np_z_subst
            rw [← open_close_subst_expr (y := x) (u := v') u₃_lc] at h_np_z_subst
            have h_te_subst_z : (t_e.open_at 0 (.fvar x)).subst_fvar x v' = t_e.open_at 0 v' := by
              rw [subst_fvar_gen_open_at t_e x v' (.fvar x) 0 hv'_lc]
              simp only [LNExpr.subst_fvar, beq_self_eq_true, ite_true]
              rw [subst_fvar_notin hx_t_e_fvs]
            rw [h_te_subst_z] at h_np_z_subst
            exact h_np_z_subst
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
      -- Pick x fresh for both avoidance sets, contexts, and body fvs
      obtain ⟨x, hx⟩ := exists_fresh_string (L_e ++ L_s ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ' ++ body₂.fvs ++ body₁.fvs ++ dom.fvs)
      have hx_Le : x ∉ L_e := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))))
      have hx_Ls : x ∉ L_s := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))
      have hx_all_fvs : x ∉ LNCtx.all_fvs Γ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
      have hx_dom : x ∉ LNCtx.dom Γ := LNCtx.not_mem_dom_of_not_mem_all_fvs hx_all_fvs
      have hx_all_fvs' : x ∉ LNCtx.all_fvs Γ' := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
      have hx_dom' : x ∉ LNCtx.dom Γ' := LNCtx.not_mem_dom_of_not_mem_all_fvs hx_all_fvs'
      have hx_body₂_fvs : x ∉ body₂.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
      have hx_body₁_fvs : x ∉ body₁.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_right _ h))
      have hx_dom_fvs : x ∉ dom.fvs := fun h => hx (List.mem_append_right _ h)
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
          (fun p hp => by cases hp with | head => exact h_lc.1 | tail _ hmem => exact hwf_ctx p hmem)
          (fun _ he => absurd he (List.not_mem_nil _))
      have hs' := ctxRed_nil_stack h_ctx; subst hs'
      -- Derive u₃.lc
      have hwf_ctx_ext_sub : LNCtx.wf ((x, .sub dom) :: Γ) :=
        fun p hp => by cases hp with
        | head => exact h_lc.1
        | tail _ hmem => exact hwf_ctx p hmem
      have hbody₂_x_lc : (body₂.open_at 0 (.fvar x)).lc :=
        subRed_preserves_lc h_sub_body_x hbody_lc hwf_ctx_ext_sub
          (fun _ he => absurd he (List.not_mem_nil _))
      have u₃_lc : u₃.lc :=
        equivRed_preserves_lc htop_body hbody₂_x_lc hwf_ctx_ext_sub
          (fun _ he => absurd he (List.not_mem_nil _))
      have hx_dom'_fvs : x ∉ dom'.fvs :=
        equivRed_preserves_not_mem_fvs h_equiv_dom hx_dom_fvs hx_all_fvs
          (fun _ he => absurd he (List.not_mem_nil _))
      -- Name the right-edge derivation for reuse in noPromoAt preservation
      have hright_lam : LNSubRed Γ' [] (.lam dom' body₁) (.lam dom' (u₃.close_at 0 x)) :=
        .ms_fun (L_e ++ L_s ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ' ++ body₂.fvs ++ body₁.fvs ++ dom.fvs)
          (fun y hy => by
            have hy_all_fvs' : y ∉ LNCtx.all_fvs Γ' := fun h =>
              hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
            have h := subRed_rename hright_body hx_all_fvs' hy_all_fvs' hx_body₁_fvs
              (by simp [LNAnn.fvs]; exact hx_dom'_fvs)
              (fun _ he => absurd he (List.not_mem_nil _))
            rw [open_close_subst u₃_lc]
            exact h)
      refine ⟨.lam dom' (u₃.close_at 0 x), ?_, hright_lam, ?_⟩
      · -- Top edge
        exact .me_fun (L_e ++ L_s ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ' ++ body₂.fvs ++ body₁.fvs ++ dom.fvs)
          h_equiv_dom
          (fun y hy => by
            have hy_all_fvs : y ∉ LNCtx.all_fvs Γ := fun h =>
              hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
            have hy_dom_fvs : y ∉ dom.fvs := fun h =>
              hy (List.mem_append_right _ h)
            have h := equivRed_rename htop_body hx_all_fvs hy_all_fvs hx_body₂_fvs hx_dom_fvs (fun _ he => absurd he (List.not_mem_nil _))
            rw [open_close_subst u₃_lc]
            exact h)
      · -- noPromoAt preservation for ME-FUN/MS-FUN
        intro z hnp
        by_cases hzx : z = x
        · -- z = x: x ∉ dom Γ', so noPromoAt x trivially holds
          subst hzx; exact noPromoAt_fresh_sub hright_lam hx_dom'
        · -- z ≠ x: invert input noPromoAt to get body-level with avoidance set,
          -- then construct output using rename + IH
          -- Unify ms_fun and ms_equ(me_fun) cases: extract avoidance set and body proof
          obtain ⟨L_np, h_body_np⟩ : ∃ L_np, ∀ w, w ∉ L_np →
              LNSubRed.noPromoAt z ((w, .sub dom) :: Γ) [] (body.open_at 0 (.fvar w)) (body₂.open_at 0 (.fvar w)) := by
            cases hnp with
            | ms_fun L_np h_body_np => exact ⟨L_np, h_body_np⟩
            | ms_equ h_equiv_np =>
              cases h_equiv_np with
              | me_fun L_np _h_dom_np h_body_np =>
                exact ⟨L_np, fun w hw => .ms_equ (h_body_np w hw)⟩
          exact .ms_fun (L_np ++ L_e ++ L_s ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ' ++ body₂.fvs ++ body₁.fvs ++ body.fvs ++ dom.fvs ++ [x, z])
            (fun y hy => by
              have hy_Lnp : y ∉ L_np := fun h =>
                hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))))))))
              have hy_all_fvs : y ∉ LNCtx.all_fvs Γ := fun h =>
                hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))))
              have hy_all_fvs' : y ∉ LNCtx.all_fvs Γ' := fun h =>
                hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))
              have hy_body₂_fvs : y ∉ body₂.fvs := fun h =>
                hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
              have hy_body_fvs : y ∉ body.fvs := fun h =>
                hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
              have hy_dom_fvs : y ∉ dom.fvs := fun h =>
                hy (List.mem_append_left _ (List.mem_append_right _ h))
              have hy_ne_x : y ≠ x := fun h =>
                hy (List.mem_append_right _ (h ▸ List.mem_cons_self _ _))
              have hy_ne_z : y ≠ z := fun h =>
                hy (List.mem_append_right _ (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self _ _)))
              -- Step 1: get noPromoAt at y from input
              have hnp_y := h_body_np y hy_Lnp
              -- Step 2: rename y → x in noPromoAt for IH
              have hnp_x := noPromoAt_sub_rename hnp_y hy_all_fvs hx_all_fvs hy_body_fvs
                (by simp [LNAnn.fvs]; exact hy_dom_fvs)
                (fun _ he => absurd he (List.not_mem_nil _))
                (fun _ => Ne.symm (fun h => hzx h.symm))
              -- Rewrite RHS: (body₂^y)[y↦x] = body₂^x
              have hrhs : (body₂.open_at 0 (.fvar y)).subst_fvar y (.fvar x) = body₂.open_at 0 (.fvar x) := by
                rw [subst_fvar_fvar_open_at]
                simp only [LNExpr.subst_fvar, beq_self_eq_true, ite_true]
                rw [subst_fvar_notin hy_body₂_fvs]
              rw [hrhs] at hnp_x
              -- Step 3: apply IH
              have hnp_out := _hnp_ih z hnp_x
              -- Step 4: rename x → y in output
              have hnp_y_out := noPromoAt_sub_rename hnp_out hx_all_fvs' hy_all_fvs' hx_body₁_fvs
                (by simp [LNAnn.fvs]; exact hx_dom'_fvs)
                (fun _ he => absurd he (List.not_mem_nil _))
                (fun _ => Ne.symm hy_ne_z)
              rw [open_close_subst u₃_lc]
              exact hnp_y_out)

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
      -- Include s_inner fvs in avoidance set so x is fresh for the entire stack
      obtain ⟨x, hx⟩ := exists_fresh_string (L_e ++ L_s ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ' ++ body₂.fvs ++ body₁.fvs ++ α.fvs ++ s_inner.flatMap LNExpr.fvs)
      have hx_Le : x ∉ L_e := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))))))
      have hx_Ls : x ∉ L_s := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))))
      have hx_all_fvs : x ∉ LNCtx.all_fvs Γ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))
      have hx_dom : x ∉ LNCtx.dom Γ := LNCtx.not_mem_dom_of_not_mem_all_fvs hx_all_fvs
      have hx_all_fvs' : x ∉ LNCtx.all_fvs Γ' := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
      have hx_body₂_fvs : x ∉ body₂.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
      have hx_body₁_fvs : x ∉ body₁.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
      have hx_α_fvs : x ∉ α.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_right _ h))
      have hx_s_inner_fvs : ∀ e ∈ s_inner, x ∉ e.fvs := fun e he hm =>
        hx (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hm⟩))
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
          (fun p hp => by cases hp with
            | head => exact hwf_stk α (List.mem_cons_self _ _)
            | tail _ hmem => exact hwf_ctx p hmem)
          (fun e he => hwf_stk e (List.mem_cons_of_mem _ he))
      -- Derive u₃.lc
      have hwf_ctx_ext_equiv : LNCtx.wf ((x, .equiv α) :: Γ) :=
        fun p hp => by cases hp with
        | head => exact hwf_stk α (List.mem_cons_self _ _)
        | tail _ hmem => exact hwf_ctx p hmem
      have hs_inner_wf : LNStack.wf s_inner := fun e he => hwf_stk e (List.mem_cons_of_mem _ he)
      have hbody₂_x_lc : (body₂.open_at 0 (.fvar x)).lc :=
        subRed_preserves_lc h_sub_body_x hbody_lc hwf_ctx_ext_equiv hs_inner_wf
      have u₃_lc : u₃.lc :=
        equivRed_preserves_lc htop_body hbody₂_x_lc hwf_ctx_ext_equiv hs_inner_wf
      have hx_α'_fvs : x ∉ α'.fvs :=
        equivRed_preserves_not_mem_fvs hα_red hx_α_fvs hx_all_fvs
          (fun _ he => absurd he (List.not_mem_nil _))
      have hx_s₁_fvs : ∀ e ∈ s₁, x ∉ e.fvs :=
        ctxRed_preserves_stack_freshness h_ctx_inner hx_all_fvs hx_s_inner_fvs
      refine ⟨.lam dom' (u₃.close_at 0 x), ?_, ?_, ?_⟩
      · -- Top edge: use equivRed_rename on htop_body
        exact .me_fop (L_e ++ L_s ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ' ++ body₂.fvs ++ body₁.fvs ++ α.fvs)
          h_equiv_dom
          (fun y hy => by
            have hy_all_fvs : y ∉ LNCtx.all_fvs Γ := fun h =>
              hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
            have hy_α_fvs : y ∉ α.fvs := fun h =>
              hy (List.mem_append_right _ h)
            have h := equivRed_rename htop_body hx_all_fvs hy_all_fvs hx_body₂_fvs hx_α_fvs hx_s_inner_fvs
            rw [open_close_subst u₃_lc]
            exact h)
      · -- Right edge: use subRed_rename on hright_body
        exact .ms_fop (L_e ++ L_s ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ' ++ body₂.fvs ++ body₁.fvs ++ α.fvs)
          (fun y hy => by
            have hy_all_fvs' : y ∉ LNCtx.all_fvs Γ' := fun h =>
              hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
            have h := subRed_rename hright_body hx_all_fvs' hy_all_fvs' hx_body₁_fvs
              (by simp [LNAnn.fvs]; exact hx_α'_fvs)
              hx_s₁_fvs
            rw [open_close_subst u₃_lc]
            exact h)
      · -- noPromoAt preservation for ME-FOP/MS-FOP
        have hx_dom' : x ∉ LNCtx.dom Γ' := LNCtx.not_mem_dom_of_not_mem_all_fvs hx_all_fvs'
        intro z hnp
        by_cases hzx : z = x
        · -- z = x: x ∉ dom Γ', so noPromoAt x trivially holds
          rw [hzx]
          have hright_lam : LNSubRed Γ' (α' :: s₁) (.lam dom' body₁) (.lam dom' (u₃.close_at 0 x)) :=
            .ms_fop (L_e ++ L_s ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ' ++ body₂.fvs ++ body₁.fvs ++ α.fvs)
              (fun y hy => by
                have hy_all_fvs' : y ∉ LNCtx.all_fvs Γ' := fun h =>
                  hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
                have h := subRed_rename hright_body hx_all_fvs' hy_all_fvs' hx_body₁_fvs
                  (by simp [LNAnn.fvs]; exact hx_α'_fvs)
                  hx_s₁_fvs
                rw [open_close_subst u₃_lc]
                exact h)
          exact noPromoAt_fresh_sub hright_lam hx_dom'
        · -- z ≠ x: invert input, apply IH, rename output
          obtain ⟨L_np, h_body_np⟩ : ∃ L_np, ∀ w, w ∉ L_np →
              LNSubRed.noPromoAt z ((w, .equiv α) :: Γ) s_inner (body.open_at 0 (.fvar w)) (body₂.open_at 0 (.fvar w)) := by
            cases hnp with
            | ms_fop L_np h_body_np => exact ⟨L_np, h_body_np⟩
            | ms_equ h_equiv_np =>
              cases h_equiv_np with
              | me_fop L_np _h_dom_np h_body_np =>
                exact ⟨L_np, fun w hw => .ms_equ (h_body_np w hw)⟩
          exact .ms_fop (L_np ++ L_e ++ L_s ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ' ++ body₂.fvs ++ body₁.fvs ++ body.fvs ++ α.fvs ++ α'.fvs ++ s_inner.flatMap LNExpr.fvs ++ s₁.flatMap LNExpr.fvs ++ [x, z])
            (fun y hy => by
              have hy_Lnp : y ∉ L_np := fun h =>
                hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))))))))))
              have hy_all_fvs : y ∉ LNCtx.all_fvs Γ := fun h =>
                hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))))))
              have hy_all_fvs' : y ∉ LNCtx.all_fvs Γ' := fun h =>
                hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))))))
              have hy_body₂_fvs : y ∉ body₂.fvs := fun h =>
                hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))))
              have hy_body_fvs : y ∉ body.fvs := fun h =>
                hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))
              have hy_α_fvs : y ∉ α.fvs := fun h =>
                hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
              have hy_α'_fvs : y ∉ α'.fvs := fun h =>
                hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
              have hy_s_inner_fvs : ∀ e ∈ s_inner, y ∉ e.fvs := fun e he hm =>
                hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hm⟩))))
              have hy_s₁_fvs : ∀ e ∈ s₁, y ∉ e.fvs := fun e he hm =>
                hy (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hm⟩)))
              have hy_ne_x : y ≠ x := fun h =>
                hy (List.mem_append_right _ (h ▸ List.mem_cons_self _ _))
              have hy_ne_z : y ≠ z := fun h =>
                hy (List.mem_append_right _ (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self _ _)))
              -- Step 1: get noPromoAt at y
              have hnp_y := h_body_np y hy_Lnp
              -- Step 2: rename y → x
              have hnp_x := noPromoAt_sub_rename hnp_y hy_all_fvs hx_all_fvs hy_body_fvs
                (by simp [LNAnn.fvs]; exact hy_α_fvs)
                hy_s_inner_fvs
                (fun _ => Ne.symm (fun h => hzx h.symm))
              have hrhs : (body₂.open_at 0 (.fvar y)).subst_fvar y (.fvar x) = body₂.open_at 0 (.fvar x) := by
                rw [subst_fvar_fvar_open_at]
                simp only [LNExpr.subst_fvar, beq_self_eq_true, ite_true]
                rw [subst_fvar_notin hy_body₂_fvs]
              rw [hrhs] at hnp_x
              -- Step 3: apply IH
              have hnp_out := _hnp_ih z hnp_x
              -- Step 4: rename x → y
              have hnp_y_out := noPromoAt_sub_rename hnp_out hx_all_fvs' hy_all_fvs' hx_body₁_fvs
                (by simp [LNAnn.fvs]; exact hx_α'_fvs)
                hx_s₁_fvs
                (fun _ => Ne.symm hy_ne_z)
              rw [open_close_subst u₃_lc]
              exact hnp_y_out)
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
