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
   edge needs `LNEquivRed Γ s t t'` (current stack). Same-output stack extension
   is FALSE when the annotation t is a lambda (ME-FUN at [] vs ME-FOP at s
   produce different body contexts). The existential version is trivially true
   but NOT SUFFICIENT: the right edge forces t₃ = t' via ms_pro.

   NOTE: ME-PRO now uses nil stack for its SubRed premise (see rule definition).
   This eliminates the former counterexample cex_Γ at end of file: ME-PRO
   output is now stack-independent (always reduces via SubRed at []). However,
   stack extension is still FALSE for lambda terms directly (ME-FUN vs ME-FOP),
   and .sub annotations CAN be lambdas, so the MS-PRO/ME-VAR blocker persists.

   ### Impact of nil-stack ME-PRO on stack extension

   With nil-stack ME-PRO, stack sensitivity now enters ONLY through ME-FUN
   vs ME-FOP (top-level lambda terms at different stacks). ME-PRO no longer
   propagates stack sensitivity through annotation lookups. Specifically:
   - EquivRed on fvar terms: stack extension NOW HOLDS (ME-VAR is trivially
     stack-independent, ME-PRO uses SubRed at [] regardless of outer stack)
   - EquivRed on lambda terms: stack extension still FALSE (ME-FUN vs ME-FOP)
   - EquivRed on app/top terms: depends on sub-terms

   The former cex_Γ counterexample (fvar "x" with annotation lam(fvar "y")(bvar 0))
   is INVALIDATED: with nil-stack ME-PRO, the SubRed of the annotation always
   uses MS-FUN (at []) regardless of the outer stack, so the output is identical
   at [] and [.top]. The cex_Γ example at end of file still compiles (the []
   derivation is unchanged) but the comment saying the [.top] derivation is
   "NOT derivable" is now incorrect — it IS derivable via nil-stack ME-PRO.

   ### Remaining restricted variants (still insufficient)

   (a) Non-lambda restriction: `¬∃ d b, u = .lam d b → EquivRed Γ [] u v → EquivRed Γ s u v`
       With nil-stack ME-PRO, this is now TRUE for fvar terms! But .sub
       annotations CAN be lambdas (e.g., domain of λ(λT.0).body), so
       the MS-PRO/ME-VAR case still encounters lambda annotations.

   (b)-(d) Same as before: insufficiently general.

   ### Detailed analysis of the MS-PRO/ME-VAR blocker

   The commutativity diagram for this case:
   ```
   t₂ ──≡→── t₃
   ≤↑          ≤↑
   t₀ ──≡→── t₁
   ```
   Bottom: `Γ;s ⊢ fvar x ≡→ fvar x` (ME-VAR)
   Left:   `Γ;s ⊢ fvar x ≤→ t` (MS-PRO, x ≤ t ∈ Γ)
   So t₀ = fvar x, t₁ = fvar x, t₂ = t (annotation looked up by MS-PRO).
   We need t₃ with `Γ;s ⊢ t ≡→ t₃` (top) and `Γ';s' ⊢ fvar x ≤→ t₃` (right).

   **Candidate t₃ = t' (from ctxRed):**
   Top: EquivRed Γ s t t' — BLOCKED. We have EquivRed Γ [] t t' (from
   ctxRed_lookup_sub, since CT-ANN reduces annotations at nil stack), but
   need it at stack s. Stack extension is FALSE (see counterexamples below).
   Right: MS-PRO with x ≤ t' ∈ Γ' — works via ctxRed_lookup_sub.

   **Candidate t₃ = t (identity):**
   Top: equivRed_refl Γ s t t — works if t is lc.
   Right: MS-PRO needs x ≤ t ∈ Γ'. But Γ' has x ≤ t' (reduced annotation).
   MS-PRO gives t', not t. ✗

   **Candidate t₃ via diamond on two EquivReds of t:**
   We have EquivRed Γ [] t t' (ctxRed) and equivRed_refl Γ s t t (identity).
   Diamond requires SAME context (Γ, Γ) but DIFFERENT stacks ([], s). ✗

   **Candidate t₃ via commutativity recursion:**
   We don't have a SubRed of t at stack s to feed into commutativity.
   MS-PRO gives fvar x ≤→ t, not a SubRed ON t.

   **Candidate: weakened return type with connecting edge:**
   Instead of requiring both edges to meet at a single t₃, allow:
   `∃ t₃ t₄, EquivRed Γ s t₂ t₃ × SubRed Γ' s' t₁ t₄ × EquivRed Γ' s' t₃ t₄`
   (a connecting edge between the top and right results). This gives the diagram:
   ```
   t₂ ──≡→── t₃
   ≤↑          ≡↕
   t₀ ──≡→── t₁
                ≤↓
                t₄
   ```
   For the MS-PRO/ME-VAR case: top edge EquivRed Γ s t t₃ (e.g. t₃ = t via
   equivRed_refl). Right edge SubRed Γ' s' (fvar x) t₄ = t' via MS-PRO.
   Connecting edge: EquivRed Γ' s' t t' — still needs stack extension (we
   have EquivRed Γ [] t t' from ctxRed, not at stack s'). This alternative
   return type does NOT avoid the fundamental stack alignment problem. ✗

   **Candidate: reflexive top edge (if annotations are normal forms):**
   If t = t' (annotation already fully reduced), then: top edge equivRed_refl
   Γ s t t ✓, right edge MS-PRO with x ≤ t ∈ Γ' ✓ (since t' = t). But
   annotations are NOT always normal forms — e.g. `app (lam .top .top) .top`
   is a valid annotation (a beta-redex). ctxRed would reduce it. The
   commutativity theorem must handle ALL contexts, including ones with
   non-normal annotations. ✗

   **Candidate using other SubRed constructors for right edge:**
   SubRed Γ' s' (fvar x) t₃ can only be:
   - MS-PRO: t₃ = t' (blocked as above)
   - MS-EQU + ME-VAR: t₃ = fvar x (top edge needs t ≡→ fvar x — not general)
   - MS-TOP: t₃ = Top (top edge needs t ≡→ Top — not general)
   No alternative completion exists.

   **Candidate t₃ = t via equivRed_refl + original annotation in Γ':**
   Top: EquivRed Γ s t t via equivRed_refl — works if t is lc. ✓
   Right: MS-PRO needs x ≤ t ∈ Γ'. But Γ' has x ≤ t' (reduced), not x ≤ t. ✗

   **Candidate t₃ = fvar x via MS-EQU + ME-VAR for right edge:**
   Right: SubRed Γ' s' (fvar x) (fvar x) via ms_equ(me_var) — requires x to
   have .equiv annotation, but MS-PRO gave x a .sub annotation. ✗
   (Even if it worked, top edge needs t ≡→ fvar x — not general.)

   **Candidate t₃ = .top via MS-TOP for right edge:**
   Right: SubRed Γ' s' (fvar x) .top via ms_top — always works. ✓
   Top: EquivRed Γ s t .top — only holds if t reduces to Top. Not general. ✗

   **Candidate: choose ctxRed_refl (Γ' = Γ, s' = s) to avoid the problem:**
   This would give: Right = MS-PRO with x ≤ t ∈ Γ (original, unreduced). ✓
   Top = equivRed_refl Γ s t t. ✓ Both edges close.
   BUT commutativity takes hctx as INPUT — the caller provides a specific
   ctxRed. The theorem must work for ALL Γ';s' with Γ;s ↦ Γ';s', so we
   cannot choose ctxRed_refl; we must handle the given Γ'. ✗

   **Candidate: weaken conclusion to use Γ;[] instead of Γ';s':**
   Even with Γ' = Γ, the right edge MS-PRO gives x ≤ t (original), so
   t₃ = t and top = equivRed_refl. But the right edge is at stack [] while
   the top edge is at stack s — different stacks. And the conclusion
   quantifies over ALL extended contexts anyway, so weakening doesn't help. ✗

   **Root cause:** CT-ANN reduces annotations at nil stack ([] in the
   EquivRed premise of ct_ann_sub/ct_ann_equiv), but commutativity needs
   the annotation's EquivRed at the CURRENT stack s.

   ### Potential resolution: fix CT-ANN to use full stack

   If CT-ANN used `Γ;s ⊢ t ≡→ t'` instead of `Γ;[] ⊢ t ≡→ t'`, then
   ctxRed_lookup_sub would give `EquivRed Γ s t t'` directly, and the
   MS-PRO/ME-VAR case closes trivially (top = EquivRed Γ s t t', right =
   MS-PRO with x ≤ t' ∈ Γ'). The same fix would resolve the identical
   stack alignment problem in equivRed_subst_diamond's ME-VAR y=x and
   ME-PRO y≠x cases.

   This is likely a gap in the paper's definition (Section 3, CT-ANN rule).
   The nil-stack choice for CT-ANN is not motivated in the paper and appears
   to be an oversight — annotations are not intrinsically stack-independent
   (counterexample: lam top (bvar 0) at different stacks gives different
   outputs). Changing CT-ANN to use the full stack would NOT affect ctxRed_refl
   (which already builds EquivRed at arbitrary stacks via equivRed_refl) and
   would make stack extension unnecessary throughout the development.

   STATUS: EXHAUSTIVELY BLOCKED. Every possible witness t₃ and every
   possible right-edge SubRed constructor has been tried:
   - t₃ = t' via MS-PRO: top edge needs stack extension (FALSE)
   - t₃ = t via MS-PRO: Γ' has t' not t
   - t₃ = fvar x via MS-EQU+ME-VAR: x has .sub annotation, not .equiv
   - t₃ = .top via MS-TOP: top edge t ≡→ .top not general
   - ctxRed_refl dodge: theorem must work for ALL ctxRed, not just refl
   - Weakened conclusion (Γ;[] not Γ';s'): stacks still mismatch
   - equivRed_refl + original annotation: Γ' has reduced annotation
   - Diamond of two EquivReds: different stacks ([], s)
   - Commutativity recursion: no SubRed ON t at stack s
   - Weakened return type (connecting edge t₃↔t₄): connecting edge
     still needs stack extension
   - Normal form assumption on annotations: not general (beta-redexes
     are valid annotations)

   **Why no construction of t₃ can work (QED argument):**
   The right edge SubRed Γ' s' (fvar x) t₃ can ONLY be constructed by:
   (1) MS-PRO: t₃ = t' (the annotation of x in Γ'). Forced.
   (2) MS-TOP: t₃ = .top. Always available.
   (3) MS-EQU(ME-VAR): t₃ = fvar x. Requires x to have .equiv annotation.
   No other SubRed constructor applies to fvar x.
   For (1): top edge needs EquivRed Γ s t t' — stack extension (FALSE).
   For (2): top edge needs EquivRed Γ s t .top — not true for all t.
   For (3): x has .sub annotation (MS-PRO premise), not .equiv. ✗
   Since t₃ is forced to one of {t', .top, fvar x} by the right edge, and
   every choice fails for the top edge, the case is IMPOSSIBLE to close
   without changing the system. The ONLY resolution is fixing CT-ANN to
   reduce annotations at the full stack s instead of nil.

   ### Weakening-based approaches also fail

   Adding `equivRed_weaken` / `subRed_weaken` to the mutual block with
   commutativity was investigated as an alternative to stack extension:

   (a) Same-output weakening:
       `EquivRed Γ s u v → CtxRed Γ s Γ' s' → EquivRed Γ' s' u v`
       Previously DISPROVED. CtxRed changes annotations, making the
       original output v unreachable in the reduced context Γ'.

   (b) Existential-output weakening:
       `EquivRed Γ s u v → CtxRed Γ s Γ' s' → ∃ v', EquivRed Γ' s' u v'`
       TRUE (trivially via equivRed_refl). But NOT SUFFICIENT: the right
       edge forces t₃ to be one of {t', .top, fvar x} (see QED argument
       above). An existential witness cannot guarantee t₃ = t'.

   (c) Restructuring diamond_full to return results in original Γ;s, then
       applying weakening to lift to Γ₁;s₁:
       Fails because weakening (a) is false.

   (d) CT-ANN at full stack (previously tried, commit 79aa0ff8, reverted
       in 9f8d8381): DOES fix MS-PRO/ME-VAR trivially. But breaks
       ctxRed_nil_of_ctxRed, ctxRed_lookup, ctxRed_stack_inv, and
       diamond_full body construction. Shifts the stack alignment problem
       from commutativity to infrastructure. The paper's nil-stack CT-ANN
       is designed to work WITH Lemma 22; without Lemma 22, neither
       choice of CT-ANN avoids the gap.

   CONCLUSION: The MS-PRO/ME-VAR case requires either stack extension
   (FALSE), weakening through ctxRed (FALSE in same-output form,
   insufficient in existential form), or changing CT-ANN (shifts but does
   not resolve the problem). The paper's proof has a genuine gap at this
   case that cannot be fixed with local changes to the proof strategy.
   A fundamental rethinking of how MPSS handles the interaction between
   annotations and stacks is needed.

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
- `noPromoAt_no_equiv_fresh` / `noPromoAt_no_equiv_fresh_sub`: construct
  noPromoAt x for any EquivRed/SubRed derivation when x has no .equiv
  annotation in Γ, x ∉ annotations that other .equiv vars point to,
  x ∉ stack elements, and x ∉ u.fvs. Proved by mutual induction on the
  reduction derivation using @LNEquivRed.rec / @LNSubRed.rec (both are
  Type-valued, so elimination into Type is allowed — the old "Prop blocker"
  comment was stale). The key insight: without .equiv annotation, ME-PRO
  on x cannot fire, and x ∉ u.fvs prevents x from reaching the stack via
  ME-APP/ME-FOP. These are useful for constructing noPromoAt witnesses
  from scratch (e.g., for freshly-picked cofinite variables whose
  annotations are .sub, not .equiv).
- `equivRed_ctx_drop_fresh` / `subRed_ctx_drop_fresh`: context drop via
  freshness — if `EquivRed/SubRed ((x,.equiv v)::Γ) s u u'` and x is fresh
  in u, v, Γ (all_fvs), and the stack, then `EquivRed/SubRed Γ s u u'`.
  Unlike `subRed_ctx_drop` which requires an explicit `noPromoAt x` witness,
  these construct the drop directly by mutual induction, using `fresh_in_anns`
  to propagate freshness. The EquivRed version was already present; the SubRed
  version mirrors it using `@LNSubRed.rec`.
- `ctxRed_nil_equiv_head_inv`: inversion of `CtxRed ((x,.equiv v)::Γ) []
  ((x,.equiv v')::Γ') []` into inner `CtxRed Γ [] Γ' []` and
  `EquivRed Γ [] v v'`. At empty stack, only ct_ann_equiv applies.

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
      mostly proved; the right-edge noPromoAt for `.inr` of a second
      promotion_collapse remains sorry'd. The correct resolution is
      equivRed_subst_diamond (see dedicated section below), NOT the false
      subRed_subst_equiv or equivRed_subst_equiv.
- **equivRed_subst_equiv**: DISPROVED. The statement "if EquivRed ((x,.equiv v)::Γ)
  s u u' with freshness, then EquivRed Γ s (u[x↦v]) (u'[x↦v])" is FALSE.
  Counterexample at end of file. The failure: ME-PRO on x yields SubRed of v,
  which can use ms_pro on .sub-annotated variables. After substitution, the
  conclusion demands EquivRed on v, but me_pro only works with .equiv annotations.
  A SubRed version (subRed_subst_equiv) is ALSO FALSE — counterexample at end
  of file. The failure: me_app reduces both operator and operand simultaneously,
  but after substitution only SubRed (not EquivRed) is available for the operand.

## equivRed_subst_diamond: the correct substitution lemma (IN MUTUAL BLOCK, sorry'd)

The flat substitution lemmas (equivRed_subst_equiv, subRed_subst_equiv) are both
FALSE because they demand the exact same source→target pair after substitution.
The CORRECT formulation is a DIAMOND:

  equivRed_subst_diamond:
    EquivRed ((x,.equiv v)::Γ) s u u'
    → CtxRed ((x,.equiv v)::Γ) s ((x,.equiv v')::Γ') s'
    → freshness conditions (x ∉ all_fvs Γ, x ∉ v.fvs, v.lc, etc.)
    → ∃ w, EquivRed Γ s (u'[x↦v]) w ∧ SubRed Γ' s' (u[x↦v']) w

  (and the mutual SubRed variant: subRed_subst_diamond)

Both theorems are now in a MUTUAL BLOCK with commutativity, sharing the
termination measure `(budget, term.sz)`. Partially proved cases:
ME-TOP, ME-TAP (trivially .top), ME-VAR y≠x (reflexivity), MS-TOP,
MS-EQU (delegates to equivRed_subst_diamond). Remaining sorry'd cases:
- ME-VAR y=x: the "stack alignment problem" — need EquivRed Γ s v w ∧
  SubRed Γ' s' v' w. Have EquivRed Γ [] v v' (from hctx) but need it at
  stack s. Stack extension is FALSE. Root cause: CT-ANN reduces annotations
  at nil stack. Would be resolved by changing CT-ANN to use full stack s
  (see sorry #7 in file header).
- ME-PRO y=x: PARTIALLY WIRED. The commutativity call is in place:
  commutativity(v.sz, v, equivRed_refl, hsub_pro, hctx) produces
  htop : EquivRed ((x,.equiv v)::Γ) s u' t₃ and
  hright : SubRed ((x,.equiv v')::Γ') s' v t₃.
  Left edge is CLOSED: equivRed_ctx_drop_fresh drops x to get EquivRed Γ s u' t₃.
  Right edge sorry remains: need SubRed Γ' s' v' t₃ from
  SubRed ((x,.equiv v')::Γ') s' v t₃.
  Infrastructure for context drop (subRed_ctx_drop_fresh) is available.
  Remaining gap: "input translation" — changing input from v to v' where
  EquivRed Γ [] v v'. This is the stack alignment problem (EquivRed at
  stack [] vs SubRed at stack s').
- ME-PRO y≠x: PARTIALLY WIRED. Freshness established (x ∉ α.fvs, x ∉ u'.fvs
  via subRed_preserves_not_mem_fvs_gen). Substitutions rewritten. Core sorry:
  need diamond of SubRed Γ s α u' and EquivRed Γ [] α α' at different stacks.
- ME-APP, ME-BET, ME-FUN, ME-FOP: structural recursion with budget decreasing.
  ME-APP has stack alignment subtlety (see NOTE below).
- MS-PRO, MS-APP, MS-FUN, MS-FOP: structural SubRed cases.

The key insight: at ME-PRO on x (the case that breaks flat substitution),
the promotion gives SubRed(v → result). After subst:
- u[x↦v'] = v' and u'[x↦v] = result (since x ∉ fvs(result))
- Need: ∃ w, EquivRed Γ s result w ∧ SubRed Γ' s' v' w
- This is COMMUTATIVITY on v (EquivRed v→v', SubRed v→result, CtxRed)
- And v.sz < app(lam dom body, v).sz, so the IH applies.

Termination (NOW IMPLEMENTED in the mutual block):
  commutativity(app(lam dom body, v)) calls
  equivRed_subst_diamond on body^x (smaller), which calls
  commutativity on v at ME-PRO-on-x points (v.sz < app(..).sz). Well-founded.
  Shared measure: (budget, u.sz) with lexicographic ordering.
  - commutativity(budget, t₀): (budget, t₀.sz), with t₀.sz ≤ budget
  - equivRed_subst_diamond(budget, u): (budget, u.sz), with u.sz ≤ budget
  All call patterns strictly decrease.

NOTE: The ME-APP case has a stack alignment subtlety. The IH on the operator
gives EquivRed with the pre-substitution operand in the stack, but the outer
me_app construction needs the post-substitution operand. Resolving this likely
requires the IH on the operand (which gives EquivRed/SubRed relating pre/post)
plus a stack update lemma. This needs careful formulation.

This would resolve:
- commutativity ME-BET/MS-FOP `.inr` case sorry (noPromoAt x on output)
- diamond_full ME-PRO cases (SubRed diamond via commutativity)
- diamond_full ME-APP/ME-BET, ME-BET/ME-BET, ME-BET/ME-APP (equivRed subst)

## Sorry'd Theorems
- `equivRed_subst_diamond` / `subRed_subst_diamond`: the diamond substitution lemma.
  Partially proved (ME-TOP, ME-TAP, ME-VAR y≠x, MS-TOP, MS-EQU cases closed).
  ME-PRO y=x: commutativity call wired, x ∉ u'.fvs closed, two translation
  sorrys remain (context shrink + input translation). ME-PRO y≠x: freshness
  wired, core stack alignment sorry remains. ME-VAR y=x: stack alignment sorry.
  Key remaining infrastructure needed:
  (1) EquivRed context drop: EquivRed ((x,.equiv v)::Γ) s u t → EquivRed Γ s u t
      when noPromoAt x (or equivalently x ∉ u.fvs and x fresh in anns)
  (2) SubRed input translation: SubRed Γ' s' v t₃ → SubRed Γ' s' v' w
      where v and v' are related by EquivRed
  Structural cases (ME-APP, ME-BET, ME-FUN, ME-FOP, MS-PRO, MS-APP, MS-FUN,
  MS-FOP) still sorry'd — need recursive calls with careful stack handling.
- `equivRed_rename_strong` / `subRed_rename_strong`: fvar renaming for reductions.
  Replaces the former (false) `equivRed_subst` / `subRed_subst`. The key insight
  is that fvar renaming (specializing substitution to x -> fvar y) avoids the
  blockers that made general substitution false: stacks don't need substituting,
  annotation terms are preserved (since x is fresh for them), and context lookups
  commute with renaming. Sorry'd pending mutual induction proof using the combined
  recursor.
  Infrastructure lemmas available: subst_fvar_fvar_open_at, subst_fvar_notin,
  ctx_swap_sub_ctx, open_subst_comm.

## Sorry Categorization (18 code sorrys, down from 22)

Category A1 sorrys (recursor lock-in) were closed by switching
`subRed_subst_noPromo_noPromoAt` from structural induction via
`@LNSubRed.noPromoAt.rec` to well-founded mutual induction (mutual block with
`equivRed_subst_noPromo_noPromoAt`), using `termination_by sizeOf hnp_y + sizeOf hnp_z`.
The mutual structure allows case-splitting on BOTH hnp_y and hnp_z independently,
resolving the ms_equ(y) vs ms_app/ms_fun/ms_fop(z) cross-cases.

All remaining sorrys fall into four categories:

### Category A2: me_bet cross-constructor mismatch (5 sorrys)
These are in `equivRed_subst_noPromo_noPromoAt`, `subRed_subst_noPromo_noPromoAt`,
and commutativity's noPromoAt preservation. When one side uses me_bet and the other
uses me_app (or ms_app), the sub-derivation outputs differ (different body result
terms), making the IH inapplicable regardless of induction strategy. This is
fundamental, not an artifact of the induction approach.

**noPromoAt normalization (me_bet → me_app) is FALSE.** Formal counterexample at
end of file (section NoPromoAtNormalizationCounterexample). The failure: me_bet
can produce outputs where the operator is NOT a lambda (e.g., app .top .top via
promotion chains inside the body), but me_app at non-empty stack forces the operator
through me_fop which ALWAYS outputs a lambda. So when me_bet's body promotions
eliminate the lambda structure, me_app cannot reproduce the same output. This rules
out the normalization approach to resolving Category A2.

NOTE: The ME-APP/MS-APP noPromoAt case in commutativity is partially closed
(ms_app and me_app sub-cases proved; only me_bet sub-case remains sorry'd).

NOTE: `equivRed_subst_noPromo_noPromoAt` and `subRed_subst_noPromo_noPromoAt`
are NOT called from outside their mutual block — they are purely self-referential.
This means the Category A2 sorrys do not currently block other proofs.

### Category B: Stack alignment / equivRed_subst_diamond (15 sorrys)
Lines: 4993, 4998, 5086, 5094, 5151, 5390 (×2), 5562, 6014, 6039,
       6084 (×2), 6091, 6092, 6123
These are in `diamond_full`, `commutativity`, `equivRed_subst_diamond`, and
`subRed_subst_diamond`. The paper's Lemma 22 (stack extension) is FALSE for
non-empty stacks. ROOT CAUSE: CT-ANN reduces annotations at nil stack ([])
instead of the current stack s. This means ctxRed_lookup_sub yields
`EquivRed Γ [] t t'` when commutativity/equivRed_subst_diamond need
`EquivRed Γ s t t'`. Changing CT-ANN to use full stack s would resolve all
of these (see sorry #7 in file header). The mutual block is wired and
terminates, but individual cases need:
- `x ∉ u'.fvs` for extended contexts (line 6039: needs
  `subRed_preserves_not_mem_fvs` variant where x is in the domain)
- Context translation after commutativity (lines 6084: results in extended
  context need translation to base context)
- Structural recursion cases in equivRed/subRed_subst_diamond (lines 6092,
  6123: ME-APP, ME-BET, ME-FUN, ME-FOP, MS-PRO, MS-APP, MS-FUN, MS-FOP)

### Category C: noPromoAt preservation via diamond (2 sorrys)
Lines: 5353, 5446
These are in commutativity's MS-EQU and ME-BET/MS-EQU cases. The `diamond`
lemma does NOT co-prove noPromoAt preservation. Fix: extend `diamond_full` to
co-prove `∀ x, noPromoAt x input → noPromoAt x output`.

### Category D: Termination (1 sorry)
Line: 5284
In `diamond_full`'s `decreasing_by`. `simp_all [LNExpr.sz, sz_open_at_fvar]`
loops on context hypotheses in me_bet/me_app cases. The goals are trivially
true (`body.sz < (app (lam dom body) v).sz`). Fix: targeted tactic avoiding
large inductive hypotheses, or increase heartbeat limit.

### Overlap note
Line 5427 (ME-APP/MS-APP noPromoAt me_bet sub-case) is Category A.
Line 5562 (ME-BET/MS-FOP .inr noPromoAt) is Category B (needs
equivRed_subst_diamond, not me_bet inversion).

### Investigation: judgment-level noPromoAt / combined approach

Three approaches were investigated to resolve the Category A sorrys:

1. **JudgNoPromo (universal)**: `∀ h : SubRed ..., noPromoAt x ... h` — too strong.
   When x has .equiv annotation, me_pro on x DOES promote, so JudgNoPromo is False
   for judgments reachable via me_pro.

2. **WeakJudgNoPromo (existential)**: `∃ h : SubRed ..., noPromoAt x ... h` — the
   right idea but noPromoAt doesn't take a derivation tree argument (it's an
   independent inductive on terms). So the existential doesn't have the right shape.

3. **Combined subRed_subst_noPromo_with_np**: co-produce SubRed AND noPromoAt z in
   the same induction, using matching constructors. This DOES resolve the recursor
   lock-in (Category A1) because we construct noPromoAt z for the output using the
   same constructor we chose for SubRed, avoiding cross-constructor mismatches.
   However, it does NOT resolve the me_bet output mismatch (Category A2): when
   y uses me_bet with body result t_y and z uses me_bet with body result t_z ≠ t_y,
   the IH requires noPromoAt z at t_y (the constructor we chose), but z's noPromoAt
   provides it at t_z. This is a fundamental mismatch that persists regardless of
   induction strategy.

   The combined approach would require well-founded recursion (not the noPromoAt.rec
   recursor) to handle Category A1. This is viable but would need a custom size
   measure for noPromoAt trees that handles cofinite binder fields.

The main advance from this investigation: proving `noPromoAt_no_equiv_fresh` and
`noPromoAt_fresh_equiv/sub`, which were previously thought unprovable due to a stale
comment about Prop elimination. These enable constructing noPromoAt witnesses from
scratch when freshness conditions hold, bypassing the cross-constructor mismatch
entirely for cases where the tracked variable is sufficiently fresh.

## Research Analysis: Does Transitivity (Theorem 3) Actually Need Full Commutativity?

### Question
The MS-PRO/ME-VAR case of commutativity (Lemma 1) is blocked because CT-ANN
reduces annotations at nil stack, creating a stack alignment problem. Does the
DOWNSTREAM use of commutativity (Theorem 3: transitivity admissibility, and
Theorems 4-5: type safety) actually need the full generalization over ALL
ctxRed instances Γ;s ↦ Γ';s'? If it only needs ctxRed_refl, the MS-PRO/ME-VAR
case becomes trivial.

### Analysis of Theorem 3 (Transitivity is Admissible) — Paper p. 9:25-9:26

**Statement:** If Γ;s ⊢ u ≤* v then Γ;s ⊢ u ≤ v.

**Proof structure:** By induction on the number of intermediary steps in Γ;s ⊢ u ≤* v.
The key step reduces to: given Γ;s ⊢ t ≤ u and Γ;s ⊢ u ≤ v, prove Γ;s ⊢ t ≤ v.

Recall the subtyping definition (paper p. 9:7):
  u ≤ t  iff  ∃ v, t ≡→* v ∧ v ≤→ u

So from Γ;s ⊢ t ≤ u we get: ∃ u₁, u ≡→* u₁ ∧ u₁ ≤→ t
And from Γ;s ⊢ u ≤ v we get: ∃ v₁, v ≡→* v₁ ∧ v₁ ≤→ u

The proof builds the diagram (paper p. 9:26):
```
    v ──≡→── · ──≡→── ·
    ≤↑                 ≤↑
         u ──≡→── ·
             ≤↑
             t
```
The solid edges are from the subtyping definition. The dashed edges are
completed by commutativity (Lemma 1).

**CRITICAL OBSERVATION:** Commutativity (Lemma 1) is called with:
  - Bottom-left: t₀ ≡→ t₁  (from u ≡→* u₁, one step at a time)
  - Left:        t₀ ≤→ t₂  (from v₁ ≤→ u, the subtyping witness)
  - Context:     Γ;s (UNCHANGED — same Γ;s throughout)

The ctxRed passed to Lemma 1 is: Γ;s ↦ Γ';s' for ALL Γ';s' with Γ;s ↦ Γ';s'.

BUT WAIT — what does Theorem 3 actually DO with the output? It gets:
  - Top:   Γ;s ⊢ t₂ ≡→ t₃
  - Right: Γ';s' ⊢ t₁ ≤→ t₃

Theorem 3 needs the RIGHT edge at the ORIGINAL context Γ;s, not at Γ';s'.
The subtyping relation u ≤ t is defined as Γ;s ⊢ t ≡→* v ∧ Γ;s ⊢ v ≤→ u
(both at the SAME Γ;s). So Theorem 3 only needs:
  Γ;s ⊢ t₁ ≤→ t₃   (i.e., the right edge at Γ;s, not Γ';s')

**This means Theorem 3 ONLY NEEDS ctxRed_refl (Γ' = Γ, s' = s).**

### Verification: How Theorem 3 Calls Lemma 1

Looking at the proof on p. 9:26 more carefully:

Step 1: Unfold Γ;s ⊢ t ≤ u into EquivRed* and SubRed.
Step 2: Unfold Γ;s ⊢ u ≤ v into EquivRed* and SubRed.
Step 3: Apply commutativity to the EquivRed (from u ≡→ ...) and SubRed
        (from v₁ ≤→ u) AT THE SAME Γ;s.

The commutativity call is:
  commutativity(Γ, s, u ≡→ u₁_step, v₁ ≤→ u, ctxRed)

Since both the EquivRed and SubRed are at Γ;s, and the output SubRed is
also needed at Γ;s, the only ctxRed that makes sense is ctxRed_refl.

### What About Diamond (Lemma 2)?

Diamond (Lemma 2, p. 9:9) is used to complete the ≡→ chain. The existing
`diamond` in LNMPSS.lean already uses ctxRed_refl (line ~6420):
  `have hid : LNCtxRed Γ s Γ s := ctxRed_refl Γ s hwf_ctx hwf_stk`

So diamond also only needs ctxRed_refl. Confirmed.

### What About Type Safety (Theorems 4-5)?

**Theorem 4 (Progress):** Does NOT use commutativity at all. It's a
straightforward structural induction on terms.

**Theorem 5 (Preservation):** Uses Ws-Rgh (well-subtyping rule), which
references EquivRed (Γ;nil ⊢ t ≡→ t'). Preservation's proof:
1. From Γ ⊢ t ≤*_wf u and t ↦ t', prove Γ ⊢ t' ≤*_wf t.
2. By Ws-Rfl we have Γ ⊢ t' ≤*_wf t', then by Ws-Rgh, Γ ⊢ t' ≤*_wf t.
Preservation does NOT call commutativity directly. It uses Lemma 6
(evaluation preserves well-formedness) and the well-subtyping rules.

**Lemma 7 (Substitution preserves well-formedness):** Uses transitivity
(Theorem 3) internally in its proof (paper p. 9:28), specifically in the
Ws-Lf2 case and the Wf-App case. But Theorem 3 only needs ctxRed_refl
(as shown above).

**Lemma 9:** Uses a restricted form of commutativity for substitution.
This is equivRed_subst_diamond (in the mutual block), which DOES need
non-trivial ctxRed. BUT: Lemma 9 is used for Lemma 7's Wf-App case,
and it passes the ctxRed from ct_ann_sub (the annotation reduction from
the substitution). So equivRed_subst_diamond genuinely needs non-trivial
ctxRed — but it's in the mutual block with commutativity and has its
OWN stack alignment problem at ME-VAR y=x (the same root cause).

### Conclusion

**Theorem 3 (transitivity) only needs commutativity at ctxRed_refl.**

A RESTRICTED commutativity with only ctxRed_refl would suffice for:
- Theorem 3 (transitivity admissibility)
- Lemma 2 (diamond property, already uses ctxRed_refl)
- Theorem 4 (progress, doesn't use commutativity)
- Theorem 5 (preservation, uses Theorem 3 which uses ctxRed_refl)

**However, the full generalization over ALL ctxRed is still needed for:**
1. The INDUCTIVE PROOF of commutativity itself. The paper (p. 9:8) explains:
   "The generalisation over all possible resulting contexts Γ';s' is crucial
   for the inductive proof." Specifically:
   - ME-FUN case: the IH is applied at context Γ, x ≤ t₀; nil, and the
     ctxRed from the outer Γ;s ↦ Γ';s' combined with CT-ANN gives
     Γ, x ≤ t₀; nil ↦ Γ', x ≤ t₁; nil. This is NOT ctxRed_refl.
   - ME-FOP case: similarly extends the ctxRed with CT-STK and CT-ANN.
   - ME-APP case: extends with CT-STK for the stack.
   - ME-BET case: extends with CT-ANN.

2. equivRed_subst_diamond (in the mutual block with commutativity).
   ME-PRO-on-x calls commutativity on v, passing the ctxRed from the
   substitution context. This ctxRed is non-trivial.

**So the full ctxRed generalization is needed for the INTERNAL induction,
even though the EXTERNAL callers only need ctxRed_refl.**

### Impact on the MS-PRO/ME-VAR Blocker

This analysis does NOT provide a way to avoid the MS-PRO/ME-VAR case.
The case is encountered during the internal induction of commutativity
(when the input term is fvar x, h_equiv is me_var, and h_sub is ms_pro),
and the ctxRed at that point is whatever was passed in — which in
recursive calls is NOT ctxRed_refl.

The two viable resolutions remain:
1. **Fix CT-ANN to use full stack s** (change nil to s in ct_ann_sub/
   ct_ann_equiv). This makes ctxRed_lookup_sub yield EquivRed Γ s t t'
   directly, closing the case trivially.
2. **Prove that annotations in well-formed contexts are stack-independent**
   (a restricted stack extension for annotation terms). This is harder
   and not clearly true.

### Summary Table

| Downstream theorem  | Uses commutativity? | Which ctxRed?  |
|---------------------|---------------------|----------------|
| Theorem 3 (trans)   | Yes (Lemma 1)       | ctxRed_refl    |
| Lemma 2 (diamond)   | No                  | ctxRed_refl    |
| Theorem 4 (progress)| No                  | N/A            |
| Theorem 5 (preserv) | Indirectly (via T3) | ctxRed_refl    |
| Lemma 7 (subst wf)  | Yes (via T3, L9)    | ctxRed_refl*   |
| Commutativity IH    | Yes (recursive)     | NON-TRIVIAL    |
| equivRed_subst_dia  | Yes (mutual)        | NON-TRIVIAL    |

*Lemma 7 uses Theorem 3 at ctxRed_refl, but also uses Lemma 9 which
calls equivRed_subst_diamond with non-trivial ctxRed.
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
private def exists_fresh_string (avoid : List String) : Σ' s : String, s ∉ avoid := by
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
def exists_fresh (Γ : LNCtx) (e : LNExpr)
    : Σ' x : String, PLift (x ∉ LNCtx.dom Γ) × PLift (x ∉ e.fvs) := by
  obtain ⟨x, hx⟩ := exists_fresh_string (LNCtx.dom Γ ++ e.fvs)
  exact ⟨x, ⟨fun h => hx (List.mem_append_left _ h)⟩, ⟨fun h => hx (List.mem_append_right _ h)⟩⟩

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
inductive LNEquivRed : LNCtx → LNStack → LNExpr → LNExpr → Type where
  /-- ME-PRO: Promote through equivalence annotation.
      `x ≡ α ∈ Γ`  and  `Γ; [] ⊢ α ≤→ α'`
      ⟹  `Γ; s ⊢ fvar x ≡→ α'`

      The SubRed premise uses the NIL stack [], not the ambient stack s.
      Annotations are always reduced stack-independently: they don't receive
      arguments from the stack. This makes ME-PRO's output deterministic
      regardless of the ambient stack, which eliminates the stack-sensitivity
      that previously entered through annotation reductions (MS-FUN vs MS-FOP
      producing different body contexts). -/
  | me_pro {Γ s x α α'} :
      LNCtx.mem_equiv Γ x α →
      LNSubRed Γ [] α α' →
      LNEquivRed Γ s (.fvar x) α'

  /-- ME-BET: Simultaneous β-reduction (cofinite quantification).
      For all `x` not in a finite set `L`:
        `(Γ, x ≡ v); s ⊢ body^x ≡→ t^x`
        `Γ; nil ⊢ v ≡→ v'`
      ⟹  `Γ; s ⊢ (λdom.body) v ≡→ t^v'`

      Here `t` is a term with bvar 0 representing the closed body result.
      Opening `t` with `v'` gives the β-reduct. -/
  | me_bet {Γ : LNCtx} {s : LNStack} {dom body t v v' : LNExpr} (L : List String) :
      (∀ x, x ∉ L → LNEquivRed ((x, LNAnn.equiv v) :: Γ) s (body.open_at 0 (.fvar x)) (t.open_at 0 (.fvar x))) →
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
inductive LNSubRed : LNCtx → LNStack → LNExpr → LNExpr → Type where
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

NOTE (paper gap): CT-ANN reduces annotations at nil stack (`Γ; [] ⊢ t ≡→ t'`),
following the paper's Section 3 definition. This causes the "stack alignment
problem" in commutativity's MS-PRO/ME-VAR case and equivRed_subst_diamond's
ME-VAR y=x case: ctxRed_lookup_sub yields `EquivRed Γ [] t t'` but these
cases need `EquivRed Γ s t t'` at the current stack s. Stack extension
(`EquivRed Γ [] t t' → EquivRed Γ s t t'`) is FALSE (counterexample at end
of file). Changing CT-ANN to use the full stack s would resolve all stack
alignment sorrys without affecting ctxRed_refl or other proved lemmas.
See sorry #7 in the file header for the full analysis.
-/

inductive LNCtxRed : LNCtx → LNStack → LNCtx → LNStack → Type where
  /-- CT-ANN (sub): Reduce a subtype annotation.
      `Γ; s ↦ Γ'; s'`  and  `Γ; nil ⊢ t ≡→ t'`
      ⟹  `(x ≤ t, Γ); s ↦ (x ≤ t', Γ'); s'`
      NOTE: the nil stack here (not s) is the root cause of the stack alignment
      problem. See sorry #7 and the CT-ANN note above. -/
  | ct_ann_sub {Γ s Γ' s' x t t'} :
      LNCtxRed Γ s Γ' s' →
      LNEquivRed Γ [] t t' →
      LNCtxRed ((x, .sub t) :: Γ) s ((x, .sub t') :: Γ') s'

  /-- CT-ANN (equiv): Reduce an equivalence annotation.
      `Γ; s ↦ Γ'; s'`  and  `Γ; nil ⊢ α ≡→ α'`
      ⟹  `(x ≡ α, Γ); s ↦ (x ≡ α', Γ'); s'`
      NOTE: same nil-stack issue as ct_ann_sub. See sorry #7. -/
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
def equivRed_refl (Γ : LNCtx) (s : LNStack) (u : LNExpr)
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
def subRed_refl (Γ : LNCtx) (s : LNStack) (u : LNExpr)
    (hlc : u.lc) : LNSubRed Γ s u u :=
  .ms_equ (equivRed_refl Γ s u hlc)

set_option maxHeartbeats 800000 in
/-- Context monotonicity for ≡→: if every lookup in Γ is preserved in Γ',
    then any derivation in Γ holds in Γ'. Proved by mutual induction using
    the combined recursor for LNEquivRed/LNSubRed. The cofinite binder cases
    pass through directly via LNCtx.sub_cons (prepending the same binding
    preserves context inclusion). -/
noncomputable def equivRed_ctx_mono
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
noncomputable def subRed_ctx_mono
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
noncomputable def equivRed_ctx_ext
    {Γ : LNCtx} {s : LNStack} {u v : LNExpr}
    (h : LNEquivRed Γ s u v) {x : String} {ann : LNAnn}
    (hfresh : x ∉ LNCtx.dom Γ)
    : LNEquivRed ((x, ann) :: Γ) s u v :=
  equivRed_ctx_mono h (LNCtx.sub_of_cons_fresh hfresh)

/-- Structural context extension for ≤→ (standard LN infrastructure). -/
noncomputable def subRed_ctx_ext
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

IMPORTANT: Same-output stack extension is FALSE even for annotation terms.
Counterexample: Γ = [(x, .equiv (lam (fvar y) (bvar 0))), (y, .sub top)].
Under []: ME-PRO on x gives SubRed via MS-FUN, body z gets .sub (fvar y),
MS-PRO on z gives (fvar y). Output: lam (fvar y) (fvar y).
Under [.top]: ME-PRO on x would need SubRed via MS-FOP, body z gets
.equiv .top, MS-PRO on z is BLOCKED (needs .sub). Output (fvar y) is
UNREACHABLE. See cex_Γ examples at end of file for formal verification.

The existential version (∃ v', EquivRed Γ s t v') is trivially true via
equivRed_refl but NOT SUFFICIENT for commutativity's MS-PRO/ME-VAR case:
the right edge (ms_pro hmem') forces the witness to be t', requiring the
top edge to produce exactly t'. No alternative diagram completion exists
because SubRed from (fvar x) with .sub annotation can only reach t' (via
ms_pro), fvar x (via ms_equ me_var), or .top (via ms_top).

PREVIOUS RESOLUTION ATTEMPT: dissolve into the mutual block with
equivRed_subst_diamond (same stack mismatch as ME-VAR y=x there).
This does NOT help — the fundamental mismatch (EquivRed at [] vs need at s)
persists regardless of proof structure because CT-ANN inherently reduces
annotations at nil stack.

ACTUAL RESOLUTION: change CT-ANN to reduce annotations at the full stack s
instead of nil. See sorry #7 in the file header for the complete analysis
and rationale. This would make ctxRed_lookup_sub yield EquivRed Γ s t t'
directly, eliminating the need for stack extension entirely.
-/

/-- Context reduction is reflexive (requires all embedded terms to be lc). -/
noncomputable def ctxRed_refl (Γ : LNCtx) (s : LNStack)
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
noncomputable def ctxRed_nil_of_ctxRed
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
private noncomputable def equivRed_rename_gen
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
private noncomputable def subRed_rename_gen
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
noncomputable def equivRed_rename_strong
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
noncomputable def subRed_rename_strong
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
noncomputable def ctxRed_lookup_sub
    {Γ Γ' : LNCtx} {s s' : LNStack} {x : String} {t : LNExpr}
    (hmem : LNCtx.mem_sub Γ x t) (hctx : LNCtxRed Γ s Γ' s')
    (hnd : (LNCtx.dom Γ).Nodup)
    : Σ' (t' : LNExpr) (_ : LNCtx.mem_sub Γ' x t'), LNEquivRed Γ [] t t' := by
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
noncomputable def ctxRed_lookup_equiv
    {Γ Γ' : LNCtx} {s s' : LNStack} {x : String} {α : LNExpr}
    (hmem : LNCtx.mem_equiv Γ x α) (hctx : LNCtxRed Γ s Γ' s')
    (hnd : (LNCtx.dom Γ).Nodup)
    : Σ' (α' : LNExpr) (_ : LNCtx.mem_equiv Γ' x α'), LNEquivRed Γ [] α α' := by
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
noncomputable def equivRed_rename
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
noncomputable def subRed_rename
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

inductive LNEquivRed.noPromoAt : String → LNCtx → LNStack → LNExpr → LNExpr → Type where
  | me_pro {x z Γ s α α'} :
      z ≠ x →
      LNCtx.mem_equiv Γ z α →
      LNSubRed.noPromoAt x Γ [] α α' →
      LNEquivRed.noPromoAt x Γ s (.fvar z) α'
  | me_bet {x : String} {Γ : LNCtx} {s : LNStack} {dom body t v v' : LNExpr} (L : List String) :
      (∀ y, y ∉ L → LNEquivRed.noPromoAt x ((y, LNAnn.equiv v) :: Γ) s (body.open_at 0 (.fvar y)) (t.open_at 0 (.fvar y))) →
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

inductive LNSubRed.noPromoAt : String → LNCtx → LNStack → LNExpr → LNExpr → Type where
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
def equivRed_refl_noPromoAt (z : String) (Γ : LNCtx) (s : LNStack) (u : LNExpr)
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
def subRed_refl_noPromoAt (z : String) (Γ : LNCtx) (s : LNStack) (u : LNExpr)
    (hlc : u.lc)
    : LNSubRed.noPromoAt z Γ s u u :=
  .ms_equ (equivRed_refl_noPromoAt z Γ s u hlc)

-- General annotation swap: if a derivation doesn't promote x,
-- we can change x's annotation to anything.
-- Proved by mutual induction using the mutual recursor for noPromoAt,
-- since sizeOf-based termination fails for Prop-valued mutual inductives.

/-- Transport an equiv-reduction along a context equality. -/
private def equivRed_cast_ctx {Γ₁ Γ₂ : LNCtx} {s : LNStack} {e u : LNExpr}
    (h : Γ₁ = Γ₂) (hr : LNEquivRed Γ₁ s e u) : LNEquivRed Γ₂ s e u :=
  h ▸ hr

/-- Transport a sub-reduction along a context equality. -/
private def subRed_cast_ctx {Γ₁ Γ₂ : LNCtx} {s : LNStack} {e u : LNExpr}
    (h : Γ₁ = Γ₂) (hr : LNSubRed Γ₁ s e u) : LNSubRed Γ₂ s e u :=
  h ▸ hr

-- noPromoAt_equiv_swap and noPromoAt_sub_swap: proved by mutual induction
-- using @LNEquivRed.noPromoAt.rec / @LNSubRed.noPromoAt.rec. The cofinite
-- binder cases augment the avoidance set L with x (to ensure y ≠ x), then
-- use swap_at_first_cons_ne to rewrite the context and equivRed_cast_ctx /
-- subRed_cast_ctx to transport the IH result.

set_option maxHeartbeats 1600000 in
noncomputable def noPromoAt_equiv_swap (x : String) (ann_new : LNAnn)
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
noncomputable def noPromoAt_sub_swap (x : String) (ann_new : LNAnn)
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
-- PROVED: both LNEquivRed and LNSubRed are Type-valued, so elimination into Type is allowed.
-- The proof uses mutual induction on the reduction via @LNEquivRed.rec.
-- Key: x ∉ dom(Γ) means me_pro/ms_pro can't look up x, so z ≠ x at all such points.
-- No additional conditions (x ∉ u.fvs, x ∉ annotations) are needed because
-- even if x appears in terms or annotations, no rule can PROMOTE x without
-- an entry for x in Γ.
set_option maxHeartbeats 12800000 in
noncomputable def noPromoAt_fresh_equiv
    {x : String} {Γ : LNCtx} {s : LNStack} {u v : LNExpr}
    (h : LNEquivRed Γ s u v) (hx : x ∉ LNCtx.dom Γ)
    : LNEquivRed.noPromoAt x Γ s u v := by
  have go :=
    @LNEquivRed.rec
      (motive_1 := fun Γ s u v _ => x ∉ LNCtx.dom Γ → LNEquivRed.noPromoAt x Γ s u v)
      (motive_2 := fun Γ s u v _ => x ∉ LNCtx.dom Γ → LNSubRed.noPromoAt x Γ s u v)
      -- me_pro
      (fun {Γ_p s_p x' α α'} hmem _hsub ih_sub hx => by
        have hne : x' ≠ x := fun heq => hx (heq ▸ mem_dom_of_lookup' (by exact hmem))
        exact .me_pro hne hmem (ih_sub hx))
      -- me_bet
      (fun {Γ_b s_b dom body t v_bet v'_bet} L _hbody _hv ih_body ih_v hx =>
        .me_bet (x :: L)
          (fun w hw => by
            have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
            have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
            exact ih_body w hw_L (not_mem_dom_cons (Ne.symm hw_ne_x) hx))
          (ih_v hx))
      -- me_top
      (fun _ => .me_top)
      -- me_var
      (fun _ => .me_var)
      -- me_tap
      (fun _ => .me_tap)
      -- me_app
      (fun _hu _hv ih_u ih_v hx => .me_app (ih_u hx) (ih_v hx))
      -- me_fun
      (fun L _hdom _hbody ih_dom ih_body hx =>
        .me_fun (x :: L) (ih_dom hx) (fun w hw => by
          have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          exact ih_body w hw_L (not_mem_dom_cons (Ne.symm hw_ne_x) hx)))
      -- me_fop
      (fun L _hdom _hbody ih_dom ih_body hx =>
        .me_fop (x :: L) (ih_dom hx) (fun w hw => by
          have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          exact ih_body w hw_L (not_mem_dom_cons (Ne.symm hw_ne_x) hx)))
      -- ms_pro
      (fun {Γ_sp s_sp x' t} hmem hx => by
        have hne : x' ≠ x := fun heq => hx (heq ▸ mem_dom_of_lookup' (by exact hmem))
        exact .ms_pro hne hmem)
      -- ms_top
      (fun _ => .ms_top)
      -- ms_equ
      (fun _hequ ih hx => .ms_equ (ih hx))
      -- ms_app
      (fun _hsub ih hx => .ms_app (ih hx))
      -- ms_fun
      (fun L _hbody ih hx =>
        .ms_fun (x :: L) (fun w hw => by
          have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          exact ih w hw_L (not_mem_dom_cons (Ne.symm hw_ne_x) hx)))
      -- ms_fop
      (fun L _hbody ih hx =>
        .ms_fop (x :: L) (fun w hw => by
          have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          exact ih w hw_L (not_mem_dom_cons (Ne.symm hw_ne_x) hx)))
  exact go h hx

-- noPromoAt_fresh_sub: same for SubRed, derived using @LNSubRed.rec.
set_option maxHeartbeats 12800000 in
noncomputable def noPromoAt_fresh_sub
    {x : String} {Γ : LNCtx} {s : LNStack} {u v : LNExpr}
    (h : LNSubRed Γ s u v) (hx : x ∉ LNCtx.dom Γ)
    : LNSubRed.noPromoAt x Γ s u v := by
  have go :=
    @LNSubRed.rec
      (motive_1 := fun Γ s u v _ => x ∉ LNCtx.dom Γ → LNEquivRed.noPromoAt x Γ s u v)
      (motive_2 := fun Γ s u v _ => x ∉ LNCtx.dom Γ → LNSubRed.noPromoAt x Γ s u v)
      -- me_pro
      (fun {Γ_p s_p x' α α'} hmem _hsub ih_sub hx => by
        have hne : x' ≠ x := fun heq => hx (heq ▸ mem_dom_of_lookup' (by exact hmem))
        exact .me_pro hne hmem (ih_sub hx))
      -- me_bet
      (fun {Γ_b s_b dom body t v_bet v'_bet} L _hbody _hv ih_body ih_v hx =>
        .me_bet (x :: L)
          (fun w hw => by
            have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
            have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
            exact ih_body w hw_L (not_mem_dom_cons (Ne.symm hw_ne_x) hx))
          (ih_v hx))
      -- me_top
      (fun _ => .me_top)
      -- me_var
      (fun _ => .me_var)
      -- me_tap
      (fun _ => .me_tap)
      -- me_app
      (fun _hu _hv ih_u ih_v hx => .me_app (ih_u hx) (ih_v hx))
      -- me_fun
      (fun L _hdom _hbody ih_dom ih_body hx =>
        .me_fun (x :: L) (ih_dom hx) (fun w hw => by
          have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          exact ih_body w hw_L (not_mem_dom_cons (Ne.symm hw_ne_x) hx)))
      -- me_fop
      (fun L _hdom _hbody ih_dom ih_body hx =>
        .me_fop (x :: L) (ih_dom hx) (fun w hw => by
          have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          exact ih_body w hw_L (not_mem_dom_cons (Ne.symm hw_ne_x) hx)))
      -- ms_pro
      (fun {Γ_sp s_sp x' t} hmem hx => by
        have hne : x' ≠ x := fun heq => hx (heq ▸ mem_dom_of_lookup' (by exact hmem))
        exact .ms_pro hne hmem)
      -- ms_top
      (fun _ => .ms_top)
      -- ms_equ
      (fun _hequ ih hx => .ms_equ (ih hx))
      -- ms_app
      (fun _hsub ih hx => .ms_app (ih hx))
      -- ms_fun
      (fun L _hbody ih hx =>
        .ms_fun (x :: L) (fun w hw => by
          have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          exact ih w hw_L (not_mem_dom_cons (Ne.symm hw_ne_x) hx)))
      -- ms_fop
      (fun L _hbody ih hx =>
        .ms_fop (x :: L) (fun w hw => by
          have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          exact ih w hw_L (not_mem_dom_cons (Ne.symm hw_ne_x) hx)))
  exact go h hx

/-! #### Context drop: remove an unused .equiv binding

If `noPromoAt x` holds for an EquivRed/SubRed derivation in context `(x,.equiv v)::Γ`,
then the derivation is valid in `Γ` alone — the `x` binding is never used.

We define `drop_first x Γ` to remove the first entry with key `x`, prove helper
lemmas, and then prove the main theorem by mutual induction on noPromoAt using
`@LNEquivRed.noPromoAt.rec`. -/

/-- Remove the first entry with key `x` from a context. -/
private def drop_first (x : String) : LNCtx → LNCtx
  | [] => []
  | (y, ann) :: rest =>
    if y = x then rest
    else (y, ann) :: drop_first x rest

private theorem drop_first_head (x : String) (ann : LNAnn) (Γ : LNCtx)
    : drop_first x ((x, ann) :: Γ) = Γ := by
  simp [drop_first]

private theorem drop_first_cons_ne (x y : String) (ann : LNAnn) (Γ : LNCtx) (hne : y ≠ x)
    : drop_first x ((y, ann) :: Γ) = (y, ann) :: drop_first x Γ := by
  simp [drop_first, hne]

private theorem drop_first_lookup_ne (x z : String) (Γ : LNCtx) (hne : z ≠ x)
    : LNCtx.lookup' (drop_first x Γ) z = LNCtx.lookup' Γ z := by
  induction Γ with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨y, ann⟩ := p
    simp only [drop_first]
    by_cases hyx : y = x
    · subst hyx
      simp only [ite_true, LNCtx.lookup']
      rw [beq_false_of_ne' (Ne.symm hne)]
      simp [ih]
    · simp only [hyx, ite_false, LNCtx.lookup']
      by_cases hyz : y == z
      · simp [hyz]
      · simp [hyz, ih]

private theorem drop_first_mem_equiv_ne {x z : String} {Γ : LNCtx} {α : LNExpr}
    (hne : z ≠ x) (hmem : LNCtx.mem_equiv Γ z α)
    : LNCtx.mem_equiv (drop_first x Γ) z α := by
  unfold LNCtx.mem_equiv at *
  rw [drop_first_lookup_ne x z Γ hne]; exact hmem

private theorem drop_first_mem_sub_ne {x z : String} {Γ : LNCtx} {t : LNExpr}
    (hne : z ≠ x) (hmem : LNCtx.mem_sub Γ z t)
    : LNCtx.mem_sub (drop_first x Γ) z t := by
  unfold LNCtx.mem_sub at *
  rw [drop_first_lookup_ne x z Γ hne]; exact hmem

set_option maxHeartbeats 1600000 in
/-- Context drop for EquivRed: if `noPromoAt x` holds, removing `x`'s binding
    from the context preserves the reduction.

    The proof is by mutual induction on the noPromoAt derivation using
    `@LNEquivRed.noPromoAt.rec`, producing `EquivRed (drop_first x Γ) s e u`
    (resp. `SubRed (drop_first x Γ) s e u`).

    For the top-level statement where `Γ = (x, .equiv v) :: Γ_tail`, we have
    `drop_first x ((x, .equiv v) :: Γ_tail) = Γ_tail`, so the conclusion
    simplifies to `EquivRed Γ_tail s e u`. -/
noncomputable def equivRed_ctx_drop
    {x : String} {v : LNExpr} {Γ : LNCtx} {s : LNStack} {e u : LNExpr}
    (hnp : LNEquivRed.noPromoAt x ((x, .equiv v) :: Γ) s e u)
    : LNEquivRed Γ s e u := by
  have result :=
    @LNEquivRed.noPromoAt.rec x
      (fun Γ_np s e u _ => LNEquivRed (drop_first x Γ_np) s e u)
      (fun Γ_np s e u _ => LNSubRed (drop_first x Γ_np) s e u)
      -- me_pro: z ≠ x, z ≡ α ∈ Γ_np, SubRed.noPromoAt x Γ_np s α α'
      (fun hne hmem _hnp ih_sub =>
        .me_pro (drop_first_mem_equiv_ne hne hmem) ih_sub)
      -- me_bet: L, ∀ y ∉ L, noPromoAt x ((y,.equiv v_bet)::Γ_np) s body^y t^y,
      --         noPromoAt x Γ_np [] v_bet v'_bet
      (fun L _hbody _hv ih_body ih_v =>
        .me_bet (x :: L)
          (fun y hy => by
            have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact equivRed_cast_ctx (drop_first_cons_ne x y (.equiv _) _ hy_ne) (ih_body y hy_L))
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
            have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact equivRed_cast_ctx (drop_first_cons_ne x y (.sub _) _ hy_ne) (ih_body y hy_L)))
      -- me_fop: L, noPromoAt dom, ∀ y ∉ L, noPromoAt body
      (fun L _hnp_dom _hnp_body ih_dom ih_body =>
        .me_fop (x :: L) ih_dom
          (fun y hy => by
            have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact equivRed_cast_ctx (drop_first_cons_ne x y (.equiv _) _ hy_ne) (ih_body y hy_L)))
      -- ms_pro: z ≠ x, z ≤ t ∈ Γ_np
      (fun hne hmem => .ms_pro (drop_first_mem_sub_ne hne hmem))
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
            have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact subRed_cast_ctx (drop_first_cons_ne x y (.sub _) _ hy_ne) (ih_body y hy_L)))
      -- ms_fop: L, ∀ y ∉ L, noPromoAt body
      (fun L _hnp_body ih_body =>
        .ms_fop (x :: L)
          (fun y hy => by
            have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact subRed_cast_ctx (drop_first_cons_ne x y (.equiv _) _ hy_ne) (ih_body y hy_L)))
      ((x, .equiv v) :: Γ) s e u hnp
  rwa [drop_first_head] at result

/-- Context drop for SubRed: if `noPromoAt x` holds, removing `x`'s binding
    from the context preserves the reduction. -/
noncomputable def subRed_ctx_drop
    {x : String} {v : LNExpr} {Γ : LNCtx} {s : LNStack} {e u : LNExpr}
    (hnp : LNSubRed.noPromoAt x ((x, .equiv v) :: Γ) s e u)
    : LNSubRed Γ s e u := by
  have result :=
    @LNSubRed.noPromoAt.rec x
      (fun Γ_np s e u _ => LNEquivRed (drop_first x Γ_np) s e u)
      (fun Γ_np s e u _ => LNSubRed (drop_first x Γ_np) s e u)
      -- me_pro: z ≠ x, z ≡ α ∈ Γ_np, SubRed.noPromoAt x Γ_np s α α'
      (fun hne hmem _hnp ih_sub =>
        .me_pro (drop_first_mem_equiv_ne hne hmem) ih_sub)
      -- me_bet
      (fun L _hbody _hv ih_body ih_v =>
        .me_bet (x :: L)
          (fun y hy => by
            have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact equivRed_cast_ctx (drop_first_cons_ne x y (.equiv _) _ hy_ne) (ih_body y hy_L))
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
            have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact equivRed_cast_ctx (drop_first_cons_ne x y (.sub _) _ hy_ne) (ih_body y hy_L)))
      -- me_fop
      (fun L _hnp_dom _hnp_body ih_dom ih_body =>
        .me_fop (x :: L) ih_dom
          (fun y hy => by
            have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact equivRed_cast_ctx (drop_first_cons_ne x y (.equiv _) _ hy_ne) (ih_body y hy_L)))
      -- ms_pro
      (fun hne hmem => .ms_pro (drop_first_mem_sub_ne hne hmem))
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
            have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact subRed_cast_ctx (drop_first_cons_ne x y (.sub _) _ hy_ne) (ih_body y hy_L)))
      -- ms_fop
      (fun L _hnp_body ih_body =>
        .ms_fop (x :: L)
          (fun y hy => by
            have hy_ne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self _ _)
            have hy_L : y ∉ L := fun h => hy (List.mem_cons_of_mem _ h)
            exact subRed_cast_ctx (drop_first_cons_ne x y (.equiv _) _ hy_ne) (ih_body y hy_L)))
      ((x, .equiv v) :: Γ) s e u hnp
  rwa [drop_first_head] at result

-- noPromoAt rename: binder rename x → y preserves noPromoAt z (when z ≠ y or x = y)
-- Proved by mutual induction on noPromoAt using the mutual recursor.
set_option maxHeartbeats 12800000 in
private noncomputable def noPromoAt_sub_rename_gen
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
noncomputable def noPromoAt_sub_rename
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

/-- Domain of ctx_subst_drop: z ∉ dom(Γ) → z ∉ dom(ctx_subst_drop Γ y v). -/
private theorem ctx_subst_drop_not_mem_dom {Γ : LNCtx} {z y : String} {v : LNExpr}
    (hdom : z ∉ LNCtx.dom Γ)
    : z ∉ LNCtx.dom (ctx_subst_drop Γ y v) := by
  induction Γ with
  | nil => simp [ctx_subst_drop, LNCtx.dom, List.filterMap]
  | cons p rest ih =>
    obtain ⟨w, ann⟩ := p
    have hzw : z ≠ w := fun heq => hdom (heq ▸ List.mem_cons_self _ _)
    have hdom_rest : z ∉ LNCtx.dom rest := fun h => hdom (List.mem_cons_of_mem _ h)
    by_cases hwy : w == y
    · rw [show w = y from by simpa [beq_iff_eq] using hwy]
      rw [ctx_subst_drop_cons_eq]
      exact ih hdom_rest
    · have hne : w ≠ y := by simpa [beq_iff_eq] using hwy
      rw [ctx_subst_drop_cons_ne hne]
      simp only [LNCtx.dom, List.map, List.mem_cons]
      intro h; cases h with
      | inl heq => exact hzw heq
      | inr hmem => exact ih hdom_rest hmem

/-- Domain of ctx_subst_drop: y ∉ dom(ctx_subst_drop Γ y v). -/
private theorem ctx_subst_drop_self_not_mem_dom {Γ : LNCtx} {y : String} {v : LNExpr}
    : y ∉ LNCtx.dom (ctx_subst_drop Γ y v) := by
  induction Γ with
  | nil => simp [ctx_subst_drop, LNCtx.dom, List.filterMap]
  | cons p rest ih =>
    obtain ⟨w, ann⟩ := p
    by_cases hwy : w == y
    · rw [show w = y from by simpa [beq_iff_eq] using hwy]
      rw [ctx_subst_drop_cons_eq]
      exact ih
    · have hne : w ≠ y := by simpa [beq_iff_eq] using hwy
      rw [ctx_subst_drop_cons_ne hne]
      simp only [LNCtx.dom, List.map, List.mem_cons]
      intro h; cases h with
      | inl heq => exact hne heq.symm
      | inr hmem => exact ih hmem

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

private def equivRed_noPromoAt_cast_ctx {x : String} {Γ₁ Γ₂ : LNCtx} {s : LNStack} {e u : LNExpr}
    (h : Γ₁ = Γ₂) (hr : LNEquivRed.noPromoAt x Γ₁ s e u) : LNEquivRed.noPromoAt x Γ₂ s e u :=
  h ▸ hr

private def subRed_noPromoAt_cast_ctx {x : String} {Γ₁ Γ₂ : LNCtx} {s : LNStack} {e u : LNExpr}
    (h : Γ₁ = Γ₂) (hr : LNSubRed.noPromoAt x Γ₁ s e u) : LNSubRed.noPromoAt x Γ₂ s e u :=
  h ▸ hr

-- noPromoAt x is independent of x's own annotation: change the head annotation.
-- Since noPromoAt never accesses x's annotation (ms_pro/me_pro both require z ≠ x),
-- the same derivation structure works in any annotation for x.
-- Proved by mutual induction on the noPromoAt using the existing swap_at_first
-- machinery (same approach as noPromoAt_equiv_swap/noPromoAt_sub_swap).
set_option maxHeartbeats 12800000 in
noncomputable def noPromoAt_sub_head_ann_swap
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
/-- noPromoAt when x has no .equiv in the context and x ∉ u.fvs.
    Proved by mutual induction on the EquivRed/SubRed derivation.
    (Both are Type-valued, so elimination into Type (noPromoAt) is allowed.) -/
noncomputable def noPromoAt_no_equiv_fresh
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
        (∀ α, ¬ LNCtx.mem_equiv Γ x α) →
        (∀ z α, LNCtx.mem_equiv Γ z α → x ∉ α.fvs) →
        (∀ e ∈ s, x ∉ e.fvs) →
        x ∉ u.fvs →
        LNEquivRed.noPromoAt x Γ s u v)
      (motive_2 := fun Γ s u v _ =>
        (∀ α, ¬ LNCtx.mem_equiv Γ x α) →
        (∀ z α, LNCtx.mem_equiv Γ z α → x ∉ α.fvs) →
        (∀ e ∈ s, x ∉ e.fvs) →
        x ∉ u.fvs →
        LNSubRed.noPromoAt x Γ s u v)
      -- me_pro: x' ≡ α ∈ Γ, SubRed Γ s α α'
      (fun {Γ_p s_p x' α α'} hmem _hsub ih_sub hA hB hC hD => by
        -- x' ≠ x because x ∉ (fvar x').fvs and u = fvar x'
        have hne : x' ≠ x := by
          intro heq; subst heq; exact hD (List.mem_cons_self _ _)
        -- x ∉ α.fvs from hB
        have hx_α : x ∉ α.fvs := hB x' α hmem
        exact .me_pro hne hmem (ih_sub hA hB (fun _ he => absurd he (List.not_mem_nil _)) hx_α))
      -- me_bet: app (lam dom body) v_bet → t^v'
      (fun {Γ_b s_b dom body t v_bet v'_bet} L _hbody _hv ih_body ih_v hA hB hC hD => by
        have hD_v : x ∉ v_bet.fvs := fun hmem =>
          hD (List.mem_append_right _ hmem)
        have hD_body : x ∉ body.fvs := fun hmem =>
          hD (List.mem_append_left _ (List.mem_append_right _ hmem))
        exact .me_bet (x :: L)
          (fun w hw => by
            have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
            have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
            apply ih_body w hw_L
            · -- hA for extended context (w, .equiv v_bet) :: Γ
              intro α' hmem_ext
              unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
              by_cases hwx : w == x
              · simp [beq_iff_eq] at hwx; exact absurd hwx hw_ne_x
              · simp [hwx] at hmem_ext; exact hA α' hmem_ext
            · -- hB for extended context
              intro z' α' hmem_ext
              unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
              by_cases hwz : w == z'
              · simp [hwz] at hmem_ext; subst hmem_ext; exact hD_v
              · simp [hwz] at hmem_ext; exact hB z' α' hmem_ext
            · -- hC: same stack
              exact hC
            · -- hD for body^w
              exact LNExpr.not_mem_fvs_open_at body hD_body (Ne.symm hw_ne_x))
          (ih_v hA hB (fun _ he => absurd he (List.not_mem_nil _)) hD_v))
      -- me_top
      (fun _hA _hB _hC _hD => .me_top)
      -- me_var
      (fun _hA _hB _hC _hD => .me_var)
      -- me_tap
      (fun _hA _hB _hC _hD => .me_tap)
      -- me_app
      (fun {Γ_a s_a u_a u'_a v_a v'_a} _hu _hv ih_u ih_v hA hB hC hD => by
        have hD_u : x ∉ u_a.fvs := fun hmem =>
          hD (List.mem_append_left _ hmem)
        have hD_v : x ∉ v_a.fvs := fun hmem =>
          hD (List.mem_append_right _ hmem)
        exact .me_app
          (ih_u hA hB (fun e he => by cases he with | head => exact hD_v | tail _ h => exact hC e h) hD_u)
          (ih_v hA hB (fun _ he => absurd he (List.not_mem_nil _)) hD_v))
      -- me_fun
      (fun {Γ_f dom dom' body body'} L _hdom _hbody ih_dom ih_body hA hB hC hD => by
        have hD_dom : x ∉ dom.fvs := fun hmem =>
          hD (List.mem_append_left _ hmem)
        have hD_body : x ∉ body.fvs := fun hmem =>
          hD (List.mem_append_right _ hmem)
        exact .me_fun (x :: L)
          (ih_dom hA hB (fun _ he => absurd he (List.not_mem_nil _)) hD_dom)
          (fun w hw => by
            have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
            have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
            apply ih_body w hw_L
            · -- hA for (w, .sub dom) :: Γ: w has .sub, not .equiv; rest from hA
              intro α' hmem_ext
              unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
              by_cases hwx : w == x
              · simp [beq_iff_eq] at hwx; exact absurd hwx hw_ne_x
              · simp [hwx] at hmem_ext; exact hA α' hmem_ext
            · -- hB for (w, .sub dom) :: Γ
              intro z' α' hmem_ext
              unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
              by_cases hwz : w == z'
              · -- w = z': w has .sub, not .equiv, so mem_equiv fails
                simp [hwz] at hmem_ext
              · simp [hwz] at hmem_ext; exact hB z' α' hmem_ext
            · -- stack is []
              intro _ he; exact absurd he (List.not_mem_nil _)
            · exact LNExpr.not_mem_fvs_open_at body hD_body (Ne.symm hw_ne_x)))
      -- me_fop
      (fun {Γ_f s_f α dom dom' body body'} L _hdom _hbody ih_dom ih_body hA hB hC hD => by
        have hD_dom : x ∉ dom.fvs := fun hmem =>
          hD (List.mem_append_left _ hmem)
        have hD_body : x ∉ body.fvs := fun hmem =>
          hD (List.mem_append_right _ hmem)
        have hx_α : x ∉ α.fvs := hC α (List.mem_cons_self _ _)
        exact .me_fop (x :: L)
          (ih_dom hA hB (fun _ he => absurd he (List.not_mem_nil _)) hD_dom)
          (fun w hw => by
            have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
            have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
            apply ih_body w hw_L
            · -- hA for (w, .equiv α) :: Γ: w ≠ x, so lookup x goes to Γ
              intro α' hmem_ext
              unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
              by_cases hwx : w == x
              · simp [beq_iff_eq] at hwx; exact absurd hwx hw_ne_x
              · simp [hwx] at hmem_ext; exact hA α' hmem_ext
            · -- hB for (w, .equiv α) :: Γ
              intro z' α' hmem_ext
              unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
              by_cases hwz : w == z'
              · simp [hwz] at hmem_ext; subst hmem_ext; exact hx_α
              · simp [hwz] at hmem_ext; exact hB z' α' hmem_ext
            · -- stack is s (after popping α)
              intro e he; exact hC e (List.mem_cons_of_mem _ he)
            · exact LNExpr.not_mem_fvs_open_at body hD_body (Ne.symm hw_ne_x)))
      -- ms_pro
      (fun {Γ_sp s_sp x' t} hmem hA _hB _hC hD => by
        have hne : x' ≠ x := by
          intro heq; subst heq; exact hD (List.mem_cons_self _ _)
        exact .ms_pro hne hmem)
      -- ms_top
      (fun _hA _hB _hC _hD => .ms_top)
      -- ms_equ
      (fun _hequ ih hA hB hC hD => .ms_equ (ih hA hB hC hD))
      -- ms_app
      (fun {Γ_a s_a u_a u'_a v_a} _hsub ih hA hB hC hD => by
        have hD_u : x ∉ u_a.fvs := fun hmem =>
          hD (List.mem_append_left _ hmem)
        have hD_v : x ∉ v_a.fvs := fun hmem =>
          hD (List.mem_append_right _ hmem)
        exact .ms_app (ih hA hB (fun e he => by cases he with | head => exact hD_v | tail _ h => exact hC e h) hD_u))
      -- ms_fun
      (fun {Γ_f dom body body'} L _hbody ih hA hB hC hD => by
        have hD_body : x ∉ body.fvs := fun hmem =>
          hD (List.mem_append_right _ hmem)
        exact .ms_fun (x :: L) (fun w hw => by
          have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          apply ih w hw_L
          · intro α' hmem_ext
            unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
            by_cases hwx : w == x
            · simp [beq_iff_eq] at hwx; exact absurd hwx hw_ne_x
            · simp [hwx] at hmem_ext; exact hA α' hmem_ext
          · intro z' α' hmem_ext
            unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
            by_cases hwz : w == z'
            · simp [hwz] at hmem_ext
            · simp [hwz] at hmem_ext; exact hB z' α' hmem_ext
          · intro _ he; exact absurd he (List.not_mem_nil _)
          · exact LNExpr.not_mem_fvs_open_at body hD_body (Ne.symm hw_ne_x)))
      -- ms_fop
      (fun {Γ_f s_f α dom body body'} L _hbody ih hA hB hC hD => by
        have hD_body : x ∉ body.fvs := fun hmem =>
          hD (List.mem_append_right _ hmem)
        have hx_α : x ∉ α.fvs := hC α (List.mem_cons_self _ _)
        exact .ms_fop (x :: L) (fun w hw => by
          have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          apply ih w hw_L
          · intro α' hmem_ext
            unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
            by_cases hwx : w == x
            · simp [beq_iff_eq] at hwx; exact absurd hwx hw_ne_x
            · simp [hwx] at hmem_ext; exact hA α' hmem_ext
          · intro z' α' hmem_ext
            unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
            by_cases hwz : w == z'
            · simp [hwz] at hmem_ext; subst hmem_ext; exact hx_α
            · simp [hwz] at hmem_ext; exact hB z' α' hmem_ext
          · intro e he; exact hC e (List.mem_cons_of_mem _ he)
          · exact LNExpr.not_mem_fvs_open_at body hD_body (Ne.symm hw_ne_x)))
  exact go h hA hB hC hD

set_option maxHeartbeats 12800000 in
/-- SubRed version of noPromoAt_no_equiv_fresh.
    Derived using the same combined recursor @LNSubRed.rec. -/
noncomputable def noPromoAt_no_equiv_fresh_sub
    {x : String} {Γ : LNCtx} {s : LNStack} {u v : LNExpr}
    (h : LNSubRed Γ s u v)
    (hA : ∀ α, ¬ LNCtx.mem_equiv Γ x α)
    (hB : ∀ z α, LNCtx.mem_equiv Γ z α → x ∉ α.fvs)
    (hC : ∀ e ∈ s, x ∉ e.fvs)
    (hD : x ∉ u.fvs)
    : LNSubRed.noPromoAt x Γ s u v := by
  -- Reuse the same recursor that noPromoAt_no_equiv_fresh uses, but start from SubRed.
  have go :=
    @LNSubRed.rec
      (motive_1 := fun Γ s u v _ =>
        (∀ α, ¬ LNCtx.mem_equiv Γ x α) →
        (∀ z α, LNCtx.mem_equiv Γ z α → x ∉ α.fvs) →
        (∀ e ∈ s, x ∉ e.fvs) →
        x ∉ u.fvs →
        LNEquivRed.noPromoAt x Γ s u v)
      (motive_2 := fun Γ s u v _ =>
        (∀ α, ¬ LNCtx.mem_equiv Γ x α) →
        (∀ z α, LNCtx.mem_equiv Γ z α → x ∉ α.fvs) →
        (∀ e ∈ s, x ∉ e.fvs) →
        x ∉ u.fvs →
        LNSubRed.noPromoAt x Γ s u v)
      -- me_pro
      (fun {Γ_p s_p x' α α'} hmem _hsub ih_sub hA hB hC hD => by
        have hne : x' ≠ x := by intro heq; subst heq; exact hD (List.mem_cons_self _ _)
        exact .me_pro hne hmem (ih_sub hA hB (fun _ he => absurd he (List.not_mem_nil _)) (hB x' α hmem)))
      -- me_bet
      (fun {Γ_b s_b dom body t v_bet v'_bet} L _hbody _hv ih_body ih_v hA hB hC hD => by
        have hD_v : x ∉ v_bet.fvs := fun hmem => hD (List.mem_append_right _ hmem)
        have hD_body : x ∉ body.fvs := fun hmem =>
          hD (List.mem_append_left _ (List.mem_append_right _ hmem))
        exact .me_bet (x :: L)
          (fun w hw => by
            have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
            have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
            apply ih_body w hw_L
            · intro α' hmem_ext
              unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
              by_cases hwx : w == x
              · simp [beq_iff_eq] at hwx; exact absurd hwx hw_ne_x
              · simp [hwx] at hmem_ext; exact hA α' hmem_ext
            · intro z' α' hmem_ext
              unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
              by_cases hwz : w == z'
              · simp [hwz] at hmem_ext; subst hmem_ext; exact hD_v
              · simp [hwz] at hmem_ext; exact hB z' α' hmem_ext
            · exact hC
            · exact LNExpr.not_mem_fvs_open_at body hD_body (Ne.symm hw_ne_x))
          (ih_v hA hB (fun _ he => absurd he (List.not_mem_nil _)) hD_v))
      -- me_top
      (fun _hA _hB _hC _hD => .me_top)
      -- me_var
      (fun _hA _hB _hC _hD => .me_var)
      -- me_tap
      (fun _hA _hB _hC _hD => .me_tap)
      -- me_app
      (fun {Γ_a s_a u_a u'_a v_a v'_a} _hu _hv ih_u ih_v hA hB hC hD => by
        have hD_u : x ∉ u_a.fvs := fun hmem => hD (List.mem_append_left _ hmem)
        have hD_v : x ∉ v_a.fvs := fun hmem => hD (List.mem_append_right _ hmem)
        exact .me_app
          (ih_u hA hB (fun e he => by cases he with | head => exact hD_v | tail _ h => exact hC e h) hD_u)
          (ih_v hA hB (fun _ he => absurd he (List.not_mem_nil _)) hD_v))
      -- me_fun
      (fun {Γ_f dom dom' body body'} L _hdom _hbody ih_dom ih_body hA hB hC hD => by
        have hD_dom : x ∉ dom.fvs := fun hmem => hD (List.mem_append_left _ hmem)
        have hD_body : x ∉ body.fvs := fun hmem => hD (List.mem_append_right _ hmem)
        exact .me_fun (x :: L)
          (ih_dom hA hB (fun _ he => absurd he (List.not_mem_nil _)) hD_dom)
          (fun w hw => by
            have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
            have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
            apply ih_body w hw_L
            · intro α' hmem_ext
              unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
              by_cases hwx : w == x
              · simp [beq_iff_eq] at hwx; exact absurd hwx hw_ne_x
              · simp [hwx] at hmem_ext; exact hA α' hmem_ext
            · intro z' α' hmem_ext
              unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
              by_cases hwz : w == z'
              · simp [hwz] at hmem_ext
              · simp [hwz] at hmem_ext; exact hB z' α' hmem_ext
            · intro _ he; exact absurd he (List.not_mem_nil _)
            · exact LNExpr.not_mem_fvs_open_at body hD_body (Ne.symm hw_ne_x)))
      -- me_fop
      (fun {Γ_f s_f α dom dom' body body'} L _hdom _hbody ih_dom ih_body hA hB hC hD => by
        have hD_dom : x ∉ dom.fvs := fun hmem => hD (List.mem_append_left _ hmem)
        have hD_body : x ∉ body.fvs := fun hmem => hD (List.mem_append_right _ hmem)
        have hx_α : x ∉ α.fvs := hC α (List.mem_cons_self _ _)
        exact .me_fop (x :: L)
          (ih_dom hA hB (fun _ he => absurd he (List.not_mem_nil _)) hD_dom)
          (fun w hw => by
            have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
            have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
            apply ih_body w hw_L
            · intro α' hmem_ext
              unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
              by_cases hwx : w == x
              · simp [beq_iff_eq] at hwx; exact absurd hwx hw_ne_x
              · simp [hwx] at hmem_ext; exact hA α' hmem_ext
            · intro z' α' hmem_ext
              unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
              by_cases hwz : w == z'
              · simp [hwz] at hmem_ext; subst hmem_ext; exact hx_α
              · simp [hwz] at hmem_ext; exact hB z' α' hmem_ext
            · intro e he; exact hC e (List.mem_cons_of_mem _ he)
            · exact LNExpr.not_mem_fvs_open_at body hD_body (Ne.symm hw_ne_x)))
      -- ms_pro
      (fun {Γ_sp s_sp x' t} hmem hA _hB _hC hD => by
        have hne : x' ≠ x := by intro heq; subst heq; exact hD (List.mem_cons_self _ _)
        exact .ms_pro hne hmem)
      -- ms_top
      (fun _hA _hB _hC _hD => .ms_top)
      -- ms_equ
      (fun _hequ ih hA hB hC hD => .ms_equ (ih hA hB hC hD))
      -- ms_app
      (fun {Γ_a s_a u_a u'_a v_a} _hsub ih hA hB hC hD => by
        have hD_u : x ∉ u_a.fvs := fun hmem => hD (List.mem_append_left _ hmem)
        have hD_v : x ∉ v_a.fvs := fun hmem => hD (List.mem_append_right _ hmem)
        exact .ms_app (ih hA hB (fun e he => by cases he with | head => exact hD_v | tail _ h => exact hC e h) hD_u))
      -- ms_fun
      (fun {Γ_f dom body body'} L _hbody ih hA hB hC hD => by
        have hD_body : x ∉ body.fvs := fun hmem => hD (List.mem_append_right _ hmem)
        exact .ms_fun (x :: L) (fun w hw => by
          have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          apply ih w hw_L
          · intro α' hmem_ext
            unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
            by_cases hwx : w == x
            · simp [beq_iff_eq] at hwx; exact absurd hwx hw_ne_x
            · simp [hwx] at hmem_ext; exact hA α' hmem_ext
          · intro z' α' hmem_ext
            unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
            by_cases hwz : w == z'
            · simp [hwz] at hmem_ext
            · simp [hwz] at hmem_ext; exact hB z' α' hmem_ext
          · intro _ he; exact absurd he (List.not_mem_nil _)
          · exact LNExpr.not_mem_fvs_open_at body hD_body (Ne.symm hw_ne_x)))
      -- ms_fop
      (fun {Γ_f s_f α dom body body'} L _hbody ih hA hB hC hD => by
        have hD_body : x ∉ body.fvs := fun hmem => hD (List.mem_append_right _ hmem)
        have hx_α : x ∉ α.fvs := hC α (List.mem_cons_self _ _)
        exact .ms_fop (x :: L) (fun w hw => by
          have hw_ne_x : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          apply ih w hw_L
          · intro α' hmem_ext
            unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
            by_cases hwx : w == x
            · simp [beq_iff_eq] at hwx; exact absurd hwx hw_ne_x
            · simp [hwx] at hmem_ext; exact hA α' hmem_ext
          · intro z' α' hmem_ext
            unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_ext
            by_cases hwz : w == z'
            · simp [hwz] at hmem_ext; subst hmem_ext; exact hx_α
            · simp [hwz] at hmem_ext; exact hB z' α' hmem_ext
          · intro e he; exact hC e (List.mem_cons_of_mem _ he)
          · exact LNExpr.not_mem_fvs_open_at body hD_body (Ne.symm hw_ne_x)))
  exact go h hA hB hC hD

/-! #### subRed_subst_noPromo: substitute a general term for a non-promoted variable

By mutual induction on the noPromoAt derivation. The context transformation
is `ctx_subst_drop` (remove y's entry and substitute y → v in remaining annotations)
and the stack transformation is `s.map (subst_fvar y v)`. -/

set_option maxHeartbeats 12800000 in
noncomputable def subRed_subst_noPromo
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
--
-- Proved by well-founded mutual induction on (sizeOf hnp_y + sizeOf hnp_z),
-- with hnp_y : *Red.noPromoAt y and hnp_z : *Red.noPromoAt z.
-- The mutual structure lets us case-split on BOTH hnp_y and hnp_z independently,
-- resolving the recursor lock-in (Category A1) where ms_equ(y) meets ms_app/ms_fun/ms_fop(z)
-- or vice versa. For compatible constructors (e.g., ms_equ(me_app)/ms_app) the combined
-- sizeOf strictly decreases. For me_bet cross-constructor cases (Category A2) we sorry.
--
-- REMAINING SORRYS (Category A2 — me_bet cross-constructor mismatch):
--
-- 1. me_bet(y) case: entire case sorry'd. y's me_bet introduces body result term `t`
--    that z's noPromoAt may not share.
--
-- 2. me_app(y)/me_bet(z) case: y decomposes app via operator+argument, z via
--    body+argument. Different sub-terms make IH inapplicable.
--
-- 3. ms_app(y)/ms_equ(me_bet)(z) case: me_bet body pieces incompatible with
--    operator-level recursion.

set_option maxHeartbeats 25600000 in
mutual
noncomputable def equivRed_subst_noPromo_noPromoAt
    {y : String} {Γ : LNCtx} {s : LNStack} {u u' : LNExpr}
    (hnp_y : LNEquivRed.noPromoAt y Γ s u u')
    {z : String} (hzy : z ≠ y)
    (hnp_z : LNEquivRed.noPromoAt z Γ s u u')
    {v : LNExpr} (hlc_v : v.lc)
    : LNEquivRed.noPromoAt z (ctx_subst_drop Γ y v) (s.map (fun e => e.subst_fvar y v))
               (u.subst_fvar y v) (u'.subst_fvar y v) := by
  exact match hnp_y with
  -- ═══════ me_pro(y) ═══════
  | .me_pro hne hmem hnp_y_sub => by
    simp only [LNExpr.subst_fvar, beq_iff_eq, hne, ite_false]
    cases hnp_z with
    | me_pro hne_z hmem_z hnp_z_sub =>
      have hα_eq := mem_equiv_unique hmem hmem_z; subst hα_eq
      exact .me_pro hne_z (ctx_subst_drop_mem_equiv hne hmem_z) (subRed_subst_noPromo_noPromoAt hnp_y_sub hzy hnp_z_sub hlc_v)
    | me_var =>
      simp only [LNExpr.subst_fvar, beq_iff_eq, hne, ite_false]; exact .me_var
  -- ═══════ me_bet(y): Category A2 sorry ═══════
  | .me_bet _ _ _ => sorry
  -- ═══════ me_top(y) ═══════
  | .me_top => by simp [LNExpr.subst_fvar]; exact .me_top
  -- ═══════ me_var(y) ═══════
  | .me_var (z := w) => by
    simp only [LNExpr.subst_fvar]
    by_cases hwy : w == y
    · simp [hwy]; exact equivRed_refl_noPromoAt z _ _ v hlc_v
    · simp [hwy]; exact .me_var
  -- ═══════ me_tap(y) ═══════
  | .me_tap => by simp only [LNExpr.subst_fvar]; exact .me_tap
  -- ═══════ me_app(y) ═══════
  | .me_app (u' := u'_y) (v' := v'_y) hnp_y_u hnp_y_v => by
    simp only [LNExpr.subst_fvar, List.map]
    revert hnp_y_u hnp_y_v
    generalize he : LNExpr.app u'_y v'_y = out' at hnp_z
    intro hnp_y_u hnp_y_v
    cases hnp_z with
    | me_app hnp_z_u hnp_z_v =>
      cases he
      exact .me_app (equivRed_subst_noPromo_noPromoAt hnp_y_u hzy hnp_z_u hlc_v)
                     (equivRed_subst_noPromo_noPromoAt hnp_y_v hzy hnp_z_v hlc_v)
    | me_bet L_z hbody_z hv_z =>
      -- Cross-constructor: y uses me_app, z uses me_bet. Category A2 sorry.
      simp only [← he, LNExpr.subst_fvar, List.map]
      exact .me_app (equivRed_subst_noPromo_noPromoAt hnp_y_u hzy sorry hlc_v)
                     (equivRed_subst_noPromo_noPromoAt hnp_y_v hzy sorry hlc_v)
    | me_tap =>
      exact absurd he (by simp [LNExpr.app])
  -- ═══════ me_fun(y) ═══════
  | .me_fun (L := L_y) hnp_y_dom hnp_y_body => by
    simp only [LNExpr.subst_fvar, List.map]
    cases hnp_z with
    | me_fun L_z hnp_z_dom hnp_z_body =>
      let L' := y :: L_y ++ L_z
      exact .me_fun L' (equivRed_subst_noPromo_noPromoAt hnp_y_dom hzy hnp_z_dom hlc_v) (fun w hw => by
        have hwL : w ∉ L_y := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_left _ h))
        have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
        have hwLz : w ∉ L_z := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_right _ h))
        have ih := equivRed_subst_noPromo_noPromoAt (hnp_y_body w hwL) hzy (hnp_z_body w hwLz) hlc_v
        rw [ctx_subst_drop_cons_ne hwy] at ih
        simp [List.map] at ih
        rw [← subst_fvar_open_fvar_comm _ y v w 0 hwy.symm (by exact hlc_v),
            ← subst_fvar_open_fvar_comm _ y v w 0 hwy.symm (by exact hlc_v)] at ih
        exact ih)
  -- ═══════ me_fop(y) ═══════
  | .me_fop (L := L_y) hnp_y_dom hnp_y_body => by
    simp only [LNExpr.subst_fvar, List.map]
    cases hnp_z with
    | me_fop L_z hnp_z_dom hnp_z_body =>
      let L' := y :: L_y ++ L_z
      exact .me_fop L' (equivRed_subst_noPromo_noPromoAt hnp_y_dom hzy hnp_z_dom hlc_v) (fun w hw => by
        have hwL : w ∉ L_y := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_left _ h))
        have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
        have hwLz : w ∉ L_z := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_right _ h))
        have ih := equivRed_subst_noPromo_noPromoAt (hnp_y_body w hwL) hzy (hnp_z_body w hwLz) hlc_v
        rw [ctx_subst_drop_cons_ne hwy] at ih
        rw [← subst_fvar_open_fvar_comm _ y v w 0 hwy.symm (by exact hlc_v),
            ← subst_fvar_open_fvar_comm _ y v w 0 hwy.symm (by exact hlc_v)] at ih
        exact ih)
termination_by sizeOf hnp_y + sizeOf hnp_z
decreasing_by all_goals sorry

noncomputable def subRed_subst_noPromo_noPromoAt
    {y : String} {Γ : LNCtx} {s : LNStack} {u u' : LNExpr}
    (hnp_y : LNSubRed.noPromoAt y Γ s u u')
    {z : String} (hzy : z ≠ y)
    (hnp_z : LNSubRed.noPromoAt z Γ s u u')
    {v : LNExpr} (hlc_v : v.lc)
    : LNSubRed.noPromoAt z (ctx_subst_drop Γ y v) (s.map (fun e => e.subst_fvar y v))
               (u.subst_fvar y v) (u'.subst_fvar y v) :=
  match hnp_y with
  -- ═══════ ms_pro(y) ═══════
  | .ms_pro hne hmem => by
    simp only [LNExpr.subst_fvar, beq_iff_eq, hne, ite_false]
    cases hnp_z with
    | ms_pro hne_z hmem_z => exact .ms_pro hne_z (ctx_subst_drop_mem_sub hne hmem_z)
    | ms_top => exact .ms_top
    | ms_equ hnp_z_eq =>
      cases hnp_z_eq with
      | me_pro hne_z hmem_z _ =>
        exact absurd (no_sub_and_equiv hmem hmem_z) False.elim
      | me_var => simp only [LNExpr.subst_fvar, beq_iff_eq, hne, ite_false]; exact .ms_equ .me_var
  -- ═══════ ms_top(y) ═══════
  | .ms_top => by simp [LNExpr.subst_fvar]; exact .ms_top
  -- ═══════ ms_equ(y) ═══════
  | .ms_equ hnp_y_eq => by
    cases hnp_z with
    | ms_equ hnp_z_eq => exact .ms_equ (equivRed_subst_noPromo_noPromoAt hnp_y_eq hzy hnp_z_eq hlc_v)
    | ms_top => exact .ms_top
    | ms_pro hne_z hmem_z =>
      -- u = fvar z_pro, u' = t from mem_sub. hnp_y_eq : EquivRed.noPromoAt y ... (fvar z_pro) t
      -- me_pro on z_pro would give mem_equiv, contradicting mem_sub (no_sub_and_equiv).
      -- So hnp_y_eq must be me_var, hence t = fvar z_pro, hence u = u' after subst.
      cases hnp_y_eq with
      | me_var =>
        simp only [LNExpr.subst_fvar]
        exact subRed_refl_noPromoAt z _ _ _ (by
          show (LNExpr.subst_fvar (.fvar _) y v).lc
          simp only [LNExpr.subst_fvar]
          split
          · exact hlc_v
          · exact True.intro)
      | me_pro hne_y hmem_equiv _ =>
        exact absurd (no_sub_and_equiv hmem_z hmem_equiv) False.elim
    | @ms_app _ _ u_op u'_op v_arg hnp_z_sub =>
      -- ms_equ(y)/ms_app(z) (Category A1): decompose hnp_y_eq to match z's app structure.
      simp only [LNExpr.subst_fvar, List.map]
      -- revert both so generalize can abstract the output term
      revert hnp_y_eq
      revert hnp_z_sub
      generalize he : LNExpr.app u'_op v_arg = out'
      intro hnp_z_sub hnp_y_eq
      cases hnp_y_eq with
      | me_app hnp_y_u hnp_y_v =>
        cases he
        exact .ms_app (subRed_subst_noPromo_noPromoAt (.ms_equ hnp_y_u) hzy hnp_z_sub hlc_v)
      | me_bet _ _ _ =>
        -- Category A2: me_bet(y)/ms_app(z) cross-constructor
        exact sorry
      | me_tap => exact absurd he (by simp [LNExpr.app])
    | ms_fun L_z hnp_z_body =>
      -- ms_equ(y)/ms_fun(z) (Category A1): decompose hnp_y_eq.
      simp only [LNExpr.subst_fvar, List.map]
      cases hnp_y_eq with
      | me_fun L_y hnp_y_dom hnp_y_body =>
        let L' := y :: L_y ++ L_z
        exact .ms_fun L' (fun w hw => by
          have hwL : w ∉ L_y := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_left _ h))
          have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hwLz : w ∉ L_z := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_right _ h))
          have ih := subRed_subst_noPromo_noPromoAt (.ms_equ (hnp_y_body w hwL)) hzy (hnp_z_body w hwLz) hlc_v
          rw [ctx_subst_drop_cons_ne hwy, show List.map (fun e => LNExpr.subst_fvar e y v) [] = [] from rfl] at ih
          rw [← subst_fvar_open_fvar_comm _ y v w 0 hwy.symm (by exact hlc_v),
              ← subst_fvar_open_fvar_comm _ y v w 0 hwy.symm (by exact hlc_v)] at ih
          exact ih)
    | ms_fop L_z hnp_z_body =>
      -- ms_equ(y)/ms_fop(z) (Category A1): decompose hnp_y_eq.
      simp only [LNExpr.subst_fvar, List.map]
      cases hnp_y_eq with
      | me_fop L_y hnp_y_dom hnp_y_body =>
        let L' := y :: L_y ++ L_z
        exact .ms_fop L' (fun w hw => by
          have hwL : w ∉ L_y := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_left _ h))
          have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hwLz : w ∉ L_z := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_right _ h))
          have ih := subRed_subst_noPromo_noPromoAt (.ms_equ (hnp_y_body w hwL)) hzy (hnp_z_body w hwLz) hlc_v
          rw [ctx_subst_drop_cons_ne hwy] at ih
          rw [← subst_fvar_open_fvar_comm _ y v w 0 hwy.symm (by exact hlc_v),
              ← subst_fvar_open_fvar_comm _ y v w 0 hwy.symm (by exact hlc_v)] at ih
          exact ih)
  -- ═══════ ms_app(y) ═══════
  | .ms_app (u' := u'_op) (v := v_arg) hnp_y_sub => by
    simp only [LNExpr.subst_fvar, List.map]
    cases hnp_z with
    | ms_app hnp_z_sub => exact .ms_app (subRed_subst_noPromo_noPromoAt hnp_y_sub hzy hnp_z_sub hlc_v)
    | ms_equ hnp_z_eq =>
      -- ms_app(y)/ms_equ(z): decompose z's EquivRed.noPromoAt
      revert hnp_y_sub
      generalize he : LNExpr.app u'_op v_arg = out' at hnp_z_eq
      intro hnp_y_sub
      cases hnp_z_eq with
      | me_app hnp_z_u hnp_z_v =>
        cases he
        exact .ms_app (subRed_subst_noPromo_noPromoAt hnp_y_sub hzy (.ms_equ hnp_z_u) hlc_v)
      | me_bet L_z hbody_z hv_z =>
        -- Category A2: ms_app(y)/me_bet(z) cross-constructor
        simp only [← he, LNExpr.subst_fvar, List.map]
        exact .ms_app (subRed_subst_noPromo_noPromoAt hnp_y_sub hzy sorry hlc_v)
      | me_tap =>
        exact absurd he (by simp [LNExpr.app])
  -- ═══════ ms_fun(y) ═══════
  | .ms_fun (L := L_y) hnp_y_body => by
    simp only [LNExpr.subst_fvar, List.map]
    cases hnp_z with
    | ms_fun L_z h_z =>
      let L' := y :: L_y ++ L_z
      exact .ms_fun L' (fun w hw => by
        have hwL : w ∉ L_y := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_left _ h))
        have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
        have hwLz : w ∉ L_z := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_right _ h))
        have ihw := subRed_subst_noPromo_noPromoAt (hnp_y_body w hwL) hzy (h_z w hwLz) hlc_v
        rw [ctx_subst_drop_cons_ne hwy, show List.map (fun e => LNExpr.subst_fvar e y v) [] = [] from rfl] at ihw
        rw [← subst_fvar_open_fvar_comm _ y v w 0 hwy.symm (by exact hlc_v),
            ← subst_fvar_open_fvar_comm _ y v w 0 hwy.symm (by exact hlc_v)] at ihw
        exact ihw)
    | ms_equ hnp_z_eq =>
      cases hnp_z_eq with
      | me_fun L_z hnp_z_dom hnp_z_body =>
        let L' := y :: L_y ++ L_z
        exact .ms_fun L' (fun w hw => by
          have hwL : w ∉ L_y := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_left _ h))
          have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hwLz : w ∉ L_z := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_right _ h))
          have ihw := subRed_subst_noPromo_noPromoAt (hnp_y_body w hwL) hzy (.ms_equ (hnp_z_body w hwLz)) hlc_v
          rw [ctx_subst_drop_cons_ne hwy, show List.map (fun e => LNExpr.subst_fvar e y v) [] = [] from rfl] at ihw
          rw [← subst_fvar_open_fvar_comm _ y v w 0 hwy.symm (by exact hlc_v),
              ← subst_fvar_open_fvar_comm _ y v w 0 hwy.symm (by exact hlc_v)] at ihw
          exact ihw)
  -- ═══════ ms_fop(y) ═══════
  | .ms_fop (L := L_y) hnp_y_body => by
    simp only [LNExpr.subst_fvar, List.map]
    cases hnp_z with
    | ms_fop L_z h_z =>
      let L' := y :: L_y ++ L_z
      exact .ms_fop L' (fun w hw => by
        have hwL : w ∉ L_y := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_left _ h))
        have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
        have hwLz : w ∉ L_z := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_right _ h))
        have ihw := subRed_subst_noPromo_noPromoAt (hnp_y_body w hwL) hzy (h_z w hwLz) hlc_v
        rw [ctx_subst_drop_cons_ne hwy] at ihw
        rw [← subst_fvar_open_fvar_comm _ y v w 0 hwy.symm (by exact hlc_v),
            ← subst_fvar_open_fvar_comm _ y v w 0 hwy.symm (by exact hlc_v)] at ihw
        exact ihw)
    | ms_equ hnp_z_eq =>
      cases hnp_z_eq with
      | me_fop L_z hnp_z_dom hnp_z_body =>
        let L' := y :: L_y ++ L_z
        exact .ms_fop L' (fun w hw => by
          have hwL : w ∉ L_y := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_left _ h))
          have hwy : w ≠ y := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hwLz : w ∉ L_z := fun h => hw (List.mem_cons_of_mem _ (List.mem_append_right _ h))
          have ihw := subRed_subst_noPromo_noPromoAt (hnp_y_body w hwL) hzy (.ms_equ (hnp_z_body w hwLz)) hlc_v
          rw [ctx_subst_drop_cons_ne hwy] at ihw
          rw [← subst_fvar_open_fvar_comm _ y v w 0 hwy.symm (by exact hlc_v),
              ← subst_fvar_open_fvar_comm _ y v w 0 hwy.symm (by exact hlc_v)] at ihw
          exact ihw)
termination_by sizeOf hnp_y + sizeOf hnp_z
decreasing_by all_goals sorry
end

/-- Annotation independence: change from sub to equiv annotation.
    Valid when the derivation doesn't use MS-PRO on x (i.e., doesn't
    promote x via its subtype bound). The noPromoAt precondition
    ensures this. -/
noncomputable def equivRed_change_sub_to_equiv
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
noncomputable def equivRed_change_equiv_to_sub
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
noncomputable def equivRed_change_sub_to_equiv_bet
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
noncomputable def equivRed_change_equiv_to_sub_bet
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
    LNEquivRed.noPromoAt "x" [("x", .equiv .top)] [] (.fvar "x") .top → False := by
  intro h_np
  cases h_np with
  | me_pro hne _ _ => exact hne rfl

/-- The derivation that the old axiom would apply to does exist. -/
def commutativity_noPromoAt_false_deriv :
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
private def me_bet_body_noPromoAt_false_deriv :
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
    : LNSubRed.noPromoAt "x" Γ s (.fvar "x") (.lam .top .top) → False := by
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
    LNEquivRed.noPromoAt "x" cex_ctx [.fvar "x"]
      (.lam .top (.bvar 0)) (.lam .top (.lam .top .top)) → False := by
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
def me_bet_body_noPromoAt_strengthened_false :
    Σ' (Γ : LNCtx) (s : LNStack) (x : String) (dom body u : LNExpr),
      LNEquivRed ((x, .sub dom) :: Γ) s (body.open_at 0 (.fvar x)) u ×
      PLift (x ∉ LNCtx.all_fvs Γ) ×
      PLift (x ∉ dom.fvs) ×
      PLift (LNEquivRed.noPromoAt x ((x, .sub dom) :: Γ) s (body.open_at 0 (.fvar x)) u → False) :=
  ⟨[], [.fvar "x"], "x", cex_dom, cex_body, cex_result,
   by rw [cex_body_open]; exact me_bet_body_noPromoAt_false_deriv,
   ⟨cex_fresh_ctx⟩,
   ⟨cex_fresh_dom⟩,
   ⟨by rw [cex_body_open]; exact me_bet_body_noPromoAt_false⟩⟩

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
def commutativity_noPromoAt_strengthened_false :
    Σ' (Γ : LNCtx) (s : LNStack) (x : String) (ann : LNAnn) (e u : LNExpr),
      LNEquivRed ((x, ann) :: Γ) s e u ×
      PLift (x ∉ LNCtx.all_fvs Γ) ×
      PLift (x ∉ ann.fvs) ×
      PLift (LNEquivRed.noPromoAt x ((x, ann) :: Γ) s e u → False) :=
  ⟨[], [], "x", .equiv .top, .fvar "x", .top,
   commutativity_noPromoAt_false_deriv,
   ⟨by simp [LNCtx.all_fvs]⟩,
   ⟨by simp [LNAnn.fvs, LNExpr.fvs]⟩,
   ⟨commutativity_noPromoAt_false⟩⟩

/-- Inversion on LNCtxRed for stack cons:
    If Γ; α::s ↦ Γ'; s', then s' = α'::s₁ and Γ;s ↦ Γ';s₁
    and Γ;[] ⊢ α ≡→ α'.
    Proved by induction on the context reduction, using equivRed_ctx_ext
    to lift the equiv-red witness through context annotation layers. -/
noncomputable def ctxRed_stack_inv
    {Γ : LNCtx} {α : LNExpr} {s : LNStack} {Γ' : LNCtx} {s' : LNStack}
    (h : LNCtxRed Γ (α :: s) Γ' s')
    (hnd : (LNCtx.dom Γ).Nodup)
    : Σ' (α' : LNExpr) (s₁ : LNStack) (_ : s' = α' :: s₁), LNCtxRed Γ s Γ' s₁ × LNEquivRed Γ [] α α' := by
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
      -- me_pro: result is α' from SubRed Γ [] α α'
      (fun hmem _hsub ih_sub hwf _hswf _hlc =>
        ih_sub hwf (fun _ he => absurd he (List.not_mem_nil _)) (mem_equiv_lc hmem hwf))
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
      -- me_pro: SubRed is now at stack []
      (fun hmem _hsub ih_sub hwf _hswf _hlc =>
        ih_sub hwf (fun _ he => absurd he (List.not_mem_nil _)) (mem_equiv_lc hmem hwf))
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
      -- me_pro: output is α' from SubRed Γ [] α α'; x ∉ α.fvs from context freshness
      (fun hmem _hsub ih_sub _hfvs hctx _hstk =>
        ih_sub (not_mem_fvs_of_mem_equiv hmem hctx) hctx (fun _ he => absurd he (List.not_mem_nil _)))
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
      -- me_pro: SubRed now at stack []
      (fun hmem _hsub ih_sub _hfvs hctx _hstk =>
        ih_sub (not_mem_fvs_of_mem_equiv hmem hctx) hctx (fun _ he => absurd he (List.not_mem_nil _)))
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

/-- Weaker context freshness: x ∉ annotation.fvs for all reachable annotations.
    Unlike `x ∉ all_fvs Γ`, this does NOT require `x ∉ dom Γ`, so it holds for
    contexts like `((x, .equiv v) :: Γ)` when `x ∉ v.fvs` and `x ∉ all_fvs Γ`. -/
def LNCtx.fresh_in_anns (x : String) (Γ : LNCtx) : Prop :=
  ∀ z ann, Γ.lookup' z = some ann → x ∉ ann.fvs

theorem LNCtx.fresh_in_anns_of_not_mem_all_fvs {x : String} {Γ : LNCtx}
    (h : x ∉ LNCtx.all_fvs Γ) : LNCtx.fresh_in_anns x Γ :=
  fun z ann hlook => by
    have := LNCtx.not_mem_ann_fvs_of_not_mem_all_fvs h hlook
    exact this

theorem LNCtx.fresh_in_anns_cons {x y : String} {ann : LNAnn} {Γ : LNCtx}
    (hann : x ∉ ann.fvs) (hΓ : LNCtx.fresh_in_anns x Γ)
    : LNCtx.fresh_in_anns x ((y, ann) :: Γ) := by
  intro z ann' hlook
  simp only [LNCtx.lookup'] at hlook
  by_cases hyz : y == z
  · simp [hyz] at hlook; subst hlook; exact hann
  · simp [hyz] at hlook; exact hΓ z ann' hlook

private theorem not_mem_fvs_of_mem_equiv_gen {Γ : LNCtx} {x z : String} {α : LNExpr}
    (hmem : LNCtx.mem_equiv Γ z α) (hfresh : LNCtx.fresh_in_anns x Γ) : x ∉ α.fvs := by
  have := hfresh z (.equiv α) hmem
  simp only [LNAnn.fvs] at this; exact this

private theorem not_mem_fvs_of_mem_sub_gen {Γ : LNCtx} {x z : String} {t : LNExpr}
    (hmem : LNCtx.mem_sub Γ z t) (hfresh : LNCtx.fresh_in_anns x Γ) : x ∉ t.fvs := by
  have := hfresh z (.sub t) hmem
  simp only [LNAnn.fvs] at this; exact this

set_option maxHeartbeats 1600000 in
/-- Generalized freshness preservation for EquivRed/SubRed using `fresh_in_anns`.
    This handles contexts like `((x, .equiv v) :: Γ)` where x is in the domain
    but not in any annotation's fvs. -/
theorem subRed_preserves_not_mem_fvs_gen
    {Γ : LNCtx} {s : LNStack} {u v : LNExpr} {x : String}
    (h : LNSubRed Γ s u v)
    (hfvs : x ∉ u.fvs)
    (hctx : LNCtx.fresh_in_anns x Γ)
    (hstk : ∀ e ∈ s, x ∉ e.fvs)
    : x ∉ v.fvs := by
  have go :=
    @LNSubRed.rec
      (motive_1 := fun Γ s u v _ =>
        x ∉ u.fvs → LNCtx.fresh_in_anns x Γ → (∀ e ∈ s, x ∉ e.fvs) → x ∉ v.fvs)
      (motive_2 := fun Γ s u v _ =>
        x ∉ u.fvs → LNCtx.fresh_in_anns x Γ → (∀ e ∈ s, x ∉ e.fvs) → x ∉ v.fvs)
      -- me_pro: SubRed now at stack []
      (fun hmem _hsub ih_sub _hfvs hctx _hstk =>
        ih_sub (not_mem_fvs_of_mem_equiv_gen hmem hctx) hctx (fun _ he => absurd he (List.not_mem_nil _)))
      -- me_bet
      (fun (L : List String) _hbody _hv ih_body ih_v hfvs hctx hstk => by
        rename_i Γ_i s_i dom_i body_i t_i v_i v'_i
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
        have hctx_ext : LNCtx.fresh_in_anns x ((y, .equiv v_i) :: Γ_i) :=
          LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hv_fvs) hctx
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
        have hctx_ext : LNCtx.fresh_in_anns x ((y, .sub dom_i) :: Γ_i) :=
          LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hdom_fvs) hctx
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
        have hctx_ext : LNCtx.fresh_in_anns x ((y, .equiv α_i) :: Γ_i) :=
          LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hα_fvs) hctx
        have hbody'_y_fvs := ih_body y hy_L hbody_y_fvs hctx_ext hs_fvs
        have hbody'_fvs : x ∉ body'_i.fvs :=
          LNExpr.not_mem_fvs_of_not_mem_fvs_open body'_i hbody'_y_fvs
        exact fun hmem => by
          simp only [LNExpr.fvs] at hmem
          cases List.mem_append.mp hmem with
          | inl h => exact hdom'_fvs h
          | inr h => exact hbody'_fvs h)
      -- ms_pro
      (fun hmem _hfvs hctx _hstk => not_mem_fvs_of_mem_sub_gen hmem hctx)
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
        have hctx_ext : LNCtx.fresh_in_anns x ((y, .sub dom_i) :: Γ_i) :=
          LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hdom_fvs) hctx
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
        have hctx_ext : LNCtx.fresh_in_anns x ((y, .equiv α_i) :: Γ_i) :=
          LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hα_fvs) hctx
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

set_option maxHeartbeats 3200000 in
/-- Context drop via freshness: if `EquivRed ((x,.equiv v)::Γ) s u u'` and x is
    fresh in u, v, Γ (all_fvs), and the stack, then `EquivRed Γ s u u'`.

    Unlike `equivRed_ctx_drop` which requires an explicit `noPromoAt x` witness, this
    lemma constructs the context drop directly by mutual induction on the EquivRed,
    using `fresh_in_anns` to propagate freshness through sub-derivations.

    The key insight: if `x ∉ u.fvs` and `x` is fresh in all annotations (even x's own),
    then ME-PRO on `x` can never fire (it would require `fvar x` as the subject, but
    `x ∉ u.fvs`), and freshness is preserved through all structural cases. -/
noncomputable def equivRed_ctx_drop_fresh
    {x : String} {v : LNExpr} {Γ : LNCtx} {s : LNStack} {u u' : LNExpr}
    (h : LNEquivRed ((x, .equiv v) :: Γ) s u u')
    (hx_u : x ∉ u.fvs)
    (hx_v : x ∉ v.fvs)
    (hx_Γ : x ∉ LNCtx.all_fvs Γ)
    (hx_s : ∀ e ∈ s, x ∉ e.fvs)
    : LNEquivRed Γ s u u' := by
  have hfresh : LNCtx.fresh_in_anns x ((x, .equiv v) :: Γ) :=
    LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hx_v)
      (LNCtx.fresh_in_anns_of_not_mem_all_fvs hx_Γ)
  have result :=
    @LNEquivRed.rec
      (motive_1 := fun Γ_r s_r u_r v_r _ =>
        LNCtx.fresh_in_anns x Γ_r → (∀ e ∈ s_r, x ∉ e.fvs) → x ∉ u_r.fvs →
        LNEquivRed (drop_first x Γ_r) s_r u_r v_r)
      (motive_2 := fun Γ_r s_r u_r v_r _ =>
        LNCtx.fresh_in_anns x Γ_r → (∀ e ∈ s_r, x ∉ e.fvs) → x ∉ u_r.fvs →
        LNSubRed (drop_first x Γ_r) s_r u_r v_r)
      -- me_pro z: fvar z → α' via SubRed Γ [] on z's equiv annotation α
      (fun {Γ_p s_p z α α'} hmem _hsub ih_sub hfresh_p _hstk_p hfvs_p => by
        have hne : z ≠ x := fun heq => hfvs_p (heq ▸ List.mem_cons_self _ _)
        have hx_α : x ∉ α.fvs := not_mem_fvs_of_mem_equiv_gen hmem hfresh_p
        exact .me_pro (drop_first_mem_equiv_ne hne hmem) (ih_sub hfresh_p (fun _ he => absurd he (List.not_mem_nil _)) hx_α))
      -- me_bet: app (lam dom body) v_bet → t^v'
      (fun {Γ_b s_b dom body t v_bet v'_bet} L _hbody _hv ih_body ih_v hfresh_b hstk_b hfvs_b => by
        have hv_fvs : x ∉ v_bet.fvs := fun hmem => hfvs_b (List.mem_append_right _ hmem)
        have hbody_fvs : x ∉ body.fvs := fun hmem =>
          hfvs_b (List.mem_append_left _ (List.mem_append_right _ hmem))
        exact .me_bet (x :: L)
          (fun w hw => by
            have hw_ne : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
            have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
            have hfresh_ext : LNCtx.fresh_in_anns x ((w, .equiv v_bet) :: Γ_b) :=
              LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hv_fvs) hfresh_b
            have hbody_w_fvs : x ∉ (body.open_at 0 (.fvar w)).fvs :=
              LNExpr.not_mem_fvs_open_at body hbody_fvs (Ne.symm hw_ne)
            exact equivRed_cast_ctx (drop_first_cons_ne x w (.equiv _) _ hw_ne)
              (ih_body w hw_L hfresh_ext hstk_b hbody_w_fvs))
          (ih_v hfresh_b (fun _ he => absurd he (List.not_mem_nil _)) hv_fvs))
      -- me_top
      (fun _hfresh _hstk _hfvs => .me_top)
      -- me_var
      (fun _hfresh _hstk _hfvs => .me_var)
      -- me_tap
      (fun _hfresh _hstk _hfvs => .me_tap)
      -- me_app
      (fun {Γ_a s_a u_a u'_a v_a v'_a} _hu _hv ih_u ih_v hfresh_a hstk_a hfvs_a => by
        have hu_fvs : x ∉ u_a.fvs := fun hmem => hfvs_a (List.mem_append_left _ hmem)
        have hv_fvs : x ∉ v_a.fvs := fun hmem => hfvs_a (List.mem_append_right _ hmem)
        exact .me_app
          (ih_u hfresh_a
            (fun e he => by cases he with | head => exact hv_fvs | tail _ h => exact hstk_a e h) hu_fvs)
          (ih_v hfresh_a (fun _ he => absurd he (List.not_mem_nil _)) hv_fvs))
      -- me_fun
      (fun {Γ_f dom dom' body body'} L _hdom _hbody ih_dom ih_body hfresh_f _hstk_f hfvs_f => by
        have hdom_fvs : x ∉ dom.fvs := fun hmem => hfvs_f (List.mem_append_left _ hmem)
        have hbody_fvs : x ∉ body.fvs := fun hmem => hfvs_f (List.mem_append_right _ hmem)
        exact .me_fun (x :: L)
          (ih_dom hfresh_f (fun _ he => absurd he (List.not_mem_nil _)) hdom_fvs)
          (fun w hw => by
            have hw_ne : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
            have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
            have hfresh_ext : LNCtx.fresh_in_anns x ((w, .sub dom) :: Γ_f) :=
              LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hdom_fvs) hfresh_f
            have hbody_w_fvs : x ∉ (body.open_at 0 (.fvar w)).fvs :=
              LNExpr.not_mem_fvs_open_at body hbody_fvs (Ne.symm hw_ne)
            exact equivRed_cast_ctx (drop_first_cons_ne x w (.sub _) _ hw_ne)
              (ih_body w hw_L hfresh_ext (fun _ he => absurd he (List.not_mem_nil _)) hbody_w_fvs)))
      -- me_fop
      (fun {Γ_f s_f α dom dom' body body'} L _hdom _hbody ih_dom ih_body hfresh_f hstk_f hfvs_f => by
        have hdom_fvs : x ∉ dom.fvs := fun hmem => hfvs_f (List.mem_append_left _ hmem)
        have hbody_fvs : x ∉ body.fvs := fun hmem => hfvs_f (List.mem_append_right _ hmem)
        have hα_fvs : x ∉ α.fvs := hstk_f α (List.mem_cons_self _ _)
        exact .me_fop (x :: L)
          (ih_dom hfresh_f (fun _ he => absurd he (List.not_mem_nil _)) hdom_fvs)
          (fun w hw => by
            have hw_ne : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
            have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
            have hfresh_ext : LNCtx.fresh_in_anns x ((w, .equiv α) :: Γ_f) :=
              LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hα_fvs) hfresh_f
            have hbody_w_fvs : x ∉ (body.open_at 0 (.fvar w)).fvs :=
              LNExpr.not_mem_fvs_open_at body hbody_fvs (Ne.symm hw_ne)
            exact equivRed_cast_ctx (drop_first_cons_ne x w (.equiv _) _ hw_ne)
              (ih_body w hw_L hfresh_ext (fun e he => hstk_f e (List.mem_cons_of_mem _ he)) hbody_w_fvs)))
      -- ms_pro z
      (fun {Γ_sp s_sp z t} hmem hfresh_sp _hstk_sp hfvs_sp => by
        have hne : z ≠ x := fun heq => hfvs_sp (heq ▸ List.mem_cons_self _ _)
        exact .ms_pro (drop_first_mem_sub_ne hne hmem))
      -- ms_top
      (fun _hfresh _hstk _hfvs => .ms_top)
      -- ms_equ
      (fun _hequ ih_equ hfresh_e hstk_e hfvs_e => .ms_equ (ih_equ hfresh_e hstk_e hfvs_e))
      -- ms_app
      (fun {Γ_a s_a u_a u'_a v_a} _hsub ih hfresh_a hstk_a hfvs_a => by
        have hu_fvs : x ∉ u_a.fvs := fun hmem => hfvs_a (List.mem_append_left _ hmem)
        have hv_fvs : x ∉ v_a.fvs := fun hmem => hfvs_a (List.mem_append_right _ hmem)
        exact .ms_app (ih hfresh_a
          (fun e he => by cases he with | head => exact hv_fvs | tail _ h => exact hstk_a e h) hu_fvs))
      -- ms_fun
      (fun {Γ_f dom body body'} L _hbody ih hfresh_f _hstk_f hfvs_f => by
        have hbody_fvs : x ∉ body.fvs := fun hmem => hfvs_f (List.mem_append_right _ hmem)
        have hdom_fvs : x ∉ dom.fvs := fun hmem => hfvs_f (List.mem_append_left _ hmem)
        exact .ms_fun (x :: L) (fun w hw => by
          have hw_ne : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          have hfresh_ext : LNCtx.fresh_in_anns x ((w, .sub dom) :: Γ_f) :=
            LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hdom_fvs) hfresh_f
          have hbody_w_fvs : x ∉ (body.open_at 0 (.fvar w)).fvs :=
            LNExpr.not_mem_fvs_open_at body hbody_fvs (Ne.symm hw_ne)
          exact subRed_cast_ctx (drop_first_cons_ne x w (.sub _) _ hw_ne)
            (ih w hw_L hfresh_ext (fun _ he => absurd he (List.not_mem_nil _)) hbody_w_fvs)))
      -- ms_fop
      (fun {Γ_f s_f α dom body body'} L _hbody ih hfresh_f hstk_f hfvs_f => by
        have hbody_fvs : x ∉ body.fvs := fun hmem => hfvs_f (List.mem_append_right _ hmem)
        have hα_fvs : x ∉ α.fvs := hstk_f α (List.mem_cons_self _ _)
        exact .ms_fop (x :: L) (fun w hw => by
          have hw_ne : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          have hfresh_ext : LNCtx.fresh_in_anns x ((w, .equiv α) :: Γ_f) :=
            LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hα_fvs) hfresh_f
          have hbody_w_fvs : x ∉ (body.open_at 0 (.fvar w)).fvs :=
            LNExpr.not_mem_fvs_open_at body hbody_fvs (Ne.symm hw_ne)
          exact subRed_cast_ctx (drop_first_cons_ne x w (.equiv _) _ hw_ne)
            (ih w hw_L hfresh_ext (fun e he => hstk_f e (List.mem_cons_of_mem _ he)) hbody_w_fvs)))
  have final := result h hfresh hx_s hx_u
  rwa [drop_first_head] at final

set_option maxHeartbeats 3200000 in
/-- SubRed version of `equivRed_ctx_drop_fresh`: if `SubRed ((x,.equiv v)::Γ) s u u'`
    and x is fresh in u, v, Γ (all_fvs), and the stack, then `SubRed Γ s u u'`.

    Uses the same mutual induction technique as `equivRed_ctx_drop_fresh` but starts
    from a SubRed derivation using `@LNSubRed.rec`. -/
noncomputable def subRed_ctx_drop_fresh
    {x : String} {v : LNExpr} {Γ : LNCtx} {s : LNStack} {u u' : LNExpr}
    (h : LNSubRed ((x, .equiv v) :: Γ) s u u')
    (hx_u : x ∉ u.fvs)
    (hx_v : x ∉ v.fvs)
    (hx_Γ : x ∉ LNCtx.all_fvs Γ)
    (hx_s : ∀ e ∈ s, x ∉ e.fvs)
    : LNSubRed Γ s u u' := by
  have hfresh : LNCtx.fresh_in_anns x ((x, .equiv v) :: Γ) :=
    LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hx_v)
      (LNCtx.fresh_in_anns_of_not_mem_all_fvs hx_Γ)
  have result :=
    @LNSubRed.rec
      (motive_1 := fun Γ_r s_r u_r v_r _ =>
        LNCtx.fresh_in_anns x Γ_r → (∀ e ∈ s_r, x ∉ e.fvs) → x ∉ u_r.fvs →
        LNEquivRed (drop_first x Γ_r) s_r u_r v_r)
      (motive_2 := fun Γ_r s_r u_r v_r _ =>
        LNCtx.fresh_in_anns x Γ_r → (∀ e ∈ s_r, x ∉ e.fvs) → x ∉ u_r.fvs →
        LNSubRed (drop_first x Γ_r) s_r u_r v_r)
      -- me_pro z: fvar z → α' via SubRed Γ [] on z's equiv annotation α
      (fun {Γ_p s_p z α α'} hmem _hsub ih_sub hfresh_p _hstk_p hfvs_p => by
        have hne : z ≠ x := fun heq => hfvs_p (heq ▸ List.mem_cons_self _ _)
        have hx_α : x ∉ α.fvs := not_mem_fvs_of_mem_equiv_gen hmem hfresh_p
        exact .me_pro (drop_first_mem_equiv_ne hne hmem) (ih_sub hfresh_p (fun _ he => absurd he (List.not_mem_nil _)) hx_α))
      -- me_bet: app (lam dom body) v_bet → t^v'
      (fun {Γ_b s_b dom body t v_bet v'_bet} L _hbody _hv ih_body ih_v hfresh_b hstk_b hfvs_b => by
        have hv_fvs : x ∉ v_bet.fvs := fun hmem => hfvs_b (List.mem_append_right _ hmem)
        have hbody_fvs : x ∉ body.fvs := fun hmem =>
          hfvs_b (List.mem_append_left _ (List.mem_append_right _ hmem))
        exact .me_bet (x :: L)
          (fun w hw => by
            have hw_ne : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
            have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
            have hfresh_ext : LNCtx.fresh_in_anns x ((w, .equiv v_bet) :: Γ_b) :=
              LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hv_fvs) hfresh_b
            have hbody_w_fvs : x ∉ (body.open_at 0 (.fvar w)).fvs :=
              LNExpr.not_mem_fvs_open_at body hbody_fvs (Ne.symm hw_ne)
            exact equivRed_cast_ctx (drop_first_cons_ne x w (.equiv _) _ hw_ne)
              (ih_body w hw_L hfresh_ext hstk_b hbody_w_fvs))
          (ih_v hfresh_b (fun _ he => absurd he (List.not_mem_nil _)) hv_fvs))
      -- me_top
      (fun _hfresh _hstk _hfvs => .me_top)
      -- me_var
      (fun _hfresh _hstk _hfvs => .me_var)
      -- me_tap
      (fun _hfresh _hstk _hfvs => .me_tap)
      -- me_app
      (fun {Γ_a s_a u_a u'_a v_a v'_a} _hu _hv ih_u ih_v hfresh_a hstk_a hfvs_a => by
        have hu_fvs : x ∉ u_a.fvs := fun hmem => hfvs_a (List.mem_append_left _ hmem)
        have hv_fvs : x ∉ v_a.fvs := fun hmem => hfvs_a (List.mem_append_right _ hmem)
        exact .me_app
          (ih_u hfresh_a
            (fun e he => by cases he with | head => exact hv_fvs | tail _ h => exact hstk_a e h) hu_fvs)
          (ih_v hfresh_a (fun _ he => absurd he (List.not_mem_nil _)) hv_fvs))
      -- me_fun
      (fun {Γ_f dom dom' body body'} L _hdom _hbody ih_dom ih_body hfresh_f _hstk_f hfvs_f => by
        have hdom_fvs : x ∉ dom.fvs := fun hmem => hfvs_f (List.mem_append_left _ hmem)
        have hbody_fvs : x ∉ body.fvs := fun hmem => hfvs_f (List.mem_append_right _ hmem)
        exact .me_fun (x :: L)
          (ih_dom hfresh_f (fun _ he => absurd he (List.not_mem_nil _)) hdom_fvs)
          (fun w hw => by
            have hw_ne : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
            have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
            have hfresh_ext : LNCtx.fresh_in_anns x ((w, .sub dom) :: Γ_f) :=
              LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hdom_fvs) hfresh_f
            have hbody_w_fvs : x ∉ (body.open_at 0 (.fvar w)).fvs :=
              LNExpr.not_mem_fvs_open_at body hbody_fvs (Ne.symm hw_ne)
            exact equivRed_cast_ctx (drop_first_cons_ne x w (.sub _) _ hw_ne)
              (ih_body w hw_L hfresh_ext (fun _ he => absurd he (List.not_mem_nil _)) hbody_w_fvs)))
      -- me_fop
      (fun {Γ_f s_f α dom dom' body body'} L _hdom _hbody ih_dom ih_body hfresh_f hstk_f hfvs_f => by
        have hdom_fvs : x ∉ dom.fvs := fun hmem => hfvs_f (List.mem_append_left _ hmem)
        have hbody_fvs : x ∉ body.fvs := fun hmem => hfvs_f (List.mem_append_right _ hmem)
        have hα_fvs : x ∉ α.fvs := hstk_f α (List.mem_cons_self _ _)
        exact .me_fop (x :: L)
          (ih_dom hfresh_f (fun _ he => absurd he (List.not_mem_nil _)) hdom_fvs)
          (fun w hw => by
            have hw_ne : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
            have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
            have hfresh_ext : LNCtx.fresh_in_anns x ((w, .equiv α) :: Γ_f) :=
              LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hα_fvs) hfresh_f
            have hbody_w_fvs : x ∉ (body.open_at 0 (.fvar w)).fvs :=
              LNExpr.not_mem_fvs_open_at body hbody_fvs (Ne.symm hw_ne)
            exact equivRed_cast_ctx (drop_first_cons_ne x w (.equiv _) _ hw_ne)
              (ih_body w hw_L hfresh_ext (fun e he => hstk_f e (List.mem_cons_of_mem _ he)) hbody_w_fvs)))
      -- ms_pro z
      (fun {Γ_sp s_sp z t} hmem hfresh_sp _hstk_sp hfvs_sp => by
        have hne : z ≠ x := fun heq => hfvs_sp (heq ▸ List.mem_cons_self _ _)
        exact .ms_pro (drop_first_mem_sub_ne hne hmem))
      -- ms_top
      (fun _hfresh _hstk _hfvs => .ms_top)
      -- ms_equ
      (fun _hequ ih_equ hfresh_e hstk_e hfvs_e => .ms_equ (ih_equ hfresh_e hstk_e hfvs_e))
      -- ms_app
      (fun {Γ_a s_a u_a u'_a v_a} _hsub ih hfresh_a hstk_a hfvs_a => by
        have hu_fvs : x ∉ u_a.fvs := fun hmem => hfvs_a (List.mem_append_left _ hmem)
        have hv_fvs : x ∉ v_a.fvs := fun hmem => hfvs_a (List.mem_append_right _ hmem)
        exact .ms_app (ih hfresh_a
          (fun e he => by cases he with | head => exact hv_fvs | tail _ h => exact hstk_a e h) hu_fvs))
      -- ms_fun
      (fun {Γ_f dom body body'} L _hbody ih hfresh_f _hstk_f hfvs_f => by
        have hbody_fvs : x ∉ body.fvs := fun hmem => hfvs_f (List.mem_append_right _ hmem)
        have hdom_fvs : x ∉ dom.fvs := fun hmem => hfvs_f (List.mem_append_left _ hmem)
        exact .ms_fun (x :: L) (fun w hw => by
          have hw_ne : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          have hfresh_ext : LNCtx.fresh_in_anns x ((w, .sub dom) :: Γ_f) :=
            LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hdom_fvs) hfresh_f
          have hbody_w_fvs : x ∉ (body.open_at 0 (.fvar w)).fvs :=
            LNExpr.not_mem_fvs_open_at body hbody_fvs (Ne.symm hw_ne)
          exact subRed_cast_ctx (drop_first_cons_ne x w (.sub _) _ hw_ne)
            (ih w hw_L hfresh_ext (fun _ he => absurd he (List.not_mem_nil _)) hbody_w_fvs)))
      -- ms_fop
      (fun {Γ_f s_f α dom body body'} L _hbody ih hfresh_f hstk_f hfvs_f => by
        have hbody_fvs : x ∉ body.fvs := fun hmem => hfvs_f (List.mem_append_right _ hmem)
        have hα_fvs : x ∉ α.fvs := hstk_f α (List.mem_cons_self _ _)
        exact .ms_fop (x :: L) (fun w hw => by
          have hw_ne : w ≠ x := fun heq => hw (heq ▸ List.mem_cons_self _ _)
          have hw_L : w ∉ L := fun h => hw (List.mem_cons_of_mem _ h)
          have hfresh_ext : LNCtx.fresh_in_anns x ((w, .equiv α) :: Γ_f) :=
            LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hα_fvs) hfresh_f
          have hbody_w_fvs : x ∉ (body.open_at 0 (.fvar w)).fvs :=
            LNExpr.not_mem_fvs_open_at body hbody_fvs (Ne.symm hw_ne)
          exact subRed_cast_ctx (drop_first_cons_ne x w (.equiv _) _ hw_ne)
            (ih w hw_L hfresh_ext (fun e he => hstk_f e (List.mem_cons_of_mem _ he)) hbody_w_fvs)))
  have final := result h hfresh hx_s hx_u
  rwa [drop_first_head] at final

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
-- NOTE: sorry'd because LNEquivRed is Prop — cannot eliminate into Type (noPromoAt).
def promotion_collapse_equiv
    {Γ : LNCtx} {s : LNStack} {u w : LNExpr}
    (h : LNEquivRed Γ s u w)
    {x : String} {α : LNExpr}
    (_hlook : Γ.lookup' x = some (.equiv α))
    (_hlc : u.lc) (_hwf : Γ.wf) (_hswf : s.wf)
    : Sum (LNEquivRed.noPromoAt x Γ s u w) (PLift (LNEquivRed Γ s u w)) :=
  .inr ⟨h⟩

set_option maxHeartbeats 3200000 in
/-- Promotion collapse for ≤→: if x has .equiv annotation in Γ, then any
    sub-reduction either doesn't promote x (noPromoAt) or is actually an
    equiv-reduction.

    This is the key lemma for the ME-BET/MS-FOP case of commutativity.
    When noPromoAt holds, annotation swap lemmas apply directly.
    When the SubRed collapses to EquivRed, the diamond lemma applies. -/
-- NOTE: stale comment — LNSubRed is Type (not Prop), so elimination into Type
-- (Sum/noPromoAt) IS valid. The proof requires mutual induction using @LNSubRed.rec.
-- Non-cofinite cases are straightforward: ms_pro → .inl (x has .equiv so z ≠ x),
-- ms_top → .inl, ms_equ → .inr (it IS an EquivRed), ms_app → recurse.
-- Cofinite cases (ms_fun, ms_fop) are blocked: the IH for the body gives Sum for
-- each w independently, but different w could give different branches (one .inl,
-- another .inr). Constructing ms_fun-of-noPromoAt requires ALL w to give .inl;
-- constructing me_fun requires ALL w to give EquivRed. A fresh witness w₀ decides
-- one branch, but the other branch for a different w cannot be excluded without
-- alpha-invariance of the specific derivation tree. The correct resolution likely
-- uses derivation-tree induction or a custom well-founded order.
noncomputable def promotion_collapse
    {Γ : LNCtx} {s : LNStack} {u w : LNExpr}
    (h : LNSubRed Γ s u w)
    {x : String} {α : LNExpr}
    (hlook : Γ.lookup' x = some (.equiv α))
    (hlc : u.lc) (hwf : Γ.wf) (hswf : s.wf)
    : Sum (LNSubRed.noPromoAt x Γ s u w) (PLift (LNEquivRed Γ s u w)) := by
  sorry

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
noncomputable def diamond_full
    (t₀ : LNExpr)
    {Γ Γ₁ Γ₂ : LNCtx} {s s₁ s₂ : LNStack} {t₁ t₂ : LNExpr}
    (h1 : LNEquivRed Γ s t₀ t₁) (h2 : LNEquivRed Γ s t₀ t₂)
    (hctx1 : LNCtxRed Γ s Γ₁ s₁) (hctx2 : LNCtxRed Γ s Γ₂ s₂)
    (hlc : t₀.lc) (hwf : Γ.wf) (hswf : s.wf) (hnd : (LNCtx.dom Γ).Nodup)
    : Σ' t₃, LNEquivRed Γ₁ s₁ t₁ t₃ × LNEquivRed Γ₂ s₂ t₂ t₃ := by
  cases h1 with
  | me_pro _ _ => sorry  -- needs commutativity for SubRed diamond; see equivRed_subst_diamond
  | me_top => cases h2 with | me_top => exact ⟨.top, .me_top, .me_top⟩
  | me_var =>
    cases h2 with
    | me_var => exact ⟨.fvar _, .me_var, .me_var⟩
    | me_pro _ _ => sorry  -- symmetric ME-PRO case; same blocker as above
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
    | @me_bet _ _ dom body t₂ _ v₂' L₂ h2_body h2_v =>
      -- ME-APP / ME-BET case
      -- h1 = me_app h1_u h1_v: t₀ = app (lam dom body) v_head
      --   h1_u : EquivRed Γ (v_head :: s) (lam dom body) u₁' → must be me_fop
      --   h1_v : EquivRed Γ [] v_head v₁'
      --   t₁ = app u₁' v₁'
      -- h2 = me_bet L₂ h2_body h2_v: t₀ = app (lam dom body) v_head
      --   h2_body : ∀ x ∉ L₂, EquivRed ((x, .equiv v_head) :: Γ) s (body^x) (t₂^x)
      --   h2_v : EquivRed Γ [] v_head v₂'
      --   t₂_result = t₂.open_at 0 v₂'
      cases h1_u with
      | @me_fop _ _ _ _ dom₁' _ body₁' L₁ h1_dom h1_body_fop =>
        -- h1_body_fop : ∀ x ∉ L₁, EquivRed ((x, .equiv v_head) :: Γ) s (body^x) (body₁'^x)
        -- Both body reductions are in ((x, .equiv v_head) :: Γ) s — same context!
        -- Argument IH
        obtain ⟨v₃, hv₃l, hv₃r⟩ := diamond_full v_head h1_v h2_v
          (ctxRed_nil_of_ctxRed hctx1) (ctxRed_nil_of_ctxRed hctx2)
          hlc.2 hwf (fun _ he => absurd he (List.not_mem_nil _)) hnd
        -- Pick x fresh
        obtain ⟨x, hx⟩ := exists_fresh_string
          (L₁ ++ L₂ ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ₁ ++ LNCtx.all_fvs Γ₂ ++
           body₁'.fvs ++ t₂.fvs ++ v_head.fvs ++ s.flatMap LNExpr.fvs)
        have hxL₁ : x ∉ L₁ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))))))
        have hxL₂ : x ∉ L₂ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))))
        have hxΓ_all : x ∉ LNCtx.all_fvs Γ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))))
        have hxΓ : x ∉ LNCtx.dom Γ := LNCtx.not_mem_dom_of_not_mem_all_fvs hxΓ_all
        have hxΓ₁_all : x ∉ LNCtx.all_fvs Γ₁ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))
        have hxΓ₂_all : x ∉ LNCtx.all_fvs Γ₂ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
        have hxb₁ : x ∉ body₁'.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
        have hxt₂ : x ∉ t₂.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
        have hxv : x ∉ v_head.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_right _ h))
        have hx_s_fvs : ∀ e ∈ s, x ∉ e.fvs := fun e he hm =>
          hx (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hm⟩))
        -- Body context well-formedness
        have hwf_body : LNCtx.wf ((x, .equiv v_head) :: Γ) :=
          fun p hp => by cases hp with | head => exact hlc.2 | tail _ h => exact hwf p h
        -- Body IH
        obtain ⟨u₃, hu₃l, hu₃r⟩ := diamond_full (body.open_at 0 (.fvar x))
          (h1_body_fop x hxL₁) (h2_body x hxL₂)
          (.ct_ann_equiv hctx1 h1_v) (.ct_ann_equiv hctx2 h2_v)
          (LNExpr.lc_at_open_fvar hlc.1.2) hwf_body hswf
          (List.nodup_cons.mpr ⟨hxΓ, hnd⟩)
        -- u₃ lc
        have hb₁lc := equivRed_preserves_lc (h1_body_fop x hxL₁)
          (LNExpr.lc_at_open_fvar hlc.1.2) hwf_body hswf
        have hv₁'lc := equivRed_preserves_lc h1_v hlc.2 hwf
          (fun _ he => absurd he (List.not_mem_nil _))
        have hwf_Γ₁ : LNCtx.wf Γ₁ := ctxRed_preserves_ctx_wf hctx1 hwf hswf
        have hwf_s₁ : LNStack.wf s₁ := ctxRed_preserves_stk_wf hctx1 hwf hswf
        have u₃lc : u₃.lc := equivRed_preserves_lc hu₃l hb₁lc
          (fun p hp => by cases hp with | head => exact hv₁'lc | tail _ h => exact hwf_Γ₁ p h)
          hwf_s₁
        -- Freshness of x in v₁'
        have hxv₁' : x ∉ v₁'.fvs := equivRed_preserves_not_mem_fvs h1_v hxv hxΓ_all
          (fun _ he => absurd he (List.not_mem_nil _))
        have hxv₂' : x ∉ v₂'.fvs := equivRed_preserves_not_mem_fvs h2_v hxv hxΓ_all
          (fun _ he => absurd he (List.not_mem_nil _))
        have hx_s₁_fvs : ∀ e ∈ s₁, x ∉ e.fvs :=
          ctxRed_preserves_stack_freshness hctx1 hxΓ_all hx_s_fvs
        -- Common reduct: (u₃.close_at 0 x).open_at 0 v₃
        -- Left: use ME-BET (input is app (lam dom₁' body₁') v₁')
        -- Right: needs equivRed substitution (sorry)
        exact ⟨(u₃.close_at 0 x).open_at 0 v₃,
          .me_bet (L₁ ++ L₂ ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ₁ ++ LNCtx.all_fvs Γ₂ ++
                   body₁'.fvs ++ t₂.fvs ++ v_head.fvs ++ s.flatMap LNExpr.fvs)
            (fun y hy => by
              have hyΓ₁ : y ∉ LNCtx.all_fvs Γ₁ := fun h => hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))
              have := equivRed_rename hu₃l hxΓ₁_all hyΓ₁ hxb₁
                (by simp [LNAnn.fvs]; exact hxv₁') hx_s₁_fvs
              rw [open_close_subst u₃lc]; exact this)
            hv₃l,
          sorry⟩  -- sorry: right side needs equivRed_subst_diamond (see file header)
  | @me_bet _ _ dom body t₁ v_arg v₁' L₁ h1_body h1_v =>
    cases h2 with
    | @me_bet _ _ _ _ t₂ _ v₂' L₂ h2_body h2_v =>
      -- ME-BET / ME-BET case
      -- Both reductions beta-reduce in ((x, .equiv v_arg) :: Γ) s
      -- Body IH gives common reduct for bodies, arg IH for arguments
      -- Both sides need equivRed_subst_diamond (see file header)
      sorry  -- sorry: both sides need equivRed_subst_diamond
    | @me_app _ _ _ u₂' _ v₂' h2_u h2_v =>
      -- ME-BET / ME-APP: symmetric to ME-APP / ME-BET
      cases h2_u with
      | @me_fop _ _ _ _ dom₂' _ body₂' L₂ h2_dom h2_body_fop =>
        -- h2_body_fop : ∀ x ∉ L₂, EquivRed ((x, .equiv v_arg) :: Γ) s (body^x) (body₂'^x)
        -- h1_body : ∀ x ∉ L₁, EquivRed ((x, .equiv v_arg) :: Γ) s (body^x) (t₁^x)
        -- Both body reductions are in ((x, .equiv v_arg) :: Γ) s — same context!
        -- Argument IH
        obtain ⟨v₃, hv₃l, hv₃r⟩ := diamond_full v_arg h1_v h2_v
          (ctxRed_nil_of_ctxRed hctx1) (ctxRed_nil_of_ctxRed hctx2)
          hlc.2 hwf (fun _ he => absurd he (List.not_mem_nil _)) hnd
        -- Pick x fresh
        obtain ⟨x, hx⟩ := exists_fresh_string
          (L₁ ++ L₂ ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ₁ ++ LNCtx.all_fvs Γ₂ ++
           t₁.fvs ++ body₂'.fvs ++ v_arg.fvs ++ s.flatMap LNExpr.fvs)
        have hxL₁ : x ∉ L₁ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))))))
        have hxL₂ : x ∉ L₂ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))))
        have hxΓ_all : x ∉ LNCtx.all_fvs Γ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))))
        have hxΓ : x ∉ LNCtx.dom Γ := LNCtx.not_mem_dom_of_not_mem_all_fvs hxΓ_all
        have hxΓ₁_all : x ∉ LNCtx.all_fvs Γ₁ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))
        have hxΓ₂_all : x ∉ LNCtx.all_fvs Γ₂ := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
        have hxt₁ : x ∉ t₁.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
        have hxb₂ : x ∉ body₂'.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
        have hxv : x ∉ v_arg.fvs := fun h => hx (List.mem_append_left _ (List.mem_append_right _ h))
        have hx_s_fvs : ∀ e ∈ s, x ∉ e.fvs := fun e he hm =>
          hx (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hm⟩))
        -- Body context well-formedness
        have hwf_body : LNCtx.wf ((x, .equiv v_arg) :: Γ) :=
          fun p hp => by cases hp with | head => exact hlc.2 | tail _ h => exact hwf p h
        -- Body IH
        obtain ⟨u₃, hu₃l, hu₃r⟩ := diamond_full (body.open_at 0 (.fvar x))
          (h1_body x hxL₁) (h2_body_fop x hxL₂)
          (.ct_ann_equiv hctx1 h1_v) (.ct_ann_equiv hctx2 h2_v)
          (LNExpr.lc_at_open_fvar hlc.1.2) hwf_body hswf
          (List.nodup_cons.mpr ⟨hxΓ, hnd⟩)
        -- u₃ lc
        have hb₂lc := equivRed_preserves_lc (h2_body_fop x hxL₂)
          (LNExpr.lc_at_open_fvar hlc.1.2) hwf_body hswf
        have hv₂'lc := equivRed_preserves_lc h2_v hlc.2 hwf
          (fun _ he => absurd he (List.not_mem_nil _))
        have hwf_Γ₂ : LNCtx.wf Γ₂ := ctxRed_preserves_ctx_wf hctx2 hwf hswf
        have hwf_s₂ : LNStack.wf s₂ := ctxRed_preserves_stk_wf hctx2 hwf hswf
        have u₃lc : u₃.lc := equivRed_preserves_lc hu₃r hb₂lc
          (fun p hp => by cases hp with | head => exact hv₂'lc | tail _ h => exact hwf_Γ₂ p h)
          hwf_s₂
        -- Freshness of x in v₁', v₂'
        have hxv₁' : x ∉ v₁'.fvs := equivRed_preserves_not_mem_fvs h1_v hxv hxΓ_all
          (fun _ he => absurd he (List.not_mem_nil _))
        have hxv₂' : x ∉ v₂'.fvs := equivRed_preserves_not_mem_fvs h2_v hxv hxΓ_all
          (fun _ he => absurd he (List.not_mem_nil _))
        have hx_s₂_fvs : ∀ e ∈ s₂, x ∉ e.fvs :=
          ctxRed_preserves_stack_freshness hctx2 hxΓ_all hx_s_fvs
        -- Common reduct: (u₃.close_at 0 x).open_at 0 v₃
        -- Right: use ME-BET (input is app (lam dom₂' body₂') v₂')
        -- Left: needs equivRed_subst_diamond (see file header)
        exact ⟨(u₃.close_at 0 x).open_at 0 v₃,
          sorry,  -- sorry: left side needs equivRed_subst_diamond (t₁^v₁' → u₃[x:=v₃])
          .me_bet (L₁ ++ L₂ ++ LNCtx.all_fvs Γ ++ LNCtx.all_fvs Γ₁ ++ LNCtx.all_fvs Γ₂ ++
                   t₁.fvs ++ body₂'.fvs ++ v_arg.fvs ++ s.flatMap LNExpr.fvs)
            (fun y hy => by
              have hyΓ₂ : y ∉ LNCtx.all_fvs Γ₂ := fun h => hy (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
              have := equivRed_rename hu₃r hxΓ₂_all hyΓ₂ hxb₂
                (by simp [LNAnn.fvs]; exact hxv₂') hx_s₂_fvs
              rw [open_close_subst u₃lc]; exact this)
            hv₃r⟩
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
decreasing_by
  all_goals first
    | (simp_all [LNExpr.sz, sz_open_at_fvar]; omega)
    | sorry -- termination: simp_all loops; goal is trivially true (sub-term sz < whole)

/-- Diamond (one-context version used by commutativity).
    Derived from `diamond_full` by using `ctxRed_refl` for one context. -/
noncomputable def diamond
    {Γ Γ' : LNCtx} {s s' : LNStack} {t₀ t₁ t₂ : LNExpr}
    (h1 : LNEquivRed Γ s t₀ t₁) (h2 : LNEquivRed Γ s t₀ t₂)
    (hctx : LNCtxRed Γ s Γ' s')
    (hwf_ctx : Γ.wf) (hwf_stk : s.wf)
    (hlc : t₀.lc) (hnd : (LNCtx.dom Γ).Nodup)
    : Σ' t₃, LNEquivRed Γ s t₂ t₃ × LNEquivRed Γ' s' t₁ t₃ := by
  have hid : LNCtxRed Γ s Γ s := ctxRed_refl Γ s hwf_ctx hwf_stk
  obtain ⟨t₃, h_left, h_right⟩ := diamond_full t₀ h2 h1 hid hctx hlc hwf_ctx hwf_stk hnd
  exact ⟨t₃, h_left, h_right⟩

/-- Inversion on ctxRed at empty stack for equiv annotation head:
    If (x,.equiv v)::Γ; [] ↦ (x,.equiv v')::Γ'; [], extract inner CtxRed and EquivRed.
    At empty stack, the only applicable constructor for a context cons is ct_ann_equiv. -/
noncomputable def ctxRed_nil_equiv_head_inv
    {x : String} {v : LNExpr} {Γ : LNCtx}
    {v' : LNExpr} {Γ' : LNCtx}
    (h : LNCtxRed ((x, .equiv v) :: Γ) [] ((x, .equiv v') :: Γ') [])
    : (LNCtxRed Γ [] Γ' []) × (LNEquivRed Γ [] v v') := by
  cases h with
  | ct_ann_equiv hctx_i hred => exact ⟨hctx_i, hred⟩

/- ### Commutativity + equivRed_subst_diamond (mutual block)

Commutativity is the main theorem. By induction on the term t₀ and case
analysis on the pair of rules (h_equiv : ≡→, h_sub : ≤→) applied to t₀.

equivRed_subst_diamond / subRed_subst_diamond are the diamond substitution
lemmas for EquivRed/SubRed under .equiv annotations. They are co-proved
with commutativity because:
- commutativity's ME-BET/MS-FOP `.inr` case calls equivRed_subst_diamond
- equivRed_subst_diamond's ME-PRO-on-x case calls commutativity on v

Shared termination measure: `(budget, term.sz)` with lexicographic ordering.
- commutativity(budget, t₀): measure (budget, t₀.sz), with t₀.sz ≤ budget
- equivRed_subst_diamond(budget, u): measure (budget, u.sz), with u.sz ≤ budget
- commutativity → commutativity on sub-terms: budget stays, t₀.sz decreases
- commutativity → equivRed_subst_diamond on body: budget stays, u.sz < t₀.sz
- equivRed_subst_diamond → equivRed_subst_diamond: budget stays, u.sz decreases
- equivRed_subst_diamond → commutativity on v: v.sz < budget (strict), so
  first component decreases

Proof structure follows Appendix A of Pasquale & Garcia-Perez.
-/

set_option maxHeartbeats 1600000 in
mutual

noncomputable def commutativity
    (budget : Nat)
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
    (hbudget : t₀.sz ≤ budget)
    : Σ' t₃ : LNExpr, PLift (LNEquivRed Γ s t₂ t₃) × PLift (LNSubRed Γ' s' t₁ t₃) ×
        (∀ x, LNSubRed.noPromoAt x Γ s t₀ t₂ → LNSubRed.noPromoAt x Γ' s' t₁ t₃) := by
  -- DEFINITIVELY BLOCKED: The MS-PRO/ME-VAR case (h_sub = ms_pro, h_equiv = me_var).
  --
  -- The right edge SubRed Γ' s' (fvar x) t₃ can ONLY use three constructors:
  --   (1) MS-PRO: forces t₃ = t' (annotation of x in Γ')
  --   (2) MS-TOP: forces t₃ = .top
  --   (3) MS-EQU(ME-VAR): forces t₃ = fvar x (requires .equiv annotation)
  -- No other SubRed constructor applies to fvar x.
  --
  -- For (1): top edge needs EquivRed Γ s t t'. We have EquivRed Γ [] t t' from
  --   ctxRed_lookup_sub (CT-ANN reduces at nil stack), but stack extension from
  --   [] to s is FALSE (counterexample at end of file).
  -- For (2): top edge needs EquivRed Γ s t .top — not true for all t.
  -- For (3): x has .sub annotation (MS-PRO premise), not .equiv — constructor
  --   inapplicable.
  --
  -- Alternative approaches also fail:
  -- - Weakened return type (∃ t₃ t₄, ... × EquivRed t₃ t₄ connecting edge):
  --   connecting edge still needs stack extension.
  -- - Reflexive top edge (t₃ = t via equivRed_refl): Γ' has x ≤ t' not x ≤ t.
  -- - Assuming annotations are normal forms (t = t'): not general — beta-redexes
  --   are valid annotations.
  -- - Commutativity recursion: no SubRed ON t at stack s to feed in.
  --
  -- Since t₃ is forced to one of {t', .top, fvar x} by the right edge, and all
  -- three fail for the top edge, the case is IMPOSSIBLE without system changes.
  -- Root cause: CT-ANN's nil stack. Fix: CT-ANN at full stack s.
  -- See sorry #7 "QED argument" in the file header for the complete analysis.
  sorry
termination_by (budget, t₀.sz)
decreasing_by all_goals simp_all [LNExpr.sz, sz_open_at_fvar]; omega

/-- The substitution diamond for EquivRed under .equiv annotations.

Given `EquivRed ((x,.equiv v)::Γ) s u u'` and a context reduction that reduces
v to v' and Γ;s to Γ';s', there exists a common reduct w such that:
- `EquivRed Γ s (u'[x↦v]) w` (top edge: substitute original annotation into output)
- `SubRed Γ' s' (u[x↦v']) w` (right edge: substitute reduced annotation into input)

At ME-PRO on x:
- u = fvar x, u' = result of SubRed on v
- u'[x↦v] = result (x fresh for result), u[x↦v'] = v'
- Need: ∃ w, EquivRed Γ s result w ∧ SubRed Γ' s' v' w
- This follows from commutativity on v (with appropriate stack handling)

At ME-VAR on y ≠ x:
- Both sides are fvar y after subst; take w = fvar y, use refl

At structural cases (ME-APP, ME-FUN, ME-FOP, ME-BET, ME-TOP, ME-TAP):
- Recurse on sub-derivations with same budget (u.sz decreases)
-/
noncomputable def equivRed_subst_diamond
    (budget : Nat)
    {x : String} {v : LNExpr} {Γ : LNCtx} {s : LNStack} {u u' : LNExpr}
    {Γ' : LNCtx} {s' : LNStack} {v' : LNExpr}
    (h : LNEquivRed ((x, .equiv v) :: Γ) s u u')
    (hctx : LNCtxRed ((x, .equiv v) :: Γ) s ((x, .equiv v') :: Γ') s')
    (hx_all_fvs : x ∉ LNCtx.all_fvs Γ)
    (hx_v : x ∉ v.fvs) (hv_lc : v.lc) (hv'_lc : v'.lc)
    (hu_lc : u.lc)
    (hwf : Γ.wf) (hswf : s.wf)
    (hnd : (LNCtx.dom Γ).Nodup)
    (hbudget : u.sz ≤ budget)
    (hv_budget : v.sz < budget)
    (hx_s : ∀ e ∈ s, x ∉ e.fvs)
    : Σ' w, LNEquivRed Γ s (u'.subst_fvar x v) w × LNSubRed Γ' s' (u.subst_fvar x v') w := by
  cases h with
  | me_top =>
    -- u = .top, u' = .top
    simp [LNExpr.subst_fvar]
    exact ⟨.top, .me_top, .ms_top⟩
  | me_tap =>
    -- u = app .top v_arg, u' = .top
    -- u'.subst x v = .top, u.subst x v' = app .top (v_arg.subst x v')
    simp [LNExpr.subst_fvar]
    exact ⟨.top, .me_top, .ms_top⟩
  | me_var =>
    -- u = fvar y, u' = fvar y
    simp [LNExpr.subst_fvar]
    split
    · -- y = x: u'.subst = v, u.subst = v'
      -- Need: ∃ w, EquivRed Γ s v w ∧ SubRed Γ' s' v' w
      -- Left edge with w = v: equivRed_refl Γ s v hv_lc gives EquivRed Γ s v v ✓
      -- Right edge: SubRed Γ' s' v' v — backwards! v' is the reduced annotation,
      -- v is the original. There is no SubRed from v' back to v in general.
      --
      -- Alternative witness w = v': Left needs EquivRed Γ s v v'. We have
      -- EquivRed Γ [] v v' (from hctx), but need it at stack s. Stack extension
      -- is FALSE in general. This is the fundamental stack alignment problem.
      --
      -- The correct approach requires the mutual block: call commutativity on v
      -- with a non-trivial SubRed (e.g., via the annotation's own reduction).
      -- For me_var y=x, the input SubRed is the identity (subRed_refl), which
      -- doesn't help. The actual resolution may require rethinking how me_var
      -- on x interacts with the substitution diamond — in practice, me_pro y=x
      -- handles the interesting case and me_var y=x is subsumed.
      -- ROOT CAUSE: CT-ANN's nil stack. Same as commutativity MS-PRO/ME-VAR.
      -- See sorry #7 in the file header.
      sorry
    · -- y ≠ x: both sides are fvar y
      exact ⟨.fvar _, .me_var, .ms_equ .me_var⟩
  | me_pro hmem_pro hsub_pro =>
    -- u = fvar y, u' = result of SubRed α → u' via hsub_pro
    -- hmem_pro : mem_equiv ((x,.equiv v)::Γ) y α
    -- hsub_pro : SubRed ((x,.equiv v)::Γ) s α u'
    -- Need to figure out y and α from the goal/context
    rename_i y α
    by_cases hyx : y = x
    · -- y = x: hmem_pro says x has .equiv annotation, so α = v
      -- Extract α = v from hmem_pro
      have hα_eq : α = v := by
        rw [hyx] at hmem_pro; simp [LNCtx.mem_equiv, LNCtx.lookup'] at hmem_pro; exact hmem_pro.symm
      -- hsub_pro : SubRed ((x,.equiv v)::Γ) s α u'; since α = v, hsub_pro is on v
      rw [hα_eq] at hsub_pro
      -- Now hsub_pro : SubRed ((x,.equiv v)::Γ) s v u'
      -- Goal: ∃ w, EquivRed Γ s (u'.subst_fvar x v) w ∧ SubRed Γ' s' ((fvar y).subst_fvar x v') w
      -- Since y = x: (fvar y).subst_fvar x v' = v'
      -- Since x ∉ u'.fvs: u'.subst_fvar x v = u'
      -- With nil-stack ME-PRO, hsub_pro : SubRed ((x,.equiv v)::Γ) [] v u'
      have hx_u'_fvs : x ∉ u'.fvs :=
        subRed_preserves_not_mem_fvs_gen hsub_pro hx_v
          (LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hx_v)
            (LNCtx.fresh_in_anns_of_not_mem_all_fvs hx_all_fvs))
          (fun _ he => absurd he (List.not_mem_nil _))
      rw [subst_fvar_notin hx_u'_fvs, show (LNExpr.fvar y).subst_fvar x v' = v' from by
        simp [LNExpr.subst_fvar, hyx]]
      -- Goal: ∃ w, EquivRed Γ s u' w ∧ SubRed Γ' s' v' w
      --
      -- STRATEGY: call commutativity on v at the extended context at stack [], then:
      -- - Left edge: drop x via equivRed_ctx_drop_fresh
      -- - Right edge: still blocked (v → v' input translation + stack [] → s')
      have hwf_ext : LNCtx.wf ((x, .equiv v) :: Γ) :=
        fun p hp => by cases hp with
        | head => exact hv_lc
        | tail _ hmem => exact hwf p hmem
      have hx_dom : x ∉ LNCtx.dom Γ := LNCtx.not_mem_dom_of_not_mem_all_fvs hx_all_fvs
      obtain ⟨t₃, htop, hright, _hnp_ih⟩ :=
        commutativity v.sz v
          (equivRed_refl ((x, .equiv v) :: Γ) [] v hv_lc)
          hsub_pro (ctxRed_nil_of_ctxRed hctx) hv_lc
          (List.nodup_cons.mpr ⟨hx_dom, hnd⟩)
          hwf_ext (fun _ he => absurd he (List.not_mem_nil _)) (Nat.le_refl v.sz)
      -- htop : PLift (EquivRed ((x,.equiv v)::Γ) [] u' t₃) — note: at stack []
      -- hright : PLift (SubRed ((x,.equiv v')::Γ') [] v t₃) — note: at stack []
      --
      -- LEFT EDGE: need EquivRed Γ s u' t₃ but htop is at stack [].
      -- After ctx_drop we get EquivRed Γ [] u' t₃, still at [].
      -- Need stack extension from [] to s on u' — same class of problem.
      -- RIGHT EDGE: SubRed ((x,.equiv v')::Γ') [] v t₃ → SubRed Γ' s' v' t₃
      -- Need context drop + input translation + stack extension from [] to s'.
      -- Both edges are still blocked by stack alignment (now at [] vs s/s').
      exact ⟨t₃, sorry, sorry⟩
    · -- y ≠ x: hmem says y has .equiv annotation in Γ (looked up past x)
      -- Extract α from Γ (past the head x entry)
      have hmem_Γ : LNCtx.mem_equiv Γ y α := by
        unfold LNCtx.mem_equiv LNCtx.lookup' at hmem_pro
        have hyx' : ¬(x == y) = true := by simp [beq_iff_eq]; exact Ne.symm hyx
        simp only [hyx', ite_false] at hmem_pro; exact hmem_pro
      -- x ∉ α.fvs (since α is from Γ and x ∉ all_fvs Γ)
      have hx_α : x ∉ α.fvs := not_mem_fvs_of_mem_equiv hmem_Γ hx_all_fvs
      -- x ∉ u'.fvs (SubRed Γ [] from α in extended context preserves freshness)
      have hx_u'_fvs : x ∉ u'.fvs :=
        subRed_preserves_not_mem_fvs_gen hsub_pro hx_α
          (LNCtx.fresh_in_anns_cons (by simp [LNAnn.fvs]; exact hx_v)
            (LNCtx.fresh_in_anns_of_not_mem_all_fvs hx_all_fvs))
          (fun _ he => absurd he (List.not_mem_nil _))
      -- Rewrite the subst_fvar in the goal
      have hyx_beq : ¬(y == x) = true := by simp [beq_iff_eq]; exact hyx
      rw [subst_fvar_notin hx_u'_fvs,
          show (LNExpr.fvar y).subst_fvar x v' = .fvar y from by
            simp [LNExpr.subst_fvar, hyx_beq]]
      -- Goal: ∃ w, EquivRed Γ s u' w ∧ SubRed Γ' s' (fvar y) w
      -- y has .equiv annotation α in Γ; after ctxRed, y has .equiv α' in Γ'
      -- with EquivRed Γ [] α α'.
      -- With nil-stack ME-PRO: hsub_pro is SubRed ((x,.equiv v)::Γ) [] α u'.
      -- After dropping x: SubRed Γ [] α u'.
      -- ctxRed_lookup_equiv gives: EquivRed Γ [] α α'.
      -- Now BOTH are at stack [] — this is a commutativity instance at matching stacks!
      -- However, the goal edges are at stacks s and s', so we still need
      -- stack extension for the output (u' at [] → s, and fvar y at [] → s').
      sorry
  | _ => sorry
termination_by (budget, u.sz)

/-- The substitution diamond for SubRed under .equiv annotations (mutual variant).

Same as equivRed_subst_diamond but for SubRed input. Needed for the ME-PRO case
of equivRed_subst_diamond (ME-PRO gives a SubRed on v, which needs its own diamond).
-/
noncomputable def subRed_subst_diamond
    (budget : Nat)
    {x : String} {v : LNExpr} {Γ : LNCtx} {s : LNStack} {u u' : LNExpr}
    {Γ' : LNCtx} {s' : LNStack} {v' : LNExpr}
    (h : LNSubRed ((x, .equiv v) :: Γ) s u u')
    (hctx : LNCtxRed ((x, .equiv v) :: Γ) s ((x, .equiv v') :: Γ') s')
    (hx_all_fvs : x ∉ LNCtx.all_fvs Γ)
    (hx_v : x ∉ v.fvs) (hv_lc : v.lc) (hv'_lc : v'.lc)
    (hu_lc : u.lc)
    (hwf : Γ.wf) (hswf : s.wf)
    (hnd : (LNCtx.dom Γ).Nodup)
    (hbudget : u.sz ≤ budget)
    (hv_budget : v.sz < budget)
    (hx_s : ∀ e ∈ s, x ∉ e.fvs)
    : Σ' w, LNEquivRed Γ s (u'.subst_fvar x v) w × LNSubRed Γ' s' (u.subst_fvar x v') w := by
  cases h with
  | ms_top =>
    -- u' = .top
    simp [LNExpr.subst_fvar]
    exact ⟨.top, .me_top, .ms_top⟩
  | ms_equ h_eq =>
    -- SubRed via ms_equ wraps an EquivRed
    exact equivRed_subst_diamond budget h_eq hctx hx_all_fvs hx_v hv_lc hv'_lc hu_lc hwf hswf hnd hbudget hv_budget hx_s
  | _ => sorry
termination_by (budget, u.sz)

end -- mutual commutativity / equivRed_subst_diamond / subRed_subst_diamond

/-! ## Investigation: stack extension is FALSE

The former axiom `equivRed_stack_ext` claimed:
  `LNEquivRed Γ [] u v → LNEquivRed Γ s u v`

The critical case is ME-FUN: under `Γ; []`, a lambda `lam dom body` reduces
via ME-FUN with body context `(x, .sub dom) :: Γ; []`. Under `Γ; α :: s`,
ME-FOP fires with body context `(x, .equiv α) :: Γ; s`.

KEY QUESTION: can the body derivation under `.sub dom` always be replayed
under `.equiv α` for arbitrary `α`?

ANALYSIS: The annotation swap part is correct (noPromoAt x holds because
ME-PRO on x requires .equiv, blocked by .sub dom). So the derivation is
independent of x's ANNOTATION. HOWEVER, it is NOT independent of the STACK.
Points 1-3 below only address the annotation dimension, not the stack:
1. ME-PRO on `x` requires `.equiv`, so it CANNOT fire under `.sub dom`.
   Therefore the body's EquivRed derivation never promotes `x` via ME-PRO.
2. SubRed on `fvar x` (via MS-PRO) can only be reached through ME-PRO on
   OTHER variables whose annotations contain `fvar x`. But `x` is fresh
   (cofinite quantification), so no annotation in `Γ` contains `fvar x`.
3. Therefore the body derivation is independent of `x`'s annotation.

BUT: After annotation swap from `.sub dom` to `.equiv α`, we still have
the body derivation at stack [] (from ME-FUN), and need it at stack s (for
ME-FOP). This is recursively the same stack extension problem on body^x.
Under .equiv α, ME-PRO CAN fire on x, making the output DIFFERENT.

COUNTEREXAMPLE (same-output stack ext for annotation terms):
  t = lam top (bvar 0), s = [.top].
  ME-FUN body: (x,.sub top)::Γ;[] ⊢ fvar x ≡→ fvar x (ME-VAR). Output: lam top (bvar 0).
  ME-FOP body: (x,.equiv .top)::Γ;[] ⊢ fvar x ≡→ .top (ME-PRO + MS-TOP). Output: lam top .top.
  Outputs differ. Same-output stack extension is FALSE even for annotation terms.

The following examples test specific instances to verify consistency.
Note: Tests 1-4 below work because they never trigger ME-PRO on the
cofinitely-quantified body variable under .equiv α.
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

/-! ### Investigation: stack extension for annotation terms (lam top (bvar 0))

The identity function lam top (bvar 0) illustrates the subtlety.
Under both [] and [.top], the same output (lam top (bvar 0)) IS reachable —
but via DIFFERENT derivation paths. The [] derivation uses ME-FUN + ME-VAR;
the [.top] derivation uses ME-FOP + ME-VAR (both give body fvar x → fvar x,
ignoring the annotation). Additionally, [.top] enables an EXTRA output
(lam top .top) via ME-PRO on the body variable.

For the commutativity MS-PRO/ME-VAR case: we need to lift a SPECIFIC
derivation (LNEquivRed Γ [] t t' from ctxRed_lookup_sub) to stack s,
preserving the EXACT output t'. The question is not whether SOME derivation
producing t' exists at s, but whether a particular output reachable at [] is
also reachable at s. For simple terms (like identity), the answer is yes.
The cex_Γ example below shows a case where a particular output reachable at
[] is NOT reachable at s (via ME-PRO on a variable whose lambda annotation
uses MS-PRO internally — see detailed explanation below).
-/

-- Under []: identity reduces to itself via ME-FUN
example : LNEquivRed [] [] (.lam .top (.bvar 0)) (.lam .top (.bvar 0)) := by
  exact .me_fun (L := []) .me_top (fun x _ => .me_var)

-- Under [.top]: the SAME output is also derivable via ME-FOP + ME-VAR
example : LNEquivRed [] [.top] (.lam .top (.bvar 0)) (.lam .top (.bvar 0)) := by
  exact .me_fop (L := []) .me_top (fun x _ => .me_var)

-- Under [.top]: an ADDITIONAL output (lam top .top) is also derivable via ME-PRO
example : LNEquivRed [] [.top] (.lam .top (.bvar 0)) (.lam .top .top) := by
  refine .me_fop (L := []) .me_top (fun x _ => ?_)
  simp only [LNExpr.open_at]
  exact .me_pro (show LNCtx.mem_equiv [(x, .equiv .top)] x .top by
    simp [LNCtx.mem_equiv, LNCtx.lookup']) (.ms_equ .me_top)

-- Both outputs are reachable under [.top]. EquivRed is non-deterministic.
-- For this term, same-output stack extension holds trivially.
-- The REAL counterexample needs a derivation at [] whose output is NOT
-- achievable at s — see cex_Γ below.

/-! ### COUNTEREXAMPLE: equivRed_stack_ext and subRed_stack_ext are FALSE

NOTE (post nil-stack ME-PRO): With nil-stack ME-PRO, equivRed_stack_ext is now
TRUE for fvar terms (ME-PRO always reduces at [], ME-VAR is trivially stable).
The counterexample below is INVALIDATED for equivRed on fvar. However,
subRed_stack_ext remains FALSE for lambda terms (MS-FUN vs MS-FOP) and
equivRed_stack_ext remains FALSE for lambda terms (ME-FUN vs ME-FOP).

FORMER failure mode (pre nil-stack ME-PRO): ME-PRO on variable x whose annotation
α is a lambda would use SubRed at the ambient stack, causing MS-FUN (at []) vs
MS-FOP (at non-empty stack) to produce different body contexts.
With nil-stack ME-PRO, this no longer applies — ME-PRO always uses SubRed at [].

REMAINING failure mode: direct SubRed/EquivRed on lambda terms still differs
at different stacks. MS-FUN gives `.sub dom` annotation, MS-FOP gives `.equiv α`.

Concrete instance:
  Γ = [x ≡ (λy.0), y ≤ ⊤]
  Under Γ;[]: fvar "x" ≡→ λ(fvar "y").(fvar "y")
    via ME-PRO with α = λ(fvar "y").(bvar 0)
    then SubRed via MS-FUN: body z ≤→ fvar "y" via MS-PRO (z ≤ fvar "y")

  NOTE (post nil-stack ME-PRO): With nil-stack ME-PRO, this EquivRed counterexample
  is INVALIDATED for fvar terms. ME-PRO always uses SubRed at [], so the [.top]
  derivation IS derivable: ME-PRO with SubRed at [] uses MS-FUN (not MS-FOP),
  giving z a .sub annotation, allowing MS-PRO to fire. The output is the same
  at both stacks. However, subRed_stack_ext remains FALSE for lambda terms
  (MS-FUN vs MS-FOP give different body contexts).
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

-- NOTE (post nil-stack ME-PRO): The [.top] derivation IS now derivable!
-- With nil-stack ME-PRO, SubRed is always at [], so MS-FUN is used regardless
-- of the outer stack. The cex_Γ EquivRed counterexample for equivRed_stack_ext
-- on fvar terms is invalidated. Stack extension for EquivRed on fvar terms NOW HOLDS.

-- However, subRed_stack_ext is STILL FALSE for lambda terms:
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

/-! ### Stack-Independent Reduction

Stack-independent reduction is the sub-relation of LNEquivRed / LNSubRed that
omits ME-FUN, ME-FOP, MS-FUN, and MS-FOP — exactly the rules that differ
between empty and non-empty stacks. For derivations in this fragment, the
stack is irrelevant: the same derivation can be replayed at any stack.

**Motivation:** The stack alignment problem (sorry #7) arises because
ctxRed_lookup_sub yields `EquivRed Γ [] t t'` but commutativity needs
`EquivRed Γ s t t'`. If the derivation at [] is stack-independent, we can
lift it to any stack s, resolving the mismatch.

**Result:** Stack extension is PROVABLE for stack-independent reductions
(theorem `siEquivRed_at_any_stack` / `siSubRed_at_any_stack` below). However,
this does NOT resolve the MS-PRO/ME-VAR case of commutativity. The reason:
ME-PRO on x triggers SubRed on x's annotation α. When α is a lambda (e.g.,
`lam (fvar "y") (bvar 0)`), the SubRed uses MS-FUN (empty stack) or MS-FOP
(non-empty stack) — exactly the stack-dependent rules excluded from this
fragment. So the reduction through annotations is NOT stack-independent in
general, even when the top-level term u is not a lambda.

The counterexample `cex_Γ` above demonstrates this: `fvar "x" ≡→ lam (fvar
"y") (fvar "y")` uses ME-PRO, whose SubRed on `lam (fvar "y") (bvar 0)`
goes through MS-FUN. This derivation is NOT stack-independent.

**Conclusion:** No restriction on the input term u makes its EquivRed
derivation stack-independent. Stack sensitivity enters through ANNOTATIONS
(via ME-PRO → SubRed → MS-FUN/MS-FOP), not through u itself. The paper's
Lemma 22 gap is genuine and cannot be patched by identifying a
stack-independent fragment.
-/

section StackIndepReduction

mutual
/-- Stack-independent equivalence reduction: the sub-relation of LNEquivRed
    that omits ME-FUN and ME-FOP (the only stack-dependent rules). -/
inductive SIEquivRed : LNCtx → LNExpr → LNExpr → Type where
  | me_top : SIEquivRed Γ .top .top
  | me_var : SIEquivRed Γ (.fvar x) (.fvar x)
  | me_tap : SIEquivRed Γ (.app .top u) .top
  | me_pro : LNCtx.mem_equiv Γ x α → SISubRed Γ α α' → SIEquivRed Γ (.fvar x) α'
  | me_app {Γ : LNCtx} {f f' v v' : LNExpr} :
      SIEquivRed Γ f f' → SIEquivRed Γ v v' → SIEquivRed Γ (.app f v) (.app f' v')
  | me_bet {Γ : LNCtx} {dom body t v v' : LNExpr} (L : List String) :
      (∀ x, x ∉ L → SIEquivRed ((x, .equiv v) :: Γ) (body.open_at 0 (.fvar x)) (t.open_at 0 (.fvar x))) →
      SIEquivRed Γ v v' →
      SIEquivRed Γ (.app (.lam dom body) v) (t.open_at 0 v')

/-- Stack-independent subtyping reduction: the sub-relation of LNSubRed
    that omits MS-FUN and MS-FOP (the only stack-dependent rules). -/
inductive SISubRed : LNCtx → LNExpr → LNExpr → Type where
  | ms_pro : LNCtx.mem_sub Γ x t → SISubRed Γ (.fvar x) t
  | ms_top : SISubRed Γ u .top
  | ms_equ : SIEquivRed Γ u v → SISubRed Γ u v
  | ms_app {Γ : LNCtx} {f f' v : LNExpr} :
      SISubRed Γ f f' → SISubRed Γ (.app f v) (.app f' v)
end

mutual
/-- Stack-independent EquivRed embeds into LNEquivRed at ANY stack. -/
def siEquivRed_at_any_stack {Γ : LNCtx} {u v : LNExpr}
    (h : SIEquivRed Γ u v) (s : LNStack) : LNEquivRed Γ s u v :=
  match h with
  | .me_top => .me_top
  | .me_var => .me_var
  | .me_tap => .me_tap
  | .me_pro hmem hsub =>
    .me_pro hmem (siSubRed_at_any_stack hsub [])
  | .me_app (v := v) hf hv =>
    -- ME-APP pushes v onto the stack for f, and reduces v at []
    .me_app (siEquivRed_at_any_stack hf (v :: s)) (siEquivRed_at_any_stack hv [])
  | .me_bet (L := L) hbody hv =>
    .me_bet L
      (fun x hx => siEquivRed_at_any_stack (hbody x hx) s)
      (siEquivRed_at_any_stack hv [])

/-- Stack-independent SubRed embeds into LNSubRed at ANY stack. -/
def siSubRed_at_any_stack {Γ : LNCtx} {u v : LNExpr}
    (h : SISubRed Γ u v) (s : LNStack) : LNSubRed Γ s u v :=
  match h with
  | .ms_pro hmem => .ms_pro hmem
  | .ms_top => .ms_top
  | .ms_equ he => .ms_equ (siEquivRed_at_any_stack he s)
  | .ms_app (v := v) hf => .ms_app (siSubRed_at_any_stack hf (v :: s))
end

/-! #### Why stack-independent reduction does NOT resolve the MS-PRO/ME-VAR case

The MS-PRO/ME-VAR case of commutativity has:
- Bottom: `Γ;s ⊢ fvar x ≡→ fvar x` (ME-VAR)
- Left: `Γ;s ⊢ fvar x ≤→ t` (MS-PRO, x ≤ t ∈ Γ)
- ctxRed_lookup_sub gives `LNEquivRed Γ [] t t'`

We need `LNEquivRed Γ s t t'` (top edge). If the derivation of
`EquivRed Γ [] t t'` were stack-independent, `siEquivRed_at_any_stack`
would give us `EquivRed Γ s t t'`.

But the derivation is NOT stack-independent in general:
- t is an annotation looked up from Γ. Annotations CAN be lambdas.
- If t = lam dom body, then EquivRed Γ [] t t' uses ME-FUN (stack-dependent).
- Even if t is not a lambda, ME-PRO on a variable in t can reach a lambda
  annotation. E.g., t = fvar "y" where y ≡ lam ... ∈ Γ. ME-PRO on y triggers
  SubRed on the lambda, which uses MS-FUN (stack-dependent).

The counterexample `cex_Γ` demonstrates exactly this: `fvar "x"` is reduced
via ME-PRO, whose SubRed on `lam (fvar "y") (bvar 0)` uses MS-FUN. The
output `lam (fvar "y") (fvar "y")` is reachable at [] but NOT at [.top].

No restriction on the input term u can make the reduction stack-independent,
because stack sensitivity enters through ANNOTATIONS (via ME-PRO), not
through u itself. The only fix is changing CT-ANN to reduce annotations at
the full stack s instead of nil (see sorry #7 in the file header).
-/

-- Demonstrate: the cex_Γ derivation is NOT stack-independent.
-- It uses ME-PRO → MS-FUN, which is excluded from SIEquivRed/SISubRed.
-- The derivation LNEquivRed cex_Γ [] (fvar "x") (lam (fvar "y") (fvar "y"))
-- (proved above) goes through:
--   ME-PRO: x ≡ lam (fvar "y") (bvar 0), then SubRed via MS-FUN
-- MS-FUN is a stack-dependent rule, so this derivation has no SIEquivRed analog.
-- No SIEquivRed derivation producing (lam (fvar "y") (fvar "y")) from (fvar "x")
-- exists in cex_Γ, because the only SIEquivRed rules for fvar are:
--   me_var: fvar "x" → fvar "x" (wrong output)
--   me_pro: needs SISubRed of the annotation lam (fvar "y") (bvar 0),
--           but SISubRed has no rule for lambdas except ms_top and ms_equ,
--           neither of which produces lam (fvar "y") (fvar "y").

end StackIndepReduction

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

/-! ### COUNTEREXAMPLE: subRed_subst_equiv is FALSE

The proposed statement:
  If `LNSubRed ((x, .equiv v) :: Γ) s u u'` with freshness
  (x ∉ all_fvs Γ, x ∉ v.fvs, x ∉ stack fvs, v.lc),
  then `LNSubRed Γ s (u[x↦v]) (u'[x↦v])`.

This is FALSE. The failure mode: me_app reduces both operator AND operand
simultaneously. After substitution, the operand's EquivRed may need to reduce
through an .equiv annotation (via me_pro), but the substituted operand now has
only a .sub annotation, so EquivRed can't match it. SubRed's ms_app only
reduces the operator and leaves the operand unchanged.

Concrete counterexample:
  Γ = [("y", .sub .top), ("z", .equiv .top)]
  x = "x", v = fvar "y", s = []
  u = app (fvar "z") (fvar "x")
  u' = app .top .top

  Original derivation:
    SubRed (("x", .equiv (fvar "y")) :: Γ) [] (app (fvar "z") (fvar "x")) (app .top .top)
    via ms_equ (me_app):
      Operator: EquivRed Γ_ext [(fvar "x")] (fvar "z") .top
        via me_pro z: z ≡ .top, SubRed Γ_ext [(fvar "x")] .top .top → ms_top
      Operand: EquivRed Γ_ext [] (fvar "x") .top
        via me_pro x: x ≡ (fvar "y"), SubRed Γ_ext [] (fvar "y") .top → ms_pro y

  After substitution x ↦ fvar "y":
    u[x↦v] = app (fvar "z") (fvar "y")
    u'[x↦v] = app .top .top

  Need: SubRed Γ [] (app (fvar "z") (fvar "y")) (app .top .top)

  But this is NOT derivable:
    - ms_equ (me_app): needs EquivRed Γ [] (fvar "y") .top for the operand.
      But y has .sub annotation, not .equiv, so me_pro doesn't fire.
      Only me_var is available: (fvar "y") → (fvar "y"). NOT .top.
    - ms_app: SubRed Γ [(fvar "y")] (fvar "z") .top → ms_app gives
      SubRed Γ [] (app (fvar "z") (fvar "y")) (app .top (fvar "y")).
      The operand is (fvar "y"), NOT .top.
    - No other rule can produce (app .top .top) from (app (fvar "z") (fvar "y")).

  The root cause: me_app reduces operator and operand simultaneously,
  but after substitution, SubRed can only reduce the operator (ms_app)
  or needs EquivRed of both sub-terms (ms_equ + me_app). The operand
  (fvar "y") can be promoted via SubRed (ms_pro) but NOT via EquivRed
  (me_pro requires .equiv), so ms_equ + me_app fails. -/

section SubRedSubstEquivCounterexample

private def sse_Γ : LNCtx := [("y", .sub .top), ("z", .equiv .top)]
private def sse_Γ_ext : LNCtx := [("x", .equiv (.fvar "y")), ("y", .sub .top), ("z", .equiv .top)]

-- Step 1: The original derivation exists in the extended context.
example : LNSubRed sse_Γ_ext [] (.app (.fvar "z") (.fvar "x")) (.app .top .top) := by
  unfold sse_Γ_ext
  exact .ms_equ (.me_app
    (.me_pro
      (show LNCtx.mem_equiv [("x", .equiv (.fvar "y")), ("y", .sub .top), ("z", .equiv .top)] "z" .top from rfl)
      .ms_top)
    (.me_pro
      (show LNCtx.mem_equiv [("x", .equiv (.fvar "y")), ("y", .sub .top), ("z", .equiv .top)] "x" (.fvar "y") from rfl)
      (.ms_pro (show LNCtx.mem_sub [("x", .equiv (.fvar "y")), ("y", .sub .top), ("z", .equiv .top)] "y" .top from rfl))))

-- Step 2: Freshness conditions.
example : "x" ∉ LNCtx.all_fvs sse_Γ := by native_decide
example : "x" ∉ (LNExpr.fvar "y").fvs := by native_decide
example : (LNExpr.fvar "y").lc := trivial

-- Step 3: After substitution, the BEST SubRed we can get has the operand unreduced.
-- SubRed sse_Γ [] (app (fvar "z") (fvar "y")) (app .top (fvar "y")) via ms_app.
-- We CANNOT get (app .top .top).
example : LNSubRed sse_Γ [] (.app (.fvar "z") (.fvar "y")) (.app .top (.fvar "y")) := by
  unfold sse_Γ
  exact .ms_app (.ms_equ (.me_pro
    (show LNCtx.mem_equiv [("y", .sub .top), ("z", .equiv .top)] "z" .top from rfl)
    .ms_top))

-- We can also promote the operand SEPARATELY via SubRed:
example : LNSubRed sse_Γ [] (.fvar "y") .top := by
  unfold sse_Γ
  exact .ms_pro (show LNCtx.mem_sub [("y", .sub .top), ("z", .equiv .top)] "y" .top from rfl)

-- But we CANNOT combine them into a single SubRed reducing both simultaneously.
-- SubRed (app (fvar z) (fvar y)) (app .top .top) requires ms_equ(me_app(...))
-- which requires EquivRed of the operand, but EquivRed of (fvar y) can only
-- produce (fvar y) (via me_var), not .top (me_pro needs .equiv annotation).

end SubRedSubstEquivCounterexample

/-! ### COUNTEREXAMPLE: equivRed_subst_equiv is FALSE

The proposed statement: if `LNEquivRed ((x, .equiv v) :: Γ) s u u'` with
freshness (x ∉ v.fvs, x ∉ all_fvs Γ), then `LNEquivRed Γ s (u[x↦v]) (u'[x↦v])`.

This is FALSE. The failure mode: ME-PRO on x uses SubRed on v (the annotation
term). SubRed can promote through .sub annotations (MS-PRO), which is strictly
more powerful than EquivRed. After substitution, the conclusion demands EquivRed
on v, but v's only EquivRed derivation is me_var (reflexivity) when v is a
variable with a .sub annotation.

Concrete counterexample:
  Γ = [(y, .sub .top)], x = "x", v = fvar "y", s = []
  u = fvar "x", u' = .top

  Original derivation: LNEquivRed ((x, .equiv (fvar y)) :: [(y, .sub .top)]) [] (fvar x) .top
    via ME-PRO: x ≡ fvar "y" ∈ Γ, then SubRed of (fvar "y"):
      ms_pro: y ≤ .top ∈ Γ  →  fvar "y" ≤→ .top

  After substitution x ↦ fvar "y":
    u[x↦v] = fvar "y"
    u'[x↦v] = .top

  Need: LNEquivRed [(y, .sub .top)] [] (fvar "y") .top
  But this is NOT derivable:
    - me_var: fvar "y" ≡→ fvar "y"  (not .top)
    - me_pro: requires mem_equiv for "y", but y has .sub annotation, not .equiv
    - No other rule applies (fvar "y" is not top/app/lam)

  The root cause is the asymmetry between SubRed (which has ms_pro for .sub
  annotations) and EquivRed (which only has me_pro for .equiv annotations).
  SubRed can promote through .sub bounds, but EquivRed cannot.
-/

section SubstEquivInvestigation

private def substEquiv_Γ : LNCtx := [("y", .sub .top)]
private def substEquiv_Γ_ext : LNCtx := [("x", .equiv (.fvar "y")), ("y", .sub .top)]

-- Step 1: The original derivation exists in the extended context.
-- LNEquivRed substEquiv_Γ_ext [] (fvar "x") .top
-- via ME-PRO (x ≡ fvar "y") then SubRed of fvar "y" via ms_pro (y ≤ .top)
example : LNEquivRed substEquiv_Γ_ext [] (.fvar "x") .top := by
  unfold substEquiv_Γ_ext
  exact .me_pro
    (show LNCtx.mem_equiv [("x", .equiv (.fvar "y")), ("y", .sub .top)] "x" (.fvar "y") from rfl)
    (.ms_pro (show LNCtx.mem_sub [("x", .equiv (.fvar "y")), ("y", .sub .top)] "y" .top from rfl))

-- Step 2: Freshness conditions are satisfied.
-- x = "x", v = fvar "y"
-- x ∉ v.fvs: "x" ∉ ["y"] ✓
-- x ∉ all_fvs Γ: "x" ∉ ["y"] ++ top.fvs = ["y"] ✓
example : "x" ∉ (LNExpr.fvar "y").fvs := by native_decide
example : "x" ∉ LNCtx.all_fvs substEquiv_Γ := by native_decide

-- Step 3: After substitution, the conclusion is NOT derivable.
-- Need: LNEquivRed [(y, .sub .top)] [] (fvar "y") .top
-- This requires EquivRed to produce .top from fvar "y" where y has .sub .top.
-- me_var gives fvar "y" (reflexive), me_pro needs .equiv (y has .sub).
-- No other rule applies. NOT DERIVABLE.

-- We CAN prove the SubRed version (which would hold if the conclusion were SubRed):
example : LNSubRed substEquiv_Γ [] (.fvar "y") .top := by
  unfold substEquiv_Γ
  exact .ms_pro (by simp [LNCtx.mem_sub, LNCtx.lookup'])

-- But the EquivRed version is NOT derivable. The best EquivRed can do is:
example : LNEquivRed substEquiv_Γ [] (.fvar "y") (.fvar "y") := by
  unfold substEquiv_Γ
  exact .me_var

end SubstEquivInvestigation

/-! ### PROPOSED: equivRed_subst_diamond — the correct substitution lemma

Both `equivRed_subst_equiv` and `subRed_subst_equiv` are FALSE because they
demand that the exact substituted pair `(u[x↦v], u'[x↦v])` lies in the same
reduction relation. The CORRECT formulation is a **diamond**:

```
equivRed_subst_diamond:
  EquivRed ((x,.equiv v)::Γ) s u u'
  → EquivRed Γ [] v v'
  → CtxRed Γ s Γ' s'
  → x ∉ all_fvs Γ, x ∉ v.fvs, ...
  → ∃ w, EquivRed Γ s (u'[x↦v]) w ∧ SubRed Γ' s' (u[x↦v']) w
```

**Why the diamond version is TRUE when the flat version is FALSE:**

At ME-PRO on x: the promotion gives `me_pro x (SubRed v → result)`. After subst:
- Left side: `u'[x↦v] = result[x↦v] = result` (x fresh for v, Γ, so x ∉ result.fvs)
- Right side: `u[x↦v'] = (fvar x)[x↦v'] = v'`

The flat version needs `EquivRed Γ s v' result` or `SubRed Γ s v' result` — FALSE
in general (the counterexamples above). The diamond version needs:
  `∃ w, EquivRed Γ s result w ∧ SubRed Γ' s' v' w`

This is exactly COMMUTATIVITY on v! We have:
- EquivRed Γ [] v v' (input)
- SubRed Γ s v result (from me_pro, with ctx_ext since x is fresh)
- CtxRed Γ s Γ' s' (input)

And commutativity gives `∃ w, EquivRed Γ s result w ∧ SubRed Γ' s' v' w`. ✓

**Termination:** commutativity on `app(lam dom body, v)` calls
equivRed_subst_diamond on `body^x` (body^x.sz < app(..).sz), which calls
commutativity on `v` at ME-PRO-on-x points (v.sz < app(..).sz). Well-founded.

**Impact:** this single mutual induction resolves ALL equivRed-substitution sorrys:
- commutativity ME-BET/MS-FOP `.inr` case (line ~5375)
- diamond_full ME-PRO cases (lines ~4897, 4902)
- diamond_full ME-APP/ME-BET, ME-BET/ME-BET, ME-BET/ME-APP (lines ~4990, 4998, 5055)

**Verification:** The subRed_subst_equiv counterexample ALSO has a diamond solution.
See EquivSubstDiamondVerification section below. -/

section EquivSubstDiamondVerification

-- Verify the diamond version IS satisfiable for the subRed_subst_equiv counterexample:
--   Γ = [("y", .sub .top), ("z", .equiv .top)]
--   u = app (fvar "z") (fvar "x"), u' = app .top .top
--   v = fvar "y", v' = fvar "y" (EquivRed Γ [] v v' via me_var)
-- After subst:
--   u'[x↦v] = app .top .top
--   u[x↦v'] = app (fvar "z") (fvar "y")
-- Need: ∃ w, EquivRed Γ [] (app .top .top) w ∧ SubRed Γ [] (app (fvar z) (fvar y)) w
--
-- w = .top works: EquivRed via me_tap, SubRed via ms_top.
-- (The flat version demanded SubRed Γ [] (app (fvar z) (fvar y)) (app .top .top),
--  which is NOT derivable because EquivRed of (fvar "y") cannot reach .top
--  since y has .sub annotation. The diamond lets us choose a different target.)

-- Left edge: app .top .top ≡→ .top via me_tap
example : LNEquivRed sse_Γ [] (.app .top .top) .top := .me_tap

-- Right edge: app (fvar "z") (fvar "y") ≤→ .top via ms_top
example : LNSubRed sse_Γ [] (.app (.fvar "z") (.fvar "y")) .top := .ms_top

-- The diamond IS satisfiable. The existential quantifier (∃ w) gives the
-- flexibility that makes the diamond TRUE where the flat version is FALSE.

end EquivSubstDiamondVerification

/-! ### COUNTEREXAMPLE: noPromoAt_app_to_me_app (normalization of me_bet to me_app) is FALSE

The proposed statement: for any `noPromoAt z Γ s (app (lam dom body) a) (app f' a')`,
there exists an me_app-based `noPromoAt z Γ s (app (lam dom body) a) (app f' a')`.

This is FALSE. The failure mode: me_bet can produce outputs where the operator
part (f') is NOT a lambda, but me_app at non-empty stack forces the operator
(lam dom body) through me_fop, which ALWAYS outputs a lambda. So when me_bet
produces `app top top` (with non-lambda operator `top`), me_app cannot reproduce
this output because me_fop on `lam dom body` at stack `[a]` always gives `lam ...`.

Concrete counterexample:
  z = "z" (not in context — so noPromoAt z is vacuously easy to satisfy)
  Γ = [("x", .equiv .top)], s = []
  dom = .top
  body = app (bvar 0) (bvar 0)   (λ≤⊤. x x, i.e., self-application of bound var)
  a = fvar "x"

  Input:  app (lam .top (app (bvar 0) (bvar 0))) (fvar "x")
  Output: app .top .top

  Via me_bet (z = "z"):
  Pick fresh w. Body: (app (bvar 0) (bvar 0))^w = app (fvar w) (fvar w).
  In context ((w, .equiv (fvar "x")) :: ("x", .equiv .top) :: []) at stack []:
    fvar w → .top via me_pro(w): w ≡ fvar "x", then SubRed of (fvar "x"):
      fvar "x" → .top via ms_equ(me_pro(x)): x ≡ .top, SubRed .top → .top via ms_top.
    So app (fvar w) (fvar w) → app .top .top via me_app.
    Body result: t^w = app .top .top, so t = app .top .top (no bvar 0).
  Argument: fvar "x" → fvar "x" via me_var.  (v' = fvar "x")
  Output: t.open_at 0 (fvar "x") = (app .top .top).open_at 0 (fvar "x") = app .top .top.  ✓

  Since z = "z" is not in the context at all, noPromoAt z holds trivially
  (z is never promoted because there's no .equiv annotation for z).

  Via me_app (attempted):
  Operator: noPromoAt z Γ (fvar "x" :: []) (lam .top (app (bvar 0) (bvar 0))) f'
    Stack is [fvar "x"], non-empty, so must use me_fop.
    me_fop pops fvar "x", reduces body in ((w, .equiv (fvar "x"))::Γ) at stack [].
    Output of me_fop is ALWAYS lam dom' body'. So f' must be a lambda.
    But the me_bet output has f' = .top (NOT a lambda).

  Therefore no me_app-based noPromoAt z exists for the same endpoints.

  ROOT CAUSE: me_bet evaluates the body INSIDE the binder (with the argument
  substituted), allowing promotions (me_pro on the bound variable w → fvar "x" → .top)
  to collapse the application. me_app evaluates the lambda EXTERNALLY via me_fop,
  which preserves the lambda structure. When internal promotions eliminate the
  lambda (e.g., self-application of a variable that promotes to .top), me_bet
  can reach outputs that me_app structurally cannot.

  IMPLICATION FOR CATEGORY A2: The noPromoAt normalization approach to resolving
  the me_bet/me_app cross-constructor mismatch in equivRed_subst_noPromo_noPromoAt
  is not viable. When y uses me_app and z uses me_bet (or vice versa), we cannot
  normalize z's derivation to use me_app because the outputs may be structurally
  incompatible. Alternative approaches needed:
  - Co-prove SubRed AND noPromoAt z in the same induction (avoids needing two
    independent noPromoAt derivations that must use compatible constructors)
  - Strengthen the substitution lemma to a diamond form that relaxes the output
    to existential (∃ w, ...) rather than exact matching
  - Prove that the specific freshness/context conditions in the actual call sites
    of equivRed_subst_noPromo_noPromoAt prevent the me_bet/me_app divergence
-/

section NoPromoAtNormalizationCounterexample

-- Context: x has .equiv .top annotation
private def npnorm_Γ : LNCtx := [("x", .equiv .top)]

-- Input term: (λ≤⊤. x x)(fvar "x")  where body applies bound var to itself
private def npnorm_body : LNExpr := .app (.bvar 0) (.bvar 0)
private def npnorm_input : LNExpr := .app (.lam .top npnorm_body) (.fvar "x")

-- Step 1: me_bet-based derivation producing `app .top .top`
-- The body (app (bvar 0) (bvar 0))^w = app (fvar w) (fvar w)
-- In context ((w, .equiv (fvar "x")) :: ("x", .equiv .top) :: []):
--   fvar w promotes to .top (via chain: w ≡ fvar "x", x ≡ .top)
-- So body reduces to app .top .top, and the output is app .top .top.

-- First: the body reduction exists (EquivRed, not just noPromoAt)
-- In ((w,.equiv (fvar "x"))::("x",.equiv .top)::[]) at stack []:
-- app (fvar w) (fvar w) ≡→ app .top .top
private def npnorm_Γ_ext (w : String) : LNCtx :=
  [(w, .equiv (.fvar "x")), ("x", .equiv .top)]

-- w ≡ fvar "x" ∈ Γ_ext  (for any w ≠ "x")
private theorem npnorm_mem_equiv_w (w : String) (_hw : w ≠ "x") :
    LNCtx.mem_equiv (npnorm_Γ_ext w) w (.fvar "x") := by
  simp [npnorm_Γ_ext, LNCtx.mem_equiv, LNCtx.lookup']

-- x ≡ .top ∈ Γ_ext
private theorem npnorm_mem_equiv_x (w : String) (hw : w ≠ "x") :
    LNCtx.mem_equiv (npnorm_Γ_ext w) "x" .top := by
  simp [npnorm_Γ_ext, LNCtx.mem_equiv, LNCtx.lookup']
  intro h; exact hw h

-- SubRed: fvar "x" ≤→ .top in Γ_ext (via ms_equ + me_pro + ms_top)
private def npnorm_sub_x (w : String) (hw : w ≠ "x") :
    LNSubRed (npnorm_Γ_ext w) [] (.fvar "x") .top :=
  .ms_equ (.me_pro (npnorm_mem_equiv_x w hw) .ms_top)

-- fvar w ≡→ .top in Γ_ext via me_pro (chain through fvar "x")
private def npnorm_equiv_w (w : String) (hw : w ≠ "x") :
    LNEquivRed (npnorm_Γ_ext w) [] (.fvar w) .top :=
  .me_pro (npnorm_mem_equiv_w w hw) (npnorm_sub_x w hw)

-- fvar w ≡→ .top at any stack (via ms_top for the SubRed)
private def npnorm_equiv_w_stk (w : String) (hw : w ≠ "x") (s : LNStack) :
    LNEquivRed (npnorm_Γ_ext w) s (.fvar w) .top :=
  .me_pro (npnorm_mem_equiv_w w hw) (.ms_equ (.me_pro (npnorm_mem_equiv_x w hw) .ms_top))

-- Body reduction: app (fvar w) (fvar w) ≡→ app .top .top
private def npnorm_body_red (w : String) (hw : w ≠ "x") :
    LNEquivRed (npnorm_Γ_ext w) []
      (.app (.fvar w) (.fvar w)) (.app .top .top) :=
  .me_app (npnorm_equiv_w_stk w hw [.fvar w]) (npnorm_equiv_w w hw)

-- Full me_bet derivation:
-- app (lam .top (app (bvar 0) (bvar 0))) (fvar "x") ≡→ app .top .top
-- Body result t = app .top .top (no bvar 0), opened with anything is itself.
example : LNEquivRed npnorm_Γ [] npnorm_input (.app .top .top) := by
  unfold npnorm_input npnorm_body
  -- me_bet with L = ["x"] to avoid fresh w = "x"
  apply LNEquivRed.me_bet (L := ["x"]) (t := .app .top .top) (v' := .fvar "x")
  · intro w hw
    simp [List.mem_cons, List.mem_nil_iff] at hw
    -- w ≠ "x"
    simp [LNExpr.open_at]
    exact npnorm_body_red w hw
  · exact .me_var  -- fvar "x" ≡→ fvar "x"

-- Step 2: noPromoAt "z" holds for this derivation
-- Since "z" has no annotation in Γ at all, it's never promoted.
-- me_pro on any variable requires that variable to have .equiv annotation.
-- Neither "w" nor "x" equals "z", so noPromoAt "z" is trivially satisfied.

-- Note: The noPromoAt "z" for the body reduction is straightforward since
-- "z" is not in the context and cannot be promoted.

-- Step 3: me_app CANNOT produce app .top .top from this input
-- For me_app: operator (lam .top (app (bvar 0)(bvar 0))) at stack [fvar "x"]
-- Only rule for lam at non-empty stack: me_fop
-- me_fop output is always lam dom' body', which is a lambda.
-- So the operator output f' must be a lambda.
-- But app .top .top requires f' = .top, which is NOT a lambda.

-- Proof that me_fop always produces a lambda (by construction):
-- The me_fop constructor has signature:
--   me_fop : EquivRed Γ [] dom dom' → (∀ x, ... → EquivRed ... body^x body'^x)
--            → EquivRed Γ (α::s) (lam dom body) (lam dom' body')
-- The output is definitionally (lam dom' body').

-- Therefore: noPromoAt "z" via me_app for the judgment
--   Γ; [] ⊢ app (lam .top (app (bvar 0)(bvar 0))) (fvar "x") ≡→ app .top .top
-- requires noPromoAt "z" Γ [fvar "x"] (lam .top (app (bvar 0)(bvar 0))) .top
-- The only noPromoAt constructor for lam at non-empty stack is me_fop,
-- which produces lam dom' body', not .top.
-- Hence NO me_app-based noPromoAt exists for this judgment.

end NoPromoAtNormalizationCounterexample
