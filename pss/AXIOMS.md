# Axioms

This formalization mechanizes Pasquale & García-Pérez (arXiv 2407.13882
v2, December 2025), the MPSS Krivine-style reformulation of Hutchins'
Pure Subtype Systems. Type safety (Theorems 4 and 5) is conditional on
the axioms below.

**Total axiom count: 11** (1 permanent, 9 active outstanding, 1 inactive
outstanding).

**Post Type-LC refactor (Option B, branch `type-lc-experiment`):**
`avoidsPro_refl` (axiom #12 in the original audit) was discharged to a
real theorem in commit `64162c2` after lifting `Term.LC` from `Prop` to
`Type`. The 5 active β-residual axioms (#6, #7, #8, #9, #10) remain
because they require restructuring `Lemma_2_DiamondMEqRed_core`'s
induction scheme to a lex measure on `(Term.size t₀, avoidsPro-count)`
— a separate, multi-day refactor. The Type-LC refactor was the
prerequisite for that work but does not by itself complete it.

### Discharge plan for the β-residuals (post-Type-LC, next-session targets)

The β-residuals have a single shared blocker: `_core`'s `induction h₁`
fixes the IHs at the source-derivation's stack, which prevents the
App×App and β-step arms from cleanly closing across stack-head shifts
and term-substitutions. Concrete plan:

1. **`MEqRed.equ_head_replace` (new lemma).** Given `MEqRed (⟨y, α,
   .equ⟩ :: Γ) s u u'`, `MEqRed Γ [] α α'`, AND `avoidsPro h y = true`,
   produce `MEqRed (⟨y, α', .equ⟩ :: Γ) s u u'`. Structural recursion;
   `Me-Pro` arm is the discharge site for the `avoidsPro` premise (when
   `Me-Pro` looks up `equBinds y α`, the avoidsPro witness rules out
   `y = name-being-promoted`). With `avoidsPro_refl` now a real
   theorem, the closing tree's `MEqRed.refl` invocations satisfy
   `avoidsPro = true` automatically. Estimated ~150-200 lines.

2. **`MEqRed.stack_head_replace` (new lemma).** Given
   `MEqRed Γ (α :: s) u u'` and `MEqRed Γ [] α α'`, produce
   `MEqRed Γ (α' :: s) u u'`. Structural recursion; the `fOp` arm
   reduces to `MEqRed.equ_head_replace` (item 1) since the body's
   `.equ` head is `α`. Estimated ~100 lines on top of item 1.

3. **`Lemma_2_DiamondMEqRed_ctx_axiom` (single-step Ct-Stk discharge).**
   With items 1 and 2, the App×App `_inline_app` arm's use of
   `_ctx_axiom` (which is exactly a single Ct-Stk step) becomes
   directly provable: apply `MEqRed.stack_head_replace` to lift
   `hu'_w` and `hu₂_w` from stack `(v::s)` to stacks `(v'::s)` and
   `(v₂::s)` respectively. Eliminates `_ctx_axiom` from `_core`'s
   closure, which removes it from Theorems 3, 4, Lemma 1 / 2 closures.

4. **β-residual axioms (#6, #9, #10).** Threading the moreover-clause
   through `_core`'s App×App, App×Bet, Bet×* arms requires
   restructuring `_core` to either (a) thread an `avoidsPro` premise
   through every constructor case, OR (b) compute the moreover-clause
   as a separate property of `_core`'s output via a second induction.
   Path (b) is cleaner but requires items 1-3 to be in place first
   (the closing arms of `_core` invoke `MEqRed.refl`, whose `avoidsPro`
   is now `true` thanks to `avoidsPro_refl`). Estimated ~500-1000
   lines combined.

5. **`Lemma_1_inline_app_bet_residual` (#7) and `Lemma_1_ctx_axiom`
   (#6).** Mirror of the Lemma 2 work for the strong-commutativity
   diagram. Same approach with MSubRed in place of one of the MEqRed.

The `_inline_app`'s App×App use of `_ctx_axiom` is the single highest-
leverage target: discharging it (via items 1-3) eliminates
`_ctx_axiom` from ALL headline theorem closures (it remains only in
the explicit `Lemma_2_DiamondMEqRed_general` form which is paper-API
boilerplate, not a headline).

> "Active" = currently in the transitive `#print axioms` dependency list
> of at least one headline theorem (Theorem 3, 4, 5; Lemma 1; Lemma 2).
> "Inactive" = no headline theorem depends on it; retained for
> documentation / paper-faithfulness / partial-discharge reasoning.

Run `nix develop --command lake build Pss.Sanity` to regenerate the
per-theorem dependency lists below.

---

## Headline theorem axiom dependencies (current)

The kernel axioms `propext`, `Quot.sound`, `Classical.choice` are common
to all five and elided below.

### `Theorem_3_TransitivityIsAdmissible`

* `Pss.Lemma_24_NarrowingMSubRed`
* `Pss.Lemma_1_ctx_axiom` *(private)*
* `Pss.Lemma_1_inline_app_bet_residual` *(private)*
* `Pss.Lemma_2_DiamondMEqRed_ctx_axiom` *(private)*
* `Pss.Lemma_2_inline_app_bet_residual_axiom` *(private)*
* `Pss.Lemma_2_inline_bet_residual_axiom` *(private)*

### `Theorem_4_Progress`

Same as Theorem 3 (Theorem 4 routes through transitivity-elim).

### `Theorem_5_Preservation`

* `Pss.Lemma_10_Inversion`
* `Pss.Lemma_24_NarrowingMSubRed`
* `Pss.Lemma_30_msPro_x_axiom`
* `Pss.Proposition_17_beta_axiom`

(Note: Theorem 5 does NOT depend on `Conjecture_8_*`, on
`Lemma_1_ctx_axiom`, or on the Lemma-2 residuals. The Wave-7 discharge
of Lemma 7 routes around Conjecture 8 via the WfM/WSubM/WSubMStar
mutual recursor.)

### `Lemma_1_StrongCommutativity`

Same as Theorem 3.

### `Lemma_2_DiamondMEqRed`

* `Pss.Lemma_2_DiamondMEqRed_ctx_axiom` *(private)*
* `Pss.Lemma_2_inline_app_bet_residual_axiom` *(private)*
* `Pss.Lemma_2_inline_bet_residual_axiom` *(private)*

---

## Permanent (paper-conjecture status)

### 1. `Conjecture_8_WellSubtypingContextIndependent`

* **File:** `Pss/Mpss/TypeSafety.lean`, line 141.
* **Statement (verbatim from paper p. 13):** For `Γ ⊢ u ≤*_wf t`, any
  covariant context `Co` such that both `Co[u]` and `Co[t]` are
  well-formed in `Γ` satisfies `Γ ⊢ Co[u] ≤*_wf Co[t]`.
* **Status:** Permanent. Open conjecture in the source paper; we mirror
  its open status here.
* **Paper:** Pasquale & García-Pérez 2024, §4 p. 13 (Conjecture 8).
* **Activity:** Currently UNUSED by any headline theorem. Wave 7's
  discharge of `Lemma_7_SubstitutionPreservesWf` was reworked to route
  around it via direct IH on the `WSubMStar` premises in the Wf-App
  case. Retained as a paper-faithful axiom for reference; if a future
  refactor reintroduces a use site, it can be re-cited here.
* **Discharge plan:** Closing this conjecture is a research-level
  metatheory result, not a proof-engineering exercise.
* **Estimated complexity:** Permanent / not a discharge target.

---

## Active outstanding (block discharged headline theorems)

These appear in the `#print axioms` closure of at least one headline
theorem.

### 2. `Lemma_24_NarrowingMSubRed`

* **File:** `Pss/Mpss/Narrowing.lean`, line 417 (axiom statement) and
  the post-axiom docstring §4 for the discharge progress.
* **Paper:** Appendix Lemma 24.
* **Statement:** Narrowing for `MSubRed`: if `MSubRed (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) st u v`
  and `Term.LC t` and `fv t ⊆ Γ₁.dom`, then
  `MSubRed (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) st u v`. (No prior chain `t → t'`
  required — the antecedent has been weakened from the paper's
  formulation.)
* **Status:** Outstanding active. Hits Theorem 3, 4, 5 and Lemma 1.
* **Discharge plan (2026-05, post-attempt-2):** The honest discharge
  takes an `msAvoidsPro h x = true` side condition (the paper's "no
  Ms-Pro on x" premise, captured by the Bool-valued `msAvoidsPro` in
  `Pss/Mpss/AvoidsPro.lean`). With the avoidance witness:
  1. Ms-Pro y arm: vacuous when y = x; else `_subBinds_narrow_neq`.
  2. Ms-Top, Ms-Equ, Ms-App: structural recursion via existing helpers.
  3. Ms-Fun arm: recurse at canonical sample
     `y0 := pickFresh (L ∪ fv body ∪ fv body' ∪ {x})` (the widened
     freshness set introduced by this commit's edit to `msAvoidsPro`),
     then build body at arbitrary z via `MSubRed.rename_sub` (no-fv
     rename in `Pss/Mpss/Renaming.lean`). NO alpha-equivariance.
  4. Ms-FOp arm: blocked on a no-fv-precondition variant of
     `MSubRed.rename_equ` (currently a `private` 400-line helper in
     `Pss/Mpss/Commutation.lean` — needs factoring into
     `Pss/Mpss/Renaming.lean` to avoid the
     `Commutation → ... → Narrowing` import cycle).
  5. Wire-up: thread `msAvoidsPro` through `_S_motive_sub` in
     `Pss/Mpss/TypeSafety.lean` and supply a witness at
     `Lemma_1_inline_fun_fun_residual` in `Pss/Mpss/Commutation.lean`.
* **Estimated complexity:** Medium-large (~400 lines refactor for the
  equ-rename promotion + ~200 lines for the discharge proper +
  ~100 lines wire-up). Total ~700 lines.
* **Foundational note:** Earlier discharge plans (path A "WSubM
  transitivity" and path B "WSubMStar end-to-end") are NOT viable
  per the analysis on lines 300-380 of `Narrowing.lean` — both
  require infrastructure downstream of this file. The avoidance-
  witness path documented above lives entirely upstream and is the
  active target.

### 3. `Lemma_10_Inversion`

* **File:** `Pss/Mpss/WellFormed.lean`, line 618.
* **Paper:** Appendix Lemma 10 (full form).
* **Statement:** `WSubMStar Γ (.abs t u) (.abs t' u') → WEquM Γ t t'`.
* **Status:** Outstanding active. Hits Theorem 5.
* **Discharge plan:** A long blocker analysis (file lines 564-617)
  identifies the precise obstruction: stripping the `WSubMStar` to
  `MSub` and inverting `Me-Fun`/`Ms-Fun` chains yields
  `MEqRedStar Γ [] t t_w` and `MEqRedStar Γ [] t' t_w`. Two helper
  lemmas (`Lemma A`, `Lemma B`) extend `WEquM` backwards along forward
  `MEqRedStar` chains. **Closing requires `WfM Γ t_w` to seed
  `WEquM Γ t_w t_w` (rfl).** Producing `WfM Γ t_w` requires
  `WfM`-preservation under `MEqRed` (a non-trivial parallel of
  `Lemma_6_EvaluationPreservesWf` for `MEqRed` instead of `Step`).
  Discharging is a substantial new mutual-recursive proof.
* **Estimated complexity:** Medium-large (~300-600 lines for the
  preservation lemma alone).

### 4. `Lemma_30_msPro_x_axiom`

* **File:** `Pss/Mpss/Substitution.lean`, line 885.
* **Paper:** Appendix Lemma 30 (Ms-Pro arm).
* **Statement:** Residual `Ms-Pro y = x` arm of Lemma 30 (substitution
  preserves `MSubRed`). Under the paper's "no promotion of `x`" side
  condition, this case is vacuous.
* **Status:** Outstanding active. Hits Theorem 5.
* **Discharge plan:** A leaf-level discharge has already been produced:
  `Lemma_30_msPro_x` (in `Pss/Mpss/AvoidsPro.lean`, line 611) is a
  theorem that takes an `msAvoidsPro h x = true` witness and discharges
  the residual via `False.elim`. The axiom remains because the SOLE
  caller `Pss.Mpss.TypeSafety._S_lf2` (in `Lemma_7_*`'s `WSubM.lf2` arm)
  invokes `Lemma_30_ReductionUnderSubst_Sub` without an avoidance
  witness, and the `WSubM.lf2` constructor does not carry such a side
  condition. Removing the axiom requires:
  1. Threading an `msAvoidsPro` premise through `Lemma_30_*_Sub`'s
     cofinite arms (needs an alpha-equivariance lemma for `msAvoidsPro`,
     since the body recursion samples `pickFresh L`); AND
  2. Threading the avoidance witness through `TypeSafety.lean`'s
     `_S_motive_sub` motive.
  See file lines 845-883 for the full breakdown.
* **Estimated complexity:** Medium (~150-250 lines, mostly in
  `TypeSafety.lean` plumbing + alpha-equivariance lemma for
  `msAvoidsPro`).

### 5. `Proposition_17_beta_axiom`

* **File:** `Pss/Mpss/OperationalSem.lean`, line 81.
* **Paper:** Proposition 17 (β arm).
* **Statement:** For prevalid extended context `Γ; s` and LC well-scoped
  `(λ ≤ bound. body) arg`,
  `MEqRed Γ s ((.abs bound body) arg) (Term.opening arg body)`.
* **Status:** Outstanding active. Hits Theorem 5.
* **Discharge plan:** `MEqRed.bet`'s body sub-derivation is at `Γ; s`
  WITHOUT the binder added (paper-faithful — see `MEQRED-BET-AUDIT.md`).
  This makes `MEqRed.refl` opaque on freshly-opened bodies whose stray
  fvar isn't in `Γ.dom`. Two paths:
  1. Custom β-helper that walks `LC e` using `MEqRed.var` (no fv-scope
     needed) at fvars; recursive `.app` case still wants `fv ⊆ Γ.dom`
     for the operand;
  2. Lifting `Term.LC` from `Prop` to `Type` would let
     `MEqRed.refl_J` itself become `Type`-valued (no `Classical.choice`
     extraction), enabling structural recursion through opened bodies
     without the fv-scope precondition.
* **Estimated complexity:** Small-medium on path 1 (~100-200 lines);
  large on path 2 (cross-codebase refactor).

### 6. `Lemma_1_ctx_axiom` *(private to `Pss.Mpss.Commutation`)*

* **File:** `Pss/Mpss/Commutation.lean`, line 158.
* **Paper:** Lemma 1 (context-evolution lift, paper-implicit).
* **Statement:** Lift a same-context joining derivation
  `(MEqRed Γ₀ s₀ t₁ t₃, MSubRed Γ₀ s₀ t₂ t₃)` across two parallel
  `↣*` evolutions `Γ₀; s₀ ↣* Γ₁; s₁` and `Γ₀; s₀ ↣* Γ₂; s₂` to a
  joining at `(Γ₁; s₁), (Γ₂; s₂)`.
* **Status:** Outstanding active. Hits Theorem 3, 4 and Lemma 1.
* **Discharge plan:** Documented in file lines 120-154. The fundamental
  obstruction is that `Ct-Stk` and `Ct-Ann` (single-step extensions)
  shift either the stack head or a context annotation under an
  `MEqRed`/`MSubRed` step, requiring `.equ`-narrowing of
  `MSubRed`/`MEqRed` along an `MEqRed`-step on the bound term — itself
  confluence-shaped (recursive). Both consumers actually pass
  reflexive-or-near-reflexive chains:
  1. The headline `Lemma_1_StrongCommutativity_sameCtx` passes
     `(refl, refl)`;
  2. The internal `_core` App × App arm passes `(refl, .stk .refl hv₂)`
     (single Ct-Stk on the stack head).
  An honest discharge would either (a) re-engineer App × App to avoid
  the stack-shift (reduce `v, v₂` to a common reduct via Lemma 2 first,
  then join at the common stack), or (b) cycle-break by inlining
  WSubM-transitivity from `TransitivityElim`.
* **Estimated complexity:** Medium (300-500 lines for the App × App
  refactor and the `.equ`-narrowing chain).

### 7. `Lemma_1_inline_app_bet_residual` *(private to `Pss.Mpss.Commutation`)*

* **File:** `Pss/Mpss/Commutation.lean`, line 171.
* **Paper:** Lemma 1, Ms-App × Me-Bet case (p. 22 of appendix).
* **Statement:** Closes the Ms-App × Me-Bet diagram given operator IH and
  the Me-Bet's body cofinite-quantified premise.
* **Status:** Outstanding active. Hits Theorem 3, 4 and Lemma 1.
* **Discharge plan:** Term-size induction with the paper's "no Me-Pro
  on `x`" side condition (`avoidsPro` Bool function, in
  `Pss/Mpss/AvoidsPro.lean`). The same blocker as the Lemma-2
  β-residuals: closing the diagram requires consuming `avoidsPro h₁ x =
  true → avoidsPro h₂' x = true` through the construction, but
  `MEqRed.refl` is built via `Classical.choice` on `Nonempty`, hiding
  its constructor tree from `avoidsPro`. The current
  `avoidsPro_refl` axiom (in `AvoidsPro.lean`) is a candidate
  unblocker but has not been threaded yet.
* **Estimated complexity:** Medium (~300-500 lines if `avoidsPro_refl`
  is consumed; large if Type-LC refactor is the path).

### 8. `Lemma_2_DiamondMEqRed_ctx_axiom` *(private to `Pss.Mpss.Diamond`)*

* **File:** `Pss/Mpss/Diamond.lean`, line 220.
* **Paper:** Lemma 2 (context-evolution lift).
* **Statement:** Mirror of `Lemma_1_ctx_axiom` for the all-`MEqRed`
  diamond setting.
* **Status:** Outstanding active. Hits Theorem 3, 4, 5 and Lemma 1, 2.
* **Discharge plan:** Same as `Lemma_1_ctx_axiom`. Additionally: the
  `_core` App × App arm uses this axiom in a small way (lifting across a
  single Ct-Stk step `Γ; v::s ↣ Γ; v'::s`). A targeted refactor of
  App × App could eliminate that internal use, leaving only the
  external (caller-supplied refl) usage.
* **Estimated complexity:** Medium (same shape as `Lemma_1_ctx_axiom`).

* **Phase 4 blocker (2026-05-03 session):** Phase 3's
  `MEqRed.stack_head_replace` is shipped (in `Renaming.lean` §9.3)
  but cannot be plugged into the App×App arm without first discharging
  its `cofinDomFresh` and `cofinAvoidsProSelf` premises on the IH
  outputs `hu'_w`, `hu₂_w`. These premises are non-trivial:
  - `cofinAvoidsProSelf` at the `fOp` arm requires
    `avoidsPro (hbody (pickFresh L)) (pickFresh L) = true`. The body
    `body^[y₀]` lives at context `⟨y₀, α, .equ⟩ :: Γ`, so `Me-Pro y₀`
    steps in the body are LEGAL — `_core`'s output may include them.
    There is therefore NO general `cofin_normalize` recipe for arbitrary
    `MEqRed Γ s u u'` that produces a witness with cofinAvoidsProSelf =
    true: at the fOp arm we cannot strip Me-Pro on the binding name.
  - Refl-shape rescue fails: `_core`'s App×App output sub-derivations
    (`hu'_w` from `ihu hu₂`, `hv'_v₃` from `ihv hv₂`) are arbitrary
    IH outputs, NOT refl-shaped, so an `avoidsPro_refl`-style trivial
    discharge is unavailable.
  - The only viable path is Option A: thread cofin* output guarantees
    through `_core`'s motive plus every `_inline_*` lemma's signature
    (`_inline_pro_pro`, `_inline_app`, `_inline_bet`, `_inline_fun_fun`,
    `_inline_fOp_fOp`, `_inline_tAp`). Each output construction (App,
    Pro, refl, fOp via rename_equ_no_fv, etc.) needs a cofin proof.
    `MEqRed.refl`'s cofin = true requires widening `L` in its `abs`
    case to include `fv body` and constructing dedicated lemmas
    `cofinDomFresh_refl`, `cofinAvoidsProSelf_refl`. This is a
    multi-day cross-cutting refactor (>500 lines, multiple files).
  - The estimate for Phase 4 has therefore been revised: it is NOT a
    one-line "plug stack_head_replace into App×App" — it requires the
    motive-threading refactor described above as a prerequisite.

* **Recommended next attempt (Phase 4a + 4b):**
  - **Phase 4a — `cofin_refl` lemmas.** Prove `cofinDomFresh_refl` and
    `cofinAvoidsProSelf_refl` for `MEqRed.refl _ _ _` by structural
    recursion on `Term.LC` (mirroring the existing `avoidsPro_refl`
    proof). Requires widening the `L` used inside `MEqRed.refl`'s `abs`
    case (or proving it works at the existing `L ∪ Γ.dom`). Estimated
    ~100-150 lines in `AvoidsPro.lean`.
  - **Phase 4b — `_core` motive enrichment.** Add cofin* output
    guarantees to `Lemma_2_DiamondMEqRed_core`'s motive and to all six
    `_inline_*` lemma signatures. Each output construction needs a
    cofin* proof. The fOp_fOp arm (which uses `rename_equ_no_fv`) needs
    a `cofin*_rename_equ_no_fv` preservation lemma. Estimated ~400-600
    lines across `Diamond.lean`, plus ~50-100 lines of preservation
    lemmas in `Renaming.lean`.
  - **Phase 4c — discharge in App×App.** Once Phases 4a and 4b are in
    place, the App×App arm can replace `_ctx_axiom` with two
    `MEqRed.stack_head_replace` calls (one per leg, using `hv` /
    `hv₂` to swap the stack head). The premises are immediate from
    the enriched IH output guarantees.

### 9. `Lemma_2_inline_app_bet_residual_axiom` *(private to `Pss.Mpss.Diamond`)*

* **File:** `Pss/Mpss/Diamond.lean`, line 292.
* **Paper:** Lemma 2, App × Bet diagonal (case grid).
* **Statement:** Closes `(MEqRed Γ (v::s) (.abs t' body') u', MEqRed Γ s ((.abs t' body') v) (opening v₂' body''))`
  given operator and operand IHs.
* **Status:** Outstanding active. Hits Theorem 3, 4, 5 and Lemma 1, 2.
* **Discharge plan:** Term-size induction bounded by `avoidsPro`. See
  the long discussion in `Diamond.lean` lines 93-150 ("moreover-clause
  threading blocker"). The blocker is `avoidsPro (MEqRed.refl _) x =
  true` not being structurally provable because `MEqRed.refl` extracts
  via `Classical.choice` from a `Nonempty`-wrapped derivation. Three
  paths discussed in the file:
  1. Type-valued `Term.LC` (cross-codebase refactor — see Option B in
     `PLAN.md`'s discharge-campaign section);
  2. Source-driven refl construction (~200 lines of mirror-recursion);
  3. Consume the existing `avoidsPro_refl` axiom (one-line, would
     unblock all three β-residuals).
* **Estimated complexity:** Medium on path 3 (~200-400 lines); medium
  on path 2 (~200 lines mirror); large on path 1 (cross-codebase).

### 10. `Lemma_2_inline_bet_residual_axiom` *(private to `Pss.Mpss.Diamond`)*

* **File:** `Pss/Mpss/Diamond.lean`, line 362.
* **Paper:** Lemma 2, Bet × {App, Bet} cases.
* **Statement:** Closes the diagram for sources of the form
  `.app (.abs t body) v` reduced by `Me-Bet` on the LHS.
* **Status:** Outstanding active. Hits Theorem 3, 4, 5 and Lemma 1, 2.
* **Discharge plan:** Same shape and same blocker as
  `Lemma_2_inline_app_bet_residual_axiom`.
* **Estimated complexity:** Same as #9.

---

## Inactive outstanding (no longer in any headline theorem's transitive deps)

Retained for documentation / paper-faithfulness / partial-discharge
reasoning. None of these are consumed by Theorem 3, 4, 5; Lemma 1, or
Lemma 2.

### 11. `Lemma_10_InversionRestricted`

* **File:** `Pss/Mpss/WellFormed.lean`, line 640.
* **Paper:** Appendix Lemma 10 (alternative formulation).
* **Statement:** `WSubMStar Γ (.abs t u) (.abs t' u') → ∃ z, MEqRedStar Γ [] t z ∧ MEqRedStar Γ [] t' z`.
  Returns a common `MEqRedStar` reduct rather than `WEquM Γ t t'`.
* **Status:** Inactive outstanding. Currently unused downstream (the
  Theorem-5 chain consumes `Lemma_10_Inversion` directly).
* **Discharge plan:** Provable WITHOUT `WfM`-preservation: stripping
  `WSubMStar` to `MSub` immediately yields the common reduct. Retained
  as documentation of the restricted variant.
* **Estimated complexity:** Small (~50-100 lines if anyone wants to
  prove it).

### 12. `avoidsPro_refl` — DISCHARGED (post Type-LC refactor)

* **File:** `Pss/Mpss/AvoidsPro.lean`, line 457.
* **Statement:** `avoidsPro (MEqRed.refl hpv hLC hfv) x = true` for any
  context, term, scope witness, and variable name.
* **Status:** PROVED as a theorem in commit `64162c2` (branch
  `type-lc-experiment`). With `Term.LC : Type` (post-Type-LC refactor),
  `MEqRed.refl` is built by direct structural recursion on the LC
  witness without `Classical.choice`, so the constructor tree of
  `MEqRed.refl` is observable to the `simp [MEqRed.refl, avoidsPro_*]`
  unfolding. The theorem mirrors the recursion of `MEqRed.refl` exactly.

---

## Lemmas the paper covers and we have proved

* **Lemma 15** (paper appendix): `Γ ⊢ u ≡_wf v ⟹ Γ ⊢ v ≡_wf u`.
  PROVED in `Pss/Mpss/WellFormed.lean` as `Lemma_15_WEquM_symm`.
* **Lemma 16** (paper appendix): `Γ ⊢ u ≡_wf v ⟹ Γ ⊢ u ≤_wf v`.
  PROVED in `Pss/Mpss/WellFormed.lean` as `Lemma_16_WEquM_to_WSubM`.
* **Proposition 18** (Reflexivity of `⟶^≡` and `⟶^≤`). PROVED in
  `Pss/Mpss/Diamond.lean` (`Proposition_18_*`), via `MEqRed.refl` /
  `MSubRed.refl` (the latter via `Ms-Equ`).
* **Lemma 7** (Substitution preserves `WfM`). PROVED in
  `Pss/Mpss/TypeSafety.lean` (`Lemma_7_SubstitutionPreservesWf`),
  including the generalized form. The paper's appeal to Conjecture 8
  in the Wf-App case is replaced by a direct IH on the `WSubMStar`
  premises — Conjecture 8 is therefore NOT in Theorem 5's closure.
* **Lemma 6** (Evaluation preserves `WfM`). PROVED in
  `Pss/Mpss/TypeSafety.lean` (`Lemma_6_EvaluationPreservesWf`),
  conditional on `Lemma_10_Inversion` and `Lemma_7_*`.
* **Lemma 11 (restricted)** (Top has no function supertype). PROVED in
  `Pss/Mpss/TypeSafety.lean` (`Lemma_11_TopHasNoFunctionSupertype`),
  via `WSubMStar.toMSub` + chain inversions.
* **`MEqRed.toScoped` / `MSubRed.toScoped`** (formerly Wave-4 axioms):
  PROVED in `Pss/Mpss/Weakening.lean` (lines 491/497).

## Audit

```
nix develop --command lake build Pss.Sanity
```

prints the full axiom dependency lists for each headline theorem (one
per `#print axioms` line). The expected baseline is `propext`,
`Quot.sound`, `Classical.choice` plus the paper-level axioms above.
