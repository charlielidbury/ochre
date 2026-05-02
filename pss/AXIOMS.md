# Axioms

This formalization mechanizes Pasquale & García-Pérez (arXiv 2407.13882
v2, December 2025), the MPSS Krivine-style reformulation of Hutchins'
Pure Subtype Systems. Type safety (Theorems 4 and 5) is conditional on
the axioms below.

**Total axiom count: 12** (1 permanent, 9 active outstanding, 2 inactive
outstanding).

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

* **File:** `Pss/Mpss/Narrowing.lean`, line 417.
* **Paper:** Appendix Lemma 24.
* **Statement:** Narrowing for `MSubRed`: if `MSubRed (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) st u v`
  and `Term.LC t` and `fv t ⊆ Γ₁.dom`, then
  `MSubRed (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) st u v`. (No prior chain `t → t'`
  required — the antecedent has been weakened from the paper's
  formulation.)
* **Status:** Outstanding active. Hits Theorem 3, 4, 5 and Lemma 1.
* **Discharge plan:** A Wave-5 attempt is documented in the file
  (lines 382-413). The Ms-App / Ms-Fun / Ms-FOp arms each need
  WSubMStar-weakening through a binder, which is downstream of
  `Narrowing.lean` via the import chain
  `TransitivityElim → Commutation → Diamond → Narrowing` — creating a
  cycle. Two paths:
  1. Inline ~200 lines of WSubMStar-weakening into `Narrowing.lean`
     (duplicating `TypeSafety.lean`'s `Lemma7._W_*` machinery); OR
  2. Re-architect to lift narrowing downstream of `WfM`-weakening (much
     larger structural change).
* **Estimated complexity:** Medium (~200-300 lines on path 1; large on
  path 2).

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

### 12. `avoidsPro_refl`

* **File:** `Pss/Mpss/AvoidsPro.lean`, line 461.
* **Statement:** `avoidsPro (MEqRed.refl hpv hLC hfv) x = true` for any
  context, term, scope witness, and variable name.
* **Status:** Inactive outstanding. Consumed only by `Lemma_30_msPro_x`
  (a theorem in the same file, line 611), which is itself consumed only
  by hypothetical future `Lemma_30_ReductionUnderSubst_Sub` callers.
  Not yet wired into `TypeSafety.lean`'s `_S_lf2` site, hence does not
  appear in any headline theorem's dependency closure.
* **Paper:** N/A (mechanization-side bridging axiom).
* **Discharge plan:** Documented in file lines 405-443. The axiom is
  morally true: `MEqRed.refl_J`'s derivation tree only invokes
  `top`/`var`/`app`/`fun_`/`fOp` constructors, all of which trivially
  satisfy `avoidsPro = true`. The kernel cannot verify this because
  `MEqRed.refl` extracts via `Classical.choice` from a `Nonempty`. Two
  paths:
  1. Type-valued `Term.LC` (Option B — would let `MEqRed.refl_J` be
     `Type`-valued and structurally recursive);
  2. Source-driven `refl_for : MEqRed Γ s α α' → MEqRed Γ s α' α'` by
     induction on the source — works for all cases except `Me-Bet`,
     whose destination `Term.opening v' body'` has no
     constructor-decomposable refl shape without re-deriving structural
     induction on `LC` (i.e. circling back to path 1).
* **Estimated complexity:** Large on path 1 (cross-codebase refactor);
  see `PLAN.md`'s discharge-campaign section "Option B".

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
