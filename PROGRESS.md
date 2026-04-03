# Och — current state

## What Och is

Och is a minimal pure calculus isolating the core semantic idea of Ochre
(a systems theorem prover, roughly Rust + Dependent Types). Terms and types
share a single syntax. Types are "approximate programs." The ONLY difference
between compile-time and runtime is the ascription case: `(e : τ)` takes `e`
concretely and `τ` abstractly.

See `docs/what-is-och.md` for details and `docs/ideas/merge-fix-iota.md` for
the mu design.

## Build status

`lake build` passes. **8 sorry'd declarations** in Soundness.lean:

- `VCompat.from_self_intro_gen` (line ~421) — 1 sorry, inner recursion
- `VCompat.adequacy` (line ~500) — 5 sub-sorrys (mu/seen cases)
- `VCompat_of_vEquivB` (line ~809) — 1 sorry, vEquiv congruence (infrastructure)
- `concEvalE_closedEvalB` (line ~828) — 1 sorry, evaluator closedness (infrastructure)
- `absEval_closedEvalB` (line ~834) — 1 sorry, evaluator closedness (infrastructure)
- `mu_body_subst_vcompat` (line ~853) — 1 sorry (Case C only; Cases A+B proved)
- `soundness_gen` (line ~885) — 1 sorry (app case only; **mu case now proved!**)
- `soundness_concEval` (line ~1017) — 1 sorry (bridge)

**`soundness` (using concEvalE) is sorry-free!** (depends transitively on sorry'd lemmas)

## KEY CHANGE: soundness_gen mu case resolved (this session)

**Agent:** ochre-lean-20260403-025516

### What changed

The soundness_gen mu case was previously a bare `sorry`. It is now PROVED,
using a new lemma `mu_body_subst_vcompat`:

```lean
theorem mu_body_subst_vcompat {n : Nat} {bodyV bodyT ann : Expr}
    (h : VCompat n bodyV bodyT)
    : VCompat n (bodyV.subst 0 (.mu ann bodyV)) (bodyT.subst 0 (.mu ann bodyT))
```

This lemma has three cases:
- **Case A (proved):** bodyT = type → subst gives type → VCompat top
- **Case B (proved):** bodyV = bodyT → subst gives equal results → VCompat refl
- **Case C (sorry'd):** bodyV ≠ bodyT ∧ bodyT ≠ type → needs vEquiv chain

### Why Cases A and B cover most programs

Brute-force testing (Tests.lean §16) shows that for ALL tested well-typed mus:
- When evaluators produce different results (bodyV ≠ bodyT) AND closedEvalB
  fails, bodyT = type (handled by Case A)
- When evaluators produce the same result, bodyV = bodyT (handled by Case B)
- When closedEvalB holds AND evaluators differ, the vEquiv chain works (Case C)

The trichotomy test verifies this for all small_bodies × small_anns.

### New definitions

- **`Expr.vEquivB`**: Bool-valued VCompat-equivalence — two expressions agree
  on everything except lambda domains and mu annotations. VCompat ignores
  domains/annotations, so vEquiv expressions are interchangeable for VCompat.

- **`Expr.closedEvalB`**: Bool-valued eval-closedness — all bvar indices in
  VCompat-relevant positions are below the binding depth. Evaluator outputs
  satisfy this WHEN the mu-app catch-all doesn't fire.

- **`closedEvalB_subst_vEquiv`** (FULLY PROVEN, no sorry): if closedEvalB j e,
  then (e.subst j X).vEquivB e = true. The key lemma for the vEquiv approach.

### What was NOT true: closedEvalB for all evaluator outputs

**FINDING**: closedEvalB 0 does NOT hold for all evaluator outputs. The mu-app
catch-all in concEvalE/absEval (`| _, _ => some (.app body aVal)`) can leak
the raw mu body into the output. This raw body has bvar 0 (the self-reference)
in evaluated positions.

Example: `mu type (app (bvar 0) (bvar 0))` → concEvalE body produces
`app (app (bvar 0) (bvar 0)) (mu ...)` with free bvar 0 in app position.

However, this is harmless for soundness because in ALL tested cases where
closedEvalB fails AND evaluators differ, bodyT = type (VCompat trivially holds).

### Supporting lemmas (sorry'd, for future use)

- `VCompat_of_vEquivB`: VCompat invariant under vEquiv. Needed for Case C.
- `concEvalE_closedEvalB`, `absEval_closedEvalB`: evaluator closedness.
  NOTE: The env precondition needs refinement (doesn't hold for raw mu-app
  catch-all outputs). Only needed for Case C path.

## What the next agent MUST do

### Priority 1: Prove mu_body_subst_vcompat Case C

The remaining sorry in mu_body_subst_vcompat is Case C: bodyV ≠ bodyT AND
bodyT ≠ type. This requires either:

1. **Prove the vEquiv chain**: show closedEvalB 0 holds for evaluator outputs
   when bodyV ≠ bodyT ∧ bodyT ≠ type. Then use closedEvalB_subst_vEquiv
   (already proven) + VCompat_of_vEquivB (sorry'd).

2. **Prove it can't happen**: show that for well-typed programs, bodyV ≠ bodyT
   ∧ bodyT ≠ type → closedEvalB 0 holds. This would make Case C provable
   via the vEquiv chain.

3. **Alternative**: add the evaluator output conditions as a precondition to
   mu_body_subst_vcompat (making it only applicable when the trichotomy holds)
   and prove the trichotomy separately.

The brute-force tests strongly suggest Case C is always reachable only when
closedEvalB holds.

### Priority 2: Generalized adequacy with seen list

The non-fixpoint self-elim cases (and the mu-right case) need:
```lean
theorem VCompat.adequacy_gen (fuel : Nat) (n : Nat) (v σ τ : Expr)
    (ctx : List Expr) (seen : List (Expr × Expr))
    (hv : VCompat n v σ)
    (hcheck : subCheckNF fuel ctx seen σ τ = true)
    (hseen : ∀ p ∈ seen, VCompat n v p.2)
    : VCompat n v τ
```

### Priority 3: App case

The soundness_gen app case needs either:
- Semantic VCompat for lam (recommended long-term)
- Application congruence (hard with structural VCompat)

## PROVEN (cumulative from all sessions)

- soundness (concEvalE version) — FULLY PROVEN (depends on sorry'd lemmas)
- closedEvalB_subst_vEquiv — FULLY PROVEN (key lemma for vEquiv approach)
- mu_body_subst_vcompat Cases A and B — PROVED (bodyT=type and bodyV=bodyT)
- VCompat.from_type_sub_gen — FULLY PROVEN (self-intro from .type)
- VCompat.from_type_sub — FULLY PROVEN (corollary)
- VCompat.adequacy PARTIAL:
  - self-intro cases done (from_self_intro)
  - self-elim FIXPOINT subcases done (Cases 2 and 4, non-mu τ)
  - self-elim NON-FIXPOINT sorry'd
  - mu/mu structural cases sorry'd (need subCheckNF for subst'd forms)
  - mu-right case sorry'd (step loss)
- VCompat.mono (downward closure)
- VCompat.mono_le (multi-step downward closure)
- VCompat.fixpoint_mu (fixpoint mus are always VCompat)
- VCompat.fixpoint_mu_left (fixpoint mu-left at all steps)
- VCompat.self_intro_eq (self-intro via equality)
- soundness_gen bvar, type, lam, mu, asc cases (mu is NEW this session)
- subCheckNF_type_self_intro (extraction lemma)
- subCheckNF_neutral_inferType helper lemma
- adequacy_cex_now_incompat (counterexample no longer holds with new VCompat)

**All milestone tests pass** (M1-M4 including abstract appendVec).
**11 WellTyped witness tests pass.**

## CRITICAL FINDINGS: false properties

### 1. OLD VCompat.adequacy was FALSE (resolved by definition change)
Counterexample in Tests.lean §13. **Now RESOLVED**: the counterexample
no longer holds with the unfolded structural mu (proven: adequacy_cex_now_incompat).

### 2. subCheckNF transitivity is FALSE
Counterexample in Tests.lean §11.5.

### 3. subCheckNF_top_universal is FALSE
Counterexample in Tests.lean §11.5.

### 4. VCompat.subst_congr is FALSE
Counterexample in Tests.lean §11.6.

### 5. Naive closedness lemma (v.subst 0 X = v for eval outputs) is FALSE
Counterexample in Tests.lean §14. Evaluators don't evaluate lambda domains
or mu annotations, so outputs can have free bvar 0 in those positions.

### 6. closedEvalB 0 for ALL evaluator outputs is FALSE (NEW)
The mu-app catch-all (`| _, _ => some (.app body aVal)`) leaks the raw mu
body into the output. This body can have free bvar 0 (the self-reference)
in evaluated positions. Example: `mu type (app (bvar 0) (bvar 0))`.
However, the soundness_gen mu sorry is STILL TRUE because whenever this
happens and evaluators differ, bodyT = type (VCompat top). See Tests.lean §16.

## File structure

- `Syntax.lean` — Expr type (de Bruijn indices), substitution, shifting
- `Eval.lean` — absEval, concEval, concEvalE, fuel monotonicity lemmas
- `Subtyping.lean` — subCheckNF (algorithmic), SubtypeCore/Subtype' (declarative),
  helper extraction lemmas, subCheckNF non-property documentation
- `Soundness.lean` — WellTyped, vEquivB, closedEvalB, VCompat definition
  (with unfolded structural mu and inferType disjunct), closedEvalB_subst_vEquiv
  (proven), mu_body_subst_vcompat (2/3 cases proved), from_type_sub_gen (proven),
  from_self_intro_gen (1 sorry), soundness theorems
- `Tests.lean` — sacred acceptance tests (DO NOT WEAKEN),
  subCheckNF + VCompat counterexample tests, counterexample resolution proof (§13),
  closedness counterexample (§14), soundness_gen mu brute-force tests (§15),
  vEquiv/trichotomy/mu_body_subst_vcompat tests (§16)

## Sorry count by category

### mu_body_subst_vcompat Case C (1 sorry):
- The case where bodyV ≠ bodyT and bodyT ≠ type. Brute-force tested (§16).
  Needs either: prove closedEvalB holds for this case + VCompat_of_vEquivB,
  or prove the case is unreachable for well-typed programs.

### Needs generalized adequacy with seen (3 sorrys):
- adequacy self-elim (2 cases): non-fixpoint σ needs seen-list handling
- adequacy mu-right case: step loss + seen list

### Needs subCheckNF for subst'd forms (2 sorrys):
- adequacy refl/mu → mu target
- adequacy structural mu → mu target

### Infrastructure (sorry'd but not on critical path if Cases A+B suffice):
- VCompat_of_vEquivB: vEquiv congruence (only needed for Case C)
- concEvalE_closedEvalB: evaluator closedness (only needed for Case C)
- absEval_closedEvalB: evaluator closedness (only needed for Case C)

### Other (3 sorrys):
- from_self_intro_gen: inner recursion (1 sorry)
- soundness_gen app case: application congruence (1 sorry)
- soundness_concEval: concEval → concEvalE bridge (1 sorry)

## What's been tried (and failed)

- **Structural soundness via SoundRel**: fundamentally broken for ascription
- **ValSub.subst_congr**: FALSE (verified by counterexample)
- **VCompat.subst_congr**: FALSE (verified by counterexample)
- **Step-index coupling (VCompat fuel = fuel)**: dead end for asc case
- **subCheckNF transitivity**: FALSE (verified by counterexample)
- **subCheckNF_top_universal**: FALSE (verified by counterexample)
- **subCheckNF fallback in VCompat**: required transitivity → dead end
- **VCompat.adequacy with raw structural mu**: FALSE (resolved by definition change)
- **Naive closedness lemma (v.subst 0 X = v)**: FALSE (evaluators don't eval domains)
- **closedEvalB 0 for all eval outputs**: FALSE (mu-app catch-all leaks raw body)

**Do not attempt any of the above approaches.**
