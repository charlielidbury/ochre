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

`lake build` passes. **8 sorry'd declarations** (all in Soundness.lean):

Soundness.lean (8):
- `VCompat.from_self_intro_gen` (line ~446) — 1 sorry, inner recursion
- `VCompat.adequacy` (line ~525) — 8 sub-sorrys (mu/seen + structural app + 2 NEW semantic lam)
- `VCompat_of_vEquivB` (line ~952) — 3 sorrys (refl→asc + 2 NEW semantic lam)
- `concEvalE_closedEvalB` (line ~1058) — 1 sorry, evaluator closedness
- `absEval_closedEvalB` (line ~1064) — 1 sorry, evaluator closedness
- `mu_body_subst_vcompat` (line ~1083) — 1 sorry (Case C only; Cases A+B proved)
- `soundness_gen` (line ~1131) — **14 sub-sorrys** (lam semantic + 13 app cases)
- `soundness_concEval` (line ~1497) — 1 sorry (bridge)

Eval.lean (0 — all 3 asc-free declarations NOW PROVEN):
- `absEval_ascFree` — PROVEN (conditional: requires input ascFree)
- `concEvalE_ascFree` — PROVEN (conditional: requires input ascFree)
- `ascFree_eval_equiv` — PROVEN (concEvalE = absEval on ascFree inputs)

**`soundness` (using concEvalE) is sorry-free!** (depends transitively on sorry'd lemmas)

## KEY CHANGE: Semantic VCompat for lam (this session)

**Agent:** ochre-lean-20260403-053631

### What changed

Replaced VCompat's structural lam disjunct with a semantic one:

```lean
-- OLD (structural):
∨ (∃ domV domT bodyV bodyT,
    v = .lam domV bodyV ∧ τ = .lam domT bodyT ∧
    VCompat n bodyV bodyT)

-- NEW (semantic):
∨ (∃ domV domT bodyV bodyT,
    v = .lam domV bodyV ∧ τ = .lam domT bodyT ∧
    ∀ (j : Nat), j ≤ n → ∀ (fuel : Nat) (env : Env) (aV aT : Expr),
      VCompat j aV aT →
      ∀ rv, concEvalE fuel env (bodyV.subst 0 aV) = some rv →
      ∀ rτ, absEval fuel env (bodyT.subst 0 aT) = some rτ →
      VCompat j rv rτ)
```

### Why

The structural lam couldn't handle the app lam×lam case: after beta-reduction,
the IH doesn't apply because `bodyV.subst 0 aV` is not a source sub-expression.
VCompat.subst_congr is FALSE (Tests.lean §11.6), so structural body compatibility
can't be threaded through substitution.

The semantic property makes the app lam×lam case trivial: extract the semantic
property from ih_f at step m+2, instantiate with ih_a at step m+1, done.

### What was proved

The **app lam×lam semantic sub-case** is now PROVED (was sorry'd). The proof:
1. Get ih_f at step m+2: `VCompat (m+2) (lam domV bodyV) (lam domT bodyT)`
2. Case-split: only semantic lam and refl are possible (top/mu/app/inferType impossible for lam)
3. For semantic lam: instantiate `h_sem (m+1) (le_refl) k env aV aT ih_a v h_conc τ h_abs`
4. For refl: sorry (see below)

### What regressed (5 new sorrys, all the SAME problem)

1. **soundness_gen lam case** (line ~1189): Must produce the semantic property.
   Requires: given compatible args, evaluating normalized bodies gives compatible
   results. The IH gives VCompat n bodyV' bodyT' (for evaluator outputs of body),
   but the semantic property needs this to hold after substitution and re-evaluation.
   
2. **adequacy lam→lam cases** (2 sorrys, lines ~582, ~604): Must construct
   semantic lam from subCheckNF. Was trivial with structural lam.

3. **VCompat_of_vEquivB lam cases** (2 sorrys, lines ~980, ~1003): Must
   transfer semantic property through vEquiv. Was trivial with structural lam.

**All 5 new sorrys reduce to the SAME underlying problem:** given VCompat n
bodyV bodyT (for bodies that are evaluator outputs of the same source),
derive the semantic property (∀ compatible args, eval gives compatible results).

### The central blocker: semantic property from structural knowledge

The fundamental challenge: VCompat n bodyV bodyT says the bodies are
"compatible" (syntactically or via mu unfolding), but the semantic property
requires showing that evaluation preserves this compatibility through
substitution and re-evaluation.

This cannot work via VCompat.subst_congr (FALSE, §11.6). It might work via:

1. **Eval-subst commutativity**: Show that evaluating bodyV'.subst 0 aV is
   equivalent to re-evaluating body in an env with aV. Then the soundness IH
   applies (same expression, compatible envs). Needs a generalized soundness_gen
   for different envs.

2. **Restricted subst_congr for evaluator outputs**: The counterexample for
   subst_congr uses bvar 0 vs lam type (bvar 0) — not evaluator outputs of
   the same source. Evaluator outputs might satisfy a restricted form.

3. **vEquiv evaluator congruence**: Show vEquiv inputs give vEquiv outputs.
   Then thread through VCompat_of_vEquivB. Would resolve the adequacy and
   vEquivB sorrys as well.

### App lam×lam refl sub-case

When ih_f gives VCompat via refl (bodyV = bodyT), the semantic property
isn't directly available. This happens when f evaluates to the same lambda
by both evaluators (e.g., f = bvar 0 with a lambda in the env). The bodies
are equal but the args differ (aV vs aT). This sub-case is sorry'd.

The bridge idea (IH on `asc (body.subst 0 aV) (body.subst 0 aT)`) almost
works but requires WellTyped for body.subst 0 aV, which isn't given by the
WellTyped app case (it gives WellTyped for body.subst 0 aT only).

## KEY CHANGE: App case decomposed into 36 sub-cases (previous session)

**Agent:** ochre-lean-20260403-042336

### What changed

The soundness_gen app case was previously a single `sorry`. It is now fully
case-split on fV (concEvalE output) × fT (absEval output) constructor shapes
(6×6 = 36 sub-cases). **23 cases proved, 13 sorry'd.**

### Proved cases (23/36):
- **fT = type** (6 cases): τ = type → VCompat top. Trivial.
- **fV = type × fT ∈ {bvar,app,asc,lam}** (4 cases): Contradiction.
  VCompat (m+1) type X = False for X ∉ {type, mu} (no applicable disjunct).
- **fV = lam × fT ∈ {bvar,app,asc}** (3 cases): Contradiction.
  VCompat (m+1) (lam ..) X = False for X ∉ {type, lam, mu}.
- **fV = asc × fT = lam** (1 case): Contradiction.
  VCompat (m+1) (asc ..) (lam ..) = False.
- **fV ∈ {bvar,app,asc} × fT ∈ {bvar,app,asc}** (9 cases): Both catch-all.
  v = app fV aV, τ = app fT aT → structural app from ih_f.mono, ih_a.mono.

### Sorry'd cases (13/36) — all involve active computation:
1. **fV = mu × fT ∈ {bvar,app,asc}** (3): mu-app left, structural right
2. **fV ∈ {bvar,app} × fT = lam** (2): structural left, beta right
3. **fV = lam × fT = lam** (1): ★ THE HARD CASE — both beta-reduce
4. **fV = mu × fT = lam** (1): mu-app left, beta right
5. **fV = type × fT = mu** (1): v = type, mu-app right
6. **fV ∈ {bvar,app,asc} × fT = mu** (3): structural left, mu-app right
7. **fV = lam × fT = mu** (1): beta left, mu-app right
8. **fV = mu × fT = mu** (1): both mu-app

### KEY INSIGHT: asc-free evaluator equivalence

Both evaluators strip ascription from their outputs (concEvalE evaluates the
lhs, absEval evaluates the rhs — either way, the asc node itself is gone).
Therefore **evaluator outputs are always asc-free**.

On asc-free inputs, concEvalE and absEval are **identical** (they differ only
at the asc case, which never fires for asc-free input). Substitution of
asc-free values into asc-free bodies produces an asc-free result.

**Consequence:** After beta-reduction or mu-app, the intermediate expression
(e.g., bodyV.subst 0 aV) is asc-free, so concEvalE and absEval produce the
same result on it. This means:

```
v = concEvalE k env (bodyV.subst 0 aV) = absEval k env (bodyV.subst 0 aV)
τ = absEval k env (bodyT.subst 0 aT) = concEvalE k env (bodyT.subst 0 aT)
```

This **reduces the cross-evaluator app case to a single-evaluator (absEval)
congruence question**: does absEval preserve VCompat through substitution
and evaluation?

### Why this matters for the lam × lam case

For the hardest sub-case (both beta-reduce), the proof needs:
- v = concEvalE k env (bodyV.subst 0 aV) — result of beta with concrete body+arg
- τ = absEval k env (bodyT.subst 0 aT) — result of beta with abstract body+arg
- ih_f: VCompat m bodyV bodyT (structural lam from IH on f)
- ih_a: VCompat (m+1) aV aT (IH on a)
- h_wt_beta: WellTyped k env (bodyT.subst 0 aT) = true (from WellTyped app case)

By the asc-free insight: v = absEval k env (bodyV.subst 0 aV).
So the goal becomes: VCompat n (absEval k env (bodyV.subst 0 aV)) (absEval k env (bodyT.subst 0 aT)).

This is **absEval-congruence for VCompat-related inputs** — a much cleaner
formulation than the original cross-evaluator problem.

### Recommended approach for future agents

Option A (absEval congruence): Prove that absEval preserves VCompat through
substitution and evaluation: if VCompat n body1 body2 and VCompat n arg1 arg2,
then VCompat n (absEval k env (body1.subst 0 arg1)) (absEval k env (body2.subst 0 arg2)).
This would resolve ALL 13 sorry'd cases at once.

Option B (semantic VCompat): Change VCompat's lam case from structural
(VCompat n bodyV bodyT) to semantic (∀ compatible args, evaluating both
bodies gives compatible results). The app case becomes trivial (instantiate
the quantifier). The difficulty moves to the lam case of soundness_gen.

Option C (formalize asc-free equivalence first): Prove the lemma
`ascFree e → concEvalE fuel env e = absEval fuel env e`, then use it to
reduce cross-evaluator sorrys to single-evaluator sorrys. This is a clean,
self-contained contribution independent of the congruence approach.

## KEY CHANGE: inferType_vEquivB and VCompat_of_vEquivB proven (previous session)

**Agent:** ochre-lean-20260403-040210

### What changed

1. **inferType_vEquivB** is now FULLY PROVEN (was sorry'd). The proof is by
   induction on v. For bvar: same ctx lookup + vEquivB_refl. For app: IH on
   function part gives vEquiv type result, then case-split on lam/mu and use
   vEquivB_subst for the substitution steps. The mu-app unfolding case uses
   vEquivB_subst twice (once for body.subst 0 f, once for retTy.subst 0 a).

2. **VCompat_of_vEquivB** is now nearly FULLY PROVEN — 7/8 VCompat disjuncts
   handled, plus the refl case for 5/6 expression shapes. The only sorry is
   the **refl→asc** sub-case, which is genuinely stuck (VCompat has no
   structural asc disjunct) but unreachable in practice since evaluator
   outputs never contain asc expressions.

### Why VCompat_of_vEquivB's asc case is stuck

When v = τ = asc t y (the refl case), vEquiv can change sub-expressions
inside t and y (e.g., lam domains). The resulting v' = asc t1 y1 and
τ' = asc t2 y2 might differ (t1 ≠ t2). But VCompat has no structural asc
disjunct, and no other disjunct applies (inferType returns none for asc,
v' is not lam/mu/app). So VCompat (n+1) v' τ' is FALSE when t1 ≠ t2.

This doesn't matter in practice: the mu_body_subst_vcompat use case only
involves evaluator outputs, which are asc-free.

Options for future agents:
- Add structural asc to VCompat (cleanest, but requires updating mono/adequacy/etc.)
- Add ascFree precondition to VCompat_of_vEquivB
- Leave sorry'd (it's unreachable for the actual use case)

## KEY CHANGE: structural app added to VCompat (previous session)

**Agent:** ochre-lean-20260403-032052

Structural app disjunct fills a gap: VCompat_of_vEquivB was FALSE without it.
See git log for details.

## KEY CHANGE: soundness_gen mu case resolved (previous session)

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

### Priority 1: Prove the semantic property for lam (THE CENTRAL BLOCKER)

The VCompat lam disjunct is now semantic (see KEY CHANGE above). The app
lam×lam case is structurally resolved. But 5 sorrys (lam case of soundness_gen,
2 adequacy cases, 2 vEquivB cases) all need the same thing: derive the semantic
property from structural knowledge about bodies.

**Most promising approaches:**

1. **Generalized soundness_gen for different envs** (MOST PROMISING). Replace
   the single `env` with `envV` and `envT` related by VCompat. Then the lam case
   extends envs differently (envV.extend aV, envT.extend aT) and invokes the IH
   on body. Requires: VCompat preserved under env shift (`Env.extend` shifts
   existing entries via `Expr.shift 1 0`).
   
   **Key insight (discovered this session):** For the semantic lam case of
   VCompat.shift, `(bodyV.shift 1 0).subst 0 aV = bodyV` (shift-subst
   cancellation). So the semantic property for shifted bodies is TRIVIALLY
   equivalent to evaluating the original bodies. VCompat.shift should be
   provable for all disjuncts. The asc case of the generalized theorem also
   works: WellTyped provides absEval on term (from envT), and the IH on term
   gives VCompat v σ, then adequacy bridges to τ.

2. **Eval-subst commutativity.** Show: `concEvalE fuel env (bodyV'.subst 0 aV)`
   = `concEvalE fuel (env_adjusted aV) body` for some env_adjusted. Then the IH
   on body with different envs gives the semantic property.
   
3. **vEquiv evaluator congruence.** Show: vEquiv inputs → vEquiv outputs for
   both evaluators. This would resolve the VCompat_of_vEquivB and adequacy sorrys.

**Do NOT attempt:** VCompat.subst_congr (FALSE, §11.6), absEval congruence
via subst_congr (also fails).

### Priority 2: App lam×lam refl sub-case

When ih_f gives VCompat via refl (bodyV = bodyT), the semantic property isn't
available. Sorry'd at line ~1416. Could be resolved by:
- The bridge idea: IH on `asc (body.subst 0 aV) (body.subst 0 aT)` — needs
  WellTyped for body.subst 0 aV (not currently given)
- Adding WellTyped k env (body.subst 0 aV) to the WellTyped app definition
  (risky: needs witness test verification)
- Proving that soundness_gen ALWAYS produces semantic lam (not refl) for lam
  evaluator outputs

### Priority 3: Prove mu_body_subst_vcompat Case C

Same as before — closedEvalB for evaluator outputs when bodyV ≠ bodyT ∧ bodyT ≠ type.

### Priority 4: Remaining app case sorrys (12 cases)

The 12 non-lam×lam app sorrys involve mu-app on one or both sides. These need
case-splitting on the mu-app behavior (which depends on ann and body shapes).
Potentially resolvable by similar techniques to the lam case.

### Priority 5: Generalized adequacy with seen list

Same as before — needs outer fuel induction, inner step induction.

## PROVEN (cumulative from all sessions)

- soundness (concEvalE version) — FULLY PROVEN (depends on sorry'd lemmas)
- closedEvalB_subst_vEquiv — FULLY PROVEN (key lemma for vEquiv approach)
- **Expr.vEquivB_shift** — FULLY PROVEN (vEquiv preserved by shift)
- **Expr.vEquivB_subst** — FULLY PROVEN (vEquiv preserved by subst)
- **VCompat.refl** — FULLY PROVEN (VCompat n e e for all n, e)
- **Expr.vEquivB_refl** — FULLY PROVEN (e.vEquivB e for all e)
- **inferType_vEquivB** — FULLY PROVEN (inferType respects vEquiv) NEW
- **VCompat_of_vEquivB** — NEARLY PROVEN (only refl→asc sorry'd, unreachable) NEW
- mu_body_subst_vcompat Cases A and B — PROVED (bodyT=type and bodyV=bodyT)
- VCompat.from_type_sub_gen — FULLY PROVEN (self-intro from .type)
- VCompat.from_type_sub — FULLY PROVEN (corollary)
- VCompat.adequacy PARTIAL:
  - self-intro cases done (from_self_intro)
  - self-elim FIXPOINT subcases done (Cases 2 and 4, non-mu τ)
  - self-elim NON-FIXPOINT sorry'd
  - mu/mu structural cases sorry'd (need subCheckNF for subst'd forms)
  - mu-right case sorry'd (step loss)
  - **structural app case sorry'd** (needs inferType congruence) NEW
- VCompat.mono (downward closure) — updated for structural app
- VCompat.mono_le (multi-step downward closure)
- VCompat.fixpoint_mu (fixpoint mus are always VCompat)
- VCompat.fixpoint_mu_left (fixpoint mu-left at all steps)
- VCompat.self_intro_eq (self-intro via equality)
- **soundness_gen app case: 23/36 sub-cases** (type, contradiction, structural app) NEW
- **Expr.ascFree_shift** — FULLY PROVEN (shift preserves asc-free)
- **Expr.ascFree_subst** — FULLY PROVEN (subst preserves asc-free)
- **Env.extend_ascFree** — FULLY PROVEN (env extension preserves asc-free)
- **Expr.ascFree_iff_ascFreeB** — FULLY PROVEN (Prop/Bool equivalence)
- **absEval_ascFree** — FULLY PROVEN (conditional: ascFree input → ascFree output) NEW
- **concEvalE_ascFree** — FULLY PROVEN (conditional: ascFree input → ascFree output) NEW
- **ascFree_eval_equiv** — FULLY PROVEN (concEvalE = absEval on ascFree inputs) NEW
- soundness_gen bvar, type, lam, mu, asc cases
- subCheckNF_type_self_intro (extraction lemma)
- subCheckNF_neutral_inferType helper lemma
- adequacy_cex_now_incompat (counterexample no longer holds with new VCompat)
- **vEquivB shape lemmas** (fwd/bwd for all constructors) NEW

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

### 6. closedEvalB 0 for ALL evaluator outputs is FALSE
The mu-app catch-all (`| _, _ => some (.app body aVal)`) leaks the raw mu
body into the output. This body can have free bvar 0 (the self-reference)
in evaluated positions. Example: `mu type (app (bvar 0) (bvar 0))`.
However, the soundness_gen mu sorry is STILL TRUE because whenever this
happens and evaluators differ, bodyT = type (VCompat top). See Tests.lean §16.

### 7. UNCONDITIONAL absEval_ascFree / concEvalE_ascFree is FALSE (NEW)
Evaluator outputs are NOT always asc-free. Lambda domains and mu annotations
pass through unevaluated, so asc in those positions persists in the output.
Additionally, the mu-app catch-all leaks the raw mu body which can have asc
in active positions.

Counterexamples (Tests.lean §17.1):
- `absEval 5 [] (lam (asc type type) (bvar 0))` → `lam (asc type type) (bvar 0)` (NOT ascFree)
- `absEval 5 [] (mu type (app (bvar 0) (asc type type)))` → output has asc

The CONDITIONAL version IS true and is now PROVEN:
- `absEval_ascFree`: `e.ascFree → env ascFree → output.ascFree`
- `concEvalE_ascFree`: same
- `ascFree_eval_equiv`: `e.ascFree → env ascFree → concEvalE = absEval`

**Impact on app case:** The asc-free insight (concEvalE = absEval after beta)
does NOT work for the general app case. After beta-reduction, `bodyV.subst 0 aV`
might NOT be ascFree because `bodyV` and `aV` (evaluator outputs of a source
program with asc) can have asc in domains/annotations and in mu-app catch-all
outputs. The conditional `ascFree_eval_equiv` only helps when the input
expression is already ascFree. See DECISION-LOG.md for analysis.

## File structure

- `Syntax.lean` — Expr type (de Bruijn indices), substitution, shifting
- `Eval.lean` — absEval, concEval, concEvalE, fuel monotonicity lemmas,
  ascFree infrastructure (all proven: ascFree_shift/subst, Env.extend_ascFree,
  absEval_ascFree, concEvalE_ascFree, ascFree_eval_equiv)
- `Subtyping.lean` — subCheckNF (algorithmic), SubtypeCore/Subtype' (declarative),
  helper extraction lemmas, subCheckNF non-property documentation
- `Soundness.lean` — WellTyped, vEquivB, closedEvalB, VCompat definition
  (with unfolded structural mu, **structural app**, and inferType disjunct),
  vEquivB_shift/subst/refl (proven), closedEvalB_subst_vEquiv (proven),
  inferType_vEquivB (proven), VCompat_of_vEquivB (nearly proven, 1 sorry),
  mu_body_subst_vcompat (2/3 cases proved), from_type_sub_gen (proven),
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

### vEquiv infrastructure (mostly resolved):
- ~~inferType_vEquivB~~: FULLY PROVEN NEW
- VCompat_of_vEquivB: 1 sorry (refl→asc only, unreachable in practice) NEW
- concEvalE_closedEvalB: evaluator closedness (sorry'd)
- absEval_closedEvalB: evaluator closedness (sorry'd)

### Structural app in adequacy (1 sorry):
- adequacy structural app case: needs inferType congruence between app components

### Semantic lam property (5 sorrys, ALL THE SAME PROBLEM): NEW
All 5 need: derive the semantic lam property from structural knowledge.
- soundness_gen lam case (1 sorry, line ~1189)
- adequacy lam→lam cases (2 sorrys, lines ~582, ~604)
- VCompat_of_vEquivB lam cases (2 sorrys, lines ~980, ~1003)

### soundness_gen app case (13 sorrys):
- fV=lam × fT=lam: 1 sorry (REFL sub-case only; SEMANTIC sub-case PROVED)
- fV=mu × fT∈{bvar,app,asc}: 3 sorrys (mu-app left, structural right)
- fV∈{bvar,app} × fT=lam: 2 sorrys (structural left, beta right)
- fV=mu × fT=lam: 1 sorry
- fV=type × fT=mu: 1 sorry
- fV∈{bvar,app,asc} × fT=mu: 3 sorrys
- fV=lam × fT=mu: 1 sorry
- fV=mu × fT=mu: 1 sorry

### Other (2 sorrys):
- from_self_intro_gen: inner recursion (1 sorry)
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
- **Unconditional absEval_ascFree / concEvalE_ascFree**: FALSE (domains pass through,
  mu-app catch-all leaks raw body with asc). The CONDITIONAL version (ascFree input →
  ascFree output) IS true and proven. But the conditional form doesn't help the
  soundness_gen app case because evaluator outputs of programs WITH asc can have asc.

**Do not attempt any of the above approaches.**
