# Proving Och sound via logical relations

## The goal

Prove: for well-typed closed programs, the concrete value is compatible
with the abstract type.

```lean
theorem soundness
    (fuel : Nat) (e : Expr) (v τ : Expr)
    (h_wt : WellTyped fuel [] e = true)
    (h_conc : concEvalE fuel [] e = some v)
    (h_abs : absEval fuel [] e = some τ)
    : VCompat fuel v τ
```

## Why logical relations?

Och's ascription `(e : τ)` evaluates `term` concretely and `ty` abstractly.
The results can have **completely different constructors** — a lambda value
vs a mu type, for instance. This is the whole point of ascription.

Previous agents tried structural relations (SoundRel, SubtypeCore) that
require matching top-level constructors. These are **fundamentally broken**
for any program with ascription. See PROGRESS.md for the history.

The standard PL solution: **logical relations**. Define compatibility
semantically, by behavior. For functions: "compatible iff applying to
compatible args gives compatible results." This avoids the need for
substitution congruence (which is FALSE for contravariant subtyping) and
handles cross-constructor cases (lam compat mu) via unfolding.

## VCompat — the compatibility relation

Defined in `Soundness.lean`. Step-indexed (Appel & McAllester 2001 style):

```
VCompat 0 v τ := True                    -- no budget: trivially compatible
VCompat (n+1) v τ :=
    τ = .type                             -- top
  ∨ v = τ                                -- refl
  ∨ (both lam, semantic function compat)  -- THE KEY CASE
  ∨ (τ = mu, unfold right, VCompat n)    -- equi-recursive right
  ∨ (v = mu, unfold left, VCompat n)     -- equi-recursive left
  ∨ (subCheckNF v τ)                     -- algorithmic fallback
```

The semantic function case: `v = lam domV bodyV`, `τ = lam domT bodyT`, and
for all `VCompat n av aτ`, evaluating `bodyV[av]` and `bodyT[aτ]` gives
`VCompat n rv rτ`.

**The definition may need refinement** as proofs develop. The current version
is a well-informed sketch. Specific open questions:

1. **concEval vs concEvalE:** The definition currently uses `concEval`
   (the real substitution-based runtime). **Try this first.** If it doesn't
   work (e.g., the lam case is too hard because concEval doesn't normalize
   under binders), fall back to `concEvalE` (env-based, normalizes under
   binders like absEval). Using concEval directly avoids needing a bridge
   theorem between the two evaluators.

2. **Env threading:** The current definition uses empty envs.
   For the lam case of soundness (normalizing under binders), we may need
   `VCompat` to be parameterized by envs. Or maybe the empty-env version is
   fine because the IH provides what we need.

3. **The inferType fallback:** Replaced the old subCheckNF fallback (which
   needed FALSE transitivity). The new disjunct `∃ ctx ty, inferType ctx v =
   some ty ∧ VCompat n ty τ` handles neutral terms (bvar, app) by inferring
   a type and checking compatibility at a lower step index. Composes cleanly
   in adequacy via the IH — no transitivity needed.

4. **Mu unfolding direction:** Currently both left and right unfold. This
   matches equi-recursive subtyping. The step-index decrease prevents
   infinite unfolding.

## Philosophy: tackle the hardest cases first

**The goal is NOT to dispense of easy cases.** The goal is to find out
whether the definitions are right. If Och in its current form is unsound,
we need to discover that as early as possible so the definitions can change.

Every session should focus on the hardest unproven case — the one most
likely to reveal a problem with the definitions. Easy cases can wait.
A session that proves the app case is worth ten sessions that polish
infrastructure lemmas.

**If you find yourself stuck on a case, that IS the interesting result.**
Document WHY it's stuck, try to construct a counterexample, and if you
suspect unsoundness, say so clearly. Changing a definition is not failure
— it's the whole point of the experiment.

## ✅ RESOLVED: VCompat "unfolded structural mu" (2026-04-03)

The old structural mu disjunct (raw bodies) made VCompat.adequacy FALSE.
**Fixed** by replacing with "unfolded structural mu" (self-substituted bodies).
See DECISION-LOG.md and Tests.lean §13 for the counterexample and resolution.

The fix trades sorrys in adequacy (which were PROVABLY FALSE) for sorrys in:
1. soundness_gen mu case (needs closedness lemma)
2. adequacy mu/mu structural cases (needs subCheckNF for subst'd forms)
All new sorrys are potentially true — none known to be false.

## Priority 1: VCompat-equivalence for soundness_gen mu case

**Highest-impact single lemma.** Would fix the soundness_gen mu sorry.

### ⚠️ The naive closedness lemma is FALSE

The previously proposed closedness lemma (`v.subst 0 X = v` for evaluator
outputs) is **FALSE**. The evaluators do NOT evaluate lambda domains or mu
annotations — they copy them from the source. Un-evaluated domains can
contain free `bvar 0` (the mu self-reference). See Tests.lean §14 for a
concrete counterexample: `mu type (lam (bvar 0) (bvar 0))`.

### Why the mu case is still true

Despite closedness failing, brute-force testing (Tests.lean §15) confirms
the soundness_gen mu sorry IS true for all tested well-typed programs (51
bodies tested, 5 with genuinely different evaluator results, all pass).

The reason: **VCompat doesn't compare domains or annotations.** Its
structural lam compares only bodies, and structural mu compares only
unfolded bodies. So `subst 0` into un-evaluated positions (domains,
annotations) is invisible to VCompat.

### Proposed approach: VCompat-equivalence

Define "VCompat-equivalence" (`vEquiv`): two expressions agree on
everything except lambda domains and mu annotations.

```lean
def Expr.vEquiv : Expr → Expr → Prop
  | .bvar k, .bvar k' => k = k'
  | .lam _ b1, .lam _ b2 => b1.vEquiv b2   -- domains ignored
  | .app f1 a1, .app f2 a2 => f1.vEquiv f2 ∧ a1.vEquiv a2
  | .asc t1 y1, .asc t2 y2 => t1.vEquiv t2 ∧ y1.vEquiv y2
  | .type, .type => True
  | .mu _ b1, .mu _ b2 => b1.vEquiv b2      -- annotations ignored
  | _, _ => False
```

Then prove three lemmas:

1. **VCompat respects vEquiv** (congruence):
   `v1.vEquiv v2 → τ1.vEquiv τ2 → VCompat n v1 τ1 → VCompat n v2 τ2`
   Note: the app case needs care — inferType ignores domains (uses
   `_dom` as wildcard), so vEquiv apps give the same inferType result.

2. **subst preserves vEquiv for closedEval expressions:**
   `closedEval 0 e → (e.subst 0 X).vEquiv e`
   Where `closedEval n e` checks that all bvar indices in
   VCompat-relevant positions (everything except lam domains and mu
   annotations) satisfy `k < n`.

3. **Evaluator outputs satisfy closedEval:**
   `concEvalE fuel env e = some v → [env invariant] → closedEval 0 v`
   This holds because the evaluator resolves all bvar lookups in
   evaluated positions. Un-evaluated positions (domains, annotations)
   are NOT checked by closedEval.

Chain: IH gives `VCompat m bodyV' bodyT'`. Lemma 3 gives
`closedEval 0 bodyV'` and `closedEval 0 bodyT'`. Lemma 2 gives
`(bodyV'.subst 0 X).vEquiv bodyV'` and `(bodyT'.subst 0 Y).vEquiv bodyT'`.
Lemma 1 gives `VCompat m (bodyV'.subst 0 X) (bodyT'.subst 0 Y)`.

### Alternative: change to raw body VCompat for mu

If the vEquiv approach proves too complex, consider using raw body VCompat
for mu (restoring the old definition). The adequacy counterexample showed
raw body mu makes adequacy FALSE, but the counterexample involves mus
that can't arise from evaluation. A restricted adequacy that only handles
evaluation-reachable VCompat pairs might work. This is riskier — the
restriction is hard to formalize cleanly.

## Priority 2: Generalized adequacy with seen list

The non-fixpoint self-elim cases need adequacy generalized to non-empty seen:

```lean
theorem VCompat.adequacy_gen (fuel : Nat) (n : Nat) (v σ τ : Expr)
    (ctx : List Expr) (seen : List (Expr × Expr))
    (hv : VCompat n v σ) (hcheck : subCheckNF fuel ctx seen σ τ = true)
    (hseen : ∀ p ∈ seen, VCompat n v p.2)
    : VCompat n v τ
```

Use outer induction on fuel, inner on step j ≤ n. See `from_type_sub_gen`
for a working example of this pattern (handles σ = type with seen).

## The app case — structural vs semantic VCompat

The app case still needs either:
1. **Application congruence** (structural VCompat path)
2. **Semantic VCompat for lam** (makes app case trivial)

The semantic approach is still recommended long-term. With structural lam,
the app case hits substitution congruence. With semantic lam ("for all
compatible args, evaluating both bodies gives compatible results"), the app
case just instantiates the universal quantifier.

## Proof strategy

### Step 1: ✅ DONE — `VCompat.mono` (downward closure)

`VCompat (n+1) v τ → VCompat n v τ`

**Proven.** Required changing the VCompat function case from `∀ av aτ,
VCompat n av aτ → ...` to the standard Appel-McAllester bounded quantifier
`∀ m, m ≤ n → ∀ av aτ, VCompat m av aτ → ...`. With this change, the
function case of mono is trivial (restrict quantifier from m ≤ k+1 to m ≤ k).

### Step 2: THE APP CASE — tackle this first

**This is the hardest case and the most likely to reveal unsoundness.**
Do NOT work on other cases until this one is resolved or understood.

The IH gives VCompat for the evaluated function and arg. The evaluators
then substitute the arg into the body and re-evaluate. But the two bodies
are DIFFERENT (normalized by different evaluators) and the two args are
DIFFERENT (concrete vs abstract).

**With structural VCompat (current):** The app case needs an "application
congruence" lemma: VCompat bodies + VCompat args → VCompat results after
substitution+evaluation. This is essentially substitution congruence —
the same problem that broke previous approaches.

**With semantic VCompat (recommended):** The app case is trivial — the
semantic function quantifier already gives you the result. The difficulty
moves to the lam case instead.

**Approaches to consider (in order of preference):**
1. **Switch to semantic VCompat with concEval.** The app case becomes
   trivial. The lam case needs: "for all compatible args, concEval of
   bodyV[av] and absEval of bodyT[aτ] give compatible results." Since
   concEval treats lam as a value (body untouched = source body), this
   may align with the soundness IH.
2. **Switch to semantic VCompat with concEvalE + env-subst equivalence.**
   Show `concEvalE [] (bodyV'.subst 0 av) = concEvalE [av] source_body`.
   Then the soundness IH applies to the source body.
3. **Reformulate with related envs** (env_v, env_τ with EnvCompat). The
   standard LR approach, but requires more infrastructure.
4. **Keep structural VCompat, prove subst_congr for VCompat.** VCompat is
   covariant, so this MIGHT work (unlike SubtypeCore). Try to disprove
   first with native_decide.

See PROGRESS.md for detailed analysis.

### Step 3: BLOCKED — `VCompat.adequacy` — mu/seen cases

**ADEQUACY IS FALSE** with the current VCompat definition (see above).
The structural mu disjunct must be replaced before this can proceed.

After fixing the mu disjunct, the remaining self-intro cases (using
from_self_intro_gen) should still work. The self-elim cases would
become provable with the "unfolded structural mu" variant.

**subCheckNF transitivity is FALSE** (counterexample in Tests.lean).
But this no longer blocks the proof — the old subCheckNF fallback was
replaced with an inferType disjunct that doesn't need transitivity.

### ✅ DONE — `soundness_gen` asc case

Proven using VCompat.adequacy (which is sorry'd). The key insight was
decoupling the VCompat step index `n` from the evaluation fuel. With
the decoupled approach, the IH gives VCompat at ANY step level, so
adequacy (same-level n) applies without step-index mismatch.

### ✅ DONE — `soundness` (concEvalE version)

The top-level `soundness` theorem (using concEvalE) is now sorry-free —
it's a direct corollary of `soundness_gen` with empty env.

### Step 4: Bridge concEval → concEvalE (soundness_concEval)

For the substitution-based runtime version. Prove that concEval results are
VCompat with concEvalE results. The main difference: concEval doesn't
normalize under lambda binders. This is a separate theorem
(`soundness_concEval`) from the primary `soundness`.

### ✅ DONE — `soundness_gen` bvar, type, lam, mu cases

All proved via structural VCompat + IH. The lam and mu cases are direct
because both evaluators process the same source body in the same env.

### ✅ DONE — `VCompat.mono` (downward closure)

Proved. The structural lam/mu cases make mono trivial (apply IH on bodies).

### ✅ DONE — Decoupled step index from fuel

The VCompat step index `n` is now a separate parameter from evaluation
`fuel` in soundness_gen. This was essential: with coupled indices, the
asc case IH gives VCompat at fuel k but needs VCompat at fuel k+1,
and adequacy preserves the step level. With decoupled indices, the IH
gives VCompat at ANY step level, eliminating the mismatch.

### ✅ DONE — VCompat: inferType disjunct (replacing subCheckNF fallback)

The old subCheckNF fallback `∃ fuel ctx, subCheckNF fuel ctx [] v τ = true`
was replaced with `∃ ctx ty, inferType ctx v = some ty ∧ VCompat n ty τ`.
This eliminated the dead-end (false transitivity) and enabled the inferType
case of adequacy to be proved cleanly via the IH. See PROGRESS.md for full
analysis. (Agent ochre-lean-20260402-234907)

### ✅ DONE — VCompat: relaxed domain/annotation matching

Structural lam/mu cases no longer require matching domains/annotations.
This is needed for adequacy: subCheckNF can change domains via
contravariance, so VCompat must accommodate different domains.

## Before you prove ANYTHING: try to disprove it first

This is the most important rule. Previous agents wasted enormous effort
proving theorems that turned out to be FALSE (SoundRel across ascription,
ValSub.subst_congr, subCheckNF transitivity). A sorry on a false statement
is worse than useless — it gives false confidence and wastes every future
agent's time.

**Before attempting any proof, you MUST:**

1. **Think about whether it could be false.** What would a counterexample
   look like? Is there a program where the preconditions hold but the
   conclusion doesn't? Write down your reasoning.

2. **Test concrete cases with `native_decide`.** Pick 2-3 real programs
   from Tests.lean and verify the theorem holds for them. If you can't
   even construct a witness for a concrete case, the theorem is probably
   wrong.

3. **Try to construct a native_decide counterexample.** Especially for
   lemmas involving subCheckNF, substitution, or cross-constructor cases.
   A 5-minute counterexample search saves days of stuck proofs.

4. **Only then attempt the proof.** And if you get stuck, go back to
   step 1 — maybe you're stuck because it's false.

**The sign of a productive session is discovering a false theorem statement
or a problem with the definitions, NOT adding more sorrys to a stuck proof.**

**Focus on the hardest cases.** Easy cases (bvar, type, top) tell you
nothing about whether the system is sound. The app case and the asc case
are where soundness lives or dies. If you have a choice between proving
an easy case and investigating a hard one, always investigate the hard one.

## Critical constraints

- **Tests are sacred.** DO NOT WEAKEN. `lake build` must pass.
- **Sorry freely, compile always.**
- **Never weaken preconditions without a witness test.** If you change
  WellTyped, verify satisfiability with `native_decide`.
- **The VCompat definition is a sketch.** If a proof doesn't go through,
  consider whether VCompat needs refinement before forcing the proof.
  Getting the definition right is more valuable than proving things about
  a wrong definition.

## What NOT to do

- **Do not use SoundRel or any structural same-constructor relation.**
  This approach is fundamentally broken for ascription. See PROGRESS.md.
- **Do not attempt ValSub.subst_congr.** It is FALSE (verified by
  native_decide counterexample, preserved in git history on main).
- **Do not re-add ValSub.lean or Monotonicity.lean.** These were part of
  the old approach and were deliberately removed.
- **Do not try to prove soundness by relating evaluator outputs
  structurally.** Use VCompat (behavioral/semantic compatibility).
