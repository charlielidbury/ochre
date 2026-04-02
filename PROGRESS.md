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

`lake build` passes. **3 sorrys** in Soundness.lean:

- `soundness_gen` app case — needs application congruence lemma
- `soundness_gen` asc case — needs VCompat.adequacy
- `soundness` — needs concEval→concEvalE bridge

**PROVEN this session:**
- `VCompat.mono` (downward closure) — was sorry'd, now sorry-free
- `soundness_gen` bvar, type, lam, mu cases — all proven

**All milestone tests pass** (M1-M4 including abstract appendVec).
**11 WellTyped witness tests pass.**

## File structure

- `Syntax.lean` — Expr type (de Bruijn indices), substitution, shifting
- `Eval.lean` — absEval, concEval, concEvalE, fuel monotonicity lemmas
- `Subtyping.lean` — subCheckNF (algorithmic), SubtypeCore/Subtype' (declarative)
- `Soundness.lean` — WellTyped, VCompat definition, soundness theorems
- `Tests.lean` — sacred acceptance tests (DO NOT WEAKEN)

## Key design decisions this session

### VCompat: structural vs semantic function case

Previous VCompat had a SEMANTIC function case: "for all compatible args,
evaluating both bodies gives compatible results." This is the standard
Appel-McAllester approach but has a fundamental problem with the soundness IH:

**Problem:** The soundness IH works on a SINGLE source expression evaluated
by both evaluators. But the semantic function case has DIFFERENT bodies
(concEval/concEvalE and absEval produce different normalized bodies from the
same source). And it has DIFFERENT arguments on each side (av for concrete,
aτ for abstract). There is no single expression to apply the IH to.

**Solution:** Use STRUCTURAL cases instead: "both are lambdas with the same
domain and compatible bodies" (and similarly for mu). With concEvalE-based
soundness, both evaluators normalize the SAME source body in the SAME env.
The IH on the body gives VCompat for the two outputs directly.

This makes lam/mu cases trivial but shifts the burden to the app case,
which now needs an "application congruence" lemma.

### soundness_gen uses concEvalE (not concEval)

The top-level `soundness` uses concEval (substitution-based runtime), but
the proof works through `soundness_gen` which uses concEvalE (env-based).
This is because concEvalE normalizes under binders like absEval, so both
evaluators process the SAME source expression in the SAME env. The IH
then applies directly.

A concEval→concEvalE bridge is needed to connect the two. This is a
separate concern from the main proof.

### VCompat bounded quantifier (earlier change)

The function case (now structural) previously had `∀ av aτ, VCompat n av aτ`
(exactly one step below). This was changed to `∀ m ≤ n` (bounded quantifier,
standard Appel-McAllester). This made mono trivially provable for the
function case. With the switch to structural cases, the bounded quantifier
is no longer relevant, but the structural case makes mono equally easy.

## What the next agent should do

The two remaining sorry'd lemmas in soundness_gen are:

### 1. App case: "application congruence" (Soundness.lean:277)

**The hardest remaining piece.** When f_v = lam dom bodyV and
f_τ = lam dom bodyT (from the IH on f), and a_v, a_τ are the evaluated
args (from IH on a), the evaluators compute:
- concEvalE n env (bodyV.subst 0 a_v) = some rv
- absEval n env (bodyT.subst 0 a_τ) = some rτ

We need VCompat n rv rτ. We have VCompat n (lam dom bodyV) (lam dom bodyT)
via structural lam (so VCompat (n-1) bodyV bodyT), and VCompat n a_v a_τ.

The challenge: bodyV.subst 0 a_v and bodyT.subst 0 a_τ are DIFFERENT
expressions. The IH of soundness_gen needs the SAME expression.

**Approaches to consider:**
1. **Env-substitution equivalence:** Prove that
   `concEvalE fuel env (body'.subst 0 aVal) = concEvalE fuel (env.extend aVal) body_source`
   where body' = concEvalE (env.extend (bvar 0)) body_source. This would let
   us apply soundness_gen to the source body with an extended env. But the
   "source body" is not directly accessible from f_v (it's been normalized).
   
2. **Separate congruence lemma:** Prove
   `VCompat n bV bT → VCompat n aV aT → EnvCompat n envV envT →
    concEvalE k envV (bV.subst 0 aV) = some rv →
    absEval k envT (bT.subst 0 aT) = some rτ →
    VCompat ??? rv rτ`
   by induction on VCompat or on the expressions.
   
3. **Reformulate soundness_gen with related envs:** Instead of a single env,
   use env_v and env_τ with EnvCompat. The IH then supports different
   expressions on each side (via env differences). This is the standard LR
   approach but requires more infrastructure.

4. **Use subCheckNF fallback:** If concEvalE and absEval outputs happen to
   be subCheckNF-related for app results, use the subCheckNF fallback of
   VCompat. This avoids the congruence issue but requires proving subCheckNF
   holds for evaluation outputs (essentially a different form of soundness).

### 2. Asc case: VCompat.adequacy (Soundness.lean:297)

`VCompat n v σ → subCheckNF fuel ctx [] σ τ = true → VCompat n v τ`

The asc case of soundness_gen:
- concEvalE evaluates term → v
- absEval evaluates ty → τ  
- IH on term gives VCompat v (absEval term) = VCompat v σ
- WellTyped gives subCheckNF σ τ
- Need: VCompat v τ (by adequacy)

Adequacy approach: case-split on VCompat, then on subCheckNF derivation.
- VCompat via subCheckNF fallback: compose the two subCheckNFs (needs
  subCheckNF transitivity)
- VCompat via structural lam/mu: transfer through subCheckNF's structural
  cases
- VCompat via mu unfolding: subCheckNF may also unfold

### 3. concEval→concEvalE bridge (Soundness.lean:283)

For the top-level soundness theorem. Prove:
`concEval fuel e = some v → concEvalE fuel [] e = some v'`
with VCompat v v' (or v = v', if that holds for closed terms).

## What's been tried (and failed)

Previous agents spent significant effort on a **structural** soundness proof
using SoundRel (a relation requiring matching top-level constructors). This
approach is **fundamentally broken**: ascription `(e : τ)` produces results
with different constructors (e.g., a lam value vs a mu type), so no
structural relation can bridge them.

**Do not attempt structural relations for soundness.** Use VCompat as described
above.
