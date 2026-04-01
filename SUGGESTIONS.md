# Extend Och gradually until it's ready

## Prove soundness of concEvalC (closure-based evaluator)

`concEvalC` (closure-based concrete evaluator, Closure.lean) correctly handles
concrete recursive fix with thunked branches AND captures definition-site envs
for correct higher-order behavior. Its soundness theorem is stated but sorry'd.

**What's been done:**
- `absEval_mono_trans` PROVED (Monotonicity.lean)
- VR logical relation DEFINED (Closure.lean) with var/type/asc cases proved
- Root cause fully analyzed: **body normalization mismatch** between concEvalC
  (keeps original bodies in closures) and absEval (normalizes bodies under binders)

**The VR approach (partially implemented) is BLOCKED.** The lam/app cases of
the fundamental theorem require the same expression on both evaluation sides,
but concEvalC evaluates `body` (original) while absEval evaluates `body_a`
(normalized). `absEval_normalize_stable` is provably FALSE, so these can't
be related.

**Recommended approach: closure-based abstract evaluator (absEvalC)**

The cleanest path is to factor the proof into two independent parts:

### Step 1: Define absEvalC (~60 lines)

```lean
inductive AVal where
  | aclo : Name → Expr → Expr → AEnv → AVal  -- closure with captured env
  | atype : AVal
  | afixV : Expr → AEnv → AVal

def absEvalC (fuel : Nat) (Γ : AEnv) (e : Expr) : Option AVal :=
  -- Structurally IDENTICAL to concEvalC except:
  -- asc case: takes RHS (ty) instead of LHS (term)  
  -- fix case: returns domain type instead of unrolling body
  -- lam case: returns aclo (captures env, NO normalization under binders)
  -- app case: evaluates ORIGINAL body in CAPTURED env extended with argument
```

### Step 2: Prove soundnessC_abs: concEvalC vs absEvalC (~150 lines)

Both evaluators:
- Keep original bodies in closures (no normalization)
- Use captured (definition-site) envs for beta-reduction
- Have structurally parallel evaluation rules

So the fundamental theorem IH applies directly (same body, captured envs).

VR_abs for closures: just check same body + consistent captured envs.
No application property needed — the IH handles it.

**Challenge:** The asc case still diverges (concrete takes LHS, abstract takes
RHS). This needs a VR_upcast-like property. With AVal-based VR_abs (simpler
closure case), this may be tractable. If not, can use the existential τ'
approach from the current fundamentalVR.

### Step 3: Prove absEvalC_equiv: readback(absEvalC) = absEval (~150 lines)

readback normalizes the closure's body using absEval in the CAPTURED env.
absEval also normalizes in the SAME env. So both use the same env — no
env mismatch.

This is a separate, focused lemma that doesn't involve concEvalC.

**Total estimated effort:** ~360 lines across the three steps.

**Note:** The concEvalS approach (SoundnessS.lean, 7 sorry's) is STALLED — the
bridge theorem `absEval_normalize_stable` is provably FALSE. The closure-based
approach supersedes it.

## North Star: abstract appendVec

The medium-term research goal is getting `appendVec` from docs/add-fix.md working
end-to-end, including with **abstract** arguments (`n : Nat, m : Nat`). Och is
useless without this — a type system that can only verify concrete computations
adds nothing over an evaluator.

Concrete appendVec (fixed n and m) should work once concEval stops normalizing
under binders (see above). Test this first as a sanity check.

For abstract appendVec, the abstract evaluator needs to handle branches where
the result type depends on which branch is taken. Currently `isZero n` for
abstract `n : Nat` correctly evaluates to `Bool` (by applying the type `Nat`
through the elimination chain). But the result of the *outer* branching
(e.g., `(isZero n) ResultType base_case recursive_case`) just gets `ResultType`
— it doesn't know that `base_case` returns `Array 0 T` and `recursive_case`
returns `Array (succ k) T`. Getting branch-precise abstract results may require
partitioning or a similar mechanism, but this is a research question, not a
known-needed feature.

## Extension roadmap

1. **Prove concEvalS soundness** — the urgent next step above.

2. **More concrete recursive fix tests** — now that concEvalS works, add tests
   for `pred`, `mapArray`, `appendArrays` with thunked branches. These exercise
   the evaluator more deeply and may reveal edge cases.

3. **Investigate abstract branching precision** — determine whether the current
   abstract evaluator (which gives `isZero n : Bool` for abstract `n`) is
   sufficient for typing recursive functions, or whether partitioning/narrowing
   is needed. This is research.

4. docs/add-cps.md — should be done eventually, but high risk and might make
   everything very messy.

5. docs/add-implicits.md — should be done eventually, but not if it adds
   unnecessary noise to the underlying theory.
