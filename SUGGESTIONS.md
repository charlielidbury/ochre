# Extend Och gradually until it's ready

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
returns `Array (succ k) T`. Self types (suggestion 1) may solve this directly
by making the return type depend on the eliminator's input.

## Suggested Roadmap

Bellow are the current set of suggested next steps which will maximise our dual goal of completing Och and having it be useful for Ochre.

In addition to these main "load bearing" pieces of work, it might also be value to do meta-work like cleaning up the codebase, combining/simplifying concepts, doing literature research (in docs/research/) if you get the sense that "this could have been solved already", etc.

Suggested roadmap mega-list:

1. **Implement self types (iota)** — add `iota` as a new `Expr` constructor
   and move the standard library over to using dependent eliminators as the
   representation for Nat, Bool, etc. Self types let Church-encoded data
   carry its own induction principle (`Nat = iota n. (P : Nat -> Type) ->
   P zero -> ((k : Nat) -> P k -> P (succ k)) -> P n`), giving dependent
   elimination for free via function application. This may be enough to get
   `appendVec` working with abstract arguments — the return type `P n`
   tracks the dependency that Church encoding alone collapses to a fixed
   `X`. See docs/research/self-types-for-och.md for full analysis. The main
   open question is handling stuck self-typed applications in absEval (may
   require type-directed evaluation). Should be done before proving
   soundness, since adding a new `Expr` constructor touches every proof.

2. **Prove soundness of concEvalC (closure-based evaluator)** —
   `concEvalC` (closure-based concrete evaluator, Closure.lean) correctly
   handles concrete recursive fix with thunked branches AND captures
   definition-site envs for correct higher-order behavior. Its soundness
   theorem is stated but sorry'd.

   **What's been done:**
   - `absEval_mono_trans` PROVED (Monotonicity.lean)
   - VR logical relation DEFINED (Closure.lean) with var/type/asc cases proved
   - Root cause fully analyzed: **body normalization mismatch** between
     concEvalC (keeps original bodies in closures) and absEval (normalizes
     bodies under binders)

   **The VR approach (partially implemented) is BLOCKED.** The lam/app
   cases of the fundamental theorem require the same expression on both
   evaluation sides, but concEvalC evaluates `body` (original) while
   absEval evaluates `body_a` (normalized). `absEval_normalize_stable` is
   provably FALSE, so these can't be related.

   **Recommended approach: closure-based abstract evaluator (absEvalC)**

   The cleanest path is to factor the proof into two independent parts:

   *Step 1: Define absEvalC (~60 lines)*

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

   *Step 2: Prove soundnessC_abs: concEvalC vs absEvalC (~150 lines)*

   Both evaluators:
   - Keep original bodies in closures (no normalization)
   - Use captured (definition-site) envs for beta-reduction
   - Have structurally parallel evaluation rules

   So the fundamental theorem IH applies directly (same body, captured envs).

   VR_abs for closures: just check same body + consistent captured envs.
   No application property needed — the IH handles it.

   **Challenge:** The asc case still diverges (concrete takes LHS, abstract
   takes RHS). This needs a VR_upcast-like property. With AVal-based VR_abs
   (simpler closure case), this may be tractable. If not, can use the
   existential τ' approach from the current fundamentalVR.

   *Step 3: Prove absEvalC_equiv: readback(absEvalC) = absEval (~150 lines)*

   readback normalizes the closure's body using absEval in the CAPTURED env.
   absEval also normalizes in the SAME env. So both use the same env — no
   env mismatch.

   This is a separate, focused lemma that doesn't involve concEvalC.

   **Total estimated effort:** ~360 lines across the three steps.

   **Note:** The concEvalS approach (SoundnessS.lean, 7 sorry's) is
   STALLED — the bridge theorem `absEval_normalize_stable` is provably
   FALSE. The closure-based approach supersedes it.

3. **More concrete recursive fix tests** — add tests for `pred`,
   `mapArray`, `appendArrays` with thunked branches. These exercise the
   evaluator independently of self types and may reveal edge cases.

4. **Investigate abstract branching precision** — determine whether self
   types (suggestion 1) fully solve the abstract branching problem, or
   whether partitioning/narrowing is still needed for some cases. Self
   types should handle the common case (dependent elimination), but
   there may be patterns that require branch-precision beyond what self
   types provide. This is research, and should be revisited after (1) is
   implemented.

5. **Add support for recursive types (type-level fix)** — extend `fix` (or
   add new machinery) so that it can define recursive types that the
   evaluator and subtype checker can lazily unfold. This would enable
   moving standard library data structure encodings from Church to Scott
   encoding, where `fix` handles type-level recursion, `iota` handles
   dependent typing, and Scott constructors are simple one-level case
   splits. Requires solving equi-recursive vs iso-recursive types and
   divergence prevention during unfolding. Lower priority than (1) because
   Church + iota already gets dependent elimination without recursive type
   machinery. See docs/ideas/scott-encoding-fix-iota.md for analysis.

6. docs/add-cps.md — should be done eventually, but high risk and might make
   everything very messy.

7. docs/add-implicits.md — should be done eventually, but not if it adds
   unnecessary noise to the underlying theory.
