import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Soundness
import Och.Monotonicity
import Och.Tests

/-!
# Closure-based concrete evaluator and its soundness

## Motivation

The env-based `concEval` (Eval.lean) normalizes under binders, which causes
both branches of Church-encoded conditionals to be evaluated — breaking
recursive fix. The substitution-based `concEvalS` treats lambdas as values
(correct CBV) but creates a structural mismatch with `absEval` that makes
soundness extremely hard to prove (the `absEval_normalize_stable` bridge
theorem is provably FALSE — see SoundnessS.lean).

This file takes a different approach: a **closure-based** concrete evaluator.
Closures capture their definition-site env, giving us:
1. Correct CBV behavior (lambdas are values, bodies not eagerly evaluated)
2. Correct higher-order behavior (captured env is used at application time)
3. Structural similarity to absEval (both use env extension for beta-reduction)

## Design

We add a `clo` constructor to a `CVal` (closure value) type, separate from
`Expr`. The evaluator produces `CVal` values. For the soundness proof, we
define a "readback" that converts `CVal` back to `Expr` (by normalizing the
closure's body in its captured env via absEval).

The soundness theorem then says: if `concEvalC` produces `CVal` c and
`absEval` produces `Expr` τ, then `readback c ⊑ τ`.

## Key property: same-body beta-reduction

When `concEvalC` applies a closure to an argument:
  `concEvalC fuel ((x, arg) :: γ_captured) body`
When `absEval` applies a lambda to an argument:
  `absEval fuel ((x, aVal) :: Γ) body'`

Where body' = absEval ((x, var x) :: Γ) body (normalized body).

Both evaluate a form of "body" in an extended env. The soundness IH
can relate these because:
- The bodies are related by SubtypeTrans (from the IH on the body expression)
- The envs are consistent (the concrete captured env relates to the abstract env)

This is exactly the structure of Soundness.lean's lam case — the key insight
is that closures make the concrete evaluator structurally parallel to absEval
WITHOUT requiring normalization under binders.
-/

open Expr

-- ============================================================
-- Closure values
-- ============================================================

/-- Runtime values produced by the closure-based evaluator.
    Separate from `Expr` to avoid modifying existing definitions/proofs. -/
inductive CVal where
  /-- Closure: a lambda that captured its definition-site environment. -/
  | clo  : Name → (dom : Expr) → (body : Expr) → (env : List (Name × CVal)) → CVal
  /-- Type (top) value. -/
  | type : CVal
  /-- A fixpoint thunk — unrolled lazily at application time. -/
  | fixV : Expr → (env : List (Name × CVal)) → CVal
  deriving Repr, Inhabited

/-- Environment for the closure-based evaluator. -/
abbrev CEnv := List (Name × CVal)

namespace CEnv

def lookup (γ : CEnv) (x : Name) : Option CVal :=
  match γ with
  | []          => none
  | (y, v) :: rest => if y == x then some v else lookup rest x

end CEnv

-- ============================================================
-- Closure-based concrete evaluator
-- ============================================================

/-- Closure-based concrete evaluator (call-by-value).

    Key differences from `concEval`:
    - Lambda case returns a CLOSURE (captures current env), NOT a normalized lambda.
      This means bodies are never evaluated until applied. Church-encoded branching
      with recursive fix works correctly because the unused branch (a closure) is
      never entered.
    - Application uses the CAPTURED env (from the closure), extended with the argument.
      This ensures correct scoping for higher-order functions.
    - Fix returns a fixV thunk, not an unrolled body. Unrolling happens at
      application time (when fixV appears in function position).

    Key SIMILARITY to `absEval`:
    - Both use env extension for beta-reduction (not substitution).
    - The soundness proof can therefore use the same inductive structure as
      Soundness.lean, with closures providing the captured env. -/
def concEvalC (fuel : Nat) (γ : CEnv) (e : Expr) : Option CVal :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .var x        => γ.lookup x
    | .lam x dom body => some (.clo x dom body γ)  -- Closure! Captures env.
    | .type         => some .type
    | .asc term _   => concEvalC fuel γ term  -- Runtime: take the lhs
    | .fix inner    =>
      match inner with
      | .lam f _dom body =>
        -- Evaluate body with f bound to a fixpoint thunk.
        -- The thunk captures the current env for later unrolling.
        concEvalC fuel ((f, .fixV inner γ) :: γ) body
      | _ => none
    | .app f a      =>
      match concEvalC fuel γ f, concEvalC fuel γ a with
      | some (.clo x _dom body γ'), some aVal =>
        -- Beta-reduce: evaluate body in CAPTURED env extended with argument
        concEvalC fuel ((x, aVal) :: γ') body
      | some (.fixV inner γ'), some aVal =>
        -- Fix in function position: unroll and apply
        match concEvalC fuel γ' (.fix inner) with
        | some (.clo x _dom body γ'') =>
          concEvalC fuel ((x, aVal) :: γ'') body
        | some .type => some .type
        | _ => none
      | some .type, some _ => some .type
      | _, _ => none  -- Stuck or failed

-- ============================================================
-- Abstract closure values and closure-based abstract evaluator
-- ============================================================

/-- Abstract closure values. Structurally identical to CVal but used by
    the abstract (compile-time) evaluator. Kept separate to avoid
    conflating concrete and abstract evaluation. -/
inductive AVal where
  /-- Abstract closure: a lambda that captured its definition-site abstract env. -/
  | aclo : Name → (dom : Expr) → (body : Expr) → (env : List (Name × AVal)) → AVal
  /-- Type (top) value. -/
  | atype : AVal
  /-- A fixpoint thunk — unrolled lazily at application time. -/
  | afixV : Expr → (env : List (Name × AVal)) → AVal
  deriving Repr, Inhabited

abbrev AEnv := List (Name × AVal)

namespace AEnv

def lookup (Γ : AEnv) (x : Name) : Option AVal :=
  match Γ with
  | []          => none
  | (y, v) :: rest => if y == x then some v else lookup rest x

end AEnv

/-- Closure-based abstract evaluator (compile-time / typing).

    Structurally IDENTICAL to `concEvalC` except:
    - **Ascription:** takes the RHS (type annotation), not the LHS (term).
      This is the ONLY semantic difference — compile-time vs runtime.
    - **Fix:** returns the domain type (like absEval), not the unrolled body.
    - **Lambda:** returns a closure capturing the env (NO normalization under
      binders). This is the key difference from `absEval`.
    - **App:** evaluates the ORIGINAL body in the CAPTURED env, not a normalized
      body in the call-site env.

    The structural parallelism with concEvalC makes the soundness proof
    (concEvalC vs absEvalC) a straightforward induction on fuel. -/
def absEvalC (fuel : Nat) (Γ : AEnv) (e : Expr) : Option AVal :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .var x        => Γ.lookup x
    | .lam x dom body => some (.aclo x dom body Γ)  -- Closure! Captures env.
    | .type         => some .atype
    | .asc _term ty => absEvalC fuel Γ ty  -- Compile-time: take the rhs
    | .fix inner    =>
      match inner with
      | .lam _f dom _body =>
        -- Abstract: return the declared type (domain annotation).
        -- Well-typedness ensures the body satisfies this type.
        absEvalC fuel Γ dom
      | _ => none
    | .app f a      =>
      match absEvalC fuel Γ f, absEvalC fuel Γ a with
      | some (.aclo x _dom body Γ'), some aVal =>
        -- Beta-reduce: evaluate body in CAPTURED env extended with argument
        absEvalC fuel ((x, aVal) :: Γ') body
      | some (.afixV inner Γ'), some aVal =>
        -- Fix in function position: evaluate the fix, then apply
        match absEvalC fuel Γ' (.fix inner) with
        | some (.aclo x _dom body Γ'') =>
          absEvalC fuel ((x, aVal) :: Γ'') body
        | some .atype => some .atype
        | _ => none
      | some .atype, some _ => some .atype  -- Type applied = Type (top absorbs)
      | _, _ => none  -- Stuck or failed

-- ============================================================
-- Readback from AVal to Expr (normalizes via absEval)
-- ============================================================

/-- Convert an abstract closure value to an Expr by normalizing the
    closure's body using absEval in the captured environment.

    This bridges absEvalC (closure-based) to absEval (Expr-based).
    readbackA(absEvalC Γ e) should equal absEval (readbackAEnv Γ) e. -/
def readbackA (fuel : Nat) (v : AVal) : Option Expr :=
  match v with
  | .atype => some .type
  | .afixV inner _Γ => some (.fix inner)
  | .aclo x dom body Γ =>
    match readbackAEnv fuel Γ with
    | some Γ' =>
      match absEval fuel ((x, .var x) :: Γ') body with
      | some body' => some (.lam x dom body')
      | none => none
    | none => none
where
  /-- Convert an AEnv to an Env by reading back each value. -/
  readbackAEnv (fuel : Nat) : AEnv → Option Env
    | [] => some []
    | (x, v) :: rest =>
      match readbackA fuel v, readbackAEnv fuel rest with
      | some e, some rest' => some ((x, e) :: rest')
      | _, _ => none

-- ============================================================
-- absEvalC tests: verify readbackA(absEvalC) = absEval
-- ============================================================

-- Helper: evaluate with absEvalC and read back to Expr
private def absEvalCReadback (fuel : Nat) (e : Expr) : Option Expr :=
  match absEvalC fuel [] e with
  | some v => readbackA fuel v
  | none => none

-- Basic: type → type
example : absEvalCReadback 100 .type = some .type := by native_decide

-- true' through absEvalC should equal absEval
example : absEvalCReadback 100 true' = absEval 100 [] true' := by native_decide

-- false' through absEvalC should equal absEval
example : absEvalCReadback 100 false' = absEval 100 [] false' := by native_decide

-- succ 2 = 3 (precision through transparent function)
example : absEvalCReadback 100 (.app succ' two') = absEval 100 [] (.app succ' two') := by native_decide

-- add 2 3 = 5
example : absEvalCReadback 100 (.app (.app add' two') three') = absEval 100 [] (.app (.app add' two') three') := by native_decide

-- isZero 0 = true
example : absEvalCReadback 100 (.app isZero' zero') = absEval 100 [] (.app isZero' zero') := by native_decide

-- isZero 3 = false
example : absEvalCReadback 100 (.app isZero' three') = absEval 100 [] (.app isZero' three') := by native_decide

-- id Nat 3 = 3 (transparency)
example : absEvalCReadback 100 (.app (.app id' Nat') three') = absEval 100 [] (.app (.app id' Nat') three') := by native_decide

-- Ascription: (3 : Nat) should give Nat
example : absEvalCReadback 100 (.asc three' Nat') = absEval 100 [] (.asc three' Nat') := by native_decide

-- ============================================================
-- Readback: convert CVal to Expr
-- ============================================================

/-- Convert a closure value back to an Expr by normalizing the
    closure's body in its captured environment.

    For closures: normalize the body under the binder (with x as neutral)
    in the captured env, producing a standard lambda with normalized body.
    This matches what absEval produces.

    For type: return .type.
    For fixV: return the fix expression. -/
def readback (fuel : Nat) (v : CVal) : Option Expr :=
  match v with
  | .type => some .type
  | .fixV inner _γ => some (.fix inner)
  | .clo x dom body γ =>
    -- Convert captured CEnv to Env (readback each value)
    match readbackEnv fuel γ with
    | some γ' =>
      match absEval fuel ((x, .var x) :: γ') body with
      | some body' => some (.lam x dom body')
      | none => none
    | none => none
where
  /-- Convert a CEnv to an Env by reading back each value. -/
  readbackEnv (fuel : Nat) : CEnv → Option Env
    | [] => some []
    | (x, v) :: rest =>
      match readback fuel v, readbackEnv fuel rest with
      | some e, some rest' => some ((x, e) :: rest')
      | _, _ => none

-- ============================================================
-- Tests
-- ============================================================

-- Helper: evaluate and read back
def evalAndReadback (fuel : Nat) (e : Expr) : Option Expr :=
  match concEvalC fuel [] e with
  | some v => readback fuel v
  | none => none

-- Basic tests: Church booleans
-- true X t f → t (as closures, then read back)
-- For closed terms applied to concrete args, readback gives the same result as absEval.

-- Non-recursive fix: works
private def fixId' : Expr := .fix (.lam "self" (.lam "n" Nat' Nat') (.lam "n" Nat' (.var "n")))

-- fixId applied to zero should read back to zero'
example : evalAndReadback 1000 (.app fixId' zero') = some zero' := by native_decide

-- true' Nat' zero' one' should give zero'
example : evalAndReadback 1000
    (.app (.app (.app true' Nat') zero') one') = some zero' := by native_decide

-- false' Nat' zero' one' should give one'
example : evalAndReadback 1000
    (.app (.app (.app false' Nat') zero') one') = some one' := by native_decide

-- succ 2 = 3 (precision through transparent function)
example : evalAndReadback 1000
    (.app succ' two') = some three' := by native_decide

-- id Nat 3 = 3 (transparency)
example : evalAndReadback 1000
    (.app (.app id' Nat') three') = some three' := by native_decide

-- add 2 3 = 5
example : evalAndReadback 1000
    (.app (.app add' two') three') = some five' := by native_decide

-- isZero 0 = true
example : evalAndReadback 1000
    (.app isZero' zero') = some true' := by native_decide

-- isZero 3 = false
example : evalAndReadback 1000
    (.app isZero' three') = some false' := by native_decide

-- ============================================================
-- THE KEY TEST: recursive fix with Church-encoded branching
-- This is what concEval can't do (returns none) but concEvalC handles.
-- ============================================================

-- toZeroThunked: recursive function that always returns 0.
-- Uses thunked branches: (isZero n) (Unit→Nat) (λ_.zero) (λ_.self zero) unit
private def toZeroThunked' : Expr := .fix (.lam "self" (.lam "n" Nat' Nat') (.lam "n" Nat'
  (.app
    (.app (.app (.app (.app isZero' (.var "n")) (.lam "_" Unit' Nat'))
      (.lam "_" Unit' zero'))
      (.lam "_" Unit' (.app (.var "self") zero')))
    unit')))

-- concEvalC handles recursive fix! (concEval returns none for this)
-- toZeroThunked 0 = 0
example : evalAndReadback 1000 (.app toZeroThunked' zero') = some zero' := by native_decide

-- toZeroThunked 1 = 0
example : evalAndReadback 1000 (.app toZeroThunked' one') = some zero' := by native_decide

-- toZeroThunked 2 = 0
example : evalAndReadback 1000 (.app toZeroThunked' two') = some zero' := by native_decide

-- toZeroThunked 3 = 0
example : evalAndReadback 1000 (.app toZeroThunked' three') = some zero' := by native_decide

-- ============================================================
-- Higher-order test: lambda returned from a function
-- f = λx. λy. x (captures x)
-- f 3 should give a function that always returns 3
-- (f 3) 5 should give 3
-- ============================================================

private def captureTest : Expr :=
  .app (.app (.lam "x" Nat' (.lam "y" Nat' (.var "x"))) three') five'

-- (λx. λy. x) 3 5 = 3
example : evalAndReadback 1000 captureTest = some three' := by native_decide

-- ============================================================
-- More recursive fix tests (matching concEvalS tests from Tests.lean)
-- ============================================================

-- rebuildThunked: n → isZero n ? 0 : succ (self (pred n))
-- Reconstructs a number by recursing to 0 and building up with succ
example : evalAndReadback 1000 (.app rebuildThunked zero') = some zero' := by native_decide
example : evalAndReadback 1000 (.app isZero' (.app rebuildThunked zero')) = some true' := by native_decide
example : evalAndReadback 1000 (.app isZero' (.app rebuildThunked one')) = some false' := by native_decide
example : evalAndReadback 1000 (.app isZero' (.app rebuildThunked two')) = some false' := by native_decide

-- addThunked: recursive addition via fix + pred
example : evalAndReadback 1000 (.app (.app addThunked zero') zero') = some zero' := by native_decide
example : evalAndReadback 1000 (.app (.app addThunked zero') three') = some three' := by native_decide
example : evalAndReadback 1000 (.app isZero' (.app (.app addThunked one') zero')) = some false' := by native_decide
example : evalAndReadback 1000 (.app isZero' (.app (.app addThunked two') one')) = some false' := by native_decide

-- Composition: toZeroThunked (addThunked 2 1) = zero
-- Two recursive functions chained
example : evalAndReadback 1000 (.app toZeroThunked' (.app (.app addThunked two') one')) = some zero' := by native_decide

-- pred tests
example : evalAndReadback 1000 (.app pred' zero') = some zero' := by native_decide
example : evalAndReadback 1000 (.app pred' one') = some zero' := by native_decide
example : evalAndReadback 1000 (.app pred' three') = some two' := by native_decide

-- ============================================================
-- Soundness theorem
-- ============================================================

/-- Env consistency between CEnv (concrete closures) and Env (abstract).
    Each abstract binding has a corresponding concrete value whose readback
    subtypes the abstract type. -/
def CEnvConsistent (fuel : Nat) (γ : CEnv) (Γ : Env) : Prop :=
  ∀ x τ, Γ.lookup x = some τ →
    ∃ v, γ.lookup x = some v ∧
      ∃ v_e, readback fuel v = some v_e ∧ SubtypeTrans v_e τ

/-- **Soundness of the closure-based evaluator (readback formulation).**

    If `absEval` says expression `e` has type `τ`, and `concEvalC` produces
    value `v` (a closure), then the readback of `v` subtypes `τ`.

    **Status:** This uses the readback-based approach. The lam case requires
    readback to succeed (readbackEnv + absEval on body in readback env), which
    depends on `absEval_succeeds_envsub` (not yet proven). The app case is harder:
    after beta-reduction, concEvalC evaluates the closure's ORIGINAL body in the
    CAPTURED env, while absEval evaluates the NORMALIZED body in the CURRENT env.
    These are different bodies in different envs.

    See `soundnessC_lr` below for the logical-relations approach that avoids
    these issues. -/
theorem soundnessC
    (Γ : Env) (γ : CEnv) (e τ : Expr) (v : CVal) (fuel : Nat)
    (h_abs : absEval fuel Γ e = some τ)
    (h_conc : concEvalC fuel γ e = some v)
    (h_env : CEnvConsistent fuel γ Γ)
    (h_wt : WellTyped fuel Γ e)
    (h_no_fix : EnvNoFix Γ)
    : ∃ v_e, readback fuel v = some v_e ∧ SubtypeTrans v_e τ := by
  sorry  -- See analysis in soundnessC_lr below

-- ============================================================
-- Logical-relations approach to soundnessC (recommended path)
-- ============================================================

/-!
### Why readback-based soundness is hard

The readback approach (soundnessC above) faces two challenges:

1. **Readback may fail.** `readback` normalizes a closure's body via absEval
   in the readback env. But we can't prove absEval succeeds in the readback env
   without an `absEval_succeeds_envsub` lemma (if absEval succeeds in Γ and
   EnvSubTrans γ' Γ, does it succeed in γ'?). This lemma is blocked in the
   app-beta case: different bodies arise from evaluating in different envs.

2. **App-beta case: different bodies, different envs.** After evaluating `f` and
   getting `clo x dom body_c γ_c` (concrete) and `lam x dom body_a` (abstract),
   the continuation evaluates `body_c` in `(x, v_a) :: γ_c` but `body_a` in
   `(x, τ_a) :: Γ`. The bodies are different (original vs normalized), and the
   envs are different (captured vs current). The function IH gives us readback
   relationship between the closure and the lambda, but not consistency between
   the captured env and the abstract env.

### The logical-relations alternative

Instead of readback, define a **Kripke-style logical relation** (step-indexed by
fuel) between CVal and Expr:

- `VR n .type .type` — type values match
- `VR n (.clo x dom body γ_c) (.lam x dom body_a)` — for any `k < n`,
  any argument `v_a, τ_a` with `VR k v_a τ_a`, if concEvalC evaluates body
  to v_res and absEval evaluates body_a to τ_res, then `VR k v_res τ_res`.
- `ER n γ_c Γ` — pointwise: each binding satisfies VR

This directly models what we need for the app-beta case: the closure "works
correctly" when applied to any consistent argument.

**Proof structure:**
- Induction on fuel, case split on e
- Lam case: construct VR directly — the closure satisfies VR because applying
  it just recurses with the IH at lower fuel
- App-beta case: extract VR from the function result, apply it to the argument
- Other cases: straightforward

**Prerequisite:** `absEval_mono_trans` (PROVED in Monotonicity.lean) is needed
for the asc case (chain IH result with well-typedness through SubtypeTrans).

**Connection to readback:** Once VR is established, showing readback succeeds
and subtypes the abstract result becomes a COROLLARY, not a proof obligation
in the main induction.

### Key obstacle: the app-beta env mismatch

In the app case, concEvalC evaluates the closure's **original** body in the
**captured** env, while absEval evaluates the **normalized** body in the
**call-site** env. The VR closure case stores a Γ_a (the abstract env at
definition time). At the call site, absEval uses Γ_call which may differ
from Γ_a. Bridging this requires either:

(a) Showing absEval of body_a gives the same result in Γ_a and Γ_call
    (env irrelevance — true when body_a is "closed" after normalization,
    but hard to formalize without a free-variable analysis), or

(b) Storing enough information in VR to handle arbitrary call-site envs.

The current implementation takes approach (a) by storing Γ_a in VR and
leaving the env mismatch as a documented gap. The fundamental theorem is
proved for all cases EXCEPT the app-beta case where the function came from
a different scope than the call site.
-/

/-!
## VR / fundamentalVR — REMOVED (does not compile)

The original VR (Kripke-style logical relation, CVal → Expr) and
fundamentalVR were defined here but **never compiled** — VR.clo has
VR in a non-strictly-positive position, which Lean 4's kernel rejects.
Previous agents didn't catch this because Closure.lean was not imported
in Och.lean.

Additionally, fundamentalVR was blocked on the body normalization mismatch
(3 sorry's: lam, app, fix). See PROGRESS.md for full analysis.

The recommended approach is soundnessC_abs (concEvalC vs absEvalC) using
VR_abs, which avoids the normalization mismatch by keeping original bodies
in closures on both sides.
-/

-- ============================================================
-- NEW APPROACH: soundnessC via absEvalC (closure-based abstract evaluator)
-- ============================================================

/-!
### Strategy: factor soundnessC into two independent proofs

Instead of directly relating concEvalC (closure-based concrete) to absEval
(Expr-based abstract with normalization under binders), we factor through
absEvalC (closure-based abstract):

```
concEvalC ←— soundnessC_abs —→ absEvalC ←— absEvalC_equiv —→ absEval
```

1. **soundnessC_abs**: concEvalC vs absEvalC. Both use closures with captured
   envs and evaluate original bodies. Structurally parallel → straightforward.

2. **absEvalC_equiv**: readbackA(absEvalC) = absEval. Both normalize in the
   same definition-site env → no env mismatch.

The tests above confirm absEvalC_equiv holds empirically (all native_decide).
-/

/-- Value relation between CVal and AVal (no fuel parameter needed).
    Structural correspondence: same constructor shapes with recursively
    consistent captured envs. Env consistency is inlined as two hypotheses
    (coverage + VR) to satisfy Lean's nested inductive and positivity checks. -/
inductive VR_abs : CVal → AVal → Prop where
  /-- Both are type values. -/
  | type_type : VR_abs .type .atype
  /-- Closure case: same name, domain, body, and consistent captured envs. -/
  | clo : ∀ {x dom body γ_c Γ_a},
      (∀ y (a : AVal), AEnv.lookup Γ_a y = some a → CEnv.lookup γ_c y ≠ none) →
      (∀ y (a : AVal) (v : CVal), AEnv.lookup Γ_a y = some a → CEnv.lookup γ_c y = some v →
        VR_abs v a) →
      VR_abs (.clo x dom body γ_c) (.aclo x dom body Γ_a)
  /-- Fix thunk case: same inner, consistent captured envs. -/
  | fixV : ∀ {inner γ_c Γ_a},
      (∀ y (a : AVal), AEnv.lookup Γ_a y = some a → CEnv.lookup γ_c y ≠ none) →
      (∀ y (a : AVal) (v : CVal), AEnv.lookup Γ_a y = some a → CEnv.lookup γ_c y = some v →
        VR_abs v a) →
      VR_abs (.fixV inner γ_c) (.afixV inner Γ_a)

/-- Environment relation between CEnv and AEnv: coverage + value relation. -/
def ER_abs (γ : CEnv) (Γ : AEnv) : Prop :=
  (∀ x (a : AVal), AEnv.lookup Γ x = some a → CEnv.lookup γ x ≠ none) ∧
  (∀ x (a : AVal) (v : CVal), AEnv.lookup Γ x = some a → CEnv.lookup γ x = some v →
    VR_abs v a)

/-- Extend ER_abs with a VR_abs-consistent binding. -/
theorem ER_abs.extend {γ : CEnv} {Γ : AEnv}
    (h : ER_abs γ Γ) (x : Name) {v : CVal} {a : AVal} (hvr : VR_abs v a) :
    ER_abs ((x, v) :: γ) ((x, a) :: Γ) := by
  obtain ⟨h_cov, h_vr⟩ := h
  refine ⟨fun y σ ha hne => ?_, fun y σ v' ha hv' => ?_⟩
  · -- Coverage
    simp only [AEnv.lookup] at ha; simp only [CEnv.lookup] at hne
    split at ha <;> rename_i h_eq
    · split at hne
      · simp at hne
      · exact absurd h_eq ‹¬_›
    · split at hne
      · exact absurd ‹_› h_eq
      · exact h_cov y σ ha hne
  · -- Value relation
    simp only [AEnv.lookup] at ha; simp only [CEnv.lookup] at hv'
    split at ha <;> rename_i h_eq
    · split at hv'
      · cases ha; cases hv'; exact hvr
      · exact absurd h_eq ‹¬_›
    · split at hv'
      · exact absurd ‹_› h_eq
      · exact h_vr y σ v' ha hv'

-- TODO: Define WellTypedC for absEvalC (well-typedness for closure-based evaluation)

/-- **Soundness of concEvalC vs absEvalC.**

    Both evaluators use closures with captured envs and evaluate original
    bodies. The structural parallelism makes this a straightforward induction.

    **Key advantage over fundamentalVR:** The body is the SAME on both sides.
    No normalization mismatch. The IH applies directly.

    **Remaining challenge:** The asc case diverges (concrete takes LHS,
    abstract takes RHS). This needs well-typedness and a VR_abs upcast. -/
theorem soundnessC_abs
    (fuel : Nat) (γ : CEnv) (Γ : AEnv) (e : Expr) (v : CVal) (a : AVal)
    (h_conc : concEvalC fuel γ e = some v)
    (h_abs : absEvalC fuel Γ e = some a)
    (h_env : ER_abs γ Γ)
    -- (h_wt : WellTypedC fuel Γ e)  -- TODO: define WellTypedC for asc/fix
    : VR_abs v a := by
  induction fuel generalizing γ Γ e v a with
  | zero => simp [concEvalC] at h_conc
  | succ n ih =>
    cases e with
    | var x =>
      simp [concEvalC, absEvalC] at h_conc h_abs
      exact h_env.2 x a v h_abs h_conc
    | type =>
      simp [concEvalC, absEvalC] at h_conc h_abs
      cases h_conc; cases h_abs
      exact VR_abs.type_type
    | lam x dom body =>
      simp only [concEvalC] at h_conc; cases h_conc
      simp only [absEvalC] at h_abs; cases h_abs
      exact VR_abs.clo h_env.1 h_env.2
    | asc term ty =>
      -- concEvalC evaluates term, absEvalC evaluates ty — they diverge here.
      -- Needs WellTypedC to relate term's value to ty's value.
      simp only [concEvalC] at h_conc
      simp only [absEvalC] at h_abs
      sorry  -- Needs WellTypedC: absEvalC term ⊑ absEvalC ty
    | fix inner =>
      -- concEvalC unrolls fix body, absEvalC returns domain type.
      -- Needs fix typing axiom.
      sorry
    | app f_e a_e =>
      simp only [concEvalC] at h_conc
      simp only [absEvalC] at h_abs
      -- Evaluate function and argument on both sides
      generalize hfc : concEvalC n γ f_e = rfc at h_conc
      generalize hac : concEvalC n γ a_e = rac at h_conc
      generalize hfa : absEvalC n Γ f_e = rfa at h_abs
      generalize haa : absEvalC n Γ a_e = raa at h_abs
      cases rfc with
      | none => cases rac <;> simp at h_conc
      | some v_f =>
        cases rac with
        | none => simp at h_conc
        | some v_a =>
          cases rfa with
          | none => cases raa <;> simp at h_abs
          | some a_f =>
            cases raa with
            | none => simp at h_abs
            | some a_a =>
              -- IH on function and argument
              have ih_f := ih γ Γ f_e v_f a_f hfc hfa h_env
              have ih_a := ih γ Γ a_e v_a a_a hac haa h_env
              -- Case-split on the function result
              cases ih_f with
              | type_type =>
                -- v_f = .type, a_f = .atype
                simp only at h_conc h_abs
                cases h_conc; cases h_abs
                exact VR_abs.type_type
              | clo h_cov_cap h_vr_cap =>
                -- v_f = .clo x dom body γ_c, a_f = .aclo x dom body Γ_a
                -- Both beta-reduce body in captured envs
                simp only at h_conc h_abs
                -- Apply IH on the body with extended captured envs
                exact ih ((_, v_a) :: _) ((_, a_a) :: _) _ v a h_conc h_abs
                  (ER_abs.extend ⟨h_cov_cap, h_vr_cap⟩ _ ih_a)
              | fixV h_cov_cap h_vr_cap =>
                -- v_f = .fixV inner γ_c, a_f = .afixV inner Γ_a
                -- Both unroll fix and apply
                simp only at h_conc h_abs
                -- First: evaluate .fix inner in captured envs
                generalize hfc_fix : concEvalC n _ (.fix _) = rfc_fix at h_conc
                generalize hfa_fix : absEvalC n _ (.fix _) = rfa_fix at h_abs
                cases rfc_fix with
                | none => simp at h_conc
                | some v_fix =>
                  cases rfa_fix with
                  | none => simp at h_abs
                  | some a_fix =>
                    -- Use IH on .fix inner with captured env consistency
                    have ih_fix := ih _ _ (.fix _) _ _ hfc_fix hfa_fix ⟨h_cov_cap, h_vr_cap⟩
                    cases ih_fix with
                    | type_type =>
                      simp only at h_conc h_abs
                      cases h_conc; cases h_abs
                      exact VR_abs.type_type
                    | clo h_cov_fix h_vr_fix =>
                      simp only at h_conc h_abs
                      exact ih _ _ _ v a h_conc h_abs
                        (ER_abs.extend ⟨h_cov_fix, h_vr_fix⟩ _ ih_a)
                    | fixV _ _ =>
                      -- fixV in fix position: concEvalC match falls to `none`
                      simp only at h_conc h_abs
                      cases h_conc

-- ============================================================
-- Key lemmas for absEvalC_equiv
-- ============================================================

/-- **Fuel monotonicity for absEval**: if absEval succeeds at fuel k,
    it succeeds with the same result at any higher fuel k + j.
    (Copied from SoundnessS.lean to avoid importing the stalled file.) -/
theorem absEval_fuel_mono : ∀ (k j : Nat) (Γ : Env) (e v : Expr),
    absEval k Γ e = some v → absEval (k + j) Γ e = some v := by
  intro k
  induction k with
  | zero => intro j Γ e v h; simp [absEval] at h
  | succ k ih =>
    intro j Γ e v h
    have h_fuel : k + 1 + j = (k + j) + 1 := by omega
    rw [h_fuel]
    cases e with
    | var x =>
      simp only [absEval] at h ⊢; exact h
    | type =>
      simp only [absEval] at h ⊢; exact h
    | lam x d b =>
      simp only [absEval] at h ⊢
      cases hb : absEval k ((x, .var x) :: Γ) b with
      | none => simp [hb] at h
      | some b' =>
        simp [hb] at h; cases h
        have := ih j ((x, .var x) :: Γ) b b' hb
        simp [this]
    | asc t ty =>
      simp only [absEval] at h ⊢
      exact ih j Γ ty v h
    | fix inner =>
      simp only [absEval] at h ⊢
      cases inner with
      | lam f dom body => exact ih j Γ dom v h
      | var _ | app _ _ | asc _ _ | type | fix _ => simp [absEval] at h
    | app f a =>
      simp only [absEval] at h ⊢
      cases hf : absEval k Γ f with
      | none => simp [hf] at h
      | some vf =>
        cases ha : absEval k Γ a with
        | none => simp [hf, ha] at h
        | some va =>
          have hf' := ih j Γ f vf hf
          have ha' := ih j Γ a va ha
          rw [hf', ha']
          rw [hf, ha] at h
          cases vf with
          | lam x _d body =>
            simp only at h ⊢
            exact ih j ((x, va) :: Γ) body v h
          | type =>
            simp only at h ⊢; exact h
          | var _ | app _ _ | asc _ _ | fix _ =>
            simp only at h ⊢; exact h

/-- If readbackAEnv succeeds for Γ and we look up x in Γ, the corresponding
    readback appears in the readback env at the same key. -/
theorem readbackAEnv_lookup (fuel : Nat) (Γ : AEnv) (Γ' : Env) (x : Name) (a : AVal)
    (h_rb : readbackA.readbackAEnv fuel Γ = some Γ')
    (h_lookup : AEnv.lookup Γ x = some a) :
    ∃ τ, readbackA fuel a = some τ ∧ Env.lookup Γ' x = some τ := by
  induction Γ generalizing Γ' with
  | nil => simp [AEnv.lookup] at h_lookup
  | cons entry rest ih =>
    obtain ⟨y, v⟩ := entry
    simp only [readbackA.readbackAEnv] at h_rb
    cases h_rv : readbackA fuel v with
    | none => simp [h_rv] at h_rb
    | some τ_v =>
      cases h_rr : readbackA.readbackAEnv fuel rest with
      | none => simp [h_rv, h_rr] at h_rb
      | some rest' =>
        simp [h_rv, h_rr] at h_rb
        subst h_rb
        simp only [AEnv.lookup] at h_lookup
        simp only [Env.lookup]
        split at h_lookup <;> rename_i h_eq
        · -- x = y: found it
          cases h_lookup
          split
          · exact ⟨τ_v, h_rv, rfl⟩
          · exact absurd h_eq ‹¬_›
        · -- x ≠ y: recurse
          split
          · exact absurd ‹_› h_eq
          · exact ih rest' h_rr h_lookup

/-!
### absEvalC_equiv: the key equivalence theorem

**Statement:** readbackA(absEvalC fuel Γ e) = absEval fuel (readbackAEnv Γ) e

**Proof strategy:** Induction on fuel, case split on e.
- var: follows from readbackAEnv_lookup
- type: trivial
- lam: readbackA and absEval both normalize body in the SAME env
  (needs absEval_fuel_mono for the fuel +1 offset in readbackA)
- asc/fix: IH on the sub-expression
- app: The hard case. When f evaluates to a closure, we need:

  ```
  absEval n ((x, τ_a) :: Γ_cap') body = absEval n ((x, τ_a) :: Γ') body_a
  ```

  where Γ_cap' is the readback of the captured env, Γ' is the readback of the
  call-site env, body is the original body, and body_a is the normalized body
  (= absEval ((x, var x) :: Γ_def') body, normalized at definition site).

  **For lambda literals:** Γ_cap' = Γ' (captured env = call-site env), so this
  reduces to: absEval body in E = absEval (absEval body with x=var x in E) in E.
  This is absEval_normalize_stable.

  **Key insight (new this session):** absEval_normalize_stable is FALSE in general
  (see SoundnessS.lean counterexample with env value `app (var z) type`), BUT the
  counterexample relies on env values being *reducible expressions*. In readback
  envs (from readbackAEnv), ALL values are fully resolved (lam/type/fix with no
  free variables other than bound lambda parameters). For such envs:
  - Normalization resolves all env variables to their values
  - The normalized body's only free variable is the lambda parameter
  - Re-evaluating the normalized body in any env gives the same result
    (the env is irrelevant since all non-parameter variables are already resolved)
  - Therefore normalize-then-evaluate = direct-evaluate

  **Proving this formally requires:**
  1. A "closed body" lemma: absEval in a readback env produces expressions with
     no free vars other than bound lambda params
  2. An "env irrelevance" lemma: absEval of a closed expression gives the same
     result regardless of env (for vars not in the expression)
  3. absEval_normalize_stable restricted to readback envs

  These are well-motivated but non-trivial. Left as the main sorry.

**Fuel issue:** readbackA uses fuel for both readbackAEnv and absEval. When the
theorem uses the same fuel for absEvalC, readbackAEnv, and absEval, sub-evaluations
at fuel n need readbackAEnv at fuel n, but h_readback_env is at fuel n+1. We use
a separate rb_fuel ≥ fuel for readback to avoid this.
-/

/-- **absEvalC ≡ absEval (via readback).**

    Uses separate `rb_fuel` for readback (≥ eval fuel) to handle the
    fuel offset between sub-evaluations and readbackAEnv. -/
theorem absEvalC_equiv
    (fuel rb_fuel : Nat) (Γ : AEnv) (Γ' : Env) (e τ : Expr) (a : AVal)
    (h_abs_c : absEvalC fuel Γ e = some a)
    (h_readback_env : readbackA.readbackAEnv rb_fuel Γ = some Γ')
    (h_abs : absEval fuel Γ' e = some τ)
    (h_fuel_le : fuel ≤ rb_fuel)
    : readbackA rb_fuel a = some τ := by
  induction fuel generalizing Γ Γ' e τ a with
  | zero => simp [absEvalC] at h_abs_c
  | succ n ih =>
    cases e with
    | var x =>
      simp only [absEvalC] at h_abs_c
      simp only [absEval] at h_abs
      obtain ⟨τ_a, h_ra, h_lookup⟩ := readbackAEnv_lookup rb_fuel Γ Γ' x a h_readback_env h_abs_c
      rw [h_lookup] at h_abs; cases h_abs; exact h_ra
    | type =>
      simp only [absEvalC] at h_abs_c; cases h_abs_c
      simp only [absEval] at h_abs; cases h_abs; rfl
    | asc term ty =>
      simp only [absEvalC] at h_abs_c
      simp only [absEval] at h_abs
      exact ih Γ Γ' ty τ a h_abs_c h_readback_env h_abs (Nat.le_of_succ_le h_fuel_le)
    | fix inner =>
      simp only [absEvalC] at h_abs_c
      simp only [absEval] at h_abs
      cases inner with
      | lam _f dom _body =>
        exact ih Γ Γ' dom τ a h_abs_c h_readback_env h_abs (Nat.le_of_succ_le h_fuel_le)
      | _ => simp [absEvalC] at h_abs_c
    | lam x dom body =>
      simp only [absEvalC] at h_abs_c; cases h_abs_c
      simp only [absEval] at h_abs
      cases h_body : absEval n ((x, .var x) :: Γ') body with
      | none => simp [h_body] at h_abs
      | some body_a =>
        simp [h_body] at h_abs; cases h_abs
        -- readbackA rb_fuel (aclo x dom body Γ)
        simp only [readbackA]
        rw [h_readback_env]
        -- Need: absEval rb_fuel ((x, var x) :: Γ') body = some body_a
        -- We have: absEval n ((x, var x) :: Γ') body = some body_a
        -- By fuel mono: absEval n ≤ absEval (n + (rb_fuel - n)) = absEval rb_fuel
        have h_diff : n + (rb_fuel - n) = rb_fuel := Nat.add_sub_cancel' (Nat.le_of_succ_le h_fuel_le)
        have h_bump := absEval_fuel_mono n (rb_fuel - n) ((x, .var x) :: Γ') body body_a h_body
        rw [h_diff] at h_bump; simp [h_bump]
    | app f_e a_e =>
      -- App case: the hardest. See analysis in the doc comment above.
      -- Sub-evaluations at fuel n, IH at fuel n.
      -- The IH on f and a works (same Γ, same Γ').
      -- The IH on body requires:
      --   (1) readbackAEnv rb_fuel ((x, v_a) :: Γ_cap) = some Γ_body_env
      --   (2) absEval n Γ_body_env body = some τ_body
      --   (3) τ_body = τ (the overall absEval result)
      -- Condition (1) is derivable from ih_f and ih_a.
      -- Condition (2) is the sub-IH.
      -- Condition (3) requires absEval_normalize_stable for readback envs.
      sorry
