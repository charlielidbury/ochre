import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Soundness
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
-- Soundness theorem (statement)
-- ============================================================

/-- Env consistency between CEnv (concrete closures) and Env (abstract).
    Each abstract binding has a corresponding concrete value whose readback
    subtypes the abstract type. -/
def CEnvConsistent (fuel : Nat) (γ : CEnv) (Γ : Env) : Prop :=
  ∀ x τ, Γ.lookup x = some τ →
    ∃ v, γ.lookup x = some v ∧
      ∃ v_e, readback fuel v = some v_e ∧ SubtypeTrans v_e τ

/-- **Soundness of the closure-based evaluator.**

    If `absEval` says expression `e` has type `τ`, and `concEvalC` produces
    value `v` (a closure), then the readback of `v` subtypes `τ`.

    This is the same soundness guarantee as Soundness.lean, but for an
    evaluator that correctly handles recursive fix with Church-encoded branching.

    ### Proof sketch

    **Lam case** (the historically hard case):
    - concEvalC returns `.clo x dom body γ` (closure captures env)
    - absEval returns `.lam x dom body'` where `body' = absEval ((x, var x) :: Γ) body`
    - readback normalizes: `body'' = absEval ((x, var x) :: γ') body`
      where `γ' = readbackEnv γ`
    - Need: `SubtypeTrans body'' body'`
    - This follows from **monotonicity** (absEval_mono): both evaluate the
      SAME body in RELATED envs. If `EnvSub γ' Γ`, then `Subtype' body'' body'`.

    **Key advantage over SoundnessS.lean**: No `absEval_normalize_stable` needed!
    The readback function normalizes the closure's body using absEval (the same
    function that produced the abstract result). So we're comparing two absEval
    results on the same expression in related envs — exactly what monotonicity gives.

    **The remaining challenge**: CEnvConsistent gives SubtypeTrans in the env,
    but monotonicity (absEval_mono) requires Subtype' (EnvSub). A future agent
    should either:
    (a) Prove a generalized monotonicity that works with SubtypeTrans, OR
    (b) Show that readback always produces values in Subtype' (not SubtypeTrans)
        relation to the abstract types, OR
    (c) Restructure the proof so the lam case doesn't need monotonicity
        (e.g., by using an LR that captures the definition-site env). -/
theorem soundnessC
    (Γ : Env) (γ : CEnv) (e τ : Expr) (v : CVal) (fuel : Nat)
    (h_abs : absEval fuel Γ e = some τ)
    (h_conc : concEvalC fuel γ e = some v)
    (h_env : CEnvConsistent fuel γ Γ)
    (h_wt : WellTyped fuel Γ e)
    (h_no_fix : EnvNoFix Γ)
    : ∃ v_e, readback fuel v = some v_e ∧ SubtypeTrans v_e τ := by
  sorry  -- Proof to be developed in future sessions
