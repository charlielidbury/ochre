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

import Och.Monotonicity

-- ============================================================
-- Value Relation (VR): Kripke-style logical relation
-- ============================================================

/-- Value relation between CVal (closure values) and Expr (abstract types).
    Step-indexed by fuel to handle the circular dependency in the closure case.

    - `VR.top`: Type is the top type — any value is in Type.
    - `VR.base`: At fuel 0, VR holds vacuously (no computation possible).
    - `VR.clo`: A closure is related to a lambda if applying both to any
      VR-consistent argument produces VR-consistent results. The existential
      `Γ_a` records the abstract env at the closure's definition site. -/
inductive VR : Nat → CVal → Expr → Prop where
  /-- Type is top: any concrete value is in the abstract type Type. -/
  | top : ∀ {n : Nat} {v : CVal}, VR n v .type
  /-- Base case: at fuel 0, VR holds vacuously. -/
  | base : ∀ {v : CVal} {τ : Expr}, VR 0 v τ
  /-- Closure case: a closure is related to a lambda with matching name/domain
      if applying to any VR-consistent argument gives VR-consistent results.
      The Γ_a is the abstract env at definition time; the application property
      evaluates body_a in ((x, τ_a) :: Γ_a). -/
  | clo : ∀ {n : Nat} {x : Name} {dom : Expr} {body : Expr}
            {γ_c : CEnv} {body_a : Expr} {Γ_a : Env},
      (∀ k, k ≤ n →
        ∀ v_a τ_a, VR k v_a τ_a →
        ∀ v_res, concEvalC k ((x, v_a) :: γ_c) body = some v_res →
        ∀ τ_res, absEval k ((x, τ_a) :: Γ_a) body_a = some τ_res →
        VR k v_res τ_res) →
      VR (n + 1) (.clo x dom body γ_c) (.lam x dom body_a)

/-- Environment relation: pointwise VR between CEnv and Env. -/
def ER (n : Nat) (γ : CEnv) (Γ : Env) : Prop :=
  ∀ x τ, Γ.lookup x = some τ → ∃ v, γ.lookup x = some v ∧ VR n v τ

-- ============================================================
-- VR lemmas
-- ============================================================

/-- VR is anti-monotone in fuel: more fuel means a stronger (or equal) relation. -/
theorem VR.mono {n m : Nat} {v : CVal} {τ : Expr}
    (h : VR (n + m) v τ) : VR n v τ := by
  induction n with
  | zero => exact VR.base
  | succ k ih =>
    cases h with
    | top => exact VR.top
    | base => exact VR.base  -- impossible since n+m > 0, but Lean needs it
    | clo h_app =>
      -- n + m = (k+1) + m, so clo level is k + m.
      -- We need VR (k+1) at clo level k.
      -- h_app : ∀ j ≤ k+m, ... → VR j ...
      -- Need: ∀ j ≤ k, ... → VR j ...
      -- Since j ≤ k ≤ k+m, this follows.
      exact VR.clo (fun j hj v_a τ_a hvr v_res hc τ_res ha =>
        h_app j (Nat.le_trans hj (Nat.le_add_right k m)) v_a τ_a hvr v_res hc τ_res ha)

/-- ER is anti-monotone in fuel. -/
theorem ER.mono {n m : Nat} {γ : CEnv} {Γ : Env}
    (h : ER (n + m) γ Γ) : ER n γ Γ := by
  intro x τ h_lookup
  obtain ⟨v, hv, hvr⟩ := h x τ h_lookup
  exact ⟨v, hv, VR.mono hvr⟩

/-- Extend ER with a VR-consistent binding. -/
theorem ER.extend {n : Nat} {γ : CEnv} {Γ : Env}
    (h : ER n γ Γ) (x : Name) {v : CVal} {τ : Expr} (hvr : VR n v τ) :
    ER n ((x, v) :: γ) ((x, τ) :: Γ) := by
  intro y σ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  simp only [CEnv.lookup]
  split at h_lookup <;> rename_i h_eq
  · split
    · cases h_lookup; exact ⟨v, rfl, hvr⟩
    · exact absurd h_eq ‹¬_›
  · split
    · exact absurd ‹_› h_eq
    · exact h y σ h_lookup

-- ============================================================
-- Fundamental theorem (VR version)
-- ============================================================

/-- **Fundamental theorem for VR.**

    If `absEval` and `concEvalC` both succeed for expression `e` in
    consistent environments, then there exists τ' with VR fuel v τ' and
    SubtypeTrans τ' τ.

    The existential τ' avoids the need for VR_upcast (which is blocked
    by `absEval_succeeds_sub` being false in general). The asc case chains
    the SubtypeTrans component instead.

    **Sorry analysis:**
    - **lam case** (1 sorry): The closure captures the original body, but absEval
      returns a normalized body. The VR.clo property needs to relate evaluations
      of different bodies (original vs normalized) in different envs (captured vs
      current). This is the **body normalization mismatch**.
    - **app case** (1 sorry): After extracting VR from the function, the closure's
      stored Γ_a may differ from the call-site Γ. This is the **env mismatch**.
      Additionally, the body normalization mismatch from the lam case propagates.
    - **fix case** (1 sorry): Needs fix typing axiom integration with VR. -/
theorem fundamentalVR
    (fuel : Nat) (γ : CEnv) (Γ : Env) (e τ : Expr) (v : CVal)
    (h_abs : absEval fuel Γ e = some τ)
    (h_conc : concEvalC fuel γ e = some v)
    (h_env : ER fuel γ Γ)
    (h_wt : WellTyped fuel Γ e)
    (h_no_fix : EnvNoFix Γ)
    : ∃ τ', VR fuel v τ' ∧ SubtypeTrans τ' τ := by
  induction fuel generalizing Γ γ e τ v with
  | zero => simp [absEval] at h_abs
  | succ n ih =>
    cases e with
    | var x =>
      -- Both look up x in their respective envs
      simp [absEval, concEvalC] at h_abs h_conc
      obtain ⟨v', hv', hvr⟩ := h_env x τ h_abs
      rw [hv'] at h_conc; cases h_conc
      exact ⟨τ, hvr, SubtypeTrans.step (Subtype'.refl τ)⟩
    | type =>
      -- Both return .type
      simp [absEval] at h_abs; rw [← h_abs]
      exact ⟨.type, VR.top, SubtypeTrans.step (Subtype'.refl .type)⟩
    | lam x dom body =>
      -- concEvalC returns closure, absEval normalizes body
      simp only [concEvalC] at h_conc; cases h_conc
      simp only [absEval] at h_abs
      cases hba : absEval n ((x, .var x) :: Γ) body with
      | none => simp [hba] at h_abs
      | some body_a =>
        simp [hba] at h_abs; rw [← h_abs]
        -- Goal: ∃ τ', VR (n+1) (.clo x dom body γ) τ' ∧ SubtypeTrans τ' (.lam x dom body_a)
        -- Construct VR.clo with Γ_a = Γ, τ' = .lam x dom body_a
        refine ⟨.lam x dom body_a, ?_, SubtypeTrans.step (Subtype'.refl _)⟩
        exact VR.clo (Γ_a := Γ) (fun k hk v_a τ_a hvr_a v_res hc τ_res ha => by
          /- BLOCKER: body normalization mismatch.
             concEvalC evaluates `body` (original) in ((x, v_a) :: γ).
             absEval evaluates `body_a` (= absEval n ((x, var x) :: Γ) body, NORMALIZED)
             in ((x, τ_a) :: Γ).

             The IH (fundamentalVR at fuel k) expects the SAME expression on both sides.
             But body ≠ body_a in general.

             Approaches to resolve:
             1. Use IH on `body` with absEval k ((x, τ_a) :: Γ) body = some σ (NOT body_a),
                then relate σ to τ_res via a compositionality lemma:
                  absEval k ((x,τ_a)::Γ) (absEval n ((x,var x)::Γ) body) ?= absEval k ((x,τ_a)::Γ) body
                This is absEval_normalize_stable which is PROVABLY FALSE in general.
             2. Use a closure-based abstract evaluator (absEvalC) that doesn't normalize under
                binders, making the proof structurally parallel to concEvalC.
             3. Prove a restricted compositionality lemma that holds when env values are
                well-formed (no raw stuck terms in env bindings). -/
          sorry)
    | asc term ty =>
      -- concEvalC evaluates term, absEval evaluates ty
      simp only [concEvalC] at h_conc
      simp only [absEval] at h_abs
      -- WellTyped gives us σ ⊑ τ
      have ⟨h_wt_term, _, σ, τ', h_abs_term, h_abs_ty, h_sub_wt⟩ := h_wt
      -- τ = τ' (both are absEval of ty)
      rw [h_abs] at h_abs_ty; cases h_abs_ty
      -- IH on term: ∃ σ', VR n v σ' ∧ SubtypeTrans σ' σ
      have ih_term := ih γ Γ term σ v h_abs_term h_conc
        (ER.mono (m := 1) (by rwa [Nat.add_comm]))
        h_wt_term h_no_fix
      -- Chain: σ' ⊑ σ ⊑ τ
      obtain ⟨σ', hvr_σ', h_sub_σ'⟩ := ih_term
      exact ⟨σ', VR.mono (m := 1) (by rwa [Nat.add_comm] at hvr_σ'),
             SubtypeTrans.trans h_sub_σ' (SubtypeTrans.step h_sub_wt)⟩
    | fix inner =>
      /- FIX CASE: Similar structure to Soundness.lean's fix case.
         absEval evaluates the domain annotation.
         concEvalC evaluates the body with the fix bound to .fixV.
         Needs fix typing axiom from WellTyped. -/
      sorry
    | app f a =>
      /- APP CASE: The hardest case. After evaluating f and a:
         - concEvalC has .clo x dom body γ_c (closure with captured env)
         - absEval has .lam x dom body_a (lambda with normalized body)
         The continuation evaluates body in γ_c vs body_a in Γ.

         Two interacting problems:
         1. body ≠ body_a (normalization mismatch, same as lam case)
         2. γ_c may differ from Γ (env mismatch: captured vs call-site)

         Approach via VR.clo: extract the application property from the
         function's VR. But VR stores Γ_a (definition-site env), and the
         call site uses Γ (possibly different). Need either env weakening
         or env irrelevance for normalized bodies. -/
      sorry

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

/-- Value relation between CVal and AVal.
    Much simpler than VR (CVal → Expr) because both use closures with
    captured envs and original bodies. No application property needed —
    the fundamental theorem IH handles application directly. -/
inductive VR_abs : Nat → CVal → AVal → Prop where
  /-- Both are type values. -/
  | type_type : VR_abs n .type .atype
  /-- Base case: fuel 0. -/
  | base : VR_abs 0 v a
  /-- Closure case: same body, consistent captured envs. -/
  | clo : ∀ {n x dom body γ_c Γ_a},
      ER_abs n γ_c Γ_a →
      VR_abs (n + 1) (.clo x dom body γ_c) (.aclo x dom body Γ_a)
  /-- Fix thunk case: same inner, consistent captured envs. -/
  | fixV : ∀ {n inner γ_c Γ_a},
      ER_abs n γ_c Γ_a →
      VR_abs (n + 1) (.fixV inner γ_c) (.afixV inner Γ_a)

/-- Environment relation between CEnv and AEnv, pointwise VR_abs. -/
def ER_abs (n : Nat) (γ : CEnv) (Γ : AEnv) : Prop :=
  ∀ x (a : AVal), Γ.lookup x = some a → ∃ v, γ.lookup x = some v ∧ VR_abs n v a

/-- Extend ER_abs with a VR_abs-consistent binding. -/
theorem ER_abs.extend {n : Nat} {γ : CEnv} {Γ : AEnv}
    (h : ER_abs n γ Γ) (x : Name) {v : CVal} {a : AVal} (hvr : VR_abs n v a) :
    ER_abs n ((x, v) :: γ) ((x, a) :: Γ) := by
  intro y σ h_lookup
  simp only [AEnv.lookup] at h_lookup ⊢
  simp only [CEnv.lookup]
  split at h_lookup <;> rename_i h_eq
  · split
    · cases h_lookup; exact ⟨v, rfl, hvr⟩
    · exact absurd h_eq ‹¬_›
  · split
    · exact absurd ‹_› h_eq
    · exact h y σ h_lookup

/-- Well-typedness for absEvalC: ascriptions are sound.
    Parallel to WellTyped but for closure-based evaluation. -/
-- TODO: Define WellTypedC for absEvalC

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
    (h_env : ER_abs fuel γ Γ)
    -- (h_wt : WellTypedC fuel Γ e)  -- TODO: define WellTypedC
    : VR_abs fuel v a := by
  sorry  -- Next agent: implement this proof. Key cases:
         -- var: both look up, ER_abs gives VR_abs. Trivial.
         -- type: both return type/atype. Trivial.
         -- lam: both return closures with same body, ER_abs by hypothesis.
         -- asc: HARD — concrete takes LHS, abstract takes RHS. Needs WellTypedC.
         -- fix: concrete unrolls, abstract returns domain. Needs fix typing.
         -- app: both beta-reduce same body in captured envs. IH applies directly.

/-- **absEvalC ≡ absEval (via readback).**

    readbackA(absEvalC fuel Γ e) = absEval fuel (readbackAEnv fuel Γ) e

    Both normalize in the same env. Empirically verified by native_decide tests. -/
theorem absEvalC_equiv
    (fuel : Nat) (Γ : AEnv) (Γ' : Env) (e τ : Expr) (a : AVal)
    (h_abs_c : absEvalC fuel Γ e = some a)
    (h_readback_env : readbackA.readbackAEnv fuel Γ = some Γ')
    (h_abs : absEval fuel Γ' e = some τ)
    : readbackA fuel a = some τ := by
  sorry  -- Next agent: prove by induction on fuel, case split on e.
         -- Key: both normalize in Γ'/readbackAEnv(Γ) — same env.
