import Och.Syntax

/-!
# Och Evaluation (de Bruijn)

Two evaluation modes that diverge only at ascription:
- **Concrete (runtime):** `(e : τ)` takes the lhs `e`.
- **Abstract (compile-time):** `(e : τ)` takes the rhs `τ`.

## Environment

The environment is a positional list: `env[k]` is the value for bvar k.
When entering a binder, we extend with a new entry and shift existing
entries up by 1 (so their free variable indices stay correct at the new depth).

## Beta-reduction

Uses substitution (not env extension) for beta-reduction. When a lambda
is applied, we substitute the argument for bvar 0 in the body, then
re-evaluate in the current env. This avoids the closure problem with
de Bruijn env-based evaluation.
-/

open Expr

/-- Evaluation environment: positional list of values.
    env[k] is the value for bvar k. -/
abbrev Env := List Expr

/-- Extend env for a new binder. Adds the new binding at position 0 and shifts
    existing entries so their free variables adjust for the new depth. -/
def Env.extend (env : Env) (v : Expr) : Env :=
  v :: env.map (Expr.shift 1 0)

/-- Concrete evaluation with environment. Structurally parallel to absEval.

    The ONLY difference from absEval is the ascription case:
    - absEval takes the rhs (type annotation) — compile-time semantics
    - concEval takes the lhs (term value) — runtime semantics

    Both evaluators wrap mu results in mu (rather than unrolling). This
    makes the soundness proof's mu case provable via mu_body (structural
    subtyping) instead of self_intro. The app-mu case matches on the mu
    body directly to apply functions.

    Uses fuel to avoid partiality. Returns `none` on timeout. -/
def concEval (fuel : Nat) (env : Env) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .bvar k       => env.get? k
    | .lam dom body =>
      match concEval fuel (env.extend (.bvar 0)) body with
      | some body' => some (.lam dom body')
      | none => none
    | .type         => some .type
    | .asc term _   => concEval fuel env term  -- runtime: take the lhs
    | .mu ann body =>
      -- Evaluate body with bvar 0 bound to the mu itself.
      -- The mu value is NOT shifted because its bvars are already at
      -- the correct depth (mu body scope = mu binder scope).
      match concEval fuel (env.extend (.mu ann body)) body with
      | some body' => some (.mu ann body')
      | none => none
    | .app f a      =>
      match concEval fuel env f, concEval fuel env a with
      | some (.lam _dom body), some aVal =>
        -- Beta-reduce via substitution: replace bvar 0 in body with aVal
        concEval fuel env (body.subst 0 aVal)
      | some (.mu _ann body), some aVal =>
        -- mu in function position: match on body directly (already normalized).
        match body with
        | .lam _dom lamBody =>
          concEval fuel env (lamBody.subst 0 aVal)
        | .type => some .type
        | _ => some (.app body aVal)
      | some .type, some _ => some .type
      | some f', some a' => some (.app f' a')
      | _, _ => none

/-- Abstract evaluation (typing) with normalization under binders.

    Lambda bodies are normalized under the binder (with the bound variable
    as neutral). This ensures that beta-redexes created by substitution are
    reduced, so e.g. `succ 2` has precise type `3`.

    Domains are NOT normalized, to preserve monotonicity: normalizing
    domains would make them vary with the environment, breaking the
    contravariant domain requirement of function subtyping. -/
def absEval (fuel : Nat) (env : Env) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .bvar k       => env.get? k
    | .lam dom body =>
      -- Normalize body under the binder: bvar 0 is treated as neutral
      match absEval fuel (env.extend (.bvar 0)) body with
      | some body' => some (.lam dom body')
      | none => none
    | .type         => some .type
    | .asc _term ty => absEval fuel env ty  -- compile-time: take the rhs
    | .mu ann body =>
      -- Evaluate body with bvar 0 bound to the mu value itself.
      -- See concEval comment for why the mu value is not shifted.
      match absEval fuel (env.extend (.mu ann body)) body with
      | some body' => some (.mu ann body')
      | none => none
    | .app f a      =>
      match absEval fuel env f, absEval fuel env a with
      | some (.lam _dom body), some aVal =>
        -- Beta-reduce via substitution
        absEval fuel env (body.subst 0 aVal)
      | some (.mu _ann body), some aVal =>
        -- mu in function position. Strategy depends on ann AND body shape.
        -- Uses the annotation (via subst) for return type when both are lambdas.
        match _ann, body with
        | .lam _dom retBody, .lam _ _ =>
          absEval fuel env (retBody.subst 0 aVal)
        | _, .lam _dom retBody =>
          absEval fuel env (retBody.subst 0 aVal)
        | _, .type => some .type
        | _, _ => some (.app body aVal)
      | some .type, some _ => some .type
      | some f', some a' => some (.app f' a')
      | _, _ => none

/-- Substitution-based concrete evaluator. Standard call-by-value lambda calculus.

    Unlike `concEval` (which uses an environment and normalizes under binders for
    proof convenience), this evaluator uses substitution and treats lambdas as
    values — their bodies are NOT evaluated until applied. -/
def concEvalS (fuel : Nat) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .bvar _ => none  -- free variable = stuck (expects closed terms)
    | .lam _ _ => some e  -- lambda is a VALUE — body not evaluated
    | .type => some .type
    | .asc term _ => concEvalS fuel term  -- runtime: erase ascription
    | .mu ann body =>
      -- Unroll: substitute self-reference into body, then evaluate
      concEvalS fuel (body.subst 0 (.mu ann body))
    | .app f a =>
      match concEvalS fuel f, concEvalS fuel a with
      | some (.lam _dom body), some aVal =>
        -- Beta-reduce via substitution
        concEvalS fuel (body.subst 0 aVal)
      | some (.mu ann body), some aVal =>
        -- mu in function position: unroll and retry
        match concEvalS fuel (.mu ann body) with
        | some (.lam _dom lamBody) => concEvalS fuel (lamBody.subst 0 aVal)
        | some .type => some .type
        | some fVal => some (.app fVal aVal)
        | none => none
      | some .type, some _ => some .type
      | some fVal, some aVal => some (.app fVal aVal)
      | _, _ => none
