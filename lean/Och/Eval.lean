import Och.Syntax

/-!
# Och Evaluation

Two evaluation modes that diverge only at ascription:
- **Concrete (runtime):** `(e : τ)` takes the lhs `e`.
- **Abstract (compile-time):** `(e : τ)` takes the rhs `τ`.

Compiling an Och program is just running it in abstract mode. Whether this
dual-interpretation is sound is a central research question.

Agents: you may change everything in this file. The definitions below are
starting points. The evaluation strategy, termination argument, and fuel
mechanism are all open to redesign.
-/

open Expr

/-- Typing environment: maps variable names to their (abstract) types. -/
abbrev Env := List (Name × Expr)

namespace Env

def lookup (Γ : Env) (x : Name) : Option Expr :=
  match Γ with
  | []          => none
  | (y, τ) :: rest => if y == x then some τ else lookup rest x

end Env

/-- Concrete evaluation with environment. Structurally parallel to absEval.

    The ONLY difference from absEval is the ascription case:
    - absEval takes the rhs (type annotation) — compile-time semantics
    - concEval takes the lhs (term value) — runtime semantics

    This parallel structure makes the soundness proof a straightforward induction.

    Uses fuel to avoid partiality. Returns `none` on timeout. -/
def concEval (fuel : Nat) (γ : Env) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .var x        => γ.lookup x
    | .lam x dom body =>
      match concEval fuel ((x, .var x) :: γ) body with
      | some body' => some (.lam x dom body')
      | none => none
    | .type         => some .type
    | .asc term _   => concEval fuel γ term  -- runtime: take the lhs
    | .fix inner =>
      match inner with
      | .lam f _dom body =>
        -- Unroll: evaluate body with f bound to the fixpoint thunk.
        -- When body later uses f (via the app case), the fix is re-evaluated.
        concEval fuel ((f, .fix inner) :: γ) body
      | _ => none
    | .app f a      =>
      match concEval fuel γ f, concEval fuel γ a with
      | some (.lam x _dom body), some aVal =>
        concEval fuel ((x, aVal) :: γ) body
      | some (.fix inner), some aVal =>
        -- Function is a fixpoint thunk: unroll it and apply
        match concEval fuel γ (.fix inner) with
        | some (.lam x _dom body) => concEval fuel ((x, aVal) :: γ) body
        | some .type => some .type
        | some fVal => some (.app fVal aVal)
        | none => none
      | some .type, some _ => some .type  -- Type applied = Type (top absorbs)
      | some f', some a' => some (.app f' a')
      | _, _ => none

/-- Abstract evaluation (typing) with normalization under binders.
    `Γ ⊢ e ⇝ τ` is computed by `absEval fuel Γ e = some τ`.

    Lambda bodies are normalized under the binder (with the bound variable
    as neutral). This ensures that beta-redexes created by substitution are
    reduced, so e.g. `succ 2` has precise type `3`.

    Domains are NOT normalized, to preserve monotonicity: normalizing
    domains would make them vary with the environment, breaking the
    contravariant domain requirement of function subtyping. -/
def absEval (fuel : Nat) (Γ : Env) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .var x        => Γ.lookup x
    | .lam x dom body =>
      -- Normalize body under the binder: x is treated as neutral
      match absEval fuel ((x, .var x) :: Γ) body with
      | some body' => some (.lam x dom body')
      | none => none
    | .type         => some .type
    | .asc _term ty => absEval fuel Γ ty  -- compile-time: take the rhs
    | .fix inner =>
      match inner with
      | .lam _f dom _body =>
        -- Abstract eval of fix: return the declared type (the domain annotation).
        -- Well-typedness (checked separately) ensures the body satisfies this type.
        absEval fuel Γ dom
      | _ => none
    | .app f a      =>
      match absEval fuel Γ f, absEval fuel Γ a with
      | some (.lam x _dom body), some aVal =>
        -- Environment-based beta: extend env instead of substituting.
        -- body was already normalized under [(x, var x) :: Γ_def], so x
        -- appears as (var x). Extending env with (x, aVal) resolves it.
        -- This approach keeps the SAME body in both sides of monotonicity/
        -- soundness proofs, making the IH directly applicable.
        absEval fuel ((x, aVal) :: Γ) body
      | some .type, some _ => some .type  -- Type applied = Type (top absorbs)
      | some f', some a' => some (.app f' a')  -- stuck
      | _, _ => none

/-- Substitution-based concrete evaluator. Standard call-by-value lambda calculus.

    Unlike `concEval` (which uses an environment and normalizes under binders for
    proof convenience), this evaluator uses substitution and treats lambdas as
    values — their bodies are NOT evaluated until applied. This is the standard
    CBV semantics from §4.1 of the spec.

    **Why this exists alongside concEval:**
    `concEval` normalizes under binders so it's structurally parallel to `absEval`,
    making the soundness proof a straightforward induction. But normalization under
    binders breaks Church-encoded branching with recursion: both branches of a
    conditional are eagerly evaluated, causing recursive branches to diverge even
    when not taken. `concEvalS` doesn't have this problem.

    **Thunking convention:** Because `concEvalS` is call-by-value (arguments are
    evaluated before being passed), Church-encoded branching still evaluates both
    arguments. To enable recursion with Church booleans, wrap branches in thunks:
    instead of `(isZero n) Nat base rec`, use
    `(isZero n) (Unit→Nat) (λ_.base) (λ_.rec) unit`.
    The thunk lambdas are values (not evaluated), so the unused branch is never
    entered. The selected thunk is then applied to unit to force it.

    **Soundness:** Not yet proven with respect to `absEval`. This requires either:
    (a) a substitution lemma for SubtypeTrans (hard because lam_body needs same domain), or
    (b) a logical-relations/step-indexed approach.
    See DECISION-LOG.md for the full analysis. -/
def concEvalS (fuel : Nat) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .var _ => none  -- free variable = stuck (expects closed terms)
    | .lam _ _ _ => some e  -- lambda is a VALUE — body not evaluated
    | .type => some .type
    | .asc term _ => concEvalS fuel term  -- runtime: erase ascription
    | .fix inner =>
      match inner with
      | .lam f _dom body =>
        -- Unroll: substitute self-reference into body, then evaluate
        concEvalS fuel (body.subst f (.fix inner))
      | _ => none
    | .app f a =>
      match concEvalS fuel f, concEvalS fuel a with
      | some (.lam x _dom body), some aVal =>
        -- Beta-reduce via substitution (not env extension)
        concEvalS fuel (body.subst x aVal)
      | some (.fix inner), some aVal =>
        -- Fix in function position: unroll and retry
        match concEvalS fuel (.fix inner) with
        | some (.lam x _dom body) => concEvalS fuel (body.subst x aVal)
        | some .type => some .type
        | some fVal => some (.app fVal aVal)
        | none => none
      | some .type, some _ => some .type
      | some fVal, some aVal => some (.app fVal aVal)
      | _, _ => none
