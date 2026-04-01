import Och.Syntax

/-!
# Och Evaluation

Two evaluation modes that diverge only at ascription:
- **Concrete (runtime):** `(e : τ)` takes the lhs `e`.
- **Abstract (compile-time):** `(e : τ)` takes the rhs `τ`.

Compiling an Och program is just running it in abstract mode. Whether this
dual-interpretation is sound is a central research question.

## mu semantics

`mu x ann body` is the unified self-reference primitive (replaces fix + iota):
- **Concrete eval:** unroll — evaluate body with x bound to the mu itself.
  This is the fix behavior: the recursive binding refers to the whole mu.
- **Abstract eval:** normalize body under the binder (x as neutral) and
  normalize ann; return `mu x ann' body'`. This is the iota behavior:
  the self type is preserved, not unrolled.
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
    | .mu x ann body =>
      -- Unroll: evaluate body with x bound to the mu itself (like fix).
      concEval fuel ((x, .mu x ann body) :: γ) body
    | .app f a      =>
      match concEval fuel γ f, concEval fuel γ a with
      | some (.lam x _dom body), some aVal =>
        concEval fuel ((x, aVal) :: γ) body
      | some (.mu x ann body), some aVal =>
        -- mu in function position: unroll it, then apply the result
        match concEval fuel γ (.mu x ann body) with
        | some (.lam y _dom lamBody) => concEval fuel ((y, aVal) :: γ) lamBody
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
    | .mu x ann body =>
      -- Normalize body under binder (iota behavior) AND normalize annotation.
      -- Returns the mu as a self-type value, not the annotation.
      match absEval fuel ((x, .var x) :: Γ) body with
      | some body' =>
        match absEval fuel Γ ann with
        | some ann' => some (.mu x ann' body')
        | none => none
      | none => none
    | .app f a      =>
      match absEval fuel Γ f, absEval fuel Γ a with
      | some (.lam x _dom body), some aVal =>
        -- Environment-based beta: extend env instead of substituting.
        absEval fuel ((x, aVal) :: Γ) body
      | some (.mu x ann body), some aVal =>
        -- mu in function position. Two strategies depending on annotation:
        --
        -- 1. If ann is informative (a lambda): use it to determine the return
        --    type. This avoids divergence for recursive mus (fix-like), where
        --    unfolding the body would substitute the mu back in and cause
        --    infinite recursion in abstract mode.
        --
        -- 2. If ann is uninformative (Type): fall back to body unfolding
        --    (self-type elimination). This handles iota-like mus where the
        --    body is the interesting part (e.g., SelfNat = mu n Type Nat').
        match absEval fuel Γ ann with
        | some (.lam y _dom retBody) =>
          -- Annotation is a function type: beta-reduce with the argument.
          absEval fuel ((y, aVal) :: Γ) retBody
        | _ =>
          -- Annotation uninformative. Unfold body (self-type elimination).
          let unfolded := body.subst x (.mu x ann body)
          match absEval fuel Γ unfolded with
          | some (.lam y _dom retBody) =>
            absEval fuel ((y, aVal) :: Γ) retBody
          | some .type => some .type
          | some f' => some (.app f' aVal)
          | none => none
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
    | .mu x ann body =>
      -- Unroll: substitute self-reference into body, then evaluate
      concEvalS fuel (body.subst x (.mu x ann body))
    | .app f a =>
      match concEvalS fuel f, concEvalS fuel a with
      | some (.lam x _dom body), some aVal =>
        -- Beta-reduce via substitution (not env extension)
        concEvalS fuel (body.subst x aVal)
      | some (.mu x ann body), some aVal =>
        -- mu in function position: unroll and retry
        match concEvalS fuel (.mu x ann body) with
        | some (.lam y _dom lamBody) => concEvalS fuel (lamBody.subst y aVal)
        | some .type => some .type
        | some fVal => some (.app fVal aVal)
        | none => none
      | some .type, some _ => some .type
      | some fVal, some aVal => some (.app fVal aVal)
      | _, _ => none
