import Och.Simple.Syntax
import Och.Simple.Subtype

/-!
# Decision procedure for the Sub relation

A fuel-based algorithm `check : Nat → Ctx → Expr → Expr → Option Bool` that
attempts to decide `Sub Γ a b`. Returns:
- `some true`  — the algorithm believes `a ⊑ b` holds
- `some false` — the algorithm believes `a ⊑ b` does not hold
- `none`       — out of fuel (could not decide)

## Design

The algorithm is syntax-directed: it pattern-matches on the shapes of `a` and `b`
and follows a deterministic strategy. Key decisions:

1. **[Refl]** and **[Top]** are checked first (fast paths).
2. **[Var]** fires when LHS is a variable — look up context and recurse.
3. **[Lam]** fires when both sides are lambdas — contravariant domain, covariant body.
4. **[App]** fires when LHS is an application — synthesize the type of `f`, extract D and R.
5. **[Asc-L/R]** fire when the relevant side is an ascription.
6. **[Mu on LHS]** — try annotation first (`A ⊑ b`), then fallback to unfold.
7. **[Mu on RHS]** — `a ⊑ A` and `a ⊑ body[0 := a]`.

The key helper is `synth`, which computes the "type" of an expression —
i.e., the smallest supertype the algorithm can determine syntactically.
For [App], `synth Γ f` must return a lambda `lam D R` so we can extract D, R.

## Limitations

- **Fuel**: terminates trivially but may return `none` on valid judgements.
- **Completeness**: the deterministic strategy may miss valid derivations.
- **synth coverage**: synth may fail on complex terms, causing check to give up.
-/

set_option autoImplicit false

namespace Och.Simple

open Expr

-- ============================================================
-- Helper: synthesize the "type" of an expression
-- ============================================================

/-- Synthesize the type of an expression. Returns a supertype that the
    expression can be shown to inhabit syntactically. This is used to
    resolve the existential D, R in the [App] rule.

    - `var x` → look up Γ(x)
    - `lam D body` → `lam D body` (it IS its own type)
    - `app f arg` → synth f, extract (D, R), return R[0 := arg]
    - `asc e τ` → τ
    - `mu A body` → A (the annotation); if that's not a lambda, try unfolding
    - `top` → `top` -/
def synth (fuel : Nat) (seen : List (Expr × Expr)) (Γ : Ctx) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .var x => Γ.get? x
    | .lam D body => some (.lam D body)
    | .app f arg => do
      let fTy ← synth fuel seen Γ f
      match fTy with
      | .lam _D R => some (R.subst 0 arg)
      | _ => none
    | .asc _e τ => some τ
    | .mu A body =>
      -- Try annotation first; if it's not a lambda, try unfolding
      match A with
      | .lam _ _ => some A
      | _ =>
        -- Unfold: synth the body with self replaced
        synth fuel seen Γ (body.subst 0 (.mu A body))
    | .top => some .top

-- ============================================================
-- The decision procedure
-- ============================================================

/-- Fuel-based decision procedure for `Sub Γ a b`.
    Returns `some true` if the algorithm determines `a ⊑ b`,
    `some false` if it determines `a ⋢ b`, `none` if out of fuel.

    The `seen` parameter tracks pairs `(a, μA.body)` for cycle detection
    in the muR rule (self-type intro on the RHS). When we encounter
    `a ⊑ μA.body` and `(a, μA.body)` is already in `seen`, we return
    `true` (coinductive assumption: the cycle is valid). -/
def check (fuel : Nat) (seen : List (Expr × Expr)) (Γ : Ctx) (a b : Expr) : Option Bool :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    -- Fast paths
    if a == b then some true           -- [Refl]
    else match b with
    | .top => some true                -- [Top]
    | _ =>
    match a, b with
    -- [Var]: look up context
    | .var x, _ =>
      match Γ.get? x with
      | some T => check fuel seen Γ T b
      | none => some false
    -- [Lam]: both sides are lambdas
    | .lam A body₁, .lam B body₂ =>
      match check fuel seen Γ B A with
      | some true =>
        check fuel seen (B :: Γ) body₁ body₂
      | other => other
    -- [App]: LHS is an application
    | .app f arg, _ =>
      -- Helper: try [App] with specific D, R witnesses
      let tryWithDR (D R : Expr) : Option Bool :=
        match check fuel seen Γ f (.lam D R) with
        | some true =>
          match check fuel seen Γ arg D with
          | some true => check fuel seen Γ (R.subst 0 arg) b
          | other => other
        | other => other
      -- Helper: try unfolding f if it's a mu, synth the unfolded form
      let tryUnfolded : Option Bool :=
        match f with
        | .mu _A bodyF =>
          match synth fuel seen Γ (bodyF.subst 0 f) with
          | some (.lam D R) => tryWithDR D R
          | _ => some false
        | _ => some false
      -- Strategy 1: use synth to find D, R from f directly
      match synth fuel seen Γ f with
      | some (.lam D R) =>
        match tryWithDR D R with
        | some true => some true
        | some false => tryUnfolded  -- annotation-based D,R failed; try unfolded
        | none => none
      | _ => tryUnfolded
    -- [Asc-L]: ascription on LHS
    | .asc e τ, _ =>
      match check fuel seen Γ e τ with
      | some true => check fuel seen Γ τ b
      | other => other
    -- [Mu on LHS]: try annotation (with body well-typedness check), then muR, then unfold
    | .mu A bodyA, _ =>
      -- Strategy 1: [Mu] use annotation: A ⊑ b AND body ⊑ A↑ (in ctx A :: Γ)
      match check fuel seen Γ A b with
      | some true =>
        match check fuel seen (A :: Γ) bodyA (A.shift 0 1) with
        | some true => some true
        | _ =>
          -- Body well-typedness failed, fall through to other strategies
          match b with
          | .mu Ab bodyB =>
            match check fuel seen Γ (.mu A bodyA) Ab with
            | some true =>
              match check fuel seen Γ (.mu A bodyA) (bodyB.subst 0 (.mu A bodyA)) with
              | some true => some true
              | _ => check fuel seen Γ (bodyA.subst 0 (.mu A bodyA)) b
            | _ => check fuel seen Γ (bodyA.subst 0 (.mu A bodyA)) b
          | _ => check fuel seen Γ (bodyA.subst 0 (.mu A bodyA)) b
      | _ =>
      -- Strategy 2: [Mu-R] if RHS is also a mu, try self-type intro
      -- BEFORE unfolding LHS (preserves the mu wrapper for correct substitution)
      match b with
      | .mu Ab bodyB =>
        match check fuel seen Γ (.mu A bodyA) Ab with
        | some true =>
          match check fuel seen Γ (.mu A bodyA) (bodyB.subst 0 (.mu A bodyA)) with
          | some true => some true
          | _ =>
            -- muR failed, try muUnfoldL
            check fuel seen Γ (bodyA.subst 0 (.mu A bodyA)) b
        | _ =>
          -- Annotation check of muR failed, try muUnfoldL
          check fuel seen Γ (bodyA.subst 0 (.mu A bodyA)) b
      | _ =>
        -- RHS is not a mu, just unfold LHS
        check fuel seen Γ (bodyA.subst 0 (.mu A bodyA)) b
    -- At this point, a is not var/lam/app/asc/mu, so a must be .top
    -- and b is not .top (handled above) and a != b (handled above)
    -- Only remaining case: a = .top, b = something non-top
    | _, .asc e τ =>
      -- [Asc-R]: ascription on RHS
      match check fuel seen Γ e τ with
      | some true => check fuel seen Γ a e
      | other => other
    | _, .mu Ab bodyB =>
      -- [Mu-R]: self-type intro on RHS with cycle detection
      if seen.any (fun p => p.1 == a && p.2 == .mu Ab bodyB) then
        some true  -- Cycle detected: coinductive assumption
      else
        let seen' := (a, .mu Ab bodyB) :: seen
        match check fuel seen' Γ a Ab with
        | some true =>
          check fuel seen' Γ a (bodyB.subst 0 a)
        | other => other
    | _, _ => some false

-- ============================================================
-- Pretty-printer for debugging
-- ============================================================

/-- Show the result of check in a human-readable way. -/
def checkShow (fuel : Nat) (Γ : Ctx) (a b : Expr) : String :=
  match check fuel [] Γ a b with
  | some true => "YES"
  | some false => "NO"
  | none => "FUEL"

-- ============================================================
-- Basic sanity tests
-- ============================================================

-- [Refl]: a ⊑ a
#eval check 10 [] [] .top .top                          -- some true
#eval check 10 [] [] (.var 0) (.var 0)                  -- some true

-- [Top]: a ⊑ ⊤
#eval check 10 [] [] (.var 0) .top                      -- some true
#eval check 10 [] [] (.lam .top (.var 0)) .top          -- some true

-- [Lam]: λ⊤.0 ⊑ λ⊤.0
#eval check 10 [] [] (.lam .top (.var 0)) (.lam .top (.var 0))  -- some true

-- [Var]: x:⊤ ⊢ x ⊑ ⊤
#eval check 10 [] [.top] (.var 0) .top                  -- some true

-- Negative: ⊤ ⊑ λ⊤.0 should fail
#eval check 10 [] [] .top (.lam .top (.var 0))          -- some false

end Och.Simple
