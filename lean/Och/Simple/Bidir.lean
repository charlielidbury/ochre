import Och.Simple.Syntax
import Och.Simple.Subtype

/-!
# Bidirectional Type Checker for Simple Och

A **total**, fuel-bounded bidirectional checker with three mutually recursive
functions:

- `synth  : Nat → Ctx → Expr → Option Expr`
- `check  : Nat → Ctx → Expr → Expr → Bool`
- `subCheck : Nat → List (Expr × Expr) → Ctx → Expr → Expr → Bool`

The `seen` set inside `subCheck` tracks `(a, μA.b)` pairs already explored on
the RHS so that self-types can be decided by cycle detection (the algorithmic
analogue of the `muR` rule, which is NOT part of the inductive `Sub`).

## Architectural role

This checker is the *computational* type system for the "check-primary"
architecture: **the checker IS the type system**. Soundness is proved as
"check is preserved under evaluation" rather than via the inductive `Sub`.
See `Och.Simple.CheckPrimary` for the semantic side.

## Relationship to inductive `Sub`

The existing inductive `Sub` has exactly 8 rules (Refl, Top, Var, Lam, App,
Asc-L, Asc-R, Mu). The checker *extends* this with self-type introduction via
cycle detection. In other words, the checker may return `true` for some pairs
that are not derivable in the inductive `Sub`; these extra acceptances are
exactly the self-type ("muR") cases, which we handle purely computationally.

## Termination

Each mutually recursive call strictly decreases `fuel`. Using a well-founded
recursion measure `fuel` on the outer argument, Lean accepts the defs as
total (non-`partial`).
-/

set_option autoImplicit false

namespace Och.Simple

open Expr

-- ============================================================
-- Seen-set membership (for cycle detection)
-- ============================================================

/-- Check if a pair `(a, b)` is in the seen set. -/
def seenMember (seen : List (Expr × Expr)) (a b : Expr) : Bool :=
  seen.any (fun p => decide (p.1 = a) && decide (p.2 = b))

-- ============================================================
-- Synth + Check + SubCheck (mutually fuel-bounded, TOTAL)
-- ============================================================

mutual
  /-- `synth fuel Γ e` returns the type of `e` in `Γ` (if any). -/
  def synth (fuel : Nat) (Γ : Ctx) (e : Expr) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match e with
      | .top => some .top
      | .var x => Γ.get? x
      | .lam D body =>
        match synth fuel Γ D with
        | some _ =>
          match synth fuel (D :: Γ) body with
          | some _ => some (.lam D body)  -- lambda IS its own type
          | none => none
        | none => none
      | .asc e τ =>
        match synth fuel Γ τ with
        | some _ =>
          if check fuel Γ e τ then some τ else none
        | none => none
      | .app f a =>
        match synth fuel Γ f with
        | some (.lam D R) =>
          if check fuel Γ a D then some (R.subst 0 a) else none
        | _ => none
      | .mu A body =>
        match synth fuel Γ A with
        | some _ =>
          if check fuel (A :: Γ) body (A.shift 0 1) then some A else none
        | none => none

  /-- `check fuel Γ e τ` returns `true` iff the checker accepts `e ⊑ τ`.
      It delegates to `subCheck` with an empty seen set so that [Refl],
      [Top], [Var], and self-type introduction can fire without a prior
      synthesis step. -/
  def check (fuel : Nat) (Γ : Ctx) (e τ : Expr) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 => subCheck fuel [] Γ e τ

  /-- [App] rule helper: LHS is `.app f arg`. Tries (A) synth-then-apply
      and (B) beta-reduction of the head. -/
  def subCheckApp (fuel : Nat) (seen : List (Expr × Expr)) (Γ : Ctx)
      (f arg b : Expr) : Bool :=
    -- Strategy A: synth the head, then apply [App] directly.
    let tryApp : Bool :=
      match synth fuel Γ f with
      | some (.lam D R) =>
        subCheck fuel seen Γ f (.lam D R) &&
        subCheck fuel seen Γ arg D &&
        subCheck fuel seen Γ (R.subst 0 arg) b
      | _ => false
    -- Strategy B: beta-reduce the head (unfold μ or substitute λ).
    let tryBeta : Bool :=
      match f with
      | .lam _ body => subCheck fuel seen Γ (body.subst 0 arg) b
      | .mu A bodyF =>
        let unfolded := bodyF.subst 0 (.mu A bodyF)
        match unfolded with
        | .lam _ body => subCheck fuel seen Γ (body.subst 0 arg) b
        | _ => subCheck fuel seen Γ (.app unfolded arg) b
      | _ => false
    tryApp || tryBeta

  /-- [Mu-L] rule helper: LHS is `.mu A body`. Tries (1) annotation,
      (2) unfolding, and (3) — when RHS is also a μ — muR with cycle
      detection. -/
  def subCheckMuL (fuel : Nat) (seen : List (Expr × Expr)) (Γ : Ctx)
      (A body b : Expr) : Bool :=
    -- Strategy 1: annotation.
    (subCheck fuel seen Γ A b && subCheck fuel seen (A :: Γ) body (A.shift 0 1))
    -- Strategy 2: unfold.
    || subCheck fuel seen Γ (body.subst 0 (.mu A body)) b
    -- Strategy 3: if b is also μ, try muR with cycle detection.
    || (match b with
        | .mu A' body' =>
          if seenMember seen (.mu A body) (.mu A' body') then
            true
          else
            let seen' := (.mu A body, .mu A' body') :: seen
            subCheck fuel seen' Γ (.mu A body) A' &&
            subCheck fuel seen' Γ (.mu A body) (body'.subst 0 (.mu A body))
        | _ => false)

  /-- `subCheck fuel seen Γ a b` attempts to decide `a ⊑ b` with the given
      fuel, using `seen` to track self-type assumptions for cycle detection. -/
  def subCheck (fuel : Nat) (seen : List (Expr × Expr)) (Γ : Ctx) (a b : Expr) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      if decide (a = b) then true                   -- [Refl]
      else match b with
      | .top => true                                -- [Top]
      | .asc eτ τ =>                                -- [Asc-R]
        subCheck fuel seen Γ eτ τ && subCheck fuel seen Γ a eτ
      | .mu A body =>                               -- [Mu-R] + cycle
        -- Give [Mu-L] a chance first if a is itself a μ.
        match a with
        | .mu Aa bodya => subCheckMuL fuel seen Γ Aa bodya (.mu A body)
        | _ =>
          if seenMember seen a (.mu A body) then
            true
          else
            let seen' := (a, .mu A body) :: seen
            subCheck fuel seen' Γ a A &&
            subCheck fuel seen' Γ a (body.subst 0 a)
      | _ =>
        match a with
        -- [Var]: LHS is a variable — look up and recurse.
        | .var x =>
          match Γ.get? x with
          | some T => subCheck fuel seen Γ T b
          | none => false
        -- [Lam]: both sides must be lambdas.
        | .lam A body₁ =>
          match b with
          | .lam B body₂ =>
            subCheck fuel seen Γ B A && subCheck fuel seen (B :: Γ) body₁ body₂
          | _ => false
        -- [App]: LHS is an application — delegate to helper.
        | .app f arg => subCheckApp fuel seen Γ f arg b
        -- [Asc-L]: ascription on LHS.
        | .asc e τ =>
          subCheck fuel seen Γ e τ && subCheck fuel seen Γ τ b
        -- [Mu-L]: LHS is a μ — delegate to helper.
        | .mu A body => subCheckMuL fuel seen Γ A body b
        -- Remaining LHS shapes don't match the RHS.
        | .top => false
end

-- ============================================================
-- Basic sanity checks
-- ============================================================

-- Refl
#eval subCheck 10 [] [] .top .top                                 -- true
#eval subCheck 10 [] [] (.var 0) (.var 0)                         -- true

-- Top
#eval subCheck 10 [] [] (.var 0) .top                             -- true
#eval subCheck 10 [] [] (.lam .top (.var 0)) .top                 -- true

-- Lam
#eval subCheck 10 [] [] (.lam .top (.var 0)) (.lam .top (.var 0)) -- true

-- Var via context
#eval subCheck 10 [] [.top] (.var 0) .top                         -- true

-- Negative
#eval subCheck 10 [] [] .top (.lam .top (.var 0))                 -- false

-- Synth
#eval synth 10 [] .top                                            -- some top
#eval synth 10 [] (.lam .top (.var 0))                            -- some (lam ...)
#eval synth 10 [] (.asc .top .top)                                -- some top

-- Check
#eval check 10 [] .top .top                                       -- true
#eval check 10 [] (.lam .top (.var 0)) (.lam .top .top)           -- true

end Och.Simple
