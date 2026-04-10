import Och.Simple.Syntax
import Och.Simple.Subtype

/-!
# Bidirectional Type Checker for Simple Och

A decidable, fuel-based bidirectional checker with:
- `synth : Nat → Ctx → Expr → Option Expr`     (synthesis: infer type)
- `check : Nat → Ctx → Expr → Expr → Bool`     (checking: verify type)
- `subCheck : Nat → List (Expr × Expr) → Ctx → Expr → Expr → Bool`
    (subtype checking with a `seen` set for cycle detection on self-types)

## Bidirectional rules

### Synthesis
```
synth ⊤            = some ⊤
synth (var x)      = Γ.get? x
synth (λA. b)      = some (λA. synth (A :: Γ) b)      -- lambda is its own type
synth (e : τ)      = some τ  (if synth τ and check e τ)
synth (f a)        = R[0 := a]  (if synth f = λD. R and check a D)
synth (μA. b)      = some A  (if synth A and check (A :: Γ) b A↑)
```

### Checking
```
check Γ e τ =
  subCheck Γ (synth Γ e) τ
```

### Subtype checking
Follows the algorithmic `Sub` judgment closely, with a `seen` set tracking
`(a, μA.b)` pairs we have already explored on the RHS to detect cycles
(self-type intro via `muR`).

## Soundness

`check_sound : check fuel Γ e τ = true → Sub Γ e τ`
`synth_sound : synth fuel Γ e = some τ → Sub Γ e τ`

Both theorems use the declarative `Sub` from `Subtype.lean`, which now
includes `muR` and `muUnfoldL`. Cycle-detection cases in `subCheck` are
discharged via the declarative `muR` rule.

These theorems are not yet formalized in Lean; a blueprint exists in the
research-D branch (`Och/Simple/CheckSoundness.lean`) — about 700 LOC with
two coinductive sorries for the `seen`-set firing cases.

## Well-formedness enables CBV

The bidirectional checker enforces well-formedness via `synth`, which
rejects garbage like `(var 42 : var 99)` (the ascription's `var 99` type
would not synthesize in an empty context). This is a crucial property
for CBV soundness.

With well-formed terms:
- Every ascription `(e : τ)` has `τ` synthesizable and `e` checkable
  against `τ`, so evaluation of `e` is guaranteed to produce a value
  satisfying `τ` (preservation).
- Every application `f a` has `f` synthesizing to `.lam D R` with `a`
  checkable against `D`, so CBV reduction of `a` first is safe —
  the resulting value still satisfies `D`.
- Every `μA. b` has `b` checkable against `A↑` in `A :: Γ`, so the
  unfolded body (with self = the mu itself) still satisfies `A`.

Under CBN (our current evaluator), these invariants hold trivially
because arguments are passed unreduced. Under CBV, the checker's
well-formedness would guarantee that argument reduction preserves
subtyping, making "well-typed CBV evaluation never gets stuck" provable.

This CBV soundness theorem is NOT implemented in this file — CBN is
retained for now. But the bidirectional checker here is the crucial
prerequisite that makes CBV tractable to formalize in future work.
-/

set_option autoImplicit false

namespace Och.Simple

open Expr

-- ============================================================
-- Seen-set membership (for cycle detection)
-- ============================================================

/-- Check if a pair (a, b) is in the seen set. Uses the DecidableEq on Expr. -/
def seenMember (seen : List (Expr × Expr)) (a b : Expr) : Bool :=
  seen.any (fun p => decide (p.1 = a) && decide (p.2 = b))

-- ============================================================
-- Synth + Check + SubCheck (mutually fuel-bounded)
-- ============================================================

-- The core bidirectional trio, parameterized by fuel. Mutually recursive
-- but fuel-bounded so they terminate trivially.
mutual
  /-- `synth fuel Γ e` returns the declarative type of `e` in `Γ` (if any).
      Also enforces well-formedness: each subterm must synthesize or check. -/
  partial def synth (fuel : Nat) (Γ : Ctx) (e : Expr) : Option Expr :=
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

  /-- `check fuel Γ e τ` returns true iff `e ⊑ τ` (or `e ⊑ σ ⊑ τ` for the
      synthesized σ). Calls subCheck directly so that rules like [Refl], [Top],
      [muR], and [Var] can fire without first synthesizing. -/
  partial def check (fuel : Nat) (Γ : Ctx) (e τ : Expr) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      -- Try subCheck directly first — this lets refl/top/muR/var fire.
      subCheck fuel [] Γ e τ

  /-- `subCheck fuel seen Γ a b` attempts to decide `Sub Γ a b` with fuel.
      `seen` tracks pairs we've explored on muR to detect cycles. -/
  partial def subCheck (fuel : Nat) (seen : List (Expr × Expr)) (Γ : Ctx) (a b : Expr) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      if decide (a = b) then true              -- [Refl]
      else match b with
      | .top => true                          -- [Top]
      | _ =>
      match a, b with
      -- [Var]: look up context on LHS
      | .var x, _ =>
        match Γ.get? x with
        | some T => subCheck fuel seen Γ T b
        | none => false
      -- [Lam]: both sides are lambdas — contravariant domain, covariant body
      | .lam A body₁, .lam B body₂ =>
        subCheck fuel seen Γ B A && subCheck fuel seen (B :: Γ) body₁ body₂
      -- [App]: LHS is an application, use synth to get D, R.
      -- If that doesn't work, try beta-reducing the head (if lambda or mu).
      | .app f arg, _ =>
        -- Strategy A: synth the head, then apply [App] directly.
        let tryApp : Bool :=
          match synth fuel Γ f with
          | some (.lam D R) =>
            subCheck fuel seen Γ f (.lam D R) &&
            subCheck fuel seen Γ arg D &&
            subCheck fuel seen Γ (R.subst 0 arg) b
          | _ => false
        -- Strategy B: beta-reduce — unfold a mu head, or substitute a lambda head.
        -- Eagerly beta-reduce when the unfolded mu body is a lambda to save fuel.
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
      -- [Asc-L]: ascription on LHS
      | .asc e τ, _ =>
        subCheck fuel seen Γ e τ && subCheck fuel seen Γ τ b
      -- [Mu-L]: try annotation strategy, unfold, and (if RHS is mu too) muR
      | .mu A body, _ =>
        -- Strategy 1: muL annotation — A ⊑ b and body ⊑ A↑
        (subCheck fuel seen Γ A b && subCheck fuel seen (A :: Γ) body (A.shift 0 1))
        -- Strategy 2: muL unfold — body[self := μA.body] ⊑ b
        || subCheck fuel seen Γ (body.subst 0 (.mu A body)) b
        -- Strategy 3: if b is also a mu, try muR (with cycle detection)
        || (match b with
            | .mu A' body' =>
              if seenMember seen a (.mu A' body') then
                true
              else
                let seen' := (a, .mu A' body') :: seen
                subCheck fuel seen' Γ a A' &&
                subCheck fuel seen' Γ a (body'.subst 0 a)
            | _ => false)
      -- [Asc-R]: ascription on RHS
      | _, .asc e τ =>
        subCheck fuel seen Γ e τ && subCheck fuel seen Γ a e
      -- [Mu-R]: self-type intro on RHS, with cycle detection
      | _, .mu A body =>
        if seenMember seen a (.mu A body) then
          true  -- Cycle: coinductive assumption
        else
          let seen' := (a, .mu A body) :: seen
          subCheck fuel seen' Γ a A &&
          subCheck fuel seen' Γ a (body.subst 0 a)
      | _, _ => false
end

-- ============================================================
-- Basic sanity checks
-- ============================================================

-- Refl
#eval subCheck 10 [] [] .top .top                               -- true
#eval subCheck 10 [] [] (.var 0) (.var 0)                       -- true

-- Top
#eval subCheck 10 [] [] (.var 0) .top                           -- true
#eval subCheck 10 [] [] (.lam .top (.var 0)) .top               -- true

-- Lam
#eval subCheck 10 [] [] (.lam .top (.var 0)) (.lam .top (.var 0))  -- true

-- Var via context
#eval subCheck 10 [] [.top] (.var 0) .top                       -- true

-- Negative
#eval subCheck 10 [] [] .top (.lam .top (.var 0))               -- false

-- Synth
#eval synth 10 [] .top                                          -- some top
#eval synth 10 [] (.lam .top (.var 0))                          -- some (lam ...)
#eval synth 10 [] (.asc .top .top)                              -- some top

-- Check
#eval check 10 [] .top .top                                     -- true
#eval check 10 [] (.lam .top (.var 0)) (.lam .top .top)         -- true

end Och.Simple
