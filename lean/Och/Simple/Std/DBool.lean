import Och.Simple.Macro
import Och.Simple.Subtype
import Och.Simple.Eval
import Och.Simple.Std.Bool

/-!
# Dependent Booleans (self-type encoding) for Simple Och

Scott-style dependent Bool where the return type of elimination depends
on the value being eliminated.

```
dtrue  = mu(dtrue : T). λP:(dtrue -> T). λt:(P dtrue). λf:T. t
dfalse = mu(dfalse : T). λP:(dfalse -> T). λt:T. λf:(P dfalse). f
dBool  = mu(dBool : T). λP:(dBool -> T). λt:(P dtrue). λf:(P dfalse). P dBool
```

Key properties:
- Dependent: motive P can vary over which boolean is eliminated
- Each constructor constrains P's domain to itself (not dBool) for self-type intro
- dtrue has λf:T (f unused, domain is Top for covariance)
- dfalse has λt:T (t unused, domain is Top for covariance)
-/

set_option autoImplicit false

namespace Och.Simple.Std

open Och.Simple Expr

-- ============================================================
-- Definitions
-- ============================================================

/-- dtrue: eliminates to the "then" branch. Motive P applied to dtrue itself. -/
def dtrue : Expr := soch{ μ(dtrue : ⊤). λ(P : dtrue → ⊤). λ(t : P dtrue). λ(f : ⊤). t }

/-- dfalse: eliminates to the "else" branch. Motive P applied to dfalse itself. -/
def dfalse : Expr := soch{ μ(dfalse : ⊤). λ(P : dfalse → ⊤). λ(t : ⊤). λ(f : P dfalse). f }

/-- dBool: the dependent boolean type. -/
def dBool : Expr := soch{ μ(dBool : ⊤). λ(P : dBool → ⊤). λ(t : P dtrue). λ(f : P dfalse). P dBool }

/-- dnot: dependent boolean negation -/
def dnot : Expr := soch{ λ(b : dBool). b (dBool → dBool) dfalse dtrue }

/-- dand: dependent boolean conjunction -/
def dand : Expr := soch{ λ(a : dBool). λ(b : dBool). a (dBool → dBool) b dfalse }

-- Free variable markers (soch{} cannot contain .var literals)
private def x42 : Expr := .var 42
private def x99 : Expr := .var 99
private def x1 : Expr := .var 1
private def x2 : Expr := .var 2

-- ============================================================
-- Evaluation tests
-- ============================================================

private def ev (e : Expr) : Option Expr := eval 200 e

-- dtrue P t f = t
example : ev (.app (.app (.app dtrue .top) x42) x99) = some x42 := rfl

-- dfalse P t f = f
example : ev (.app (.app (.app dfalse .top) x42) x99) = some x99 := rfl

-- dBool with constant motive: dBool (λ_.T) T T = T
example : ev (soch{ dBool (λ(_ : ⊤). ⊤) ⊤ ⊤ }) = some .top := rfl

-- dtrue selects first data arg, dfalse selects second
example : ev (.app (.app (.app dtrue .top) x1) x2) = some x1 := rfl
example : ev (.app (.app (.app dfalse .top) x1) x2) = some x2 := rfl

-- dnot: negation
-- dnot dtrue should behave like dfalse
example : ev (.app (.app (.app (soch{ dnot dtrue }) .top) x42) x99) = some x99 := rfl
-- dnot dfalse should behave like dtrue
example : ev (.app (.app (.app (soch{ dnot dfalse }) .top) x42) x99) = some x42 := rfl

-- dand truth table
example : ev (.app (.app (.app (soch{ dand dtrue dtrue }) .top) x42) x99) = some x42 := rfl
example : ev (.app (.app (.app (soch{ dand dtrue dfalse }) .top) x42) x99) = some x99 := rfl
example : ev (.app (.app (.app (soch{ dand dfalse dtrue }) .top) x42) x99) = some x99 := rfl
example : ev (.app (.app (.app (soch{ dand dfalse dfalse }) .top) x42) x99) = some x99 := rfl

-- ============================================================
-- Sub derivations (what currently works)
-- ============================================================

-- dtrue <= T (trivially)
example : Sub [] dtrue .top := Sub.top [] dtrue

-- dfalse <= T (trivially)
example : Sub [] dfalse .top := Sub.top [] dfalse

-- dBool <= T (trivially)
example : Sub [] dBool .top := Sub.top [] dBool

-- Self-subtyping (refl)
example : Sub [] dtrue dtrue := Sub.refl [] dtrue
example : Sub [] dfalse dfalse := Sub.refl [] dfalse
example : Sub [] dBool dBool := Sub.refl [] dBool

-- dtrue <= T via mu rule
-- A = T, need: T <= T (refl) and [T] |- body <= T (by Top)
example : Sub [] dtrue .top :=
  Sub.mu [] .top _ .top
    (Sub.refl [] .top)
    (Sub.top [.top] _)

-- dfalse <= T via mu rule
example : Sub [] dfalse .top :=
  Sub.mu [] .top _ .top
    (Sub.refl [] .top)
    (Sub.top [.top] _)

-- ============================================================
-- Self-type intro via Sub.muR (expressive form, self = subject)
-- ============================================================

-- Sanity check: trivial muR — top ⊑ μ(⊤). ⊤
-- Using the expressive muR with self = .top: needs .top ⊑ ⊤ and .top ⊑ ⊤[0:=.top] = ⊤.
example : Sub [] .top (.mu .top .top) :=
  Sub.muR [] .top .top .top
    (Sub.top [] .top)
    (Sub.top [] .top)

-- ── Sub [] dtrue dBool via expressive muR + muUnfoldL ────
-- Strategy:
--   1. Outer: Sub.muR dtrue dBool. Needs dtrue ⊑ ⊤ (annotation) and
--      dtrue ⊑ dBool.body[0 := dtrue]. dBool.body[0 := dtrue] =
--        λ(dtrue→⊤). λ(app (var 0) dtrue). λ(app (var 1) dfalse).
--          (app (var 2) dtrue)
--   2. For the body premise: muUnfoldL on dtrue, giving dtrue's unfolded
--      body = λ(dtrue→⊤). λ(app (var 0) dtrue). λ⊤. (var 1)
--      and the well-typedness premise b ⊑ ⊤ (shifted), trivial by top.
--   3. Compare the two lam-lam-lam structures: domains match at each
--      layer, then the innermost lam has LHS domain ⊤ vs RHS domain
--      (app (var 1) dfalse) — contravariant, needs RHS ⊑ ⊤ (by top).
--      The innermost body compares (var 1) vs (app (var 2) dtrue).
--      By Sub.var, var 1 has type E.shift 0 2 = (app (var 2) dtrue), so
--      refl closes it.
example : Sub [] dtrue dBool := by
  -- Unfold the definitions (requires Lean to compute them).
  show Sub [] (.mu .top _) (.mu .top _)
  apply Sub.muR _ _ .top _
  · exact Sub.top [] dtrue
  · -- Need: Sub [] dtrue (dBool.body.subst 0 dtrue)
    -- dtrue = .mu .top dtrue_body. Use muUnfoldL.
    apply Sub.muUnfoldL _ .top _
    · -- body ⊑ ⊤.shift in .top :: []
      exact Sub.top _ _
    · -- dtrue_body[0 := dtrue] ⊑ dBool.body[0 := dtrue]
      -- Both sides are closed lambdas. Compare structurally.
      show Sub [] _ _
      -- Outer λ: dtrue → ⊤ on both sides
      apply Sub.lam
      · exact Sub.refl _ _
      · -- Under [dtrue → ⊤]:
        -- LHS: λ(app (var 0) dtrue). λ⊤. (var 1)
        -- RHS: λ(app (var 0) dtrue). λ(app (var 1) dfalse). (app (var 2) dtrue)
        apply Sub.lam
        · exact Sub.refl _ _
        · -- Under [app (var 0) dtrue; dtrue → ⊤]:
          -- LHS: λ⊤. (var 1)
          -- RHS: λ(app (var 1) dfalse). (app (var 2) dtrue)
          apply Sub.lam
          · -- contravariant domain: (app (var 1) dfalse) ⊑ ⊤
            exact Sub.top _ _
          · -- Under [app (var 1) dfalse; app (var 0) dtrue; dtrue → ⊤]:
            -- Goal: var 1 ⊑ app (var 2) dtrue
            -- var 1 has type (app (var 0) dtrue).shift 0 2 = app (var 2) dtrue
            apply Sub.var _ 1 _ (.app (.var 2) dtrue)
            · -- Ctx.get? proof
              show Ctx.get? _ 1 = some _
              -- Compute Ctx.get?
              rfl
            · exact Sub.refl _ _

-- ── Sub [] dfalse dBool via expressive muR + muUnfoldL ────
-- Symmetric to dtrue ⊑ dBool. dfalse differs: its body has λ⊤ in the
-- "t" position (not "f"). The key insight: the var `f` (var 0 inside
-- the innermost λ) has type (app (var 1) dfalse) = (P dfalse), matching
-- the dBool.body[0:=dfalse] third-arg position.
example : Sub [] dfalse dBool := by
  show Sub [] (.mu .top _) (.mu .top _)
  apply Sub.muR _ _ .top _
  · exact Sub.top [] dfalse
  · apply Sub.muUnfoldL _ .top _
    · exact Sub.top _ _
    · -- dfalse_body[0:=dfalse] ⊑ dBool.body[0:=dfalse]
      -- dfalse_body = λ(dfalse→⊤). λ⊤. λ(app (var 1) dfalse). (var 0)
      -- After subst 0 dfalse (closed): same structure with dfalse values
      -- dBool.body[0:=dfalse] = λ(dfalse→⊤). λ(app (var 0) dtrue). λ(app (var 1) dfalse). (app (var 2) dfalse)
      show Sub [] _ _
      apply Sub.lam
      · exact Sub.refl _ _                        -- dfalse → ⊤  matches
      · apply Sub.lam
        · -- LHS domain: ⊤, RHS domain: (app (var 0) dtrue)
          -- contravariant: (app (var 0) dtrue) ⊑ ⊤
          exact Sub.top _ _
        · apply Sub.lam
          · -- (app (var 1) dfalse) ⊑ (app (var 1) dfalse) — refl
            exact Sub.refl _ _
          · -- Goal: var 0 ⊑ (app (var 2) dfalse)
            -- var 0 has type (app (var 1) dfalse).shift 0 1 = app (var 2) dfalse
            apply Sub.var _ 0 _ (.app (.var 2) dfalse)
            · rfl
            · exact Sub.refl _ _

-- ASPIRATIONAL: dependent elimination with typed motive
-- Given dtrue <= dBool and a motive P : dBool -> T,
-- we could type the elimination dtrue P t f : P dtrue
-- Flip condition: Sub.muR + possible BetaR for type computation
-- example : Sub [] (dtrue_applied_to_depMotive) depMotiveResult := ...

end Och.Simple.Std
