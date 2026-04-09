import Och.Simple.Macro
import Och.Simple.Subtype
import Och.Simple.Eval

/-!
# μ (self-reference) test suite for Simple Och

Tests eval behavior, Sub derivations, and Church-style encodings using μ.
-/

set_option autoImplicit false

namespace Och.Simple.MuTests

open Och.Simple Expr

-- ============================================================
-- 1. Basic μ tests
-- ============================================================

section BasicMu

/-- Trivial fixpoint: μ(f : ⊤). f — unfolds forever, eval runs out of fuel. -/
def FIX : Expr := soch{ μ(f : ⊤). f }

-- FIX diverges: eval with any fuel returns none (each step just unfolds again).
example : eval 1 FIX = none := rfl
example : eval 10 FIX = none := rfl
example : eval 100 FIX = none := rfl

/-- Constant top: μ(s : ⊤). ⊤ — body ignores self, unfolds to ⊤. -/
def CONST_TOP : Expr := soch{ μ(s : ⊤). ⊤ }

-- Unfolds: body[s := μs:⊤.⊤] = ⊤, which is a value.
example : eval 10 CONST_TOP = some .top := rfl

-- Sub: CONST_TOP ⊑ ⊤ via mu rule.
-- A = ⊤, need: ⊤ ⊑ ⊤ (refl) and [⊤] ⊢ ⊤ ⊑ ⊤↑ = ⊤ (refl).
example : Sub [] CONST_TOP .top :=
  Sub.mu [] .top .top .top
    (Sub.refl [] .top)
    (Sub.refl [.top] .top)

/-- Self-referential identity: μ(self : ⊤ → ⊤). λ(x : ⊤). x -/
def SELF_ID : Expr := soch{ μ(self : ⊤ → ⊤). λ(x : ⊤). x }

-- Unfolds: body[self := mu] = (λ⊤. var 0), which is a value.
-- (The self variable var 0 in body is the lambda param x, not self. After substitution,
--  self is gone and x becomes var 0 in the lambda.)
example : eval 10 SELF_ID = some (.lam .top (.var 0)) := rfl

-- Apply SELF_ID to ⊤: should return ⊤.
example : eval 10 (.app SELF_ID .top) = some .top := rfl

-- Sub: SELF_ID ⊑ ⊤ (trivially).
example : Sub [] SELF_ID .top :=
  Sub.top [] SELF_ID

-- Sub: SELF_ID ⊑ (⊤ → ⊤) via mu rule.
-- A = lam top top, need:
--   (⊤ → ⊤) ⊑ (⊤ → ⊤)  (refl)
--   [(⊤ → ⊤)] ⊢ λ(x : ⊤). x ⊑ (⊤ → ⊤)↑ = (⊤ → ⊤)
-- For the body check: λ⊤. var 0 ⊑ λ⊤. ⊤ via [Lam] + [Top].
-- Wait, (⊤ → ⊤)↑ = shift 0 1 (lam top top) = lam top top. Good.
-- Body: var 0 in ctx [(⊤→⊤)] refers to self. Under the mu binder,
-- body = lam top (var 0). We need [(⊤→⊤)] ⊢ lam top (var 0) ⊑ lam top top.
-- [Lam]: need ⊤ ⊑ ⊤ (refl) and [⊤, (⊤→⊤)] ⊢ var 0 ⊑ ⊤ (by [Top]).
example : Sub [] SELF_ID (.lam .top .top) :=
  Sub.mu [] (.lam .top .top) (.lam .top (.var 0)) (.lam .top .top)
    (Sub.refl [] (.lam .top .top))
    (Sub.lam [.lam .top .top] .top .top (.var 0) .top
      (Sub.refl [.lam .top .top] .top)
      (Sub.top [.top, .lam .top .top] (.var 0)))

/-- μ with a body that returns a constant — not self. -/
def MU_CONST_LAM : Expr := soch{ μ(s : ⊤). λ(x : ⊤). ⊤ }

-- Body ignores self, unfolds to λ⊤.⊤.
example : eval 10 MU_CONST_LAM = some (.lam .top .top) := rfl

-- Apply: (μs:⊤. λx:⊤. ⊤) ⊤ = ⊤
example : eval 10 (.app MU_CONST_LAM .top) = some .top := rfl

end BasicMu

-- ============================================================
-- 2. Church booleans via μ (for eval, not dependent)
-- ============================================================

section ChurchBoolMu

/-- Church true via μ — self-reference is unused. -/
def TRUE_MU : Expr := soch{ μ(self : ⊤). λ(t : ⊤). λ(f : ⊤). t }

/-- Church false via μ. -/
def FALSE_MU : Expr := soch{ μ(self : ⊤). λ(t : ⊤). λ(f : ⊤). f }

-- Eval: TRUE_MU unfolds to λt.λf.t
example : eval 10 TRUE_MU = some (.lam .top (.lam .top (.var 1))) := rfl

-- Eval: FALSE_MU unfolds to λt.λf.f
example : eval 10 FALSE_MU = some (.lam .top (.lam .top (.var 0))) := rfl

-- Application: TRUE_MU a b = a
-- Use var 42 and var 99 as distinct markers.
example : eval 100 (.app (.app TRUE_MU (.var 42)) (.var 99)) = some (.var 42) := rfl

-- Application: FALSE_MU a b = b
example : eval 100 (.app (.app FALSE_MU (.var 42)) (.var 99)) = some (.var 99) := rfl

end ChurchBoolMu

-- ============================================================
-- 3. Dependent booleans (self-type encoding)
-- ============================================================

section DBool

/-!
  Dependent booleans use self-types so the motive P is applied to the
  SPECIFIC constructor, enabling dependent elimination.

  The encoding (in named notation):
  ```
  dtrue  = μ(dtrue : ⊤). λ(P : dtrue → ⊤). λ(t : P dtrue). λ(f : ⊤). t
  dfalse = μ(dfalse : ⊤). λ(P : dfalse → ⊤). λ(t : ⊤). λ(f : P dfalse). f
  dBool  = μ(dBool : ⊤). λ(P : dBool → ⊤). λ(t : P dtrue). λ(f : P dfalse). P dBool
  ```

  In Simple Och, ⊤ plays the role of the universe (Type in full Och).
-/

/-- dtrue: eliminates to the "then" branch. Motive P is applied to dtrue itself. -/
def dtrue : Expr := soch{ μ(dtrue : ⊤). λ(P : dtrue → ⊤). λ(t : P dtrue). λ(f : ⊤). t }

/-- dfalse: eliminates to the "else" branch. Motive P is applied to dfalse itself. -/
def dfalse : Expr := soch{ μ(dfalse : ⊤). λ(P : dfalse → ⊤). λ(t : ⊤). λ(f : P dfalse). f }

/-- dBool: the dependent boolean type. -/
def dBool : Expr := soch{ μ(dBool : ⊤). λ(P : dBool → ⊤). λ(t : P dtrue). λ(f : P dfalse). P dBool }

-- ── Eval: dtrue P t f = t ─────────────────────────────────
-- After unfolding μ, dtrue becomes: λP. λt. λf. t
-- The μ unfolds in one step, then the lambdas are applied.

-- dtrue with simple args: dtrue ⊤ (var 42) (var 99) = var 42
-- First we need to pass P, then t, then f.
-- dtrue = μ... so eval unfolds it, getting λP.λt.λf.t (with substitution for self).
-- The body of dtrue after self-subst:
--   λ(P : [dtrue/dtrue] dtrue → ⊤). λ(t : P [dtrue/dtrue] dtrue). λ(f : ⊤). t
-- Since dtrue occurs in domains (not affecting evaluation), the body evaluates to
-- a 3-arg lambda that returns its second argument.

-- Simple test: dtrue applied to 3 args.
-- P = ⊤ (constant motive), t = var 42, f = var 99
-- dtrue ⊤ (var 42) (var 99) should give var 42
-- But we need to pass (dtrue → ⊤) as the domain annotation matches.
-- Actually, eval is untyped (call-by-name), so we can pass anything.
example : eval 100 (.app (.app (.app dtrue .top) (.var 42)) (.var 99))
    = some (.var 42) := rfl

-- dfalse applied to 3 args: dfalse ⊤ (var 42) (var 99) = var 99
example : eval 100 (.app (.app (.app dfalse .top) (.var 42)) (.var 99))
    = some (.var 99) := rfl

-- ── Eval: dependent elimination ───────────────────────────
-- dtrue selects second arg (first data arg), dfalse selects third arg (second data arg).
-- These are the same tests but more explicitly named.

private def ev (e : Expr) := eval 200 e

-- dtrue as a boolean: selects "then" branch
example : ev (.app (.app (.app dtrue .top) (.var 1)) (.var 2)) = some (.var 1) := rfl

-- dfalse as a boolean: selects "else" branch
example : ev (.app (.app (.app dfalse .top) (.var 1)) (.var 2)) = some (.var 2) := rfl

-- ── Eval: dBool itself ────────────────────────────────────
-- dBool unfolds: μ body, body[dBool := μ...] = λP.λt.λf. P dBool'
-- where dBool' is the substituted mu expression.
-- Applied to args: dBool P t f = P dBool'
-- This computes the motive applied to dBool — useful for type computation.

-- dBool (λ_:⊤. ⊤) ⊤ ⊤ should give (λ_:⊤. ⊤) dBool' = ⊤
-- (constant motive returns ⊤)
-- Actually this requires evaluating (λ_.⊤) applied to dBool', which gives ⊤.
example : ev (.app (.app (.app dBool (.lam .top .top)) .top) .top) = some .top := rfl

-- ── Sub: dtrue ⊑ ⊤ (trivially) ───────────────────────────
example : Sub [] dtrue .top := Sub.top [] dtrue

-- ── Sub: CONST_TOP ⊑ CONST_TOP (refl) ────────────────────
example : Sub [] CONST_TOP CONST_TOP := Sub.refl [] CONST_TOP

-- ── Sub: dtrue ⊑ dBool ───────────────────────────────────
-- This is the fundamental self-type intro check.
--
-- Using Sub.mu: μA.b ⊑ c  needs  A ⊑ c  AND  A::Γ ⊢ b ⊑ A↑
--
-- For dtrue (A = ⊤): need ⊤ ⊑ dBool. But ⊤ is NOT a subtype of dBool
-- in Simple Och's rules (no rule derives ⊤ ⊑ non-⊤).
--
-- The current Sub.mu rule is too weak for self-type intro because it requires
-- the annotation A to be ⊑ the target c. In full Och, self_intro works
-- differently: a ⊑ μ(ann).body if a ⊑ body (unfold the mu on the right).
--
-- This is a known limitation: Simple Och's Sub.mu rule handles mu on the LEFT
-- but there is no rule for mu on the RIGHT (self-type intro). Adding such a
-- rule would enable dtrue ⊑ dBool.
--
-- For now, we can only prove dtrue ⊑ ⊤ (trivially).

-- TODO: Add Sub.muR rule (self-type intro on the right side) to enable:
-- example : Sub [] dtrue dBool := ...
-- example : Sub [] dfalse dBool := ...

end DBool

-- ============================================================
-- 4. Recursive functions via μ
-- ============================================================

section RecursiveFunctions

/-- A function that ignores its argument and calls itself — diverges. -/
def DIVERGE : Expr := soch{ μ(f : ⊤ → ⊤). λ(x : ⊤). f x }

-- DIVERGE unfolds to λx. DIVERGE x, which when applied unfolds again → diverges.
-- eval of DIVERGE alone produces a lambda (one unfolding).
-- But the domain contains the self-reference, so after substitution we get a lambda
-- whose domain is ⊤ (since the annotation domain is ⊤).
-- Body: λ(x : ⊤). f x. After subst f := μf:(⊤→⊤). λx:⊤. f x:
--   λ(x : ⊤). (μf:(⊤→⊤). λx:⊤. f x) x
-- This is a lambda value (eval stops at lambda).
-- But the body contains DIVERGE applied to x, so applying this to an arg diverges.

-- DIVERGE alone evaluates to a lambda (after one mu unfolding).
-- The body of the lambda contains the self-application.
-- Let's test: eval 10 DIVERGE should give some lambda.
-- mu unfolds: body.subst 0 DIVERGE
-- body = lam top (app (var 1) (var 0))  -- var 1 = self, var 0 = x
-- After subst var 0 := DIVERGE in body (which is at the mu level):
-- Actually subst target=0 in body = lam top (app (var 1) (var 0)):
--   lam: dom.subst 0 DIVERGE = top.subst 0 DIVERGE = top
--         body.subst 1 (DIVERGE.shift 0 1) in (app (var 1) (var 0))
--         var 1: 1 == 1, so replace with DIVERGE.shift 0 1
--         var 0: 0 < 1, so stays var 0
-- Result: lam top (app DIVERGE' (var 0)) where DIVERGE' is DIVERGE shifted.
-- This is a lambda, so eval returns it.

-- We can't easily check the exact shifted form, but we can verify it's Some:
example : (eval 10 DIVERGE).isSome = true := rfl

-- Applying DIVERGE to ⊤ diverges (infinite recursion):
example : eval 10 (.app DIVERGE .top) = none := rfl
example : eval 50 (.app DIVERGE .top) = none := by native_decide

-- Sub: DIVERGE ⊑ (⊤ → ⊤) via mu rule.
-- A = lam top top = (⊤ → ⊤).
-- Need: (⊤→⊤) ⊑ (⊤→⊤) (refl).
-- And [(⊤→⊤)] ⊢ λ(x:⊤). f x ⊑ (⊤→⊤)↑ = (⊤→⊤).
-- Note: f = var 0 in the body refers to self (bound by mu).
-- Under ctx [(⊤→⊤)]:
-- body = lam top (app (var 1) (var 0))
-- (⊤→⊤) = lam top top
-- [Lam]: need ⊤ ⊑ ⊤ (refl) and [⊤, (⊤→⊤)] ⊢ app (var 1) (var 0) ⊑ ⊤ (by [Top]).
example : Sub [] DIVERGE (.lam .top .top) :=
  Sub.mu [] (.lam .top .top) (.lam .top (.app (.var 1) (.var 0))) (.lam .top .top)
    (Sub.refl [] (.lam .top .top))
    (Sub.lam [.lam .top .top] .top .top (.app (.var 1) (.var 0)) .top
      (Sub.refl [.lam .top .top] .top)
      (Sub.top [.top, .lam .top .top] (.app (.var 1) (.var 0))))

end RecursiveFunctions

-- ============================================================
-- 5. Tests that should FAIL / limitations
-- ============================================================

section Limitations

-- ── Infinite unfolding ────────────────────────────────────
-- μ(f : ⊤). f diverges at ANY fuel level.
-- Each eval step just substitutes f with the mu term, producing the same mu term.
example : eval 1 (soch{ μ(f : ⊤). f }) = none := rfl
example : eval 10 (soch{ μ(f : ⊤). f }) = none := rfl
example : eval 50 (soch{ μ(f : ⊤). f }) = none := by native_decide

-- ── Self-application ──────────────────────────────────────
-- μ(x : ⊤). x x — self-application. Diverges because unfolding produces
-- (μx:⊤. x x) (μx:⊤. x x), and applying the first to the second unfolds again.
def OMEGA : Expr := soch{ μ(x : ⊤). x x }
example : eval 10 OMEGA = none := rfl
example : eval 50 OMEGA = none := by native_decide

-- ── No right-side mu rule ─────────────────────────────────
-- Sub.mu only works when mu is on the LEFT: μA.b ⊑ c.
-- There is no rule for a ⊑ μA.b (self-type intro on the right).
-- This means we cannot prove dtrue ⊑ dBool or dfalse ⊑ dBool.
-- Adding Sub.muR would enable this.

-- ── Nested mu depth ───────────────────────────────────────
-- Deeply nested mu requires proportionally more fuel.
-- μ(a : ⊤). μ(b : ⊤). μ(c : ⊤). ⊤ — three levels of unfolding.
def NESTED_MU : Expr := soch{ μ(a : ⊤). μ(b : ⊤). μ(c : ⊤). ⊤ }
-- Each level unfolds once, consuming 1 fuel each, then ⊤ returns immediately.
-- So fuel 4 should suffice (3 unfoldings + 1 for the final ⊤).
example : eval 4 NESTED_MU = some .top := rfl
-- But fuel 2 is not enough (only 2 unfoldings, still a mu).
example : eval 2 NESTED_MU = none := rfl

-- ── μ in function position ────────────────────────────────
-- When μ unfolds to a lambda, application works.
-- When it doesn't, eval gets stuck or diverges.
-- μ(f : ⊤). ⊤ applied to ⊤ — unfolds to ⊤, then app ⊤ ⊤ is stuck.
example : eval 10 (.app CONST_TOP .top) = some (.app .top .top) := rfl

end Limitations

-- ============================================================
-- 6. μ interacting with other constructs
-- ============================================================

section MuInteraction

-- ── μ inside ascription ───────────────────────────────────
-- (μs:⊤. ⊤ : ⊤) — ascription is erased, mu unfolds to ⊤.
example : eval 10 (.asc CONST_TOP .top) = some .top := rfl

-- ── μ inside application ──────────────────────────────────
-- (λx:⊤. x) (μs:⊤. ⊤) — identity applied to CONST_TOP.
-- eval: first eval identity (value), then subst arg = CONST_TOP for x in body,
-- then eval body = eval CONST_TOP = ⊤.
example : eval 20 (.app (.lam .top (.var 0)) CONST_TOP) = some .top := rfl

-- ── μ returning a lambda applied to args ──────────────────
-- (μs:(⊤→⊤). λx:⊤. x) ⊤ — self-ref identity applied to ⊤.
example : eval 20 (.app SELF_ID .top) = some .top := rfl

-- ── Nested μ and λ ────────────────────────────────────────
-- μ(f : ⊤ → ⊤). λ(x : ⊤). μ(g : ⊤). x
-- Inner mu unfolds, ignoring g, returning x.
def NESTED_MU_LAM : Expr := soch{ μ(f : ⊤ → ⊤). λ(x : ⊤). μ(g : ⊤). x }

-- After outer mu unfolds: λx. μg:⊤. x (with f substituted away from the body).
-- Actually, body = lam top (mu top (var 1)). After subst var 0 := NESTED_MU_LAM:
-- lam top (mu top (var 1)) -- var 1 points to f, which after subst becomes:
-- Hmm, let me trace: body is in the mu scope [f].
-- body = lam top (mu top (var 1))
-- var 1 in scope [g, x, f] — but wait, the body of mu(f:...) is the lam.
-- In the mu body scope [f]: body = lam top (mu top (var 1))
--   Under the lam [x, f]: mu top (var 1) — var 1 = f
--   Under the inner mu [g, x, f]: var 1 = x... wait no.
-- Let me recount. soch{μ(f : ⊤→⊤). λ(x : ⊤). μ(g : ⊤). x}
-- Macro: μ(f:...). enters ctx [f]
--   λ(x:...). enters ctx [x, f]
--     μ(g:...). enters ctx [g, x, f]
--       x → index 1 in [g, x, f]
-- So body of outer mu = lam top (mu top (var 1))
-- subst 0 := NESTED_MU_LAM in body:
--   lam: dom.subst 0 NML = top
--        inner.subst 1 (NML.shift 0 1):
--          mu: ann.subst 1 (NML.shift 0 1) = top
--              (var 1).subst 2 (NML.shift 0 2):
--                var 1: 1 < 2, so stays var 1. Wait that's wrong.
-- Actually subst goes under one binder (the lam), so target becomes 1.
-- Then under the mu, target becomes 2.
-- var 1 at target 2: 1 < 2, so stays var 1. But var 1 should be x!
-- After substitution, x = var 0 in the lam body. So in [g, x]:
-- var 1 = x. Good, x is still x. The f (which was var 2 in [g,x,f]) is gone.
-- So the result is: lam top (mu top (var 1))
-- Wait, var 1 in scope [g, x] with f eliminated... that means var 1 = x. OK.
-- So after outer mu unfolds: λx. μg:⊤. x
-- Then μg:⊤. x unfolds to x.subst 0 (μg:⊤. x) = x (since x = var 0 at that level??)
-- Hmm, this is the var 1 issue. In the body of the inner mu, var 1 refers to x.
-- After subst 0 := (mu top (var 1)) in (var 1): var 1 > 0, so var (1-1) = var 0.
-- So the inner mu body after unfolding = var 0, which is x at the lambda level.

-- Applied: (λx. μg:⊤. x) ⊤ → μg:⊤. ⊤ → ⊤
example : eval 30 (.app NESTED_MU_LAM .top) = some .top := rfl

-- ── μ with unused self but complex body ───────────────────
-- μ(s : ⊤). (λ(x : ⊤). x) ⊤ — body is a redex, self unused.
def MU_REDEX : Expr := soch{ μ(s : ⊤). (λ(x : ⊤). x) ⊤ }
-- Unfolds mu, then evaluates (λx.x) ⊤ = ⊤.
example : eval 10 MU_REDEX = some .top := rfl

end MuInteraction

-- ============================================================
-- 7. Sub derivations involving μ
-- ============================================================

section MuSub

-- ── μ(s:⊤). ⊤ ⊑ ⊤ ───────────────────────────────────────
-- Already shown above. Repeat for clarity.
example : Sub [] (Expr.mu .top .top) .top :=
  Sub.mu [] .top .top .top
    (Sub.refl [] .top)
    (Sub.refl [.top] .top)

-- ── μ(s:A). b ⊑ A when A = λ⊤.⊤ and b = λ⊤.⊤ ──────────
-- SELF_ID ⊑ (⊤→⊤) — proved above, repeated for this section.
-- This shows the mu rule handles function types as annotations.

-- ── Two different mus with same annotation ────────────────
-- μ(s:⊤). ⊤ ⊑ ⊤ and μ(s:⊤). (λx:⊤.x) ⊑ ⊤ both hold.
-- But μ(s:⊤). ⊤ ⊑ μ(s:⊤). ⊤ holds by refl.
example : Sub [] CONST_TOP CONST_TOP := Sub.refl [] CONST_TOP

-- ── Sub.mu + Sub.top composition ──────────────────────────
-- μ(s:⊤).⊤ ⊑ ⊤ ⊑ ⊤ — the annotation check (⊤ ⊑ ⊤) is trivial.
-- We already showed CONST_TOP ⊑ ⊤. Now chain it with [Top]:
-- μ(s:⊤→⊤). λx:⊤. x ⊑ ⊤
example : Sub [] SELF_ID .top := Sub.top [] SELF_ID

-- ── DIVERGE ⊑ (⊤ → ⊤) ───────────────────────────────────
-- Proved above. The body check uses [Top] to handle the stuck app in the body.

end MuSub

-- ============================================================
-- 8. de Bruijn index stress tests
-- ============================================================

section DeBruijnStress

-- ── μ inside λ ────────────────────────────────────────────
-- λ(x : ⊤). μ(s : ⊤). x
-- Under λ: ctx [x]. Under μ: ctx [s, x].
-- x = var 1 in [s, x].
def LAM_MU : Expr := soch{ λ(x : ⊤). μ(s : ⊤). x }

-- Applied to (var 42): λx. μs:⊤. x applied to (var 42)
-- → (μs:⊤. x)[x := var 42] = μs:⊤. (var 42).shift 0 1... wait.
-- subst 0 := (var 42) in body of lam:
-- body = mu top (var 1). subst 0 := (var 42):
--   mu: ann.subst 0 (var 42) = top
--       (var 1).subst 1 ((var 42).shift 0 1):
--         var 1: 1 == 1, replace with (var 42).shift 0 1 = var 43
-- Result: mu top (var 43). Then mu unfolds: (var 43).subst 0 (mu top (var 43))
--   var 43: 43 > 0, so var 42.
-- Final: var 42.
example : eval 20 (.app LAM_MU (.var 42)) = some (.var 42) := rfl

-- ── λ inside μ inside λ ──────────────────────────────────
-- λ(a : ⊤). μ(s : ⊤ → ⊤). λ(b : ⊤). a
-- ctx after λ(a): [a]
-- ctx after μ(s): [s, a]
-- ctx after λ(b): [b, s, a]
-- a = var 2 in [b, s, a]
def LAM_MU_LAM : Expr := soch{ λ(a : ⊤). μ(s : ⊤ → ⊤). λ(b : ⊤). a }

-- Applied to (var 42), then (var 99):
-- Step 1: (λa. μs:(⊤→⊤). λb. a) (var 42) → (μs:(⊤→⊤). λb. (var 42))[a := var 42]
-- Actually: subst 0 := (var 42) in body (mu (lam top top) (lam top (var 2)))
--   mu: ann = (lam top top).subst 0 (var 42) = lam top top
--       body = (lam top (var 2)).subst 1 ((var 42).shift 0 1)
--            = lam (top.subst 1 (var 43)) ((var 2).subst 2 ((var 43).shift 0 1))
--            = lam top (var 2 at target 2: 2 == 2 → replace with (var 43).shift 0 1 = var 44)
-- Hmm, this is getting complex. Let me just verify with eval.
-- After all substitutions, applying to (var 42) should give μs:(⊤→⊤). λb. (var 42)↑ish
-- Then mu unfolds giving λb. (var 42)ish. Then applying to (var 99) gives (var 42).
example : eval 30 (.app (.app LAM_MU_LAM (.var 42)) (.var 99)) = some (.var 42) := rfl

end DeBruijnStress

end Och.Simple.MuTests
