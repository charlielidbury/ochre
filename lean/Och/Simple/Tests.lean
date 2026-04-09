import Och.Simple.Syntax
import Och.Simple.Subtype
import Och.Simple.Eval

/-!
# Tests for the simplified Och calculus

Comprehensive test suite covering:
- A) Concrete evaluation tests
- B) Sub derivation tests (explicit proof terms)
- C) Key examples from the spec (Church booleans, ID function)
-/

set_option autoImplicit false

namespace Och.Simple.Tests

open Och.Simple Expr

-- ============================================================
-- Definitions
-- ============================================================

/-- BOOL = λt:⊤. λa:t. λb:t. t -/
def BOOL : Expr := .lam .top (.lam (.var 0) (.lam (.var 1) (.var 2)))

/-- TRUE = λt:⊤. λa:t. λb:t. a -/
def TRUE : Expr := .lam .top (.lam (.var 0) (.lam (.var 1) (.var 1)))

/-- FALSE = λt:⊤. λa:t. λb:t. b -/
def FALSE : Expr := .lam .top (.lam (.var 0) (.lam (.var 1) (.var 0)))

/-- ID = λb:BOOL. (b BOOL TRUE FALSE : BOOL) -/
def ID : Expr := .lam BOOL (.asc (.app (.app (.app (.var 0) BOOL) TRUE) FALSE) BOOL)

-- ============================================================
-- A) Concrete evaluation tests
-- ============================================================

private def ev (e : Expr) : Option Expr := eval 100 e

-- Basic evaluation
example : ev .top = some .top := rfl
example : ev (.var 0) = some (.var 0) := rfl
example : ev (.lam .top (.var 0)) = some (.lam .top (.var 0)) := rfl

-- Identity: (λ⊤. 0) ⊤ → ⊤
example : ev (.app (.lam .top (.var 0)) .top) = some .top := rfl

-- Ascription erased: (⊤ : ⊤) → ⊤
example : ev (.asc .top .top) = some .top := rfl

-- Nested application: (λ⊤. λ⊤. 0) ⊤ ⊤ → ⊤
example : ev (.app (.app (.lam .top (.lam .top (.var 0))) .top) .top) = some .top := rfl

-- Stuck application: (var 0) ⊤ stays stuck
example : ev (.app (.var 0) .top) = some (.app (.var 0) .top) := rfl

-- Church boolean evaluation: TRUE ⊤ (var 42) (var 99) → var 42
example : ev (.app (.app (.app TRUE .top) (.var 42)) (.var 99)) = some (.var 42) := rfl

-- Church boolean evaluation: FALSE ⊤ (var 42) (var 99) → var 99
example : ev (.app (.app (.app FALSE .top) (.var 42)) (.var 99)) = some (.var 99) := rfl

-- ID applied to TRUE: should evaluate to something
-- ID TRUE = (TRUE BOOL TRUE FALSE) which should reduce to TRUE
-- Let's trace: TRUE BOOL TRUE FALSE
--   TRUE = λt. λa. λb. a
--   TRUE BOOL → λa. λb. a  (with t=BOOL in body, but subst makes it: lam BOOL (lam BOOL (var 1)))
--   ... applied to TRUE → lam BOOL TRUE  (subst var 1 for a gives: lam BOOL (var 0 becomes TRUE?))
-- Actually let's just check what eval produces.
-- The ascription is erased, so we eval: app (app (app (var 0) BOOL) TRUE) FALSE
-- with var 0 bound to TRUE (from the outer lam applied to TRUE as argument).
-- Wait, ID TRUE = (lam BOOL body) applied to TRUE.
-- body = asc (app (app (app (var 0) BOOL) TRUE) FALSE) BOOL
-- After subst var 0 := TRUE in body:
--   asc (app (app (app TRUE BOOL) TRUE) FALSE) BOOL
-- eval erases asc, so we eval: app (app (app TRUE BOOL) TRUE) FALSE
-- TRUE BOOL = (λt. λa. λb. a) BOOL → subst 0 := BOOL in (λa. λb. a)
--   = lam (BOOL.subst 0 BOOL) (lam (var 1).subst 1 (BOOL.shift 0 1)) ...
-- Actually this gets complex. Let's just let native_decide or rfl check it.
example : ev (.app ID TRUE) = some TRUE := rfl

-- ID applied to FALSE should produce FALSE
example : ev (.app ID FALSE) = some FALSE := rfl

-- ============================================================
-- B) Sub derivation tests — explicit proof terms
-- ============================================================

-- [Refl]: ⊤ ⊑ ⊤
example : Sub [] Expr.top Expr.top :=
  Sub.refl [] .top

-- [Top]: anything ⊑ ⊤
example : Sub [] (.var 0) Expr.top :=
  Sub.top [] (.var 0)

example : Sub [] BOOL Expr.top :=
  Sub.top [] BOOL

-- [Refl]: BOOL ⊑ BOOL
example : Sub [] BOOL BOOL :=
  Sub.refl [] BOOL

-- ============================================================
-- C.2) TRUE ⊑ BOOL
-- ============================================================

-- TRUE ⊑ BOOL in empty context
-- TRUE = lam top (lam (var 0) (lam (var 1) (var 1)))
-- BOOL = lam top (lam (var 0) (lam (var 1) (var 2)))
--
-- [Lam] [] ⊢ TRUE ⊑ BOOL
--   [Refl] [] ⊢ top ⊑ top
--   [Lam] [top] ⊢ lam (var 0) (lam (var 1) (var 1)) ⊑ lam (var 0) (lam (var 1) (var 2))
--     [Refl] [top] ⊢ var 0 ⊑ var 0
--     [Lam] [var 0, top] ⊢ lam (var 1) (var 1) ⊑ lam (var 1) (var 2)
--       [Refl] [var 0, top] ⊢ var 1 ⊑ var 1
--       [Var] [var 1, var 0, top] ⊢ var 1 ⊑ var 2
--         Ctx.get? [var 1, var 0, top] 1 = some (var 2)   (list[1]=var 0, shifted by 2)
--         [Refl] [var 1, var 0, top] ⊢ var 2 ⊑ var 2
example : Sub [] TRUE BOOL :=
  Sub.lam [] .top .top
    (.lam (.var 0) (.lam (.var 1) (.var 1)))
    (.lam (.var 0) (.lam (.var 1) (.var 2)))
    (Sub.refl [] .top)
    (Sub.lam [.top] (.var 0) (.var 0)
      (.lam (.var 1) (.var 1))
      (.lam (.var 1) (.var 2))
      (Sub.refl [.top] (.var 0))
      (Sub.lam [.var 0, .top] (.var 1) (.var 1)
        (.var 1)
        (.var 2)
        (Sub.refl [.var 0, .top] (.var 1))
        (Sub.var [.var 1, .var 0, .top] 1 (.var 2) (.var 2)
          rfl
          (Sub.refl [.var 1, .var 0, .top] (.var 2)))))

-- ============================================================
-- C.3) FALSE ⊑ BOOL
-- ============================================================

-- FALSE = lam top (lam (var 0) (lam (var 1) (var 0)))
-- BOOL  = lam top (lam (var 0) (lam (var 1) (var 2)))
--
-- Same structure as TRUE ⊑ BOOL, but the innermost step uses var 0 (b) instead of var 1 (a).
-- [Var] [var 1, var 0, top] ⊢ var 0 ⊑ var 2
--   Ctx.get? [var 1, var 0, top] 0 = some (var 2)   (list[0]=var 1, shifted by 1)
--   [Refl] [var 1, var 0, top] ⊢ var 2 ⊑ var 2
example : Sub [] FALSE BOOL :=
  Sub.lam [] .top .top
    (.lam (.var 0) (.lam (.var 1) (.var 0)))
    (.lam (.var 0) (.lam (.var 1) (.var 2)))
    (Sub.refl [] .top)
    (Sub.lam [.top] (.var 0) (.var 0)
      (.lam (.var 1) (.var 0))
      (.lam (.var 1) (.var 2))
      (Sub.refl [.top] (.var 0))
      (Sub.lam [.var 0, .top] (.var 1) (.var 1)
        (.var 0)
        (.var 2)
        (Sub.refl [.var 0, .top] (.var 1))
        (Sub.var [.var 1, .var 0, .top] 0 (.var 2) (.var 2)
          rfl
          (Sub.refl [.var 1, .var 0, .top] (.var 2)))))

-- ============================================================
-- C.7) Ascription: (TRUE : BOOL) ⊑ BOOL
-- ============================================================

-- [Asc-L] [] ⊢ (TRUE : BOOL) ⊑ BOOL
--   [] ⊢ TRUE ⊑ BOOL    (proved above)
--   [Refl] [] ⊢ BOOL ⊑ BOOL
example : Sub [] (.asc TRUE BOOL) BOOL :=
  Sub.ascL [] TRUE BOOL BOOL
    -- TRUE ⊑ BOOL (same proof as above)
    (Sub.lam [] .top .top
      (.lam (.var 0) (.lam (.var 1) (.var 1)))
      (.lam (.var 0) (.lam (.var 1) (.var 2)))
      (Sub.refl [] .top)
      (Sub.lam [.top] (.var 0) (.var 0)
        (.lam (.var 1) (.var 1))
        (.lam (.var 1) (.var 2))
        (Sub.refl [.top] (.var 0))
        (Sub.lam [.var 0, .top] (.var 1) (.var 1)
          (.var 1)
          (.var 2)
          (Sub.refl [.var 0, .top] (.var 1))
          (Sub.var [.var 1, .var 0, .top] 1 (.var 2) (.var 2)
            rfl
            (Sub.refl [.var 1, .var 0, .top] (.var 2))))))
    -- BOOL ⊑ BOOL
    (Sub.refl [] BOOL)

-- ============================================================
-- C.4) ID ⊑ (BOOL → BOOL)  i.e. Sub [] ID (lam BOOL BOOL)
-- ============================================================

-- Helper: TRUE ⊑ BOOL in context [BOOL] (same structure, longer context)
private def trueSub_inBOOL : Sub [BOOL] TRUE BOOL :=
  Sub.lam [BOOL] .top .top
    (.lam (.var 0) (.lam (.var 1) (.var 1)))
    (.lam (.var 0) (.lam (.var 1) (.var 2)))
    (Sub.refl [BOOL] .top)
    (Sub.lam [.top, BOOL] (.var 0) (.var 0)
      (.lam (.var 1) (.var 1))
      (.lam (.var 1) (.var 2))
      (Sub.refl [.top, BOOL] (.var 0))
      (Sub.lam [.var 0, .top, BOOL] (.var 1) (.var 1)
        (.var 1)
        (.var 2)
        (Sub.refl [.var 0, .top, BOOL] (.var 1))
        (Sub.var [.var 1, .var 0, .top, BOOL] 1 (.var 2) (.var 2)
          rfl
          (Sub.refl [.var 1, .var 0, .top, BOOL] (.var 2)))))

-- Helper: FALSE ⊑ BOOL in context [BOOL]
private def falseSub_inBOOL : Sub [BOOL] FALSE BOOL :=
  Sub.lam [BOOL] .top .top
    (.lam (.var 0) (.lam (.var 1) (.var 0)))
    (.lam (.var 0) (.lam (.var 1) (.var 2)))
    (Sub.refl [BOOL] .top)
    (Sub.lam [.top, BOOL] (.var 0) (.var 0)
      (.lam (.var 1) (.var 0))
      (.lam (.var 1) (.var 2))
      (Sub.refl [.top, BOOL] (.var 0))
      (Sub.lam [.var 0, .top, BOOL] (.var 1) (.var 1)
        (.var 0)
        (.var 2)
        (Sub.refl [.var 0, .top, BOOL] (.var 1))
        (Sub.var [.var 1, .var 0, .top, BOOL] 0 (.var 2) (.var 2)
          rfl
          (Sub.refl [.var 1, .var 0, .top, BOOL] (.var 2)))))

-- The main ID proof: Sub [] ID (lam BOOL BOOL)
--
-- ID = lam BOOL (asc (app (app (app (var 0) BOOL) TRUE) FALSE) BOOL)
--
-- [Lam] [] ⊢ ID ⊑ lam BOOL BOOL
--   [Refl] [] ⊢ BOOL ⊑ BOOL
--   [Asc-L] [BOOL] ⊢ (... : BOOL) ⊑ BOOL
--     [BOOL] ⊢ app (app (app (var 0) BOOL) TRUE) FALSE ⊑ BOOL   -- (A)
--     [Refl] [BOOL] ⊢ BOOL ⊑ BOOL
--
-- (A) Three nested [App] rules:
--
-- [App] f=(app (app (var 0) BOOL) TRUE), a=FALSE, D=BOOL, R=BOOL
--   f ⊑ lam BOOL BOOL                          -- (A.1)
--   FALSE ⊑ BOOL                                -- falseSub_inBOOL
--   BOOL.subst 0 FALSE = BOOL ⊑ BOOL            -- refl
--
-- (A.1) [App] f=(app (var 0) BOOL), a=TRUE, D=BOOL, R=(lam BOOL BOOL)
--   f ⊑ lam BOOL (lam BOOL BOOL)                -- (A.2)
--   TRUE ⊑ BOOL                                  -- trueSub_inBOOL
--   (lam BOOL BOOL).subst 0 TRUE = lam BOOL BOOL ⊑ lam BOOL BOOL  -- refl
--
-- (A.2) [App] f=(var 0), a=BOOL, D=⊤, R=lam (var 0) (lam (var 1) (var 2))
--   var 0 ⊑ BOOL = lam ⊤ (lam (var 0) (lam (var 1) (var 2)))
--     [Var] Ctx.get? [BOOL] 0 = some BOOL, then BOOL ⊑ BOOL (refl)
--   BOOL ⊑ ⊤                                     -- top
--   R.subst 0 BOOL = lam BOOL (lam BOOL BOOL) ⊑ lam BOOL (lam BOOL BOOL)  -- refl
--
-- Note on R.subst 0 BOOL where R = lam (var 0) (lam (var 1) (var 2)):
--   subst replaces var 0 with BOOL in the domain, shifts under binders, etc.
--   Result: lam BOOL (lam BOOL BOOL)   (all three bound vars become BOOL)
example : Sub [] ID (.lam BOOL BOOL) :=
  -- [Lam]
  Sub.lam [] BOOL BOOL
    (.asc (.app (.app (.app (.var 0) BOOL) TRUE) FALSE) BOOL)
    BOOL
    (Sub.refl [] BOOL)
    -- [Asc-L]
    (Sub.ascL [BOOL]
      (.app (.app (.app (.var 0) BOOL) TRUE) FALSE) BOOL BOOL
      -- (A): app (app (app (var 0) BOOL) TRUE) FALSE ⊑ BOOL
      -- Outermost [App]: D=BOOL, R=BOOL
      (Sub.app [BOOL]
        (.app (.app (.var 0) BOOL) TRUE) FALSE BOOL
        BOOL BOOL
        -- (A.1): app (app (var 0) BOOL) TRUE ⊑ lam BOOL BOOL
        -- Middle [App]: D=BOOL, R=lam BOOL BOOL
        (Sub.app [BOOL]
          (.app (.var 0) BOOL) TRUE (.lam BOOL BOOL)
          BOOL (.lam BOOL BOOL)
          -- (A.2): app (var 0) BOOL ⊑ lam BOOL (lam BOOL BOOL)
          -- Inner [App]: D=⊤, R=lam (var 0) (lam (var 1) (var 2))
          (Sub.app [BOOL]
            (.var 0) BOOL (.lam BOOL (.lam BOOL BOOL))
            .top (.lam (.var 0) (.lam (.var 1) (.var 2)))
            -- var 0 ⊑ BOOL via [Var]
            (Sub.var [BOOL] 0 BOOL BOOL
              rfl
              (Sub.refl [BOOL] BOOL))
            -- BOOL ⊑ ⊤ via [Top]
            (Sub.top [BOOL] BOOL)
            -- R.subst 0 BOOL = lam BOOL (lam BOOL BOOL) ⊑ lam BOOL (lam BOOL BOOL)
            (Sub.refl [BOOL] (.lam BOOL (.lam BOOL BOOL))))
          -- TRUE ⊑ BOOL
          trueSub_inBOOL
          -- (lam BOOL BOOL).subst 0 TRUE = lam BOOL BOOL ⊑ lam BOOL BOOL
          (Sub.refl [BOOL] (.lam BOOL BOOL)))
        -- FALSE ⊑ BOOL
        falseSub_inBOOL
        -- BOOL.subst 0 FALSE = BOOL ⊑ BOOL
        (Sub.refl [BOOL] BOOL))
      -- BOOL ⊑ BOOL
      (Sub.refl [BOOL] BOOL))

-- ============================================================
-- C.6) f ⊤ rejection — why Sub [lam BOOL BOOL] (app (var 0) top) BOOL cannot hold
-- ============================================================

-- To show Sub [lam BOOL BOOL] (app (var 0) top) BOOL, we would need [App]:
--   Sub [lam BOOL BOOL] (var 0) (lam D R)     -- var 0 has type lam BOOL BOOL
--   Sub [lam BOOL BOOL] top D                  -- top ⊑ D
--
-- The only way to derive var 0 ⊑ lam D R is via [Var] which gives us the
-- bound lam BOOL BOOL, so D = BOOL and R = BOOL. But then we need:
--   Sub [lam BOOL BOOL] top BOOL
-- i.e., ⊤ ⊑ BOOL. Since BOOL is a lambda, the only rule that could apply is:
--   [Refl] — but top ≠ BOOL
--   [Top]  — wrong direction (a ⊑ ⊤, not ⊤ ⊑ a)
--   [Var]  — top is not a variable
--   [Lam]  — top is not a lambda
--   [App]  — top is not an application
--   [Asc-L] — top is not an ascription
--   [Asc-R] — BOOL is not an ascription
--   [Beta-R] — BOOL is not an application
-- No rule applies, so Sub [lam BOOL BOOL] top BOOL is not derivable.
-- Therefore Sub [lam BOOL BOOL] (app (var 0) top) BOOL is not derivable.
-- This demonstrates that our type system correctly rejects applying a
-- BOOL → BOOL function to ⊤ (which is not a BOOL).

-- ============================================================
-- Additional tests
-- ============================================================

-- [Asc-R]: a ⊑ (e : τ) when e ⊑ τ and a ⊑ τ
-- TRUE ⊑ (TRUE : BOOL)
private def trueSub_empty : Sub [] TRUE BOOL :=
  Sub.lam [] .top .top
    (.lam (.var 0) (.lam (.var 1) (.var 1)))
    (.lam (.var 0) (.lam (.var 1) (.var 2)))
    (Sub.refl [] .top)
    (Sub.lam [.top] (.var 0) (.var 0)
      (.lam (.var 1) (.var 1))
      (.lam (.var 1) (.var 2))
      (Sub.refl [.top] (.var 0))
      (Sub.lam [.var 0, .top] (.var 1) (.var 1)
        (.var 1)
        (.var 2)
        (Sub.refl [.var 0, .top] (.var 1))
        (Sub.var [.var 1, .var 0, .top] 1 (.var 2) (.var 2)
          rfl
          (Sub.refl [.var 1, .var 0, .top] (.var 2)))))

-- Note: ascR's second premise is `a ⊑ e` (not `a ⊑ τ` as in the spec).
-- Here a = e = TRUE, so the second premise is TRUE ⊑ TRUE (refl).
example : Sub [] TRUE (.asc TRUE BOOL) :=
  Sub.ascR [] TRUE TRUE BOOL trueSub_empty (Sub.refl [] TRUE)

-- [Var] in a simple context: x:⊤ ⊢ x ⊑ ⊤
-- Ctx.get? [top] 0 = some (top.shift 0 1) = some top
example : Sub [.top] (.var 0) .top :=
  Sub.var [.top] 0 .top .top
    rfl
    (Sub.refl [.top] .top)

-- Lambda subtyping with contravariant domain: (λ⊤. 0) ⊑ (λ(λ⊤.⊤). 0)
-- Since (λ⊤.⊤) ⊑ ⊤ (by [Top]), the domain check B ⊑ A is (λ⊤.⊤) ⊑ ⊤.
-- Body check in context [lam top top]: var 0 ⊑ var 0 by refl.
example : Sub [] (.lam .top (.var 0)) (.lam (.lam .top .top) (.var 0)) :=
  Sub.lam [] .top (.lam .top .top)
    (.var 0) (.var 0)
    (Sub.top [] (.lam .top .top))
    (Sub.refl [.lam .top .top] (.var 0))

-- ============================================================
-- D) Mu (self-reference) tests
-- ============================================================

-- D.1) Eval: mu is a value
example : ev (.mu .top (.var 0)) = some (.mu .top (.var 0)) := rfl

-- D.2) Eval: mu unfolding in function position
-- (μs:⊤. λx:⊤. x) applied to ⊤
-- Step: eval (μs:⊤. λx:⊤. x) = some (μs:⊤. λx:⊤. x)  (mu is a value)
-- Then in app case: body.subst 0 (mu ...) = (λx:⊤. x).subst 0 (mu ⊤ (λ⊤. 0))
-- This is λ⊤. 0 (no free var 0 in body of lam)... wait, var 0 in (λx:⊤. x) refers to x
-- Actually (λx:⊤. x) has body = var 0 which refers to x (binder in lam).
-- After subst 0 (mu...): the lam body (var 0) has target 1 bumped, so var 0 stays.
-- Result: (λ⊤. 0) applied to ⊤ → ⊤
example : ev (.app (.mu .top (.lam .top (.var 0))) .top) = some .top := rfl

-- D.3) Sub: μs:⊤. s ⊑ ⊤
-- [Mu] with annotation = ⊤:
--   Sub [] ⊤ ⊤ (by [Top] or [Refl])
--   Sub [⊤] (var 0) (⊤.shift 0 1) = Sub [⊤] (var 0) ⊤ (by [Top])
example : Sub [] (.mu .top (.var 0)) .top :=
  Sub.mu [] .top (.var 0) .top
    (Sub.top [] .top)
    (Sub.top [.top] (.var 0))

-- D.4) Sub: μs:⊤. s ⊑ ⊤ via refl annotation
-- The annotation is ⊤, and ⊤ ⊑ ⊤ trivially
example : Sub [] (.mu .top (.var 0)) .top :=
  Sub.mu [] .top (.var 0) .top
    (Sub.refl [] .top)
    (Sub.top [.top] (.var 0))

-- D.5) Self-referential identity: μself:(BOOL→BOOL). λb:BOOL. (b BOOL TRUE FALSE : BOOL)
-- This is an ID function that refers to itself as "self"
-- The annotation is (BOOL → BOOL) = lam BOOL BOOL
-- The body is the same as the original ID body
-- We need: Sub [] (mu (lam BOOL BOOL) ID_body) (lam BOOL BOOL)
-- Via [Mu]:
--   Sub [] (lam BOOL BOOL) (lam BOOL BOOL)  -- [Refl]
--   Sub [(lam BOOL BOOL)] ID_body ((lam BOOL BOOL).shift 0 1)
--     = Sub [(lam BOOL BOOL)] ID_body (lam (BOOL.shift 0 1) (BOOL.shift 1 1))
-- This is tricky because the shifted BOOL is not syntactically equal to BOOL
-- (BOOL has free vars referring to outer scope which would shift)
-- Actually BOOL = lam top (lam (var 0) (lam (var 1) (var 2)))
-- BOOL.shift 0 1 = lam top (lam (var 0) (lam (var 1) (var 2))) -- same! (no free vars)
-- Wait, BOOL is closed (all vars are bound). So BOOL.shift 0 1 = BOOL... hmm
-- Actually var 0 in the innermost lam refers to the param of lam (var 0), var 1 refers
-- to lam (.var 0) param, var 2 refers to lam .top param. All bound. So shift has no effect.
-- Let me verify:
#eval (BOOL.shift 0 1 == BOOL)  -- should be true

-- D.6) Eval: recursive function that calls itself
-- fix = μf:⊤. f
-- (fix) ⊤ → (body.subst 0 fix) ⊤ = (var 0 .subst 0 fix) ⊤ = fix ⊤ → ... (infinite loop, fuel runs out)
-- With finite fuel, this should return none
example : eval 10 (.app (.mu .top (.var 0)) .top) = none := rfl

-- D.7) Eval: recursive function that terminates
-- A mu that unfolds to a lambda: μf:⊤. λx:⊤. x
-- Applied to ⊤: unfolds once → (λx:⊤. x) applied to ⊤ → ⊤
example : ev (.app (.mu .top (.lam .top (.var 0))) .top) = some .top := rfl

end Och.Simple.Tests
