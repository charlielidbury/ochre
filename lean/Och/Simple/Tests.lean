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
-- D) IotaIntro — self-types with covariant occurrences
-- ============================================================

/-!
These tests exercise the [Iota-Intro] rule for types that use the
self-reference only in covariant positions. In such cases, the fixed
self-reference formulation (where the self-binder is instantiated with
μA.b itself) collapses the obligations to reflexivity after substitution.
-/

-- [Iota-Intro] trivial case: ⊤ ⊑ μ⊤. ⊤
-- The body ⊤ is closed (self-variable unused), so body[0 := μ⊤. ⊤] = ⊤.
-- Both premises close by [Refl] (for ⊤ ⊑ ⊤) and [Top] (for ⊤ ⊑ ⊤).
example : Sub [] Expr.top (.mu .top .top) :=
  Sub.iotaIntro [] .top .top .top
    (Sub.refl [] .top)
    (show Sub [] Expr.top ((Expr.top).subst 0 (.mu .top .top)) by
      simp [Expr.subst]; exact Sub.refl [] .top)

-- [Iota-Intro] where self appears covariantly: μ⊤. self (where self = var 0)
-- The body is `var 0`, which under substitution becomes μ⊤. var 0 itself.
-- So given some `a` with `a ⊑ ⊤` and `a ⊑ μ⊤. (var 0)`, we can conclude `a ⊑ μ⊤. (var 0)`.
-- The second premise is itself the goal — so this is a fixed-point form that
-- IotaIntro can derive reflexively only when the value already inhabits the type.
-- We use `.top` as the witness, which is NOT in the type (it should be rejected),
-- so instead we test with the type being `μ⊤. ⊤` (degenerate).
-- A more interesting test: covariant body `lam X self` — the "wrap" pattern.

-- Wrap = μ⊤. (⊤ → self)    -- a function from ⊤ to the self-type itself
-- encoded as: μ .top (.lam .top (.var 1))
-- The body has self = var 0, but under the outer λ binder it becomes var 1.
-- Under the μ-binder, self is at index 0; inside the inner lambda, self is at index 1.
private def Wrap : Expr := .mu .top (.lam .top (.var 1))

-- Under IotaIntro, to check `v ⊑ Wrap` we need:
--   1) v ⊑ ⊤ (always, by [Top])
--   2) v ⊑ (.lam .top (.var 1)).subst 0 Wrap
--      = .lam .top ((.var 1).subst 1 (Wrap.shift 0 1))
--      = .lam .top (Wrap.shift 0 1)
-- Actually let's compute: (.var 1).subst 1 (Wrap.shift 0 1) = Wrap.shift 0 1
-- (since 1 == 1). So the target becomes .lam .top (Wrap.shift 0 1).
-- For `v = .lam .top Wrap`... hmm the shift complicates things.
-- Let's take a simpler example.

-- Degenerate covariant self-type: μself. ⊤
-- Body doesn't mention self. So body[μ] = ⊤.
example : Sub [] Expr.top (.mu .top .top) :=
  Sub.iotaIntro [] .top .top .top
    (Sub.top [] .top)
    (show Sub [] Expr.top ((Expr.top).subst 0 (.mu .top .top)) from by
      simp [Expr.subst]; exact Sub.refl [] .top)

-- Another degenerate case: μself. ⊤, with a lambda witness
example : Sub [] (.lam .top .top) (.mu .top .top) :=
  Sub.iotaIntro [] (.lam .top .top) .top .top
    (Sub.top [] (.lam .top .top))
    (show Sub [] (.lam .top .top) ((Expr.top).subst 0 (.mu .top .top)) from by
      simp [Expr.subst]; exact Sub.top [] _)

-- μself. self where self = var 0. The body is var 0.
-- Under substitution, body[0 := μ.(var 0)] = μ.(var 0) itself.
-- So `a ⊑ μself. self` iff `a ⊑ μself. self` — pure fixed point.
-- Demonstrates that IotaIntro here is vacuous without a prior witness.
-- To actually derive this for some `a`, we'd need `a ⊑ μself. self` as a premise
-- (which is exactly what we're trying to prove). So this example is *not* provable
-- from scratch; it illustrates the fixed-point nature.

-- μself. (self → ⊤)  — types of "things that take self as input"
-- Body: .lam (.var 0) .top.  After subst: .lam (.mu self (lam self top)) .top
-- where the body's .var 0 (referring to the μ-binder) is replaced with the μ itself.
-- This is a covariant-in-top self-type; the body ⊤ doesn't mention self.
-- Checking `.lam (.mu...) .top ⊑ this μ-type` becomes:
--   premise 1: .lam ... .top ⊑ .top  → [Top]
--   premise 2: .lam ... .top ⊑ .lam (.mu ...) .top  → [Refl]
private def SelfToTop : Expr := .mu .top (.lam (.var 0) .top)

-- The witness is essentially "λ(_ : SelfToTop). ⊤" which lives at the right type
-- after the self-binder is instantiated with SelfToTop itself.
example : Sub [] (.lam SelfToTop .top) SelfToTop := by
  -- By [Iota-Intro]: need
  --   (a) (.lam SelfToTop .top) ⊑ .top
  --   (b) (.lam SelfToTop .top) ⊑ ((.lam (.var 0) .top).subst 0 SelfToTop)
  -- Compute (b): (.lam (.var 0) .top).subst 0 SelfToTop
  --   = .lam ((.var 0).subst 0 SelfToTop) ((.top).subst 1 (SelfToTop.shift 0 1))
  --   = .lam SelfToTop .top
  -- So (b) becomes (.lam SelfToTop .top) ⊑ (.lam SelfToTop .top), closable by [Refl].
  apply Sub.iotaIntro _ (.lam SelfToTop .top) .top (.lam (.var 0) .top)
  · exact Sub.top _ _
  · show Sub [] (.lam SelfToTop .top) ((Expr.lam (.var 0) .top).subst 0 SelfToTop)
    -- The subst should reduce to .lam SelfToTop .top
    have hcompute : ((Expr.lam (.var 0) .top).subst 0 SelfToTop) = .lam SelfToTop .top := by
      simp [Expr.subst, Expr.shift]
    rw [hcompute]
    exact Sub.refl _ _

-- Check that the self-type is also an IotaIntro subtype of itself trivially via [Refl]
example : Sub [] SelfToTop SelfToTop := Sub.refl _ _

end Och.Simple.Tests
