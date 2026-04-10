import Och.Simple.Syntax
import Och.Simple.Subtype
import Och.Simple.Eval

/-!
# Church-encoded Unit for Simple Och

```
UNIT = λa:⊤. λx:a. a
TT   = λa:⊤. λx:a. x
```
-/

set_option autoImplicit false

namespace Och.Simple.Std

open Och.Simple Expr

-- ============================================================
-- Definitions
-- ============================================================

/-- UNIT = λa:⊤. λx:a. a -/
def UNIT : Expr := .lam .top (.lam (.var 0) (.var 1))

/-- TT = λa:⊤. λx:a. x -/
def TT : Expr := .lam .top (.lam (.var 0) (.var 0))

-- ============================================================
-- Evaluation tests
-- ============================================================

private def ev (e : Expr) : Option Expr := eval 100 e

-- TT applied: TT ⊤ (var 42) → var 42
example : ev (.app (.app TT .top) (.var 42)) = some (.var 42) := rfl

-- TT UNIT TT → TT (applying TT to UNIT and TT gives back TT)
example : ev (.app (.app TT UNIT) TT) = some TT := rfl

-- ============================================================
-- Subtype derivations
-- ============================================================

/-- TT ⊑ UNIT
    TT   = lam top (lam (var 0) (var 0))
    UNIT = lam top (lam (var 0) (var 1))

    [Lam] top ⊑ top, then
    [Lam] (var 0) ⊑ (var 0), then
    [Var] var 0 ⊑ var 1: Ctx.get? [var 0, top] 0 = some (var 1), refl
-/
example : Sub [] TT UNIT :=
  Sub.lam [] .top .top
    (.lam (.var 0) (.var 0))
    (.lam (.var 0) (.var 1))
    (Sub.refl [] .top)
    (Sub.lam [.top] (.var 0) (.var 0)
      (.var 0)
      (.var 1)
      (Sub.refl [.top] (.var 0))
      (Sub.var [.var 0, .top] 0 (.var 1) (.var 1)
        rfl
        (Sub.refl [.var 0, .top] (.var 1))))

/-- UNIT ⊑ ⊤ -/
example : Sub [] UNIT .top :=
  Sub.top [] UNIT

end Och.Simple.Std
