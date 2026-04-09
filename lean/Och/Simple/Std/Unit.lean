import Och.Simple.Macro
import Och.Simple.Subtype
import Och.Simple.Eval

/-!
# Church-encoded Unit for Simple Och

```
UNIT = λa:T. λx:a. a
TT   = λa:T. λx:a. x
```
-/

set_option autoImplicit false

namespace Och.Simple.Std

open Och.Simple Expr

-- ============================================================
-- Definitions
-- ============================================================

/-- UNIT = λa:T. λx:a. a -/
def UNIT : Expr := soch{ λ(a : ⊤). λ(x : a). a }

/-- TT = λa:T. λx:a. x -/
def TT : Expr := soch{ λ(a : ⊤). λ(x : a). x }

-- ============================================================
-- Evaluation tests
-- ============================================================

private def ev (e : Expr) : Option Expr := eval 100 e

-- TT applied: TT T (var 42) -> var 42
example : ev (.app (.app TT .top) (.var 42)) = some (.var 42) := rfl

-- TT UNIT TT -> TT (applying TT to UNIT and TT gives back TT)
example : ev (.app (.app TT UNIT) TT) = some TT := rfl

-- UNIT T x -> T (returns the type parameter)
example : ev (.app (.app UNIT .top) (.var 42)) = some .top := rfl

-- ============================================================
-- Subtype derivations
-- ============================================================

/-- TT <= UNIT
    [Lam] top <= top, then
    [Lam] (var 0) <= (var 0), then
    [Var] var 0 <= var 1 -/
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

/-- UNIT <= T -/
example : Sub [] UNIT .top := Sub.top [] UNIT

/-- TT <= T -/
example : Sub [] TT .top := Sub.top [] TT

end Och.Simple.Std
