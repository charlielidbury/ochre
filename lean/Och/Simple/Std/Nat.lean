import Och.Simple.Macro
import Och.Simple.Subtype
import Och.Simple.Eval
import Och.Simple.Std.Bool

/-!
# Church-encoded Natural Numbers for Simple Och

```
NAT   = λa:T. λz:a. λf:(a -> a). a
ZERO  = λa:T. λz:a. λf:(a -> a). z
SUCC  = λn:NAT. λa:T. λz:a. λf:(a -> a). f (n a z f)
ADD   = λn:NAT. λm:NAT. n NAT m SUCC
```
-/

set_option autoImplicit false

namespace Och.Simple.Std

open Och.Simple Expr

-- ============================================================
-- Definitions
-- ============================================================

/-- NAT = λa:T. λz:a. λf:(a -> a). a -/
def NAT : Expr := soch{ λ(a : ⊤). λ(z : a). λ(f : a → a). a }

/-- ZERO = λa:T. λz:a. λf:(a -> a). z -/
def ZERO : Expr := soch{ λ(a : ⊤). λ(z : a). λ(f : a → a). z }

/-- ONE = λa:T. λz:a. λf:(a -> a). f z -/
def ONE : Expr := soch{ λ(a : ⊤). λ(z : a). λ(f : a → a). f z }

/-- TWO = λa:T. λz:a. λf:(a -> a). f (f z) -/
def TWO : Expr := soch{ λ(a : ⊤). λ(z : a). λ(f : a → a). f (f z) }

/-- THREE = λa:T. λz:a. λf:(a -> a). f (f (f z)) -/
def THREE : Expr := soch{ λ(a : ⊤). λ(z : a). λ(f : a → a). f (f (f z)) }

/-- FOUR = λa:T. λz:a. λf:(a -> a). f (f (f (f z))) -/
def FOUR : Expr := soch{ λ(a : ⊤). λ(z : a). λ(f : a → a). f (f (f (f z))) }

/-- FIVE = λa:T. λz:a. λf:(a -> a). f (f (f (f (f z)))) -/
def FIVE : Expr := soch{ λ(a : ⊤). λ(z : a). λ(f : a → a). f (f (f (f (f z)))) }

/-- SUCC = λn:NAT. λa:T. λz:a. λf:(a -> a). f (n a z f) -/
def SUCC : Expr := soch{ λ(n : NAT). λ(a : ⊤). λ(z : a). λ(f : a → a). f (n a z f) }

/-- ADD = λn:NAT. λm:NAT. n NAT m SUCC -/
def ADD : Expr := soch{ λ(n : NAT). λ(m : NAT). n NAT m SUCC }

/-- MUL = λn:NAT. λm:NAT. n NAT ZERO (λacc:NAT. ADD acc m) -/
def MUL : Expr := soch{ λ(n : NAT). λ(m : NAT). n NAT ZERO (λ(acc : NAT). ADD acc m) }

/-- ISZERO = λn:NAT. n BOOL TRUE (λ_:BOOL. FALSE)
    Uses BOOL from the Bool module. -/
def ISZERO : Expr := soch{ λ(n : NAT). n BOOL TRUE (BOOL → FALSE) }

-- ============================================================
-- Evaluation tests
-- ============================================================

private def ev (e : Expr) : Option Expr := eval 200 e

-- ZERO T z f -> z
example : ev (.app (.app (.app ZERO .top) (.var 99)) (.var 42)) = some (.var 99) := rfl

-- ONE T z f -> f z
example : ev (.app (.app (.app ONE .top) (.var 99)) (.var 42))
  = some (.app (.var 42) (.var 99)) := rfl

-- TWO T z f -> f (f z)
example : ev (.app (.app (.app TWO .top) (.var 99)) (.var 42))
  = some (.app (.var 42) (.app (.var 42) (.var 99))) := rfl

-- THREE T z f -> f (f (f z))
example : ev (.app (.app (.app THREE .top) (.var 99)) (.var 42))
  = some (.app (.var 42) (.app (.var 42) (.app (.var 42) (.var 99)))) := rfl

-- SUCC ZERO with identity successor: gives z
private def idFn : Expr := soch{ λ(x : ⊤). x }
example : ev (.app (.app (.app (.app SUCC ZERO) .top) (.var 99)) idFn)
  = some (.var 99) := rfl

-- SUCC ZERO with stuck f: f applied to (ZERO T z f)
example : ev (.app (.app (.app (.app SUCC ZERO) .top) (.var 99)) (.var 42))
  = some (.app (.var 42) (.app (.app (.app ZERO .top) (.var 99)) (.var 42))) := rfl

-- ADD ZERO ONE T z f -> ONE T z f -> f z
example : ev (.app (.app (.app (.app (.app ADD ZERO) ONE) .top) (.var 99)) (.var 42))
  = some (.app (.var 42) (.var 99)) := rfl

-- ADD ONE ONE with identity successor (concrete: gives z)
example : ev (.app (.app (.app (.app (.app ADD ONE) ONE) .top) (.var 99)) idFn)
  = some (.var 99) := rfl

-- ISZERO ZERO -> TRUE behavior (selects first)
example : ev (.app (.app (.app (.app ISZERO ZERO) .top) (.var 42)) (.var 99))
  = some (.var 42) := rfl

-- ISZERO ONE -> FALSE behavior (selects second)
example : ev (.app (.app (.app (.app ISZERO ONE) .top) (.var 42)) (.var 99))
  = some (.var 99) := rfl

-- ISZERO TWO -> FALSE behavior
example : ev (.app (.app (.app (.app ISZERO TWO) .top) (.var 42)) (.var 99))
  = some (.var 99) := rfl

-- MUL ZERO ONE T z f -> ZERO behavior (z)
example : ev (.app (.app (.app (.app (.app MUL ZERO) ONE) .top) (.var 99)) idFn)
  = some (.var 99) := rfl

-- MUL ONE ONE with identity -> z (ONE = 1 iteration of SUCC starting from ZERO)
-- MUL ONE ONE = ONE NAT ZERO (λacc. ADD acc ONE)
-- = (λacc. ADD acc ONE) ZERO = ADD ZERO ONE = ONE
example : ev (.app (.app (.app (.app (.app MUL ONE) ONE) .top) (.var 99)) idFn)
  = some (.var 99) := rfl

-- ============================================================
-- Subtype derivations
-- ============================================================

-- Helper: the "a -> a" domain used for f parameter
-- At depth 2 (in [f:(a->a), z:a, a:T]): a = var 2
-- arrAA = lam (var 1) (var 2) -- at depth 2 before f's binder
private def arrAA : Expr := .lam (.var 1) (.var 2)

/-- ZERO <= NAT -/
example : Sub [] ZERO NAT :=
  Sub.lam [] .top .top
    (.lam (.var 0) (.lam arrAA (.var 1)))
    (.lam (.var 0) (.lam arrAA (.var 2)))
    (Sub.refl [] .top)
    (Sub.lam [.top] (.var 0) (.var 0)
      (.lam arrAA (.var 1))
      (.lam arrAA (.var 2))
      (Sub.refl [.top] (.var 0))
      (Sub.lam [.var 0, .top] arrAA arrAA
        (.var 1)
        (.var 2)
        (Sub.refl [.var 0, .top] arrAA)
        (Sub.var [arrAA, .var 0, .top] 1 (.var 2) (.var 2)
          rfl
          (Sub.refl [arrAA, .var 0, .top] (.var 2)))))

/-- ONE <= NAT
    Innermost: app (var 0) (var 1) <= var 2
    Use [App]: f=var 0 has type arrAA shifted, a=var 1 has type var 2 -/
example : Sub [] ONE NAT :=
  Sub.lam [] .top .top
    (.lam (.var 0) (.lam arrAA (.app (.var 0) (.var 1))))
    (.lam (.var 0) (.lam arrAA (.var 2)))
    (Sub.refl [] .top)
    (Sub.lam [.top] (.var 0) (.var 0)
      (.lam arrAA (.app (.var 0) (.var 1)))
      (.lam arrAA (.var 2))
      (Sub.refl [.top] (.var 0))
      (Sub.lam [.var 0, .top] arrAA arrAA
        (.app (.var 0) (.var 1))
        (.var 2)
        (Sub.refl [.var 0, .top] arrAA)
        -- [App]: f=var 0, a=var 1, D=var 2, R=var 3
        (Sub.app [arrAA, .var 0, .top]
          (.var 0) (.var 1) (.var 2)
          (.var 2) (.var 3)
          -- var 0 <= lam (var 2) (var 3) via [Var]
          (Sub.var [arrAA, .var 0, .top] 0
            (.lam (.var 2) (.var 3)) (.lam (.var 2) (.var 3))
            rfl
            (Sub.refl [arrAA, .var 0, .top] (.lam (.var 2) (.var 3))))
          -- var 1 <= var 2 via [Var]
          (Sub.var [arrAA, .var 0, .top] 1 (.var 2) (.var 2)
            rfl
            (Sub.refl [arrAA, .var 0, .top] (.var 2)))
          -- R[0:=a] = var 2 <= var 2
          (Sub.refl [arrAA, .var 0, .top] (.var 2)))))

/-- NAT <= T -/
example : Sub [] NAT .top := Sub.top [] NAT

end Och.Simple.Std
