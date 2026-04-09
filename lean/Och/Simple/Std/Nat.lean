import Och.Simple.Syntax
import Och.Simple.Subtype
import Och.Simple.Eval

/-!
# Church-encoded Natural Numbers for Simple Och

```
NAT   = λa:⊤. λz:a. λf:(λx:a. a). a
ZERO  = λa:⊤. λz:a. λf:(λx:a. a). z
SUCC  = λn:NAT. λa:⊤. λz:a. λf:(λx:a. a). f (n a z f)
ADD   = λn:NAT. λm:NAT. n NAT m SUCC
```

Parameter order: z before f (matching full Och), so that ADD works correctly:
  ADD ZERO m = ZERO NAT m SUCC = m  (ZERO returns z=m)
-/

set_option autoImplicit false

namespace Och.Simple.Std

open Och.Simple Expr

-- ============================================================
-- Definitions
-- ============================================================

-- Helper: the "a → a" domain annotation used for the f parameter.
-- At depth 2 (after binding a, z where a is at var 1):
-- (λx:a. a) = lam (var 1) (var 2)
private def arrAA : Expr := .lam (.var 1) (.var 2)

/-- NAT = λa:⊤. λz:a. λf:(λx:a. a). a
    depth 0 → 1 (bind a): a=0
    depth 1 → 2 (bind z): a=1, z=0. DOM_Z at depth 1: var 0 (a)
    depth 2 → 3 (bind f): a=2, z=1, f=0. DOM_F at depth 2: lam (var 1) (var 2)
    Body: a = var 2 -/
def NAT : Expr := .lam .top (.lam (.var 0) (.lam arrAA (.var 2)))

/-- ZERO = λa:⊤. λz:a. λf:(λx:a. a). z
    Body: z = var 1 -/
def ZERO : Expr := .lam .top (.lam (.var 0) (.lam arrAA (.var 1)))

/-- ONE = λa:⊤. λz:a. λf:(λx:a. a). f z
    Body: app (var 0) (var 1) -/
def ONE : Expr := .lam .top (.lam (.var 0) (.lam arrAA
  (.app (.var 0) (.var 1))))

/-- TWO = λa:⊤. λz:a. λf:(λx:a. a). f (f z) -/
def TWO : Expr := .lam .top (.lam (.var 0) (.lam arrAA
  (.app (.var 0) (.app (.var 0) (.var 1)))))

/-- THREE = λa:⊤. λz:a. λf:(λx:a. a). f (f (f z)) -/
def THREE : Expr := .lam .top (.lam (.var 0) (.lam arrAA
  (.app (.var 0) (.app (.var 0) (.app (.var 0) (.var 1))))))

/-- SUCC = λn:NAT. λa:⊤. λz:a. λf:(λx:a. a). f (n a z f)
    depth 4: n=3, a=2, z=1, f=0
    Body: app (var 0) (app (app (app (var 3) (var 2)) (var 1)) (var 0)) -/
def SUCC : Expr :=
  .lam NAT (.lam .top (.lam (.var 0) (.lam arrAA
    (.app (.var 0) (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0))))))

/-- ADD = λn:NAT. λm:NAT. n NAT m SUCC
    depth 2: n=1, m=0
    Body: app (app (app (var 1) NAT) (var 0)) SUCC -/
def ADD : Expr :=
  .lam NAT (.lam NAT
    (.app (.app (.app (.var 1) NAT) (.var 0)) SUCC))

-- ============================================================
-- Evaluation tests
-- ============================================================

private def ev (e : Expr) : Option Expr := eval 200 e

-- ZERO ⊤ (var 99) (var 42) → var 99  (returns z)
example : ev (.app (.app (.app ZERO .top) (.var 99)) (.var 42)) = some (.var 99) := rfl

-- ONE ⊤ z f → f z
example : ev (.app (.app (.app ONE .top) (.var 99)) (.var 42))
  = some (.app (.var 42) (.var 99)) := rfl

-- TWO ⊤ z f → f (f z)
example : ev (.app (.app (.app TWO .top) (.var 99)) (.var 42))
  = some (.app (.var 42) (.app (.var 42) (.var 99))) := rfl

-- THREE ⊤ z f → f (f (f z))
example : ev (.app (.app (.app THREE .top) (.var 99)) (.var 42))
  = some (.app (.var 42) (.app (.var 42) (.app (.var 42) (.var 99)))) := rfl

-- SUCC ZERO: (SUCC ZERO) ⊤ z f → f (ZERO ⊤ z f)
-- The inner ZERO application stays unevaluated in call-by-name (f is stuck).
example : ev (.app (.app (.app (.app SUCC ZERO) .top) (.var 99)) (.var 42))
  = some (.app (.var 42) (.app (.app (.app ZERO .top) (.var 99)) (.var 42))) := rfl

-- SUCC ZERO with concrete successor: use (λx:⊤.x) as f
-- SUCC ZERO ⊤ z (λx.x) → (λx.x) (ZERO ⊤ z (λx.x)) → ZERO ⊤ z (λx.x) → z
private def idFn : Expr := .lam .top (.var 0)
example : ev (.app (.app (.app (.app SUCC ZERO) .top) (.var 99)) idFn)
  = some (.var 99) := rfl

-- ADD ZERO ONE ⊤ z f → ONE ⊤ z f → f z
-- (ADD ZERO ONE = ZERO NAT ONE SUCC, ZERO returns z=ONE)
example : ev (.app (.app (.app (.app (.app ADD ZERO) ONE) .top) (.var 99)) (.var 42))
  = some (.app (.var 42) (.var 99)) := rfl

-- ============================================================
-- Subtype derivations
-- ============================================================

-- Context shorthand for depth 3 under NAT's lams:
-- Γ₃ = [arrAA_shifted, var 0, top]
-- where arrAA_shifted is the domain of f (lam (var 1) (var 2)) from NAT's structure

/-- ZERO ⊑ NAT -/
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
        -- var 1 ⊑ var 2 in [arrAA, var 0, top]
        -- Ctx.get? 1 = (var 0).shift 0 2 = var 2
        (Sub.var [arrAA, .var 0, .top] 1 (.var 2) (.var 2)
          rfl
          (Sub.refl [arrAA, .var 0, .top] (.var 2)))))

/-- ONE ⊑ NAT
    Innermost: app (var 0) (var 1) ⊑ var 2
    Use [App]: f=var 0, a=var 1
    Context: [arrAA, var 0, top]
    Ctx.get? 0 = arrAA.shift 0 1 = lam (var 2) (var 3)
    So D=var 2, R=var 3
    a=var 1 ⊑ D=var 2: Ctx.get? 1 = (var 0).shift 0 2 = var 2, refl
    R[0:=a] = (var 3).subst 0 (var 1) = var 2 ⊑ var 2: refl -/
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
          -- var 0 ⊑ lam (var 2) (var 3) via [Var]
          (Sub.var [arrAA, .var 0, .top] 0
            (.lam (.var 2) (.var 3)) (.lam (.var 2) (.var 3))
            rfl
            (Sub.refl [arrAA, .var 0, .top] (.lam (.var 2) (.var 3))))
          -- var 1 ⊑ var 2 via [Var]
          (Sub.var [arrAA, .var 0, .top] 1 (.var 2) (.var 2)
            rfl
            (Sub.refl [arrAA, .var 0, .top] (.var 2)))
          -- R[0:=a] = var 2 ⊑ var 2
          (Sub.refl [arrAA, .var 0, .top] (.var 2)))))

end Och.Simple.Std
