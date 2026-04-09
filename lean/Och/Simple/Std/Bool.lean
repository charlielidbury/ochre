import Och.Simple.Syntax
import Och.Simple.Subtype
import Och.Simple.Eval

/-!
# Church-encoded Booleans for Simple Och

```
BOOL  = λt:⊤. λa:t. λb:t. t
TRUE  = λt:⊤. λa:t. λb:t. a
FALSE = λt:⊤. λa:t. λb:t. b
```
-/

set_option autoImplicit false

namespace Och.Simple.Std

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

/-- IF = λb:BOOL. λt:⊤. λa:t. λb':t. b t a b'
    At depth 4: b=3, t=2, a=1, b'=0 -/
def IF : Expr :=
  .lam BOOL (.lam .top (.lam (.var 0) (.lam (.var 1)
    (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)))))

/-- NOT = λb:BOOL. b BOOL FALSE TRUE -/
def NOT : Expr :=
  .lam BOOL (.app (.app (.app (.var 0) BOOL) FALSE) TRUE)

/-- AND = λa:BOOL. λb:BOOL. a BOOL b FALSE
    At depth 2: a=1, b=0 -/
def AND : Expr :=
  .lam BOOL (.lam BOOL (.app (.app (.app (.var 1) BOOL) (.var 0)) FALSE))

/-- OR = λa:BOOL. λb:BOOL. a BOOL TRUE b
    At depth 2: a=1, b=0 -/
def OR : Expr :=
  .lam BOOL (.lam BOOL (.app (.app (.app (.var 1) BOOL) TRUE) (.var 0)))

-- ============================================================
-- Evaluation tests
-- ============================================================

private def ev (e : Expr) : Option Expr := eval 100 e

-- TRUE ⊤ x y → x
example : ev (.app (.app (.app TRUE .top) (.var 42)) (.var 99)) = some (.var 42) := rfl

-- FALSE ⊤ x y → y
example : ev (.app (.app (.app FALSE .top) (.var 42)) (.var 99)) = some (.var 99) := rfl

-- IF TRUE ⊤ x y → x
example : ev (.app (.app (.app (.app IF TRUE) .top) (.var 42)) (.var 99)) = some (.var 42) := rfl

-- IF FALSE ⊤ x y → y
example : ev (.app (.app (.app (.app IF FALSE) .top) (.var 42)) (.var 99)) = some (.var 99) := rfl

-- NOT TRUE → FALSE (evaluated: NOT TRUE ⊤ x y → y)
example : ev (.app (.app (.app (.app NOT TRUE) .top) (.var 42)) (.var 99)) = some (.var 99) := rfl

-- NOT FALSE → TRUE (evaluated: NOT FALSE ⊤ x y → x)
example : ev (.app (.app (.app (.app NOT FALSE) .top) (.var 42)) (.var 99)) = some (.var 42) := rfl

-- AND TRUE TRUE → TRUE (evaluated with ⊤ x y → x)
example : ev (.app (.app (.app (.app (.app AND TRUE) TRUE) .top) (.var 42)) (.var 99)) = some (.var 42) := rfl

-- AND TRUE FALSE → FALSE (evaluated with ⊤ x y → y)
example : ev (.app (.app (.app (.app (.app AND TRUE) FALSE) .top) (.var 42)) (.var 99)) = some (.var 99) := rfl

-- AND FALSE TRUE → FALSE
example : ev (.app (.app (.app (.app (.app AND FALSE) TRUE) .top) (.var 42)) (.var 99)) = some (.var 99) := rfl

-- AND FALSE FALSE → FALSE
example : ev (.app (.app (.app (.app (.app AND FALSE) FALSE) .top) (.var 42)) (.var 99)) = some (.var 99) := rfl

-- OR TRUE TRUE → TRUE
example : ev (.app (.app (.app (.app (.app OR TRUE) TRUE) .top) (.var 42)) (.var 99)) = some (.var 42) := rfl

-- OR TRUE FALSE → TRUE
example : ev (.app (.app (.app (.app (.app OR TRUE) FALSE) .top) (.var 42)) (.var 99)) = some (.var 42) := rfl

-- OR FALSE TRUE → TRUE
example : ev (.app (.app (.app (.app (.app OR FALSE) TRUE) .top) (.var 42)) (.var 99)) = some (.var 42) := rfl

-- OR FALSE FALSE → FALSE
example : ev (.app (.app (.app (.app (.app OR FALSE) FALSE) .top) (.var 42)) (.var 99)) = some (.var 99) := rfl

-- ============================================================
-- Subtype derivations
-- ============================================================

-- Helper: construct TRUE ⊑ BOOL proof in any context (reusable)
private def trueSub (Γ : Ctx) : Sub Γ TRUE BOOL :=
  Sub.lam Γ .top .top
    (.lam (.var 0) (.lam (.var 1) (.var 1)))
    (.lam (.var 0) (.lam (.var 1) (.var 2)))
    (Sub.refl Γ .top)
    (Sub.lam (.top :: Γ) (.var 0) (.var 0)
      (.lam (.var 1) (.var 1))
      (.lam (.var 1) (.var 2))
      (Sub.refl (.top :: Γ) (.var 0))
      (Sub.lam (.var 0 :: .top :: Γ) (.var 1) (.var 1)
        (.var 1)
        (.var 2)
        (Sub.refl (.var 0 :: .top :: Γ) (.var 1))
        (Sub.var (.var 1 :: .var 0 :: .top :: Γ) 1 (.var 2) (.var 2)
          rfl
          (Sub.refl (.var 1 :: .var 0 :: .top :: Γ) (.var 2)))))

/-- TRUE ⊑ BOOL -/
example : Sub [] TRUE BOOL := trueSub []

-- Helper: construct FALSE ⊑ BOOL proof in any context
private def falseSub (Γ : Ctx) : Sub Γ FALSE BOOL :=
  Sub.lam Γ .top .top
    (.lam (.var 0) (.lam (.var 1) (.var 0)))
    (.lam (.var 0) (.lam (.var 1) (.var 2)))
    (Sub.refl Γ .top)
    (Sub.lam (.top :: Γ) (.var 0) (.var 0)
      (.lam (.var 1) (.var 0))
      (.lam (.var 1) (.var 2))
      (Sub.refl (.top :: Γ) (.var 0))
      (Sub.lam (.var 0 :: .top :: Γ) (.var 1) (.var 1)
        (.var 0)
        (.var 2)
        (Sub.refl (.var 0 :: .top :: Γ) (.var 1))
        (Sub.var (.var 1 :: .var 0 :: .top :: Γ) 0 (.var 2) (.var 2)
          rfl
          (Sub.refl (.var 1 :: .var 0 :: .top :: Γ) (.var 2)))))

/-- FALSE ⊑ BOOL -/
example : Sub [] FALSE BOOL := falseSub []

end Och.Simple.Std
