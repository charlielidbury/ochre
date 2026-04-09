import Och.Simple.Macro
import Och.Simple.Subtype
import Och.Simple.Eval

/-!
# Church-encoded Booleans for Simple Och

```
BOOL  = λt:T. λa:t. λb:t. t
TRUE  = λt:T. λa:t. λb:t. a
FALSE = λt:T. λa:t. λb:t. b
```
-/

set_option autoImplicit false

namespace Och.Simple.Std

open Och.Simple Expr

-- ============================================================
-- Definitions
-- ============================================================

/-- BOOL = λt:T. λa:t. λb:t. t -/
def BOOL : Expr := soch{ λ(t : ⊤). λ(a : t). λ(b : t). t }

/-- TRUE = λt:T. λa:t. λb:t. a -/
def TRUE : Expr := soch{ λ(t : ⊤). λ(a : t). λ(b : t). a }

/-- FALSE = λt:T. λa:t. λb:t. b -/
def FALSE : Expr := soch{ λ(t : ⊤). λ(a : t). λ(b : t). b }

/-- IF = λb:BOOL. λt:T. λa:t. λb':t. b t a b' -/
def IF : Expr := soch{ λ(b : BOOL). λ(t : ⊤). λ(a : t). λ(b' : t). b t a b' }

/-- NOT = λb:BOOL. b BOOL FALSE TRUE -/
def NOT : Expr := soch{ λ(b : BOOL). b BOOL FALSE TRUE }

/-- AND = λa:BOOL. λb:BOOL. a BOOL b FALSE -/
def AND : Expr := soch{ λ(a : BOOL). λ(b : BOOL). a BOOL b FALSE }

/-- OR = λa:BOOL. λb:BOOL. a BOOL TRUE b -/
def OR : Expr := soch{ λ(a : BOOL). λ(b : BOOL). a BOOL TRUE b }

/-- XOR = λa:BOOL. λb:BOOL. a BOOL (NOT b) b -/
def XOR : Expr := soch{ λ(a : BOOL). λ(b : BOOL). a BOOL (NOT b) b }

/-- IMPLIES = λa:BOOL. λb:BOOL. OR (NOT a) b -/
def IMPLIES : Expr := soch{ λ(a : BOOL). λ(b : BOOL). OR (NOT a) b }

-- ============================================================
-- Evaluation tests
-- ============================================================

private def ev (e : Expr) : Option Expr := eval 200 e

-- Basic elimination
example : ev (soch{ TRUE ⊤ }) = some (soch{ λ(a : ⊤). λ(b : ⊤). a }) := rfl
example : ev (soch{ FALSE ⊤ }) = some (soch{ λ(a : ⊤). λ(b : ⊤). b }) := rfl

-- TRUE T x y -> x
example : ev (.app (.app (.app TRUE .top) (.var 42)) (.var 99)) = some (.var 42) := rfl

-- FALSE T x y -> y
example : ev (.app (.app (.app FALSE .top) (.var 42)) (.var 99)) = some (.var 99) := rfl

-- IF TRUE T x y -> x
example : ev (.app (.app (.app (.app IF TRUE) .top) (.var 42)) (.var 99)) = some (.var 42) := rfl

-- IF FALSE T x y -> y
example : ev (.app (.app (.app (.app IF FALSE) .top) (.var 42)) (.var 99)) = some (.var 99) := rfl

-- NOT TRUE applied -> FALSE behavior
example : ev (.app (.app (.app (.app NOT TRUE) .top) (.var 42)) (.var 99)) = some (.var 99) := rfl

-- NOT FALSE applied -> TRUE behavior
example : ev (.app (.app (.app (.app NOT FALSE) .top) (.var 42)) (.var 99)) = some (.var 42) := rfl

-- AND truth table
example : ev (.app (.app (.app (.app (.app AND TRUE) TRUE) .top) (.var 42)) (.var 99)) = some (.var 42) := rfl
example : ev (.app (.app (.app (.app (.app AND TRUE) FALSE) .top) (.var 42)) (.var 99)) = some (.var 99) := rfl
example : ev (.app (.app (.app (.app (.app AND FALSE) TRUE) .top) (.var 42)) (.var 99)) = some (.var 99) := rfl
example : ev (.app (.app (.app (.app (.app AND FALSE) FALSE) .top) (.var 42)) (.var 99)) = some (.var 99) := rfl

-- OR truth table
example : ev (.app (.app (.app (.app (.app OR TRUE) TRUE) .top) (.var 42)) (.var 99)) = some (.var 42) := rfl
example : ev (.app (.app (.app (.app (.app OR TRUE) FALSE) .top) (.var 42)) (.var 99)) = some (.var 42) := rfl
example : ev (.app (.app (.app (.app (.app OR FALSE) TRUE) .top) (.var 42)) (.var 99)) = some (.var 42) := rfl
example : ev (.app (.app (.app (.app (.app OR FALSE) FALSE) .top) (.var 42)) (.var 99)) = some (.var 99) := rfl

-- XOR truth table
example : ev (.app (.app (.app (.app (.app XOR TRUE) TRUE) .top) (.var 42)) (.var 99)) = some (.var 99) := rfl
example : ev (.app (.app (.app (.app (.app XOR TRUE) FALSE) .top) (.var 42)) (.var 99)) = some (.var 42) := rfl
example : ev (.app (.app (.app (.app (.app XOR FALSE) TRUE) .top) (.var 42)) (.var 99)) = some (.var 42) := rfl
example : ev (.app (.app (.app (.app (.app XOR FALSE) FALSE) .top) (.var 42)) (.var 99)) = some (.var 99) := rfl

-- IMPLIES truth table: a => b = OR (NOT a) b
example : ev (.app (.app (.app (.app (.app IMPLIES TRUE) TRUE) .top) (.var 42)) (.var 99)) = some (.var 42) := rfl
example : ev (.app (.app (.app (.app (.app IMPLIES TRUE) FALSE) .top) (.var 42)) (.var 99)) = some (.var 99) := rfl
example : ev (.app (.app (.app (.app (.app IMPLIES FALSE) TRUE) .top) (.var 42)) (.var 99)) = some (.var 42) := rfl
example : ev (.app (.app (.app (.app (.app IMPLIES FALSE) FALSE) .top) (.var 42)) (.var 99)) = some (.var 42) := rfl

-- ============================================================
-- Subtype derivations
-- ============================================================

-- Helper: construct TRUE <= BOOL proof in any context (reusable)
def trueSub (G : Ctx) : Sub G TRUE BOOL :=
  Sub.lam G .top .top
    (.lam (.var 0) (.lam (.var 1) (.var 1)))
    (.lam (.var 0) (.lam (.var 1) (.var 2)))
    (Sub.refl G .top)
    (Sub.lam (.top :: G) (.var 0) (.var 0)
      (.lam (.var 1) (.var 1))
      (.lam (.var 1) (.var 2))
      (Sub.refl (.top :: G) (.var 0))
      (Sub.lam (.var 0 :: .top :: G) (.var 1) (.var 1)
        (.var 1)
        (.var 2)
        (Sub.refl (.var 0 :: .top :: G) (.var 1))
        (Sub.var (.var 1 :: .var 0 :: .top :: G) 1 (.var 2) (.var 2)
          rfl
          (Sub.refl (.var 1 :: .var 0 :: .top :: G) (.var 2)))))

/-- TRUE <= BOOL -/
example : Sub [] TRUE BOOL := trueSub []

-- Helper: construct FALSE <= BOOL proof in any context
def falseSub (G : Ctx) : Sub G FALSE BOOL :=
  Sub.lam G .top .top
    (.lam (.var 0) (.lam (.var 1) (.var 0)))
    (.lam (.var 0) (.lam (.var 1) (.var 2)))
    (Sub.refl G .top)
    (Sub.lam (.top :: G) (.var 0) (.var 0)
      (.lam (.var 1) (.var 0))
      (.lam (.var 1) (.var 2))
      (Sub.refl (.top :: G) (.var 0))
      (Sub.lam (.var 0 :: .top :: G) (.var 1) (.var 1)
        (.var 0)
        (.var 2)
        (Sub.refl (.var 0 :: .top :: G) (.var 1))
        (Sub.var (.var 1 :: .var 0 :: .top :: G) 0 (.var 2) (.var 2)
          rfl
          (Sub.refl (.var 1 :: .var 0 :: .top :: G) (.var 2)))))

/-- FALSE <= BOOL -/
example : Sub [] FALSE BOOL := falseSub []

/-- BOOL <= T -/
example : Sub [] BOOL .top := Sub.top [] BOOL

/-- (TRUE : BOOL) <= BOOL via Asc-L -/
example : Sub [] (.asc TRUE BOOL) BOOL :=
  Sub.ascL [] TRUE BOOL BOOL (trueSub []) (Sub.refl [] BOOL)

/-- TRUE <= (TRUE : BOOL) via Asc-R -/
example : Sub [] TRUE (.asc TRUE BOOL) :=
  Sub.ascR [] TRUE TRUE BOOL (trueSub []) (Sub.refl [] TRUE)

end Och.Simple.Std
