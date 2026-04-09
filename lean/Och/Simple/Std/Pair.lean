import Och.Simple.Syntax
import Och.Simple.Subtype
import Och.Simple.Eval
import Och.Simple.Std.Bool
import Och.Simple.Std.Nat

/-!
# Church-encoded Pairs for Simple Och

```
PAIR   = λa:⊤. λb:⊤. λr:⊤. λf:(λx:a. λy:b. r). r
MkPair = λa:⊤. λb:⊤. λx:a. λy:b. λr:⊤. λf:(λx:a. λy:b. r). f x y
FST    = λa:⊤. λb:⊤. λp:(PAIR a b). p a (λx:a. λy:b. x)
SND    = λa:⊤. λb:⊤. λp:(PAIR a b). p b (λx:a. λy:b. y)
```
-/

set_option autoImplicit false

namespace Och.Simple.Std

open Och.Simple Expr

-- ============================================================
-- Definitions
-- ============================================================

/-- PAIR = λa:⊤. λb:⊤. λr:⊤. λf:(λx:a. λy:b. r). r
    depth 1: a=0
    depth 2: a=1, b=0
    depth 3: a=2, b=1, r=0
    depth 4: a=3, b=2, r=1, f=0
    DOM_F at depth 3: λx:a. λy:b. r
      At depth 3: a=2, b=1, r=0
      Inside one lam: a=3, b=2, r=1
      Inside two lams: a=4, b=3, r=2
      DOM_F = lam (var 2) (lam (var 2) (var 2))
    Body: r = var 1 -/
def PAIR : Expr :=
  .lam .top (.lam .top (.lam .top (.lam
    (.lam (.var 2) (.lam (.var 2) (.var 2)))
    (.var 1))))

/-- MkPair = λa:⊤. λb:⊤. λx:a. λy:b. λr:⊤. λf:(λx':a. λy':b. r). f x y
    depth 1: a=0
    depth 2: a=1, b=0
    depth 3: a=2, b=1, x=0. DOM_X at depth 2: var 1 (a)
    depth 4: a=3, b=2, x=1, y=0. DOM_Y at depth 3: var 2 (b... no)

    Actually at depth 3 (after a, b, x): b is at position 1. So DOM_Y at depth 3 = var 1 (b).
    Wait: variables index into the context from most recent. At depth 3: x=0, b=1, a=2. So b=var 1.

    depth 4: a=3, b=2, x=1, y=0. DOM_Y at depth 3: var 1 (b)
    depth 5: a=4, b=3, x=2, y=1, r=0. DOM=top
    depth 6: a=5, b=4, x=3, y=2, r=1, f=0
    DOM_F at depth 5: λx':a. λy':b. r
      At depth 5: a=4, b=3, r=0
      Inside one lam: a=5, b=4, r=1
      Inside two lams: a=6, b=5, r=2
      DOM_F = lam (var 4) (lam (var 4) (var 2))
    Body at depth 6: f x y = app (app (var 0) (var 3)) (var 2) -/
def MkPair : Expr :=
  .lam .top (.lam .top (.lam (.var 1) (.lam (.var 1)
    (.lam .top (.lam
      (.lam (.var 4) (.lam (.var 4) (.var 2)))
      (.app (.app (.var 0) (.var 3)) (.var 2)))))))

/-- FST = λa:⊤. λb:⊤. λp:(PAIR a b). p a (λx:a. λy:b. x)
    depth 1: a=0
    depth 2: a=1, b=0
    depth 3: a=2, b=1, p=0
    DOM_P at depth 2: PAIR a b = app (app PAIR (var 1)) (var 0)
    Body at depth 3: p a (λx:a. λy:b. x) = app (app (var 0) (var 2)) SELECTOR
    SELECTOR at depth 3: λx:a. λy:b. x
      At depth 3: a=2
      Inside one lam (depth 4): a=3, domain = var 2 (a at depth 3)
      Inside two lams (depth 5): a=4, b=3(at depth 3 b=1, +1=2 then +1=3)
        Actually: at depth 3 b=1. Going under x's lam: b=2. Going under y's lam: b=3.
        Domain of y at depth 4: var 2 (b shifted from 1 at depth 3 to 2 at depth 4)
      body = x = var 1
    SELECTOR = lam (var 2) (lam (var 2) (var 1)) -/
def FST : Expr :=
  .lam .top (.lam .top (.lam
    (.app (.app PAIR (.var 1)) (.var 0))
    (.app (.app (.var 0) (.var 2)) (.lam (.var 2) (.lam (.var 2) (.var 1))))))

/-- SND = λa:⊤. λb:⊤. λp:(PAIR a b). p b (λx:a. λy:b. y)
    Same structure as FST but selects b and returns y.
    Body at depth 3: p b (λx:a. λy:b. y) = app (app (var 0) (var 1)) SELECTOR_SND
    SELECTOR_SND = lam (var 2) (lam (var 2) (var 0)) -/
def SND : Expr :=
  .lam .top (.lam .top (.lam
    (.app (.app PAIR (.var 1)) (.var 0))
    (.app (.app (.var 0) (.var 1)) (.lam (.var 2) (.lam (.var 2) (.var 0))))))

-- ============================================================
-- Evaluation tests
-- ============================================================

private def ev (e : Expr) : Option Expr := eval 200 e

-- MkPair ⊤ ⊤ (var 42) (var 99) creates a pair
-- Then FST ⊤ ⊤ pair → var 42
private def testPair : Expr := .app (.app (.app (.app MkPair .top) .top) (.var 42)) (.var 99)

-- FST ⊤ ⊤ (MkPair ⊤ ⊤ x y) → x
example : ev (.app (.app (.app FST .top) .top) testPair) = some (.var 42) := rfl

-- SND ⊤ ⊤ (MkPair ⊤ ⊤ x y) → y
example : ev (.app (.app (.app SND .top) .top) testPair) = some (.var 99) := rfl

-- Pair of booleans: MkPair ⊤ ⊤ TRUE FALSE, then FST gives TRUE
private def boolPair : Expr := .app (.app (.app (.app MkPair .top) .top) TRUE) FALSE

example : ev (.app (.app (.app FST .top) .top) boolPair) = some TRUE := rfl
example : ev (.app (.app (.app SND .top) .top) boolPair) = some FALSE := rfl

-- ============================================================
-- Subtype derivations
-- ============================================================

-- MkPair ⊑ (⊤ → ⊤ → ... ) is complex; just verify PAIR ⊑ ⊤ and PAIR PAIR_eq
example : Sub [] PAIR .top := Sub.top [] PAIR
example : Sub [] MkPair .top := Sub.top [] MkPair
example : Sub [] FST .top := Sub.top [] FST
example : Sub [] SND .top := Sub.top [] SND

-- Self-subtyping (refl)
example : Sub [] PAIR PAIR := Sub.refl [] PAIR
example : Sub [] MkPair MkPair := Sub.refl [] MkPair

end Och.Simple.Std
