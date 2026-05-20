import Och.Macro
import Och.Eval
import Och.EvalSubst
import Och.Std.Bool
import Och.Std.DNat
import Och.API

/-!
# Polymorphic identity function

```
id  = λT:Type. λx:T. x
```

`id` preserves the precise singleton type of its argument:
`id T x : x` (the singleton).
-/

namespace Std

-- ============================================================
-- Definitions
-- ============================================================

def id_ := och{ λT:Type. λx:T. x }

-- ============================================================
-- Tests
-- ============================================================

section Tests

private def fuel : Nat := 100

-- ----------------------------------------------------------
-- Transparency: convertibility (positive)
-- ----------------------------------------------------------

-- id Nat 3 reduces to 3 (transparency preserved).
example : Och.checkSubtype 200 (och{ id_ Nat_ three_ }) three_ = .ok true ∧
          Och.checkSubtype 200 three_ (och{ id_ Nat_ three_ }) = .ok true := by
  native_decide

-- ----------------------------------------------------------
-- Transparency: negative
-- ----------------------------------------------------------

-- id Nat 3 should NOT equal Nat — it is more precise (singleton 3).
-- One-directional rejection: `Nat_ ⊑ id Nat_ three_` is false.
example : Och.checkSubtype 200 Nat_ (och{ id_ Nat_ three_ }) = .ok false := by
  native_decide

-- ----------------------------------------------------------
-- Computation: concEval (positive)
-- ----------------------------------------------------------

-- id Nat 3 = 3 (identity computes correctly).
example : concEval fuel (och{ id_ Nat_ three_ })
  = concEval fuel three_ := by native_decide

-- id Nat 0 = 0
example : concEval fuel (och{ id_ Nat_ zero_ })
  = .ok zero_ := by native_decide

-- id Bool true = true  (works on other types too)
example : concEval fuel (och{ id_ Bool true_ })
  = .ok true_ := by native_decide

end Tests
end Std
