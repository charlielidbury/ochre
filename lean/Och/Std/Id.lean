import Och.Macro
import Och.Eval
import Och.EvalSubst
import Och.Std.Bool
import Och.Std.DNat
import Och.API

/-!
# Polymorphic identity functions

```
id  = λT:Type. λx:T. x
idAscribed = λT:Type. λx:T. (x : T)
```

These exist to test *transparency*: `id` preserves the precise singleton
type of its argument; `idAscribed` *also* preserves it after the A8 fix
(SoundnessAudit) — ascription is computationally transparent, so the
*value* of `(x : T)` is `x`, while its *type* is `T`. Previously
`absEval` returned `(T, T)`, making `absEvalVal idAscribed … = T` and
`concEval idAscribed … = three_` disagree on the same term, which
breaks subject reduction (`Nat_ ⊑ (zero_ : Nat_)` was accepted, but
`(zero_ : Nat_)` computes to `zero_` and `Nat_ ⊄ zero_`).

The widening *intent* (lose precision via ascription) is now expressed
by checking the *type* component, not the value: `idAscribed T x : T`,
whereas `id T x : x` (the singleton). See the type-component tests
below.
-/

namespace Std

-- ============================================================
-- Definitions
-- ============================================================

def id_ := och{ λT:Type. λx:T. x }
def idAscribed := och{ λT:Type. λx:T. (x : T) }

-- ============================================================
-- Tests
-- ============================================================

section Tests

private def fuel : Nat := 100

-- ----------------------------------------------------------
-- Transparency: convertibility (positive)
-- ----------------------------------------------------------

-- id Nat 3 reduces to 3 (transparency preserved). §6.4. Phrased as
-- bidirectional `subCheck` after the engine-collapse migration:
-- two terms are convertible iff each subsumes the other.
example : Och.subCheckE 200 (och{ id_ Nat_ three_ }) three_ = .ok true ∧
          Och.subCheckE 200 three_ (och{ id_ Nat_ three_ }) = .ok true := by
  native_decide

-- Ascription narrows asymmetrically: on the LHS, `(three_ : Nat_)`
-- presents as `Nat_` (annotation); on the RHS, as `three_` (inner).
-- So `three_ ⊑ (idAscribed Nat_ three_)` holds but not vice versa.
example : Och.subCheckE 200 three_ (och{ idAscribed Nat_ three_ }) = .ok true := by
  native_decide
example : Och.subCheckE 200 (och{ idAscribed Nat_ three_ }) three_ = .ok false := by
  native_decide

-- id_ preserves singleton; idAscribed widens to annotation.
-- id_ Nat_ three_ ⊑ idAscribed Nat_ three_ (three_ ⊑ three_ via RHS)
-- but not vice versa (Nat_ ⊄ three_ via LHS).
example : Och.subCheckE 200 (och{ id_ Nat_ three_ }) (och{ idAscribed Nat_ three_ })
            = .ok true := by native_decide
example : Och.subCheckE 200 (och{ idAscribed Nat_ three_ }) (och{ id_ Nat_ three_ })
            = .ok false := by native_decide

-- ----------------------------------------------------------
-- Transparency: negative
-- ----------------------------------------------------------

-- id Nat 3 should NOT equal Nat — it is more precise (singleton 3).
-- One-directional rejection: `Nat_ ⊑ id Nat_ three_` is false.
example : Och.subCheckE 200 Nat_ (och{ id_ Nat_ three_ }) = .ok false := by
  native_decide

-- Semantic claim: `idAscribed Nat_ three_` is typeable at `Nat_`
-- (the ascription preserves the checked type). Uses `subCheckE` —
-- the public entry point — so the test stays robust to which
-- internal pathway dispatches it.
example : Och.subCheckE 200 (och{ idAscribed Nat_ three_ }) Nat_
  = .ok true := by native_decide

-- ----------------------------------------------------------
-- Computation: concEval (positive)
-- ----------------------------------------------------------

-- id Nat 3 = 3 (identity computes correctly). Under the unified Nat_,
-- concEval on three_ normalises the numeral's fix-wrappers; its
-- result does not literally equal the syntactic `three_`, so compare
-- against concEval of three_ on both sides.
example : concEval fuel (och{ id_ Nat_ three_ })
  = concEval fuel three_ := by native_decide

-- id Nat 0 = 0
example : concEval fuel (och{ id_ Nat_ zero_ })
  = .ok zero_ := by native_decide

-- idAscribed Nat 3 = 3 (concrete evaluation is still precise)
example : concEval fuel (och{ idAscribed Nat_ three_ })
  = concEval fuel three_ := by native_decide

-- id Bool true = true  (works on other types too)
example : concEval fuel (och{ id_ Bool true_ })
  = .ok true_ := by native_decide

end Tests
end Std
