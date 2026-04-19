import Och.Macro
import Och.Eval
import Och.TyCheck
import Och.Std.Bool
import Och.Std.Nat

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

private def fuel : Nat := 50

-- ----------------------------------------------------------
-- Transparency: NbE normal-form (positive)
-- ----------------------------------------------------------

-- id Nat 3 normalises to 3 (transparency preserved). §6.4
example : NbE.nf 200 (och{ id_ Nat_ three_ })
  = NbE.nf 200 three_ := by native_decide

-- After A8, idAscribed normalises identically to id_ (the
-- ascription is computationally transparent and NbE
-- normalises under binders). The previous "widening via asc"
-- was unsound: it accepted `Nat_ ⊑ (zero_ : Nat_)`, but
-- `(zero_ : Nat_)` computes to `zero_` and `Nat_ ⊄ zero_`
-- (subject reduction fails). Widening is now expressed via
-- `NbE.typeCheck` (which keeps the annotation as the *expected
-- type* without conflating it with the value), not via the
-- value-level evaluator.
example : NbE.nf 200 (och{ idAscribed Nat_ three_ })
  = NbE.nf 200 three_ := by native_decide

example : NbE.nf 200 (och{ idAscribed Nat_ three_ })
  = NbE.nf 200 (och{ id_ Nat_ three_ }) := by native_decide

-- ----------------------------------------------------------
-- Transparency: NbE (negative)
-- ----------------------------------------------------------

-- id Nat 3 should NOT equal Nat — it is more precise (singleton 3)
example : NbE.nf 200 (och{ id_ Nat_ three_ })
  ≠ NbE.nf 200 Nat_ := by native_decide

-- The §6.4 widening intent now lives in `NbE.typeCheck`: the
-- ascription gives `idAscribed Nat_ three_` the *checked* type
-- `Nat_`, while `id_ Nat_ three_` synthesises the singleton
-- `three_`. (Checked via tyInfer's `.asc` arm, which returns τ.)
example : NbE.typeCheck 200 (och{ idAscribed Nat_ three_ }) Nat_
  = .ok true := by native_decide

-- ----------------------------------------------------------
-- Computation: concEval (positive)
-- ----------------------------------------------------------

-- id Nat 3 = 3 (identity computes correctly)
example : concEval fuel (och{ id_ Nat_ three_ })
  = some three_ := by native_decide

-- id Nat 0 = 0
example : concEval fuel (och{ id_ Nat_ zero_ })
  = some zero_ := by native_decide

-- idAscribed Nat 3 = 3 (concrete evaluation is still precise)
example : concEval fuel (och{ idAscribed Nat_ three_ })
  = some three_ := by native_decide

-- id Bool true = true  (works on other types too)
example : concEval fuel (och{ id_ Bool true_ })
  = some true_ := by native_decide

end Tests
end Std
