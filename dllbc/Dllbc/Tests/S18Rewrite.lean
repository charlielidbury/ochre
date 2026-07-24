import Dllbc.Boundary
import Dllbc.Std

/-!
# §18 test suite — the rewriting layer

The next ergonomics layer after the M15 recursor sugar, and the fix for the M16
`count_swapL` wall: the count-preservation algebra needed motives that abstract a
computed subterm (`eqb m a`) at EVERY occurrence, hand-written and error-prone.
The mechanism is `abstractOccurrences` — syntactic subterm abstraction at the
`Term` level, post-elaboration, de Bruijn-correct under binders — with a
round-trip guarantee: `(λx. abstractOccurrences e t) e` β-reduces back to `t`.
No matching by eye, no missed occurrence, no tactic engine.
-/

open Dllbc

namespace Dllbc.Tests.S18Rewrite

def eqbA (a b : Term) : Term := .app (.app Std.eqbFnT a) b
def tnat : Nat → Term | 0 => .ctorApp "Z" [] | n + 1 => .ctorApp "S" [tnat n]

/-- The round-trip property: abstracting `e` out of `t` and applying it back
    recovers `t` (by conversion). -/
def roundTrips (e t : Term) : Bool :=
  let applied := Term.app (Term.lam (.const "Bool") (abstractOccurrences e t)) e
  match (do let a ← readC 2000 applied; let b ← readC 2000 t; pure (Val.convert 2000 a b)).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-! ## `abstractOccurrences` round-trips (the mechanism, unit-tested) -/

-- Two occurrences at the top level.
example : roundTrips (eqbA (tnat 1) (tnat 2))
  (.idT (.const "Nat") (eqbA (tnat 1) (tnat 2)) (eqbA (tnat 1) (tnat 2))) = true := by native_decide
-- An occurrence under a binder — `e` shifted, the bound var and free vars kept straight.
example : roundTrips (eqbA (tnat 1) (tnat 2))
  (.lam (.const "Nat") (.idT (.const "Nat") (eqbA (tnat 1) (tnat 2)) (.pvar 0))) = true := by native_decide
-- No occurrence: `t` is unchanged (the binder is vacuous).
example : roundTrips (eqbA (tnat 1) (tnat 2)) (.idT (.const "Nat") (tnat 3) (tnat 3)) = true := by native_decide
-- The same subterm at DIFFERENT binder depths — both abstracted correctly.
example : roundTrips (eqbA (tnat 1) (tnat 2))
  (.idT (.const "Nat") (eqbA (tnat 1) (tnat 2)) (.lam (.const "Nat") (eqbA (tnat 1) (tnat 2)))) = true := by
  native_decide

end Dllbc.Tests.S18Rewrite
