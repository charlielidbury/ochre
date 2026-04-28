import Mathlib.Logic.Relation

/-! # Smoke test

Verifies that `lake build` works end-to-end and that Mathlib is importable.
This module can be removed once Wave 1 lands and other modules exercise the
toolchain.
-/

namespace Pss.Util.Smoke

example : (1 : Nat) + 1 = 2 := rfl

example : Relation.ReflTransGen (fun a b : Nat => a + 1 = b) 0 0 :=
  Relation.ReflTransGen.refl

end Pss.Util.Smoke
