import Pss.Checker.Term

/-! # `Pss.Checker.Refl` — α-equivalence

Verbatim port of `pss/checker-artifact/src/refl.el`.

Two terms are α-equivalent if they are equal up to renaming of bound
variables.  We track an environment mapping bound variables of the LHS to
those of the RHS; free variables must match exactly.
-/

namespace Pss.Checker
namespace Term

/-- α-equivalence with an explicit environment.  `env` maps LHS bound
    variables to the corresponding RHS bound variables. -/
partial def alphaEquivalentP (t1 t2 : Term) : Bool := go [] t1 t2
where
  go (env : List (String × String)) : Term → Term → Bool
    | .top, .top => true
    | .var x, .var y =>
      match env.lookup x with
      | some y' => x == x && y == y'  -- bound: must match
      | none => x == y                 -- free: must be the same name
    | .macroRef x, .macroRef y => x == y
    | .fun_ x t1 b1, .fun_ y t2 b2 =>
      go env t1 t2 && go ((x, y) :: env) b1 b2
    | .app a1 b1, .app a2 b2 => go env a1 a2 && go env b1 b2
    | .yfix f1, .yfix f2 => go env f1 f2
    | .or alts1, .or alts2 =>
      alts1.length == alts2.length &&
      (List.zip alts1 alts2).all (fun (a, b) => go env a b)
    | _, _ => false

end Term
end Pss.Checker
