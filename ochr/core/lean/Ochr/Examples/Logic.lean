import Ochr.Test

/-! # Logic: decisions and the empty type

`False`, `True` and `And` are the `Prelude`'s (`Ochr/Prelude.lean`), which every block uses
implicitly. This library adds `Dec(P, Q)`, a decision that carries its evidence, and `Void`, a
type with no values, with `absurdV`. -/

open Ochr.Test

ochr Logic {
  -- A decision that carries its evidence: `Yes` with a proof of `P`, or `No` with a proof of
  -- `Q` (`LeDec` in `Words` decides the order on `Word`). At runtime `Dec` is a boolean; its
  -- fields are proofs, which are erased.
  inductive Dec (P : Prop) (Q : Prop) := Yes(h : P) | No(k : Q)

  -- A type with no values, and a proof of `False` from one.
  inductive Void : Type
  def absurdV (v : Void) : False := match v {}
}
