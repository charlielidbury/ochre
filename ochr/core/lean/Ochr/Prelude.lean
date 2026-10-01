import Ochr.Notation

/-!
# The library: `Prelude`

The declarations every program starts from, written in Ochr and checked like any other
block (RULES §1, §8; v2.1, D52). Every block uses `Prelude` implicitly: its declarations
come first in every program (`Ochr.Test.libOf`), and its names are in every block's
namespace. `Eq` is primitive and computes to `True`, `False` and `And` (§4), so the kernel
knows these by name, as it knows `Pair` for its notation:
* `Pair (A B : Type₀) := Mk(fst : A, snd : B)`: `A × B`, `(a, b)`, `t.0`, `t.1` are notation
  (`Surface.resolve`: `.tind "Pair"`, `.ctor "Pair" 0 Mk`; the places `.0`/`.1`,
  `Obs.stepV`, `Machine.placeType`); printed back in that notation (`Pretty`); a codomain
  written `A × B` is data (`Machine.isPropTerm?`, `paramFlags`).
* `False`: `Eq` on distinct constructors computes to it (`Machine.mkEqM`, `vFalse`).
* `True := I`: `refl` is notation for `I`, and `Eq` on equal values computes to `True`
  (`vTrue`); `⊤` is notation for `True`.
* `And := Intro(l, r)`: `P ∧ Q` and `⟨h, k⟩` are notation; `Eq` on constructor values and
  `Id` compute to it (`andList`), and the unit laws `And(True, P) ≡ P ≡ And(P, True)`
  (`Basic.mkAnd`, `unitTop`, D50) make `True` and `And` kernel-known.
`Nat` (`Z`, `S`, numerals) and `Unit` (`()`) are still built into the checker. -/

ochr Prelude {
  inductive Pair (A : Type) (B : Type) := Mk(fst : A, snd : B)
  inductive False : Prop
  inductive True : Prop := I
  inductive And (P : Prop) (Q : Prop) : Prop := Intro(l : P, r : Q)
}
