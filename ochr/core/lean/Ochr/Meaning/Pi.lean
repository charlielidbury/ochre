import Ochr.Meaning.Value

/-!
# Carriers of Π-types (docs/18 Def. "meaning of types", function types; `Slice.lean` §1)

An n-ary `Π(x₁ : A₁, …, xₙ : Aₙ). B` is a telescope: each parameter type is a function of the
meanings of the earlier parameters, and so is the codomain. Its carrier is built by recursion
on the parameters, accumulating the prefix of meanings (`List Sem`) and the type `Fin` of the
*final contents* of the borrow parameters seen so far: a borrow parameter `x : &T` contributes
its content type `T` to the domain and to `Fin` (a function with borrow parameters means a
function from the parameters' starting contents to the result and the borrowed places' final
contents). The output is one of three shapes (`PiOut`): a proposition (impredicative: the Π
is a proposition and needs no carrier, `piProp`), borrow-free data `B × Fin`, or a returned
borrow `&U`: the forward value in `U` with an *injective* backward function `U → Fin`
(`Back`), docs/18's relation R folded into the carrier.

Levels: a Π at `Type₀` has every component at level ≤ 1 and its carrier is `piCar0 : Type`; a Π
at `Type₁` or `Type₂` lifts lower components (`piCar1`, `piCar2`). Which applies is read off the
declared sorts (D55), by the reference run.
-/

namespace Ochr.Meaning

universe u

/-- The level-0 carrier of a type meaning (`PEmpty` off level ≤ 1). -/
def TyM.el0 : TyM → Type
  | .ty0 A => A
  | .prop P => PLift P
  | _ => PEmpty

/-- The level-1 carrier: level-1 types, the universes `Prop` and `Type₀`, lower levels lifted. -/
def TyM.el1 : TyM → Type 1
  | .ty1 A => A
  | .univ 0 => ULift Prop
  | .univ 1 => Type
  | T => ULift.{1} T.el0

/-- The level-2 carrier: level-2 types, the universe `Type₁`, lower levels lifted. -/
def TyM.el2 : TyM → Type 2
  | .ty2 A => A
  | .univ 2 => Type 1
  | T => ULift.{2} T.el1

/-- Encode an element of a level-0 carrier as a meaning. -/
def TyM.enc0 : (T : TyM) → T.el0 → Sem
  | .ty0 A, a => .el0 A a
  | .prop _, _ => .proof
  | .ty1 _, x | .ty2 _, x | .univ _, x | .err, x => x.elim

/-- Encode an element of a level-1 carrier. -/
def TyM.enc1 : (T : TyM) → T.el1 → Sem
  | .ty1 A, a => .el1 A a
  | .univ 0, P => .ty (.prop P.down)
  | .univ 1, A => .ty (.ty0 A)
  | .ty0 A, a => .el0 A a.down
  | .prop _, _ => .proof
  | .univ (_ + 2), x | .ty2 _, x | .err, x => x.down.elim

/-- Encode an element of a level-2 carrier. -/
def TyM.enc2 : (T : TyM) → T.el2 → Sem
  | .ty2 A, a => .el2 A a
  | .univ 2, A => .ty (.ty1 A)
  | .ty1 A, a => .el1 A a.down
  | .univ 0, P => .ty (.prop P.down.down)
  | .univ 1, A => .ty (.ty0 A.down)
  | .ty0 A, a => .el0 A a.down.down
  | .prop _, _ => .proof
  | .univ (_ + 3), x | .err, x => x.down.down.elim

/-- A parameter of a Π-type as the model reads it: whether it is a borrow, and its (content)
type as a function of the meanings of the earlier parameters. -/
structure PiParam : Type 3 where
  isRef : Bool
  dom : List Sem → TyM

/-- What a call returning `&U` from borrowed places with final contents `Fin` gives back: the
returned borrow's content at return, and an injective backward function from the value the
caller leaves in it to the final contents (`Slice.lean`'s `Back`). -/
def Back (Fin U : Type u) : Type u := {p : U × (U → Fin) // ∀ v w, p.2 v = p.2 w → v = w}

/-- The output of a Π with data codomain, as a function of the prefix and of `Fin`. -/
inductive PiOut : Type 3 where
  /-- borrow-free data `B`: the result with the final contents -/
  | data (B : List Sem → TyM)
  /-- a returned borrow `&U`: `Back Fin U` -/
  | ref (U : List Sem → TyM)

def PiOut.car0 : PiOut → List Sem → Type → Type
  | .data B, acc, Fin => (B acc).el0 × Fin
  | .ref U, acc, Fin => Back Fin (U acc).el0

/-- The level-0 carrier of a Π with the parameters `ps` after the prefix `acc`, with the final
contents accumulated so far in `Fin` (`PUnit` at the start). -/
def piCar0 : List PiParam → List Sem → Type → PiOut → Type
  | [], acc, Fin, out => out.car0 acc Fin
  | p :: ps, acc, Fin, out =>
    (a : (p.dom acc).el0) →
      piCar0 ps (acc ++ [(p.dom acc).enc0 a]) (match p.isRef with | true => Fin × (p.dom acc).el0 | false => Fin) out

/-- A Π into a proposition: a proposition, however large the domains (impredicativity). Each
parameter ranges over its level-1 carrier so that `Π(A : Type₀). P(A)` and `Π(P : Prop). Q(P)`
are covered; a borrow parameter contributes nothing to a proof. -/
def piProp : List PiParam → List Sem → (List Sem → Prop) → Prop
  | [], acc, P => P acc
  | p :: ps, acc, P => ∀ a : (p.dom acc).el1, piProp ps (acc ++ [(p.dom acc).enc1 a]) P

/-- The level-1 carrier of a Π at `Type₁`: parameters and codomain at their level-1 carriers,
no final contents (a type-level function borrows nothing: `&` is applied only at `Type₀`). -/
def piCar1 : List PiParam → List Sem → (List Sem → TyM) → Type 1
  | [], acc, B => (B acc).el1
  | p :: ps, acc, B => (a : (p.dom acc).el1) → piCar1 ps (acc ++ [(p.dom acc).enc1 a]) B

/-- The level-2 carrier of a Π at `Type₂`. -/
def piCar2 : List PiParam → List Sem → (List Sem → TyM) → Type 2
  | [], acc, B => (B acc).el2
  | p :: ps, acc, B => (a : (p.dom acc).el2) → piCar2 ps (acc ++ [(p.dom acc).enc2 a]) B

/-- `TailM (x : &Nat) : &Nat` as a level-0 Π-carrier: `Slice.lean`'s `TailMTy`, up to the
accumulated `PUnit`. -/
example : piCar0 [⟨true, fun _ => .ty0 Nat⟩] [] PUnit (.ref fun _ => .ty0 Nat)
    = ((d : Nat) → Back (PUnit × Nat) Nat) := rfl

/-- `AddM (x : &Nat) (y : Nat) : Unit`: from the starting content and `y` to `()` and the
final content. -/
example : piCar0 [⟨true, fun _ => .ty0 Nat⟩, ⟨false, fun _ => .ty0 Nat⟩] [] PUnit (.data fun _ => .ty0 Unit)
    = ((d : Nat) → (y : Nat) → Unit × (PUnit × Nat)) := rfl

/-- `Π(A : Type₀). Π(x : A). A` at level 1: the polymorphic identity's type. -/
example : piCar1 [⟨false, fun _ => .univ 1⟩, ⟨false, fun acc => (acc.getD 0 .err).asTy⟩] []
      (fun acc => (acc.getD 0 .err).asTy)
    = ((A : Type) → (x : ULift.{1} A) → ULift.{1} A) := rfl

end Ochr.Meaning
