import Ochr.Meaning.Sem

/-!
# The type the reference run returns, and what it reads a function type off a term as

A type's meaning is a code (`Sem.lean`, docs/31 D59), which carries its whole structure: a function
type's telescope, a data type's declaration and parameters. So the type the reference run returns
with a meaning (`TyS`) is the code and, for a borrow-typed result, the label of the borrow; nothing
is carried beside the code.

To build a function type's code the reference run reads its parameters and codomain off the term
as functions of the earlier arguments (`PiDom`, `PiCod`): the type each domain term and the codomain
term run to, at each tuple of arguments. These describe how a code is computed; they are not
stored in a type (`Apply.lean`'s `telL` turns them into the telescope code).
-/

namespace Ochr.Meaning

/-- A type as the reference run knows it: its meaning (a code), and for a borrow-typed result the
label of the borrow. -/
structure TyS : Type 3 where
  m : TyM
  label : Option Nat := none

/-- A type with no borrow label. -/
def TyS.plain (T : TyM) : TyS := ⟨T, none⟩

/-- The declaration's name and parameters' meanings of a data type, read off its code: what a
constructor value that records no parameters is read at (docs/31 D8). -/
def TyS.data (R : DataRead) (T : TyS) : Option (String × List Sem) := T.m.dataName? R

/-- A parameter of a function type as the reference run reads it off the term: whether it is a
borrow (`&A`), and its (content) type at each tuple of earlier arguments. -/
structure PiDom : Type 3 where
  isRef : Bool
  dom : List Sem → TyM

/-- The codomain of a function type as the reference run reads it: a returned borrow `&U` or
borrow-free data `B`, at each tuple of arguments. -/
structure PiCod : Type 3 where
  isRef : Bool
  cod : List Sem → TyM

/-- A Π into a proposition: a proposition, however large the domains (impredicativity). Each
parameter ranges over its level-1 carrier so that `Π(A : Type₀). P(A)` and `Π(P : Prop). Q(P)`
are covered; a borrow parameter contributes nothing to a proof. -/
def piProp (R : DataRead) : List PiDom → List Sem → (List Sem → Prop) → Prop
  | [], acc, P => P acc
  | p :: ps, acc, P => ∀ a : (p.dom acc).el1, piProp R ps (acc ++ [(p.dom acc).code1.2.enc R a]) P

end Ochr.Meaning
