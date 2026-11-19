import Ochr.Meaning.DecisionsInst
import Ochr.Meaning.Run
import Ochr.Examples.Nat
import Ochr.Examples.List
import Ochr.Examples.Box

/-!
# The drop at the join reads the places moved at entry at the checker's grain (built)

docs/31 D24 (third lead, 2026-11-19). D84's join of a match is read from the places already
moved when the match starts (`Machine.staticJoin`: `botPlaces` of each binding's value, every
place with a `⊥` inside a value) and from the arms' syntax (`Decide.jdMoves`). The reference
run's `movedPlaces` was the WHOLE variables reading `moved`, a gap recorded when it was written.
It is a fault of the model, with an accepted program on which the model's `Id` was false:

* `Refill`: `p.0` is moved before the match, one arm refills it, the other does not. The checker's
  join says `p.0` is moved and drops it after the arm taken; `RefillRead`, which reads it after
  the match, is REJECTED ("was moved out").
* `IdRefill`: the same match as one side of an `Id` whose other side leaves `p.0` moved. The
  checker accepts `refl`: both sides leave `p.0` moved. The reference, passing the entry `[]` to
  the join, left `p` whole after the first side and partly moved after the second, and `Id`
  compares every position.

Kernel-checked here: the checker's entry set of a partly moved pair is its moved field
(`botPlaces_partly`), and the reference's is the same place at the same grain
(`movedIn_partly`), where the set as first written held only whole variables. Evaluated at build
(`#guard`s on `Decide.jdMoves` through `checkerDecisions`): from the entry `[p.0]` the join of a
match one arm of which refills `p.0` is `[p.0]`, and from the entry `[]` it is `[]`.
-/

open Ochr.Test

ochr JoinProbes uses Nats, Lists, Boxes {
  -- a place moved before the match and refilled by one arm is moved after it
  def Refill (n : Nat) (xs : List(Nat)) (ys : List(Nat)) : Nat := (
    let p = (xs, Z);
    let a = p.0;
    match n { Z => (p.0 := ys; Z), S m => Z }
  )
  -- control: it is read after the match
  reject def RefillRead (n : Nat) (xs : List(Nat)) (ys : List(Nat)) : List(Nat) := (
    let p = (xs, Z);
    let a = p.0;
    match n { Z => (p.0 := ys; ()), S m => () };
    p.0
  )
  -- so two sides that differ only in refilling it are `Id`: both leave it moved
  def IdRefill (xs : List(Nat)) (ys : List(Nat)) : Nat := (
    let k = Z;
    let p = (xs, Z);
    let a = p.0;
    let h : Id(Unit, (match k { Z => (p.0 := ys; ()), S m => () }), (match k { Z => (let z = ys; ()), S m => () })) = refl;
    Z
  )
}

namespace Ochr.Meaning.Regress.JoinProbes
open Ochr Ochr.Meaning

/-- A pair type with one constructor, so that a move of a field is at the field's grain. -/
def pairD : IndDecl := { name := "P", ctors := [("MkP", [("a", .nat), ("b", .nat)])] }

/-- The first field of variable `0`. -/
def p0 : Place := .field ⟨"P", 0, 0, "a"⟩ (.var 0)

/-- The checker's entry set of `MkP(⊥, Z)` bound at variable `0`: its moved field. -/
theorem botPlaces_partly :
    ((botPlaces (.ind "P" 0 ⟨"MkP"⟩ [] [.bot, .zero]) (.var 0)) == [p0]) = true := by decide

/-- The reference's entry set of the meaning of the same value, the tuple `P.0(moved, 0)`: the
same place at the same grain. (As first written, `movedPlaces` listed only variables whose whole
meaning is `moved`, so it listed nothing here.) -/
theorem movedIn_partly :
    ((Sem.movedIn (.dat "P" [] 0 [.moved, .el0 Nat 0] none) (.var 0)) == [p0]) = true := by
  simp [Sem.movedIn, Sem.movedInFields, p0]
  decide

/-- `match k { Z => (p.0 := Z; Z), S m => Z }` with `p` at variable `0` and `k` at variable `1`:
one arm refills `p.0`. -/
def tRefill : Term := .matchNat (.var 1) (.seq (.assign p0 .zero) .zero) .zero

def stP : MState := { inds := [pairD] }
/-- The frame's readings, innermost first: `p : P`, `k : Nat`. -/
def scP : List DeclInfo := [.ind "P" [], .other]

-- from the entry `[p.0]` the join says `p.0` is moved (the arm that does not refill it leaves it so)
#guard ((checkerDecisions stP 100).joinMoves scP [p0] tRefill) == [p0]
-- from the entry `[]`, which the run used to pass, it says nothing is
#guard ((checkerDecisions stP 100).joinMoves scP [] tRefill) == []

/-! ## The slack `⊑` allowed at a binding (docs/31 D24)

`Rel` first compared a binding's meanings by `⊑`. That admits a reference state holding a value
where the checker's holds `⊥` inside a partly moved tuple, and the places moved at entry, which
the join reads, then differ. -/

/-- The checker's `P(⊥, ⊥)` is below a reference's `P(0, ⊥)` in `Sem.le`. -/
theorem slack_le : Sem.dat "P" [] 0 [.moved, .moved] none ⊑ Sem.dat "P" [] 0 [.el0 Nat 0, .moved] none :=
  .dat (.cons (.moved _) (.cons (.refl _) .nil))

/-- Their entry sets differ: `[p.0, p.1]` against `[p.1]`. -/
theorem slack_entry :
    ((Sem.movedIn (.dat "P" [] 0 [.moved, .moved] none) (.var 0)).length,
      (Sem.movedIn (.dat "P" [] 0 [.el0 Nat 0, .moved] none) (.var 0)).length) = (2, 1) := by
  simp [Sem.movedIn, Sem.movedInFields]

end Ochr.Meaning.Regress.JoinProbes
