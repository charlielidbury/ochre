import Ochr.Meaning.DataModel.Exists.Knot.Grammar
import Ochr.Test
import Ochr.Examples.Nat
import Ochr.Examples.List
import Ochr.Examples.Logic

/-!
# Value arguments at a hint that varies with the knot's records (exists7, docs/34 §18.10)

The grammar's old condition (B2) asked that a value argument of a nested occurrence not stand at a
parameter whose declared type mentions an earlier argument that varies: its hint (the parameter's
type at the earlier arguments) would vary with the knot's records. The checker does not ask it, and
Lean does not either: `NF (A : Type) (n : Nat) (f : NegF(A, n)) := MkNF(y : A)` with
`DF := LeafF | NodeF(p : NF(DF, 0, ()))` is accepted by both (Lean's kernel accepts the analogue).

(B2) is now `HintSteady ∨ hintFreeB`: the hint is steady, OR the value argument does not read its hint
(`Knot/HintFree.lean`: its head is not a constructor with its parameters left to the hint, an embedded
value, or `clone`/`peek`/`inplace`), so its value is the same at both hints (`runT_hintFree`). `DF`
passes (`()` does not read its hint), and so does a constructor with its parameters written (`DK2`).

Outside it, still: a constructor whose parameters are NOT written, at a hint computed from the type
being declared (`DK`, `DT3`; Lean accepts both). The run gives such a constructor the record of its
hint (`runT`'s `.ctor` clause, the checker's `evalCtor` `sol`), so its value carries the earlier
declaration's parameter type at the knot's own code. Here that type is `List(Nat)` whatever the code
(`TK` ignores its argument; `TF` at `0` takes the other arm), but the knot sees a global's meaning and
an earlier parameter type only through `ParamTyLocal`, which lets `PK`'s parameter type read `A`.

The two neighbours that make `DK` the residual are rejected: a value argument may not name the type
being declared (`DL`, D36/D71), and a constructor whose parameter no field determines must write it
(`DT`, resolution). So an unwritten parameter of a value argument's constructor is always fixed by its
fields, never by the type being declared; what remains is only that the run reads it from the hint.
-/

open Ochr Ochr.Test

namespace Ochr.Meaning.DataModel.Exists.HintShapes

ochr HintShapes uses Logic, Nats, Lists {
  inductive Void0 : Type
  def NegF (X : Type) (b : Nat) : Type := (match b { Z => Unit, S(k) => Π(x : X). Void0 })
  inductive NF (A : Type) (n : Nat) (f : NegF(A, n)) := MkNF(y : A)
  -- the checker's own example (D121's report): `()` does not read its hint
  inductive DF := LeafF | NodeF(p : NF(DF, 0, ()))
  def TK (X : Type) : Type := List(Nat)
  inductive PK (A : Type) (t : TK(A)) := MkPK(y : A)
  -- a constructor with its parameters written does not read its hint
  inductive DK2 := LK2 | NK2(p : PK(DK2, Nil[Nat]))
  -- a constructor with its parameter left to the hint, the hint `TK(DK)`: outside the grammar
  inductive DK := LK | NK(p : PK(DK, Cons(0, Nil[Nat])))
  def TF (X : Type) (b : Nat) : Type := (match b { Z => List(Nat), S(k) => List(X) })
  inductive PF (A : Type) (n : Nat) (t : TF(A, n)) := MkPF(y : A)
  inductive DT3 := LT3 | NT3(p : PF(DT3, 0, Cons(0, Nil[Nat])))
  -- the neighbours: a value argument naming the type, a parameter no field determines
  inductive Pl (A : Type) (l : List(A)) := MkPl(y : A)
  reject inductive DL := LeafL | NodeL(p : Pl(DL, Nil[DL]))
  inductive Tg (A : Type) := MkTg(n : Nat)
  inductive PT (A : Type) (t : Tg(A)) := MkPT(y : A)
  reject inductive DT := LT | NT(p : PT(DT, MkTg(3)))
}

#guard (Ochr.Test.run "HintShapes" HintShapes).rejectedWith [
  ("DL", "field p of NodeL : Pl(DL, Nil[DL]): fields are first-order data"),
  ("DT", "cannot infer the parameter A of MkTg")]

def prog : Surface.Program := libOf {} 2000000 HintShapes ++ HintShapes.decls

def items : List Item :=
  prog.filterMap fun d => match Surface.resolveProgram prog d with
    | .ok it => some it
    | .error _ => none

open Ochr.Meaning.DataModel.Exists.Knot in
-- the grammar at each declaration the checker stores (`DF`, `DK2` pass; `DK`, `DT3` do not), in its
-- two parts: all four pass `GrammarCoreOk`; `DK`, `DT3` fail only `GrammarHintOk` ((B2), main's D123);
-- `NF`'s, `PK`'s and `PF`'s first parameter is stored nestable
#guard let inds := (globalsAfter {} items).2
  let ok (n : String) : Option (Bool × Bool × Bool) := (inds.find? (·.name == n)).map fun d =>
    (decide (GrammarOk inds d), decide (GrammarCoreOk inds d), decide (GrammarHintOk inds d))
  let nest (n : String) : Option (List Bool) := (inds.find? (·.name == n)).map (·.nestable)
  [ok "DF", ok "DK2", ok "DK", ok "DT3"] ==
      [some (true, true, true), some (true, true, true), some (false, true, false), some (false, true, false)] &&
    [nest "NF", nest "PK", nest "PF"] == [some [true, false, false], some [true, false], some [true, false, false]]

end Ochr.Meaning.DataModel.Exists.HintShapes
