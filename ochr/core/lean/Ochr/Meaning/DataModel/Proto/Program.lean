import Ochr.Meaning.DataModel.Proto.Members

/-!
# Prototype (b2): the probe programs' declarations, their records and their signature

The declarations of `DataModel/Probes.lean` (and the library's `Word`, `Bool`, `List`), each with
the record its type keeps (`*Rec`) and its fields' shapes (`progShape`). A record keeps what the
declaration's field types read of the parameters: a type parameter's entry (its code, or its
declaration and record), a value parameter read small, and for a parameter above level 0 nothing
but the propositions and codes the field types compute from it (`teqRec`: the truth of `a = b`).
The signature is written by hand here; that it is the reference run's reading of the declared
field types is faithfulness (docs/34 §6), the assembly's obligation.
-/

namespace Ochr.Meaning.DataModel.Proto

open Ochr

def h (n : String) : Hint := ⟨n⟩

def wordD : IndDecl := { name := "Word", ctors := [("Zero", []), ("Succ", [("pred", .tind "Word" [])])] }
def boolD : IndDecl := { name := "Bool", ctors := [("false", []), ("true", [])] }
def listD : IndDecl :=
  { name := "List", params := [(h "A", .sort 1)],
    ctors := [("Nil", []), ("Cons", [("h", .place (.var 0)), ("t", .tind "List" [.place (.var 1)])])] }
def roseD : IndDecl :=
  { name := "Rose", params := [(h "A", .sort 1)],
    ctors := [("Node", [("a", .place (.var 0)), ("kids", .tind "List" [.tind "Rose" [.place (.var 1)]])])] }
def singleD : IndDecl :=
  { name := "Single", params := [(h "A", .sort 1), (h "a", .place (.var 0))],
    ctors := [("MkS", [("x", .place (.var 1)), ("e", .eq (.place (.var 2)) (.place (.var 0)) (.place (.var 1)))])] }
def teqD : IndDecl :=
  { name := "TEq", params := [(h "U", .sort 2), (h "a", .place (.var 0)), (h "b", .place (.var 1))],
    ctors := [("MkTEq", [("h", .eq (.place (.var 2)) (.place (.var 1)) (.place (.var 0)))])] }
def bwD : IndDecl :=
  { name := "BW", ctors := [("MkBW", [("b", .tind "Bool" []), ("x", .call (.const "BF") [.place (.var 0)] false)])] }
def bhD : IndDecl :=
  { name := "BH", ctors := [("MkBH", [("b", .tind "Bool" []), ("x", .call (.const "BG") [.place (.var 0)] false)])] }
def vecD : IndDecl :=
  { name := "VecF", params := [(h "A", .sort 1), (h "n", .tind "Word" [])],
    ctors := [("VNil", [("h", .eq (.tind "Word" []) (.place (.var 0)) (.ctor "Word" 0 (h "") [] []))]),
      ("VCons", [("m", .tind "Word" []), ("x", .place (.var 2)), ("xs", .tind "VecF" [.place (.var 3), .place (.var 1)]),
        ("h", .eq (.tind "Word" []) (.place (.var 4)) (.ctor "Word" 1 (h "") [] [.place (.var 2)]))])] }
def isZD : IndDecl :=
  { name := "IsZ", params := [(h "n", .tind "Word" [])], sort := 0,
    ctors := [("MkZ", [("h", .eq (.tind "Word" []) (.place (.var 0)) (.ctor "Word" 0 (h "") [] []))])] }
def fin1D : IndDecl :=
  { name := "Fin1", params := [(h "n", .nat)], ctors := [("Only", [("h", .eq .nat (.place (.var 0)) (.succ .zero))])] }
def vD : IndDecl :=
  { name := "V", ctors := [("MkV", [("n", .nat), ("x", .tind "Fin1" [.place (.var 0)])])] }

/-! ## Records -/

/-- A type's entry in a record: a data type's declaration and record, a leaf's code. A type of
level 1 has none (no field is of such a type, (I6)). -/
def entryOf : Ty → Entry
  | .t0 _ (.data d r _) => .data d r
  | .t0 A c => .leaf A c
  | .t1 _ _ => .none

def shapeOf : Entry → Shape
  | .leaf B c => .leaf B c
  | .data d r => .sub d r
  | .none => .leaf PEmpty .err

def constRec (x : Entry) : Rec := fun _ => x
def propEntry (P : Prop) : Entry := .leaf (PLift P) (.prop P)

/-- The small reading of `Zero` and `Succ(m)`. -/
def zeroS : Small := .node 0 []
def succS (m : Small) : Small := .node 1 [m]

/-- `Single(A, a)`: `A`'s entry; the equation `x = a`, `a` read small. -/
def singleRec (eA : Entry) (sa : Small) : Rec
  | [(0, 1, [sx])] => propEntry (sx = sa)
  | _ => eA

/-- `TEq(U, a, b)`: only the truth of `a = b` (`U`, of level 2, is not kept). -/
def teqRec (P : Prop) : Rec := constRec (propEntry P)

/-- `VecF(A, n)`: `A`'s entry and the two equations on `n`, read small. -/
def vecRec (eA : Entry) (sn : Small) : Rec
  | [(0, 0, _)] => propEntry (sn = zeroS)
  | [(1, 3, sm :: _)] => propEntry (sn = succS sm)
  | _ => eA

def isZRec (sn : Small) : Rec := constRec (propEntry (sn = zeroS))
def fin1Rec (sn : Small) : Rec := constRec (propEntry (sn = .el Nat 1))

/-- `BF(b)` and `BG(b)` (`DataModel/Probes.lean`), as the field types they compute. -/
def bfShape : Small → Shape
  | .node 0 [] => .leaf Nat .nat
  | .node 1 [] => .leaf Unit .unit
  | _ => .leaf PEmpty .err

def bgShape : Small → Shape
  | .node 0 [] => .leaf Nat .nat
  | .node 1 [] => .leaf (Nat → Nat) (.fn (Nat → Nat))
  | _ => .leaf PEmpty .err

/-! ## The signature -/

def progShape (d : IndDecl) (r : Rec) (c i : Nat) (e : List Small) : Shape :=
  match d.name, c, i, e with
  | "Word", 1, 0, _ => .sub d r
  | "List", 1, 0, _ => shapeOf (r [])
  | "List", 1, 1, _ => .sub d r
  | "Rose", 0, 0, _ => shapeOf (r [])
  | "Rose", 0, 1, _ => .sub listD (constRec (.data d r))
  | "Single", 0, 0, _ => shapeOf (r [])
  | "Single", 0, 1, e => shapeOf (r [(0, 1, e)])
  | "TEq", 0, 0, _ => shapeOf (r [])
  | "BW", 0, 0, _ => .sub boolD (constRec .none)
  | "BW", 0, 1, [s] => bfShape s
  | "BH", 0, 0, _ => .sub boolD (constRec .none)
  | "BH", 0, 1, [s] => bgShape s
  | "VecF", 0, 0, e => shapeOf (r [(0, 0, e)])
  | "VecF", 1, 0, _ => .sub wordD (constRec .none)
  | "VecF", 1, 1, _ => shapeOf (r [])
  | "VecF", 1, 2, sm :: _ => .sub d (vecRec (r []) sm)
  | "VecF", 1, 3, e => shapeOf (r [(1, 3, e)])
  | "IsZ", 0, 0, _ => shapeOf (r [])
  | "Fin1", 0, 0, _ => shapeOf (r [])
  | "V", 0, 0, _ => .leaf Nat .nat
  | "V", 0, 1, [s] => .sub fin1D (fin1Rec s)
  | _, _, _, _ => .leaf PEmpty .err

def S : Sig := ⟨progShape⟩

/-- A constructor value is a member when its fields fit (`mem_iff`, right to left). -/
theorem mem_intro (d : IndDecl) (r : Rec) (c : Fin d.ctors.length) (fs : List Val)
    (hf : FitsM S d r c 0 (arity d c) [] fs) : Mem S d r (.dat d.name r c fs) :=
  (mem_iff S d r _).2 ⟨c, fs, rfl, hf⟩

end Ochr.Meaning.DataModel.Proto
