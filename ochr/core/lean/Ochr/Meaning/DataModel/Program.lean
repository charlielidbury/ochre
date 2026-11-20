import Ochr.Meaning.Data

/-!
# A data model of the probe programs' declarations (docs/34 §10, §14)

The declarations of `DataModel/Probes.lean` (and the library's `Word`, `Bool`, `List`), each with
the record its type keeps (`*Rec`), its fields' shapes (`progShape`), and the record at given
parameters (`progRecOf`): a concrete `DataModel` (`dmP`), on which the concrete runs and
memberships of `DataModel/Examples.lean`, `Regress/DataCodes.lean` and `Regress/CodeRuns.lean` are
built. A record keeps what the declaration's field types read of the parameters: a type
parameter's entry (its code, or its declaration and record, at `paramKey`), a value parameter read
small, and for a parameter above level 0 nothing but the propositions and codes the field types
compute from it (`teqRec`: the truth of `a = b`). The signature is written by hand here; that it
is the reference run's reading of the declared field types is faithfulness (`Faithful.lean`), the
existence statement's obligation.
-/

namespace Ochr.Meaning.DataModel.Program

open Ochr Ochr.Meaning Ochr.Meaning.DataLib

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

def reD : IndDecl :=
  { name := "RE", params := [(h "A", .sort 1)],
    ctors := [("MkRE", [("xs", .tind "List" [.place (.var 0)]),
      ("v", .eq (.tind "Word" []) (.call (.const "LenL") [.place (.var 1), .place (.var 0)] false) (.ctor "Word" 1 (h "") [] [.ctor "Word" 0 (h "") [] []]))])] }
def hD : IndDecl :=
  { name := "H", params := [(h "f", .pi [h "x"] [.tind "Word" []] (.sort 1))],
    ctors := [("HB", []), ("HS", [("y", .call (.const "App0") [.place (.var 0)] false),
      ("r", .tind "H" [.place (.var 1)])])] }
def mmD : IndDecl :=
  { name := "MM", params := [(h "G", .pi [h "X"] [.sort 1] (.tind "Word" []))],
    ctors := [("MkMM", [("y", .call (.const "MG") [.place (.var 0)] false)])] }
def fpD : IndDecl :=
  { name := "FP", params := [(h "f", .pi [h "x"] [.tind "Word" []] (.tind "Word" []))],
    ctors := [("MkFP", [("y", .tind "Word" []), ("e", .eq (.tind "Word" []) (.call (.place (.var 1)) [.place (.var 0)] false) (.place (.var 0)))])] }

/-- The program's declarations. -/
def progDecls : List IndDecl :=
  [wordD, boolD, listD, roseD, singleD, teqD, bwD, bhD, vecD, isZD, fin1D, vD, reD, hD, mmD, fpD]

/-! ## Records -/

/-- A type's entry in a record: a data type's declaration and record, a leaf's code. A type of
level 1 has none (no field is of such a type, (I6)). -/
def entryOf : TyM → Entry
  | .t0 _ (.data d r _) => .data d r
  | .t0 A c => .leaf A c
  | _ => .none

/-- An entry's shape (a `Prop`-sorted declaration's: a proof). -/
def shapeOf : Entry → Shape
  | .leaf B c => .leaf B c
  | .data d r => if d.sort == 0 then .prf d r else .sub d r
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
  | [(0, 0, [])] => propEntry (sn = zeroS)
  | [(1, 3, sm :: _)] => propEntry (sn = succS sm)
  | _ => eA

def isZRec (sn : Small) : Rec := constRec (propEntry (sn = zeroS))
def fin1Rec (sn : Small) : Rec := constRec (propEntry (sn = .el Nat 1))

/-- `LenL` read off a list's small reading: what `RE`'s record keys its equation by. -/
def lenS : Small → Nat
  | .node 1 [_, t] => lenS t + 1
  | _ => 0

/-- `RE(A)`: `A`'s entry; the equation `LenL(A, xs) = Succ(Zero)`, `xs` read small. -/
def reRec (eA : Entry) : Rec
  | [(0, 1, [sxs])] => propEntry (lenS sxs = 1)
  | _ => eA

/-- A key holding a number: position `k` of a sequence a record keeps. -/
def keyN (k : Nat) : List RStep := [(1, 0, [.node k []])]

/-- `H(f)`: the codes `App0` gives along the unfolding, `f(0), f(1), …` (`f`, of level 1, is not
kept); a child's record is the parent's shifted by one (`shiftRec`). -/
def hRec (g : Nat → Entry) : Rec
  | [(1, 0, [.node k []])] => g k
  | _ => .none

def shiftRec (r : Rec) : Rec
  | [(1, 0, [.node k []])] => r (keyN (k + 1))
  | st => r st

/-- `MM(G)`: the code `MG(G)` (`G(Word)` matched); `FP(f)`: the equation `f(y) = y`, `y` read
small. -/
def mmRec (e : Entry) : Rec := constRec e
def fpRec (P : Small → Prop) : Rec
  | [(0, 1, [sy])] => propEntry (P sy)
  | _ => .none

/-- `Π(n : Nat). Nat`'s code (a function in a field, a leaf). -/
abbrev NatFn : Type := (n : Nat) → Nat × PUnit
def tNatFn : Tel Code0 PUnit NatFn := .param PUnit false Nat .nat (fun _ => Nat × PUnit) fun _ => .dat PUnit Nat .nat

/-- `BF(b)` and `BG(b)` (`DataModel/Probes.lean`), as the field types they compute. -/
def bfShape : Small → Shape
  | .node 0 [] => .leaf Nat .nat
  | .node 1 [] => .leaf Unit .unit
  | _ => .leaf PEmpty .err

def bgShape : Small → Shape
  | .node 0 [] => .leaf Nat .nat
  | .node 1 [] => .leaf NatFn (.pi NatFn tNatFn)
  | _ => .leaf PEmpty .err

/-! ## The signature -/

def progShape (d : IndDecl) (r : Rec) (c i : Nat) (e : List Small) : Shape :=
  match d.name, c, i, e with
  | "Word", 1, 0, _ => .sub d r
  | "List", 1, 0, _ => shapeOf (r (paramKey 0))
  | "List", 1, 1, _ => .sub d r
  | "Rose", 0, 0, _ => shapeOf (r (paramKey 0))
  | "Rose", 0, 1, _ => .sub listD (constRec (.data d r))
  | "Single", 0, 0, _ => shapeOf (r (paramKey 0))
  | "Single", 0, 1, e => shapeOf (r [(0, 1, e)])
  | "TEq", 0, 0, _ => shapeOf (r [])
  | "BW", 0, 0, _ => .sub boolD (constRec .none)
  | "BW", 0, 1, [s] => bfShape s
  | "BH", 0, 0, _ => .sub boolD (constRec .none)
  | "BH", 0, 1, [s] => bgShape s
  | "VecF", 0, 0, e => shapeOf (r [(0, 0, e)])
  | "VecF", 1, 0, _ => .sub wordD (constRec .none)
  | "VecF", 1, 1, _ => shapeOf (r (paramKey 0))
  | "VecF", 1, 2, sm :: _ => .sub d (vecRec (r (paramKey 0)) sm)
  | "VecF", 1, 3, e => shapeOf (r [(1, 3, e)])
  | "IsZ", 0, 0, _ => shapeOf (r [])
  | "Fin1", 0, 0, _ => shapeOf (r [])
  | "V", 0, 0, _ => .leaf Nat .nat
  | "V", 0, 1, [s] => .sub fin1D (fin1Rec s)
  | "RE", 0, 0, _ => .sub listD (constRec (r (paramKey 0)))
  | "RE", 0, 1, e => shapeOf (r [(0, 1, e)])
  | "H", 1, 0, _ => shapeOf (r (keyN 0))
  | "H", 1, 1, _ => .sub d (shiftRec r)
  | "MM", 0, 0, _ => shapeOf (r [])
  | "FP", 0, 0, _ => .sub wordD (constRec .none)
  | "FP", 0, 1, e => shapeOf (r [(0, 1, e)])
  | _, _, _, _ => .leaf PEmpty .err

def S : Sig := ⟨progShape⟩

/-- A type parameter's entry (a type used as a value). -/
def tyEntry : Sem → Entry
  | .ty T => entryOf T
  | _ => .none

/-- **The record at parameters**, for the declarations whose parameters are at level 0 (the
records of `H`, `MM`, `FP` are written at their instances in `Adversarial.lean`: their parameters
are functions, which the record keeps only through what the field types compute from them). -/
def progRecOf (d : IndDecl) (ps : List Sem) : Rec :=
  match d.name, ps with
  | "List", [A] => constRec (tyEntry A)
  | "Rose", [A] => constRec (tyEntry A)
  | "Single", [A, a] => singleRec (tyEntry A) a.small
  | "TEq", [_, a, b] => teqRec (a = b)
  | "VecF", [A, n] => vecRec (tyEntry A) n.small
  | "IsZ", [n] => isZRec n.small
  | "Fin1", [n] => fin1Rec n.small
  | "RE", [A] => reRec (tyEntry A)
  | _, _ => constRec .none

/-- **The probe programs' data model.** Parameter types are not needed by the runs here. -/
def dmP : DataModel where
  covers d := d ∈ progDecls
  sig := S
  recOf := progRecOf
  paramTy _ _ _ := TyM.univ 1

/-- A constructor value is a member when its fields fit (`mem_iff`, right to left). -/
theorem mem_intro (d : IndDecl) (r : Rec) (c : Fin d.ctors.length) (fs : List Sem)
    (hf : FitsM S d r c 0 (arity d c) [] fs) : dmP.Mem d r (.dat d.name r c fs) :=
  (mem_iff S d r _).2 ⟨c, fs, rfl, hf⟩

end Ochr.Meaning.DataModel.Program
