import Ochr.Meaning.Data

/-!
# A data model of the probe programs' declarations (docs/34 §10, §14)

The declarations are written as the checker records them: in a field's type the parameters are
`var 0 …` (the last parameter innermost) and the fields `var np …` (the last field innermost),
as `Machine.fieldTele` binds them (the fields first, then the parameters). `H`'s recursive field
type is abbreviated (`H(f)` for `H(λ(x : Word) : Type => f(Succ(x)))`: only its name matters here).

The declarations of `DataModel/Probes.lean` (and the library's `Word`, `Bool`, `List`), each with
the record its type keeps (`*R`, `*Rec`), and the record at given parameters (`progRecOf`): a
concrete `DataModel` (`dmP`), on which the concrete runs and memberships of
`DataModel/Examples.lean`, `Regress/DataCodes.lean` and `Regress/CodeRuns.lean` are built.

Records are in the layout of docs/34 §18 (`DataLib/Universal.lean`): a record is a function of
paths, and the signature is the universal one (`uSig`), which reads a field's shape off the record
at the field's key (`kindKey`: the earlier fields read small, projected to the constructor's index
fields); a data field's record is the CONTINUATION past the key (`contStep`), so a recursive
declaration's record continues into itself (`listR`'s tail) and a nested one's into the record of
the former it nests in (`roseR`'s forest, `forestR`, which is `List`'s record at `Rose(A)`:
`forestR_eq`). A record keeps what the declaration's field types read of the parameters: a type
parameter's entry at `paramKey` (its record past `paramContStep`), a level-0 value parameter read
small there, and for a parameter above level 0 nothing but the propositions and codes the field
types compute from it (`teqRec`: the truth of `a = b`; `hRec`: the codes `f(0), f(1), …` along
the unfolding). The records are written by hand here; that they are the reference run's reading of
the declared field types is faithfulness (`Faithful.lean`), the existence statement's obligation.
-/

namespace Ochr.Meaning.DataModel.Program

open Ochr Ochr.Meaning Ochr.Meaning.DataLib

def h (n : String) : Hint := ⟨n⟩

def wordD : IndDecl := { name := "Word", ctors := [("Zero", []), ("Succ", [("pred", .tind "Word" [])])] }
def boolD : IndDecl := { name := "Bool", ctors := [("false", []), ("true", [])] }
def listD : IndDecl :=
  { name := "List", params := [(h "A", .sort 1)],
    ctors := [("Nil", []), ("Cons", [("h", .place (.var 0)), ("t", .tind "List" [.place (.var 0)])])] }
def roseD : IndDecl :=
  { name := "Rose", params := [(h "A", .sort 1)],
    ctors := [("Node", [("a", .place (.var 0)), ("kids", .tind "List" [.tind "Rose" [.place (.var 0)]])])] }
def singleD : IndDecl :=
  { name := "Single", params := [(h "A", .sort 1), (h "a", .place (.var 0))],
    ctors := [("MkS", [("x", .place (.var 1)), ("e", .eq (.place (.var 1)) (.place (.var 3)) (.place (.var 0)))])] }
def teqD : IndDecl :=
  { name := "TEq", params := [(h "U", .sort 2), (h "a", .place (.var 0)), (h "b", .place (.var 1))],
    ctors := [("MkTEq", [("h", .eq (.place (.var 2)) (.place (.var 1)) (.place (.var 0)))])] }
def bwD : IndDecl :=
  { name := "BW", ctors := [("MkBW", [("b", .tind "Bool" []), ("x", .call (.const "BF") [.place (.var 1)] false)])] }
def bhD : IndDecl :=
  { name := "BH", ctors := [("MkBH", [("b", .tind "Bool" []), ("x", .call (.const "BG") [.place (.var 1)] false)])] }
def vecD : IndDecl :=
  { name := "VecF", params := [(h "A", .sort 1), (h "n", .tind "Word" [])],
    ctors := [("VNil", [("h", .eq (.tind "Word" []) (.place (.var 0)) (.ctor "Word" 0 (h "") [] []))]),
      ("VCons", [("m", .tind "Word" []), ("x", .place (.var 1)), ("xs", .tind "VecF" [.place (.var 1), .place (.var 5)]),
        ("h", .eq (.tind "Word" []) (.place (.var 0)) (.ctor "Word" 1 (h "") [] [.place (.var 5)]))])] }
def isZD : IndDecl :=
  { name := "IsZ", params := [(h "n", .tind "Word" [])], sort := 0,
    ctors := [("MkZ", [("h", .eq (.tind "Word" []) (.place (.var 0)) (.ctor "Word" 0 (h "") [] []))])] }
def fin1D : IndDecl :=
  { name := "Fin1", params := [(h "n", .nat)], ctors := [("Only", [("h", .eq .nat (.place (.var 0)) (.succ .zero))])] }
def vD : IndDecl :=
  { name := "V", ctors := [("MkV", [("n", .nat), ("x", .tind "Fin1" [.place (.var 1)])])] }

def reD : IndDecl :=
  { name := "RE", params := [(h "A", .sort 1)],
    ctors := [("MkRE", [("xs", .tind "List" [.place (.var 0)]),
      ("v", .eq (.tind "Word" []) (.call (.const "LenL") [.place (.var 0), .place (.var 2)] false) (.ctor "Word" 1 (h "") [] [.ctor "Word" 0 (h "") [] []]))])] }
def hD : IndDecl :=
  { name := "H", params := [(h "f", .pi [h "x"] [.tind "Word" []] (.sort 1))],
    ctors := [("HB", []), ("HS", [("y", .call (.const "App0") [.place (.var 0)] false),
      ("r", .tind "H" [.place (.var 0)])])] }
def mmD : IndDecl :=
  { name := "MM", params := [(h "G", .pi [h "X"] [.sort 1] (.tind "Word" []))],
    ctors := [("MkMM", [("y", .call (.const "MG") [.place (.var 0)] false)])] }
def fpD : IndDecl :=
  { name := "FP", params := [(h "f", .pi [h "x"] [.tind "Word" []] (.tind "Word" []))],
    ctors := [("MkFP", [("y", .tind "Word" []), ("e", .eq (.tind "Word" []) (.call (.place (.var 0)) [.place (.var 2)] false) (.place (.var 2)))])] }

/-- The program's declarations. -/
def progDecls : List IndDecl :=
  [wordD, boolD, listD, roseD, singleD, teqD, bwD, bhD, vecD, isZD, fin1D, vD, reD, hD, mmD, fpD]

/-! ## Records (docs/34 §18: functions of paths)

At a field's key `[(c, i, es)]` (`kindKey`, `es` the earlier fields read small, at non-index fields
`.other`): the field type's entry; past `(c, i, es ++ [.proof])` (`contStep`): its data type's
record. At `paramKey j = [(j, 0, [.other])]`: parameter `j`'s entry; past `paramContStep j`
`= (j, 0, [.other, .other])`: its data type's record. -/

/-- A type's entry in a record: a data type's declaration (its record is the continuation,
`recOfTy`), a leaf's code. A type of level 1 has none (no field is of such a type, (I6)). -/
def entryOf : TyM → Entry
  | .t0 _ (.data d _ _) => .data d
  | .t0 A c => .leaf A c
  | _ => .none

/-- A data type's record: what a record holds past the type's key. -/
def recOfTy : TyM → Rec
  | .t0 _ (.data _ r _) => r
  | _ => natRec

/-- An entry's shape, its record (a data entry's) the continuation `r`: what `uShape` reads. -/
def shapeOf (e : Entry) (r : Rec) : Shape :=
  match e with
  | .leaf B c => .leaf B c
  | .data d => if d.sort == 0 then .prf d r else .sub d r
  | _ => .leaf PEmpty .err

theorem uShape_shapeOf (d : IndDecl) (r : Rec) (c i : Nat) (es : List Small) :
    uShape d r c i es = shapeOf (r (kindKey c i (projIdx d c es))) (contRec r (contStep c i (projIdx d c es))) := by
  unfold uShape shapeOf
  generalize r (kindKey c i (projIdx d c es)) = e
  cases e <;> rfl

def constRec (x : Entry) : Rec := fun _ => x
def propEntry (P : Prop) : Entry := .leaf (PLift P) (.prop P)

/-- The small reading of `Zero` and `Succ(m)`. -/
def zeroS : Small := .node 0 []
def succS (m : Small) : Small := .node 1 [m]

/-- `Word`: `pred` is `Word` again, at `Word`'s record. -/
def wordR : Rec
  | [(1, 0, [])] => .data wordD
  | (1, 0, [.proof]) :: q => wordR q
  | _ => .none

/-- `Bool`: no fields. -/
def boolR : Rec := constRec .none

/-- `List(A)`: `A`'s entry and record (`eA`, `rA`) at `paramKey 0` and at the field `h`; the tail's
record is `List(A)`'s own. -/
def listR (eA : Entry) (rA : Rec) : Rec
  | [(0, 0, [.other])] => eA
  | (0, 0, [.other, .other]) :: q => rA q
  | [(1, 0, [])] => eA
  | (1, 0, [.proof]) :: q => rA q
  | [(1, 1, [_])] => .data listD
  | (1, 1, [_, .proof]) :: q => listR eA rA q
  | _ => .none

mutual
/-- `Rose(A)`: `A`'s entry and record; the forest `kids : List(Rose(A))` at `forestR`. -/
def roseR (eA : Entry) (rA : Rec) : Rec
  | [(0, 0, [.other])] => eA
  | (0, 0, [.other, .other]) :: q => rA q
  | [(0, 0, [])] => eA
  | (0, 0, [.proof]) :: q => rA q
  | [(0, 1, [_])] => .data listD
  | (0, 1, [_, .proof]) :: q => forestR eA rA q
  | _ => .none
/-- `List(Rose(A))`'s record (`listR (.data roseD) (roseR eA rA)`, `forestR_eq`), written so that
the two recursions are structural. -/
def forestR (eA : Entry) (rA : Rec) : Rec
  | [(0, 0, [.other])] => .data roseD
  | (0, 0, [.other, .other]) :: q => roseR eA rA q
  | [(1, 0, [])] => .data roseD
  | (1, 0, [.proof]) :: q => roseR eA rA q
  | [(1, 1, [_])] => .data listD
  | (1, 1, [_, .proof]) :: q => forestR eA rA q
  | _ => .none
end

/-- **The forest's record is `List`'s at `Rose(A)`**: what the run gives `List(Rose(A))` (`List`'s
record at the parameter `Rose(A)`) is the continuation `Rose`'s record holds past `kids`. -/
theorem forestR_eq (eA : Entry) (rA : Rec) : forestR eA rA = listR (.data roseD) (roseR eA rA) := by
  funext p
  induction p with
  | nil => rfl
  | cons s q ih =>
    rw [forestR.eq_def, listR.eq_def]
    split <;> (try split) <;> simp_all

/-- `Single(A, a)`: `A`'s entry and record; `a` read small at its `paramKey`; the field `x : A`;
the equation `e : x = a`, keyed by `x` read small (`x` is an index field). -/
def singleRec (eA : Entry) (rA : Rec) (sa : Small) : Rec
  | [(0, 0, [.other])] => eA
  | (0, 0, [.other, .other]) :: q => rA q
  | [(1, 0, [.other])] => .small sa
  | [(0, 0, [])] => eA
  | (0, 0, [.proof]) :: q => rA q
  | [(0, 1, [sx])] => propEntry (sx = sa)
  | _ => .none

/-- `TEq(U, a, b)`: only the truth of `a = b` (`U`, of level 2, is not kept; nor are `a`, `b`, of a
level-1 type). -/
def teqRec (P : Prop) : Rec
  | [(0, 0, [])] => propEntry P
  | _ => .none

/-- `VecF(A, n)`: `A`'s entry and record; `n` read small at its `paramKey`; `VNil`'s equation on
`n`; `VCons(m, x, xs, h)`: `m : Word`, `x : A`, `xs : VecF(A, m)` (the record at `m`, read small:
`m` is an index field) and the equation `n = Succ(m)`. -/
def vecRec (eA : Entry) (rA : Rec) (sn : Small) : Rec
  | [(0, 0, [.other])] => eA
  | (0, 0, [.other, .other]) :: q => rA q
  | [(1, 0, [.other])] => .small sn
  | [(0, 0, [])] => propEntry (sn = zeroS)
  | [(1, 0, [])] => .data wordD
  | (1, 0, [.proof]) :: q => wordR q
  | [(1, 1, [_])] => eA
  | (1, 1, [_, .proof]) :: q => rA q
  | [(1, 2, [_, _])] => .data vecD
  | (1, 2, [sm, _, .proof]) :: q => vecRec eA rA sm q
  | [(1, 3, [sm, _, _])] => propEntry (sn = succS sm)
  | _ => .none

/-- `IsZ(n)` and `Fin1(n)`: `n` read small at its `paramKey`; the equation. -/
def isZRec (sn : Small) : Rec
  | [(0, 0, [.other])] => .small sn
  | [(0, 0, [])] => propEntry (sn = zeroS)
  | _ => .none
def fin1Rec (sn : Small) : Rec
  | [(0, 0, [.other])] => .small sn
  | [(0, 0, [])] => propEntry (sn = .el Nat 1)
  | _ => .none

/-- `Π(n : Nat). Nat`'s code (a function in a field, a leaf). -/
abbrev NatFn : Type := (n : Nat) → Nat × PUnit
def tNatFn : Tel Code0 PUnit NatFn := .param PUnit false Nat .nat (fun _ => Nat × PUnit) fun _ => .dat PUnit Nat .nat

/-- `BF(b)` and `BG(b)` (`DataModel/Probes.lean`), as the field types they compute (entries). -/
def bfEntry : Small → Entry
  | .node 0 [] => .leaf Nat .nat
  | .node 1 [] => .leaf Unit .unit
  | _ => .none

def bgEntry : Small → Entry
  | .node 0 [] => .leaf Nat .nat
  | .node 1 [] => .leaf NatFn (.pi NatFn tNatFn)
  | _ => .none

/-- `BW := MkBW(b : Bool, x : BF(b))`, `BH := MkBH(b : Bool, x : BG(b))`: `b`'s declaration and
record; `x`'s type at `b` read small (an index field). -/
def bwR : Rec
  | [(0, 0, [])] => .data boolD
  | (0, 0, [.proof]) :: q => boolR q
  | [(0, 1, [sb])] => bfEntry sb
  | _ => .none
def bhR : Rec
  | [(0, 0, [])] => .data boolD
  | (0, 0, [.proof]) :: q => boolR q
  | [(0, 1, [sb])] => bgEntry sb
  | _ => .none

/-- `V := MkV(n : Nat, x : Fin1(n))`: `x`'s record at `n` read small. -/
def vR : Rec
  | [(0, 0, [])] => .leaf Nat .nat
  | [(0, 1, [_])] => .data fin1D
  | (0, 1, [sn, .proof]) :: q => fin1Rec sn q
  | _ => .none

/-- `LenL` read off a list's small reading: what `RE`'s record keys its equation by. -/
def lenS : Small → Nat
  | .node 1 [_, t] => lenS t + 1
  | _ => 0

/-- `RE(A)`: `A`'s entry and record; `xs : List(A)` (`List`'s record at `A`); the equation
`LenL(A, xs) = Succ(Zero)`, keyed by `xs` read small (an index field). -/
def reRec (eA : Entry) (rA : Rec) : Rec
  | [(0, 0, [.other])] => eA
  | (0, 0, [.other, .other]) :: q => rA q
  | [(0, 0, [])] => .data listD
  | (0, 0, [.proof]) :: q => listR eA rA q
  | [(0, 1, [sxs])] => propEntry (lenS sxs = 1)
  | _ => .none

/-- `H(f)`: the codes `App0` gives along the unfolding, `f(0), f(1), …` (entries `g k`, records
`gr k`; `f`, of level 1, is not kept). The child `r : H(λx. f(Succ(x)))`'s record is the
continuation, the parent's shifted by one (`shiftRec`, `Adversarial.shift_hRec`). -/
def hRec (g : Nat → Entry) (gr : Nat → Rec) : Rec
  | [(1, 0, [])] => g 0
  | (1, 0, [.proof]) :: q => gr 0 q
  | [(1, 1, [_])] => .data hD
  | (1, 1, [_, .proof]) :: q => hRec (fun k => g (k + 1)) (fun k => gr (k + 1)) q
  | _ => .none

/-- The record of `H`'s recursive field `r`: the continuation past it. -/
def shiftRec (r : Rec) : Rec := contRec r (contStep 1 1 [.other])

/-- `MM(G)`: the code `MG(G)` gives (`G(Word)` matched), its entry and record; `FP(f)`: `y : Word`
and the equation `f(y) = y`, keyed by `y` read small (an index field). -/
def mmRec (e : Entry) (re : Rec) : Rec
  | [(0, 0, [])] => e
  | (0, 0, [.proof]) :: q => re q
  | _ => .none
def fpRec (P : Small → Prop) : Rec
  | [(0, 0, [])] => .data wordD
  | (0, 0, [.proof]) :: q => wordR q
  | [(0, 1, [sy])] => propEntry (P sy)
  | _ => .none

/-! ## The model -/

/-- The signature is the universal one (`uSig`, docs/34 §18): every model's. -/
abbrev S : Sig := uSig

/-- A type parameter's entry and record (a type used as a value). -/
def tyEntry : Sem → Entry
  | .ty T => entryOf T
  | _ => .none
def tyRec : Sem → Rec
  | .ty T => recOfTy T
  | _ => natRec

/-- **The record at parameters**, for the declarations whose parameters are at level 0 (the
records of `H`, `MM`, `FP` are written at their instances in `Adversarial.lean`: their parameters
are functions, which the record keeps only through what the field types compute from them). -/
def progRecOf (d : IndDecl) (ps : List Sem) : Rec :=
  match d.name, ps with
  | "Word", [] => wordR
  | "List", [A] => listR (tyEntry A) (tyRec A)
  | "Rose", [A] => roseR (tyEntry A) (tyRec A)
  | "Single", [A, a] => singleRec (tyEntry A) (tyRec A) a.small
  | "TEq", [_, a, b] => teqRec (a = b)
  | "BW", [] => bwR
  | "BH", [] => bhR
  | "VecF", [A, n] => vecRec (tyEntry A) (tyRec A) n.small
  | "IsZ", [n] => isZRec n.small
  | "Fin1", [n] => fin1Rec n.small
  | "V", [] => vR
  | "RE", [A] => reRec (tyEntry A) (tyRec A)
  | _, _ => constRec .none

/-- **The probe programs' data model.** Parameter types are not needed by the runs here. -/
def dmP : DataModel where
  covers d := d ∈ progDecls
  recOf := progRecOf
  paramTy _ _ _ := TyM.univ 1

/-- A constructor value is a member when its fields fit (`mem_iff`, right to left). -/
theorem mem_intro (d : IndDecl) (r : Rec) (c : Fin d.ctors.length) (fs : List Sem)
    (hf : FitsM S d r c 0 (arity d c) [] fs) : dmP.Mem d r (.dat d.name r c fs) :=
  (mem_iff S d r _).2 ⟨c, fs, rfl, hf⟩

/-- A record none of whose leaf entries holds a data code: every field shape at it is `LeafOk`
(`ctorR_mem`'s side condition). -/
theorem recLeafOk_of (dm : DataModel) (d : IndDecl) (r : Rec)
    (h : ∀ (p : List RStep) (B : Type) (c : Code0 B), r p = .leaf B c → c.dataCode? = none) :
    dm.RecLeafOk d r := by
  intro c i e
  show dm.LeafOk (uShape d r c i e)
  unfold uShape
  split
  · split <;> trivial
  · rename_i B cd hk
    intro d' r' hc
    rw [h _ B cd hk] at hc
    cases hc
  · intro d' r' hc
    cases hc

end Ochr.Meaning.DataModel.Program

