import Ochr.Meaning.Regress.CodeRuns
import Ochr.Meaning.DataModel.Program

/-!
# Parameters the checker solves from a field's type (docs/34 §14.1 item 7, §17.5; kernel-checked)

The design point of the port: a data type's code keeps a record, not its parameters, so the run's
constructor clause (`unifyTyS`) reads a parameter back off a field's type only where the record
keeps it: at `paramKey`, a level-0 type parameter's entry, and (Handoff 3b) a value parameter of a
level-0 type read small, which the run rebuilds (`ofSmall`) into a parameter giving the same
record (records read value parameters only small, `RecordsFaithful.smallOnly`). The checker
(`Machine.unifyParams`) reads the parameter list of the field's type, so it also solves a parameter
above level 0.

**The suite and the case studies.** Traced (a temporary trace in `Machine.evalCtor`, not kept)
over every example and case study as the build elaborates it, and over `lake exe tests` as far as
`Quicksort.ScanLeft`: every constructor evaluated with no parameters written and no hint naming
the type, and solved from its fields, has only type parameters, read either as a field's own type (`Opt.Some(x)`,
`Pair.Mk(a, b)`, `List.Cons(h, t)`, `Box.MkBox(x)`) or as a direct argument of a field's type
(`ArrayOf.MkArray(s : SliceOf(R))`, `Cell.MkC(h, t : SliceOf(R))`, `GBucket.GCons(…, t :
GBucket(V))`). The model reads both (`cell_solves` is the pattern).

**Constructed programs** (`DataModel/Probes.lean`, `DMProbeSolve`, all accepted, asserted by the
build): `SW` (`let w = MkW(t)`, `t : Tag(3)`: `Wrap`'s value parameter `n` from `Tag(n)`), `SO`
(`let w = A2(t)`: `Opt2`'s `n` from `Tag(n)`, where `Opt2`'s record depends on `n` through its other
constructor's equation) and `SH` (`let w = MkHW(t)`, `t : HL(F0)`: `HW`'s parameter, a function into
`Type₀`, from `HL(f)`). `SW` and `SO` now run to the checker's answer (`sw_ctor`, `so_ctor`: the
tree at `Wrap(3)`'s and `Opt2(3)`'s record and type; before 3b both failed, `Tag(3)` and `Tag(4)`
being one type). `SH` still fails (`sh_fails`): a parameter above level 0 has no small reading, so
the checker's inference there is outside the model, and the residual rule (docs/34 §17.5) excludes it.
-/

namespace Ochr.Meaning.DataModel.ParamSolve

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Regress.CodeRuns
open Ochr.Meaning.DataModel.Program (constRec propEntry tyEntry tyRec)

def hn (n : String) : Hint := ⟨n⟩

/-! ## The declarations, as the checker records them -/

def slD : IndDecl := { name := "Sl", params := [(hn "R", .sort 1)], ctors := [("MkSl", [("c", .place (.var 0))])] }
def cellD : IndDecl :=
  { name := "CellT", params := [(hn "R", .sort 1)], ctors := [("MkCT", [("h", .nat), ("t", .tind "Sl" [.place (.var 0)])])] }
def tagD : IndDecl := { name := "Tag", params := [(hn "n", .nat)], ctors := [("MkTag", [("x", .nat)])] }
def wrapD : IndDecl := { name := "Wrap", params := [(hn "n", .nat)], ctors := [("MkW", [("t", .tind "Tag" [.place (.var 0)])])] }
def hlD : IndDecl := { name := "HL", params := [(hn "f", .pi [hn "x"] [.nat] (.sort 1))], ctors := [("MkHL", [("y", .nat)])] }
def hwD : IndDecl :=
  { name := "HW", params := [(hn "f", .pi [hn "x"] [.nat] (.sort 1))], ctors := [("MkHW", [("t", .tind "HL" [.place (.var 0)])])] }
def opt2D : IndDecl :=
  { name := "Opt2", params := [(hn "n", .nat)],
    ctors := [("A2", [("t", .tind "Tag" [.place (.var 0)])]), ("B2", [("h", .eq .nat (.place (.var 0)) (.succ (.succ (.succ .zero))))])] }

def ΓS : List IndDecl := [slD, cellD, tagD, wrapD, hlD, hwD, opt2D]

/-! ## Their data model: canonical records (docs/34 §18: functions of paths)

Each declaration's record keeps its fields' types at their keys (`kindKey`; a data field's record
the continuation past it, `contStep`) and, at `paramKey`, a type parameter's entry (its record past
`paramContStep`) or a level-0 value parameter read small. -/

/-- `Sl(R)`: `R`'s entry and record, at `paramKey 0` and at the field `c`. -/
def slRec (eR : Entry) (rR : Rec) : Rec
  | [(0, 0, [.other])] => eR
  | (0, 0, [.other, .other]) :: q => rR q
  | [(0, 0, [])] => eR
  | (0, 0, [.proof]) :: q => rR q
  | _ => .none

/-- `CellT(R)`: `R`'s entry and record; `h : Nat`; `t : Sl(R)`. -/
def cellRec (eR : Entry) (rR : Rec) : Rec
  | [(0, 0, [.other])] => eR
  | (0, 0, [.other, .other]) :: q => rR q
  | [(0, 0, [])] => .leaf Nat .nat
  | [(0, 1, [_])] => .data slD
  | (0, 1, [_, .proof]) :: q => slRec eR rR q
  | _ => .none

/-- `Tag(n)`: `n` read small at its `paramKey` (its field reads nothing of `n`); `x : Nat`. -/
def tagRec (sn : Small) : Rec
  | [(0, 0, [.other])] => .small sn
  | [(0, 0, [])] => .leaf Nat .nat
  | _ => .none

/-- `Wrap(n)`: `n` read small at its `paramKey`; `t : Tag(n)`, `Tag`'s record at `n`. -/
def wrapRec (sn : Small) : Rec
  | [(0, 0, [.other])] => .small sn
  | [(0, 0, [])] => .data tagD
  | (0, 0, [.proof]) :: q => tagRec sn q
  | _ => .none

/-- `HL(f)`, `HW(f)`: `f`, a function into `Type₀` (above level 0), is not kept. -/
def hlRec : Rec
  | [(0, 0, [])] => .leaf Nat .nat
  | _ => .none
def hwRec : Rec
  | [(0, 0, [])] => .data hlD
  | (0, 0, [.proof]) :: q => hlRec q
  | _ => .none

/-- `Opt2(n)`: `n` read small at its `paramKey`; `A2`'s `t : Tag(n)`; `B2`'s equation `n = 3`. -/
def opt2Rec (sn : Small) : Rec
  | [(0, 0, [.other])] => .small sn
  | [(0, 0, [])] => .data tagD
  | (0, 0, [.proof]) :: q => tagRec sn q
  | [(1, 0, [])] => propEntry (sn = Small.el Nat 3)
  | _ => .none

/-- The record at parameters: a type parameter's entry; a level-0 value parameter read small at
its `paramKey`; `Opt2`'s equation at `n`, read small. `HL`'s and `HW`'s parameter, a function into
`Type₀` (above level 0), is not kept. -/
def solveRecOf (d : IndDecl) (ps : List Sem) : Rec :=
  match d.name, ps with
  | "Sl", [A] => slRec (tyEntry A) (tyRec A)
  | "CellT", [A] => cellRec (tyEntry A) (tyRec A)
  | "Tag", [n] => tagRec n.small
  | "Wrap", [n] => wrapRec n.small
  | "HL", [_] => hlRec
  | "HW", [_] => hwRec
  | "Opt2", [n] => opt2Rec n.small
  | _, _ => constRec .none

def dmS : DataModel where
  covers d := d ∈ ΓS
  recOf := solveRecOf
  paramTy _ _ _ := TyM.univ 1

/-! ## What a field's type gives back -/

/-- **The suite's pattern**: `CellT`'s `R` is read back off `t : Sl(R)`, from `Sl`'s record. -/
theorem cell_solves :
    unifyTyS dmS 1 (.tind "Sl" [.place (.var 0)]) (.plain (dmS.tyM slD [.ty TyM.nat])) [none] = [some (.ty TyM.nat)] := rfl

/-- **A type parameter nested in a field's type is read back** (the lead's 3a: `unifyTyS` recurses
through the records' entries): `MkGrid(v)` with `v : List(List(Nat))` solves `A := Nat` from
`List(List(A))`. -/
theorem nested_solves :
    unifyTyS Program.dmP 1 (.tind "List" [.tind "List" [.place (.var 0)]])
      (.plain (Program.dmP.tyM Program.listD [.ty (Program.dmP.tyM Program.listD [.ty TyM.nat])])) [none]
      = [some (.ty TyM.nat)] := rfl

/-- **`Wrap`'s `n` is read back off `t : Tag(n)`** (Handoff 3b): `Tag`'s record keeps `n` read
small, and the run solves `n` to the meaning rebuilt from it. -/
theorem wrap_solves (n : Sem) :
    unifyTyS dmS 1 (.tind "Tag" [.place (.var 0)]) (.plain (dmS.tyM tagD [n])) [none] = [some (ofSmall n.small)] := rfl

/-- `HW`'s `f` is not read back off `t : HL(f)`. -/
theorem hw_unsolved (f : Sem) :
    unifyTyS dmS 1 (.tind "HL" [.place (.var 0)]) (.plain (dmS.tyM hlD [f])) [none] = [none] := rfl

/-- **The rebuilt parameter gives the record the written one does**, at the declarations with a
value parameter: their records read it only small (`small_ofSmall`). So `Opt2`'s record, which its
field `Tag(n)` did not determine before (its equation `n = 3` is not read by `Tag`), is read back. -/
theorem recOf_ofSmall (n : Sem) : ∀ d ∈ [tagD, wrapD, opt2D], dmS.recOf d [ofSmall n.small] = dmS.recOf d [n] := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · show tagRec (ofSmall n.small).small = tagRec n.small; rw [small_ofSmall]
  · show wrapRec (ofSmall n.small).small = wrapRec n.small; rw [small_ofSmall]
  · show opt2Rec (ofSmall n.small).small = opt2Rec n.small; rw [small_ofSmall]

/-- `Tag(3)` and `Tag(4)` are now different types: `Tag` is injective in its value parameter. -/
theorem tag_injective : dmS.tyM tagD [.el0 Nat 3] ≠ dmS.tyM tagD [.el0 Nat 4] := by
  intro h
  have h1 : some (tagD.name, dmS.recOf tagD [.el0 Nat 3]) = some (tagD.name, dmS.recOf tagD [.el0 Nat 4]) :=
    congrArg TyM.dataRec? h
  have h2 := congrFun (Prod.mk.inj (Option.some.inj h1)).2 (paramKey 0)
  simp [dmS, solveRecOf, tagD, tagRec, paramKey, Sem.small] at h2

/-! ## The runs -/

section
variable (ρ : Assignment) (φ : Future)

/-- **A one-field constructor with one unwritten parameter and no hint fails** when the field's
type does not give the parameter back: no record is known before the fields, the field runs at
`err`, `unifyTyS` leaves the parameter unsolved, and the clause has no record to build at. -/
theorem ctor1_fails (K : RunCtx) (d : IndDecl) (ty : String) (c : Nat) (x : Hint) (a FT : Term) (s : SState)
    (hd : K.Γ.find? (·.name == ty) = some d) (hfl : K.D.flags (scopeOf s) (.ctor ty c x [] [a]) = (false, false))
    (hp : d.params.length = 1) (hs : (d.sort == 0) = false)
    (hFT : fieldTerm d c 0 = some FT) (hfv : FT.freeVars = [0])
    (hint : TyS) (hh : hint.data = none)
    (v : Sem) (R : TyS) (s' : SState) (ha : runT K ρ φ false (.plain TyM.err) a s = some ((v, R), s'))
    (hu : unifyTyS K.dm 1 FT R [none] = [none]) :
    run K ρ φ hint (.ctor ty c x [] [a]) s = none := by
  have hpe : d.params.isEmpty = false := by
    cases h : d.params with
    | nil => rw [h] at hp; cases hp
    | cons _ _ => rfl
  rw [run, runT]
  simp only [SM.erasedIf, hfl, SM.stmtIf, Bool.false_eq_true, if_false, hd, runParams, bind, pure,
    List.isEmpty_nil, Bool.not_true, Bool.false_or, hpe, hh, hp, List.replicate, Option.bind]
  simp only [runFields, hFT, hfv, hs, Bool.false_and, SM.stmtIf, Bool.false_eq_true, if_false]
  have hne : d.params ≠ [] := fun h => by rw [h] at hp; cases hp
  rw [if_neg (by simp [hp])]
  simp only [SM.stmtIf, Bool.false_eq_true, if_false, Regress.CE4flip.SM.bind_apply, ha, pure, hp, hu]
  simp [ctorOut, SM.fail]

/-- **A one-field constructor with one unwritten parameter and no hint runs** when the field's
type gives the parameter back (`p`): the field runs at `err`, `unifyTyS` solves the parameter, and
the clause builds the tree at the record of the solved parameter. -/
theorem ctor1_runs (K : RunCtx) (d : IndDecl) (ty : String) (c : Nat) (x : Hint) (a FT : Term) (s : SState)
    (hd : K.Γ.find? (·.name == ty) = some d) (hfl : K.D.flags (scopeOf s) (.ctor ty c x [] [a]) = (false, false))
    (hp : d.params.length = 1) (hs : (d.sort == 0) = false)
    (hFT : fieldTerm d c 0 = some FT) (hfv : FT.freeVars = [0])
    (hint : TyS) (hh : hint.data = none)
    (v : Sem) (R : TyS) (s' : SState) (ha : runT K ρ φ false (.plain TyM.err) a s = some ((v, R), s'))
    (p : Sem) (hu : unifyTyS K.dm 1 FT R [none] = [some p]) :
    run K ρ φ hint (.ctor ty c x [] [a]) s =
      some ((DataModel.ctorR d (K.dm.recOf d [p]) c [v], .plain (K.dm.tyR d (K.dm.recOf d [p]))), s') := by
  have hpe : d.params.isEmpty = false := by
    cases h : d.params with
    | nil => rw [h] at hp; cases hp
    | cons _ _ => rfl
  rw [run, runT]
  simp only [SM.erasedIf, hfl, SM.stmtIf, Bool.false_eq_true, if_false, hd, runParams, bind, pure,
    List.isEmpty_nil, Bool.not_true, Bool.false_or, hpe, hh, hp, List.replicate]
  simp only [runFields, hFT, hfv, hs, Bool.false_and, SM.stmtIf, Bool.false_eq_true, if_false]
  rw [if_neg (by simp [hp])]
  simp only [SM.stmtIf, Bool.false_eq_true, if_false, Regress.CE4flip.SM.bind_apply, ha, pure, hp, hu]
  simp [ctorOut, hs, solved, pure]

/-- A frame holding `t` at type `T`. -/
def bindT (T : TyM) (v : Sem) : SBinding := { ty := .plain T, val := fun _ => v, decl := .other }

theorem read_t (G : String → Sem × TyS) (T : TyM) (v : Sem) (hw : v.whole) :
    runT (Kp dmS ΓS G) ρ φ false (.plain TyM.err) (.place (.var 0)) (frame [bindT T v])
      = some ((v, .plain T), frame [bindT T v]) := by
  show readPlace (Kp dmS ΓS G) φ (.var 0) true (frame [bindT T v]) = _
  rw [readPlace_frame φ _ [bindT T v] 0 (bindT T v) (by simp) rfl hw]
  rfl

/-- **`SW` in the model** (Handoff 3b; before it, the run failed): from a frame holding
`t : Tag(3)`, `MkW(t)` with no parameter written and no hint runs to `Wrap(3)`'s tree at `Wrap(3)`'s
type, as the checker's `MkW(t) : Wrap(3)`; and `let w = MkW(t); 0` runs. -/
theorem sw_ctor (G : String → Sem × TyS) (tv : Sem) (hw : tv.whole) :
    run (Kp dmS ΓS G) ρ φ (.plain .err) (.ctor "Wrap" 0 (hn "MkW") [] [.place (.var 0)])
      (frame [bindT (dmS.tyM tagD [.el0 Nat 3]) tv]) =
      some ((dmS.ctorM wrapD [.el0 Nat 3] 0 [tv], .plain (dmS.tyM wrapD [.el0 Nat 3])),
        frame [bindT (dmS.tyM tagD [.el0 Nat 3]) tv]) := by
  rw [ctor1_runs ρ φ _ wrapD "Wrap" 0 _ _ _ _ rfl rfl rfl rfl rfl rfl _ rfl tv _ _ (read_t ρ φ G _ tv hw)
    (ofSmall (Sem.el0 Nat 3).small) (wrap_solves _)]
  rw [show (Kp dmS ΓS G).dm = dmS from rfl, recOf_ofSmall _ wrapD (by simp)]
  rfl

theorem sw_runs (G : String → Sem × TyS) (tv : Sem) (hw : tv.whole) (hint : TyS) :
    (run (Kp dmS ΓS G) ρ φ hint (.letIn (hn "w") (.ctor "Wrap" 0 (hn "MkW") [] [.place (.var 0)]) (num 0))
      (frame [bindT (dmS.tyM tagD [.el0 Nat 3]) tv])).isSome := by
  rw [run_letIn, sw_ctor ρ φ G tv hw]
  simp [bind, Option.bind, run_num]

/-- **`SH` in the model**: from a frame holding `t : HL(F0)`, the run of `let w = MkHW(t); 0` fails,
whatever `F0` means: `HW`'s parameter is a function into `Type₀` (above level 0), which no record
keeps. The checker accepts `SH`; the residual rule (docs/34) excludes it. -/
theorem sh_fails (G : String → Sem × TyS) (f tv : Sem) (hw : tv.whole) (hint : TyS) :
    run (Kp dmS ΓS G) ρ φ hint (.letIn (hn "w") (.ctor "HW" 0 (hn "MkHW") [] [.place (.var 0)]) (num 0))
      (frame [bindT (dmS.tyM hlD [f]) tv]) = none := by
  rw [run_letIn]
  rw [ctor1_fails ρ φ _ hwD "HW" 0 _ _ _ _ rfl rfl rfl rfl rfl rfl _ rfl tv _ _ (read_t ρ φ G _ tv hw) rfl]
  rfl

/-- **`SO` in the model** (before Handoff 3b the run failed, no field determining `Opt2`'s
record): from a frame holding `t : Tag(3)`, `A2(t)` runs to `Opt2(3)`'s tree at `Opt2(3)`'s type,
whose record holds `B2`'s equation `3 = 3`; and `let w = A2(t); 0` runs. -/
theorem so_ctor (G : String → Sem × TyS) (tv : Sem) (hw : tv.whole) :
    run (Kp dmS ΓS G) ρ φ (.plain .err) (.ctor "Opt2" 0 (hn "A2") [] [.place (.var 0)])
      (frame [bindT (dmS.tyM tagD [.el0 Nat 3]) tv]) =
      some ((dmS.ctorM opt2D [.el0 Nat 3] 0 [tv], .plain (dmS.tyM opt2D [.el0 Nat 3])),
        frame [bindT (dmS.tyM tagD [.el0 Nat 3]) tv]) := by
  rw [ctor1_runs ρ φ _ opt2D "Opt2" 0 _ _ _ _ rfl rfl rfl rfl rfl rfl _ rfl tv _ _ (read_t ρ φ G _ tv hw)
    (ofSmall (Sem.el0 Nat 3).small) (wrap_solves _)]
  rw [show (Kp dmS ΓS G).dm = dmS from rfl, recOf_ofSmall _ opt2D (by simp)]
  rfl

theorem so_runs (G : String → Sem × TyS) (tv : Sem) (hw : tv.whole) (hint : TyS) :
    (run (Kp dmS ΓS G) ρ φ hint (.letIn (hn "w") (.ctor "Opt2" 0 (hn "A2") [] [.place (.var 0)]) (num 0))
      (frame [bindT (dmS.tyM tagD [.el0 Nat 3]) tv])).isSome := by
  rw [run_letIn, so_ctor ρ φ G tv hw]
  simp [bind, Option.bind, run_num]

end

end Ochr.Meaning.DataModel.ParamSolve
