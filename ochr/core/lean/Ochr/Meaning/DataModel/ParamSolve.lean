import Ochr.Meaning.Regress.CodeRuns
import Ochr.Meaning.DataModel.Program

/-!
# Parameters the checker solves from a field's type (docs/34 §14.1 item 7; kernel-checked)

The design point of the port: a data type's code keeps a record, not its parameters, so the run's
constructor clause (`unifyTyS`) reads a parameter back off a field's type only where the record
keeps it, a level-0 type parameter's entry at `paramKey`. The checker (`Machine.unifyParams`)
reads the parameter list of the field's type, so it also solves a value or a large parameter.

**The suite and the case studies.** Traced (a temporary trace in `Machine.evalCtor`, not kept)
over every example and case study as the build elaborates it, and over `lake exe tests` as far as
`Quicksort.ScanLeft`: every constructor evaluated with no parameters written and no hint naming
the type, and solved from its fields, has only type parameters, read either as a field's own type (`Opt.Some(x)`,
`Pair.Mk(a, b)`, `List.Cons(h, t)`, `Box.MkBox(x)`) or as a direct argument of a field's type
(`ArrayOf.MkArray(s : SliceOf(R))`, `Cell.MkC(h, t : SliceOf(R))`, `GBucket.GCons(…, t :
GBucket(V))`). The model reads both (`cell_solves` is the pattern). No accepted program in the
suite solves a value or a large parameter from a field.

**Constructed programs that do** (`DataModel/Probes.lean`, `DMProbeSolve`, all accepted, asserted
by the build): `SW` (`let w = MkW(t)`, `t : Tag(3)`: `Wrap`'s value parameter `n` from `Tag(n)`),
`SH` (`let w = MkHW(t)`, `t : HL(F0)`: `HW`'s function parameter from `HL(f)`), `SO`
(`let w = A2(t)`: `Opt2`'s `n` from `Tag(n)`, where `Opt2`'s record depends on `n` through its other
constructor's equation, so the record is not determined by the field at all). On each the model's
run of the constructor FAILS (`sw_fails`, `sh_fails`, `so_fails`): `Tag`'s and `HL`'s records keep
nothing of their parameters (their fields read nothing of them), so the field's type does not
give the parameter back, and with no hint the clause has no record. The checker accepts each, so
`evalCtor_step_stmt` is false at these programs. `SC` (`let c = MkCT(0, s)`, `s : Sl(Nat)`), the
suite's pattern, runs (`cell_solves`).
-/

namespace Ochr.Meaning.DataModel.ParamSolve

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Regress.CodeRuns
open Ochr.Meaning.DataModel.Program (constRec shapeOf propEntry tyEntry)

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

/-! ## Their data model: canonical records -/

/-- The signature: `Sl`'s and `CellT`'s fields read `R`'s entry; `Tag`'s and `HL`'s read nothing of
their parameters; `Opt2`'s `B2` reads the equation `n = 3`. -/
def solveShape (d : IndDecl) (r : Rec) (c i : Nat) (_e : List Small) : Shape :=
  match d.name, c, i with
  | "Sl", 0, 0 => shapeOf (r (paramKey 0))
  | "CellT", 0, 0 => .leaf Nat .nat
  | "CellT", 0, 1 => .sub slD (constRec (r (paramKey 0)))
  | "Tag", 0, 0 => .leaf Nat .nat
  | "Wrap", 0, 0 => .sub tagD (constRec .none)
  | "HL", 0, 0 => .leaf Nat .nat
  | "HW", 0, 0 => .sub hlD (constRec .none)
  | "Opt2", 0, 0 => .sub tagD (constRec .none)
  | "Opt2", 1, 0 => shapeOf (r [(1, 0, [])])
  | _, _, _ => .leaf PEmpty .err

/-- `Opt2(n)`'s record: `B2`'s equation, `n` read small. -/
def opt2Rec (n : Sem) : Rec
  | [(1, 0, [])] => propEntry (n.small = Small.el Nat 3)
  | _ => .none

/-- The record at parameters: a type parameter's entry; `Opt2`'s equation at `n`, read small. -/
def solveRecOf (d : IndDecl) (ps : List Sem) : Rec :=
  match d.name, ps with
  | "Sl", [A] => constRec (tyEntry A)
  | "CellT", [A] => constRec (tyEntry A)
  | "Opt2", [n] => opt2Rec n
  | _, _ => constRec .none

def dmS : DataModel where
  covers d := d ∈ ΓS
  sig := ⟨solveShape⟩
  recOf := solveRecOf
  paramTy _ _ _ := TyM.univ 1

/-! ## What a field's type gives back -/

/-- **The suite's pattern**: `CellT`'s `R` is read back off `t : Sl(R)`, from `Sl`'s record. -/
theorem cell_solves :
    unifyTyS dmS 1 (.tind "Sl" [.place (.var 0)]) (.plain (dmS.tyM slD [.ty TyM.nat])) [none] = [some (.ty TyM.nat)] := rfl

/-- `Wrap`'s `n` is not read back off `t : Tag(n)`, whatever `n` is: `Tag`'s record keeps nothing. -/
theorem wrap_unsolved (n : Sem) :
    unifyTyS dmS 1 (.tind "Tag" [.place (.var 0)]) (.plain (dmS.tyM tagD [n])) [none] = [none] := rfl

/-- `HW`'s `f` is not read back off `t : HL(f)`. -/
theorem hw_unsolved (f : Sem) :
    unifyTyS dmS 1 (.tind "HL" [.place (.var 0)]) (.plain (dmS.tyM hlD [f])) [none] = [none] := rfl

/-- The proposition a `Prop` code is of. -/
def propOfCode : {A : Type} → Code0 A → Prop
  | _, .prop P => P
  | _, _ => True

theorem propEntry_inj {P Q : Prop} (h : propEntry P = propEntry Q) : P = Q := by
  simp only [propEntry, Entry.leaf.injEq] at h
  have key : ∀ (A A' : Type) (a : Code0 A) (a' : Code0 A'), A = A' → HEq a a' → propOfCode a = propOfCode a' := by
    intro A A' a a' hA ha; subst hA; cases ha; rfl
  exact key _ _ _ _ h.1 h.2

/-- `Opt2`'s record depends on `n` (`B2`'s equation), but `A2`'s field `Tag(n)` does not: at `3`
and `4` the field's type is the same and the records differ. -/
theorem opt2_record_not_determined :
    dmS.tyM tagD [.el0 Nat 3] = dmS.tyM tagD [.el0 Nat 4] ∧
      dmS.recOf opt2D [.el0 Nat 3] ≠ dmS.recOf opt2D [.el0 Nat 4] := by
  refine ⟨rfl, fun h => ?_⟩
  have h' : propEntry (Small.el Nat 3 = Small.el Nat 3) = propEntry (Small.el Nat 4 = Small.el Nat 3) :=
    congrFun h [(1, 0, [])]
  have h'' := propEntry_inj h'
  have : Small.el Nat 4 = Small.el Nat 3 := cast h'' rfl
  simp at this

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

/-- A frame holding `t` at type `T`. -/
def bindT (T : TyM) (v : Sem) : SBinding := { ty := .plain T, val := fun _ => v, decl := .other }

theorem read_t (G : String → Sem × TyS) (T : TyM) (v : Sem) (hw : v.whole) :
    runT (Kp dmS ΓS G) ρ φ false (.plain TyM.err) (.place (.var 0)) (frame [bindT T v])
      = some ((v, .plain T), frame [bindT T v]) := by
  show readPlace (Kp dmS ΓS G) φ (.var 0) true (frame [bindT T v]) = _
  rw [readPlace_frame φ _ [bindT T v] 0 (bindT T v) (by simp) rfl hw]
  rfl

/-- **`SW` in the model**: from a frame holding `t : Tag(3)`, the run of `let w = MkW(t); 0` fails,
whatever `t` is; the checker accepts `SW` (`DMProbeSolve`). -/
theorem sw_fails (G : String → Sem × TyS) (tv : Sem) (hw : tv.whole) (hint : TyS) :
    run (Kp dmS ΓS G) ρ φ hint (.letIn (hn "w") (.ctor "Wrap" 0 (hn "MkW") [] [.place (.var 0)]) (num 0))
      (frame [bindT (dmS.tyM tagD [.el0 Nat 3]) tv]) = none := by
  rw [run_letIn]
  rw [ctor1_fails ρ φ _ wrapD "Wrap" 0 _ _ _ _ rfl rfl rfl rfl rfl rfl _ rfl tv _ _ (read_t ρ φ G _ tv hw) rfl]
  rfl

/-- **`SH` in the model**: from a frame holding `t : HL(F0)`, the run of `let w = MkHW(t); 0` fails,
whatever `F0` means; the checker accepts `SH`. -/
theorem sh_fails (G : String → Sem × TyS) (f tv : Sem) (hw : tv.whole) (hint : TyS) :
    run (Kp dmS ΓS G) ρ φ hint (.letIn (hn "w") (.ctor "HW" 0 (hn "MkHW") [] [.place (.var 0)]) (num 0))
      (frame [bindT (dmS.tyM hlD [f]) tv]) = none := by
  rw [run_letIn]
  rw [ctor1_fails ρ φ _ hwD "HW" 0 _ _ _ _ rfl rfl rfl rfl rfl rfl _ rfl tv _ _ (read_t ρ φ G _ tv hw) rfl]
  rfl

/-- **`SO` in the model**: from a frame holding `t : Tag(3)`, the run of `let w = A2(t); 0` fails;
here no field could give the record back (`opt2_record_not_determined`). The checker accepts `SO`. -/
theorem so_fails (G : String → Sem × TyS) (tv : Sem) (hw : tv.whole) (hint : TyS) :
    run (Kp dmS ΓS G) ρ φ hint (.letIn (hn "w") (.ctor "Opt2" 0 (hn "A2") [] [.place (.var 0)]) (num 0))
      (frame [bindT (dmS.tyM tagD [.el0 Nat 3]) tv]) = none := by
  rw [run_letIn]
  rw [ctor1_fails ρ φ _ opt2D "Opt2" 0 _ _ _ _ rfl rfl rfl rfl rfl rfl _ rfl tv _ _ (read_t ρ φ G _ tv hw) rfl]
  rfl

end

end Ochr.Meaning.DataModel.ParamSolve
