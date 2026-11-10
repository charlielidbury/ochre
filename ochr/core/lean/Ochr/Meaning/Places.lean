import Ochr.Meaning.Apply

/-!
# Places on meanings, and the decisions the reference run reads from syntax

## Places

A place `x | *p | p.i | p.g` is followed on a meaning with its type at hand: `*` is the identity
(a borrow's holder means its content, docs/27 Def. 2), `.i` and `.g` project a field of a
constructor value, whose parameters are read off the type (`DataModel.paramsOf`) and whose
field types come from the declaration (`DataModel.fieldTy`). A partly moved value (`Sem.ctor`)
projects like a whole one; `⊥` and `err` have no fields. Updating at a path re-packs with
`DataModel.ctorM`, so a field set to `moved` makes the value an untyped tuple.

## Decisions (docs/18 §"Decisions, by kind", *aligned*)

Some of the checker's decisions change what a step means, and the model must make the same
choice: whether a term is a statement (run on a copy that is thrown away), a Π-type's sort, η at
`Unit` (D80), copy or move on a read (D80), and D84's drop at the join. The checker reads each
from syntax and declared types alone (`Decide.lean`, D77, D80), never from a run, so the
reference run can read the same. `Decisions` is that interface; the step lemmas prove its
fields equal to the checker's functions (`Decide.preFlags`, `piSort`, `etaUnit`/`declCopy`,
`jdMoves`), which is where "aligned" is discharged.
-/

namespace Ochr.Meaning

open Classical

/-- The readings the reference run takes from syntax, exactly as the checker does. `sc` is the
scope of declared-type readings (`Binding.decl`, innermost first), as `Decide.placeDecl` takes
it. -/
structure Decisions : Type where
  /-- Is this term a statement (erased: a type, a proof, a type-returning or proof-returning
  call), and is it a proof (`Decide.preFlags`)? -/
  flags : List DeclInfo → Term → Bool × Bool
  /-- A place's declared-type reading (`Decide.placeDecl`). -/
  placeDecl : List DeclInfo → Place → DeclInfo
  /-- A term's declared-type reading (`Decide.declOf`). -/
  declOf : List DeclInfo → Term → DeclInfo
  /-- Does a reading say "copy" (`Decide.declCopy`, D80)? -/
  copy : DeclInfo → Bool
  /-- The sort of a Π-term (`Machine.piSort` / `Decide.sortOf`): 0 for `Prop`, `l + 1` for `Type_l`. -/
  piSort : List DeclInfo → Term → Nat
  /-- D84: the places a match drops at its join (`Decide.jdMoves`), given the places already
  moved when the match starts (its `entry` argument). -/
  joinMoves : List DeclInfo → List Place → Term → List Place
  /-- D84 [Id-typestate]/[Obs-ref]: the borrow bindings a side re-points (assigns whole and does
  not consume), read from syntax and declared types (`Decide.typeState`'s `repointed`). -/
  rePointed : List DeclInfo → Term → List Place

section
variable (dm : DataModel) (Γ : List IndDecl)

/-- The declaration and parameters of a data type meaning, if it is one in `Γ`. -/
noncomputable def TyM.dataOf (T : TyM) : Option (IndDecl × List Sem) :=
  (Γ.findSome? fun d => (dm.paramsOf d T).map (d, ·))

/-- Field `i` of constructor `c` of a value of the data type `T`, with its type. -/
noncomputable def Sem.stepField (T : TyM) (c i : Nat) (s : Sem) : Option (Sem × TyM) :=
  match s with
  | .proof => some (.proof, .err)
  | _ =>
    match T.dataOf dm Γ with
    | some (d, ps) =>
      match dm.fieldsOf d ps s with
      | some (c', fs) => if c' = c then (fs[i]?).map fun f => (f, dm.fieldTy d ps c i (fs.take i)) else none
      | none => none
    | none => none

/-- One step on a meaning at type `T`: the sub-meaning and its type. -/
noncomputable def Sem.step (T : TyM) : Step → Sem → Option (Sem × TyM)
  | .deref, s => some (s, T)
  | .proj 0, s =>
    if T = .ty0 Nat then
      match s.asNat with
      | some (n + 1) => some (.el0 Nat n, .ty0 Nat)
      | some 0 => none
      | none => match s with
        | .ctor "Nat" 1 [w] => some (w, .ty0 Nat)
        | _ => none
    else Sem.stepField dm Γ T 0 0 s
  | .proj i, s => Sem.stepField dm Γ T 0 i s
  | .field g, s => Sem.stepField dm Γ T g.ctor g.idx s

/-- Follow a path on a meaning at type `T`. -/
noncomputable def Sem.follow (T : TyM) (s : Sem) : List Step → Option (Sem × TyM)
  | [] => some (s, T)
  | st :: sts => (Sem.step dm Γ T st s).bind fun (s', T') => Sem.follow T' s' sts

/-- Update the sub-meaning at a path (re-packing each constructor value on the way, so a field
set to `moved` makes its value an untyped tuple). -/
noncomputable def Sem.updAt (T : TyM) (f : Sem → Sem) : List Step → Sem → Option Sem
  | [], s => some (f s)
  | .deref :: sts, s => Sem.updAt T f sts s
  | st :: sts, s =>
    if T = .ty0 Nat then
      match st, s.asNat with
      | .proj 0, some (n + 1) => (Sem.updAt (.ty0 Nat) f sts (.el0 Nat n)).map Sem.succ
      | _, _ => none
    else
      match T.dataOf dm Γ with
      | some (d, ps) =>
        match dm.fieldsOf d ps s with
        | some (c, fs) =>
          let i := match st with | .proj i => i | .field g => g.idx | .deref => 0
          match fs[i]? with
          | some fi =>
            (Sem.updAt (dm.fieldTy d ps c i (fs.take i)) f sts fi).map fun fi' =>
              dm.ctorM d ps c (fs.set i fi')
          | none => none
        | none => none
      | none => none

end

end Ochr.Meaning
