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
  /-- The reading of a type term, as a type (`Decide.typeDecl`): what a binding declared at it
  reads (D19, R3: a parameter's reading is its domain term's, `Decide.paramDecls`). -/
  typeDecl : List DeclInfo → Term → DeclInfo

/-- The scope after a telescope of parameter types: each parameter's reading, read in the scope
of the earlier ones, innermost first (`Decide.telescope`). -/
def Decisions.teleDecls (D : Decisions) (sc : List DeclInfo) : List Term → List DeclInfo
  | [] => sc
  | d :: ds => D.teleDecls (D.typeDecl sc d :: sc) ds

/-- The declared readings of a telescope's parameters, in order (`Decide.paramDecls`'s first
component): what a frame binds them at. -/
def Decisions.paramDecls (D : Decisions) (sc : List DeclInfo) (ds : List Term) : List DeclInfo :=
  ((D.teleDecls sc ds).take ds.length).reverse

/-- The declared readings of a function's parameters, in order, and of its codomain, read in the
scope `sc` where the function is formed (`Decide.paramDecls`): what the closure's frame binds its
parameters at, and (`.pi cd`) `self`. -/
def Decisions.fixDecls (D : Decisions) (sc : List DeclInfo) (ds : List Term) (c : Term) : List DeclInfo × DeclInfo :=
  (D.paramDecls sc ds, D.typeDecl (D.teleDecls sc ds) c)

section
variable (dm : DataModel) (Γ : List IndDecl)

/-- The declaration and parameters of a data type meaning, if it is one in `Γ`, chosen by its
CARRIER (classically). Not used to find one's way inside a value: carriers do not determine
declarations (docs/31 D31, `Regress/DataOfChoice_189132fd.lean`); [Rec]'s rank still reads it. -/
noncomputable def TyM.dataOf (T : TyM) : Option (IndDecl × List Sem) :=
  (Γ.findSome? fun d => (dm.paramsOf d T).map (d, ·))

/-- The declaration and parameters a structured type names (docs/31 D31): the declaration of
`Γ` with its data's NAME, at its data's parameters. A value is decoded by this, never by its
carrier. -/
def TyS.dataDecl (T : TyS) : Option (IndDecl × List Sem) :=
  T.data.bind fun (n, ps) => (Γ.find? (·.name == n)).map (·, ps)

/-- The structured type field `i` of constructor `c` of `d` at `ps` is read at, given the earlier
fields: its declared type and data, the hint `Value.meanFields` reads the field at. -/
def fieldHint (d : IndDecl) (ps : List Sem) (c i : Nat) (earlier : List Sem) : TyS :=
  ⟨dm.fieldTy d ps c i earlier, none, none, dm.fieldData d ps c i earlier⟩

/-- Field `i` of constructor `c` of a value of the data type `T`, with its type. -/
noncomputable def Sem.stepField (T : TyS) (c i : Nat) (s : Sem) : Option (Sem × TyS) :=
  match s with
  | .proof => some (.proof, .plain .err)
  | _ =>
    match T.dataDecl Γ with
    | some (d, ps) =>
      match dm.fieldsOf d ps s with
      | some (c', fs) => if c' = c then (fs[i]?).map fun f => (f, fieldHint dm d ps c i (fs.take i)) else none
      | none => none
    | none => none

/-- One step on a meaning at type `T`: the sub-meaning and its type. -/
noncomputable def Sem.step (T : TyS) : Step → Sem → Option (Sem × TyS)
  | .deref, s => some (s, T)
  | .proj 0, s =>
    if T.m = .ty0 Nat then
      match s.asNat with
      | some (n + 1) => some (.el0 Nat n, .plain (.ty0 Nat))
      | some 0 => none
      | none => match s with
        | .ctor "Nat" 1 [w] => some (w, .plain (.ty0 Nat))
        | _ => none
    else Sem.stepField dm Γ T 0 0 s
  | .proj i, s => Sem.stepField dm Γ T 0 i s
  | .field g, s => Sem.stepField dm Γ T g.ctor g.idx s

/-- Follow a path on a meaning at type `T`. -/
noncomputable def Sem.follow (T : TyS) (s : Sem) : List Step → Option (Sem × TyS)
  | [] => some (s, T)
  | st :: sts => (Sem.step dm Γ T st s).bind fun (s', T') => Sem.follow T' s' sts

/-- Update the sub-meaning at a path (re-packing each constructor value on the way, so a field
set to `moved` makes its value an untyped tuple). -/
noncomputable def Sem.updAt (T : TyS) (f : Sem → Sem) : List Step → Sem → Option Sem
  | [], s => some (f s)
  | .deref :: sts, s => Sem.updAt T f sts s
  | st :: sts, s =>
    if T.m = .ty0 Nat then
      match st, s.asNat with
      | .proj 0, some (n + 1) => (Sem.updAt (.plain (.ty0 Nat)) f sts (.el0 Nat n)).map Sem.succ
      | _, _ => none
    else
      match T.dataDecl Γ with
      | some (d, ps) =>
        match dm.fieldsOf d ps s with
        | some (c, fs) =>
          let i := match st with | .proj i => i | .field g => g.idx | .deref => 0
          match fs[i]? with
          | some fi =>
            (Sem.updAt (fieldHint dm d ps c i (fs.take i)) f sts fi).map fun fi' =>
              dm.ctorM d ps c (fs.set i fi')
          | none => none
        | none => none
      | none => none

end

mutual
/-- The places under `q` whose content in the meaning `x` is `moved`: `Machine.botPlaces`, on
meanings. A partly moved constructor value is a tuple (`DataModel.ctorM`) and names its fields as
the checker does (a `FieldRef` is compared without its printing name); a partly moved number is
`S` of its predecessor, the step `.0`. A whole value holds no moved part. -/
def Sem.movedIn : Sem → Place → List Place
  | .moved, q => [q]
  | .ctor t c fs, q => if t = "Nat" then Sem.movedInNat fs q else Sem.movedInFields t c q 0 fs
  | _, _ => []
termination_by structural x => x

def Sem.movedInFields (t : String) (c : Nat) (q : Place) : Nat → List Sem → List Place
  | _, [] => []
  | i, w :: ws => Sem.movedIn w (.field ⟨t, c, i, s!"f{i}"⟩ q) ++ Sem.movedInFields t c q (i + 1) ws
termination_by structural _ ws => ws

def Sem.movedInNat : List Sem → Place → List Place
  | [], _ => []
  | w :: _, q => Sem.movedIn w (.proj 0 q)
termination_by structural ws => ws
end

end Ochr.Meaning
