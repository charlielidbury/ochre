import Ochr.Meaning.DataModel.Exists.PreludeModel
import Ochr.Test

/-!
# The checker's frame for typing a field, pinned (docs/31 D160)

`teleFrame` (`DataModel/Faithful.lean`) is the meaning of the frame the checker's `fieldTele`
(`Machine.lean`) evaluates field `i`'s type in. Since D160 it types the fields not yet bound
(the field being typed among them) `err`, at the value `moved`, read `other`. This file runs the
checker's own `fieldTele` and records, at the moment it has evaluated field `i`'s type and before
it binds field `i`, every binding of the frame it evaluated in. Each `#guard` compares that record
with the expected one, so the build fails if the checker's frame changes.

How each binding corresponds to `teleFrame`'s (`name : type = value [reading]`):
* an earlier field `j < i`: `some T` at the value given (D117: what it stands for, each live loan resolved to its
  borrow's content, `resolveLoans`, as `fieldTypesOf` binds it), `T` the field's type the checker computed
  (`dm.fieldTy … j (e.take j)`), read `prop` exactly when `fieldTermIsProp` says so
  (`fieldProof`), `other` else;
* the field being typed and every later one: no type, value `⊥`, read `other` (`err`, `moved`,
  `other`);
* then the parameters: each at its declared type evaluated at the earlier ones (`dm.paramTy`), at
  its value, read as its declared type term is (`paramDecls`).

The only difference from `teleFrame` the record shows is the frame count: the checker pushes this
frame above the one `checkInd` binds the parameters in (`snap` binds them there too), while
`teleFrame` is one frame. It predates D160, and D160 does not change it; whether anything the run
of a field type does can see the frame below is for the simulation of the checker to settle, not
this guard.

The declarations: `V := MkV(n : Nat, x : Fin1(n))` (a dependent field) and
`Three (A : Type) := MkThree(a : A, e : Eq(Nat, 0, 0), b : Nat)` (three fields, a parameter, and a
proof field followed by another field). Both accepted.
-/

namespace Ochr.Meaning.DataModel.Exists.TeleFrameGuard

open Ochr Ochr.Test

ochr TeleG {
  inductive Fin1 (n : Nat) := MkFin1
  inductive V := MkV(n : Nat, x : Fin1(n))
  inductive Three (A : Type) := MkThree(a : A, e : Eq(Nat, 0, 0), b : Nat)
}

-- all three are accepted
#guard (Ochr.Test.run "TeleG" TeleG).rejectedWith []

/-- The block's items, after the library's. -/
def items : List Item :=
  (Prelude.decls ++ TeleG.decls).filterMap fun d => match Surface.resolveProgram (Prelude.decls ++ TeleG.decls) d with
    | .ok it => some it
    | .error _ => none

/-- The checker's globals and inductive declarations after the library and the block. -/
def sigma : List GDef × List IndDecl := globalsAfter {} items

def declNamed (n : String) : IndDecl := (sigma.2.find? (·.name == n)).getD default

def showDecl : DeclInfo → String
  | .prop => "prop"
  | .other => "other"
  | .sort l => s!"sort {l}"
  | _ => "another reading"

def showB (b : Binding) : String :=
  s!"{b.hint.name} : {match b.ty with | some T => toString T | none => "none"} = {b.val} [{showDecl b.decl}]"

/-- **The frame `fieldTele` types field `i` of constructor `c` of `n` in**, at parameters `ps` and
earlier field values `fs`: the checker is stopped right after it evaluated field `i`'s type (in its
callback, before it binds field `i`) and the top frame is rendered, with the number of frames and
of the bindings below it. As in `checkInd`, the frame below binds the parameters at their types. -/
def snap (n : String) (ps : List Value) (c i : Nat) (fs : List Value) : String :=
  let st : MState := { globals := sigma.1, inds := sigma.2 }
  let d := declNamed n
  let x : M (List (String × Value × Value)) := do
    for ((h, PT), v) in d.params.zip ps do
      pushBind h (some (← evalType 100000 PT)) v
    fieldTele 100000 d ps c fun j _ => do
      if j = i then
        let s ← get
        let fr := s.env.back!
        let below := (s.env.toList.dropLast.map (·.binds.size)).foldl (· + ·) 0
        err (s!"frames {s.env.size} ({below} below): " ++ "; ".intercalate (fr.binds.toList.map showB))
      -- D117 (main, merged by machine9): `fieldTypesOf` binds what each earlier field stands for, `resolveLoans`
      resolveLoans 100000 (fs.getD j .bot)
  match runM x st with
  | .error m => m
  | .ok _ => "no snapshot"

/-- `snap` with a borrow `r ↦ borrow₀ held` bound first (in the frame below), so an earlier field's value can be the
loan `loan₀` it lends: D117's case. -/
def snapLent (n : String) (c i : Nat) (fs : List Value) (held : Value) : String :=
  let st : MState := { globals := sigma.1, inds := sigma.2 }
  let d := declNamed n
  let x : M (List (String × Value × Value)) := do
    pushBind ⟨"r"⟩ (some (.tRef .tNat)) (.borrow 0 held)
    fieldTele 100000 d [] c fun j _ => do
      if j = i then
        let s ← get
        let fr := s.env.back!
        let below := (s.env.toList.dropLast.map (·.binds.size)).foldl (· + ·) 0
        err (s!"frames {s.env.size} ({below} below): " ++ "; ".intercalate (fr.binds.toList.map showB))
      resolveLoans 100000 (fs.getD j .bot)
  match runM x st with
  | .error m => m
  | .ok _ => "no snapshot"

/-! ## `V := MkV(n : Nat, x : Fin1(n))` -/

-- typing `n`: the current field `n` and the later field `x` are unbound
#guard snap "V" [] 0 0 [] == "frames 2 (0 below): n : none = ⊥ [other]; x : none = ⊥ [other]"
-- typing `x` (its type reads `n`): `n` is bound at its type, the current field `x` is not
#guard snap "V" [] 0 1 [.succ .zero] == "frames 2 (0 below): n : Nat = 1 [other]; x : none = ⊥ [other]"

/-! ## `Three (A : Type) := MkThree(a : A, e : Eq(Nat, 0, 0), b : Nat)`, at `A := Nat` -/

#guard snap "Three" [.tNat] 0 0 [] ==
  "frames 2 (1 below): a : none = ⊥ [other]; e : none = ⊥ [other]; b : none = ⊥ [other]; A : Type = Nat [sort 1]"
#guard snap "Three" [.tNat] 0 1 [.zero] ==
  "frames 2 (1 below): a : Nat = 0 [other]; e : none = ⊥ [other]; b : none = ⊥ [other]; A : Type = Nat [sort 1]"
-- the proof field `e` (its type `Eq(Nat, 0, 0)` evaluates to `⊤`) is read `prop` once bound
#guard snap "Three" [.tNat] 0 2 [.zero, .proof] ==
  "frames 2 (1 below): a : Nat = 0 [other]; e : ⊤ = ⋆ [prop]; b : none = ⊥ [other]; A : Type = Nat [sort 1]"

/-! ## D117: a lent earlier field is bound as what its loan stands for

`n` holds `loan₀`, lent to the borrow `r ↦ borrow₀ 1` below: the frame that types `x` binds `n` at `1`, the borrow's
content, not the loan (before D117 it bound `loan₀`, a second occurrence of the loan, and the type's read of `n`
ended `r`'s borrow from inside the private copy). `teleFrame` binds an earlier field at the value it is given:
the existence lane's reading of a lent field's value must be the borrow's content (finding for that lane). -/
#guard snapLent "V" 0 1 [.loan 0] (.succ .zero) == "frames 2 (1 below): n : Nat = 1 [other]; x : none = ⊥ [other]"

-- the record is produced only by stopping at field `i` (not a vacuous match)
#guard snap "V" [] 0 2 [.succ .zero, .unit] == "no snapshot"

end Ochr.Meaning.DataModel.Exists.TeleFrameGuard
