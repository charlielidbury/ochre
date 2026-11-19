import Ochr.Meaning.State
import Ochr.Meaning.Pi

/-!
# The semantic state the reference run acts on (docs/18 Def. "reference run", docs/27 §5)

The reference run is a state transformer on *meanings*: it never sees a `Value`. Its state is
the checker's `Env` with each position holding a meaning as a function of the future (`SVal`),
each binding its declared type as a `TyM`, the shape (which positions hold a borrow of which
label), and a label counter for fresh borrows. `MState.sstate` reads a checker state into one;
`SState.toMean` forgets the types.

[Access] on this state ends exactly the borrows the accessed position's meaning depends on
(`SState.access`), in label order; that the order does not matter is a lemma of the skeleton
(WF3). [End] is `Mean.semEnd` lifted (`SState.endLabel`).
-/

namespace Ochr.Meaning

/-- A meaning as a function of the future. -/
abbrev SVal : Type 3 := Future → Sem

/-- A semantic binding: its declared type, its meaning, and, for a function's binding of itself
(D78), the recursion it may make: the decreasing parameter and the rank its argument must stay
below (docs/24 §4, guarded recursion: a call that does not decrease means the error value). -/
structure SBinding : Type 3 where
  ty : TyS
  val : SVal
  /-- its declared-type reading (`Binding.decl`), an input of the aligned decisions -/
  decl : DeclInfo := .other
  recBound : Option (Nat × Nat) := none

structure SFrame : Type 3 where
  binds : List SBinding := []
  temps : List SVal := []

/-- A place a borrow is lent at (docs/31 D29, main's D90): a position, the path below it, and
whether the borrow has a FILL there (a returned borrow's: a sealed program over its hole, or the
mark `lent_k v`) or its one LOAN (a plain borrow's, `&p`). The reference's [Access] reads these and
nothing else; the relation makes them the checker's (`Env.sitesOf`). -/
structure Site where
  pos : Pos
  path : List Step
  fill : Bool

/-- A step's field: `.proj i` and `.field g` name the same field of a constructor value when they
agree on the constructor and the index (`Machine.stepV` follows both); `*` is none. -/
def _root_.Ochr.Step.key : Step → Option (Nat × Nat)
  | .deref => none
  | .proj i => some (0, i)
  | .field g => some (g.ctor, g.idx)

/-- A path compared by fields. -/
def pathKey (ψ : List Step) : List (Option (Nat × Nat)) := ψ.map Step.key

/-- [Access] of a place at `steps` reaches a site at the path `ψ` of the same position when the
site is on the path, at the place or inside its content (`accessPath`, then `accessInside`): one
path is a prefix of the other. -/
def dataHit (steps ψ : List Step) : Bool :=
  (pathKey ψ).isPrefixOf (pathKey steps) || (pathKey steps).isPrefixOf (pathKey ψ)

/-- [Access] for a match reaches the sites on the path and at the place, not inside its content
(`accessPath`, then `accessNeutralHead`: a sealed program at the place is a fill there). -/
def tagHit (steps ψ : List Step) : Bool := (pathKey ψ).isPrefixOf (pathKey steps)

structure SState : Type 3 where
  env : List SFrame
  shape : Pos → Option Nat
  nextLoan : Nat
  /-- where each borrow is lent (docs/31 D29); read only for the labels the state holds -/
  lent : Nat → List Site := fun _ => []

namespace SState

def valAt (s : SState) : Pos → SVal
  | .bind f i => match s.env[f]?.bind (·.binds[i]?) with
    | some b => b.val
    | none => fun _ => .err
  | .temp f i => match s.env[f]?.bind (·.temps[i]?) with
    | some v => v
    | none => fun _ => .err

def tyAt (s : SState) : Pos → TyS
  | .bind f i => match s.env[f]?.bind (·.binds[i]?) with
    | some b => b.ty
    | none => .plain .err
  | .temp _ _ => .plain .err

def setAt (s : SState) (p : Pos) (v : SVal) : SState :=
  match p with
  | .bind f i => { s with env := s.env.modify f fun fr =>
      { fr with binds := fr.binds.modify i fun b => { b with val := v } } }
  | .temp f i => { s with env := s.env.modify f fun fr => { fr with temps := fr.temps.set i v } }

def positions (s : SState) : List Pos := Id.run do
  let mut out := #[]
  for h : f in [0:s.env.length] do
    let fr := s.env[f]
    for i in [0:fr.binds.length] do out := out.push (Pos.bind f i)
    for i in [0:fr.temps.length] do out := out.push (Pos.temp f i)
  pure out.toList

/-- Forget the types: the state as a `Mean`. -/
def toMean (s : SState) : Mean := ⟨s.positions, fun φ p => s.valAt p φ, s.shape⟩

/-- The meaning at `p` depends on label `l` (`Mean.dependsOn`). -/
def dependsOn (s : SState) (p : Pos) (l : Nat) : Prop := s.toMean.dependsOn p l

/-- Replace every position's meaning. -/
def mapVals (s : SState) (f : Pos → SVal → SVal) : SState :=
  { s with env := s.env.zipIdx.map fun (fr, fi) =>
      { binds := fr.binds.zipIdx.map fun (b, i) => { b with val := f (.bind fi i) b.val },
        temps := fr.temps.zipIdx.map fun (v, i) => f (.temp fi i) v } }

/-- [End l] on sites (docs/31 D29; main's `lendV (.ended l …)` with the substitution): each site of
any label lying under `l`'s holder `r`, at the path `*::π`, is replaced, for each site of `l`, by
that site whole if it is a fill (a fill over `l` becomes a fill over every borrow of `l`'s final
content) and by the path `π` below it, keeping its own kind, if it is `l`'s loan (the content
replaces the loan, so a reborrow's loan lands at its own path); `l` keeps no site. -/
def relend (s : SState) (l : Nat) (r : Pos) : Nat → List Site := fun m =>
  if m = l then [] else (s.lent m).flatMap fun x =>
    match x.path with
    | .deref :: π =>
      if x.pos = r then (s.lent l).map fun y => if y.fill then y else { y with path := y.path ++ π, fill := x.fill }
      else [x]
    | _ => [x]

/-- [End l] (docs/27 Def. 4): the holder `r` of `l` is forgotten and every meaning reads `l`'s
final content as what `r` holds now; the places `l` was lent pass to the borrows of that content
(`relend`). A label held nowhere is inert: nothing happens. -/
noncomputable def endLabel (s : SState) (l : Nat) : SState :=
  open Classical in
  match (s.positions.find? fun p => decide (s.shape p = some l)) with
  | some r =>
    let m := s.toMean.semEnd r l
    ({ s with shape := m.shape, lent := s.relend l r }).mapVals fun p _ => (m.val · p)
  | none => s

/-- The live labels, in label order. -/
def liveLabels (s : SState) : List Nat :=
  (s.positions.filterMap s.shape).mergeSort (· ≤ ·)

/-- The label `l` has a site at `p` whose path `hit` accepts (`dataHit`, `tagHit`). -/
def reached (s : SState) (p : Pos) (hit : List Step → Bool) (l : Nat) : Bool :=
  (s.lent l).any fun x => decide (x.pos = p) && hit x.path

/-- [Access] of the position `p` (docs/31 D29, main's D90): end, in label order and to a fixpoint,
every live label with a site at `p` that `hit` accepts: `dataHit steps` for a read, a borrow, an
assignment and a drop of the place at `steps`, `tagHit steps` for a match. Ending one label passes
its sites to the borrows of its content (`relend`), which may then be reached in turn; there are
at most as many rounds as live labels. It reads sites only, never a meaning: the reference ends
a borrow as the checker does, from where it is lent, whatever the place's meaning depends on.

As first written (docs/27 §5) it ended the labels the observed meaning depends on (`obsDep`), and
the relation then had to carry the borrows the checker ended early (docs/31 D25, D27, D28). Main's
D90 made the checker's ends static; D29 made the reference's the same. -/
noncomputable def access (s : SState) (p : Pos) (hit : List Step → Bool) : SState :=
  let step (s : SState) : SState := (s.liveLabels.filter (s.reached p hit)).foldl endLabel s
  (List.range s.liveLabels.length).foldl (fun s _ => step s) s

/-- The label `l` is now lent at the sites `xs` (a fresh borrow's, or a borrow-returning call's). -/
def setLent (s : SState) (l : Nat) (xs : List Site) : SState :=
  { s with lent := fun m => if m = l then xs else s.lent m }

@[simp] theorem setLent_env (s : SState) (l : Nat) (xs : List Site) : (s.setLent l xs).env = s.env := rfl
@[simp] theorem setLent_shape (s : SState) (l : Nat) (xs : List Site) : (s.setLent l xs).shape = s.shape := rfl
@[simp] theorem setLent_nextLoan (s : SState) (l : Nat) (xs : List Site) :
    (s.setLent l xs).nextLoan = s.nextLoan := rfl
@[simp] theorem setLent_valAt (s : SState) (l : Nat) (xs : List Site) (p : Pos) :
    (s.setLent l xs).valAt p = s.valAt p := rfl
@[simp] theorem setLent_tyAt (s : SState) (l : Nat) (xs : List Site) (p : Pos) :
    (s.setLent l xs).tyAt p = s.tyAt p := rfl
@[simp] theorem setLent_positions (s : SState) (l : Nat) (xs : List Site) :
    (s.setLent l xs).positions = s.positions := rfl

/-- The top frame's index. -/
def topIdx (s : SState) : Nat := s.env.length - 1

/-- De Bruijn variable `i` of the top frame, as a position. -/
def varPos (s : SState) (i : Nat) : Option Pos :=
  match s.env.getLast? with
  | some fr => if i < fr.binds.length then some (.bind s.topIdx (fr.binds.length - 1 - i)) else none
  | none => none

def pushFrame (s : SState) : SState := { s with env := s.env ++ [{}] }

def pushBind (s : SState) (b : SBinding) : SState :=
  { s with env := s.env.modify s.topIdx fun fr => { fr with binds := fr.binds ++ [b] } }

def pushTemp (s : SState) (v : SVal) : SState :=
  { s with env := s.env.modify s.topIdx fun fr => { fr with temps := fr.temps ++ [v] } }

def freshLoan (s : SState) : Nat × SState := (s.nextLoan, { s with nextLoan := s.nextLoan + 1 })

/-- The position holding the borrow of label `l`, if any. -/
noncomputable def holderOf (s : SState) (l : Nat) : Option Pos :=
  open Classical in s.positions.find? fun p => decide (s.shape p = some l)

/-- Take the holder of `l` away (the borrow moves elsewhere): the old holder is forgotten and no
longer in the shape. The caller records the new holder. -/
noncomputable def takeLabel (s : SState) (l : Nat) : SState :=
  match s.holderOf l with
  | some r => { (s.setAt r fun _ => .moved) with shape := fun p => if p = r then none else s.shape p }
  | none => s

/-- Park a borrow in a fresh temporary of the top frame, which becomes its holder (D14: a label
always has a holder, from its creation to its end). -/
noncomputable def pushTempShaped (s : SState) (v : SVal) (l : Nat) : SState :=
  let s' := s.pushTemp v
  match s'.env.getLast? with
  | some fr => { s' with shape := fun p => if p = .temp s'.topIdx (fr.temps.length - 1) then some l else s'.shape p }
  | none => s'

/-- The state's closed future: `φ` with every live label fixed to its holder's current content,
iterated as `access` iterates (a holder may itself read a live label). A read that skips
[Access] reads at it, so it depends on `φ` only at labels the state does not hold (D14). -/
noncomputable def closedFuture (s : SState) (φ : Future) : Future :=
  (List.range s.liveLabels.length).foldl (fun ψ _ =>
    s.liveLabels.foldl (fun ψ l =>
      match s.holderOf l with
      | some r => ψ.upd l (s.valAt r ψ)
      | none => ψ) ψ) φ

/-- Drop the last binding of the top frame ([Let]'s drop; the borrow it holds is ended by the
drop, `run`'s `.letIn`). Its shape entry is cleared with it (mono-lemmas'
`DropHolderCounterexample`: a stale entry would make the next binding at that position a holder of a
borrow it never made). -/
def dropLast (s : SState) : SState :=
  let removed : Option Pos := match s.env.getLast? with
    | some fr => some (.bind s.topIdx (fr.binds.length - 1))
    | none => none
  { s with env := s.env.modify s.topIdx fun fr => { fr with binds := fr.binds.dropLast },
           shape := fun p => if some p = removed then none else s.shape p }

end SState

mutual
/-- The sites of the borrow `l` in a value held at `pos`, the value lying at `path` (docs/31 D29):
`l`'s loan where it is not inside a fill over `l`, each mark `lent_l` and each sealed program among
whose loans `l` is, read as a fill at its own place (a path goes through a mark, `Machine.stepV`,
and does not go into a sealed program). -/
def _root_.Ochr.Value.sitesOf (l : Nat) (pos : Pos) (path : List Step) : Value → List Site
  | .loan m => if m = l then [⟨pos, path, false⟩] else []
  | .gloan m w => if m = l then [⟨pos, path, true⟩] else Value.sitesOf l pos path w
  | .sealed t => if (Value.sealed t).hasLoan l then [⟨pos, path, true⟩] else []
  | .borrow _ w => Value.sitesOf l pos (path ++ [.deref]) w
  | .succ w => Value.sitesOf l pos (path ++ [.proj 0]) w
  | .ind ty c _ _ fs => Value.sitesOfFields l pos path ty c 0 fs
  | _ => []

def _root_.Ochr.Value.sitesOfFields (l : Nat) (pos : Pos) (path : List Step) (ty : String) (c : Nat) :
    Nat → List Value → List Site
  | _, [] => []
  | i, w :: ws => Value.sitesOf l pos (path ++ [.field ⟨ty, c, i, ""⟩]) w ++ Value.sitesOfFields l pos path ty c (i + 1) ws
end

/-- The sites of the borrow `l` in Ω: where the checker's [Access] finds it (docs/31 D29). -/
def _root_.Ochr.Env.sitesOf (env : Env) (l : Nat) : List Site :=
  (allPos env).flatMap fun p => (valAt env p).sitesOf l p []

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl)

/-- The checker's state read as a semantic state: each binding's value as a function of the
future at its stored type, each temporary's, the shape, and the label counter. A binding is
typed at its stored type with the structure of the value it holds where that is a type
(`Value.strS`, the audit's A19). A binding of a
function of itself carries no recursion mark here (the checker's `RecCtx` is a check's input);
the reference run sets it when it pushes a frame. -/
noncomputable def _root_.Ochr.MState.sstate (ρ : Assignment) (st : MState) : SState :=
  { env := st.env.toList.zipIdx.map fun (fr, f) =>
      { binds := fr.binds.toList.zipIdx.map fun (b, i) =>
          { ty := Value.strS dm C Γ ρ b.val (Env.hintAt dm C Γ ρ st.env (.bind f i)),
            val := fun φ => Env.mean dm C Γ ρ φ st.env (.bind f i),
            decl := b.decl },
        temps := fr.temps.toList.zipIdx.map fun (_, i) => fun φ => Env.mean dm C Γ ρ φ st.env (.temp f i) },
    shape := Env.shape st.env,
    nextLoan := st.nextLoan,
    lent := Env.sitesOf st.env }

end

end Ochr.Meaning
