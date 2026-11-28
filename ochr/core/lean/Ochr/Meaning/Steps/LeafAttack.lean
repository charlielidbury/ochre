import Ochr.Meaning.Steps.TopLeaf
import Ochr.Test
import Ochr.Meaning.Regress.GenNeutralContent

/-!
# The knot's leaf facts and the goal clause, attacked on the real checker (lead48, 2026-11-28; docs/31 D291)

Programs chosen to break (A) the checker's part of `Top.Leaf.LeafConvG`: the goal `fixCont` compares the leaf's type with,
read after [Return]'s checks and the frame's pop, is the goal at the leaf; and (B) the goal clause (docs/31 D290) at the
named facts that state it as equality of MEANINGS, at an instance where the goal IS written under the extension: an
argument's evaluation generalising a sealed program the goal mentions (`CallHeadArgsG`), a callee's in-place run
refining an unknown the goal mentions (`CallFnG`, `CallExitG`), a join refining (`JoinContG`). Each run is the checker's
own `checkTail` of the definition's body from the generic state it records, with a continuation that inspects the leaf.
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr LeafAtk {
  inductive Bx := MkBx(n : Nat)
  def G (n : Nat) : Nat by n := match n { Z => Z, S(m) => G(m), }
  def F2 (m : Nat) : Nat := match m { Z => Z, S(j) => Z, }
  def K1 (m : Nat) : Nat := m
  def Gb (n : Nat) : Bx by n := match n { Z => MkBx(Z), S(m) => Gb(m), }
  def AddM (x : &Nat) (y : Nat) : Unit by x := match *x { Z => *x := y, S(p) => AddM(&p, y), }
  def TailM (x : &Nat) : &Nat by x := match *x { Z => x, S(p) => TailM(&p), }
  def Fm (b : Bx) (k : Nat) : Nat := (let r = match k { Z => Z, S(j) => (let q = b.0; Z), }; r)
  def Vn (n : Nat) : Type := match n { Z => Unit, S(m) => Nat, }
  def Fld (b : Bx) : Nat := match b { MkBx(n) => clone(n), }
  -- A. the goal read after the pop (accepted programs)
  -- 1. an erased body writing through its borrow parameter
  def L1 (x : &Nat) : True := (*x := 5; refl)
  -- 2. `AddMZero`: the goal refined by the split, the borrow parameter's content around a reborrow at the pop
  def L2 (x : &Nat) : Id(Unit, AddM(&*x, 0), ()) by x := match *x { Z => refl, S(p) => L2(&p), }
  -- 3. a goal holding a sealed program, re-run by the refinement
  def L3 (n : Nat) : Eq(Nat, G(n), Z) by n := match n { Z => refl, S(m) => L3(m), }
  -- 4. a returned borrow ([Return] on a borrow; the other parameter's borrow ends at the pop)
  def L4 (x : &Nat) (y : &Nat) : &Nat := x
  -- 5. a stuck call's fill in the borrowed place, re-run when the pop ends the borrow
  def L5 (x : &Nat) : Unit := (let t = TailM(&*x); *t := Z)
  -- 6. a sealed scrutinee generalised at the end of the body, inside the goal
  def L6 (n : Nat) : Eq(Nat, F2(G(n)), Z) := (let g = G(clone(n)); match g { Z => refl, S(k) => refl, })
  -- 7. a write into a parameter of one constructor, the pop with its content refined
  def L7 (b : &Bx) : Unit := match *b { MkBx(n) => n := Z, }
  -- 8. a function returning a function: the leaf's type and the goal are code (`LeafSideG`'s `FO` fails)
  def L8 (n : Nat) : (Π(m : Nat). Nat) := λ(m : Nat) : Nat => clone(m)
  -- 15. a leaf returning an unknown (`LeafReturnG` as first stated is false here)
  def Id1 (n : Nat) : Nat := n
  -- 16. a leaf returning a moved-out place, or a partly moved one: rejected (a read asks its content whole)
  reject def R1 (n : Nat) : Nat := (let a = n; n)
  reject def R2 (p : Pair(Nat, Nat)) : Pair(Nat, Nat) := (let a = p.0; p)
  -- C. the pop at the leaf: a borrow parameter's content refilled, re-borrowed, split by a match
  -- 9. moved out and refilled through the borrow (`mem::replace`), both parameters
  def P1 (x : &Nat) (y : &Nat) : Unit := (let a = *x; let b = *y; *x := b; *y := a)
  -- 10. a parameter re-pointed at a reborrow of the other's content (a chain of loans across the two cells)
  def P2 (x : &Nat) (y : &Nat) : Unit := y := &*x
  -- 11. re-pointed at a reborrow of its own content's field, then written (`Trav`)
  def P3 (x : &Nat) : Unit := match *x { Z => (), S(p) => (x := &p; *x := 0), }
  -- 12. split by a tail match, a write through the pattern variable in one world, a recursive call in the other
  def P4 (x : &Nat) : Unit by x := match *x { Z => *x := 1, S(p) => P4(&p), }
  -- 13. split by a match not in tail position (closed off as a block), then written
  def P5 (x : &Nat) (n : Nat) : Unit := (let u = match n { Z => (), S(m) => *x := 2, }; *x := 3)
  -- 14. a one-constructor content refined in place, its field moved out and refilled
  def P6 (b : &Bx) : Unit := match *b { MkBx(n) => (let k = n; n := S(k)), }
  -- B. the goal written under the extension (rejected or not: only the leaf is inspected)
  -- `CallHeadArgsG`: the argument's match on a sealed program generalises it, in the goal too
  reject def B1 (n : Nat) : Eq(Nat, F2(G(n)), Z) := (let g = G(clone(n)); let r = K1(match g { Z => Z, S(k) => Z, }); refl)
  -- `CallFnG`/`CallExitG`: the callee's in-place run refines the caller's unknown in place, in the goal too
  reject def B2 (b : Bx) : Eq(Bx, clone(b), MkBx(Z)) := (let r = Fm(b, Z); refl)
  -- `JoinContG` (a data function: a lemma's join is empty, its arms being statements): the join of world `Z` drops `b.0`,
  -- which arm `S` moves, refining `b`'s unknown in place, in the goal too
  reject def J1 (b : Bx) (k : Nat) : Vn(Fld(b)) := match k { Z => 0, S(j) => (let q = b.0; 0), }
  -- `JoinContG`: the join drops `c.0`, generalising the sealed program `c` holds, then refining it in place
  reject def J2 (n : Nat) (k : Nat) : Vn(Fld(Gb(n))) := (let c = Gb(clone(n)); match k { Z => 0, S(j) => (let q = c.0; 0), })
}

namespace Ochr.Meaning.Steps.LeafAtk

open Ochr Ochr.Meaning
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)

-- every verdict as expected
#guard ((Ochr.Test.runWith (some Prelude) "LeafAtk" LeafAtk {} (located := false)).allAsExpected)

/-- The resolved body of a definition of the block. -/
def bodyOf (name : String) : Term :=
  match LeafAtk.decls.find? (·.name == name) with
  | some d => match Ochr.Surface.runResolve LeafAtk.decls d 100000 with
    | (.ok (.ok (.defn df)), _) => df.body
    | _ => .zero
  | none => .zero

/-- The checker's recorded state at the entry of a definition's body (its frame: the function's binding of itself,
then `np` parameters). -/
def entryOf (nm : String) (np : Nat) : Option MState :=
  let r := Ochr.Test.runWith (some Prelude) "LeafAtk" LeafAtk { recordStates := true } (located := true)
  match r.rows.find? (·.name == nm) with
  | some row => (row.trace.toList.filterMap fun e => match e with
      | .state _ _ _ st => if st.env.size == 2 && st.env[1]!.binds.size == np + 1 then some st else none
      | _ => none).head?
  | none => none

/-! ## (A) The goal `fixCont` reads after [Return]'s checks and the frame's pop is the leaf's

`kPop` runs `checkFix`'s own continuation (`Top.fixCont`, copied from `Machine.checkFix`) at the leaf, and then asks that
the goal be the leaf's. `fixCont` ends with `conv`, which puts back the state it started from but for fresh names (D103;
`Conv.conv_namesKept`, PROVED), so the goal after `fixCont` is the goal `conv` compared the leaf's type with. Each
program is accepted, so `fixCont` succeeds at every leaf (its comparison included), and the guard asks the goal at every
leaf. Programs: an erased body writing through its borrow parameter (`L1`), `AddMZero` (`L2`: the borrow parameter's
content around a reborrow at the pop), a goal holding a sealed program refined by the split (`L3`), a returned borrow
(`L4`), a stuck call's fill re-run when the pop ends the borrow (`L5`), a sealed scrutinee generalised inside the goal at
the end of the body (`L6`), a write into a parameter of one constructor refined in place (`L7`). -/

/-- `checkFix`'s continuation at the leaf, then the goal as it was at the leaf. -/
def kPop (name : String) : Value → Value → M Unit := fun v T => do
  let g0 := (← get).goal
  Ochr.Meaning.Steps.Form.Top.fixCont 1000 name none v T
  unless (← get).goal == g0 do err "LeafGoalPop: the goal read after the pop is not the leaf's"

/-- The leaf's goal is a goal: set, and not D124's deferred hint (`hintM` reads it as a type, `Value.tyS`). -/
def kGoalForm : Value → Value → M Unit := fun _ _ => do
  match (← get).goal with
  | some g => if (Ochr.Meaning.Steps.deferredHint? g).isSome then err "a deferred hint as the goal" else pure ()
  | none => err "no goal at the leaf"

def progsA : List (String × Nat) :=
  [("L1", 1), ("L2", 1), ("L3", 1), ("L4", 2), ("L5", 1), ("L6", 1), ("L7", 1), ("L8", 1)]

-- at every leaf of every program, the goal `fixCont` compares with is the leaf's, and it is a goal
#guard progsA.all fun (n, k) => (entryOf n k).any fun st => isOk (Ochr.checkTail 1000 (bodyOf n) (kPop n)) st 100000
#guard progsA.all fun (n, k) => (entryOf n k).any fun st => isOk (Ochr.checkTail 1000 (bodyOf n) kGoalForm) st 100000

/-- At the leaf, the goal and the leaf's type are function types (Π-closures): values that hold code, outside the class
`Conv.FO` on which N3 is proved (`Conv.conv_sound_fo'`). -/
def kCode : Value → Value → M Unit := fun _ T => do
  match (← get).goal, T with
  | some (.tPi ..), .tPi .. => pure ()
  | _, _ => err "not code"

-- `L8` is accepted, and at its leaf both types are code: there `LeafConvG` rests on N3 for code (the conversion lane's
-- `CodeOk`, open), not on `LeafSideG`
#guard (entryOf "L8" 1).any fun st => isOk (Ochr.checkTail 1000 (bodyOf "L8") kCode) st 100000

/-! ## [Return] at the leaf (`LeafReturnG`): its first form is false at a leaf returning an unknown

At `Id1`'s leaf the value is the parameter's unknown `σ0`, and `fixCont` succeeds there; `meanV` at an unknown is its
assignment's value, so an assignment sending `σ0` to `.moved` refutes the first form, which asked every assignment
(`Top.Leaf.leafReturnG_old_false`). The restated form asks the leaf's own assignment, which meets the state. -/

/-- At the leaf the value is an unknown, and `checkFix`'s continuation succeeds. -/
def kAbsLeaf (name : String) : Value → Value → M Unit := fun v T => do
  unless v matches .abs _ do err "not an unknown"
  Ochr.Meaning.Steps.Form.Top.fixCont 1000 name none v T

#guard (bodyOf "Id1").pp [] == "#0"
#guard (entryOf "Id1" 1).any fun st => isOk (Ochr.checkTail 1000 (bodyOf "Id1") (kAbsLeaf "Id1")) st 100000

/-! ## (C) The pop at the leaf (`LeafPopG`, `LeafPopAt`): the borrows it ends and the finals it leaves

`kCells` runs `fixCont`'s pop at the leaf and asks, of the checker's state after it, what the two facts carry to the
reference's: no borrow and no loan is left anywhere (every borrow live at the leaf is the body frame's, and the pop ends
it), and each cell (the generic call's owned place of a borrow parameter) holds a whole value of its content type
(`packedErr` none: its type converts to the content type, [Repack] at a dependent one). Every program is accepted, so
`fixCont` succeeds at every leaf. -/

/-- `fixCont` at the leaf, then the cells: no borrow or loan left, each cell whole at its content type. -/
def kCells (name : String) : Value → Value → M Unit := fun v T => do
  Ochr.Meaning.Steps.Form.Top.fixCont 1000 name none v T
  let st ← get
  for p in allPos st.env do
    let w := valAt st.env p
    if w.hasBorrow then err s!"a borrow survives the pop: {w}"
    unless w.loans.isEmpty do err s!"a loan survives the pop: {w}"
  let some fr := st.env[st.env.size - 1]? | err "no frame"
  for b in fr.binds do
    if b.val.hasHole then err s!"cell {b.hint.name} holds a moved-out part: {b.val}"
    match b.ty with
    | some C => if let some m ← Ochr.packedErr 1000 b.val C then err s!"cell {b.hint.name}: {m}"
    | none => err s!"cell {b.hint.name} has no type"

def progsC : List (String × Nat) :=
  [("L2", 1), ("L5", 1), ("L7", 1), ("P1", 2), ("P2", 2), ("P3", 1), ("P4", 1), ("P5", 2), ("P6", 1)]

#guard progsC.all fun (n, k) => (entryOf n k).any fun st => isOk (Ochr.checkTail 1000 (bodyOf n) (kCells n)) st 100000
-- the check bites: at a borrow codomain (`L4`, outside `LeafPopG`, a data codomain) the result keeps its cell lent
#guard (entryOf "L4" 2).any fun st => !isOk (Ochr.checkTail 1000 (bodyOf "L4") (kCells "L4")) st 100000

/-! ## (B) The goal written under the extension: the leaf's goal is the entry's under the path's records

At each instance below the checker WRITES the goal between the body's entry and the leaf (`kWritten`), and the goal at the
leaf is exactly the entry's goal under the path's records (`kExp`): every refinement made on the path (`refs`: a world's
`σ := C(σ̄)`, an η-refinement in place) substituted, every sealed program re-normalised (which reads the generalisation
records, `neutrals`, [Seal-stuck]), to a fixpoint. An assignment that meets the path's records (`TypedAssignment`: the
refinements, and each generalised program's meaning at its unknown, `GenTailG`) gives the two the same meaning, since a
sealed program means its run and substitution commutes with meaning (`meanV_substAbs`): so the clause holds by equality
of meanings there, as D288 reads it. A write the records do not account for would make `kExp` fail. -/

/-- The entry's goal under the current state's records: refinements substituted, sealed programs re-normalised. -/
def expectGoal (g0 : Value) : M Value := do
  let mut g := g0
  for _ in [0:3] do
    g ← withErased (Ochr.renormV 1000 g)
    for (σ, r) in (← get).refs.reverse do
      g ← withErased (Ochr.substV 1000 (.abs σ) r g)
  pure g

/-- At the leaf, the goal is the entry's `g0` under the path's records. -/
def kExp (g0 : Value) : Value → Value → M Unit := fun _ _ => do
  let gl := (← get).goal
  let e ← expectGoal g0
  unless gl == some e do err s!"the goal at the leaf {gl} is not the entry's under the path's records {e}"

/-- At the leaf, the goal is not the entry's `g0`: it was written. -/
def kWritten (g0 : Value) : Value → Value → M Unit := fun _ _ => do
  if (← get).goal == some g0 then err "the goal was not written"

/-- The instances: `B1` (`CallHeadArgsG`), `B2` (`CallFnG`, `CallExitG`), `J1`, `J2` (`JoinContG`), and the end-of-body
writes `L2`, `L3` (a world's refinement, `WorldRefineG`), `L6` (a generalisation, `GenTailG`). -/
def progsB : List (String × Nat) := [("B1", 1), ("B2", 1), ("J1", 2), ("J2", 2), ("L2", 1), ("L3", 1), ("L6", 1)]

#guard progsB.all fun (n, k) => (entryOf n k).any fun (st : MState) => st.goal.any fun g0 =>
  isOk (Ochr.checkTail 1000 (bodyOf n) (kWritten g0)) st 100000
#guard progsB.all fun (n, k) => (entryOf n k).any fun (st : MState) => st.goal.any fun g0 =>
  isOk (Ochr.checkTail 1000 (bodyOf n) (kExp g0)) st 100000
-- and where nothing writes the goal, it is the entry's (`L1`, `L4`, `L5`, `L7`)
#guard [("L1", 1), ("L4", 2), ("L5", 1), ("L7", 1)].all fun (n, k) => (entryOf n k).any fun (st : MState) => st.goal.any fun g0 =>
  isOk (Ochr.checkTail 1000 (bodyOf n) (fun _ _ => do unless (← get).goal == some g0 do err "written")) st 100000

/-- The leaf's goal and the path's records (as a failure's message, to read them). -/
def kShow : Value → Value → M Unit := fun _ _ => do
  let st ← get
  err s!"goal {st.goal}; refs {st.refs}; neutrals {st.neutrals.map fun (n, σ) => (toString n, σ)}"

/-- What `kShow` reports at a program's first leaf. -/
def showLeaf (n : String) (k : Nat) : String :=
  match (entryOf n k).map fun (st : MState) => runMachine (Ochr.checkTail 1000 (bodyOf n) kShow) st 100000 with
  | some (Outcome.fail (Fail.error m _), _, _) => m
  | _ => "?"

-- the writes, at the first leaf of each instance: `B1`, the argument's generalisation `⌈G(σ0)⌉ := σ1` inside the goal;
-- `B2`, the callee's in-place run refining the caller's `σ0 := MkBx(σ1)`, the goal's `Eq` then taken apart; `J1`, world
-- `Z`'s join refining `σ0 := MkBx(σ2)` in the goal `⌈Vn(⌈Fld(σ0)⌉)⌉`; `J2`, the join generalising `⌈Gb(σ0)⌉ := σ2`, then
-- refining `σ2 := MkBx(σ3)`
#guard showLeaf "B1" 1 == "goal (some (Eq(Nat, ⌈F2(σ1)⌉, 0))); refs []; neutrals [(⌈G(σ0)⌉, 1)]"
#guard showLeaf "B2" 1 == "goal (some (Eq(Nat, σ1, 0))); refs [(0, MkBx(σ1))]; neutrals []"
#guard showLeaf "J1" 2 == "goal (some ⌈Vn(σ2)⌉); refs [(0, MkBx(σ2)), (1, 0)]; neutrals []"
#guard showLeaf "J2" 2 == "goal (some ⌈Vn(σ3)⌉); refs [(2, MkBx(σ3)), (1, 0)]; neutrals [(⌈Gb(σ0)⌉, 2)]"

end Ochr.Meaning.Steps.LeafAtk
