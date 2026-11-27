import Ochr.Meaning.Steps.ParGuards

/-!
# The checker's body start state, for each kind of function (model5, 2026-11-21; docs/31 D126)

docs/31 D126 rules that the reference runs a closure's body in the checker's frames: frame 0 the
cells of the borrow parameters, frame 1 the captures, the function's own name, then the parameters.
This file pins that shape by running the checker (`Config.recordStates`, the state recorded on entry
to the body; every `#guard` runs in the build), so the model's frames are built against what the
checker does and not against a description of it. `Steps/ParGuards.lean` has the global with one
parameter (`I`, `P`). Here:

- `Sb (r : &Nat) : Unit` (a borrow parameter): frame 0 is the cell `r° ↦ loan 0` at the CONTENT type
  `Nat`; frame 1 is `Sb ↦ .gfn Sb` at the declared Π-type, marked (D78), then `r ↦ borrow 0 σ0` at
  `&Nat`; the counter is past the label.
- `Rc (n : Nat) : Nat by n` (recursive): the frames of a global with one parameter, `[{}, {Rc, n}]`;
  only the [Rec] context differs (the candidate `0`).
- `Lc`'s λ `λ(x : Nat) : Nat => clone(n)` (a capture): frame 0 empty; frame 1 is the capture
  `κ ↦ σ0` at `Nat` (flagged a capture), the λ's binding of itself `_ ↦ .clo [σ0] …` (marked with
  its own [Rec] context), then `x ↦ σ1`. The enclosing body's frames are GONE: `checkFix` starts the
  λ's body from a fresh environment (`env := #[{}]`), and the λ's body is the closed term (`capture`
  renumbers the free variables to the captures).
- `Bc (n : Nat) (r : &Nat) : Nat` and its λ `λ(x : Nat) (q : &Nat) : Nat => clone(n)` (a borrow
  parameter and a capture): `Bc`'s body `[{r° ↦ loan 0}, {Bc, n ↦ σ0, r ↦ borrow 0 σ1}]`; the λ's
  body `[{q° ↦ loan 1}, {κ ↦ σ0, _, x ↦ σ2, q ↦ borrow 1 σ3}]`: frame 0 holds the λ's OWN cell only
  (not `r°`), and the counters run on (label 1, unknowns from 2).
-/

open Ochr.Test

ochr FrameProbeB {
  def Sb (r : &Nat) : Unit := *r := Z
}

ochr FrameProbeR {
  def Rc (n : Nat) : Nat by n := match n { Z => Z, S m => Rc(m) }
}

ochr FrameProbeC {
  def Lc (n : Nat) : Nat := let h = (λ(x : Nat) : Nat => clone(n)); h(Z)
}

ochr FrameProbeBC {
  def Bc (n : Nat) (r : &Nat) : Nat := let h = (λ(x : Nat) (q : &Nat) : Nat => clone(n)); Z
}

namespace Ochr.Meaning.Steps.Form

namespace FrameGuards

open Ochr Ochr.Surface
open ParGuards (entries bindOk)

/-- The first recorded entry state whose frames hold `sizes` bindings (frame 0 first). -/
def entryAt (b : Block) (name : String) (sizes : List Nat) : Option MState :=
  (entries b name).find? fun st => st.env.toList.map (·.binds.size) == sizes

/-- A frame with no temporaries. -/
def noTemps (st : MState) : Bool := st.env.toList.all (·.temps.isEmpty)

/-- The function's binding of itself in a global's body: `.gfn f` at the global's type, marked, recursive or not
(main's D136 as amended, docs/31 D218: every function's binding of itself takes a fresh mark; only a function that
declares `by` has a [Rec] context). -/
def selfOk (st : MState) (f : String) (d : DeclInfo) : Bool :=
  match st.env[1]!.binds[0]?, st.globals.find? (·.name == f) with
  | some b, some g => b.hint.name == f && b.val == .gfn f && b.ty == some g.ty && b.decl == d && !b.proof &&
      b.recUid == some 0 && !b.cap && b.lazyTy.isNone
  | _, _ => false

/-- A capture binding: the value at its type, flagged a capture, unmarked. -/
def capOk (b : Binding) (v : Value) (T : Value) : Bool :=
  b.val == v && b.ty == some T && b.decl == .other && b.cap && !b.proof && b.recUid.isNone

/-- A λ's binding of itself: its closure over `cs`, marked with the fresh mark its check took, `uid` (main's D136 as
amended: a local function is not recursive and has no [Rec] context, but its binding of itself is marked). -/
def lamSelfOk (b : Binding) (cs : List Value) (uid : Nat) : Bool :=
  (match b.val with | .clo cs' _ _ => cs' == cs | _ => false) && b.recUid == some uid && !b.cap &&
    b.decl == .pi .other

/-- A borrow parameter: the borrow of label `l` with content `c`, at `&T`. -/
def borOk (b : Binding) (x : String) (l : Nat) (c T : Value) : Bool :=
  b.hint.name == x && b.val == .borrow l c && b.ty == some (.tRef T) && b.decl == .ref .other &&
    b.recUid.isNone && !b.cap

/-! ## A borrow parameter: the cell in frame 0 -/

#guard (entryAt FrameProbeB "Sb" [1, 2]).any fun st =>
  noTemps st && st.env.size == 2 &&
  bindOk st.env[0]!.binds[0]! "r°" (.loan 0) .tNat .other none &&
  selfOk st "Sb" (.pi .unit) &&
  borOk st.env[1]!.binds[1]! "r" 0 (.abs 0) .tNat &&
  st.nextLoan == 1 && st.nextAbs == 1 && st.absTy == #[.tNat] && st.goal == some .tUnit
-- and it is the body's first entry: the states recorded before it are the parameter types', in the
-- frame the parameters are first pushed into (frame 1 then empty)
#guard ((entries FrameProbeB "Sb").takeWhile fun st => st.env.toList.map (·.binds.size) != [1, 2]).all
  fun st => st.env.toList.map (·.binds.size) == [0, 0]

/-! ## A recursive function: a global's frames, the [Rec] candidate -/

#guard (entries FrameProbeR "Rc").head?.any fun st =>
  noTemps st && st.env.size == 2 && st.env[0]!.binds.isEmpty && st.env[1]!.binds.size == 2 &&
  selfOk st "Rc" (.pi .other) &&
  bindOk st.env[1]!.binds[1]! "n" (.abs 0) .tNat .other none &&
  st.nextLoan == 0 && st.nextAbs == 1 && st.goal == some .tNat &&
  (match st.recStack with | [r] => r.fn == .gfn "Rc" && r.entries == #[some 0] && r.cands == [0] | _ => false)

/-! ## A λ with a capture: the capture in frame 1, the enclosing frames gone -/

#guard (entryAt FrameProbeC "Lc" [0, 3]).any fun st =>
  noTemps st && st.env.size == 2 &&
  capOk st.env[1]!.binds[0]! (.abs 0) .tNat &&
  lamSelfOk st.env[1]!.binds[1]! [.abs 0] 1 &&
  bindOk st.env[1]!.binds[2]! "x" (.abs 1) .tNat .other none &&
  st.nextLoan == 0 && st.nextAbs == 2 && st.goal == some .tNat &&
  -- since main's D136 neither `Lc` nor its λ (no `by`) has a [Rec] context (it was two)
  st.recStack.isEmpty

/-! ## A borrow parameter and a capture: the enclosing body, then the λ's own frame 0 -/

#guard (entryAt FrameProbeBC "Bc" [1, 3]).any fun st =>
  noTemps st && st.env.size == 2 &&
  bindOk st.env[0]!.binds[0]! "r°" (.loan 0) .tNat .other none &&
  selfOk st "Bc" (.pi .other) &&
  bindOk st.env[1]!.binds[1]! "n" (.abs 0) .tNat .other none &&
  borOk st.env[1]!.binds[2]! "r" 0 (.abs 1) .tNat &&
  st.nextLoan == 1 && st.nextAbs == 2
#guard (entryAt FrameProbeBC "Bc" [1, 4]).any fun st =>
  noTemps st && st.env.size == 2 &&
  bindOk st.env[0]!.binds[0]! "q°" (.loan 1) .tNat .other none &&
  capOk st.env[1]!.binds[0]! (.abs 0) .tNat &&
  lamSelfOk st.env[1]!.binds[1]! [.abs 0] 1 &&
  bindOk st.env[1]!.binds[2]! "x" (.abs 2) .tNat .other none &&
  borOk st.env[1]!.binds[3]! "q" 1 (.abs 3) .tNat &&
  st.nextLoan == 2 && st.nextAbs == 4

end FrameGuards

end Ochr.Meaning.Steps.Form
