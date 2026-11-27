import Ochr.Meaning.Steps.ColumnIStart
import Ochr.Test

/-!
# Sanity runs of the first columns with a parameter (lead14; compiled, not kernel-checked)

**The programs.** `I`'s body is the core term `S(#0)` (`ParBody.bodyI`), `P`'s
`match #0 { Z => Z, S _ => #0.0 }`. `P` is what the surface `match n { Z => Z, S m => m }` resolves
to (asserted below). `I` is NOT what the surface `S(n)` resolves to: there `S` is a function, the
surface's `succFn = fix _ (n : Nat) : Nat := S(#0)`, and `S(n)` is a CALL of it (asserted below),
which the checker checks as a call (it checks `succFn`'s body at its own generic call, then the call;
docs/31 D124). The core `I` is `succFn` under a name: its column is the check of `succFn`'s body.
Numerals (`1`, `Term.ofNat`) are the surface's direct `S`.

**The body's start state** (`checkFix`'s generic state, recorded by the checker itself at the body's
entry, `Config.recordStates`, for the surface `P` and for a surface function with `I`'s signature):
frame 0 empty; frame 1 holding the function's binding of itself `f ↦ .gfn f` at `Π(n : Nat). Nat`,
read `.pi .other`, MARKED (`recUid = some 0`), then `n ↦ σ0` at `Nat` read `.other`; `absTy = [Nat]`,
`nextAbs = 1`, no loan, the goal `Nat`, typed, no refinement; Σ the function's own global, as `checkDef`
pushed it. It does not depend on the body (two bodies below), and its kernel is `ColumnI.stI`, where
`Pre`, `Rel` and `SGood` are proved (`Steps/ColumnIStart.lean`).
-/

open Ochr.Test

ochr ParProbeI {
  def Ip (n : Nat) : Nat := S(n)
}

ochr ParProbeP {
  def Pp (n : Nat) : Nat := match n { Z => Z, S m => m }
}

namespace Ochr.Meaning.Steps.Form

namespace ParGuards

open Ochr Ochr.Surface
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)

/-- The resolved body of a declaration of a block. -/
def bodyOf (b : Block) (name : String) : Term :=
  match b.decls.find? (·.name == name) with
  | some d => match runResolve b.decls d 100000 with
    | (.ok (.ok (.defn df)), _) => df.body
    | _ => .zero
  | none => .zero

/-- `P`'s body is the surface's `match n { Z => Z, S m => m }`. -/
def bodyP : Term := .matchNat (.var 0) .zero (.place (.proj 0 (.var 0)))

#guard bodyOf ParProbeP "Pp" == bodyP
-- the surface `S(n)` is a call of `succFn`, whose body is `I`'s
#guard bodyOf ParProbeI "Ip" == .call succFn [.place (.var 0)] false
#guard succFn == .fix ⟨"_"⟩ [⟨"n"⟩] [.nat] .nat none bodyI

/-- The checker's recorded states on entry to the located terms of a declaration of a block. -/
def entries (b : Block) (name : String) : List MState :=
  let r := Ochr.Test.runWith none b.name b { recordStates := true } (located := true)
  match r.rows.find? (·.name == name) with
  | some row => row.trace.toList.filterMap fun
      | .state _ false _ st => some st | _ => none
  | none => []

def declIs : DeclInfo → DeclInfo → Bool
  | .other, .other => true
  | .pi a, .pi b => declIs a b
  | _, _ => false

/-- A binding as the relation reads it: name, value, stored type, reading, proof flag, mark. -/
def bindOk (b : Binding) (x : String) (v : Value) (T : Value) (d : DeclInfo) (mark : Option Nat) : Bool :=
  b.hint.name == x && b.val == v && b.ty == some T && declIs b.decl d && !b.proof && b.recUid == mark &&
    !b.cap && b.lazyTy.isNone

open ColumnI (piNat)

/-- A global as `checkDef` pushes it for `f (n : Nat) : Nat := body`. -/
def globalOk (g : GDef) (f : String) (body : Term) : Bool :=
  g.name == f && g.ty == piNat && g.fn? == some (.fix ⟨f⟩ [⟨"n"⟩] [.nat] .nat none body) && g.val == .gfn f &&
    !g.model && g.absTys.isEmpty && g.absDecls.isEmpty

/-- The body's start state agrees with `ColumnI.stI` (renamed to `f`, `f`'s body `body`) on its kernel
(`MState.norm`: what `Pre`, `Rel` and the steps read). -/
def kernelOk (f : String) (body : Term) (st : MState) : Bool :=
  st.env.size == 2 && st.env[0]!.binds.isEmpty && st.env[0]!.temps.isEmpty && st.env[1]!.temps.isEmpty &&
  st.env[1]!.binds.size == 2 &&
  bindOk st.env[1]!.binds[0]! f (.gfn f) piNat (.pi .other) (some 0) &&
  bindOk st.env[1]!.binds[1]! "n" (.abs 0) .tNat .other none &&
  (match st.globals with | [g] => globalOk g f body | _ => false) && st.inds.isEmpty &&
  st.absTy == #[.tNat] && st.nextAbs == 1 && st.nextLoan == 0 && st.goal == some .tNat &&
  st.refs.isEmpty && st.etaRefs.isEmpty && st.neutrals.isEmpty && !st.liveScope &&
  st.absDecl.size == 1 && declIs st.absDecl[0]! .other

/-- ... and on the mode the run starts in: typed, not in tail position, no reading handed down, no
private copy, the function's mark taken (`nextRecUid` one past it), no [Rec] context (no `by`). -/
def modeOk (f : String) (st : MState) : Bool :=
  st.typing && !st.curTail && !st.tailNext && st.tailDecl.isNone && !st.copying && !st.inPlace && !st.headEval &&
  st.erasedDepth == 0 && st.privateDepth == 0 && st.depth == 0 && st.obsFrame.isNone && st.nextRecUid == 1 &&
  -- since main's D136 a function without `by` has no [Rec] context (it was one context with no candidate); since its
  -- amendment the function's check still takes a mark, so `nextRecUid` is one past it
  st.recStack.isEmpty && f == f

-- the first recorded state of each function is its body's entry: the same for every body
#guard (entries ParProbeP "Pp").head?.any fun st => kernelOk "Pp" bodyP st && modeOk "Pp" st
#guard (entries ParProbeI "Ip").head?.any fun st => kernelOk "Ip" (.call succFn [.place (.var 0)] false) st && modeOk "Ip" st

/-- The full start state of `I`'s body: the kernel `ColumnI.stI` in the mode `checkFix` starts it in. -/
def stI : MState :=
  { ColumnI.stI with typing := true, nextRecUid := 1 }

-- the hand-built kernel passes the same test
#guard kernelOk "I" bodyI ColumnI.stI && kernelOk "I" bodyI stI && modeOk "I" stI

/-- `I` and `P` as core definitions: accepted by `checkDef`, which leaves exactly their global. -/
def defI : Def := { name := "I", hs := [⟨"n"⟩], doms := [.nat], cod := .nat, body := bodyI }
def defP : Def := { name := "P", hs := [⟨"n"⟩], doms := [.nat], cod := .nat, body := bodyP }
#guard isOk (checkDef defI) {} 100000
#guard isOk (checkDef defP) {} 100000
#guard match (outSt (checkDef defI) {} 100000).globals with | [g] => globalOk g "I" bodyI | _ => false
#guard match (outSt (checkDef defP) {} 100000).globals with | [g] => globalOk g "P" bodyP | _ => false

/-! ## `I`'s body from the start state: `S(σ0)` at `Nat`, `n` moved -/

#guard outVal (Ochr.eval 100 true bodyI (some .tNat)) stI 100000 == (.succ (.abs 0), some .tNat)
#guard ((outSt (Ochr.eval 100 true bodyI (some .tNat)) stI 100000).env[1]!.binds.map (·.val)) ==
  #[.gfn "I", .bot]
-- the run makes no unknown and no loan, and keeps the frames
#guard (outSt (Ochr.eval 100 true bodyI (some .tNat)) stI 100000).nextAbs == 1
#guard (outSt (Ochr.eval 100 true bodyI (some .tNat)) stI 100000).env.size == 2

/-! ## `VarNumAInv`: the read of a variable holding a numeral over an unknown

At the start state (`σ0`), at `S(σ0)` and at a numeral over `Z`; typed and untyped; in tail position;
under a handed-down reading; in a private copy (`copying`: `clone`'s mode, where the read copies). -/

def withN (v : Value) : MState :=
  { stI with env := stI.env.set! 1 { binds := #[stI.env[1]!.binds[0]!, { stI.env[1]!.binds[1]! with val := v }] } }

def modeOf (st : MState) : Bool × Bool × Bool × Nat := (st.headEval, st.copying, st.inPlace, st.erasedDepth)

def readN (typed : Bool) : M (Value × Option Value) := Ochr.evalCore 100 typed (.place (.var 0)) none

#guard [Value.abs 0, .succ (.abs 0), .succ (.succ .zero)].all fun v =>
  outVal (readN true) (withN v) 100000 == (v, some .tNat) &&
  -- moved: the copy decision at `.other` is false
  ((outSt (readN true) (withN v) 100000).env[1]!.binds.map (·.val)) == #[.gfn "I", .bot] &&
  -- in tail position and under a handed-down reading: the same
  outVal (readN true) { withN v with curTail := true } 100000 == (v, some .tNat) &&
  outVal (Ochr.eval 100 true (.place (.var 0)) none) { withN v with tailDecl := some .other } 100000 == (v, some .tNat) &&
  -- untyped: the same value, a type only if computed, and then `Nat`
  (outVal (readN false) (withN v) 100000).1 == v &&
  (outVal (readN false) (withN v) 100000).2.all (· == .tNat) &&
  -- the mode after is the mode before
  modeOf (outSt (readN true) (withN v) 100000) == (false, false, false, 0)
-- in `clone`'s mode the read copies: the binding keeps its value
#guard ((outSt (readN true) { withN (.abs 0) with copying := true } 100000).env[1]!.binds.map
  (·.val)) == #[.gfn "I", .abs 0]

end ParGuards

end Ochr.Meaning.Steps.Form
