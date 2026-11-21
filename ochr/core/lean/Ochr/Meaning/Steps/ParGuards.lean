import Ochr.Meaning.Steps.ParBody
import Ochr.Meaning.Steps.ColumnB
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
`nextAbs = 1`, no loan, the goal `Nat`, typed, no refinement. The state does not depend on the body.
-/

open Ochr.Test

ochr ParProbe {
  def Ip (n : Nat) : Nat := S(n)
  def Pp (n : Nat) : Nat := match n { Z => Z, S m => m }
}

namespace Ochr.Meaning.Steps.Form

namespace ParGuards

open Ochr Ochr.Surface
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)

/-- The resolved body of a declaration of `ParProbe`. -/
def bodyOf (name : String) : Term :=
  match ParProbe.decls.find? (·.name == name) with
  | some d => match runResolve ParProbe.decls d 100000 with
    | (.ok (.ok (.defn df)), _) => df.body
    | _ => .zero
  | none => .zero

/-- `P`'s body is the surface's `match n { Z => Z, S m => m }`. -/
def bodyP : Term := .matchNat (.var 0) .zero (.place (.proj 0 (.var 0)))

#guard bodyOf "Pp" == bodyP
-- the surface `S(n)` is a call of `succFn`, whose body is `I`'s
#guard bodyOf "Ip" == .call succFn [.place (.var 0)] false
#guard succFn == .fix ⟨"_"⟩ [⟨"n"⟩] [.nat] .nat none bodyI

/-- The checker's recorded states on entry to the located terms of a `ParProbe` declaration. -/
def entries (name : String) : List MState :=
  let r := Ochr.Test.runWith none "ParProbe" ParProbe { recordStates := true } (located := true)
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

def piNat : Value := .tPi [] (.pi [⟨"n"⟩] [.nat] .nat) []

/-- The body's start state of a function `f (n : Nat) : Nat`, as `checkFix` makes it. -/
def stF (f : String) : MState :=
  { env := #[{}, { binds := #[{ hint := ⟨f⟩, ty := some piNat, val := .gfn f, decl := .pi .other, recUid := some 0 },
      { hint := ⟨"n"⟩, ty := some .tNat, val := .abs 0, decl := .other }] }],
    nextAbs := 1, absTy := #[.tNat], absDecl := #[.other], goal := some .tNat, typing := true,
    recStack := [{ fn := .gfn f, entries := #[some 0], cands := [], uid := 0 }], nextRecUid := 1 }

/-- The recorded state agrees with `stF f` on every field the relation and the steps read. -/
def startOk (f : String) (st : MState) : Bool :=
  st.env.size == 2 && st.env[0]!.binds.isEmpty && st.env[0]!.temps.isEmpty && st.env[1]!.temps.isEmpty &&
  st.env[1]!.binds.size == 2 &&
  bindOk st.env[1]!.binds[0]! f (.gfn f) piNat (.pi .other) (some 0) &&
  bindOk st.env[1]!.binds[1]! "n" (.abs 0) .tNat .other none &&
  st.absTy == #[.tNat] && st.nextAbs == 1 && st.nextLoan == 0 && st.goal == some .tNat && st.typing &&
  st.refs.isEmpty && st.etaRefs.isEmpty && st.neutrals.isEmpty && !st.curTail && st.tailDecl.isNone &&
  !st.copying && !st.inPlace && !st.headEval && st.erasedDepth == 0 && st.privateDepth == 0 &&
  st.depth == 0 && st.obsFrame.isNone && st.absDecl.size == 1 && st.nextRecUid == 1 &&
  (match st.recStack with
    | [r] => r.fn == .gfn f && r.entries == #[some 0] && r.cands.isEmpty && r.uid == 0
    | _ => false) &&
  declIs st.absDecl[0]! .other

-- the first recorded state of each function is its body's entry: the same for every body
#guard (entries "Pp").head?.any (startOk "Pp")
#guard (entries "Ip").head?.any (startOk "Ip")
-- and the hand-built state passes the same test
#guard startOk "I" (stF "I")

/-- `I` and `P` as core definitions: accepted by `checkDef`. -/
def defI : Def := { name := "I", hs := [⟨"n"⟩], doms := [.nat], cod := .nat, body := bodyI }
def defP : Def := { name := "P", hs := [⟨"n"⟩], doms := [.nat], cod := .nat, body := bodyP }
#guard isOk (checkDef defI) {} 100000
#guard isOk (checkDef defP) {} 100000

/-! ## `I`'s body from the start state: `S(σ0)` at `Nat`, `n` moved -/

def stI : MState := stF "I"

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
  ColumnB.modeOf (outSt (readN true) (withN v) 100000) == (false, false, false, 0)
-- in `clone`'s mode the read copies: the binding keeps its value
#guard ((outSt (readN true) { withN (.abs 0) with copying := true } 100000).env[1]!.binds.map
  (·.val)) == #[.gfn "I", .abs 0]

end ParGuards

end Ochr.Meaning.Steps.Form
