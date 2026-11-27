import Ochr.Meaning.Steps.BorrowPar
import Ochr.Meaning.Steps.FrameGuards
import Ochr.Meaning.Steps.SplitGuards

/-!
# The checker on `W` and `K`, pinned (lead18, 2026-11-21; compiled, not kernel-checked; docs/31 D138)

Every `#guard` runs the checker. What is pinned: the programs (the surface resolves to `defW`'s and `defK`'s bodies and
signatures; `checkDef` accepts both, and rejects `*r` for `W`); the body's start state (`stW`'s, `stK`'s kernel, against
the state the checker records); each body's typed run (value, type, end kernel) at every hint and tail flag; the run in
tail position (`checkTail`, as `checkFix` checks the body: one leaf); the return's derivation line; the entry conditions.
-/

open Ochr.Test

ochr BorrowProbeW {
  def Wc (r : &Nat) : Nat := clone(*r)
}
ochr BorrowProbeK {
  def Kc (r : &Nat) : &Nat := r
}
ochr BorrowProbeW0 {
  def Wm (r : &Nat) : Nat := Z
}

namespace Ochr.Meaning.Steps.Form.ColumnW.Guards

open Ochr Ochr.Meaning Ochr.Meaning.Steps.Form Ochr.Surface
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)
open Ochr.Meaning.Steps.Form.ColumnP.Guards (gEq kRecT)

/-- Two bindings agree on what the kernel and the relation read (`ColumnP.Guards.bindEq`, with every reading compared:
`declIs` knows `.other` and `.pi` only, and a borrow parameter is read `.ref .other`). -/
def bindEq (a b : Binding) : Bool :=
  a.hint.name == b.hint.name && a.val == b.val && a.ty == b.ty && a.decl == b.decl && a.proof == b.proof &&
    a.recUid == b.recUid && a.cap == b.cap && a.lazyTy.isNone && b.lazyTy.isNone

def frameEq (a b : Frame) : Bool :=
  a.binds.size == b.binds.size && (a.binds.zip b.binds).all (fun (x, y) => bindEq x y) && a.temps == b.temps

/-- Two states have the same kernel (`ColumnP.Guards.kernEq` with every reading compared). -/
def kernEq (a b : MState) : Bool :=
  a.env.size == b.env.size && (a.env.zip b.env).all (fun (x, y) => frameEq x y) &&
    a.globals.length == b.globals.length && (a.globals.zip b.globals).all (fun (x, y) => gEq x y) &&
    a.inds.isEmpty && b.inds.isEmpty && a.nextLoan == b.nextLoan && a.nextAbs == b.nextAbs && a.absTy == b.absTy &&
    a.absDecl == b.absDecl && a.refs == b.refs && a.etaRefs == b.etaRefs && a.neutrals == b.neutrals &&
    a.goal == b.goal && a.liveScope == b.liveScope

/-- The resolved definition of a declaration of a block. -/
def defOf (b : Block) (name : String) : Option Def :=
  match b.decls.find? (·.name == name) with
  | some d => match runResolve b.decls d 100000 with
    | (.ok (.ok (.defn df)), _) => some df
    | _ => none
  | none => none

/-! ## The programs -/

#guard (defOf BorrowProbeW "Wc").any fun d => d.body == bodyW && d.doms == [.ref .nat] && d.cod == .nat && d.dec.isNone
#guard (defOf BorrowProbeK "Kc").any fun d => d.body == bodyK && d.doms == [.ref .nat] && d.cod == .ref .nat && d.dec.isNone
#guard isOk (checkDef defW) {} 100000 && isOk (checkDef defK) {} 100000
#guard match (outSt (checkDef defW) {} 100000).globals with
  | [g] => g.name == "W" && g.ty == piW && g.fn? == some fixW && g.val == .gfn "W" | _ => false
#guard match (outSt (checkDef defK) {} 100000).globals with
  | [g] => g.name == "K" && g.ty == piK && g.fn? == some fixK && g.val == .gfn "K" | _ => false
-- the smaller `*r` is rejected: the read moves the content out of the parameter's borrow, which ends at the return
#guard !isOk (checkDef { defW with body := .place (.deref (.var 0)) }) {} 100000

def linesOf (d : Def) (cfg : Config) : List String :=
  match runMachine (checkDef d) { cfg := cfg } 100000 with
  | (_, _, log) => log.toList.filterMap fun | .line s => some s | _ => none

#guard linesOf defW { derivation := true, trace := true } == ["[Def] W: goal Nat",
  "[Return] W returns it: σ0 : Nat, with 0 place(s) held by borrow", "[Def] W: path ends with type Nat against goal Nat"]
#guard linesOf defK { derivation := true, trace := true } == ["[Def] K: goal &Nat",
  "[Return] K returns it: borrow_0 σ0 : &Nat, with 0 place(s) held by borrow",
  "[Def] K: path ends with type &Nat against goal &Nat"]

/-! ## The body's start state -/

/-- The full start states, in `checkFix`'s mode (no [Rec] context: no `by`; the function's mark taken). -/
def stWm : MState :=
  { stW with typing := true, nextRecUid := 1 }
def stKm : MState :=
  { stK with typing := true, nextRecUid := 1 }

/-- A recorded state with the function renamed to `st0`'s (its binding of itself and its global). -/
def renamed (st0 st : MState) : MState :=
  let sb := st0.env[1]!.binds[0]!
  let fr1 := st.env[1]!
  let b0 := fr1.binds[0]!
  let b0' : Binding := { b0 with hint := sb.hint, val := sb.val, ty := sb.ty }
  { st with globals := st0.globals, env := st.env.set! 1 { fr1 with binds := fr1.binds.set! 0 b0' } }

/-- The recorded entry of the body (frames of sizes `[1, 2]`: the cell, then the function and the parameter), renamed,
has `st0`'s kernel, in `checkFix`'s mode. -/
def entryOk (b : Block) (f : String) (st0 : MState) : Bool :=
  (FrameGuards.entryAt b f [1, 2]).any fun st =>
    kernEq (renamed st0 st) st0 &&
    st.typing && !st.curTail && !st.tailNext && st.tailDecl.isNone && !st.copying && !st.inPlace && st.privateDepth == 0

#guard entryOk BorrowProbeW "Wc" stW && entryOk BorrowProbeK "Kc" stK

/-! ## The bodies' runs -/

def runOk (body : Term) (h : Option Value) (st : MState) (v : Value) (T : Value) (st' : MState) : Bool :=
  isOk (Ochr.eval 1000 true body h) st 100000 && outVal (Ochr.eval 1000 true body h) st 100000 == (v, some T) &&
    kernEq (outSt (Ochr.eval 1000 true body h) st 100000) st'

-- `W`: the content `σ0 : Nat`, in place; at any hint, either tail flag, under a handed-down reading
#guard [none, some .tNat].all fun h => [true, false].all fun tl =>
  runOk bodyW h { stWm with tailNext := tl } vW .tNat stW && runOk bodyW h { stWm with curTail := tl } vW .tNat stW
#guard runOk bodyW none { stWm with tailDecl := some .other } vW .tNat stW
-- `K`: the borrow `borrow₀ σ0 : &Nat`, moved out of `r`
#guard [none, some (.tRef .tNat)].all fun h => [true, false].all fun tl =>
  runOk bodyK h { stKm with tailNext := tl } vK (.tRef .tNat) endK && runOk bodyK h { stKm with curTail := tl } vK (.tRef .tNat) endK
-- in tail position (`checkTail`, as `checkFix` checks a body): one leaf, the same value at the same kernel
def leavesOf (body : Term) (st : MState) : List (MState × Value × Option Value) :=
  (runMachine (Ochr.checkTail 1000 body kRecT) st 100000).2.2.toList.filterMap fun
    | .state _ _ (some (v, T)) s => some (s, v, T)
    | _ => none
#guard match leavesOf bodyW stWm with | [(s, v, T)] => kernEq s stW && v == vW && T == some .tNat | _ => false
#guard match leavesOf bodyK stKm with | [(s, v, T)] => kernEq s endK && v == vK && T == some (.tRef .tNat) | _ => false

/-! ## Entry conditions -/

-- in `clone`'s mode (or in place) `K`'s read of `r` COPIES the borrow instead of moving it (`r` keeps it): the plain mode
-- is assumed
#guard (outVal (Ochr.eval 1000 true bodyK none) { stKm with copying := true } 100000).1 == vK
-- an untyped run reads the same
#guard (outVal (Ochr.eval 1000 false bodyW none) stWm 100000).1 == vW
#guard (outVal (Ochr.eval 1000 false bodyK none) stKm 100000).1 == vK

-- `InvMoveBorrow`'s instance at `K` (docs/31 D145): the checker's end kernel is the start with `r` set to `⊥`, and the
-- value in flight is the borrow `r` held
#guard kernEq endK { stK with env := Env.setAtE stK.env (.bind 1 1) .bot } && valAt stK.env (.bind 1 1) == vK

/-! ## A result holds at most one label (docs/31 D141)

`OutGood` asks a borrow parameter's final at the futures typed for the result (`BodyOut.held`), and the model's result
holds at most one label. So does the checker's: a borrow sits inside no data (core D8, D48; the census in core
DECISIONS rejects a constructor, pair or box of borrows), and `&` is only ever the whole declared type, so a borrow of a
borrow is rejected too. -/
#guard match runMachine (checkDef { defK with name := "KK", doms := [.ref (.ref .nat)], cod := .ref (.ref .nat) }) {} 100000 with
  | (.fail (.error m _), _, _) => m.startsWith "[D48]"
  | _ => false

end Ochr.Meaning.Steps.Form.ColumnW.Guards
