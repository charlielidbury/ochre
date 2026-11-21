import Ochr.Meaning.Steps.BlockQ
import Ochr.Meaning.Steps.SplitGuards

/-!
# The checker at `Q`'s closed-off block, pinned (lead18, 2026-11-21; compiled, not kernel-checked; docs/31 D137)

Every `#guard` runs the checker. What is pinned: the program (the surface's `S(match …)` is a call of `succFn`; the core
`Q` is accepted); the body's start state (`stQ`'s kernel, the mode); the block's captures (`ckBlockCaps`: `n` by move,
the static join's `[n]` re-rooted); the order of events (the [Entry] access, the read of `n.0` in world `S`, each arm's
return check, the block's call, the read of `n` that the call moves, the close); the block's value `⌈anonQ(σ0)⌉` exactly,
its type `Nat`, and the state after (`endQ`); the body's value `S(⌈anonQ(σ0)⌉) : Nat` and its end state (`endQ`); the
entry conditions (the tail flags, a handed-down reading, `clone`'s mode, an untyped run, a private copy); and, for a
variant with a borrow live across the block and an arm writing through it, what the block captures and leaves.
-/

open Ochr.Test

ochr BlockProbe {
  def Qs (n : Nat) : Nat := S(match n { Z => Z, S m => m })
}

namespace Ochr.Meaning.Steps.Form.ColumnQ.Guards

open Ochr Ochr.Meaning Ochr.Meaning.Steps.Form
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)
open Ochr.Meaning.Steps.Form.ParGuards (declIs bindOk globalOk)
open Ochr.Meaning.Steps.Form.ColumnP.Guards (kernEq)
open Ochr.Meaning.Steps.Form.ColumnI (piNat)

/-! ## The program -/

-- the surface's `S(…)` is a call of `succFn` (docs/31 D124); the core `Q` uses the term former `S`
#guard ParGuards.bodyOf BlockProbe "Qs" == .call Ochr.Surface.succFn [matchQ] false
-- `checkDef` accepts `Q`, leaving exactly its global
#guard isOk (checkDef defQ) {} 100000
#guard match (outSt (checkDef defQ) {} 100000).globals with
  | [g] => g.name == "Q" && g.ty == piNat && g.fn? == some fixQ && g.val == .gfn "Q" && !g.model | _ => false

/-- The trace of `checkDef defQ`. -/
def linesOfQ (cfg : Config) : List String :=
  match runMachine (checkDef defQ) { cfg := cfg } 100000 with
  | (_, _, log) => log.toList.filterMap fun | .line s => some s | _ => none

-- one check of the body: no split at the body's level (no `[Split]` line); the block, then one path end
#guard linesOfQ { trace := true } == ["[Def] Q: goal Nat",
  "[Stuck block] fix _ (n : Nat) : Nat := match n { Z => 0, S _ => n.0 }(#0)", "[Def] Q: path ends with type Nat against goal Nat"]
-- the rules applied, in order: the [Entry] access of the capture; world `Z`'s arm returns `Z`; world `S`'s arm reads
-- (moves) `n.0` and returns `σ1`; the block's call reads (moves) `n` and closes off; the body returns `S(⌈…(σ0)⌉)`
#guard linesOfQ { derivation := true, trace := true } == ["[Def] Q: goal Nat", "[Entry] a place a stuck block would capture",
  "[Read] its declared type is not a copy type: moved out",
  "[Return] a stuck match's arm returns it: 0 : Nat, with 0 place(s) held by borrow",
  "[Return] a stuck match's arm returns it: σ1 : Nat, with 0 place(s) held by borrow",
  "[Stuck block] fix _ (n : Nat) : Nat := match n { Z => 0, S _ => n.0 }(#0)",
  "[Read] its declared type is not a copy type: moved out",
  "[Close] fix _ (n : Nat) : Nat := match n { Z => 0, S _ => n.0 }: a sealed result",
  "[Return] Q returns it: S(⌈(fix _ (n : Nat) : Nat := match n { Z => 0, S _ => n.0 })(σ0)⌉) : Nat, with 0 place(s) held by borrow",
  "[Def] Q: path ends with type Nat against goal Nat"]

/-! ## The body's start state -/

/-- The body's full start state, in `checkFix`'s mode (one [Rec] context, not recursive). -/
def stQm : MState :=
  { stQ with typing := true, recStack := [{ fn := .gfn "Q", entries := #[some 0], cands := [], uid := 0 }], nextRecUid := 1 }

-- the hand-built kernel and mode are those `checkFix` starts a body with one `Nat` parameter in (`ParGuards`)
#guard ParGuards.kernelOk "Q" bodyQ stQ && ParGuards.kernelOk "Q" bodyQ stQm && ParGuards.modeOk "Q" stQm
-- the surface program's recorded start state: the same kernel (but for its body, a call of `succFn`) and mode
#guard (ParGuards.entries BlockProbe "Qs").head?.any fun st =>
  ParGuards.kernelOk "Qs" (.call Ochr.Surface.succFn [matchQ] false) st && ParGuards.modeOk "Qs" st

/-! ## The block: captures, value, type, state after -/

/-- The captures as `ckBlockCaps` reads them (the places `movedPlace` is asked of; the captures with their modes). -/
def capsOk (bc : List Place × List (Place × Nat)) : Bool :=
  bc.1 == [.var 0] && bc.2 == [(.var 0, 2)]

-- `n` is captured by MOVE (mode 2): the arm `S _` moves `n.0`, so the static join moves `n` (K1(a), (e))
#guard isOk (Ochr.Meaning.Steps.ckBlockCaps 1000 matchQ) stQ 100000
#guard capsOk (outVal (Ochr.Meaning.Steps.ckBlockCaps 1000 matchQ) stQ 100000)

/-- The block's code, read off the value the checker returns: no capture of its own, `fix _ (n : Nat) : Nat := matchQ`,
the parameter read `.other` at `Nat`. -/
def anonOk (v : Value) : Bool :=
  match v with
  | .sealed (.call (.val (.clo [] (.fix h [x] [.val .tNat] (.val .tNat) none b) [(d, .tNat)])) [.val (.abs 0)] true) =>
    h.name == "_" && x.name == "n" && b == matchQ && declIs d .other
  | _ => false

/-- The match's run: the value `⌈anonQ(σ0)⌉` (`vQ`, every part checked by `anonOk`), at `Nat`, ending with `endQ`'s kernel. -/
def blockOk (h : Option Value) (st : MState) : Bool :=
  isOk (Ochr.eval 1000 true matchQ h) st 100000 &&
  (outVal (Ochr.eval 1000 true matchQ h) st 100000).1 == vQ &&
  anonOk (outVal (Ochr.eval 1000 true matchQ h) st 100000).1 &&
  (outVal (Ochr.eval 1000 true matchQ h) st 100000).2 == some .tNat &&
  kernEq (outSt (Ochr.eval 1000 true matchQ h) st 100000) endQ

#guard blockOk none stQm && blockOk (some .tNat) stQm
-- the [Rec] context and the mode are as they were
#guard (outSt (Ochr.eval 1000 true matchQ none) stQm 100000).recStack.map (·.cands) == [[]]
-- the table of unknowns after: world `S`'s `σ1 : Nat` is kept, read `.other`, and named by nothing
#guard (outSt (Ochr.eval 1000 true matchQ none) stQm 100000).absTy == #[.tNat, .tNat]
#guard ((outSt (Ochr.eval 1000 true matchQ none) stQm 100000).absDecl.map (declIs · .other)) == #[true, true]
#guard !(vQ.hasAbs 1) && vQ.hasAbs 0

/-! ## The body: `S(⌈anonQ(σ0)⌉) : Nat`, the state `endQ` -/

#guard outVal (Ochr.eval 1000 true bodyQ none) stQm 100000 == (.succ vQ, some .tNat)
#guard outVal (Ochr.eval 1000 true bodyQ (some .tNat)) stQm 100000 == (.succ vQ, some .tNat)
#guard kernEq (outSt (Ochr.eval 1000 true bodyQ none) stQm 100000) endQ
-- in tail position (`checkTail`, as `checkFix` checks the body): one leaf, `k` on `S(⌈anonQ(σ0)⌉) : Nat` at `endQ`
def leavesQ (st : MState) : List (MState × Value × Option Value) :=
  (runMachine (Ochr.checkTail 1000 bodyQ ColumnP.Guards.kRecT) st 100000).2.2.toList.filterMap fun
    | .state _ _ (some (v, T)) s => some (s, v, T)
    | _ => none
#guard match leavesQ stQm with
  | [(s, v, T)] => kernEq s endQ && v == .succ vQ && T == some .tNat
  | _ => false

/-! ## Entry conditions -/

-- the tail flags and a handed-down reading do not move the block
#guard blockOk none { stQm with tailNext := true } && blockOk none { stQm with curTail := true } &&
  blockOk none { stQm with tailDecl := some .other }
-- inside a private copy: the same
#guard blockOk none { stQm with privateDepth := 1 }
-- in `clone`'s mode the block's argument read COPIES `n`: the same value, but `n ↦ σ0` after (the plain mode is assumed)
#guard (outVal (Ochr.eval 1000 true matchQ none) { stQm with copying := true } 100000).1 == vQ
#guard ((outSt (Ochr.eval 1000 true matchQ none) { stQm with copying := true } 100000).env[1]!.binds.map (·.val)) ==
  #[.gfn "Q", .abs 0]
-- an untyped run of the match is stuck: it fails (the enclosing call closes off)
#guard !isOk (Ochr.eval 1000 false matchQ none) stQm 100000
-- a block entered after another world ran names a later unknown: from a state whose counter is at 2, world `S`'s is
-- `σ2` (not in the value), and the end table is `[Nat, Nat, Nat]`
#guard (outVal (Ochr.eval 1000 true matchQ none) { stQm with nextAbs := 2, absTy := #[.tNat, .tNat], absDecl := #[.other, .other] } 100000).1 == vQ
#guard (outSt (Ochr.eval 1000 true matchQ none) { stQm with nextAbs := 2, absTy := #[.tNat, .tNat], absDecl := #[.other, .other] } 100000).absTy.size == 3

/-! ## Places an arm writes, and a borrow live across the block (not in `Q`; pinned for the columns after it)

A place an arm writes is captured by `&` (K1(b)): the block's call takes a fresh borrow of it, which the call consumes,
and the place is left holding a sealed FILL, the program of the block's effect on it (`⌈let c1 = …; anon(σ0, &c1); c1⌉`).
A write through a borrow `y` live across the block captures `*y` by `&` (a reborrow `&*y`): `y` stays live after the block,
and its lender receives the fill when it ends. -/

/-- The trace of `checkDef` of a definition with `Q`'s signature and body `b`. -/
def linesOfDef (b : Term) : List String :=
  match runMachine (checkDef { defQ with name := "W", body := b }) { cfg := { trace := true } } 100000 with
  | (_, _, log) => log.toList.filterMap fun | .line s => some s | _ => none

/-- `let x = Z; S(match n { Z => { x := Z; Z }, S m => m }); x` -/
def bodyWx : Term :=
  .letIn ⟨"x"⟩ .zero (.seq (.succ (.matchNat (.var 1) (.seq (.assign (.var 0) .zero) .zero) (.place (.proj 0 (.var 1)))))
    (.place (.var 0)))
/-- `let x = Z; let y = &x; S(match n { Z => { *y := Z; Z }, S m => m }); x` -/
def bodyWy : Term :=
  .letIn ⟨"x"⟩ .zero (.letIn ⟨"y"⟩ (.borrow (.var 0)) (.seq (.succ (.matchNat (.var 2)
    (.seq (.assign (.deref (.var 0)) .zero) .zero) (.place (.proj 0 (.var 2))))) (.place (.var 1))))

#guard isOk (checkDef { defQ with name := "W", body := bodyWx }) {} 100000
#guard linesOfDef bodyWx == ["[Def] W: goal Nat",
  "[Stuck block] fix _ (n : Nat) (x : &Nat) : Nat := match n { Z => *x := 0; 0, S _ => n.0 }(#1, &#0)",
  "[Def] W: path ends with type Nat against goal Nat"]
#guard isOk (checkDef { defQ with name := "W", body := bodyWy }) {} 100000
#guard linesOfDef bodyWy == ["[Def] W: goal Nat",
  "[Stuck block] fix _ (n : Nat) (y : &Nat) : Nat := match n { Z => *y := 0; 0, S _ => n.0 }(#2, &*#0)",
  "[Def] W: path ends with type Nat against goal Nat"]
-- the written place's content after the block, as the body returns it: the fill
def derivOfDef (b : Term) : List String :=
  match runMachine (checkDef { defQ with name := "W", body := b }) { cfg := { derivation := true } } 100000 with
  | (_, _, log) => log.toList.filterMap fun | .line s => some s | _ => none
#guard (derivOfDef bodyWx).contains
    "[Return] W returns it: ⌈let c1 = 0; (fix _ (n : Nat) (x : &Nat) : Nat := match n { Z => *x := 0; 0, S _ => n.0 })(σ0, &c1); c1⌉ : Nat, with 0 place(s) held by borrow"

end Ochr.Meaning.Steps.Form.ColumnQ.Guards
