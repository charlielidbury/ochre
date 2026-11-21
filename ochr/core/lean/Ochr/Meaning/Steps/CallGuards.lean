import Ochr.Meaning.Steps.ParGuards

/-!
# The checker at the first call, pinned by running it (lead15, 2026-11-21; docs/31 D127)

The program: `def I (n : Nat) : Nat := S(#0)` (core; `ParGuards.defI`), then
`def J : Nat := I(Z)`, whose core body is `.call (.const "I") [.zero] false`: exactly what the surface
`Jp : Nat := Ip(0)` resolves to (asserted below; the surface's `S(n)` in `Ip`'s body is a call of
`succFn`, docs/31 D124, which does not touch `J`'s body). Every `#guard` runs in the build.

**What the checker does at the call** (`Machine.evalCall`, `callFn`, `runBody`, `runBodyCore`):
- `J`'s body starts (`checkDef`'s constant branch) from one empty frame with `I`'s global in Σ, no
  unknown, no label, goal `none` (the goal is handed as the hint), not in tail position (`stJ`;
  recorded on the surface probe's entry to `Jp`'s body).
- The head `I` and the argument `Z` are evaluated typed (the head with `headEval`), each pushed as a
  temporary of the caller's frame (main's D115), `callType` gives `Nat` (`[Call-type] I(0) : Nat`).
- `runBodyCore` pushes the callee's frame ON TOP OF THE CALLER'S (not a fresh environment): the
  temporaries leave frame 0 as the frame binds them (`takeCallTemps`), `self` is `I ↦ .gfn I` at the
  declared Π-type, read `.pi .other`, NOT marked (at the generic call, `checkFix`, it is marked), the
  parameter is `n ↦ Z` LAZILY TYPED (`ty = none`, `lazyTy = (Π(n : Nat). Nat, [Z], 0)`; at the
  generic call it is stored at `Nat`); then the body runs UNTYPED, in tail position, at call depth 1,
  with no hint (`needsCtx` is false for `S(#0)`). That state is `stCJ` below.
- In the untyped run the read of `n` returns `Z` with NO type (an untyped read of a lazily typed
  binding computes none) and moves `n` (`n ↦ ⊥`); `S` returns `S(Z)` at `Nat`.
- The frame pops; the call returns `S(Z)` at `Nat`; the state is `stJ` again on every field the
  step statements read (one empty frame, no temporary, the counters as they were).
-/

open Ochr.Test

ochr CallProbeJ {
  def Ip (n : Nat) : Nat := S(n)
  def Jp : Nat := Ip(0)
}

namespace Ochr.Meaning.Steps.Form

namespace CallGuards

open Ochr Ochr.Surface
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)
open ParGuards (bodyOf entries bindOk declIs globalOk defI)
open ColumnI (piNat gI)

/-- `J`'s body: the call of the global `I` at `Z`. -/
def bodyJ : Term := .call (.const "I") [.zero] false

-- the surface's `Jp : Nat := Ip(0)` is this call
#guard bodyOf CallProbeJ "Jp" == .call (.const "Ip") [.zero] false

/-- `J` as a core definition (a constant). -/
def defJ : Def := { name := "J", hs := [], doms := [], cod := .nat, body := bodyJ }

#guard match (outSt (checkDef defI) {} 100000).globals with | [g] => globalOk g "I" bodyI | _ => false
-- `ColumnI.gI` is that global
#guard globalOk gI "I" bodyI

/-- The state `checkDef defJ` evaluates `J`'s body from, as `ProgState.step` starts an item (Σ only)
and `checkDef`'s constant branch sets it (one empty frame, no goal, no [Rec] context). -/
def stJ : MState := { env := #[{}], globals := [gI] }

/-- `I` then `J`, from the empty state. -/
def both : M Unit := do checkDef defI; checkDef defJ

#guard isOk both {} 100000
#guard isOk (checkDef defJ) stJ 100000

/-- The trace of `I` then `J` (`Config.trace`, `derivation`: the rules in the paper's names). -/
def linesOf (cfg : Config) : List String :=
  match runMachine both { cfg := cfg } 100000 with
  | (_, _, log) => log.toList.filterMap fun | .line s => some s | _ => none

-- `J`: the call's type, then the callee's body run (indented: call depth 1), whose read moves `n`;
-- `J` is defined as `1`
#guard linesOf { trace := true, derivation := true } ==
  ["[Def] I: goal Nat", "[Read] its declared type is not a copy type: moved out",
    "[Return] I returns it: S(σ0) : Nat, with 0 place(s) held by borrow",
    "[Def] I: path ends with type Nat against goal Nat", "[Call-type] I(0) : Nat",
    "  [Read] its declared type is not a copy type: moved out",
    "[Return] J is defined as it: 1 : Nat, with 0 place(s) held by borrow"]

/-- A constant's body start state with one earlier global named `f` (the global's own fields aside):
one empty frame, nothing else. -/
def startOk (f : String) (st : MState) : Bool :=
  st.env.size == 1 && st.env[0]!.binds.isEmpty && st.env[0]!.temps.isEmpty &&
  st.globals.map (·.name) == [f] && st.inds.isEmpty && st.absTy.isEmpty && st.nextAbs == 0 &&
  st.nextLoan == 0 && st.goal.isNone && st.refs.isEmpty && st.etaRefs.isEmpty && st.neutrals.isEmpty &&
  !st.liveScope && st.absDecl.isEmpty && st.recStack.isEmpty

/-- ... in the plain mode, not in tail position, no reading handed down. -/
def startModeOk (st : MState) : Bool :=
  !st.curTail && !st.tailNext && st.tailDecl.isNone && !st.copying && !st.inPlace && !st.headEval &&
  st.erasedDepth == 0 && st.privateDepth == 0 && st.depth == 0

-- the surface probe's entry to `Jp`'s body, recorded by the checker
#guard (entries CallProbeJ "Jp").head?.any fun st => startOk "Ip" st && startModeOk st
#guard startOk "I" stJ && startModeOk stJ

/-! ## The call, from `stJ`: the run, and the callee's body states (`Config.recordDeep`) -/

def runJ (cfg : Config) := runMachine (Ochr.eval 100 true bodyJ (some .tNat)) { stJ with cfg := cfg } 100000

-- `S(Z)` at `Nat`
#guard outVal (Ochr.eval 100 true bodyJ (some .tNat)) stJ 100000 == (.succ .zero, some .tNat)
-- and the state after is `stJ`'s on every field a step reads
#guard startOk "I" (outSt (Ochr.eval 100 true bodyJ (some .tNat)) stJ 100000) &&
  startModeOk (outSt (Ochr.eval 100 true bodyJ (some .tNat)) stJ 100000)
#guard match (outSt (Ochr.eval 100 true bodyJ (some .tNat)) stJ 100000).globals with
  | [g] => globalOk g "I" bodyI | _ => false

/-- The states at call depth 1, on entry (`false`) and exit (`true`) of each evaluation, with the value
in flight on exit. -/
def deep : List (Bool × Option (Value × Option Value) × MState) :=
  match runJ { recordDeep := true } with
  | (_, _, log) => log.toList.filterMap fun
      | LogEntry.deep ex fl st => some (ex, fl, st) | _ => none

/-- The callee's frame as `runBodyCore` builds it: `self` at the declared Π-type, read `.pi .other`,
unmarked; then `n ↦ w` lazily typed, the deferred type parameter 0 of `I`'s Π-type at `[Z]`. -/
def calleeFrameOk (fr : Frame) (w : Value) : Bool :=
  fr.binds.size == 2 && fr.temps.isEmpty &&
  bindOk fr.binds[0]! "I" (.gfn "I") piNat (.pi .other) none &&
  (let b := fr.binds[1]!
   b.hint.name == "n" && b.val == w && b.ty.isNone && declIs b.decl .other && !b.proof && b.recUid.isNone &&
     !b.cap && b.lazyTy.any fun (P, ws, i) => P == piNat && ws == [.zero] && i == 0)

/-- The callee's state: `stJ`'s frame below (its temporaries taken), the callee's frame on top, the
counters as at the call, at call depth 1. -/
def calleeOk (st : MState) (w : Value) : Bool :=
  st.env.size == 2 && st.env[0]!.binds.isEmpty && st.env[0]!.temps.isEmpty && calleeFrameOk st.env[1]! w &&
  st.absTy.isEmpty && st.nextAbs == 0 && st.nextLoan == 0 && st.goal.isNone && st.depth == 1 &&
  !st.copying && !st.inPlace && !st.headEval && st.erasedDepth == 0 && st.privateDepth == 0 && st.recStack.isEmpty

-- four records: the body's entry, the read's entry, the read's exit, the body's exit
#guard deep.length == 4
-- the body's entry: the callee's state `stCJ`, in tail position (`tailNext`)
#guard match deep with
  | (false, _, st) :: _ => calleeOk st .zero && st.tailNext && !st.curTail && st.tailDecl.isNone
  | _ => false
-- the read of `n`, UNTYPED (`typing` false), as the tail term (`curTail`)
#guard match deep with
  | _ :: (false, _, st) :: _ => calleeOk st .zero && !st.typing && st.curTail
  | _ => false
-- the read returns `Z` with no type and moves `n`
#guard match deep with
  | _ :: _ :: (true, some (v, T), st) :: _ => v == .zero && T.isNone && calleeOk st .bot
  | _ => false
-- the body returns `S(Z)` at `Nat`
#guard match deep with
  | [_, _, _, (true, some (v, T), st)] => v == .succ .zero && T == some .tNat && calleeOk st .bot
  | _ => false

/-- `stCJ`: the callee's state on entry to the body, as recorded (its kernel). -/
def stCJ : MState :=
  { env := #[{}, { binds := #[
      { hint := ⟨"I"⟩, ty := some piNat, val := .gfn "I", decl := .pi .other },
      { hint := ⟨"n"⟩, ty := none, val := .zero, decl := .other, lazyTy := some (piNat, [.zero], 0) }] }],
    globals := [gI], depth := 1, tailNext := true }

#guard calleeOk stCJ .zero
-- the body's untyped run from `stCJ`: `S(Z)` at `Nat`, `n` moved
#guard outVal (Ochr.eval 100 false bodyI none) stCJ 100000 == (.succ .zero, some .tNat)
#guard calleeOk (outSt (Ochr.eval 100 false bodyI none) stCJ 100000) .bot

/-! ## A non-recursive body never reads its own binding (D31)

The callee's frame binds `self` (above), but the checker rejects every read of it in the body of a
function with no decreasing parameter: read whole, called, or bound by a `let`. So in a run of an
accepted non-recursive body nothing reads `self`, in place or in the closure's frame, where the two
bind different values (docs/31 D127). -/

/-- `def f (n : Nat) : B := body` with `body` reading `self` (`#1`: the frame is `[self, n]`). -/
def selfReader (body : Term) (B : Term) : Def := { name := "K", hs := [⟨"n"⟩], doms := [.nat], cod := B, body := body }

def rejectedD31 (d : Def) : Bool :=
  match runMachine (checkDef d) {} 100000 with
  | (.fail (.error m _), _, _) => (m.splitOn "is not in scope in its own body").length > 1
  | _ => false

#guard rejectedD31 (selfReader (.place (.var 1)) (.pi [⟨"m"⟩] [.nat] .nat))
#guard rejectedD31 (selfReader (.call (.place (.var 1)) [.zero] false) .nat)
#guard rejectedD31 (selfReader (.seq (.letIn ⟨"g"⟩ (.place (.var 1)) .tt) .tt) .unit)

end CallGuards

end Ochr.Meaning.Steps.Form
