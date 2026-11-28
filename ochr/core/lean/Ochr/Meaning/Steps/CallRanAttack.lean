import Ochr.Meaning.Steps.CallStepGuards

/-!
# The checker's in-place run of a callee's body, attacked before the simulation is closed through it (lead40, 2026-11-28)

`CallStep.CallRanSimG` is where the simulation's own induction hypothesis (`Master.IH`) must be applied to a callee's
body for the first time. `Machine.runBodyCore` pushes the callee's frame and runs `eval fuel' false body hint`; the
hypothesis (`Master.EvalAt`, untyped) is about exactly such a run, from a state related to a reference state, with the
reference run at `hintM K ρ hint` (the MEANING of the checker's hint value). This file runs the push on the checker, at the
calls of the columns and at a callee whose body calls another global, and checks each entry condition `EvalAt` asks of
the body's start state on the checker's side (the mode, the frames, the tail flags, the reading handed down, the hint),
and that the body run from that state is the call's.

`pushPhase` is a copy of `runBodyCore` up to the body's `eval` (the depth counter, which no statement reads, left out);
`callAt` runs the real `callFn` from the same call point; the guards compare the two.

**FINDING (the hint; docs/31 D243, REPAIRED by the orchestrator's ruling).** At a callee whose body reads its hint (a
constructor whose parameters are not written, D89) and takes no borrow argument, the checker hands the body
`hintLater piTy ws` (main's D124: the codomain at the arguments, evaluated where it is read, `forceHint`). `BareNone(())`
below: the body `ONone` is run at that hint and builds `ONone[Nat]` (the parameter read off the forced hint). Read as a
value, that sealed `⋄hint` program means `err` (`tyS_hintLater`, kernel-checked: the reference's `.prim` clause fails on
`⋄hint`), and the reference's constructor whose parameters are not written fails at the hint `err` (`runT_bareCtor_err`,
kernel-checked: no record, `ctorOut none`). As `hintM` read every hint as a value, `EvalAt`'s (E4) was FALSE at the body
of `BareNone`, though the reference's run in place (`runBodyRef`, at the codomain) succeeds: the induction hypothesis
could not be applied to that body. Since the ruling `hintM` reads the deferred hint as the deferred codomain,
`K.M.paramTy ρ P ws |ds|`, as `LaterOk` reads a deferred call type (`hintM_hintLater`).
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr CallRanAtk {
  inductive Op (A : Type) := ONone | OSome(v : A)
  def Ip (n : Nat) : Nat := S(n)
  def Two (n : Nat) : Nat := Ip(Ip(n))
  def Wc (r : &Nat) : Nat := clone(*r)
  def Kc (r : &Nat) : &Nat := r
  def R (n : Nat) : Nat by n := match n { Z => Z, S m => R(m) }
  def BareNone (u : Unit) : Op(Nat) := ONone
  def At (a : Nat) (c : Nat) : Unit := (let b = Z; ?)
}

namespace Ochr.Meaning.Steps.Form.CallRanAttack

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)

/-- The checker's state at `At`'s hole: `a ↦ σa` (variable 2), `c ↦ σc` (variable 1), `b ↦ Z` (variable 0). -/
def stA : MState := CallGAttack.holeOf "CallRanAtk" CallRanAtk "At"

#guard stA.env.size == 2 && stA.env[1]!.binds.size == 4
#guard stA.globals.length == 7

/-- The call point of `g(ws)`: the head and the arguments pushed as the top frame's last temporaries (D115). -/
def callPoint (g : String) (ws : List Value) : M Unit := do
  Ochr.pushTemp (.gfn g) none
  for w in ws do Ochr.pushTemp w none

/-- **A copy of `Machine.runBodyCore` up to the body's `eval`** (the depth counter left out): the state the body starts
in, its hint, and the body. -/
def pushPhase (fuel : Nat) (fv : Value) (ws : Array Value) : M (Option Value × Term) := do
  let (cs, t, rd) ← Ochr.fixOf fv
  let .fix self hs ds c _ body := t | Ochr.err "not a fix"
  let pf ← Ochr.paramFlags fuel cs rd ds
  let (pds, cd) ← Ochr.paramDecls fuel cs rd hs ds c
  let pds := if rd.length > cs.length then (rd.drop cs.length).map (·.1) else pds
  let piTy := Value.tPi cs (.pi hs ds c) rd
  let tys ← Ochr.paramTypes fuel piTy ws.toList ((pds.zipIdx.filter (·.1 matches .ref _)).map (·.2))
  let selfTy ← Ochr.funType fuel fv none
  let pds' ← pds.mapM Ochr.refineDecl
  let f0 ← Ochr.topIdx
  Ochr.pushFrame
  Ochr.pushCaps fuel cs rd
  let (fv, ws) ← Ochr.takeCallTemps f0 ws.size
  Ochr.pushBind self (some selfTy) fv false (.pi cd)
  for ((((((h, w), p), pd), A), i), pd') in (((((hs.zip ws.toList).zip pf).zip pds).zip tys.toList).zipIdx).zip pds' do
    Ochr.pushBind h A (Ochr.etaUnit pd w) p pd'
    if A.isNone then
      Ochr.modifyFrame (← Ochr.topIdx) fun fr =>
        { fr with binds := fr.binds.modify (fr.binds.size - 1) ({ · with lazyTy := some (piTy, ws.toList, i) }) }
  let hint ← if ← Ochr.readsHint fuel true false body then do
      if ws.all (fun w => !(w matches .borrow ..)) then pure (some (Ochr.hintLater piTy ws))
      else some <$> Ochr.declCallType fuel piTy ws
    else pure none
  modify fun s => { s with tailNext := true }
  pure (hint, body)

/-- The call point of `g(ws)` from `At`'s hole, after the arguments' own runs (`pre`, e.g. a borrow taken). -/
def atCall (pre : M (List Value)) (g : String) : M (List Value) := do
  let ws ← pre
  callPoint g ws
  pure ws

/-- The body's start: the push from the call point. -/
def start (pre : M (List Value)) (g : String) : M (Option Value × Term) := do
  let ws ← atCall pre g
  pushPhase 1000 (.gfn g) ws.toArray

/-- The body's run from its start (as `runBodyCore` runs it: `withErasedIf` is the identity at a callee of class `0`). -/
def bodyRun (pre : M (List Value)) (g : String) : M (Value × Option Value) := do
  let (hint, body) ← start pre g
  Ochr.eval 1000 false body hint

/-- The real call from the same call point, untyped, type wanted (a `let`'s right-hand side). -/
def callAt (pre : M (List Value)) (g : String) (n : Nat) : M (Value × Option Value) := do
  let ws ← atCall pre g
  modify fun s => { s with wantTy := true }
  Ochr.callFn 1000 false none n (ws.toArray.map fun _ => none) false

/-- The start state, its hint and its body. -/
def stP (pre : M (List Value)) (g : String) : MState := outSt (start pre g) stA 1000000
def hintP (pre : M (List Value)) (g : String) : Option Value := (outVal (start pre g) stA 1000000).1

/-- What `EvalAt` asks of the body's start on the checker's side: the plain mode, a frame (one more than the call
point's), the tail flag set, no reading handed down, no deferral flag, the callee's frame holding `self` and the
parameters, its temporaries none, and the call point's temporaries taken off (D115). -/
def entryOk (pre : M (List Value)) (g : String) (nparams : Nat) : Bool :=
  let st := stP pre g
  st.headEval == false && st.copying == false && st.inPlace == false && st.env.size == stA.env.size + 1 &&
    st.tailNext == true && st.tailDecl.isNone && st.deferCallTy == false &&
    st.env.back!.binds.size == nparams + 1 && st.env.back!.temps.size == 0 &&
    st.env[stA.env.size - 1]!.temps.size == stA.env.back!.temps.size

def none₀ : M (List Value) := pure []
def zero₀ : M (List Value) := pure [.zero]
def unit₀ : M (List Value) := pure [.unit]
/-- `&b`, as the argument's run leaves it: `b` lent, the borrow a value. -/
def borrowB : M (List Value) := do
  let w ← Ochr.borrowPlace 100 (.var 0)
  pure [w]

/-! ## The columns' calls: `Ip(Z)` (`I`), `Two(Z)` (a body calling another global), `R(1)` (a recursive body at a known
argument), `Wc(&b)` (a borrow parameter), `Kc(&b)` (a returned borrow), `BareNone(())` (a body reading its hint) -/

#guard isOk (start zero₀ "Ip") stA 1000000
#guard entryOk zero₀ "Ip" 1
#guard entryOk zero₀ "Two" 1
#guard entryOk (pure [.succ .zero]) "R" 1
#guard entryOk borrowB "Wc" 1
#guard entryOk borrowB "Kc" 1
#guard entryOk unit₀ "BareNone" 1

-- the parameter's type: a borrow parameter's evaluated at the push (`&Nat`), a data parameter's deferred (`lazyTy`)
#guard match (stP borrowB "Wc").env.back!.binds[1]!.ty with | some (.tRef _) => true | _ => false
#guard (stP zero₀ "Ip").env.back!.binds[1]!.ty.isNone && (stP zero₀ "Ip").env.back!.binds[1]!.lazyTy.isSome
-- the borrow argument's holder moves from the caller's temporary into the parameter (D115)
#guard match (stP borrowB "Wc").env.back!.binds[1]!.val with | .borrow _ _ => true | _ => false
-- `self` is the global, at its declared type
#guard match (stP zero₀ "Ip").env.back!.binds[0]!.val, (stP zero₀ "Ip").env.back!.binds[0]!.ty with
  | .gfn "Ip", some (.tPi ..) => true | _, _ => false

-- the hint: none where the body reads none; the deferred codomain where it reads one and no argument is a borrow
#guard (hintP zero₀ "Ip").isNone && (hintP zero₀ "Two").isNone && (hintP borrowB "Wc").isNone
#guard match hintP unit₀ "BareNone" with
  | some (.sealed (.prim "⋄hint" (.val (.tPi ..) :: _))) => true | _ => false

-- the body's run from the copy of the push is the call's: the same value as `callFn` from the same call point
#guard Value.exact (outVal (bodyRun zero₀ "Ip") stA 1000000).1 (.succ .zero)
#guard Value.exact (outVal (callAt zero₀ "Ip" 1) stA 1000000).1 (.succ .zero)
#guard Value.exact (outVal (bodyRun zero₀ "Two") stA 1000000).1 (.succ (.succ .zero))
#guard Value.exact (outVal (callAt zero₀ "Two" 1) stA 1000000).1 (.succ (.succ .zero))
#guard Value.exact (outVal (bodyRun (pure [.succ .zero]) "R") stA 1000000).1 .zero
#guard Value.exact (outVal (callAt (pure [.succ .zero]) "R" 1) stA 1000000).1 .zero
#guard Value.exact (outVal (bodyRun borrowB "Wc") stA 1000000).1 .zero
#guard Value.exact (outVal (callAt borrowB "Wc" 1) stA 1000000).1 .zero
#guard match (outVal (bodyRun borrowB "Kc") stA 1000000).1 with | .borrow _ _ => true | _ => false
-- `BareNone`'s body, run at the deferred hint, builds `ONone` recording its parameter `Nat` (read off the forced hint)
#guard match (outVal (bodyRun unit₀ "BareNone") stA 1000000).1 with
  | .ind "Op" _ _ [.tNat] [] => true | _ => false
#guard match (outVal (callAt unit₀ "BareNone" 1) stA 1000000).1 with
  | .ind "Op" _ _ [.tNat] [] => true | _ => false
-- and run at no hint the same body builds `ONone` recording no parameter: the deferred hint is what the run reads
#guard match (outVal (do let (_, body) ← start unit₀ "BareNone"; Ochr.eval 1000 false body none) stA 1000000).1 with
  | .ind "Op" _ _ [] [] => true | _ => false

/-! ## The model's side of the finding, kernel-checked -/

/-- **The reference's run of D124's deferred hint fails**: `⋄hint` is no primitive of the model (`runT`'s last `.prim`
clause). -/
theorem runT_hintLater (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (P : Value) (ws : Array Value)
    (s : SState) : runT K ρ φ tl h (.prim "⋄hint" (.val P :: ws.toList.map Term.val)) s = none := by
  rw [runT] <;> first | rfl | (intros; simp_all)

/-- **D124's deferred hint, read as a value, means `err`** (the record of docs/31 D243's finding): before the ruling,
`hintM` read every hint as a type value (`Value.tyS`), so the hint `EvalAt` handed the reference's run of a callee's body
whose checker run got `hintLater piTy ws` was the meaning of that sealed `⋄hint` program, `err`, not the codomain at the
arguments. -/
theorem tyS_hintLater (K : RunCtx) (ρ : Assignment) (P : Value) (ws : Array Value) :
    Value.tyS K.dm K.M K.Γ ρ (Ochr.hintLater P ws) = .plain TyM.err := by
  show TyS.plain (Value.mean K.dm (codeMeaning K) K.Γ ρ (fun _ => .err) (.plain TyM.err) (Ochr.hintLater P ws)).asTy = _
  rw [meanV_eq_mean K ρ]
  unfold Ochr.hintLater
  rw [meanV]
  simp only [runT_hintLater]
  rfl

/-- D124's deferred hint taken apart: the function type and the arguments it was made of. -/
theorem deferredHint?_hintLater (P : Value) (ws : Array Value) :
    deferredHint? (Ochr.hintLater P ws) = some (P, ws.toList) := by
  unfold Ochr.hintLater deferredHint?
  simp only [List.filterMap_map, Option.some.injEq, Prod.mk.injEq, true_and]
  have : (Term.val? ∘ Term.val) = (some : Value → Option Value) := funext fun _ => rfl
  rw [this, List.filterMap_some]

/-- **Since the ruling on D243, `hintM` reads D124's deferred hint as what it defers**: the codomain of the function type
at the arguments, as `LaterOk` reads a deferred call type. -/
theorem hintM_hintLater (K : RunCtx) (ρ : Assignment) (P : Value) (ws : Array Value) :
    hintM K ρ (some (Ochr.hintLater P ws)) = K.M.paramTy ρ P ws.toList (piArity P) :=
  Master.hintM_of_some (deferredHint?_hintLater P ws)

/-- **The reference's constructor whose parameters are not written fails at the hint `err`** (D89's case: no field
determines a parameter): no record from the hint, none from the fields, so `ctorOut none`. With `tyS_hintLater`:
at `BareNone`'s body, run by the checker at `hintLater` (above), the reference's run at that hint read as a value fails, so
`EvalAt`'s (E4) was false there before the ruling on D243, while the run in place (`runBodyRef`, at the codomain) succeeds. -/
theorem runT_bareCtor_err (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (ty : String) (c : Nat) (h : Hint)
    (d : IndDecl) (s : SState) (hd : K.Γ.find? (·.name == ty) = some d) (hp : d.params ≠ [])
    (hfl : K.D.flags (scopeOf s) (.ctor ty c h [] []) = (false, false)) :
    runT K ρ φ tl (.plain TyM.err) (.ctor ty c h [] []) s = none := by
  rw [runT]
  simp only [hfl, SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  have hpe : d.params.isEmpty = false := by
    cases e : d.params with
    | nil => exact absurd e hp
    | cons _ _ => rfl
  have hall : ((List.replicate d.params.length (none : Option Sem)).all fun x => x.isSome) = false := by
    cases e : d.params with
    | nil => exact absurd e hp
    | cons _ _ => simp [List.replicate_succ]
  simp only [hd, runParams, runFields, pure, bind, StateT.bind, List.isEmpty_nil, Bool.not_true, Bool.false_or, hpe,
    Bool.false_eq_true, if_false, TyS.data]
  have hdr : (TyS.plain TyM.err).m.dataRec? = none := rfl
  simp only [hdr, hall, if_true, true_or, Bool.false_eq_true, if_false]
  rfl

end Ochr.Meaning.Steps.Form.CallRanAttack
