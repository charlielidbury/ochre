import Ochr.Meaning.Steps.CallStep
import Ochr.Meaning.Steps.MachineMono

/-!
# The checker's in-place call simulated, through the induction hypothesis (lead40, 2026-11-28; docs/31 D244)

`CallStep.CallRanSimG` (the paper's case 1, its body step): the checker's run of a call of an accepted global with a
frame-free body is simulated by the reference's run in place (`runCallRef`), or, closed off, by `callOf`. This is the
first place the simulation's own induction hypothesis (`Master.IH`) is applied THROUGH a call: `callFn` →
`runBody` → `runBodyCore` pushes the callee's frame and runs `eval (n - 3) false body hint`, exactly a run `EvalAt`
(untyped) is about.

**What is proved here** (`callRanSimG_of`): `CallRanSimG` from the induction hypothesis at the body and named facts:
- `CallEnterG` (MIXED): the call closed off and simulated by `callOf` (the closed-off half, D206, not separately
  stated), or the body's start `stP` reached, with every entry condition of `EvalAt` at it against the reference's
  in-place push (`inStart … (callPre …)`), the body's run from it, and the rest of the call (`exitM`, a copy of the
  checker's code after the body) from its end; and the hint the checker hands the body (`BodyHint`: none, deferred,
  computed at the call);
- the hint, case by case, read as the reference's codomain at the arguments (`fbG`'s): `HintNoneG` (MODEL, N9's
  reference half: a body the checker reads no hint in runs alike at any hint), `HintDeferredG` (MODEL: the deferred
  codomain, `paramTy`, is the forming state's codomain), `HintComputedG` (MIXED, C2 at the codomain);
- `CallOfOkG` (MODEL): an accepted global applied to member arguments succeeds (`ApplyMem.callOfL_mem`), which with C1
  (`callInPlace_of`) gives (E4) at the body: the reference's run in place succeeds;
- `CallExitG` (MIXED): from the induction hypothesis's conclusion at the body's end, the checker's pop and tail
  (`exitM`) against `runCallRef`'s (`EndsOk`, `popCallFrame`, `endInto`): `CallConcl` for the run in place;
- C1's own facts, as `callAcceptedFF_of` takes them (`CallPtLocalG`, `AcceptedGlobalG`, `CallPopG`, `FundCtx`,
  `FixEqG`, `GlobalsOk` across `Δ`).
The checker's side of the entry is guarded (`Steps/CallRanAttack`: the copy `pushPhase` at the columns' calls).
-/

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.CallInPlace
  Ochr.Meaning.Steps.Form.FrameEnd

/-! ## The checker's call after the body: a copy of the code -/

/-- What the rest of a call needs from its front (`callFn`, `runBody`, `runBodyCore`): the pop's fuel, the depth to
restore, a model function's counter, whether the body ran erased (a callee of class `1`), the call's type `B`, the label
reserved at a borrow codomain, `callFn`'s fuel for the renaming, the class, the declared result reading, whether the
call's type is deferred, and the function type and arguments. -/
structure ExitData where
  pfuel : Nat
  depth : Nat
  model : Bool
  erased : Bool
  B : Option Value
  g? : Option Nat
  lfuel : Nat
  cls : Nat
  res : DeclInfo
  later : Bool
  piTy : Value
  ws : Array Value

/-- `modify f` when `b`. -/
def optModify (b : Bool) (f : MState → MState) : M Unit := if b then modify f else pure ()

/-- `callFn`'s renaming of the result into the label reserved at a borrow codomain (main's D99): a borrow made before or
in the call ended into `g`; another result ends `g` with nothing; no reservation, nothing. -/
def renameInto (e : ExitData) (r : Value) : M Value :=
  match e.g?, r with
  | some g, .borrow k _ =>
    if k == g then pure r else do
      Ochr.pushTemp r e.B "callFn"
      Ochr.lendEnv e.lfuel (.into k g)
      Ochr.popTemp
  | some g, _ => do
    Ochr.pushTemp r e.B "callFn"
    Ochr.lendEnv e.lfuel (.ended g [])
    Ochr.popTemp
  | none, _ => pure r

/-- **The checker's call after its body's run** (a copy of the code, guarded in `Steps/CallRanSim`'s attack):
`withErasedIf`'s exit; `runBodyCore` after the body (the result checked whole and held below the frame at the call's
type, the frame popped, the depth restored, the result taken back); `runBody`'s model counter; `callFn`'s tail (the
result renamed into the reserved label, D99; the flags; the deferred type; η at `Unit`). -/
def exitM (e : ExitData) (v₀ : Value) : M (Value × Option Value) := do
  optModify e.erased (fun s => { s with erasedDepth := s.erasedDepth - 1 })
  Ochr.wholeReturned v₀
  let f ← Ochr.topIdx
  Ochr.pushTempAt (f - 1) v₀ e.B "runBodyCore"
  Ochr.popFrame e.pfuel
  modify fun s => { s with depth := e.depth }
  let r ← Ochr.popTemp
  optModify e.model (fun s => { s with modelDepth := s.modelDepth - 1 })
  let r ← renameInto e r
  Ochr.setFlags (e.cls != 0, e.cls == 2)
  modify fun s => { s with callTyLater := if e.later then some (e.piTy, e.ws.toList) else none }
  pure (Ochr.etaUnit e.res (if e.cls == 2 then Value.proof else r), e.B)

theorem grows_pushTemp' (v : Value) (T : Option Value) (site : String) : GrowsM (Ochr.pushTemp v T site) :=
  Machine.growsM_of_growsIn fun _ => Machine.growsIn_pushTemp v T site

theorem grows_optModify (b : Bool) (f : MState → MState) (h : ∀ s, TablesGrow s (f s)) : GrowsM (optModify b f) := by
  unfold optModify; cases b
  · exact GrowsM.pure _
  · exact GrowsM.modify h

theorem grows_renameInto (e : ExitData) (r : Value) : GrowsM (renameInto e r) := by
  unfold renameInto
  split
  · split
    · exact GrowsM.pure _
    · exact GrowsM.bind (grows_pushTemp' _ _ _) fun _ => GrowsM.bind (grows_lendEnv _ _) fun _ => grows_popTemp
  · exact GrowsM.bind (grows_pushTemp' _ _ _) fun _ => GrowsM.bind (grows_lendEnv _ _) fun _ => grows_popTemp
  · exact GrowsM.pure _

theorem grows_exitM (e : ExitData) (v₀ : Value) : GrowsM (exitM e v₀) := by
  have ht : ∀ s : MState, TablesGrow s { s with erasedDepth := s.erasedDepth - 1 } :=
    fun _ => ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩
  have ht2 : ∀ (d : Nat) (s : MState), TablesGrow s { s with depth := d } :=
    fun _ _ => ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩
  have ht3 : ∀ s : MState, TablesGrow s { s with modelDepth := s.modelDepth - 1 } :=
    fun _ => ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩
  have ht4 : ∀ (o : Option (Value × List Value)) (s : MState), TablesGrow s { s with callTyLater := o } :=
    fun _ _ => ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩
  unfold exitM
  refine GrowsM.bind (grows_optModify _ _ ht) fun _ => ?_
  refine GrowsM.bind (grows_wholeReturned _) fun _ => ?_
  refine GrowsM.bind grows_topIdx fun _ => ?_
  refine GrowsM.bind (grows_pushTempAt _ _ _ _) fun _ => ?_
  refine GrowsM.bind (grows_popFrame _) fun _ => ?_
  refine GrowsM.bind (GrowsM.modify (ht2 _)) fun _ => ?_
  refine GrowsM.bind grows_popTemp fun _ => ?_
  refine GrowsM.bind (grows_optModify _ _ ht3) fun _ => ?_
  refine GrowsM.bind (grows_renameInto _ _) fun _ => ?_
  refine GrowsM.bind (grows_setFlags _) fun _ => ?_
  exact GrowsM.bind (GrowsM.modify (ht4 _)) fun _ => GrowsM.pure _

/-! ## The hint a called body gets, and the reference's -/

/-- D124's deferred hint taken apart: the function type and the arguments it was made of. -/
theorem deferredHint?_hintLater (P : Value) (ws : Array Value) :
    deferredHint? (Ochr.hintLater P ws) = some (P, ws.toList) := by
  unfold Ochr.hintLater deferredHint?
  simp only [List.filterMap_map, Option.some.injEq, Prod.mk.injEq, true_and]
  have : (Term.val? ∘ Term.val) = (some : Value → Option Value) := funext fun _ => rfl
  rw [this, List.filterMap_some]

/-- **The hint `runBodyCore` hands a called body** (main's D124), at the body's start `stP`: none where the body reads
none (`readsHint`); D124's deferred hint where it reads one and no argument is a borrow; otherwise the codomain computed
at the call (`declCallType`), from a state with the push's frames and Σ. -/
inductive BodyHint (body : Term) (piTy : Value) (ws : Array Value) (stP : MState) : Option Value → Prop
  | none : (∃ f st b st', Runs (Ochr.readsHint f true false body) st b false st') → BodyHint body piTy ws stP none
  | deferred : ws.all (fun w => !(w matches .borrow ..)) = true →
      BodyHint body piTy ws stP (some (Ochr.hintLater piTy ws))
  | computed (T : Value) : (∃ f stH b st', Runs (Ochr.declCallType f piTy ws) stH b T st' ∧ stH.env = stP.env ∧
      stH.globals = stP.globals) → BodyHint body piTy ws stP (some T)

/-- The reference's hint at the body of a call of a global's code: the codomain at the arguments, read at the global's
forming state (`fbG`, the `.fix` clause's; what `runCallRef` runs the body at). -/
noncomputable def refHint (K : RunCtx) (ρ : Assignment) (φ : Future) (ds : List Term) (c : Term) (asR : List Res) : TyS :=
  (fbG K ρ φ ds c).2.1 (asR.map (·.1))

/-- The reference's state at the body's start: `runCallRef`'s reservation at a borrow codomain, then the push. -/
noncomputable def refStart (K : RunCtx) (ρ : Assignment) (φ : Future) (g : String) (ds : List Term) (c : Term)
    (asR : List Res) (sc : SState) : SState :=
  inStart K ρ φ (K.C.global g) ds c asR (callPre c asR sc)

/-! ## The body's start: what the entry gives -/

/-- **The body's start, against the reference's in-place push** (what `CallEnterG` concludes): the extension the front
handed on; `EvalAt`'s entry conditions at the checker's state `stP` (the plain mode, a frame, the tail flag set, no
reading handed down, `Pre`, `Rel` with the reference's `refStart`); the global's code holds no embedded value and no
hole; the hint the checker hands (`BodyHint`), naming only the call point's unknowns. -/
structure CallEntry (K : RunCtx) (φ : Future) (Δ : Nat → TyS) (ρ : Assignment) (π : Nat → Nat) (stc : MState)
    (sc : SState) (g : String) (ws : Array Value) (asR : List Res) (sf : Hint) (hs : List Hint) (ds : List Term)
    (c : Term) (dec : Option Nat) (body : Term) (stP : MState) (hint : Option Value) (ρ₁ : Assignment)
    (Δ₁ : Nat → TyS) (π₁ : Nat → Nat) : Prop where
  ext : Ext { K with Δ := Δ } ρ π stc stP ρ₁ Δ₁ π₁
  mode : ModeR stP
  size : 0 < stP.env.size
  tail : stP.tailNext = true
  decl : stP.tailDecl = none
  pre : Pre { K with Δ := Δ₁ } ρ₁ stP
  rel : Rel { K with Δ := Δ₁ } ρ₁ φ π₁ stP (refStart { K with Δ := Δ } ρ φ g ds c asR sc)
  noVal : (Term.fix sf hs ds c dec body).anyAtom (fun _ => true) = false
  hole : body.hasHolePrim = false
  hform : BodyHint body (.tPi [] (.pi hs ds c) []) ws stP hint
  hintBelow : HintBelow hint stc.absTy.size

/-- **The exit data fits the front** (what `CallEnterG` concludes of `exitM`'s data): a label is reserved exactly at a
borrow codomain, and it is the reference's `callPre`'s fresh label under the renaming. -/
structure ExitFits (π₁ : Nat → Nat) (sc : SState) (c : Term) (e : ExitData) : Prop where
  reserve : e.g?.isSome = (match c with | .ref _ => true | _ => false)
  label : ∀ g₀, e.g? = some g₀ → π₁ g₀ = sc.nextLoan

/-! ## The named facts -/

/-- **The call's front and the push** (MIXED; the paper's case 1, steps 1 and 2; with the closed-off half). From
`CallRanSimG`'s hypotheses, either the call closed off and is simulated by `callOf` (the closed-off half, D206's
`CallClosedG`, unchanged, not separately stated), or the checker reached the body's start `stP` (`runBodyCore`'s push
after `callFn`'s front: [Call-type] and [Rec] on private copies, [Lend]'s marks at the reserved label), with every entry
condition of `EvalAt` there against the reference's push (`CallEntry`), the body ran from it, and the rest of the call is
`exitM`, whose data fits the front (`ExitFits`). The checker's side guarded (`Steps/CallRanAttack`, `pushPhase`); the
reference's: the push relates by statement transfer (C2) for a type evaluated at the push, by `paramTy` for a deferred
one, the reservation's marks are `callPre`'s fills (pinned at `Kr`, `CallStepGuards`). -/
def CallEnterG (K : RunCtx) (φ : Future) : Prop :=
  ∀ n, IH K φ (n + 1) → ∀ (Δ : Nat → TyS) (ρ : Assignment) (π : Nat → Nat) (g : String) (hd typed : Bool)
    (fT : Option Value) (ws : Array Value) (tys : Array (Option Value)) (cf : CallFlags) (stc st₁ : MState)
    (sc : SState) (asR : List Res) (v : Value) (T? : Option Value) (bh : Nat)
    (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term),
    K.cur.map (·.1) ≠ some g → stc.recStack.any (·.fn == .gfn g) = false → GlobalsOk K stc →
    stc.globals.find? (·.name == g) = some gd → gd.fn? = some (.fix self hs ds c dec body) → lG K hs ds c ≠ 0 →
    body.frameFree = true → ModeR stc → stc.tailNext = false → 0 < stc.env.size →
    CallPt { K with Δ := Δ } ρ φ π stc sc g ws tys (K.C.global g) asR →
    fT = (stc.globals.find? (·.name == g)).map (·.ty) →
    (typed = false → (refCall { K with Δ := Δ } (K.C.global g) asR sc).isSome) →
    DecTab K.D st₁ →
    Runs (Ochr.callFn n typed fT ws.size tys hd none none cf.res cf.fills cf.want cf.defer none) stc bh (v, T?) st₁ →
    (CallConcl K φ Δ ρ π stc st₁ (callOf K.dm.read (K.C.global g) asR) sc v T? cf typed ∧ Kept stc st₁) ∨
    ∃ (m : Nat) (stP stE : MState) (hint : Option Value) (ρ₁ : Assignment) (Δ₁ : Nat → TyS) (π₁ : Nat → Nat)
      (v₀ : Value) (T₀ : Option Value) (b b' : Nat) (e : ExitData),
      m < n + 1 ∧ CallEntry K φ Δ ρ π stc sc g ws asR self hs ds c dec body stP hint ρ₁ Δ₁ π₁ ∧
      Runs (Ochr.eval m false body hint) stP b (v₀, T₀) stE ∧ Runs (exitM e v₀) stE b' (v, T?) st₁ ∧
      ExitFits π₁ sc c e

/-- **The pop and the tail** (MIXED; the paper's case 1, steps 4 and 5). From `CallRanSimG`'s hypotheses, the body's
start (`CallEntry`), the induction hypothesis's conclusion at the body's end (the reference's body run in place at its
codomain, the result's meaning and label, `Pre` and `Rel` with the result held, `Kept`), and the checker's `exitM` from
there: the call is simulated by the reference's run in place (`runCallRef`: the pop's strict ends `EndsOk` and
`popCallFrame`, then `endInto` at a borrow codomain). Its parts, by reading: `wholeReturned` and the checker's ends over
whole contents make the reference's strict ends pass (D98, N7); `popFrame`'s drops (newest binding first) against
`popEnds` in label order (commutation of ends, `RelendComm`); the result moved from the callee's frame to the caller's
(`pushTempAt`, `popTemp` against `popCallFrame`'s re-park); `renameInto` against `endInto` (D99; `ExitFits`); η at
`Unit`; the deferred type (`callTyLater`) and the call's type `B` against the codomain at the arguments. -/
def CallExitG (K : RunCtx) (φ : Future) : Prop :=
  ∀ n (Δ : Nat → TyS) (ρ : Assignment) (π : Nat → Nat) (g : String) (hd typed : Bool)
    (fT : Option Value) (ws : Array Value) (tys : Array (Option Value)) (cf : CallFlags) (stc st₁ : MState)
    (sc : SState) (asR : List Res) (v : Value) (T? : Option Value) (bh : Nat)
    (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term)
    (stP stE : MState) (hint : Option Value) (ρ₁ : Assignment) (Δ₁ : Nat → TyS) (π₁ : Nat → Nat)
    (v₀ : Value) (T₀ : Option Value) (b' : Nat) (e : ExitData)
    (ρ₂ : Assignment) (Δ₂ : Nat → TyS) (π₂ : Nat → Nat) (r : Res) (s₂ : SState),
    K.cur.map (·.1) ≠ some g → stc.recStack.any (·.fn == .gfn g) = false → GlobalsOk K stc →
    stc.globals.find? (·.name == g) = some gd → gd.fn? = some (.fix self hs ds c dec body) → lG K hs ds c ≠ 0 →
    body.frameFree = true → ModeR stc → stc.tailNext = false → 0 < stc.env.size →
    CallPt { K with Δ := Δ } ρ φ π stc sc g ws tys (K.C.global g) asR →
    fT = (stc.globals.find? (·.name == g)).map (·.ty) → DecTab K.D st₁ →
    Runs (Ochr.callFn n typed fT ws.size tys hd none none cf.res cf.fills cf.want cf.defer none) stc bh (v, T?) st₁ →
    CallEntry K φ Δ ρ π stc sc g ws asR self hs ds c dec body stP hint ρ₁ Δ₁ π₁ → ExitFits π₁ sc c e →
    Ext { K with Δ := Δ₁ } ρ₁ π₁ stP stE ρ₂ Δ₂ π₂ →
    runT { K with Δ := Δ } ρ φ true (refHint { K with Δ := Δ } ρ φ ds c asR) body
      (refStart { K with Δ := Δ } ρ φ g ds c asR sc) = some (r, s₂) →
    meanV { K with Δ := Δ₂ } ρ₂ (fun l => φ (π₂ l)) r.2 v₀ = r.1 → r.2.label = (Value.heldLabel v₀).map π₂ →
    Pre { K with Δ := Δ₂ } ρ₂ (stE.withTempT v₀ T₀) → Rel { K with Δ := Δ₂ } ρ₂ φ π₂ (stE.withTempT v₀ T₀) s₂ →
    Kept stP stE → Runs (exitM e v₀) stE b' (v, T?) st₁ →
    CallConcl K φ Δ ρ π stc st₁ (runCallRef { K with Δ := Δ } ρ φ (K.C.global g) [] (.fix self hs ds c dec body) [] asR)
      sc v T? cf typed ∧ Kept stc st₁

/-- **N9's reference half at a called body** (MODEL; read true): a body holding no embedded value and no hole, in which
the checker reads no hint (`readsHint` false: no constructor whose parameters are not written in tail position), runs alike
at every hint in tail position, its result's type included. The reference hands hints exactly where the typed check does
(D119, D156, D172); a tail's hint reaches only a bare constructor, an embedded value and `rewrite`'s term. -/
def HintNoneG (K : RunCtx) (φ : Future) : Prop :=
  ∀ (Δ : Nat → TyS) (ρ : Assignment) (body : Term) (h : TyS) (s : SState),
    body.anyAtom (fun _ => true) = false → body.hasHolePrim = false →
    (∃ f st b st', Runs (Ochr.readsHint f true false body) st b false st') →
    runT { K with Δ := Δ } ρ φ true (.plain .err) body s = runT { K with Δ := Δ } ρ φ true h body s

/-- **The deferred codomain is the forming state's** (MODEL; read true): at a call of a global's code (no captures, no
embedded value) whose arguments are no borrows, the deferred codomain (`paramTy` past the last domain, read at the
arguments' values under the constant future) is the codomain the `.fix` clause reads at the arguments' meanings at the
global's forming state (`fbG`). By reading: `stateOf 0 (capsState [] [])` is `formG`; the type runs from a state with no
label read no future (`RunCongr.runT_congrE`); the arguments are loan-free (WF5) and record their parameters, so their
meanings are the reference's (`CallPt.mean`) at every future and hint. -/
def HintDeferredG (K : RunCtx) (φ : Future) : Prop :=
  ∀ (Δ : Nat → TyS) (ρ : Assignment) (π : Nat → Nat) (stc : MState) (sc : SState) (g : String) (ws : Array Value)
    (tys : Array (Option Value)) (asR : List Res) (hs : List Hint) (ds : List Term) (c : Term),
    CallPt { K with Δ := Δ } ρ φ π stc sc g ws tys (K.C.global g) asR →
    (Term.pi hs ds c).anyAtom (fun _ => true) = false → ws.all (fun w => !(w matches .borrow ..)) = true →
    ({ K with Δ := Δ }).M.paramTy ρ (.tPi [] (.pi hs ds c) []) ws.toList ds.length =
      refHint { K with Δ := Δ } ρ φ ds c asR

/-- **C2 at the codomain** (MIXED; statement transfer, docs/18 case 2): the codomain the checker computes at the push
(`declCallType`, at a call with a borrow argument) means the reference's codomain at the arguments, read at the global's
forming state. By reading: `declCallType` binds the parameters to the arguments in a frame of its own and evaluates the
codomain on a private copy; its run is simulated by the reference's at the related state (the induction hypothesis, at
the type, at a smaller fuel), and that run reads the caller's frames only through an `Id` in the codomain (D230: an
observation sees every position), which is statement transfer proper. -/
def HintComputedG (K : RunCtx) (φ : Future) : Prop :=
  ∀ (Δ : Nat → TyS) (ρ : Assignment) (π : Nat → Nat) (stc : MState) (sc : SState) (g : String) (ws : Array Value)
    (tys : Array (Option Value)) (asR : List Res) (hs : List Hint) (ds : List Term) (c : Term) (stP : MState)
    (T : Value) (ρ₁ : Assignment) (Δ₁ : Nat → TyS) (π₁ : Nat → Nat),
    CallPt { K with Δ := Δ } ρ φ π stc sc g ws tys (K.C.global g) asR →
    Ext { K with Δ := Δ } ρ π stc stP ρ₁ Δ₁ π₁ → Pre { K with Δ := Δ₁ } ρ₁ stP →
    (∃ f stH b st', Runs (Ochr.declCallType f (.tPi [] (.pi hs ds c) []) ws) stH b T st' ∧ stH.env = stP.env ∧
      stH.globals = stP.globals) →
    hintM { K with Δ := Δ₁ } ρ₁ (some T) = refHint { K with Δ := Δ } ρ φ ds c asR

/-- **An accepted global's call at member arguments succeeds** (MODEL; read true: `ApplyMem.callOfL_mem` and
`callOfL_mem_ref` at the global's level, its meaning a member, `AcceptedGlobalG`, its codomain defined at member
arguments, `FnGoodG`/`PiCallable`). -/
def CallOfOkG (K : RunCtx) (φ : Future) : Prop :=
  ∀ (Δ : Nat → TyS) (ρ : Assignment) (π : Nat → Nat) (g : String) (ws : Array Value) (tys : Array (Option Value))
    (stc : MState) (sc : SState) (asR : List Res) (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term)
    (dec : Option Nat) (body : Term),
    stc.globals.find? (·.name == g) = some gd → K.cur.map (·.1) ≠ some g → gd.fn? = some (.fix self hs ds c dec body) →
    CallPt { K with Δ := Δ } ρ φ π stc sc g ws tys (K.C.global g) asR →
    DomMembers K.dm.read (psG { K with Δ := Δ } ρ φ ds) (asR.map (·.1)) →
    BorrowArgsTyped K.dm.read (K.C.global g) asR sc →
    (callOf K.dm.read (K.C.global g) asR sc).isSome

/-! ## The reference's run in place, taken apart at the body -/

/-- **The body's run in place succeeds where the call in place does** (`runCallRef` at a global's code: the reservation
at a borrow codomain is `callPre`'s, the push is `inStart`, the hint `refHint`). -/
theorem body_isSome_of_runCallRef (K : RunCtx) (ρ : Assignment) (φ : Future) (fres : Res) (self : Hint) (hs : List Hint)
    (ds : List Term) (c : Term) (dec : Option Nat) (body : Term) (args : List Res) (s : SState)
    (h : (runCallRef K ρ φ fres [] (.fix self hs ds c dec body) [] args s).isSome) :
    (runT K ρ φ true ((fbG K ρ φ ds c).2.1 (args.map (·.1))) body (inStart K ρ φ fres ds c args (callPre c args s))).isSome := by
  have key : ∀ s', (runBodyRef K ρ φ fres [] (.fix self hs ds c dec body) [] args s').isSome →
      (runT K ρ φ true ((fbG K ρ φ ds c).2.1 (args.map (·.1))) body (inStart K ρ φ fres ds c args s')).isSome := by
    intro s' h'
    unfold runBodyRef at h'
    simp only at h'
    split at h'
    · rename_i r R s₁ heq
      have e : runT K ρ φ true ((fbG K ρ φ ds c).2.1 (args.map (·.1))) body (inStart K ρ φ fres ds c args s') =
          some ((r, R), s₁) := heq
      rw [e]; rfl
    · simp at h'
  cases c with
  | ref U =>
    apply key
    have e : callPre (.ref U) args s = (s.freshLoan.2).setLent s.freshLoan.1
        (((args.filterMap (·.2.label)).flatMap s.lent).map fun x : Site => { x with fill := true }) := rfl
    rw [e]
    unfold runCallRef at h
    simp only at h
    cases hb : runBodyRef K ρ φ fres [] (.fix self hs ds (.ref U) dec body) [] args
      ((s.freshLoan.2).setLent s.freshLoan.1
        (((args.filterMap (·.2.label)).flatMap s.lent).map fun x : Site => { x with fill := true })) with
    | none => rw [hb] at h; simp at h
    | some p => rfl
  | _ => exact key s h

/-! ## The hint, case by case -/

/-- A term holding no embedded value names no unknown. -/
theorem noAbs_of_noVal {t : Term} (h : t.anyAtom (fun _ => true) = false) (σ : Nat) :
    t.anyAtom (· == .abs σ) = false := by
  cases e : t.anyAtom (· == .abs σ)
  · rfl
  · have := Term.anyAtom_mono (P := (· == .abs σ)) (Q := fun _ => true) (fun _ _ => rfl) t e
    rw [h] at this; cases this

/-- The global's code holding no embedded value: neither does its body, nor its function type's terms. -/
theorem noVal_parts {self : Hint} {hs : List Hint} {ds : List Term} {c : Term} {dec : Option Nat} {body : Term}
    (h : (Term.fix self hs ds c dec body).anyAtom (fun _ => true) = false) :
    body.anyAtom (fun _ => true) = false ∧ (Term.pi hs ds c).anyAtom (fun _ => true) = false := by
  simp only [Term.anyAtom, Bool.or_eq_false_iff] at h ⊢
  exact ⟨h.2, h.1.1, h.1.2⟩

/-- **The body runs alike at the checker's hint, read by `hintM` at the push's context, and at the reference's
codomain at the arguments**, in each of the three ways `runBodyCore` hands it a hint: none (`HintNoneG`), deferred
(`hintM`'s reading since docs/31 D243 with `paramTy_congrA`, then `HintDeferredG`), computed at the call
(`HintComputedG`). The context's change from the call point to the push does not reach the body, which names no unknown
(`runT_congrA`). -/
theorem hint_run {K : RunCtx} {φ : Future} (hhn : HintNoneG K φ) (hhd : HintDeferredG K φ) (hhc : HintComputedG K φ)
    {Δ : Nat → TyS} {ρ : Assignment} {π : Nat → Nat} {stc : MState} {sc : SState} {g : String} {ws : Array Value}
    {tys : Array (Option Value)} {asR : List Res} {self : Hint} {hs : List Hint} {ds : List Term} {c : Term}
    {dec : Option Nat} {body : Term} {stP : MState} {hint : Option Value} {ρ₁ : Assignment} {Δ₁ : Nat → TyS}
    {π₁ : Nat → Nat}
    (hcp : CallPt { K with Δ := Δ } ρ φ π stc sc g ws tys (K.C.global g) asR)
    (hE : CallEntry K φ Δ ρ π stc sc g ws asR self hs ds c dec body stP hint ρ₁ Δ₁ π₁) (s : SState) :
    runT { K with Δ := Δ₁ } ρ₁ φ true (hintM { K with Δ := Δ₁ } ρ₁ hint) body s =
      runT { K with Δ := Δ } ρ φ true (refHint { K with Δ := Δ } ρ φ ds c asR) body s := by
  obtain ⟨hext, -, -, -, -, hpre, -, hnoVal, hhole, hform, hhb⟩ := hE
  obtain ⟨hnv, hpi⟩ := noVal_parts hnoVal
  have hcong : ∀ h, runT { K with Δ := Δ₁ } ρ₁ φ true h body s = runT { K with Δ := Δ } ρ φ true h body s := fun h =>
    (runT_congrA { K with Δ := Δ } Δ₁ ρ ρ₁ φ true body h s
      (fun σ hσ => by rw [noAbs_of_noVal hnv σ] at hσ; cases hσ)).symm
  rw [hcong]
  cases hform with
  | none hr => exact hhn Δ ρ body _ s hnv hhole hr
  | deferred hnb =>
    rw [hintM_of_some (deferredHint?_hintLater _ _)]
    have hag : ∀ σ, Value.anyAtomList (· == .abs σ) ws.toList = true → AgreeA { K with Δ := Δ } Δ₁ ρ ρ₁ σ := by
      intro σ hσ
      have hlt := hhb _ rfl σ ((deferredHint?_atoms (deferredHint?_hintLater (.tPi [] (.pi hs ds c) []) ws) _).2 hσ)
      obtain ⟨a, d⟩ := hext.agree σ hlt
      exact ⟨a.symm, d.symm⟩
    have hP : ∀ σ, (Value.tPi [] (.pi hs ds c) []).anyAtom (· == .abs σ) = true →
        AgreeA { K with Δ := Δ } Δ₁ ρ ρ₁ σ := by
      intro σ hσ
      have h2 := noAbs_of_noVal hpi σ
      simp only [Value.anyAtom, Value.anyAtomList, Value.anyAtomRd, Bool.or_false, Bool.false_or] at hσ
      simp only [Term.anyAtom] at h2
      rcases Bool.or_eq_true_iff.1 hσ with hσ | hσ
      · cases hσ
      · simp only [Term.anyAtom] at hσ; rw [h2] at hσ; cases hσ
    rw [show piArity (.tPi [] (.pi hs ds c) []) = ds.length from rfl,
      ← paramTy_congrA { K with Δ := Δ } Δ₁ ρ ρ₁ _ ws.toList ds.length hP hag]
    rw [hhd Δ ρ π stc sc g ws tys asR hs ds c hcp hpi hnb]
  | computed T hT => rw [hhc Δ ρ π stc sc g ws tys asR hs ds c stP T ρ₁ Δ₁ π₁ hcp hext hpre hT]

/-! ## `CallRanSimG`, through the induction hypothesis -/

/-- **The checker's in-place call simulated, through the induction hypothesis** (docs/31 D244; the paper's case 1 for
an accepted global with a frame-free body): `CallRanSimG` from the induction hypothesis applied to the callee's body at
the push, in the callee's frame, at the hint the checker hands it (each of the three ways), and named facts. The closed-
off half passes through `CallEnterG`. In the in-place half: the reference's start state is good (the frame lemma's start,
`callStartG`, PROVED); (E4), the reference's body run in place succeeding, comes from `callOf`'s success (`CallOfOkG`)
through C1 (`callInPlace_of`), not from the call's hypotheses (which give it only for an untyped call); the body's hint
is the reference's codomain (`hint_run`); the induction hypothesis (`EvalAt` untyped, at the push's context) gives the
body's simulation; the decision table at the body's end from the call's end (`exitM` only extends the tables,
`grows_exitM`); the pop and the tail are `CallExitG`. -/
theorem callRanSimG_of {K : RunCtx} {φ : Future} (hen : CallEnterG K φ) (hex : CallExitG K φ)
    (hhn : HintNoneG K φ) (hhd : HintDeferredG K φ) (hhc : HintComputedG K φ) (hco : CallOfOkG K φ)
    (hpt : CallPtLocalG K φ) (hacc : ∀ st, AcceptedGlobalG K st)
    (hpop : ∀ Δ ρ, CallPopG { K with Δ := Δ } ρ φ) (hfc : ∀ Δ, Strict.FundCtx { K with Δ := Δ })
    (hfix : ∀ Δ st, FixEqG { K with Δ := Δ } st) (hGΔ : ∀ Δ st, GlobalsOk K st → GlobalsOk { K with Δ := Δ } st) :
    CallRanSimG K φ := by
  intro n ih Δ ρ π g hd typed fT ws tys cf stc st₁ sc asR v T? bh gd self hs ds c dec body hcur hns hG hfind hfn hl0
    hff hm htn hsz hcp hfT hok hD hrun
  rcases hen n ih Δ ρ π g hd typed fT ws tys cf stc st₁ sc asR v T? bh gd self hs ds c dec body hcur hns hG hfind hfn
      hl0 hff hm htn hsz hcp hfT hok hD hrun with ⟨hcl, hkept⟩ |
    ⟨m, stP, stE, hint, ρ₁, Δ₁, π₁, v₀, T₀, b, b', e, hmn, hE, hbody, hexit, hfits⟩
  · exact ⟨Or.inr hcl, hkept⟩
  -- C1's data at the call point
  obtain ⟨hgood, hloc, hlw, hsites, hlive, hnd, hdom, hlab, hbt, hheld⟩ :=
    hpt Δ ρ π g ws tys stc sc asR gd self hs ds c dec body hfind hfn hcp
  obtain ⟨hselfV, hselfT, hmem, hv⟩ := hacc stc g gd self hs ds c dec body hfind hcur hfn Δ ρ φ
  have hIP := callInPlace_of { K with Δ := Δ } ρ φ (callStartG _ ρ φ) (hpop Δ ρ) (hfc Δ) stc (hfix Δ stc)
    (hGΔ Δ stc hG) g gd self hs ds c dec body hfind hcur hfn hv hff asR sc hselfV hselfT hmem hgood hloc hlw hsites
    hlive hnd hdom hlab hbt hheld
  -- (E4): `callOf` succeeds, so the call in place does (C1), so the body's run in place does
  have hcoS := hco Δ ρ π g ws tys stc sc asR gd self hs ds c dec body hfind hcur hfn hcp hdom hbt
  have hrc : (runCallRef { K with Δ := Δ } ρ φ (K.C.global g) [] (.fix self hs ds c dec body) [] asR sc).isSome := by
    cases hx' : runCallRef { K with Δ := Δ } ρ φ (K.C.global g) [] (.fix self hs ds c dec body) [] asR sc with
    | some _ => rfl
    | none =>
      rw [hx'] at hIP
      cases hy : callOf K.dm.read (K.C.global g) asR sc with
      | none => rw [hy] at hcoS; cases hcoS
      | some p => rw [hy] at hIP; exact (hIP : False).elim
  have hbR := body_isSome_of_runCallRef { K with Δ := Δ } ρ φ (K.C.global g) self hs ds c dec body asR sc hrc
  -- the reference's start is good: the frame lemma's start (`callStartG`, PROVED)
  have hmem' : selfG { K with Δ := Δ } ρ φ hs ds c dec body ∈ₛ[K.dm.read] piTG { K with Δ := Δ } ρ φ hs ds c := by
    rw [← hselfV, ← hselfT]; exact hmem
  have hstart := callStartG { K with Δ := Δ } ρ φ hs ds c _ _ asR (callPre c asR sc) rfl hmem' hgood hloc hlw hsites
    hlive hnd hdom hlab hheld
  have hSG : Strict.SGood K.dm K.Γ φ (refStart { K with Δ := Δ } ρ φ g ds c asR sc) := by
    unfold refStart
    rw [inStart_fres { K with Δ := Δ } ρ φ (fres' := (selfG { K with Δ := Δ } ρ φ hs ds c dec body,
      .plain (piTG { K with Δ := Δ } ρ φ hs ds c))) hselfV hselfT]
    exact hstart.2.good
  -- the induction hypothesis at the body, at the push's context, untyped, at the checker's hint
  have hH := hint_run hhn hhd hhc hcp hE (refStart { K with Δ := Δ } ρ φ g ds c asR sc)
  obtain ⟨hnv, -⟩ := noVal_parts hE.noVal
  obtain ⟨⟨ρ₂, Δ₂, π₂, r, s₂, hext₂, hx, hmean, -, hlab₂, hpre₂, hrel₂, -, -⟩, hkept⟩ :=
    (ih m hmn Δ₁ ρ₁).1 body stP stE false hint v₀ T₀ (refStart { K with Δ := Δ } ρ φ g ds c asR sc) π₁
      hE.mode (fun h => by cases h) hE.size (Or.inl hE.decl) hE.pre hE.rel hSG
      (hacc stc g gd self hs ds c dec body hfind hcur hfn Δ₁ ρ₁ φ).2.2.2
      (fun σ hσ => by rw [noAbs_of_noVal hnv σ] at hσ; cases hσ)
      (hE.hintBelow.mono hE.ext.abs) hE.hole
      (fun _ => by rw [hE.tail, hH]; exact hbR)
      (DecTab.of_rest hD (grows_exitM e v₀) hexit) b hbody
  rw [hE.tail, hH] at hx
  -- the pop and the tail
  obtain ⟨hcon, hkept'⟩ := hex n Δ ρ π g hd typed fT ws tys cf stc st₁ sc asR v T? bh gd self hs ds c dec body stP stE
    hint ρ₁ Δ₁ π₁ v₀ T₀ b' e ρ₂ Δ₂ π₂ r s₂ hcur hns hG hfind hfn hl0 hff hm htn hsz hcp hfT hD hrun hE hfits hext₂ hx
    hmean hlab₂ hpre₂ hrel₂ hkept hexit
  exact ⟨Or.inl hcon, hkept'⟩

end Ochr.Meaning.Steps.Form.Master
