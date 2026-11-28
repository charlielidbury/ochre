import Ochr.Meaning.Steps.CallStartInv
import Ochr.Meaning.Steps.UnderCheck

/-!
# The step for a call of an accepted global, in place: what it assumes (lead39, 2026-11-28; docs/31 D241)

The brief's task 2. `CallFnG` (`MasterCall`) at a head `g` that is an ACCEPTED global (not under check, not of class
proof) whose body forms no function, function type or `Id` (`Term.frameFree`): the checker's `callFn` runs the body in
place, or closes the call off when the body is stuck. This file states, classed, the facts about the checker's run it
needs, and assembles the branch from them and the model's C1 (`callInPlace_of`, whose start is now proved,
`CallStartInv.callStartG`).

The facts, read against today's checker (`Machine.callFn`, `runBody`, `runBodyCore`, `popFrame`; main through D138):
- `CallRanSimG` (MIXED; the paper's case 1, steps 1 to 5 but the link): the checker's run is simulated by the reference's
  run IN PLACE (`CallRef.runCallRef`: the result label reserved and lent at a borrow codomain, the callee's frame pushed,
  the body, the pop) when the body ran, and by `callOf` when it closed off. Its parts, by reading:
  (i) the front: [Call-type] (typed) and [Rec] (typed) change no reference state; [Lend]'s marks for a label `g₀`
  reserved from the counter are the reference's `callPre` (the fills at the borrow arguments' sites), the renaming
  extended `g₀ ↦ s.nextLoan` (CHECKER: `callFn` reserves `g₀` with `freshLoan` before the body and marks with
  `lendEnv (.mark l g₀)`; pinned by `CallGAttack`'s `Kr`: `borrow_1 0`, `b ↦ lent_1 loan_1`);
  (ii) the push (C2): `runBodyCore` binds `self` at its Π-type and each parameter at its type at the arguments (a
  borrow parameter's at the call point, the others deferred, `lazyTy`), the head and arguments taken off the caller's
  temporaries (D115); the reference's `callFrame` binds them at the binders read at the forming state: equal by
  statement transfer (C2), and the hint (`hintLater`/`declCallType`) means the codomain at the arguments (N9);
  (iii) the body, by the induction hypothesis (`EvalAt` untyped, tail flag set), its (E4) from C1's `callOf` side;
  (iv) the pop (`pushTempAt` at the call's type, `popFrame`, `popTemp`) against `popCallFrame`, the result's label kept
  and every other label of the frame or made by the body ended in both;
  (v) the tail (`callFn` after `r`): the result renamed into `g₀` (`lendEnv (.into k g₀)`, D99) against `runCallRef`'s
  `endInto`; η at `Unit` (`etaUnit res`) against the reference's `Unit` reading; the deferred type (`callTyLater`).
  The closed-off half is lead29's/lead31's `CallClosedG` (D206), unchanged.
- `CallPtLocalG` (MIXED): at a related call point, the reference's state meets C1's hypotheses: goodness, locality,
  well-founded lending (from the checker's acyclic loans through the relation, N5), every site at a position, the
  borrow arguments' labels live and distinct, the arguments members of the domains (typed: [Call-type]; untyped: (E4)),
  labelled exactly at the borrow parameters, `BorrowArgsTyped` (the reference's own strict test) and `ArgsHeld` (D240:
  from `BorrowArgsTyped` and the round trip of codes under the knot's `PiCallable`).
- `AcceptedGlobalG` (MODEL, a clause of the context): an accepted global's meaning is the `.fix` clause's closure at its
  forming state, a member of its type, its body's embedded values good (from `GlobalsOk.fn`, `.mem` and the `.fix`
  clause, `run_fix_def`; by reading).
- `OccursLiveG` (CHECKER, (WF2)): every label occurring in a checker state after a call is live.
And the model's: `CallPopG` (read, D230), `FixEqG` (from `RecDescG`, `FnGoodG`: `FixEqDesc.fixEqG_of`).
-/

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.CallInPlace
  Ochr.Meaning.Steps.Form.FrameEnd

/-- **`CallFnG`'s conclusion at a reference run `x` of the call** (`refCall`, the run in place, `callOf`). -/
def CallConcl (K : RunCtx) (φ : Future) (Δ : Nat → TyS) (ρ : Assignment) (π : Nat → Nat) (stc st₁ : MState)
    (x : SM Res) (sc : SState) (v : Value) (T? : Option Value) (cf : CallFlags) (typed : Bool) : Prop :=
  ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (r : Res) (s' : SState),
    Ext { K with Δ := Δ } ρ π stc st₁ ρ' Δ' π' ∧ x sc = some (r, s') ∧
    meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧
    (∀ T, T? = some T → StrAgree { K with Δ := Δ' } ρ' T r.2) ∧
    r.2.label = (Value.heldLabel v).map π' ∧
    Pre { K with Δ := Δ' } ρ' (st₁.withTempT v T?) ∧ Rel { K with Δ := Δ' } ρ' φ π' (st₁.withTempT v T?) s' ∧
    (cf.defer = true → ∀ caps hs ds cod rd ws', st₁.callTyLater = some (.tPi caps (.pi hs ds cod) rd, ws') →
      ({ K with Δ := Δ' }).M.paramTy ρ' (.tPi caps (.pi hs ds cod) rd) ws' ds.length = r.2) ∧
    ((typed = true ∨ (cf.want = true ∧ cf.defer = false)) → T? = none → r.2.m = TyM.err)

/-- **The checker's call of an accepted global, simulated in place or closed off** (MIXED; the parts (i) to (v) of the
module docstring, and `CallClosedG`). At a body in the frame-free fragment (lead40, docs/31 D244: the hypothesis
`frameFree` added, which the in-place branch has and C1 needs, for the body's (E4)); assembled from the induction
hypothesis and named facts in `Steps/CallRanSim` (`callRanSimG_of`). -/
def CallRanSimG (K : RunCtx) (φ : Future) : Prop :=
  ∀ n, IH K φ (n + 1) → ∀ (Δ : Nat → TyS) (ρ : Assignment) (π : Nat → Nat) (g : String) (hd typed : Bool)
    (fT : Option Value) (ws : Array Value) (tys : Array (Option Value)) (cf : CallFlags) (stc st₁ : MState)
    (sc : SState) (asR : List Res) (v : Value) (T? : Option Value) (bh : Nat)
    (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term),
    K.cur.map (·.1) ≠ some g → stc.recStack.any (·.fn == .gfn g) = false → GlobalsOk K stc →
    stc.globals.find? (·.name == g) = some gd → gd.fn? = some (.fix self hs ds c dec body) → lG K hs ds c ≠ 0 →
    body.frameFree = true →
    ModeR stc → stc.tailNext = false → 0 < stc.env.size →
    CallPt { K with Δ := Δ } ρ φ π stc sc g ws tys (K.C.global g) asR →
    fT = (stc.globals.find? (·.name == g)).map (·.ty) →
    (typed = false → (refCall { K with Δ := Δ } (K.C.global g) asR sc).isSome) →
    DecTab K.D st₁ →
    Runs (Ochr.callFn n typed fT ws.size tys hd none none cf.res cf.fills cf.want cf.defer none) stc bh (v, T?) st₁ →
    (CallConcl K φ Δ ρ π stc st₁ (runCallRef { K with Δ := Δ } ρ φ (K.C.global g) [] (.fix self hs ds c dec body) [] asR)
        sc v T? cf typed ∨
      CallConcl K φ Δ ρ π stc st₁ (callOf K.dm.read (K.C.global g) asR) sc v T? cf typed) ∧
    Kept stc st₁

/-- **The reference's call point meets C1's hypotheses** (MIXED; see the module docstring). -/
def CallPtLocalG (K : RunCtx) (φ : Future) : Prop :=
  ∀ (Δ : Nat → TyS) (ρ : Assignment) (π : Nat → Nat) (g : String) (ws : Array Value) (tys : Array (Option Value))
    (stc : MState) (sc : SState) (asR : List Res) (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term)
    (dec : Option Nat) (body : Term),
    stc.globals.find? (·.name == g) = some gd → gd.fn? = some (.fix self hs ds c dec body) →
    CallPt { K with Δ := Δ } ρ φ π stc sc g ws tys (K.C.global g) asR →
    Strict.SGood K.dm K.Γ φ (callPre c asR sc) ∧ SState.RInv (fun _ => False) (callPre c asR sc) ∧
    LendWF (callPre c asR sc) ∧
    (∀ l (y : Site), y ∈ (callPre c asR sc).lent l → y.pos ∈ (callPre c asR sc).positions) ∧
    (∀ a ∈ asR, ∀ l, a.2.label = some l → (callPre c asR sc).Live l) ∧ (argLabels asR).Nodup ∧
    DomMembers K.dm.read (psG { K with Δ := Δ } ρ φ ds) (asR.map (·.1)) ∧
    (∀ (i : Nat) (a : Res) (d : PiDom), asR[i]? = some a → (psG { K with Δ := Δ } ρ φ ds)[i]? = some d →
      (a.2.label.isSome = d.isRef)) ∧
    BorrowArgsTyped K.dm.read (K.C.global g) asR sc ∧ ArgsHeld { K with Δ := Δ } ρ φ ds c asR (callPre c asR sc)

/-- **An accepted global's meaning is its `.fix` closure at its forming state** (MODEL; a clause of the context, by
reading from `GlobalsOk.fn`, `.mem` and `run_fix_def`), at every `Δ`; its body's embedded values are good. -/
def AcceptedGlobalG (K : RunCtx) (st : MState) : Prop :=
  ∀ (g : String) (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term),
    st.globals.find? (·.name == g) = some gd → K.cur.map (·.1) ≠ some g → gd.fn? = some (.fix self hs ds c dec body) →
    ∀ (Δ : Nat → TyS) (ρ : Assignment) (φ : Future),
      (K.C.global g).1 = selfG { K with Δ := Δ } ρ φ hs ds c dec body ∧
      (K.C.global g).2.m = piTG { K with Δ := Δ } ρ φ hs ds c ∧
      (K.C.global g).1 ∈ₛ[K.dm.read] (K.C.global g).2.m ∧ body.valsOk (Strict.ValsP { K with Δ := Δ } ρ φ)

/-- **Every label occurring in a checker state after a call is live** (CHECKER; (WF2) outside a sealed program's run). -/
def OccursLiveG (K : RunCtx) : Prop :=
  ∀ (Δ : Nat → TyS) (ρ : Assignment) (st : MState), Pre { K with Δ := Δ } ρ st →
    ∀ l, st.Occurs l → liveLoan st.env l = true

/-- **The step for a call of an accepted global with a frame-free body** (`CallFnG`'s statement at such a head):
the checker's run is simulated by the reference's call, `refCall` (its strict test, then the callee's meaning applied). -/
def CallAcceptedFF (K : RunCtx) (φ : Future) : Prop :=
  ∀ n, IH K φ (n + 1) → ∀ (Δ : Nat → TyS) (ρ : Assignment) (π : Nat → Nat) (g : String) (hd typed : Bool)
    (fT : Option Value) (ws : Array Value) (tys : Array (Option Value)) (cf : CallFlags) (stc st₁ : MState)
    (sc : SState) (asR : List Res) (v : Value) (T? : Option Value) (bh : Nat)
    (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term),
    K.cur.map (·.1) ≠ some g → stc.recStack.any (·.fn == .gfn g) = false → GlobalsOk K stc →
    stc.globals.find? (·.name == g) = some gd → gd.fn? = some (.fix self hs ds c dec body) → lG K hs ds c ≠ 0 →
    body.frameFree = true →
    ModeR stc → stc.tailNext = false → 0 < stc.env.size →
    CallPt { K with Δ := Δ } ρ φ π stc sc g ws tys (K.C.global g) asR →
    fT = (stc.globals.find? (·.name == g)).map (·.ty) →
    (typed = false → (refCall { K with Δ := Δ } (K.C.global g) asR sc).isSome) →
    DecTab K.D st₁ →
    Runs (Ochr.callFn n typed fT ws.size tys hd none none cf.res cf.fills cf.want cf.defer none) stc bh (v, T?) st₁ →
    CallConcl K φ Δ ρ π stc st₁ (refCall { K with Δ := Δ } (K.C.global g) asR) sc v T? cf typed ∧ Kept stc st₁

/-- **The in-place branch, assembled** (docs/31 D241): from the checker-side simulation `CallRanSimG`, the call point's
reference facts `CallPtLocalG`, the occurring labels' liveness `OccursLiveG`, the context's `AcceptedGlobalG`, and the
model's C1 (`callInPlace_of`, its start PROVED, `callStartG`), which assumes the pop `CallPopG` and the fixpoint equation
`FixEqG`. The run in place and `callOf` agree (C1), so the relation the checker's state has with the run in place's
result transfers to `callOf`'s, which is `refCall`'s once its strict test passes (`BorrowArgsTyped`). -/
theorem callAcceptedFF_of {K : RunCtx} {φ : Future} (hsim : CallRanSimG K φ) (hpt : CallPtLocalG K φ)
    (hocc : OccursLiveG K) (hacc : ∀ st, AcceptedGlobalG K st)
    (hpop : ∀ Δ ρ, CallPopG { K with Δ := Δ } ρ φ) (hfc : ∀ Δ, Strict.FundCtx { K with Δ := Δ })
    (hfix : ∀ Δ st, FixEqG { K with Δ := Δ } st) (hGΔ : ∀ Δ st, GlobalsOk K st → GlobalsOk { K with Δ := Δ } st) :
    CallAcceptedFF K φ := by
  intro n ih Δ ρ π g hd typed fT ws tys cf stc st₁ sc asR v T? bh gd self hs ds c dec body hcur hns hG hfind hfn hl0
    hff hm htn hsz hcp hfT hok hD hrun
  obtain ⟨hdisj, hkept⟩ := hsim n ih Δ ρ π g hd typed fT ws tys cf stc st₁ sc asR v T? bh gd self hs ds c dec body hcur
    hns hG hfind hfn hl0 hff hm htn hsz hcp hfT hok hD hrun
  obtain ⟨hgood, hloc, hlw, hsites, hlive, hnd, hdom, hlab, hbt, hheld⟩ :=
    hpt Δ ρ π g ws tys stc sc asR gd self hs ds c dec body hfind hfn hcp
  have hrefCall : refCall { K with Δ := Δ } (K.C.global g) asR sc = callOf K.dm.read (K.C.global g) asR sc := by
    unfold refCall; exact if_pos hbt
  refine ⟨?_, hkept⟩
  rcases hdisj with ⟨ρ', Δ', π', r, s', hext, hx, hmean, hstr, hlabel, hpre, hrel, hdefer, hmiss⟩ | hcl
  · obtain ⟨hselfV, hselfT, hmem, hv⟩ := hacc stc g gd self hs ds c dec body hfind hcur hfn Δ ρ φ
    have hIP := callInPlace_of { K with Δ := Δ } ρ φ (callStartG _ ρ φ) (hpop Δ ρ) (hfc Δ) stc (hfix Δ stc)
      (hGΔ Δ stc hG) g gd self hs ds c dec body hfind hcur hfn hv hff asR sc hselfV hselfT hmem hgood hloc hlw hsites
      hlive hnd hdom hlab hbt hheld
    rw [hx] at hIP
    cases hco : callOf K.dm.read (K.C.global g) asR sc with
    | none => rw [hco] at hIP; exact hIP.elim
    | some p =>
      obtain ⟨r', s''⟩ := p
      rw [hco] at hIP
      obtain ⟨hrr, htr⟩ := hIP
      subst hrr
      exact ⟨ρ', Δ', π', r, s'', hext, by rw [hrefCall, hco], hmean, hstr, hlabel, hpre,
        htr _ _ _ _ (hocc Δ' ρ' _ hpre) hrel, hdefer, hmiss⟩
  · obtain ⟨ρ', Δ', π', r, s', hext, hx, hrest⟩ := hcl
    exact ⟨ρ', Δ', π', r, s', hext, by rw [hrefCall]; exact hx, hrest⟩

/-! ## The step for a call of a global, composed (the brief's task 3; docs/31 D241) -/

/-- **A call of the function under check happens only while it is on the [Rec] stack** (CHECKER; D31 with D136: a
function without `by` cannot name itself, so no call of `K.cur`'s global is made at its check; with `by` its entry is on
the stack while its body, nested functions and block arms are checked). The other direction of `RecCurG`. -/
def CurOnStackG (K : RunCtx) : Prop :=
  ∀ (stc : MState) (g : String), K.cur.map (·.1) = some g → stc.recStack.any (·.fn == .gfn g) = true

/-- **A call's head `g` is a global with a `fix` code** (CHECKER: `CallPt.temps` holds `.gfn g`, which `evalCall` makes
only for a global function, `lookupGlobal`'s `fn?`), and the call is unerased only where the callee's sort is not `Prop`
(MIXED: the aligned decision `K.D.flags` against the model's sort `lG`). -/
def GlobalFixG (K : RunCtx) (φ : Future) : Prop :=
  ∀ (Δ : Nat → TyS) (ρ : Assignment) (π : Nat → Nat) (g : String) (ws : Array Value) (tys : Array (Option Value))
    (stc : MState) (sc : SState) (asR : List Res),
    CallPt { K with Δ := Δ } ρ φ π stc sc g ws tys (K.C.global g) asR →
    ∃ gd self hs ds c dec body, stc.globals.find? (·.name == g) = some gd ∧ gd.fn? = some (.fix self hs ds c dec body) ∧
      lG K hs ds c ≠ 0

/-- **`CallFnG` with what it needs and lacks** (docs/31 D241): `CallFnG`'s statement with the two entry conditions
the call consumes and `EvalAt` does not carry (`RecCurG` at the call point; `RecRankG` at a typed site, already
`RecRankG`'s docstring's "`EvalAt` is to take it"), the context's `GlobalsOk`, and a callee that is under check or
whose body is frame-free (the frame property is proved for such bodies only, `runFrameI_frameFree`). -/
def CallFnGW (K : RunCtx) (φ : Future) : Prop :=
  ∀ n, IH K φ (n + 1) → ∀ (Δ : Nat → TyS) (ρ : Assignment) (π : Nat → Nat) (g : String) (hd typed : Bool)
    (fT : Option Value) (ws : Array Value) (tys : Array (Option Value)) (cf : CallFlags) (stc st₁ : MState)
    (sc : SState) (asR : List Res) (v : Value) (T? : Option Value) (bh : Nat),
    RecCurG K stc → (typed = true → RecRankG K ρ stc) → GlobalsOk K stc →
    (∀ gd self hs ds c dec body, stc.globals.find? (·.name == g) = some gd → gd.fn? = some (.fix self hs ds c dec body) →
      K.cur.map (·.1) ≠ some g → body.frameFree = true) →
    ModeR stc → stc.tailNext = false → 0 < stc.env.size →
    CallPt { K with Δ := Δ } ρ φ π stc sc g ws tys (K.C.global g) asR →
    fT = (stc.globals.find? (·.name == g)).map (·.ty) →
    (typed = false → (refCall { K with Δ := Δ } (K.C.global g) asR sc).isSome) →
    DecTab K.D st₁ →
    Runs (Ochr.callFn n typed fT ws.size tys hd none none cf.res cf.fills cf.want cf.defer none) stc bh (v, T?) st₁ →
    CallConcl K φ Δ ρ π stc st₁ (refCall { K with Δ := Δ } (K.C.global g) asR) sc v T? cf typed ∧ Kept stc st₁

/-- **The step's call phase, composed** (docs/31 D241): from the step for a call of the function under check
(`CallUnderCheckG`, D205), the in-place branch (`CallAcceptedFF`, assembled above), and the two checker facts that tell
the branches apart (`CurOnStackG`, `GlobalFixG`). -/
theorem callFnGW_of {K : RunCtx} {φ : Future} (hU : CallUnderCheckG K φ) (hA : CallAcceptedFF K φ)
    (hS : CurOnStackG K) (hF : GlobalFixG K φ) : CallFnGW K φ := by
  intro n ih Δ ρ π g hd typed fT ws tys cf stc st₁ sc asR v T? bh hrc hrr hG hff hm htn hsz hcp hfT hok hD hrun
  cases hst : stc.recStack.any (·.fn == .gfn g) with
  | true =>
    obtain ⟨⟨g', b⟩, hcur, hg'⟩ := Option.map_eq_some_iff.1 (hrc g hst)
    have hcur' : K.cur = some (g, b) := by rw [hcur]; simp only at hg'; rw [hg']
    exact hU n ih Δ ρ π g b hd typed fT ws tys cf stc st₁ sc asR v T? bh hcur' hst hrr hm htn hsz hcp hfT hok hD hrun
  | false =>
    have hcur : K.cur.map (·.1) ≠ some g := fun e => by rw [hS stc g e] at hst; cases hst
    obtain ⟨gd, self, hs, ds, c, dec, body, hfind, hfn, hl0⟩ := hF Δ ρ π g ws tys stc sc asR hcp
    exact hA n ih Δ ρ π g hd typed fT ws tys cf stc st₁ sc asR v T? bh gd self hs ds c dec body hcur hst hG hfind hfn
      hl0 (hff gd self hs ds c dec body hfind hfn hcur) hm htn hsz hcp hfT hok hD hrun

end Ochr.Meaning.Steps.Form.Master
