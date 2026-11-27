import Ochr.Meaning.Steps.MasterUntyped
import Ochr.Meaning.Steps.FrameFrag

/-!
# The general step for a call of a global: the statement and what it assumes (lead29, 2026-11-22; docs/31 D200)

`StepCallG` is the part of `Master.StepCall` whose head is a global's name, `g(ā)` (`.call (.const g) as hd`): `EvalAt`
for it, from the induction hypothesis, at every fuel, context and assignment, typed or untyped, erased or not. It covers
the callee's body run to a value in place (`runBody`, untyped, in tail position) and the call closed off (`closeCall`),
borrow arguments, a declared result that is a borrow ([Lend], `into`), a recursive callee (the definition being checked
called by its own name, `K.cur`), an erased call, and the call as a `let`'s right-hand side, whose type is deferred
(`LaterOk`, D183).

The reference's run of the call (`runT`'s `.call` clause, at a global head) is: the head's meaning `K.C.global g` (the
`.const` clause, no state change), the arguments (`runArgs`), then the strict test that each borrow argument's label
holds its parameter's content type, and the callee's meaning applied (`callOf`): `refCall` below. It never runs the
callee's body. The checker runs the head, the arguments (each a temporary of the caller's frame, D115), and then
`callFn`: [Call-type] (typed), [Rec] (typed), [Lend], and the body in place or [Close].

**The statement is assembled from two phases** (`stepCallG_of`, to be proved from the facts below):
- `CallHeadArgsG` (mixed): up to the CALL POINT (the head and the arguments evaluated and held as temporaries), the
  checker's run is simulated by the reference's `runArgs`, and the two call points are related (`CallPt`);
- `CallFnG` (mixed): from related call points, `callFn` is simulated by `refCall`. It splits in three
  (`CallFnGFrom`): the body run in place (`CallRanG`), closed off (`CallClosedG`), a proof value or a proof-class callee
  (`CallProofG`); the first is where the context's clauses are consumed: the callee's meaning (`GlobalsOk.fn`, and
  `memBelow` for `K.cur`), the frame property (`FrameFrag.RunFrameS`, D129, which does NOT cover a body that reads its
  own binding: `RunFrameSelfG` below), the label kind of the callee's result (`RetKindG`, ruling R3), and the recursion's
  rank (`RecRankG`).
- The erased call (the table erases it) is D158's wrapper at a call: `ErasedCallG`.
-/

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

open Classical in
/-- **The reference's call after its head and arguments** (`runT`'s `.call` clause, its last part): the strict test that
each borrow argument's label is live and holds its parameter's content type, then the callee's meaning applied. -/
noncomputable def refCall (K : RunCtx) (fv : Res) (as : List Res) : SM Res :=
  fun s => if BorrowArgsTyped K.dm.read fv as s then callOf K.dm.read fv as s else none

/-- **The step for a call of a global** (lead29's Task 1): `EvalAt` at `g(ā)`, every global name `g`, every argument
list and head flag, from the induction hypothesis. The part of `StepCall` whose head is `.const g`; the rest of
`StepCall` (a head that is a place, a closure, an embedded value) shares `CallFnG` and differs in the head's run. -/
def StepCallG (K : RunCtx) (φ : Future) : Prop :=
  ∀ n, IH K φ n → ∀ (Δ : Nat → TyS) (ρ : Assignment) (g : String) (as : List Term) (hd : Bool),
    EvalAt { K with Δ := Δ } ρ φ n (.call (.const g) as hd)

/-! ## The call point -/

/-- **Related call points** (D115): the checker's top frame ends with the head `gfn g` and the arguments `ws` as its
last temporaries, each argument evaluated at the type `tys[i]` (or none); the reference has the head's meaning `fv`
and the arguments' results `as`, in its state `sc`. The two states meet `Pre`/`Rel` (the temporaries counted by the
relation's holder clause, as every value in flight), the reference's is good, and each argument's value means the
reference's result, carries its label (renamed), and its type agrees. -/
structure CallPt (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (stc : MState) (sc : SState)
    (g : String) (ws : Array Value) (tys : Array (Option Value)) (fv : Res) (as : List Res) : Prop where
  temps : ∃ fr base, stc.env.back? = some fr ∧ fr.temps = base ++ #[.gfn g] ++ ws
  head : fv = K.C.global g
  pre : Pre K ρ stc
  rel : Rel K ρ φ π stc sc
  good : Strict.SGood K.dm K.Γ φ sc
  len : as.length = ws.size ∧ tys.size = ws.size
  mean : ∀ (i : Nat) (w : Value) (r : Res), ws[i]? = some w → as[i]? = some r → meanV K ρ (fun l => φ (π l)) r.2 w = r.1
  label : ∀ (i : Nat) (w : Value) (r : Res), ws[i]? = some w → as[i]? = some r → r.2.label = (Value.heldLabel w).map π
  ty : ∀ (i : Nat) (r : Res) (T : Value), as[i]? = some r → tys[i]? = some (some T) → StrAgree K ρ T r.2

/-- The flags `evalAt` reads for a call, and what `callFn` is handed by `evalCall` (D80, D82, D130): the call's declared
result reading `res`, the fills of the borrow arguments lending a `Unit` place, whether the type is wanted, and whether
the call's type is deferred (`deferHere`, the entry's flag). -/
structure CallFlags where
  res : DeclInfo
  fills : Array Bool
  want : Bool
  defer : Bool

/-! ## The two phases -/

/-- **Up to the call point** (MIXED; to be assembled from the induction hypothesis at the head and at each argument, the
checker's inversion of `evalCall`'s loop, and the per-argument hint sites of D172/D179). From an `evalCore` state meeting
`CoreSimK`'s entry conditions for `g(ā)`, unerased by the table, a successful run of the call reaches the call point
`stc` (head and arguments held as temporaries, D115) and then runs `callFn` (`evalCall`'s last line; the head is a
`.const`, so no [Rec] mark and no `given`) at a smaller fuel, ending in a state with `st'`'s kernel and mode; and the
reference's arguments, run from any related good state, reach a call point related to `stc` (`CallPt`), under an
extension. `callFn` is handed `deferHere` and `wantHere` (D130), what `OutL` reads through `TyWanted` and `LaterOk`. -/
def CallHeadArgsG (K : RunCtx) (φ : Future) : Prop :=
  ∀ n, IH K φ n → ∀ (Δ : Nat → TyS) (ρ : Assignment) (g : String) (as : List Term) (hd : Bool)
    (st st' : MState) (typed : Bool) (hint : Option Value) (v : Value) (T? : Option Value) (s : SState)
    (π : Nat → Nat) (bh : Nat),
    ModeR st → (typed = true → st.curTail = false) → st.tailNext = false → st.tailDecl = none →
    Pre { K with Δ := Δ } ρ st → Rel { K with Δ := Δ } ρ φ π st s → Strict.SGood K.dm K.Γ φ s →
    (Term.call (.const g) as hd).valsOk (Strict.ValsP { K with Δ := Δ } ρ φ) →
    (Term.call (.const g) as hd).absBelow st.absTy.size → HintBelow hint st.absTy.size →
    (Term.call (.const g) as hd).hasHolePrim = false →
    K.D.flags (scopeOf s) (.call (.const g) as hd) = (false, false) → DecTab K.D st' →
    Runs (Ochr.evalCore n typed (.call (.const g) as hd) hint) st bh (v, T?) st' →
    ∃ (m : Nat) (stc st₁ : MState) (fT : Option Value) (ws : Array Value) (tys : Array (Option Value)) (cf : CallFlags)
      (bh' : Nat),
      m + 1 < n ∧ cf.defer = st.deferHere ∧ cf.want = st.wantHere ∧ Kept st stc ∧ stc.tailNext = false ∧
      fT = (stc.globals.find? (·.name == g)).map (·.ty) ∧ as.length = ws.size ∧
      Runs (Ochr.callFn m typed fT as.length tys hd none none cf.res cf.fills cf.want cf.defer none) stc bh' (v, T?) st₁ ∧
      Kern st₁ st' ∧ ModeEq st₁ st' ∧
      ∃ (ρc : Assignment) (Δc : Nat → TyS) (πc : Nat → Nat) (asR : List Res) (sc : SState),
        Ext { K with Δ := Δ } ρ π st stc ρc Δc πc ∧
        runArgs { K with Δ := Δ } ρ φ false (K.C.global g).2.m [] as s = some (asR, sc) ∧
        CallPt { K with Δ := Δc } ρc φ πc stc sc g ws tys (K.C.global g) asR

/-- **The call itself** (MIXED): from related call points of a call of the global `g`, `callFn`'s successful run is
simulated by `refCall` (the borrow arguments' strict test and the callee's meaning applied): `OutL`'s content at the
call (`Out`, the deferred type a `let` reads, the promised type) and `Kept`. Its induction hypothesis is at the fuel
`callFn` runs at plus one (the body runs in place two levels down, `runBody` → `runBodyCore` → `eval`). For an untyped
run, the reference's call succeeds (`hok`, which an untyped `EvalAt`'s entry condition gives through `runArgs`). Proved
from its three branches by `CallFnGFrom`. -/
def CallFnG (K : RunCtx) (φ : Future) : Prop :=
  ∀ n, IH K φ (n + 1) → ∀ (Δ : Nat → TyS) (ρ : Assignment) (π : Nat → Nat) (g : String) (hd typed : Bool)
    (fT : Option Value) (ws : Array Value) (tys : Array (Option Value)) (cf : CallFlags) (stc st₁ : MState)
    (sc : SState) (asR : List Res) (v : Value) (T? : Option Value) (bh : Nat),
    ModeR stc → stc.tailNext = false → 0 < stc.env.size →
    CallPt { K with Δ := Δ } ρ φ π stc sc g ws tys (K.C.global g) asR →
    fT = (stc.globals.find? (·.name == g)).map (·.ty) →
    (typed = false → (refCall { K with Δ := Δ } (K.C.global g) asR sc).isSome) →
    DecTab K.D st₁ →
    Runs (Ochr.callFn n typed fT ws.size tys hd none none cf.res cf.fills cf.want cf.defer none) stc bh (v, T?) st₁ →
    (∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (r : Res) (s' : SState),
      Ext { K with Δ := Δ } ρ π stc st₁ ρ' Δ' π' ∧ refCall { K with Δ := Δ } (K.C.global g) asR sc = some (r, s') ∧
      meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧
      (∀ T, T? = some T → StrAgree { K with Δ := Δ' } ρ' T r.2) ∧
      r.2.label = (Value.heldLabel v).map π' ∧
      Pre { K with Δ := Δ' } ρ' (st₁.withTempT v T?) ∧ Rel { K with Δ := Δ' } ρ' φ π' (st₁.withTempT v T?) s' ∧
      (cf.defer = true → ∀ caps hs ds cod rd ws', st₁.callTyLater = some (.tPi caps (.pi hs ds cod) rd, ws') →
        ({ K with Δ := Δ' }).M.paramTy ρ' (.tPi caps (.pi hs ds cod) rd) ws' ds.length = r.2) ∧
      ((typed = true ∨ (cf.want = true ∧ cf.defer = false)) → T? = none → r.2.m = TyM.err)) ∧
    Kept stc st₁

/-- `EvalAt` with one more hypothesis on the reference state (here: whether the table erases the term there). -/
def EvalAtIf (K : RunCtx) (ρ : Assignment) (φ : Future) (n : Nat) (t : Term) (Q : SState → Prop) : Prop :=
  ∀ (st st' : MState) (typed : Bool) (hint : Option Value) (v : Value) (T? : Option Value) (s : SState)
    (π : Nat → Nat),
    Q s → ModeR st → (typed = true → st.tailNext = false) → 0 < st.env.size →
    (st.tailDecl = none ∨ st.tailDecl = some (K.D.declOf (DecideScope.topReadings st) t)) →
    Pre K ρ st → Rel K ρ φ π st s → Strict.SGood K.dm K.Γ φ s →
    t.valsOk (Strict.ValsP K ρ φ) → t.absBelow st.absTy.size → HintBelow hint st.absTy.size → t.hasHolePrim = false →
    (typed = false → (runT K ρ φ st.tailNext (hintM K ρ hint) t s).isSome) →
    DecTab K.D st' →
    ∀ bh, Runs (Ochr.eval n typed t hint) st bh (v, T?) st' →
    OutL K ρ φ π st st' s (runT K ρ φ st.tailNext (hintM K ρ hint) t) v T? t (TyWanted typed st) ∧ Kept st st'

/-- An `EvalAtIf` at a split of the reference states is `EvalAt`. -/
theorem evalAt_of_split {K : RunCtx} {ρ : Assignment} {φ : Future} {n : Nat} {t : Term} (Q : SState → Prop)
    (h₁ : EvalAtIf K ρ φ n t Q) (h₂ : EvalAtIf K ρ φ n t (fun s => ¬ Q s)) : EvalAt K ρ φ n t := by
  intro st st' typed hint v T? s π
  by_cases hq : Q s
  · exact h₁ st st' typed hint v T? s π hq
  · exact h₂ st st' typed hint v T? s π hq

/-- **The erased call** (D158's wrapper at a call; not built): `EvalAt` for `g(ā)` where the table erases it (a call of
a global returning a type, or a proof: `evalAt` runs it on a private copy, `inStatement`; the reference on a copy,
`SM.erasedIf`, `⋆` for a proof). -/
def ErasedCallG (K : RunCtx) (φ : Future) : Prop :=
  ∀ n, IH K φ n → ∀ (Δ : Nat → TyS) (ρ : Assignment) (g : String) (as : List Term) (hd : Bool),
    EvalAtIf { K with Δ := Δ } ρ φ n (.call (.const g) as hd)
      (fun s => ¬ K.D.flags (scopeOf s) (.call (.const g) as hd) = (false, false))

/-- **`eval` around `evalCore` at a call** (CHECKER; `EvalInvD` excludes calls: there `evalAt` reads the flags `callFn`
set, `getFlags`, and its pre-pass reads no reading of the call's head). The same transport, for a call: `evalCore`
starts at a state with `st`'s kernel and mode, its tail flag `curTail` the entry's `tailNext`, the deferral flag
consumed into `deferHere` (D130), the wanted flag into `wantHere`; and ends with `st'`'s kernel and mode. -/
def EvalInvDCall : Prop :=
  ∀ (n : Nat) (typed : Bool) (f : Term) (as : List Term) (hd : Bool) (hint : Option Value) (st st' : MState) (bh : Nat)
    (v : Value) (T? : Option Value) (D : Decisions),
    ModeR st → DecTab D st' → (st.tailDecl = none ∨ st.tailDecl = some (D.declOf (DecideScope.topReadings st) (.call f as hd))) →
    (D.declOf (DecideScope.topReadings st) (.call f as hd)).isProof = false →
    Runs (Ochr.eval (n + 2) typed (.call f as hd) hint) st bh (v, T?) st' →
    ∃ (st₀ st₁ : MState) (bh' : Nat), Kern st st₀ ∧ ModeEq st st₀ ∧ st₀.curTail = st.tailNext ∧
      st₀.tailNext = false ∧ st₀.tailDecl = none ∧
      Runs (Ochr.evalCore n typed (.call f as hd) hint) st₀ bh' (v, T?) st₁ ∧ Kern st₁ st' ∧ ModeEq st₁ st' ∧
      st₀.deferCallTy = false ∧ st₀.deferHere = st.deferCallTy ∧ st₀.callTyLater = none ∧
      st₀.wantHere = (typed || st.wantTy)

/-! ## The clauses of the context and the entry conditions the call needs

`CallFnG` splits by `callFn`'s three outcomes at a global head (its inversion is a fact about the checker alone, to be
stated with the branches): the body run in place (`runBody`, untyped, in tail position, at the declared codomain's
hint, the frame popped), closed off (`closeCall`, the row read off the declared codomain), a proof-class callee (its
borrow arguments ended, `⋆`). The first branch is where the context is consumed:
- the callee's meaning: `GlobalsOk.fn` (`K.C.global g` is the closure of its `fix` term) for an earlier global, and
  `GlobalsOk.memBelow` (the stage at the bound) for the definition being checked, `K.cur`;
- the frame property: `FrameFrag.RunFrameS` (D129), which relates the reference's run of the body IN PLACE (the callee's
  frame on the caller's state, which the induction hypothesis at the body relates to the checker's) with its run in the
  closure (`fixBodyAt`, whose result `callOf` applies). It is stated for bodies that do not read their own binding,
  which a recursive callee's body does (`R(m)` is `.call (.place self) …`): the recursive callee needs it at a body that
  reads `self`, with `SelfRel` relating the two `self`s (in place `K.C.global g`, in the closure the stage below);
- the label kind of the callee's result: `RetKindG` (below; ruling R3);
- the recursion's rank: `RecRankG` (an entry condition), needed at typed call sites only. Under main's D135 (ruling
  (C)) a call of the function being checked never runs its body: it closes off at once, so no in-place run of a body
  under its own check exists, and the former checker fact `RecCheckedG` ([Rec] at every call, typed or not) is moot
  and deleted (lead31; docs/31 D204).
-/

/-- **(R3) A callee's result is labelled exactly where its codomain is written `&`** (MODEL; a clause of the context,
to be established when each definition is accepted, through the relation, from its typed check at unknown parameters:
the checker's leaf value is a borrow exactly when the reference's result is labelled (`Out`'s label clause, both
directions), a borrow only at a type `&A` (`OutL`'s kind clause, R3), the leaf type converts to the goal, and the goal
is `&` exactly when the codomain is written `&` (`refTopOk`)). For every earlier global with a `fix`, at every
assignment, future and forming state, the closure's function (`fixG`, what `run_fix_def` forms and `GlobalsOk.fn`
names) at member arguments returns a body output whose result label is present exactly when the codomain is a borrow
type (`codOf`'s `isRef`: the codomain term is `&U`). Both directions are consumed: at a data codomain `callOf`'s result
carries no label, so the checker's in-place value must not be a borrow (machine12's `gb (r : &Nat) : Nat := r`, which the
checker never accepted and the context admitted); at a borrow codomain `callOf`'s result always carries a fresh label,
and `callFn` relabels the body's value into it only if it is a borrow. -/
def RetKindG (K : RunCtx) (st : MState) : Prop :=
  ∀ (n : String) (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term),
    st.globals.find? (·.name == n) = some gd → K.cur.map (·.1) ≠ some n →
    gd.fn? = some (.fix self hs ds c dec body) →
    ∀ (ρ : Assignment) (φ : Future) (s : SState) (piT : TyM) (args : List Sem) (o : BodyOut),
      DomMembers K.dm.read (runDoms K ρ φ s ds) args →
      fixG K ρ φ (bindsOf K ρ φ s ds, fixCod K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c, K.D.typeDecl (K.D.teleDecls (scopeOf s) ds) c)
        (K.D.piSort (scopeOf s) (.pi hs ds c)) s (runDoms K ρ φ s ds) (codOf K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c) piT
        s.nextLoan dec body args = some o →
      o.retLabel.isSome = (codOf K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c).isRef

/-- **The recursion's rank, an entry condition** (MIXED: a condition on the assignment against the checker's [Rec]
stack). While the definition `n` is checked at the stage bound `b` (`K.cur = some (n, b)`), every [Rec] entry of the
checker's state for it records, at each surviving decreasing position, an unknown whose value has rank at most `b`. The
column `R` took it as the entry condition "the argument is at most the stage"; here it is on the state, because a call
of `n` inside the run (typed, or untyped in an in-place run of `n`'s own body) lands where the stage-`b` closure is the
function only if its decreasing argument has rank below `b`, which a [Rec] check against the entry gives. It is not in
`Pre` (`Pre` reads the kernel, which has no [Rec] stack): `EvalAt` is to take it, and every step to carry it. -/
def RecRankG (K : RunCtx) (ρ : Assignment) (st : MState) : Prop :=
  ∀ (n : String) (b : Nat), K.cur = some (n, b) → ∀ ctx ∈ st.recStack, ctx.fn = .gfn n →
    ∀ (j σ : Nat), j ∈ ctx.cands → ctx.entries[j]? = some (some σ) → semRank (ρ σ) ≤ b

/-! ## The composition, at the class of states the other steps use -/

/-- **The reference's run of a call of a global the table does not erase** is its arguments' run followed by
`refCall` (`runT`'s `.call` clause: `SM.erasedIf (false, false)` is the run itself, and a global's head is
`pure (K.C.global g)`, `SM.headOf` of a non-place). -/
theorem runT_callConst (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (hint : TyS) (g : String)
    (as : List Term) (hd : Bool) (s : SState) (hfl : K.D.flags (scopeOf s) (.call (.const g) as hd) = (false, false)) :
    runT K ρ φ tl hint (.call (.const g) as hd) s =
      (runArgs K ρ φ false (K.C.global g).2.m [] as >>= fun asR => refCall K (K.C.global g) asR) s := by
  rw [runT]
  simp only [hfl, SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false, SM.headOf]
  rw [runT]
  rfl

theorem IH.mono {K : RunCtx} {φ : Future} {n m : Nat} (h : IH K φ n) (hmn : m ≤ n) : IH K φ m :=
  fun k hk Δ ρ => h k (Nat.lt_of_lt_of_le hk hmn) Δ ρ

/-- **The unerased call of a global, from the two phases** (the composition `StepCallGFrom` asks, at the class of
states the other proved steps use: a frame, and the table not reading the call as a proof). PROVED from
`EvalInvDCall` (checker), `CallHeadArgsG` and `CallFnG` (mixed), all three unproved. Concludes `Out` and `Kept`;
`CallFnG`'s deferred and promised types are not yet carried to `OutL` (they need `evalAt`'s bookkeeping after
`evalCore` to keep `callTyLater`, which `EvalInvDCall` does not yet say). -/
theorem stepCallG_unerased {K : RunCtx} {φ : Future} (hE : EvalInvDCall) (hH : CallHeadArgsG K φ) (hF : CallFnG K φ) :
    ∀ n, IH K φ n → ∀ (Δ : Nat → TyS) (ρ : Assignment) (g : String) (as : List Term) (hd : Bool),
      EvalSimK { K with Δ := Δ } ρ φ n (.call (.const g) as hd)
        (fun st => 0 < st.env.size ∧
          (K.D.declOf (DecideScope.topReadings st) (.call (.const g) as hd)).isProof = false) := by
  intro n ih Δ ρ g as hd st st' typed hint v T? s π hP _ hm htl htd hp hr hS hv hab hhb hnh hfl hok hD bh h
  by_cases hn : n < 3
  · exact absurd h (Machine.evalLow n typed _ hint st st' bh _ hn (fun w e => by cases e))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  obtain ⟨st₀, st₁, bh', hk₀, hm₀, hct, htn, htd₀, h₀, hk₁, hm₁, -, -, -, -⟩ :=
    hE (m + 1) typed (.const g) as hd hint st st' bh v T? K.D hm hD htd hP.2 h
  have hD₁ : DecTab K.D st₁ := DecTab.of_kern hk₁.symm hD
  obtain ⟨m', stc, st₂, fT, ws, tys, cf, bh'', hlt, -, -, hkc, htnc, hfT, hlen, hrun, hk₂, hm₂,
      ρc, Δc, πc, asR, sc, hext, hargs, hpt⟩ :=
    hH (m + 1) (ih.mono (by omega)) Δ ρ g as hd st₀ st₁ typed hint v T? s π bh'
      (hm.of_modeEq hm₀) (fun e => hct.trans (htl e)) htn htd₀ (hp.of_kern hk₀) (hr.of_kern hk₀) hS hv
      (by rw [← hk₀.absTy]; exact hab) (by rw [← hk₀.absTy]; exact hhb) hnh hfl hD₁ h₀
  have hrunT : ∀ tl h', runT { K with Δ := Δ } ρ φ tl h' (.call (.const g) as hd) s =
      refCall { K with Δ := Δc } (K.C.global g) asR sc := by
    intro tl h'
    rw [runT_callConst _ ρ φ tl h' g as hd s hfl]
    simp only [Bind.bind, hargs]
    rfl
  have hsz : 0 < stc.env.size := by
    rw [hkc.size, ← ColumnC.size_of_erase hk₀.env]; exact hP.1
  have hD₂ : DecTab K.D st₂ := DecTab.of_kern hk₂.symm hD₁
  have hok' : typed = false → (refCall { K with Δ := Δc } (K.C.global g) asR sc).isSome := by
    intro e; rw [← hrunT st.tailNext (hintM { K with Δ := Δ } ρ hint)]; exact hok e
  obtain ⟨⟨ρ', Δ', π', r, s', hext', hx, hm', ha, hl, hp', hr', -, -⟩, hkept⟩ :=
    hF m' (ih.mono (by omega)) Δc ρc πc g hd typed fT ws tys cf stc st₂ sc asR v T? bh''
      ((hm.of_modeEq hm₀).of_modeEq hkc.mode) htnc hsz hpt hfT hok' hD₂
      (by rw [← hlen]; exact hrun)
  have hO : Out { K with Δ := Δ } ρ φ π st₀ st₂ s
      (runT { K with Δ := Δ } ρ φ st.tailNext (hintM { K with Δ := Δ } ρ hint) (.call (.const g) as hd)) v T? :=
    ⟨ρ', Δ', π', r, s', hext.trans hext', by rw [hrunT]; exact hx, hm', ha, hl, hp', hr'⟩
  exact ⟨Out.of_kern hk₀ (hk₂.trans hk₁) hO,
    ((((Kept.of_kern hk₀ hm₀).trans hkc).trans hkept).trans (Kept.of_kern hk₂ hm₂)).trans (Kept.of_kern hk₁ hm₁)⟩

/-- **The statement to prove next** (`stepCallG_of`): the step for a call of a global from the two phases, the
transport and the erased wrapper. -/
def StepCallGFrom (K : RunCtx) (φ : Future) : Prop :=
  EvalInvDCall → CallHeadArgsG K φ → CallFnG K φ → ErasedCallG K φ → StepCallG K φ

end Ochr.Meaning.Steps.Form.Master
