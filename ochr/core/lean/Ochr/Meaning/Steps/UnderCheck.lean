import Ochr.Meaning.Steps.FrameEnd

/-!
# The call of the function under check, the closed-off call and the re-run of a sealed program (lead31; docs/31 D205, D206)

The lead's Task 1 (a) and (b), statements only. Main's D135: while a function is checked, a call of it never runs its
body; it closes off at once (`Machine.underCheck`: the head is on the [Rec] stack; until main's D136 compared by code, `Value.sameCode`, now by value: the stack holds top-level definitions only, whose value is their name), as a call of
an unknown function does. So the step for such a call is the closed-off step whose head means what the context gives the
function under check: for a global, `K.C.global g`, the stage closure at the bound (`GlobalsOk.memBelow`); a sealed
program means the reference's run of its text (`meanV`'s `.sealed` clause), whose head call applies that same meaning to
the same argument meanings, so the value agrees by definition, and the type agrees where the argument's rank is below the
bound, which a typed site's [Rec] test and `RecRankG` give.

Attacked on the checker (`Steps/UnderCheckAttack.lean`): `RH` (one argument), `AH` (two, recursing on the second while
the first grows), `TH` (a call whose body would run to a value in place, `TH(TT, m)`, now sealed), `RB` (a block's
re-run after a later split reaches a recursive call, which closes off), and `GoH`, a LOCAL recursive function capturing
a variable that a split refines, called through a closure that captures the function under check. The last is the
finding of docs/31 D205: the checker recognises the function under check by its CODE, and the sealed program's head is
the closure VALUE with its capture refined; the model knows a function under check only as a global, by NAME (`K.cur`;
`Binding.refTy` reads a marked binding at `C.global` of its name; `meanV` of a closure value is its real closure). For a
local recursive function the model has no stage, so its own check's simulation cannot start from a good related state.
RULED by the lead (2026-11-27, lead32's brief R-A; to be main's D136, ruled pending its landing): NO model change. A
recursive function is a top-level definition; a local function (a `fix` formed inside a body) is not recursive, as in
Lean's kernel, which has no local recursion (the elaborator lifts `let rec`). So `K.cur` stays a global's name, `meanV` of
a closure stays the real closure, and nothing about local recursive functions is owed. `GoH` and its guard are accepted
until D136 lands; then `GoH` is a `reject def` (docs/31 D205). D136 LANDED (merged by lead34, 2026-11-27): `GoH` is
rejected at `go`'s `by y`, and `RecCurG` compares the stack's values (`==`; `sameCode` is deleted).
-/

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

-- `RecCurG` moved to `Steps/Master.lean` (lead47, R1, docs/31 D284): with the other direction, `RecRankG` and the
-- counter clause it is the tie `RecTie`, an entry condition of `EvalAt` and `TailAt`. Its history (D205, D218): the
-- clause was two-way, then one-way after main's D136 (a non-recursive global is not on the stack during its own check,
-- so the two-way clause was false there); R1 makes it two-way again AS AN ENTRY CONDITION, which a non-recursive
-- function's check meets once it runs with `K.cur = none` (main's D147/D148).

/-- **The step for a call of the global under check** (MIXED; main's D135, ruling (C) of D200; Task 1 (a)). `CallFnG`'s
statement at a head `g` with `K.cur = some (g, b)`, with `g` on the [Rec] stack (so `callFn` closes the call off at once; since D136 that is every call of `K.cur` the check makes, a non-recursive one making none, D31) and, at a
typed site, `RecRankG` (so the decreasing argument, a strict part of the entry by [Rec], has rank below `b`, where the
stage closure is the true function at its true codomain). Its parts (named, not separately stated):
- CHECKER, by construction: at a head on the [Rec] stack `callFn` reaches `closeCall` (`closesOff ← underCheck fv`; as
  a [Seal] head call, `stuckNow`), after [Call-type], [Rec] (typed) and [Lend]'s marks; the body never runs.
- MODEL, by definition: [Close]'s outputs are sealed programs whose head call is `.gfn g`, meaning `K.C.global g`, the
  head the reference's `refCall` applies (`meanV`'s `.gfn` clause); C1 to C8 of `notes/closeoff-model.md` as for every
  closed-off call (`CallClosedG`, D206).
- The type clause (`StrAgree` of the declared codomain at the arguments with `callOf`'s type) at a typed site:
  `RecRankG` with [Rec]; at an untyped site the type is read only where the call's type is wanted, and every untyped
  call of the global under check is at a call site that a typed check tested ([Rec] at a closure's or block's own
  check, re-run with captures refined consistently with the assignment): the per-run form of principle 10 (D205).
Principle 7 (closing off rebuilds the call), principle 10, principle 12 (clean inputs). -/
def CallUnderCheckG (K : RunCtx) (φ : Future) : Prop :=
  ∀ n, IH K φ (n + 1) → ∀ (Δ : Nat → TyS) (ρ : Assignment) (π : Nat → Nat) (g : String) (b : Nat) (hd typed : Bool)
    (fT : Option Value) (ws : Array Value) (tys : Array (Option Value)) (cf : CallFlags) (stc st₁ : MState)
    (sc : SState) (asR : List Res) (v : Value) (T? : Option Value) (bh : Nat),
    K.cur = some (g, b) → stc.recStack.any (·.fn == .gfn g) = true → (typed = true → RecRankG K ρ stc) →
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
      -- lead39 (docs/31 D241): `CallFnG`'s two clauses of `OutL` (D183, ruling (ii)), which this branch must conclude too
      (cf.defer = true → ∀ caps hs ds cod rd ws', st₁.callTyLater = some (.tPi caps (.pi hs ds cod) rd, ws') →
        ({ K with Δ := Δ' }).M.paramTy ρ' (.tPi caps (.pi hs ds cod) rd) ws' ds.length = r.2) ∧
      ((typed = true ∨ (cf.want = true ∧ cf.defer = false)) → T? = none → r.2.m = TyM.err) ∧
      -- lead48 (docs/31 D290): the goal clause, as `CallFnG` concludes it (a call closed off at once writes no goal)
      hintM { K with Δ := Δ' } ρ' st₁.goal = hintM { K with Δ := Δ } ρ stc.goal) ∧
    Kept stc st₁

/-- **The re-run of a sealed program** (MIXED; Task 1 (b); principle 7: a sealed program means the run of its text, and
is re-run exactly when an input changes, its head never re-closed; principle 8: the refinement that triggers it is met by
the assignment). When a refinement or an [End] changes a sealed program's text, the checker re-normalises it
(`nfSealed`: an untyped run of the text from one empty frame, its head call not closed off, a text holding a hole left
as it is, a stuck run left sealed or replaced by its generalisation record). Its result means what the sealed text
means, at every assignment and hint: the reference's run of the text from the empty state (`meanV`'s `.sealed` clause).
To be assembled from: the induction hypothesis at the text (an untyped `EvalAt` from a start state related to
`emptyState 0`, the label renaming sending the checker's counter to `0`); the reference's success there, from the sealed
value's membership in a good state (a member is never `err`); a stuck run, from the generalisation record's path
condition (`TypedAssignment`); the head call that does not close off, from the in-place branch of `CallFnG` (D202:
`RunFrame` with `FixEqG`). Needs no hole parametricity: a text holding a hole is never run (D97). -/
def SealRerunG (K : RunCtx) (φ : Future) : Prop :=
  ∀ n, IH K φ (n + 1) → ∀ (ρ : Assignment) (t : Term) (st st' : MState) (v : Value) (bh : Nat) (h : TyS),
    Pre K ρ st → DecTab K.D st' → t.valsOk (Strict.ValsP K ρ φ) →
    meanV K ρ φ h (.sealed t) ≠ .err →
    Runs (Ochr.nfSealed (n + 1) t) st bh v st' →
    ∃ ρ' : Assignment, (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧ meanV K ρ' φ h v = meanV K ρ φ h (.sealed t)

end Ochr.Meaning.Steps.Form.Master

/-! ## The in-place branch for an accepted global, and where its fixpoint clause comes from (Task 1 (c); D207) -/

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- **The call of an accepted global** (MIXED; Task 1 (c)): `CallFnG` at a head that is not under check, from the
context's clauses it consumes: the callee's meaning (`GlobalsOk.fn`, its closure), the frame property at equal selves
(`RunFrame`, D202), the fixpoint clause (`FixEqG`), the label kind of the result (`RetKindG`, R3), and `RecCurG` (so
`callFn` runs the body, or closes it off when the body is stuck, never because the head is under check). The in-place
run is `RunFrame`-related to `fixBodyAt` with `self` the global itself at its true type, which `FixEqG` equates with the
global's function, which `callOf` applies. Principle 6 (effects stay local: the run in place is the run in isolation,
plugged in) and principle 4 (it decides as its meaning does). -/
def CallAcceptedG (K : RunCtx) (φ : Future) : Prop :=
  ∀ n, IH K φ (n + 1) → ∀ (Δ : Nat → TyS) (ρ : Assignment) (π : Nat → Nat) (g : String) (hd typed : Bool)
    (fT : Option Value) (ws : Array Value) (tys : Array (Option Value)) (cf : CallFlags) (stc st₁ : MState)
    (sc : SState) (asR : List Res) (v : Value) (T? : Option Value) (bh : Nat),
    K.cur.map (·.1) ≠ some g → RecCurG K stc → GlobalsOk K stc → RunFrame → FixEqG K stc → RetKindG K stc →
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
      Pre { K with Δ := Δ' } ρ' (st₁.withTempT v T?) ∧ Rel { K with Δ := Δ' } ρ' φ π' (st₁.withTempT v T?) s') ∧
    Kept stc st₁

/-- **The body descends** (MODEL; a clause of the context for each accepted global, like `FnGoodG`; docs/31 D207,
RESTATED by D232). The reference's run of the global's body at member arguments `args` (from its forming state `formG`)
depends on its own binding only through that binding's function below `args`' rank: for two selves that are closures over
the global's domains at its sort (`closureAt` at a codomain of the true one's kind), each of a function good at every
member argument (`OutGood'`) with a type that fits (`PiFits`), whose functions and codomains agree at the member argument
lists of rank below `args`', the body's outputs agree. Without a decreasing parameter (`dec = none`, rank `0`) the body
ignores its own binding (D31: it cannot name itself).

**As first stated (D207) it was FALSE, by reading** (D232): it asked of the selves only their parameter codes and their
calls below the rank; the whole-state test after a write at a field path reads every binding, `self` included, so at an
argument of rank `0` (no agreement asked) a member and `err` give different outputs on a body that writes a field there.
The selves are now closures of good functions, the only selves the reference ever binds (the stage closures, and the
global's own closure).

**Where it comes from** (D213 corrected by D232, D233; not built): at the global's acceptance, after the knot
(`FnGoodG`, membership), from the simulation of the global's own check under two contexts whose meanings of the global are
the two selves (one of them the global's own closure at its true type, which `MemBelow` must be widened to admit), the
reference's output being the meaning of the checker's leaf under each; that meaning reads the global only through the
values `.gfn g` the leaf's sealed programs hold (as a head call, or, until main's D139, as a stuck block's argument:
`RecDescAttack.MB0`), each call of it [Rec]-tested against the entry (entries stay on the stack while block arms are
checked), so at member arguments of rank below `args`', where the two selves agree (the closure application lemma).
Attacked on `R`, `AH` (two arguments, the second decreasing), `MT`/`MB`/`MB0r` (a recursive call under a match on another
argument), `TB`/`TBB` (returning a borrow of the argument): `Steps/RecDescAttack`. -/
def RecDescG (K : RunCtx) (st : MState) : Prop :=
  ∀ (n : String) (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term),
    st.globals.find? (·.name == n) = some gd → K.cur.map (·.1) ≠ some n →
    gd.fn? = some (.fix self hs ds c dec body) →
    ∀ (ρ : Assignment) (φ : Future) (args : List Sem), DomMembers K.dm.read (psG K ρ φ ds) args →
    ∀ (outX outY : PiCod) (gX gY : List Sem → Option BodyOut),
      outX.isRef = (outG K ρ φ ds c).isRef → outY.isRef = (outG K ρ φ ds c).isRef →
      PiFits K.dm.read (lG K hs ds c) (psG K ρ φ ds) outX (fun _ => True) →
      PiFits K.dm.read (lG K hs ds c) (psG K ρ φ ds) outY (fun _ => True) →
      (∀ a, DomMembers K.dm.read (psG K ρ φ ds) a → ∃ o, gX a = some o ∧ OutGood' K.dm.read (psG K ρ φ ds) outX a o) →
      (∀ a, DomMembers K.dm.read (psG K ρ φ ds) a → ∃ o, gY a = some o ∧ OutGood' K.dm.read (psG K ρ φ ds) outY a o) →
      (∀ bs, DomMembers K.dm.read (psG K ρ φ ds) bs → fixRank dec bs < fixRank dec args →
        gX bs = gY bs ∧ outX.cod bs = outY.cod bs) →
      fixBodyAt K ρ φ (fbG K ρ φ ds c) formG (psG K ρ φ ds) (outG K ρ φ ds c)
          (piTyAt K.dm.read (lG K hs ds c) (psG K ρ φ ds) outX) 0 body
          (closureAt K.dm.read (lG K hs ds c) φ (psG K ρ φ ds) outX gX) args =
        fixBodyAt K ρ φ (fbG K ρ φ ds c) formG (psG K ρ φ ds) (outG K ρ φ ds c)
          (piTyAt K.dm.read (lG K hs ds c) (psG K ρ φ ds) outY) 0 body
          (closureAt K.dm.read (lG K hs ds c) φ (psG K ρ φ ds) outY gY) args

end Ochr.Meaning.Steps.Form.Master
