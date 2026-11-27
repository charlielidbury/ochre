import Ochr.Meaning.Steps.FrameEnd

/-!
# The call of the function under check, the closed-off call and the re-run of a sealed program (lead31; docs/31 D205, D206)

The lead's Task 1 (a) and (b), statements only. Main's D135: while a function is checked, a call of it never runs its
body; it closes off at once (`Machine.underCheck`: the head's code, `Value.sameCode`, is on the [Rec] stack), as a call of
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
until D136 lands; then `GoH` is a `reject def` (docs/31 D205).
-/

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- **The functions under check, as the context knows them** (MIXED entry condition; docs/31 D205). D135: `callFn`
closes a call off at once when its head has the code of a function on the [Rec] stack. The context knows one such
function, `K.cur`, by name. This clause ties the two for globals: a global is under check in the checker's state
exactly when it is `K.cur`'s, so a call of any other global runs its body (the in-place branch) and a call of `K.cur`'s
closes off. Closures on the stack have no counterpart in the context (the finding of D205). Principle 10 (recursion
descends: every call the check makes is of an earlier definition, a value, or the definition itself) and principle 4
(one code, two runs: what is under check is decided alike by the checker and the model). -/
def RecCurG (K : RunCtx) (st : MState) : Prop :=
  ∀ h : String, st.recStack.any (·.fn.sameCode (.gfn h)) = true ↔ K.cur.map (·.1) = some h

/-- **The step for a call of the global under check** (MIXED; main's D135, ruling (C) of D200; Task 1 (a)). `CallFnG`'s
statement at a head `g` with `K.cur = some (g, b)`, under `RecCurG` (so `callFn` closes the call off at once) and, at a
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
    K.cur = some (g, b) → RecCurG K stc → (typed = true → RecRankG K ρ stc) →
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

/-- **The body descends** (MODEL; a clause of the context for each accepted recursive global, like `FixEqG`; docs/31
D207, the answer to the lead's second question: no conclusion of the general statement carries "every recursive call
is at a lower rank", so it is this clause, established at the global's acceptance). The reference's run of the body at
arguments `a` depends on `self` only through `self`'s applications at argument lists of rank below `a`'s: two selves
whose applications agree there (and whose function types have the same parameter codes, so the arguments are run and
tested alike) give the same body output. `FixEqG` follows by induction on the rank (stage `rank a + 1` at `a` binds
`self` to stage `rank a` at the weakened type, which agrees with the global's function below `rank a` by the same
induction: the stabilisation). Established at acceptance from the simulation of the global's own check at every bound
(the knot): its conclusion makes the reference's output the meaning of the checker's leaf, which depends on `K.C.global
g` only through the sealed programs of calls of `g` (D135 closes every such call off), each made where [Rec] tested its
decreasing argument against the entry (typed sites; at untyped sites, the per-run form of principle 10, D205), so at a
rank below the entry's. Principle 10 (recursion descends) and principle 1 (a recursive function means its limit by
stages). -/
def RecDescG (K : RunCtx) (st : MState) : Prop :=
  ∀ (n : String) (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (j : Nat) (body : Term),
    st.globals.find? (·.name == n) = some gd → K.cur.map (·.1) ≠ some n →
    gd.fn? = some (.fix self hs ds c (some j) body) →
    ∀ (ρ : Assignment) (φ : Future) (s : SState) (args : List Sem) (X Y : Sem) (TX TY : TyM),
      DomMembers K.dm.read (runDoms K ρ φ s ds) args →
      (∀ as : List Sem, TX.paramAt? K.dm.read as = TY.paramAt? K.dm.read as) →
      (∀ (bs : List Res) (s' : SState), fixRank (some j) (bs.map (·.1)) < fixRank (some j) args →
        callOf K.dm.read (X, .plain TX) bs s' = callOf K.dm.read (Y, .plain TY) bs s') →
      let fb := (bindsOf K ρ φ s ds, fixCod K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c, K.D.typeDecl (K.D.teleDecls (scopeOf s) ds) c)
      fixBodyAt K ρ φ fb s (runDoms K ρ φ s ds) (codOf K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c) TX s.nextLoan body X args =
        fixBodyAt K ρ φ fb s (runDoms K ρ φ s ds) (codOf K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c) TY s.nextLoan body Y args

end Ochr.Meaning.Steps.Form.Master
