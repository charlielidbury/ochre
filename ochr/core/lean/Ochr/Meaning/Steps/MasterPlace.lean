import Ochr.Meaning.Steps.MasterUntyped
import Ochr.Meaning.Steps.AccessAttack
import Ochr.Meaning.Steps.PlaceGuards

/-!
# The master induction's read of a place, decomposed (lead26, 2026-11-22; docs/31 D181)

`.place p` has no sub-run, so its step is a composition of facts, not an induction. Its core, shared with
`borrow` and `assign`, is ONE fact, part checker and part model: the checker's [Access] of the place
(`accessPath`, then `accessInside`) is the reference's (`SState.access pos (dataHit steps)`), with the entry
conditions holding afterwards (`AccessG`). It was attacked first on the cases the fragment and the columns did not
cover (`Steps/AccessAttack.lean`: a field path, a place under a borrow, a place lent twice, a proof place, a place
whose content holds an unknown, a partly moved place; every case agrees on the labels ended and the sites and
holders left). The read of one place, the place's type, and the step around them are stated here, and the two
assemblies are PROVED from them:

* `readPlace_sim`: the checker's `readPlace` against the reference's `SM.guarded ContentOk (readPlace …)`, from
  `ReadInvD`, `BorrowReadWhole` (checker), `AccessG` (mixed), `ReadOutG` (mixed: the read after its access);
* `stepPlace_direct`: the evaluation step for a place read directly (no positional projection, which the checker runs
  as the one-constructor match naming the field, D81), from `PlaceInvD` (checker), `PlaceTypeG` (mixed),
  `readPlace_sim`'s three, and `EvalInvDT` (checker: `eval` hands `evalCore` the typing flag `typed`).

The class: a direct place, an unerased term the table reads as decided data. NOT covered: a place with a positional
projection (a one-constructor match, `projMatch`; its arm is a direct read of the field); an erased read (the erased
wrapper, D158). The read of a borrow whose content is partly moved is accepted today (`PlaceGuards.MB2`, D181) and
will be rejected (RULED (A), main's D127): the step assumes it as one named checker fact, `BorrowReadWhole`, false
until then.
-/

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- A place the checker reads directly: no positional projection `q.i` (which it runs as the one-constructor match
naming the field, D81 [Proj], `projIn`; a number's `.0` included, conservatively). -/
def _root_.Ochr.Place.Direct : Place → Prop
  | .var _ => True
  | .deref q => q.Direct
  | .field _ q => q.Direct
  | .proj _ _ => False

/-- The checker's write of `⊥` at a place, as a function of Ω (`Machine.setPlace`): at the variable's position, the
path updated. -/
def ckSetBot (env : Env) (pos : Pos) (steps : List Step) : Option Env :=
  ((valAt env pos).updAt (fun _ => .bot) steps).map (Env.setAtE env pos)

/-- What the checker's read leaves in place: a proof (never moved), or a value that is not a borrow at a place whose
reading the table says copies (D80). A borrow always moves. -/
def ReadCopies (v : Value) (c : Bool) : Prop := v = .proof ∨ ((∀ l w, v ≠ .borrow l w) ∧ c = true)

/-! ## The access: the shared core -/

/-- **The checker's [Access] of a place is the reference's** (mixed; STATED, attacked in `Steps/AccessAttack.lean`;
the core of `place`, `borrow` and `assign`). From related states with a frame, the checker's `accessPath; accessInside`
of `p` ends the borrows the reference's access of `p`'s position at its steps ends (`dataHit`: on the path, at the
place, inside its content; in rounds, an end passing its sites to the borrows of the content it gives back), and the
entry conditions hold afterwards, under an extension (an end's [Repack] and a fill's re-run may make unknowns).

The strict end tests (`AccessOk`, ruling (A) of D106): in a TYPED run (`typing`) the checker's own tests give them
(no borrow ends over moved-out content, D53, D98; [Repack], D64), so the fact concludes them; in an untyped run the
checker runs no [Repack], and they are an entry condition (an untyped run's step has the reference's success,
`hok`).

Its parts, for whoever proves it: (C) the checker's access is a chain of single ends `endTopLoan`, each of a live
label reached at the place by the checker's sites (`Env.sitesOf`), to a state where none is reached; (X) one end,
`endBorrow l` against `SState.endLabel (π l)` (the old `endBorrow_step_stmt` in this form; the fragment's
`FragEnd.rel_end` is its case of one loan of a number); (M) the reference's access is any such chain (its rounds end
in label order, the checker in path and content order; ends reached together commute: `RelendComm.relend_comm`,
`SState.endLabel_comm`), with the strict tests carried across the orders. -/
def AccessG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st st' : MState) (s : SState) (p : Place)
    (pos : Pos) (n bh : Nat),
    ModeR st → 0 < st.env.size → Pre K ρ st → Rel K ρ φ π st s → Strict.SGood K.dm K.Γ φ s →
    resolve s p = some (pos, p.steps.2) →
    (st.typing = false → AccessOk K φ s pos (dataHit p.steps.2)) →
    DecTab K.D st' →
    Runs (do Ochr.accessPath n p; Ochr.accessInside n p) st bh () st' →
    AccessOk K φ s pos (dataHit p.steps.2) ∧
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat),
      Ext K ρ π st st' ρ' Δ' π' ∧ Kept st st' ∧ st'.typing = st.typing ∧
      Pre { K with Δ := Δ' } ρ' st' ∧ Rel { K with Δ := Δ' } ρ' φ π' st' (s.access pos (dataHit p.steps.2))

/-! ## The read of a place -/

/-- **`readPlace`, inverted** (a fact about the checker alone; STATED, for the machine lane): the access, then the
place's content at the variable's position (not `⊥`; D111's internal check and the unsized check pass), then, in the
plain mode, the read leaves the place (`ReadCopies`: a proof, or a non-borrow at a place the aligned table reads as
copying) or writes `⊥` there (a borrow always; a value not partly moved otherwise, D53). Bookkeeping only around the
two; the read keeps the mode, the frames and the top readings (`Kept`). -/
def ReadInvD : Prop :=
  ∀ (n : Nat) (p : Place) (st st' : MState) (bh : Nat) (v : Value) (D : Decisions),
    ModeR st → DecTab D st' → Runs (Ochr.readPlace (n + 1) p) st bh v st' →
    ∃ (stA : MState) (pos : Pos) (bA : Nat),
      Runs (do Ochr.accessPath n p; Ochr.accessInside n p) st bA () stA ∧ DecTab D stA ∧
      ckVarPos st.env p.steps.1 = some pos ∧ (valAt stA.env pos).follow p.steps.2 = some v ∧ v ≠ .bot ∧
      Kept stA st' ∧ st'.typing = stA.typing ∧
      (ReadCopies v (D.copy (D.placeDecl (DecideScope.topReadings stA) p)) → Kern stA st') ∧
      (¬ ReadCopies v (D.copy (D.placeDecl (DecideScope.topReadings stA) p)) →
        ((∀ l w, v ≠ .borrow l w) → v.hasHole = false) ∧
        ∃ E', ckSetBot stA.env pos p.steps.2 = some E' ∧ Kern { stA with env := E' } st')

/-- **A read of a place holding a borrow finds the borrow's content whole** (a fact about the checker alone; FALSE
today, TRUE after main's D127, the lead's ruling (A) on D181, D182): `readPlace`'s borrow branch runs before the
`hasHole` test every other moved value meets. Pin: `PlaceGuards.readR` (at `MB2`'s point the read returns a borrow
over `(⊥, σb)`; it fails after D127), beside `MB1` (accepted) and `MB3` (rejected). -/
def BorrowReadWhole : Prop :=
  ∀ (n : Nat) (p : Place) (st st' : MState) (bh : Nat) (v : Value),
    Runs (Ochr.readPlace n p) st bh v st' → ∀ l w, v = .borrow l w → w.hasHole = false

/-- **The read after its access** (mixed; STATED; the model's half of the read): at the checker's state after the
access, related to the reference's state after its own access, the reference's `readPlace` of `p` at the copy
decision `c` (the aligned table's, the checker's) succeeds in a typed run (in an untyped one it is an entry condition)
and gives the value the checker's content means, carrying its borrow's label; the states after are related with the
value in flight: the place unchanged where the checker copies, `⊥` against the reference's `moved` where it moves (a
whole borrow parked in a temporary on both sides, `rel_moveOut`'s case; a field path through `Sem.updAt`,
`botWrite_rel`'s). A borrow read is whole (`hbw`, from `BorrowReadWhole`): as first stated, without it, FALSE at a
borrow whose content is partly moved (`PlaceGuards.MB2`, D181). -/
def ReadOutG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (stA stR : MState) (s : SState) (p : Place)
    (pos : Pos) (v : Value) (c : Bool),
    0 < stA.env.size → resolve s p = some (pos, p.steps.2) → Strict.SGood K.dm K.Γ φ s →
    AccessOk K φ s pos (dataHit p.steps.2) →
    Pre K ρ stA → Rel K ρ φ π stA (s.access pos (dataHit p.steps.2)) →
    (valAt stA.env pos).follow p.steps.2 = some v → v ≠ .bot →
    K.D.copy (K.D.placeDecl (DecideScope.topReadings stA) p) = c →
    (stA.typing = false → (readPlace K φ p c s).isSome) →
    (ReadCopies v c → stR = stA) →
    (¬ ReadCopies v c → ((∀ l w, v ≠ .borrow l w) → v.hasHole = false) ∧
      ∃ E', ckSetBot stA.env pos p.steps.2 = some E' ∧ stR = { stA with env := E' }) →
    (∀ l w, v = .borrow l w → w.hasHole = false) →
    ∃ (r : Res) (s' : SState), readPlace K φ p c s = some (r, s') ∧
      meanV K ρ (fun l => φ (π l)) r.2 v = r.1 ∧ r.2.label = (Value.heldLabel v).map π ∧
      Pre K ρ (stR.withTempT v none) ∧ Rel K ρ φ π (stR.withTempT v none) s'

/-- `readPlace` of a structure update of the context at `Δ` is `readPlace` at the context (it reads the data model,
the declarations and the decisions only). -/
theorem readPlace_withΔ (K : RunCtx) (Δ : Nat → TyS) (φ : Future) (p : Place) (c : Bool) :
    readPlace { K with Δ := Δ } φ p c = readPlace K φ p c := rfl

theorem contentOk_withΔ (K : RunCtx) (Δ : Nat → TyS) (φ : Future) (p : Place) :
    ContentOk { K with Δ := Δ } φ p = ContentOk K φ p := rfl

/-- **The checker's `readPlace` simulates the reference's** (`readPlace_step_stmt` in the master's form), PROVED from
`ReadInvD`, `BorrowReadWhole` (checker), `AccessG`, `ReadOutG` (mixed). -/
theorem readPlace_sim (hRI : ReadInvD) (hBW : BorrowReadWhole) (hA : AccessG) (hRO : ReadOutG) {K : RunCtx} {ρ : Assignment} {φ : Future}
    {π : Nat → Nat} {st st' : MState} {s : SState} {p : Place} {v : Value} {n bh : Nat}
    (hm : ModeR st) (hne : 0 < st.env.size) (hp : Pre K ρ st) (hr : Rel K ρ φ π st s)
    (hS : Strict.SGood K.dm K.Γ φ s)
    (hok : st.typing = false →
      (SM.guarded (ContentOk K φ p) (readPlace K φ p (K.D.copy (K.D.placeDecl (scopeOf s) p))) s).isSome)
    (hD : DecTab K.D st') (h : Runs (Ochr.readPlace (n + 1) p) st bh v st') :
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (r : Res) (s' : SState),
      Ext K ρ π st st' ρ' Δ' π' ∧
      SM.guarded (ContentOk K φ p) (readPlace K φ p (K.D.copy (K.D.placeDecl (scopeOf s) p))) s = some (r, s') ∧
      meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧ r.2.label = (Value.heldLabel v).map π' ∧
      Pre { K with Δ := Δ' } ρ' (st'.withTempT v none) ∧ Rel { K with Δ := Δ' } ρ' φ π' (st'.withTempT v none) s' ∧
      Kept st st' ∧ st'.typing = st.typing := by
  obtain ⟨stA, pos, bA, hacc, hDA, hpos, hcont, hnb, hmA, htyA, hcp, hmv⟩ := hRI n p st st' bh v K.D hm hD h
  have hres : resolve s p = some (pos, p.steps.2) := rel_resolve_ck K ρ φ st s π p pos hr hpos
  -- the copy decision: the reference's scope is the checker's, which the access keeps
  have hsc := scopeOf_rel hr
  -- the strict tests of the access, from the reference's success in an untyped run
  have hokA : st.typing = false → AccessOk K φ s pos (dataHit p.steps.2) := fun e => by
    have := hok e
    revert this
    unfold SM.guarded
    split
    · rename_i hc; unfold ContentOk at hc; rw [hres] at hc; exact fun _ => hc
    · simp
  obtain ⟨hAok, ρ', Δ', π', hext, hkept, htyp, hpA, hrA⟩ := hA K ρ φ π st stA s p pos n bA hm hne hp hr hS hres hokA hDA hacc
  have hsc' : scopeOf s = DecideScope.topReadings stA := by rw [hsc, hkept.top]
  have hneA : 0 < stA.env.size := by rw [hkept.size]; exact hne
  -- the reference's read is not guarded away: the access's tests pass
  have hguard : SM.guarded (ContentOk K φ p) (readPlace K φ p (K.D.copy (K.D.placeDecl (scopeOf s) p))) s =
      readPlace K φ p (K.D.copy (K.D.placeDecl (scopeOf s) p)) s :=
    SM.guarded_of (by unfold ContentOk; rw [hres]; exact hAok)
  -- the read itself, on the state after the access
  generalize hc : K.D.copy (K.D.placeDecl (scopeOf s) p) = c at hok hguard ⊢
  have hcA : (({ K with Δ := Δ' } : RunCtx).D.copy (({ K with Δ := Δ' } : RunCtx).D.placeDecl
      (DecideScope.topReadings stA) p)) = c := by rw [← hc, hsc']
  -- the checker's state after the read, as `ReadOutG` takes it
  obtain ⟨stR, hR₁, hR₂, hkR, hRa, hRl⟩ : ∃ stR, (ReadCopies v c → stR = stA) ∧
      (¬ ReadCopies v c → ((∀ l w, v ≠ .borrow l w) → v.hasHole = false) ∧
        ∃ E', ckSetBot stA.env pos p.steps.2 = some E' ∧ stR = { stA with env := E' }) ∧ Kern stR st' ∧
      stR.absTy = stA.absTy ∧ stR.nextLoan = stA.nextLoan := by
    by_cases hrc : ReadCopies v c
    · refine ⟨stA, fun _ => rfl, fun h => absurd hrc h, hcp ?_, rfl, rfl⟩
      rw [← hsc', hc]; exact hrc
    · obtain ⟨hh, E', hE', hk⟩ := hmv (by rw [← hsc', hc]; exact hrc)
      exact ⟨{ stA with env := E' }, fun h => absurd h hrc, fun _ => ⟨hh, E', hE', rfl⟩, hk, rfl, rfl⟩
  obtain ⟨r, s', hrd, hmean, hlab, hpR, hrR⟩ := hRO { K with Δ := Δ' } ρ' φ π' stA stR s p pos v c hneA hres hS hAok
    hpA hrA hcont hnb hcA
    (fun e => by
      have := hok (by rw [← htyp]; exact e)
      rw [hguard] at this; exact this)
    hR₁ hR₂ (hBW (n + 1) p st st' bh v h)
  refine ⟨ρ', Δ', π', r, s', ?_, by rw [hguard]; exact hrd, hmean, hlab,
    Pre.of_kern (hkR.withTempT v none) hpR, Rel.of_kern (hkR.withTempT v none) hrR, ?_, ?_⟩
  · exact hext.congr rfl rfl (hRa.symm.trans hkR.absTy) (hRl.symm.trans hkR.nextLoan)
  · exact hkept.trans hmA
  · rw [htyA, htyp]

/-! ## The step -/

/-- **`eval` around `evalCore` hands it the typing flag** (a fact about the checker alone; STATED, for the machine
lane: `EvalInvD` with one more conjunct, `evalAt`'s `modify typing := typed` before `evalCore`). The read's strict
end tests come from the checker's own tests only where the checker runs [Repack], which it does in a typed run
(`typing`); `CoreSimK` does not say which runs those are. -/
def EvalInvDT : Prop :=
  ∀ (n : Nat) (typed : Bool) (t : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (D : Decisions),
    ModeR st → DecTab D st' → (∀ w, t ≠ .val w) → (∀ f as h, t ≠ .call f as h) →
    D.declOf (DecideScope.topReadings st) t ≠ .any → (D.declOf (DecideScope.topReadings st) t).isProof = false →
    (st.tailDecl = none ∨ st.tailDecl = some (D.declOf (DecideScope.topReadings st) t)) →
    Runs (Ochr.eval (n + 2) typed t hint) st bh (v, T?) st' →
    ∃ (st₀ st₁ : MState) (bh' : Nat), Kern st st₀ ∧ ModeEq st st₀ ∧ st₀.curTail = st.tailNext ∧
      st₀.tailNext = false ∧ st₀.tailDecl = none ∧ st₀.curDecl = some (D.declOf (DecideScope.topReadings st₀) t) ∧
      st₀.typing = typed ∧
      Runs (Ochr.evalCore n typed t hint) st₀ bh' (v, T?) st₁ ∧ Kern st₁ st' ∧ ModeEq st₁ st'

/-- `CoreSimK` from states whose typing flag is the run's (`EvalInvDT`). -/
def CoreSimKT (K : RunCtx) (ρ : Assignment) (φ : Future) (n : Nat) (t : Term) (P : MState → Prop := fun _ => True) :
    Prop :=
  ∀ (st st' : MState) (typed : Bool) (hint : Option Value) (v : Value) (T? : Option Value) (s : SState)
    (π : Nat → Nat),
    P st → st.typing = typed → ModeR st → (typed = true → st.curTail = false) → st.tailNext = false →
    st.tailDecl = none →
    st.curDecl = some (K.D.declOf (DecideScope.topReadings st) t) → Pre K ρ st → Rel K ρ φ π st s →
    Strict.SGood K.dm K.Γ φ s →
    t.valsOk (Strict.ValsP K ρ φ) → t.absBelow st.absTy.size → HintBelow hint st.absTy.size → t.hasHolePrim = false →
    K.D.flags (scopeOf s) t = (false, false) →
    (typed = false → (runT K ρ φ st.curTail (hintM K ρ hint) t s).isSome) →
    DecTab K.D st' →
    ∀ bh, Runs (Ochr.evalCore n typed t hint) st bh (v, T?) st' →
    Out K ρ φ π st st' s (runT K ρ φ st.curTail (hintM K ρ hint) t) v T? ∧ Kept st st'

/-- **`eval` around `evalCore`, with the typing flag**: `eval_of_coreK` from `CoreSimKT`. -/
theorem eval_of_coreKT {K : RunCtx} {ρ : Assignment} {φ : Future} (hE : EvalInvDT) {n : Nat} {t : Term}
    {P : MState → Prop}
    (hP : ∀ a b, Kern a b → P a → P b) (ht : ∀ w, t ≠ .val w) (hcall : ∀ f as h, t ≠ .call f as h)
    (hany : ∀ st, P st → K.D.declOf (DecideScope.topReadings st) t ≠ .any ∧
      (K.D.declOf (DecideScope.topReadings st) t).isProof = false) (hc : CoreSimKT K ρ φ n t P) :
    EvalSimK K ρ φ (n + 2) t P := by
  intro st st' typed hint v T? s π hPs _ hm htl htd hp hr hS hv hab hhb hnh hfl hok hD bh h
  obtain ⟨st₀, st₁, bh', hk₀, hm₀, hct, htn, htd₀, hcd₀, hty₀, h₀, hk₁, hm₁⟩ :=
    hE n typed t hint st st' bh v T? K.D hm hD ht hcall (hany st hPs).1 (hany st hPs).2 htd h
  obtain ⟨hc', hkp⟩ := hc st₀ st₁ typed hint v T? s π (hP st st₀ hk₀ hPs) hty₀ (hm.of_modeEq hm₀)
    (fun e => hct.trans (htl e)) htn htd₀ hcd₀ (hp.of_kern hk₀) (hr.of_kern hk₀) hS hv
    (by rw [← hk₀.absTy]; exact hab) (by rw [← hk₀.absTy]; exact hhb) hnh hfl (by rw [hct]; exact hok)
    (DecTab.of_kern hk₁.symm hD) bh' h₀
  rw [hct] at hc'
  exact ⟨Out.of_kern hk₀ hk₁ hc', ((Kept.of_kern hk₀ hm₀).trans hkp).trans (Kept.of_kern hk₁ hm₁)⟩

/-- The place's type and, typed, its [Repack] whole: the first two lines of `evalCore`'s `.place` clause. -/
def placeTyPart (n : Nat) (typed want : Bool) (p : Place) : M (Option Value) := do
  let T ← if typed then some <$> Ochr.placeType n p else if want then Ochr.placeType? n p else pure none
  if typed then if let some T := T then Ochr.repackAt n p T "read whole"
  pure T

/-- **`evalCore` of a direct place read, inverted** (a fact about the checker alone; STATED, guarded below): no
projection to run as a match (`projIn` finds none), then the type part (`placeTyPart`, at the wanted flag), then
`readPlace` at the same fuel; `readPlace 0` is out of fuel. -/
def PlaceInvD : Prop :=
  ∀ (m : Nat) (typed : Bool) (p : Place) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value),
    p.Direct → Runs (Ochr.evalCore (m + 1) typed (.place p) hint) st bh (v, T?) st' →
    ∃ (n : Nat) (st₁ : MState) (b₁ b₂ : Nat), m = n + 1 ∧
      Runs (placeTyPart m typed st.wantHere p) st b₁ T? st₁ ∧ Runs (Ochr.readPlace m p) st₁ b₂ v st'

/-- **The place's type** (mixed; STATED): the checker's type part (a private computation: a field's type evaluates
the declaration's field types, a dependent one through the borrows of earlier fields, D117; [Repack] may make
unknowns) keeps the entry conditions under an extension, leaves the reference untouched, names only unknowns below the
counter, and its type, if any, is the reference's read's type (a typed run has one). -/
def PlaceTypeG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st st₁ : MState) (s : SState) (p : Place)
    (n bh : Nat) (typed want : Bool) (T? : Option Value),
    ModeR st → 0 < st.env.size → Pre K ρ st → Rel K ρ φ π st s → Strict.SGood K.dm K.Γ φ s →
    Runs (placeTyPart n typed want p) st bh T? st₁ →
    (typed = true → T?.isSome) ∧
    ∃ (ρ₁ : Assignment) (Δ₁ : Nat → TyS) (π₁ : Nat → Nat),
      Ext K ρ π st st₁ ρ₁ Δ₁ π₁ ∧ Kept st st₁ ∧ st₁.typing = st.typing ∧
      Pre { K with Δ := Δ₁ } ρ₁ st₁ ∧ Rel { K with Δ := Δ₁ } ρ₁ φ π₁ st₁ s ∧ HintBelow T? st₁.absTy.size ∧
      ∀ T, T? = some T → ∀ (c : Bool) (r : Res) (s' : SState), readPlace K φ p c s = some (r, s') →
        StrAgree { K with Δ := Δ₁ } ρ₁ T r.2

/-- The reference's run of a place the table reads as decided data: its guarded read at the aligned copy decision. -/
theorem runT_place (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (hint : TyS) (p : Place) (s : SState)
    (hfl : K.D.flags (scopeOf s) (.place p) = (false, false)) :
    runT K ρ φ tl hint (.place p) s =
      SM.guarded (ContentOk K φ p) (readPlace K φ p (K.D.copy (K.D.placeDecl (scopeOf s) p))) s := by
  rw [runT]; show SM.erasedIf (K.D.flags (scopeOf s) _) _ s = _; rw [hfl]; rfl

/-- The type in flight is not read by the entry conditions (`Env.erase` forgets a temporary's stored type). -/
theorem kern_withTempT_none (st : MState) (v : Value) (T? : Option Value) :
    Kern (st.withTempT v none) (st.withTempT v T?) :=
  ⟨by rw [erase_withTempT, erase_withTempT], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `StrAgree` is the hint's meaning at the type: moved across an extension as `hintM_congrA` moves it. -/
theorem strAgree_congrA {K : RunCtx} {ρ ρ₁ : Assignment} {Δ₁ : Nat → TyS} {T : Value} {R : TyS} {n : Nat}
    (hb : HintBelow (some T) n) (hag : ∀ σ, σ < n → ρ₁ σ = ρ σ ∧ Δ₁ σ = K.Δ σ) (h : StrAgree K ρ T R) :
    StrAgree { K with Δ := Δ₁ } ρ₁ T R := by
  have e := hintM_congrA (K := K) (ρ := ρ) (ρ₁ := ρ₁) (Δ₁ := Δ₁) hb hag
  show (hintM { K with Δ := Δ₁ } ρ₁ (some T)).m = R.m
  rw [e]; exact h

section
variable {K : RunCtx} {φ : Future}

/-- **The read of a direct place, at `evalCore`, in general** (typed or untyped, at every tail flag), from the five
facts `PlaceInvD` (checker), `PlaceTypeG` (mixed), `ReadInvD` (checker), `AccessG` (mixed), `ReadOutG` (mixed). -/
theorem place_coreT (hPI : PlaceInvD) (hPT : PlaceTypeG) (hRI : ReadInvD) (hBW : BorrowReadWhole) (hA : AccessG)
    (hRO : ReadOutG)
    {ρ : Assignment} {m : Nat} {p : Place} (hdir : p.Direct) :
    CoreSimKT K ρ φ (m + 1) (.place p) (fun st => 0 < st.env.size) := by
  intro st st' typed hint v T? s π hne hty hm _ _ _ _ hp hr hS _ _ _ _ hfl hok hD bh h
  obtain ⟨n, st₁, b₁, b₂, rfl, hT, hR⟩ := hPI m typed p hint st st' bh v T? hdir h
  obtain ⟨hTs, ρ₁, Δ₁, π₁, he₁, hK₁, hty₁, hp₁, hr₁, hb₁, hag₁⟩ :=
    hPT K ρ φ π st st₁ s p (n + 1) b₁ typed st.wantHere T? hm hne hp hr hS hT
  have hx := runT_place K ρ φ st.curTail (hintM K ρ hint) p s hfl
  obtain ⟨ρ', Δ', π', r, s', he', hrd, hmean, hlab, hp', hr', hK', hty'⟩ :=
    readPlace_sim (K := { K with Δ := Δ₁ }) hRI hBW hA hRO (hm.of_modeEq hK₁.mode) (by rw [hK₁.size]; exact hne) hp₁ hr₁ hS
      (fun e => by
        have := hok (by rw [← hty, ← hty₁]; exact e)
        rw [hx] at this; exact this)
      hD hR
  refine ⟨⟨ρ', Δ', π', r, s', he₁.trans he', by rw [hx]; exact hrd, hmean, ?_, hlab,
    Pre.of_kern (kern_withTempT_none st' v T?) hp', Rel.of_kern (kern_withTempT_none st' v T?) hr'⟩, hK₁.trans hK'⟩
  intro T hT'
  have hrd' := (SM.guarded_some hrd).2
  exact strAgree_congrA (K := { K with Δ := Δ₁ }) (n := st₁.absTy.size)
    (fun T' e => by cases e; exact hb₁ T hT') he'.agree (hag₁ T hT' _ r s' hrd')

/-- **The step for a direct place read, typed or untyped, at every tail flag, where the table reads it as decided
data** (docs/31 D181, D182), with what the run keeps. ASSUMES 7 facts: `EvalInvDT`, `PlaceInvD`, `ReadInvD`,
`BorrowReadWhole` (checker; the last FALSE today, true after main's D127), `PlaceTypeG`, `AccessG`, `ReadOutG` (each
part checker, part model). It uses no induction hypothesis (a read has no sub-run). -/
theorem stepPlace_direct (hET : EvalInvDT) (hPI : PlaceInvD) (hPT : PlaceTypeG) (hRI : ReadInvD)
    (hBW : BorrowReadWhole) (hA : AccessG) (hRO : ReadOutG) :
    ∀ n, IH K φ n → ∀ (Δ : Nat → TyS) (ρ : Assignment) (p : Place), p.Direct →
      EvalSimK { K with Δ := Δ } ρ φ n (.place p)
        (fun st => 0 < st.env.size ∧ K.D.declOf (DecideScope.topReadings st) (.place p) ≠ .any ∧
          (K.D.declOf (DecideScope.topReadings st) (.place p)).isProof = false) := by
  intro n _ Δ ρ p hdir
  by_cases hn : n < 3
  · intro st st' typed hint v T? s π _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bh h
    exact absurd h (Machine.evalLow n typed _ hint st st' bh _ hn (fun w e => by cases e))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  exact eval_of_coreKT (K := { K with Δ := Δ }) hET
    (fun a b hk ha => ⟨by rw [← ColumnC.size_of_erase hk.env]; exact ha.1,
      by rw [← ColumnC.topReadings_kern hk]; exact ha.2⟩)
    (fun w e => by cases e) (fun f as h e => by cases e) (fun st hst => hst.2)
    (fun st st' typed hint v T? s π hP => place_coreT (K := { K with Δ := Δ }) hPI hPT hRI hBW hA hRO hdir
      st st' typed hint v T? s π hP.1)

end

end Ochr.Meaning.Steps.Form.Master

/-! ## Pins of the stated checker facts, on the checker's own state at a hole (`AccessAttack.st1`: `x ↦ (σa, loan_0)`,
`r ↦ borrow_0 σb`; `x` is variable 1) -/

namespace Ochr.Meaning.Steps.Form.PlacePins
open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form.Master
open Ochr.Meaning.Steps.AccessAttack (st1 pf)

/-- Two runs agree: both succeed with the same value and type (compared exactly) and the same Ω. -/
def sameOut (a b : Outcome (Value × Option Value)) : Bool :=
  match a, b with
  | .ok (v, T) st, .ok (v', T') st' =>
    Value.exact v v' && (match T, T' with | some X, some Y => Value.exact X Y | none, none => true | _, _ => false) &&
      allPos st.env == allPos st'.env && (allPos st.env).all fun q => Value.exact (valAt st.env q) (valAt st'.env q)
  | _, _ => false

/-- `PlaceInvD`'s decomposition, run: the type part at the wanted flag, then `readPlace`, at `evalCore`'s fuel less
one. -/
def viaParts (typed : Bool) (p : Place) : M (Value × Option Value) := do
  let T ← placeTyPart 99 typed (← get).wantHere p
  let v ← Ochr.readPlace 99 p
  pure (v, T)

def core (typed : Bool) (p : Place) : Outcome (Value × Option Value) :=
  (runMachine (Ochr.evalCore 100 typed (.place p) none) st1 100000).1
def parts (typed : Bool) (p : Place) : Outcome (Value × Option Value) := (runMachine (viaParts typed p) st1 100000).1

-- `PlaceInvD`: typed and untyped, a copied field, the moved pair (its borrow ended first), the lent field
#guard sameOut (core true (pf 0 (.var 1))) (parts true (pf 0 (.var 1)))
#guard sameOut (core false (pf 0 (.var 1))) (parts false (pf 0 (.var 1)))
#guard sameOut (core true (.var 1)) (parts true (.var 1))
#guard sameOut (core false (.var 1)) (parts false (.var 1))
#guard sameOut (core true (pf 1 (.var 1))) (parts true (pf 1 (.var 1)))
-- control: the parts with the other flag give another type (typed `Nat`; untyped, not wanted, none)
#guard !sameOut (core true (pf 0 (.var 1))) (parts false (pf 0 (.var 1)))

/-- The state after `readPlace` of `p`, if it succeeds, with the value. -/
def readOut (p : Place) : Option (Value × MState) :=
  match (runMachine (Ochr.readPlace 100 p) st1 100000).1 with
  | .ok v st' => some (v, st')
  | _ => none

-- `ReadInvD`: reading the pair `x` ends `0` (the access) and moves `x` out (a pair is not a copy type)
#guard match readOut (.var 1) with
  | some (_, st') => !liveLoan st'.env 0 && Value.exact (valAt st'.env (.bind 1 3)) .bot
  | none => false
-- reading `x.0` copies (a number): `x` keeps its first field and `0` stays live (control: `x` is not `⊥`)
#guard match readOut (pf 0 (.var 1)) with
  | some (_, st') => liveLoan st'.env 0 && !Value.exact (valAt st'.env (.bind 1 3)) .bot
  | none => false

/-- The typing flags of the evaluations entered at call depth above 0 (`Config.recordDeep`), from `st1` at depth 1:
`S(x.0)`'s own entry, then its argument's, which `evalCore` of `S` runs at the state `eval` handed it. -/
def deepTyping (typed : Bool) : List Bool :=
  let st : MState := { st1 with depth := 1, cfg := { st1.cfg with recordDeep := true } }
  (runMachine (Ochr.eval 100 typed (.succ (.place (pf 0 (.var 1)))) none) st 100000).2.2.toList.filterMap fun
    | .deep false _ s => some s.typing | _ => none

-- `EvalInvDT`: the argument's evaluation is entered with the typing flag of the run around it
#guard (deepTyping true).getLast? == some true
#guard (deepTyping false).getLast? == some false
#guard (deepTyping true).length == 2

end Ochr.Meaning.Steps.Form.PlacePins
