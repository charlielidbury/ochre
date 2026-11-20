import Ochr.Meaning.Steps.Statements

/-!
# Decisions at an extended table of unknowns (the lead's (ii), docs/31 D57)

A step that creates unknowns extends the context's Δ; under the lead's (ii) it extends the
context's decisions with it, to the checker's decisions at the extended table. What then must not
be disturbed is stated here, and not proved:
- `decAligned_grow`, the one-sided transfer: where the table only grows (no old entry rewritten),
  the checker's answer on an input naming only old unknowns is the old one;
- `runT_congrD`/`meanV_congrD`, the congruence of the run in the decisions: two tables that agree
  on every input naming only old unknowns give a term or value naming only old unknowns the same
  run or meaning (the analogue of `AssignCongr.runT_congrA`).
Since main's D96 the decisions read no unknown's type, only its frozen reading (`absDecl`, written
once by `freshAbs`), so a refinement, which rewrites the types, keeps the decision core whole, and
a step that adds unknowns only extends it: the one-sided transfer is the only thing left of the
table here (docs/31 D65).
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

/-- A term's unknowns are below `n`. -/
def _root_.Ochr.Term.absBelow (n : Nat) (t : Term) : Prop := ∀ σ, t.anyAtom (· == .abs σ) = true → σ < n

theorem _root_.Ochr.Term.absBelow_mono {n m : Nat} {t : Term} (h : t.absBelow n) (hnm : n ≤ m) : t.absBelow m :=
  fun σ hσ => Nat.lt_of_lt_of_le (h σ hσ) hnm

/-- **Two decision tables agree on the inputs naming no unknown at or above `n`**: a place's or a
reading's decision names none (they read the readings in scope, not values); a term's names those
its embedded values hold. -/
structure _root_.Ochr.Meaning.Decisions.AgreeOld (n : Nat) (D D' : Decisions) : Prop where
  placeDecl : ∀ sc p, D'.placeDecl sc p = D.placeDecl sc p
  copy : ∀ r, D'.copy r = D.copy r
  flags : ∀ sc t, t.absBelow n → D'.flags sc t = D.flags sc t
  declOf : ∀ sc t, t.absBelow n → D'.declOf sc t = D.declOf sc t
  piSort : ∀ sc t, t.absBelow n → D'.piSort sc t = D.piSort sc t
  joinMoves : ∀ sc entry t, t.absBelow n → D'.joinMoves sc entry t = D.joinMoves sc entry t
  rePointed : ∀ sc t, t.absBelow n → D'.rePointed sc t = D.rePointed sc t
  typeDecl : ∀ sc t, t.absBelow n → D'.typeDecl sc t = D.typeDecl sc t
  blockCaps : ∀ sc entry t, t.absBelow n → D'.blockCaps sc entry t = D.blockCaps sc entry t

theorem _root_.Ochr.Meaning.Decisions.AgreeOld.refl (n : Nat) (D : Decisions) : D.AgreeOld n D :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem _root_.Ochr.Meaning.Decisions.AgreeOld.trans {n m : Nat} {D₁ D₂ D₃ : Decisions}
    (h₁ : D₁.AgreeOld n D₂) (h₂ : D₂.AgreeOld m D₃) (hnm : n ≤ m) : D₁.AgreeOld n D₃ where
  placeDecl sc p := (h₂.placeDecl sc p).trans (h₁.placeDecl sc p)
  copy r := (h₂.copy r).trans (h₁.copy r)
  flags sc t ht := (h₂.flags sc t (Term.absBelow_mono ht hnm)).trans (h₁.flags sc t ht)
  declOf sc t ht := (h₂.declOf sc t (Term.absBelow_mono ht hnm)).trans (h₁.declOf sc t ht)
  piSort sc t ht := (h₂.piSort sc t (Term.absBelow_mono ht hnm)).trans (h₁.piSort sc t ht)
  joinMoves sc e t ht := (h₂.joinMoves sc e t (Term.absBelow_mono ht hnm)).trans (h₁.joinMoves sc e t ht)
  rePointed sc t ht := (h₂.rePointed sc t (Term.absBelow_mono ht hnm)).trans (h₁.rePointed sc t ht)
  typeDecl sc t ht := (h₂.typeDecl sc t (Term.absBelow_mono ht hnm)).trans (h₁.typeDecl sc t ht)
  blockCaps sc e t ht := (h₂.blockCaps sc e t (Term.absBelow_mono ht hnm)).trans (h₁.blockCaps sc e t ht)

/-- `DecAligned` on the inputs naming only unknowns below `n` (a place's and a reading's decisions
name none). -/
structure DecAlignedBelow (n : Nat) (D : Decisions) (st : MState) : Prop where
  flags : ∀ fuel sc t fl b st', t.absBelow n → Runs (do
      let d ← withLive true (Ochr.declOf fuel false [] [] t)
      pure ((← Ochr.preFlags t d).getD (false, false))) (scopeState st sc) b fl st' → D.flags sc t = fl
  placeDecl : ∀ fuel sc p d b st', Runs (withLive true (Ochr.placeDecl fuel [] p)) (scopeState st sc) b d st' →
    D.placeDecl sc p = d
  declOf : ∀ fuel sc t d b st', t.absBelow n →
    Runs (withLive true (Ochr.declOf fuel false [] [] t)) (scopeState st sc) b d st' → D.declOf sc t = d
  copy : ∀ fuel r c b st', Runs (Ochr.declCopy fuel r) st b c st' → D.copy r = c
  piSort : ∀ fuel sc t l b st', t.absBelow n →
    Runs (withLive true (Ochr.sortOf fuel (.tPi [] t []))) (scopeState st sc) b l st' → D.piSort sc t = l
  joinMoves : ∀ fuel sc entry t ms b st', t.absBelow n →
    Runs (withLive true (Ochr.jdMoves fuel [] [] t entry)) (scopeState st sc) b ms st' → D.joinMoves sc entry t = ms
  rePointed : ∀ fuel sc t ts b st', t.absBelow n →
    Runs (withLive true (Ochr.typeState fuel t)) (scopeState st sc) b ts st' → D.rePointed sc t = ts.repointed
  typeDecl : ∀ fuel sc T d b st', T.absBelow n →
    Runs (withLive true (Ochr.typeDecl fuel false [] [] T)) (scopeState st sc) b d st' → D.typeDecl sc T = d

/-- A step that only adds unknowns: the decision core is kept but for the frozen readings, whose
old entries are kept (main's D96: the table is written once per unknown, by `freshAbs`, and kept
whole by `restoreKeep` and `exitWorld`). A refinement rewrites the unknowns' TYPES, which no
decision reads since D96, so it keeps the decision core whole (`DecCore`). -/
structure Grows (st st' : MState) : Prop where
  globals : st.globals = st'.globals
  inds : st.inds = st'.inds
  liveScope : st.liveScope = st'.liveScope
  live : ∀ i, DecideScope.liveVal st i = DecideScope.liveVal st' i
  size : st.absDecl.size ≤ st'.absDecl.size
  old : ∀ σ, σ < st.absDecl.size → st'.absDecl[σ]? = st.absDecl[σ]?

/-- **The one-sided transfer** (the lead's (ii)): where the table only grows, the checker's
decisions on inputs naming only old unknowns are the old ones. Since main's D96 a decision reads an
unknown only by its frozen reading (`absReading σ`, `absDecl[σ]`), never by its type, so what is
open is only the simulation of `Decide.lean` (`DecideScope.decideSim`) for tables whose old entries
agree, carrying that every unknown a decision reads is one its input or Σ names (a closure's
captures are read by their recorded readings, `capReadings`). A refinement is not growth and needs
nothing: it keeps the decision core whole. -/
theorem decAligned_grow {D : Decisions} {st st' : MState} (hd : DecAligned D st) (hg : Grows st st') :
    DecAlignedBelow st.absDecl.size D st' := by
  sorry

/-- **The congruence of the run in the decisions** (the lead's (ii); the analogue of
`AssignCongr.runT_congrA`): the run asks the decisions only of the term it runs, its subterms and
the readings in scope (its state holds meanings, not values), so two tables agreeing on the inputs
naming only unknowns below `n` give a term naming only those the same run. Stated, NOT proved, by
the lead's instruction (large, very likely true, nothing depends on a proof yet). -/
theorem runT_congrD (K : RunCtx) (ρ : Assignment) (φ : Future) (D' : Decisions) (n : Nat)
    (hD : K.D.AgreeOld n D') (tl : Bool) (t : Term) (hint : TyS) (s : SState) (ht : t.absBelow n) :
    runT K ρ φ tl hint t s = runT { K with D := D' } ρ φ tl hint t s := by
  sorry

/-- The congruence for a value's meaning (its sealed programs and closures run their terms). Stated,
NOT proved, with `runT_congrD`. -/
theorem meanV_congrD (K : RunCtx) (ρ : Assignment) (φ : Future) (D' : Decisions) (n : Nat)
    (hD : K.D.AgreeOld n D') (hint : TyS) (v : Value) (hv : ∀ σ, v.anyAtom (· == .abs σ) = true → σ < n) :
    meanV K ρ φ hint v = meanV { K with D := D' } ρ φ hint v := by
  sorry

end Ochr.Meaning.Steps
