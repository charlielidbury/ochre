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

-- `Term.absBelow` and `Decisions.AgreeOld` moved to `Steps/Statements.lean` (docs/31 D75: the
-- statement form extends the context's decisions with its `Δ`).

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
