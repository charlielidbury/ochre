import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.RunLib
import Ochr.Meaning.Steps.Machine.All
import Ochr.Meaning.Steps.Machine.False
import Ochr.Meaning.Steps.Machine.DecideFuel
import Ochr.Meaning.Steps.Machine.DecideFuelFF

/-!
# Facts about the machine alone (the slice, main's decision 2026-11-20; its own lane)

The context's decisions `K.D` are FIXED for a whole run of an item: the checker's own decisions
at the item's final state (`Consistency.const_split` builds the context so, `P.ctx dm D st'`). A
step statement assumes them aligned with the checker's tables at the state AFTER it
(`DecTab K.D st'`) and concludes `CtxOk` there under the same decisions; an assembly obtains that
hypothesis for each part of its run from its own, through (a) and (b) below:
- (a) a successful run of a machine function only extends the tables a decision reads
  (`TablesGrow`): the globals and the declarations are kept, the frozen readings `absDecl` only
  grow (an old entry is never rewritten, main's D96), and the counters are not lowered;
- (b) the decisions aligned at a larger table are aligned at a smaller one (`DecTab.back`).

**Fresh names are never reused within an item.** `freshAbs` pushes, and every exit from a private
computation (`inStatement`'s restore, `exitWorld`, and since main's amendment of the comparison
fix the comparison's exit) keeps `nextAbs`, `nextLoan`, `absDecl` and the new tail of `absTy`,
dropping only the records made inside. So one table answers for every unknown the run creates: the
proof relies on this here, and only here.

Nothing in this file mentions the model: no assignment, no reference state, no meaning.

## Other facts the proof owes that are about the machine alone

To be stated here as they are reached (from the slice's knowledge, 2026-11-20):
- the block's captures at a state (D90's obligation 1, per state): `Decisions.blockCaps` of the
  checker is static (`BlockCaps.staticBlockCaps`), reading the state only through the top frame's
  readings and the entry set (its `⊥` places), so with the table fixed the clause `CtxOk.dec`'s
  `blockCaps` asks at a state is a fact about the checker alone: at the state's readings and entry
  set, the static instance is what `Steps.ckBlockCaps` computes there. A write of `⊥` (the join's
  drop) changes only the entry set, so `ctx_botWrite`'s open part is this fact at the state after.
  Measured (the slice, item 4, 2026-11-20; probe at every `Machine.blockEntry` of the suite, on the
  recorded state): 338 block entries, the static instance equal to the checker's captures at all 335
  where the checker's run succeeds (252 with a nonempty entry set); the other 3 are the checker's own
  [Join] rejections (`JoinPlaces.BadIdx`, `BadIdxRead`, `BadDerefRead`), where nothing is asked.
  `CtxOk` asks it for every match term at every state, where the run reads it only at a block's
  entry; stating it there (the [Entry] step's hypothesis) would spare every other step re-proving it;
- an access loses no unknown the state names, and makes only unknowns nothing names
  (`repackCheck`'s `lentUnknown`, docs/31 D35, D57);
- a decision's run leaves the state as it was (PROVED for the decisions the slice reads,
  `Slice.DecideKeep`), and a successful run at one fuel is a successful run with the same answer
  at every larger fuel (the decisions are asked at any fuel, `DecAligned`): PROVED for every field of
  `Decisions` but `blockCaps` (`Machine.fuelAgree_flags`, `_placeDecl`, `_declOf`, `_copy`, `_piSort`,
  `_joinMoves`, `_rePointed`, `_typeDecl`: two successes at any fuels and budgets agree;
  `Machine.FuelMono`). The checker's block captures (`ckBlockCaps`) run the machine itself
  (`movedPlace`, `blockCaptures`), so theirs is a fuel induction over the whole machine block, and
  `blockCaptures` (now fuel-bounded) make it a relational induction over the whole block, not yet done;
- a comparison's private copy leaves no record naming an unknown it made (main's comparison fix),
  and `placeType?`'s private copies likewise (to be swept before `placeType?`'s step is stated);
- (WF1)–(WF16) and `ShapeFacts` are kept by every step: about checker states only, but each step's
  proof reads its own; listed here so that whoever proves (a) can collect the ones whose proof
  is a closure induction of the same shape.
-/

namespace Ochr.Meaning.Steps

open Ochr Ochr.Meaning

/-! `TablesGrow`, `GrowsM` and their closure lemmas are in `Steps/Machine/Defs.lean` (imported here);
the proofs of (a) are under `Steps/Machine/` (its `HANDOFF.md` says how they go). -/

/-! ## (b) Alignment at a larger table is alignment at a smaller one -/

/-- **(b) The transfer of alignment from a larger table to a smaller.** A decision whose run succeeds
at `st` reads only the tables' old entries (it names only unknowns `st` has, and their readings are
frozen), so it succeeds at `st'` with the same answer, which the decisions give. The one-way
simulation of `Decide.lean` (`DecideScope.decideSim`) for tables whose old entries agree, the
converse direction of the removed `DecExtend.decAligned_grow` and the same lemma underneath. Open (the machine
lane). -/
theorem DecTab.back {D : Decisions} {st st' : MState} (hd : DecTab D st') (hg : TablesGrow st st') :
    DecTab D st := by
  sorry

/-- An assembly's tool: the decisions after the whole run are aligned after a part of it, where
the rest of the run only extends the tables. -/
theorem DecTab.of_rest {α : Type} {D : Decisions} {st₁ st' : MState} {rest : M α} {b : Nat} {a : α}
    (hd : DecTab D st') (hrest : GrowsM rest) (h : Runs rest st₁ b a st') : DecTab D st₁ :=
  hd.back (h.grows hrest)

/-! ## (a) Every machine function's successful run only extends the tables

One statement per machine function an assembly runs, at every fuel (added as the change of form
reaches each assembly). The proof is one closure induction over the machine's mutual block
(`Slice.DecideKeep`'s technique, with `TablesGrow` in place of equality): every write of the
state either keeps the tables (the frames, the flags, the log, the records), or pushes an unknown
(`freshAbs`), or is a private computation's exit, which keeps the names (the module docstring).
Open (the machine lane). -/

open Machine in
section
theorem grows_content (p : Place) : GrowsM (Ochr.content p) := growsM_of_growsIn fun _ => growsIn_content p
theorem grows_content? (p : Place) : GrowsM (Ochr.content? p) := growsM_of_growsIn fun _ => growsIn_content? p
theorem grows_ppPlace (p : Place) : GrowsM (Ochr.ppPlace p) := growsM_of_growsIn fun _ => growsIn_ppPlace p
theorem grows_absType (σ : Nat) : GrowsM (Ochr.absType σ) := growsM_of_growsIn fun _ => growsIn_absType σ
theorem grows_lookupInd (n : String) : GrowsM (Ochr.lookupInd n) := growsM_of_growsIn fun _ => growsIn_lookupInd n
theorem grows_recordedNeutral (v : Value) : GrowsM (Ochr.recordedNeutral v) :=
  growsM_of_growsIn fun _ => growsIn_recordedNeutral v
theorem grows_setPlace (p : Place) (v : Value) : GrowsM (Ochr.setPlace p v) := growsM_of_growsIn fun _ => growsIn_setPlace p v
theorem grows_logEffect (p : Place) (k : String) : GrowsM (Ochr.logEffect p k) :=
  growsM_of_growsIn fun _ => growsIn_logEffect p k
theorem grows_movedPlace (fuel : Nat) (q : Place) : GrowsM (Ochr.movedPlace fuel q) :=
  growsM_of_growsIn fun _ => (machineGrows fuel).movedPlace q
theorem grows_accessPath (fuel : Nat) (p : Place) : GrowsM (Ochr.accessPath fuel p) :=
  growsM_of_growsIn fun _ => (machineGrows fuel).accessPath p
theorem grows_accessInside (fuel : Nat) (p : Place) (o : Bool) : GrowsM (Ochr.accessInside fuel p o) :=
  growsM_of_growsIn fun _ => (machineGrows fuel).accessInside p o
theorem grows_endBorrow (fuel : Nat) (l : Nat) : GrowsM (Ochr.endBorrow fuel l) :=
  growsM_of_growsIn fun _ => (machineGrows fuel).endBorrow l
theorem grows_etaInPlace (fuel σ : Nat) (d : IndDecl) (ps : List Value) :
    GrowsM (Ochr.etaInPlace fuel σ d ps) := growsM_of_growsIn fun _ => (machineGrows fuel).etaInPlace σ d ps
theorem grows_placeTypeQ (fuel : Nat) (p : Place) : GrowsM (Ochr.placeType? fuel p) :=
  growsM_of_growsIn fun _ => (machineGrows fuel).placeType? p
theorem grows_substEnv (fuel : Nat) (x r : Value) (t : Bool) : GrowsM (Ochr.substEnv fuel x r t) :=
  growsM_of_growsIn fun _ => (machineGrows fuel).substEnv x r t
theorem grows_generalizeNeutral (fuel : Nat) (p : Place) (n : Value) :
    GrowsM (Ochr.generalizeNeutral fuel p n) := growsM_of_growsIn fun _ => (machineGrows fuel).generalizeNeutral p n
theorem grows_renormAll (fuel : Nat) : GrowsM (Ochr.renormAll fuel) :=
  growsM_of_growsIn fun _ => (machineGrows fuel).renormAll
theorem grows_refine (fuel σ : Nat) (r : Value) : GrowsM (Ochr.refine fuel σ r) :=
  growsM_of_growsIn fun _ => (machineGrows fuel).refine σ r
theorem grows_dropAtJoin (fuel : Nat) (q : Place) : GrowsM (Ochr.dropAtJoin fuel q) :=
  growsM_of_growsIn fun _ => (machineGrows fuel).dropAtJoin q

/-- FALSE as stated (`Machine.not_grows_restoreKeep`, kernel-checked): `restoreKeep saved` takes the
globals and the declarations from `saved`. It keeps the tables when `saved` has the current ones,
which holds at every use in the machine: `restoreKeep_grows` below, `Machine.growsIn_restoreKeep`.
Kept (with its `sorry`) only while its users (`EqJAsm.eq_step_asm`) move to `restoreKeep_grows`. -/
theorem grows_restoreKeep (saved : MState) : GrowsM (Ochr.restoreKeep saved) := by sorry
/-- **`restoreKeep` to an earlier state of the same run only extends the tables** (the corrected
`grows_restoreKeep`): the snapshot `saved` is a state the run has grown from (`TablesGrow saved cur`),
so it has the current globals and declarations, which are all `restoreKeep` takes from it. -/
theorem restoreKeep_grows {saved cur st' : MState} {b : Nat} (hs : TablesGrow saved cur)
    (h : Runs (Ochr.restoreKeep saved) cur b () st') : TablesGrow cur st' :=
  (growsIn_restoreKeep (G := (saved.globals, saved.inds)) ⟨rfl, rfl⟩).runs ⟨hs.globals, hs.inds⟩ h
theorem grows_expectTy (fuel : Nat) (w : String) (T : Option Value) (A : Value) :
    GrowsM (Ochr.expectTy fuel w T A) := growsM_of_growsIn fun _ => (machineGrows fuel).expectTy w T A
theorem grows_mkEqM (fuel : Nat) (A a b : Value) : GrowsM (Ochr.mkEqM fuel A a b) :=
  growsM_of_growsIn fun _ => (machineGrows fuel).mkEqM A a b
theorem grows_evalType (fuel : Nat) (t : Term) : GrowsM (Ochr.evalType fuel t) :=
  growsM_of_growsIn fun _ => (machineGrows fuel).evalType t
theorem grows_eval (fuel : Nat) (typed : Bool) (t : Term) (hint : Option Value) :
    GrowsM (Ochr.eval fuel typed t hint) := growsM_of_growsIn fun _ => (machineGrows fuel).eval typed t hint
theorem grows_blockEntry (fuel : Nat) (mt : Term) : GrowsM (Ochr.blockEntry fuel mt) :=
  growsM_of_growsIn fun _ => (machineGrows fuel).blockEntry mt
/-- FALSE as stated: the arms run inside `closeBlock`, and an arm's world exit (`exitWorld`) keeps
the arm's frozen readings and counters, so an arm that lowers them leaves them lowered. True when
every arm only extends the tables: `grows_closeBlock_of`. Kept (with its `sorry`) only while its
user (`EqJAsm`) moves to `grows_closeBlock_of`. -/
theorem grows_closeBlock (fuel : Nat) (mt : Term) (arms : List BlockArm) (B? : Option Value) :
    GrowsM (Ochr.closeBlock fuel mt arms B?) := by sorry
/-- `closeBlock` whose arms only extend the tables only extends the tables. -/
theorem grows_closeBlock_of (fuel : Nat) (mt : Term) (arms : List BlockArm) (B? : Option Value)
    (h : ∀ a ∈ arms, GrowsM a.setup ∧ ∀ r, GrowsM (a.body r)) : GrowsM (Ochr.closeBlock fuel mt arms B?) :=
  growsM_of_growsIn fun _ => (machineGrows fuel).closeBlock mt arms
    (fun a ha => ⟨growsIn_of_growsM (h a ha).1, fun r => growsIn_of_growsM ((h a ha).2 r)⟩) B?
theorem grows_joinDrop (fuel : Nat) (mt : Term) {run : M (Value × Option Value)} (h : GrowsM run) :
    GrowsM (Ochr.joinDrop fuel mt run) :=
  growsM_of_growsIn fun _ => (machineGrows fuel).joinDrop mt run (growsIn_of_growsM h)
theorem grows_demand (b : Bool) : GrowsM (Ochr.demand b) := growsM_of_growsIn fun _ => growsIn_demand b
theorem grows_getFlags : GrowsM Ochr.getFlags := growsM_of_growsIn fun _ => growsIn_getFlags
theorem grows_setFlags (f : Bool × Bool) : GrowsM (Ochr.setFlags f) := growsM_of_growsIn fun _ => growsIn_setFlags f

theorem grows_wholeReturned (v : Value) : GrowsM (Ochr.wholeReturned v) :=
  growsM_of_growsIn fun _ => growsIn_wholeReturned v
theorem grows_pushTempAt (f : Nat) (v : Value) (T : Option Value) (site : String) :
    GrowsM (Ochr.pushTempAt f v T site) := growsM_of_growsIn fun _ => growsIn_pushTempAt f v T site
theorem grows_topIdx : GrowsM Ochr.topIdx := growsM_of_growsIn fun _ => growsIn_topIdx
theorem grows_popFrame (fuel : Nat) : GrowsM (Ochr.popFrame fuel) :=
  growsM_of_growsIn fun _ => (machineGrows fuel).popFrame
theorem grows_popTemp : GrowsM Ochr.popTemp := growsM_of_growsIn fun _ => growsIn_popTemp
theorem grows_lendEnv (fuel : Nat) (op : LendOp) : GrowsM (Ochr.lendEnv fuel op) :=
  growsM_of_growsIn fun _ => growsIn_lendEnv fuel op
theorem grows_observe (fuel : Nat) (typed : Bool) (t : Term) (A : Value) (W : List Pos)
    (refs : List (Place × Value × Value)) : GrowsM (Ochr.observe fuel typed t A W refs) :=
  growsM_of_growsIn fun _ => (machineGrows fuel).observe typed t A W refs []
end

/-- One step of the closure: a combinator or a machine function's statement. -/
macro "grows_step" : tactic => `(tactic| first
  | with_reducible exact GrowsM.pure _
  | with_reducible exact GrowsM.get
  | with_reducible exact GrowsM.err _
  | with_reducible exact GrowsM.exhausted _
  | with_reducible exact grows_content _
  | with_reducible exact grows_content? _
  | with_reducible exact grows_ppPlace _
  | with_reducible exact grows_absType _
  | with_reducible exact grows_lookupInd _
  | with_reducible exact grows_recordedNeutral _
  | with_reducible exact grows_setPlace _ _
  | with_reducible exact grows_logEffect _ _
  | with_reducible exact grows_movedPlace _ _
  | with_reducible exact grows_accessPath _ _
  | with_reducible exact grows_accessInside _ _ _
  | with_reducible exact grows_endBorrow _ _
  | with_reducible exact grows_etaInPlace _ _ _ _
  | with_reducible exact grows_placeTypeQ _ _
  | with_reducible exact grows_substEnv _ _ _ _
  | with_reducible exact grows_generalizeNeutral _ _ _
  | with_reducible exact grows_renormAll _
  | with_reducible exact grows_refine _ _ _
  | with_reducible exact grows_dropAtJoin _ _
  | with_reducible exact grows_restoreKeep _
  | with_reducible exact grows_expectTy _ _ _ _
  | with_reducible exact grows_mkEqM _ _ _ _
  | with_reducible exact grows_evalType _ _
  | with_reducible exact grows_eval _ _ _ _
  | with_reducible exact grows_blockEntry _ _
  | with_reducible exact grows_closeBlock _ _ _ _
  | with_reducible exact grows_demand _
  | with_reducible exact grows_getFlags
  | with_reducible exact grows_setFlags _
  | (with_reducible refine grows_joinDrop _ _ ?_)
  | with_reducible exact grows_wholeReturned _
  | with_reducible exact grows_pushTempAt _ _ _ _
  | with_reducible exact grows_topIdx
  | with_reducible exact grows_popFrame _
  | with_reducible exact grows_popTemp
  | with_reducible exact grows_lendEnv _ _
  | (with_reducible exact GrowsM.modify fun _ => ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩)
  | (with_reducible refine GrowsM.bind ?_ (fun _ => ?_))
  | (with_reducible refine GrowsM.forIn _ _ (fun _ _ => ?_))
  | (with_reducible refine GrowsM.discard ?_)
  | (with_reducible refine GrowsM.map _ ?_)
  | split
  | (dsimp only))

/-- The closure, to the end: every successful run of the term only extends the tables. -/
macro "grows_go" : tactic => `(tactic| repeat (any_goals grows_step))

end Ochr.Meaning.Steps
