import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.RunLib

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
  at every larger fuel (the decisions are asked at any fuel, `DecAligned`);
- a comparison's private copy leaves no record naming an unknown it made (main's comparison fix),
  and `placeType?`'s private copies likewise (to be swept before `placeType?`'s step is stated);
- (WF1)–(WF16) and `ShapeFacts` are kept by every step: about checker states only, but each step's
  proof reads its own; listed here so that whoever proves (a) can collect the ones whose proof
  is a closure induction of the same shape.
-/

namespace Ochr.Meaning.Steps

open Ochr Ochr.Meaning

/-- **The tables a decision reads only grow** from `st` to `st'`: the globals and the declarations
are kept, the frozen readings of the old unknowns are kept and new ones may follow, and the
counters of unknowns and labels are not lowered. -/
structure TablesGrow (st st' : MState) : Prop where
  globals : st'.globals = st.globals
  inds : st'.inds = st.inds
  size : st.absDecl.size ≤ st'.absDecl.size
  old : ∀ σ, σ < st.absDecl.size → st'.absDecl[σ]? = st.absDecl[σ]?
  nextAbs : st.nextAbs ≤ st'.nextAbs
  nextLoan : st.nextLoan ≤ st'.nextLoan

theorem TablesGrow.refl (st : MState) : TablesGrow st st :=
  ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem TablesGrow.trans {st₁ st₂ st₃ : MState} (h₁ : TablesGrow st₁ st₂) (h₂ : TablesGrow st₂ st₃) :
    TablesGrow st₁ st₃ :=
  ⟨h₂.globals.trans h₁.globals, h₂.inds.trans h₁.inds, Nat.le_trans h₁.size h₂.size,
    fun σ hσ => (h₂.old σ (Nat.lt_of_lt_of_le hσ h₁.size)).trans (h₁.old σ hσ),
    Nat.le_trans h₁.nextAbs h₂.nextAbs, Nat.le_trans h₁.nextLoan h₂.nextLoan⟩

/-- Every successful run of `x` only extends the tables. -/
def GrowsM {α : Type} (x : M α) : Prop := ∀ st b a st', Runs x st b a st' → TablesGrow st st'

theorem GrowsM.bind {α β : Type} {x : M α} {k : α → M β} (hx : GrowsM x) (hk : ∀ a, GrowsM (k a)) :
    GrowsM (x >>= k) := by
  intro st b c st' h
  obtain ⟨L, left, log, h⟩ := h
  rw [runMachineL_bind] at h
  rcases e : runMachineL x st b L with ⟨o, b₁, L₁⟩
  rw [e] at h
  rcases o with ⟨a, st₁⟩ | f | m
  · exact (hx st b a st₁ ⟨L, b₁, L₁, e⟩).trans (hk a st₁ b₁ c st' ⟨L₁, left, log, h⟩)
  · cases h
  · cases h

theorem GrowsM.pure {α : Type} (a : α) : GrowsM (Pure.pure a : M α) := by
  intro st b c st' h
  obtain ⟨L, left, log, h⟩ := h
  simp only [runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at h
  rw [← h.1.2]; exact TablesGrow.refl st

theorem GrowsM.get : GrowsM (MonadState.get : M MState) := by
  intro st b c st' h
  obtain ⟨L, left, log, h⟩ := h
  simp only [runMachineL_get, Prod.mk.injEq, Outcome.ok.injEq] at h
  rw [← h.1.2]; exact TablesGrow.refl st

/-- A write of the state that keeps the tables. -/
theorem GrowsM.modify {g : MState → MState} (hg : ∀ s, TablesGrow s (g s)) : GrowsM (modify g : M Unit) := by
  intro st b c st' h
  obtain ⟨L, left, log, h⟩ := h
  simp only [runMachineL_modify, Prod.mk.injEq, Outcome.ok.injEq] at h
  rw [← h.1.2]; exact hg st

theorem GrowsM.ite {α : Type} {c : Prop} [Decidable c] {x y : M α} (hx : GrowsM x) (hy : GrowsM y) :
    GrowsM (if c then x else y) := by
  split <;> assumption

theorem GrowsM.forIn {α β : Type} (xs : List α) (b : β) {body : α → β → M (ForInStep β)}
    (hb : ∀ a b, GrowsM (body a b)) : GrowsM (forIn xs b body) := by
  induction xs generalizing b with
  | nil => exact GrowsM.pure b
  | cons a as ih =>
    rw [List.forIn_cons]
    exact (hb a b).bind fun r => by cases r with
      | done b' => exact GrowsM.pure b'
      | yield b' => exact ih b'

/-- The tables after a run of `x` only grew. -/
theorem Runs.grows {α : Type} {x : M α} {st st' : MState} {b : Nat} {a : α} (hx : GrowsM x)
    (h : Runs x st b a st') : TablesGrow st st' :=
  hx st b a st' h

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

theorem GrowsM.err {α : Type} (m : String) : GrowsM (Ochr.err m : M α) := by
  intro st b c st' h
  obtain ⟨L, left, log, h⟩ := h
  simp [runMachineL_err] at h

theorem GrowsM.exhausted {α : Type} (m : String) : GrowsM (Ochr.exhausted m : M α) := by
  intro st b c st' h
  obtain ⟨L, left, log, h⟩ := h
  simp [runMachineL_exhausted] at h

theorem GrowsM.map {α β : Type} (g : α → β) {x : M α} (hx : GrowsM x) : GrowsM (g <$> x) := by
  rw [map_eq_pure_bind]
  exact hx.bind fun a => GrowsM.pure _

theorem GrowsM.discard {α : Type} {x : M α} (hx : GrowsM x) : GrowsM (discard x) := by
  show GrowsM (Functor.mapConst PUnit.unit x)
  rw [LawfulFunctor.map_const]
  exact hx.map _

/-! ## (a) Every machine function's successful run only extends the tables

One statement per machine function an assembly runs, at every fuel (added as the change of form
reaches each assembly). The proof is one closure induction over the machine's mutual block
(`Slice.DecideKeep`'s technique, with `TablesGrow` in place of equality): every write of the
state either keeps the tables (the frames, the flags, the log, the records), or pushes an unknown
(`freshAbs`), or is a private computation's exit, which keeps the names (the module docstring).
Open (the machine lane). -/

theorem grows_content (p : Place) : GrowsM (Ochr.content p) := by sorry
theorem grows_content? (p : Place) : GrowsM (Ochr.content? p) := by sorry
theorem grows_ppPlace (p : Place) : GrowsM (Ochr.ppPlace p) := by sorry
theorem grows_absType (σ : Nat) : GrowsM (Ochr.absType σ) := by sorry
theorem grows_lookupInd (n : String) : GrowsM (Ochr.lookupInd n) := by sorry
theorem grows_recordedNeutral (v : Value) : GrowsM (Ochr.recordedNeutral v) := by sorry
theorem grows_setPlace (p : Place) (v : Value) : GrowsM (Ochr.setPlace p v) := by sorry
theorem grows_logEffect (p : Place) (k : String) : GrowsM (Ochr.logEffect p k) := by sorry
theorem grows_movedPlace (fuel : Nat) (q : Place) : GrowsM (Ochr.movedPlace fuel q) := by sorry
theorem grows_accessPath (fuel : Nat) (p : Place) : GrowsM (Ochr.accessPath fuel p) := by sorry
theorem grows_accessInside (fuel : Nat) (p : Place) (o : Bool) : GrowsM (Ochr.accessInside fuel p o) := by sorry
theorem grows_endBorrow (fuel : Nat) (l : Nat) : GrowsM (Ochr.endBorrow fuel l) := by sorry
theorem grows_etaInPlace (fuel σ : Nat) (d : IndDecl) (ps : List Value) :
    GrowsM (Ochr.etaInPlace fuel σ d ps) := by sorry
theorem grows_placeTypeQ (fuel : Nat) (p : Place) : GrowsM (Ochr.placeType? fuel p) := by sorry
theorem grows_substEnv (fuel : Nat) (x r : Value) (t : Bool) : GrowsM (Ochr.substEnv fuel x r t) := by sorry
theorem grows_generalizeNeutral (fuel : Nat) (p : Place) (n : Value) :
    GrowsM (Ochr.generalizeNeutral fuel p n) := by sorry
theorem grows_renormAll (fuel : Nat) : GrowsM (Ochr.renormAll fuel) := by sorry
theorem grows_refine (fuel σ : Nat) (r : Value) : GrowsM (Ochr.refine fuel σ r) := by sorry
theorem grows_dropAtJoin (fuel : Nat) (q : Place) : GrowsM (Ochr.dropAtJoin fuel q) := by sorry

theorem grows_restoreKeep (saved : MState) : GrowsM (Ochr.restoreKeep saved) := by sorry
theorem grows_expectTy (fuel : Nat) (w : String) (T : Option Value) (A : Value) :
    GrowsM (Ochr.expectTy fuel w T A) := by sorry
theorem grows_mkEqM (fuel : Nat) (A a b : Value) : GrowsM (Ochr.mkEqM fuel A a b) := by sorry
theorem grows_evalType (fuel : Nat) (t : Term) : GrowsM (Ochr.evalType fuel t) := by sorry
theorem grows_eval (fuel : Nat) (typed : Bool) (t : Term) (hint : Option Value) :
    GrowsM (Ochr.eval fuel typed t hint) := by sorry
theorem grows_blockEntry (fuel : Nat) (mt : Term) : GrowsM (Ochr.blockEntry fuel mt) := by sorry
theorem grows_closeBlock (fuel : Nat) (mt : Term) (arms : List BlockArm) (B? : Option Value) :
    GrowsM (Ochr.closeBlock fuel mt arms B?) := by sorry
theorem grows_joinDrop (fuel : Nat) (mt : Term) {run : M (Value × Option Value)} (h : GrowsM run) :
    GrowsM (Ochr.joinDrop fuel mt run) := by sorry
theorem grows_demand (b : Bool) : GrowsM (Ochr.demand b) := by sorry
theorem grows_getFlags : GrowsM Ochr.getFlags := by sorry
theorem grows_setFlags (f : Bool × Bool) : GrowsM (Ochr.setFlags f) := by sorry

theorem grows_wholeReturned (v : Value) : GrowsM (Ochr.wholeReturned v) := by sorry
theorem grows_pushTempAt (f : Nat) (v : Value) : GrowsM (Ochr.pushTempAt f v) := by sorry
theorem grows_topIdx : GrowsM Ochr.topIdx := by sorry
theorem grows_popFrame (fuel : Nat) : GrowsM (Ochr.popFrame fuel) := by sorry
theorem grows_popTemp : GrowsM Ochr.popTemp := by sorry
theorem grows_lendEnv (fuel : Nat) (op : LendOp) : GrowsM (Ochr.lendEnv fuel op) := by sorry
theorem grows_observe (fuel : Nat) (typed : Bool) (t : Term) (A : Value) (W : List Pos)
    (refs : List (Place × Value)) : GrowsM (Ochr.observe fuel typed t A W refs) := by sorry

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
  | with_reducible exact grows_pushTempAt _ _
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
