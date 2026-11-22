import Ochr.Meaning.Steps.HintSites
import Ochr.Meaning.Steps.Machine.HintKeep

/-!
# Main's D124 and D122, read off the merged checker: five named facts PROVED (machine9)

The lead lane stated these as facts about the checker, false on the proof line's checker before the merge of main's
D122 and D124 (machine9, `spine-machine10`), true after; their pins in `Steps/HintSites.lean` and
`Steps/MasterGuards.lean` flipped at the merge.

* `HintSites.UntypedLetTailNoHint`, `UntypedSeqTailNoHint`, `UntypedMatchNatArmNoHint`, `UntypedMatchIndArmNoHint`:
  `evalCore` reads `curTail` once, after its `tick`, and at these four forms the hint appears only as
  `if typed || !tail then none else hint` (D124), which is `none` for an untyped run out of tail position. So the two
  runs are the same computation from the state after the read: equal outcomes, at every budget and log.
* `HintSites.ClonePeekPlace`: `clone`'s arm is `let .place p := u | err …` and `peek`'s `unless u matches .place _ do
  err …` (D122); no earlier arm of `evalCore` matches `.prim "clone" [u]` or `.prim "peek" [u]`, and `placeOperand?`
  of a `prim` is `none`.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

theorem rml_get_bind {α : Type} (k : MState → M α) (st : MState) (b : Nat) (L : Array LogEntry) :
    runMachineL (get >>= k) st b L = runMachineL (k st) st b L := rfl

theorem rml_wanted_bind {α : Type} (k : Bool → M α) (st : MState) (b : Nat) (L : Array LogEntry) :
    runMachineL (wanted >>= k) st b L = runMachineL (k st.wantHere) st b L := rfl

theorem runs_wanted_bind' {α : Type} {k : Bool → M α} {st st' : MState} {b : Nat} {y : α} :
    Runs (wanted >>= k) st b y st' ↔ Runs (k st.wantHere) st b y st' := Iff.rfl

/-- Two computations with the same outcome from `st` at every budget and log run alike from `st`. -/
theorem runs_iff_of_rml {α : Type} {x y : M α} {st : MState} (he : ∀ b L, runMachineL x st b L = runMachineL y st b L)
    {b : Nat} {r : α} {st' : MState} : Runs x st b r st' ↔ Runs y st b r st' :=
  ⟨fun ⟨L, l, g, h⟩ => ⟨L, l, g, by rw [← he]; exact h⟩, fun ⟨L, l, g, h⟩ => ⟨L, l, g, by rw [he]; exact h⟩⟩

/-- The common proof: past the `tick`, the read of the tail flag and of `wanted`, the untyped run's hint at the four
forms is `none` out of tail position. -/
macro "untyped_tail_hint" hct:ident b:ident : tactic => `(tactic| (
  unfold Ochr.evalCore
  rw [runMachineL_bind, runMachineL_bind]
  cases $b:ident with
  | zero => rfl
  | succ _ =>
    rw [runMachineL_tick_succ]
    dsimp only
    rw [rml_get_bind, rml_get_bind, rml_wanted_bind, rml_wanted_bind]
    simp only [Term.placeOperand?, $hct:ident, Bool.not_false, Bool.false_or, ↓reduceIte]))

set_option maxHeartbeats 4000000 in
theorem rml_untyped_letIn (n : Nat) (x : Hint) (u w : Term) (hint : Option Value) (st : MState)
    (hct : st.curTail = false) (b : Nat) (L : Array LogEntry) :
    runMachineL (Ochr.evalCore (n + 1) false (.letIn x u w) hint) st b L =
      runMachineL (Ochr.evalCore (n + 1) false (.letIn x u w) none) st b L := by
  untyped_tail_hint hct b

set_option maxHeartbeats 4000000 in
theorem rml_untyped_seq (n : Nat) (u w : Term) (hint : Option Value) (st : MState) (hct : st.curTail = false)
    (b : Nat) (L : Array LogEntry) :
    runMachineL (Ochr.evalCore (n + 1) false (.seq u w) hint) st b L =
      runMachineL (Ochr.evalCore (n + 1) false (.seq u w) none) st b L := by
  untyped_tail_hint hct b

set_option maxHeartbeats 4000000 in
theorem rml_untyped_matchNat (n : Nat) (p : Place) (z s : Term) (hint : Option Value) (st : MState)
    (hct : st.curTail = false) (b : Nat) (L : Array LogEntry) :
    runMachineL (Ochr.evalCore (n + 1) false (.matchNat p z s) hint) st b L =
      runMachineL (Ochr.evalCore (n + 1) false (.matchNat p z s) none) st b L := by
  untyped_tail_hint hct b

set_option maxHeartbeats 4000000 in
theorem rml_untyped_matchInd (n : Nat) (p : Place) (ty : String) (arms : List (Hint × Term)) (hint : Option Value)
    (st : MState) (hct : st.curTail = false) (b : Nat) (L : Array LogEntry) :
    runMachineL (Ochr.evalCore (n + 1) false (.matchInd p ty arms) hint) st b L =
      runMachineL (Ochr.evalCore (n + 1) false (.matchInd p ty arms) none) st b L := by
  untyped_tail_hint hct b

/-- **`UntypedLetTailNoHint`, PROVED** (main's D124 at a `let`'s tail). -/
theorem untypedLetTailNoHint : Form.HintSites.UntypedLetTailNoHint :=
  fun n x u w hint st _ _ _ hct => runs_iff_of_rml (rml_untyped_letIn n x u w hint st hct)

/-- **`UntypedSeqTailNoHint`, PROVED** (main's D124 at a `;`'s tail). -/
theorem untypedSeqTailNoHint : Form.HintSites.UntypedSeqTailNoHint :=
  fun n u w hint st _ _ _ hct => runs_iff_of_rml (rml_untyped_seq n u w hint st hct)

/-- **`UntypedMatchNatArmNoHint`, PROVED** (main's D124 at a match on a number's arms). -/
theorem untypedMatchNatArmNoHint : Form.HintSites.UntypedMatchNatArmNoHint :=
  fun n p z u hint st _ _ _ hct => runs_iff_of_rml (rml_untyped_matchNat n p z u hint st hct)

/-- **`UntypedMatchIndArmNoHint`, PROVED** (main's D124 at a match on a declared inductive's arms). -/
theorem untypedMatchIndArmNoHint : Form.HintSites.UntypedMatchIndArmNoHint :=
  fun n p ty arms hint st _ _ _ hct => runs_iff_of_rml (rml_untyped_matchInd n p ty arms hint st hct)

set_option maxHeartbeats 4000000 in
/-- **`ClonePeekPlace`, PROVED** (main's D122: `clone` and `peek` take a place, typed or untyped). -/
theorem clonePeekPlace : Form.HintSites.ClonePeekPlace := by
  intro n typed f u hint st st' bh r hf h
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  rw [runs_get_bind, runs_wanted_bind'] at h
  rcases hf with rfl | rfl
  · simp only [Term.placeOperand?] at h
    split at h
    · exact ⟨_, rfl⟩
    · exact absurd h (fun h => runs_err_false h)
  · simp only [Term.placeOperand?] at h
    split at h
    · exact ⟨_, rfl⟩
    · exact absurd h (fun h => runs_err_bind_false h)

end Ochr.Meaning.Steps.Machine
