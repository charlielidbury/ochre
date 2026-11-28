import Ochr.Meaning.Steps.Machine.CheckIndSpec
import Ochr.Meaning.Steps.Machine.CheckItem
import Ochr.Meaning.Steps.TopConst

/-!
# The top's restriction `SortsG`, PROVED (lead44, 2026-11-28; docs/31 D256 on)

`Top.SortsG` (no data declaration of the program at `Type₁`) was a named hypothesis of `consistency_of_master`, read
true. It is a fact about the checker alone, at every list of items and every fuel: `checkInd` rejects a sort above
`Type₀` ("an inductive type is in Prop or Type") before it writes anything, and only an accepted inductive
declaration adds to the declarations (`checkItem_tables`). So the hypothesis is discharged
(`Top.sortsG_indsOf`). What lifting the restriction would need is the model's, not the checker's: docs/31 D256.
-/

namespace Ochr.Meaning.Steps.Machine
open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

set_option maxHeartbeats 8000000 in
/-- **An accepted inductive declaration is in `Prop` or `Type₀`**: `checkInd`'s third test. -/
theorem runs_checkInd_sort {d : IndDecl} {st st' : MState} {b : Nat} (h : Runs (checkInd d) st b () st') :
    d.sort ≤ 1 := by
  unfold checkInd at h
  dsimp (config := { proj := false }) only at h
  obtain ⟨c, s₁, b₁, hd, h⟩ := Runs.bind_inv h
  obtain ⟨_, hs₁⟩ := runs_declared_inv hd
  subst hs₁
  clear hd
  cases c
  case true =>
    rw [if_pos rfl] at h
    obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact (runs_err_false he).elim
  rw [if_neg Bool.false_ne_true] at h
  obtain ⟨_, s₂, b₂, _, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  by_cases hsort : d.sort > 1
  · rw [if_pos hsort] at h
    obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact (runs_err_false he).elim
  omega

/-- Along the items, every declaration added is in `Prop` or `Type₀`. -/
theorem sigAfterFrom_sorts (cfg : Config) (fuel : Nat) :
    ∀ (items : List Item) (start : List GDef × List IndDecl), (∀ d ∈ start.2, d.sort ≠ 2) →
      ∀ d ∈ (sigAfterFrom cfg fuel start items).2, d.sort ≠ 2
  | [], _, h => h
  | it :: items, start, h => by
    unfold sigAfterFrom
    rw [List.foldl_cons]
    apply sigAfterFrom_sorts cfg fuel items
    split
    · rename_i st' hst
      obtain ⟨hI, hD⟩ := checkItem_tables it _ st' fuel hst
      cases it with
      | ind d =>
        rw [(hI d rfl).1]
        intro e he
        rcases List.mem_append.1 he with he | he
        · exact h e he
        · rw [List.mem_singleton] at he
          subst he
          have hr := runs_of_runMachine_fst hst
          unfold checkItem at hr
          obtain ⟨_, s₁, b₁, _, h₂⟩ := Runs.bind_inv hr
          have := runs_checkInd_sort h₂
          show d.sort ≠ 2
          omega
      | defn d => rw [(hD d rfl).1]; exact h
    · exact h

end Ochr.Meaning.Steps.Machine

namespace Ochr.Meaning.Steps.Form.Top

/-- **`SortsG` at every program** (PROVED, standard axioms): no list of items, at any fuel, has a data declaration at
`Type₁` among its accepted declarations. -/
theorem sortsG_indsOf (cfg : Config) (fuel : Nat) (items : List Item) : SortsG (indsOf cfg fuel items) :=
  Steps.Machine.sigAfterFrom_sorts cfg fuel items ([], []) (fun _ h => by cases h)

end Ochr.Meaning.Steps.Form.Top
