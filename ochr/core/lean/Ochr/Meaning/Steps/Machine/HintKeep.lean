import Ochr.Meaning.Steps.Slice.DecideKeep

/-!
# D124's `readsHint` and D117's `resolveLoans` read the state only (machine9, at the merge of main 0951e80c..e0b73bce)

`readsHint` decides from syntax and declarations whether a term's run reads the hint it is handed; the
machine computes it before the `if` it guards (a nested `←` is lifted to the statement), so every
inversion through an assignment, a call's argument, a constructor's field, an ascription or a called
body passes it first. Both are value-recursive in the fuel only.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Slice

theorem keep_anyM {α : Type} (xs : List α) {f : α → M Bool} (hf : ∀ a, Keep (f a)) : Keep (xs.anyM f) := by
  induction xs with
  | nil => exact keep_pure false
  | cons a as ih =>
    unfold List.anyM
    exact keep_bind (hf a) (fun b => by cases b <;> first | exact ih | exact keep_pure _)

theorem keep_readsHint : ∀ (fuel : Nat) (tl tr : Bool) (t : Term), Keep (readsHint fuel tl tr t)
  | 0, _, _, _ => by unfold readsHint; keep_go
  | n + 1, tl, tr, t => by
    have ih := keep_readsHint n
    unfold readsHint; keep_go
    all_goals first | exact ih _ _ _ | exact keep_anyM _ (fun _ => ih _ _ _) | skip

theorem keep_resolveLoans : ∀ (fuel : Nat) (v : Value), Keep (resolveLoans fuel v)
  | 0, _ => by unfold resolveLoans; keep_go
  | n + 1, v => by
    have ih := keep_resolveLoans n
    unfold resolveLoans; keep_go
    all_goals first | exact ih _ | skip

end Ochr.Meaning.Steps.Machine
