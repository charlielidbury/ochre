import Ochr.Meaning.Steps.Machine.PlaceInv
import Ochr.Meaning.Steps.MasterPlace

/-!
# `BorrowReadWhole`, proved (machine11)

`Master.BorrowReadWhole` (`Steps/MasterPlace.lean`): a successful read of a place that returns a borrow finds the
borrow's content whole. Since main's D127 `readPlace`'s borrow branch fails on a content that is `⊥` or has a hole
before it moves the borrow; every other branch returns the place's content, which is then not a borrow.

The proof walks the code goal-first with `RetP` ("every value a successful run returns satisfies `P`"): a bind needs
`P` of the continuation only, an `err` (or anything bound after one) returns nothing, a branch is split, and each
`pure` is checked against `P`. It never reads the states.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- Every value a successful run of `x` returns satisfies `P`. -/
@[irreducible] def RetP {α : Type} (P : α → Prop) (x : M α) : Prop :=
  ∀ (st : MState) (b : Nat) (a : α) (st' : MState), Runs x st b a st' → P a

theorem RetP.run {α : Type} {P : α → Prop} {x : M α} (h : RetP P x) {st : MState} {b : Nat} {a : α} {st' : MState}
    (hr : Runs x st b a st') : P a := by
  unfold RetP at h; exact h _ _ _ _ hr

theorem RetP.pure' {α : Type} {P : α → Prop} {a : α} (h : P a) : RetP P (pure a : M α) := by
  unfold RetP; intro st b a' st' hr
  obtain ⟨rfl, -⟩ := runs_pure_inv hr
  exact h

theorem RetP.bind' {α β : Type} {P : β → Prop} {x : M α} {f : α → M β} (h : ∀ a, RetP P (f a)) :
    RetP P (x >>= f) := by
  unfold RetP; intro st b y st' hr
  obtain ⟨a, s₁, b₁, -, h₁⟩ := Runs.bind_inv hr
  exact (h a).run h₁

theorem RetP.err' {α : Type} {P : α → Prop} {m : String} : RetP P (err m : M α) := by
  unfold RetP; intro st b a st' hr
  exact (runs_err_false hr).elim

theorem RetP.err_bind {α β : Type} {P : β → Prop} {m : String} {f : α → M β} : RetP P (err m >>= f) := by
  unfold RetP; intro st b y st' hr
  exact (runs_err_bind_false hr).elim

theorem RetP.ite' {α : Type} {P : α → Prop} {c : Prop} [Decidable c] {x y : M α}
    (h₁ : c → RetP P x) (h₂ : ¬ c → RetP P y) : RetP P (if c then x else y) := by
  by_cases hc : c
  · rw [if_pos hc]; exact h₁ hc
  · rw [if_neg hc]; exact h₂ hc

theorem RetP.dite' {α : Type} {P : α → Prop} {c : Prop} [Decidable c] {x : c → M α} {y : ¬ c → M α}
    (h₁ : ∀ hc, RetP P (x hc)) (h₂ : ∀ hc, RetP P (y hc)) : RetP P (if hc : c then x hc else y hc) := by
  by_cases hc : c
  · rw [dif_pos hc]; exact h₁ hc
  · rw [dif_neg hc]; exact h₂ hc

/-- What a read returns when it returns a borrow. -/
def BorrowWhole (a : Value) : Prop := ∀ l w, a = .borrow l w → w.hasHole = false

set_option maxHeartbeats 4000000 in
theorem retP_readPlace (m : Nat) (p : Place) : RetP BorrowWhole (Ochr.readPlace (m + 1) p) := by
  unfold Ochr.readPlace
  repeat (any_goals first
    | (with_reducible apply RetP.err_bind)
    | (with_reducible apply RetP.err')
    | (with_reducible apply RetP.pure')
    | (apply RetP.ite' <;> intro _)
    | (apply RetP.dite' <;> intro _)
    | (with_reducible apply RetP.bind'; intro _)
    | (dsimp only)
    | (split))
  all_goals (unfold BorrowWhole; intro l' w' e; cases e; simp_all)

/-- **`BorrowReadWhole`, PROVED**: a read that returns a borrow finds its content whole (main's D127). -/
theorem borrowReadWhole : Form.Master.BorrowReadWhole := by
  intro n p st st' bh v h l w hv
  cases n with
  | zero => exact (runs_readPlace_zero h).elim
  | succ m => exact (retP_readPlace m p).run h l w hv

end Ochr.Meaning.Steps.Machine
