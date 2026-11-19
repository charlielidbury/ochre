import Ochr.Meaning.SState

/-!
# A reachable meaning whose dependence on one label is conditional on another (built)

docs/31 D27 (fourth lead, 2026-11-19). The repair of D25 chosen first (candidate 1) adds to `Rel`
that the reference state is the reading of a `Good` checker-form state, keeps the comparison by
equality after the early ends, and rests on a lemma: "in a state satisfying the invariant, whether
a position depends on a label does not depend on the other labels' contents". That lemma is false,
and the tie is not enough.

A stuck call of an unknown function `σ_f : Π(x : &Nat, y : &Pair(Nat, Nat)). &Pair(Nat, Nat)`
returns a borrow `k`; each lent place holds a fill with the hole `k`, meaning its component of the
callee's backward function at `k`'s final content. When `k`'s holder holds `(loan_j, loan_m)`
(two reborrows of its fields) and `k` ends, the fill of `x` means `(back (ψ j, ψ m)).1`. An
assignment gives `σ_f` any member of its type, so any backward function whose joint result is
injective (`back_injective`): here `back (a, b) = (if a = 0 then b else c, (a, if a = 0 then c else b))`.
So `x`'s meaning depends on `m` exactly when `j` holds `0` (`fx_dep_m`, `fx_indep_m`), at typed
futures: the dependence of one label is conditional on another's content, at a `Good` state.

Against the relation: let the checker have ended `j` early (`E = [j]`, its holder holding `S(n)`)
and hold at `x` the constant `c`. After the early end the two agree (`fx_after_end`), and the
preimage is `Good`; yet the reference's [Access] of `x` ends `m` (it depends on `m` at a future
where `j` is `0`) and the checker's ends nothing (a constant holds no loan). So a step stated
from every such state is false. At a REACHABLE state the checker's `x` holds the fill with
`(S(n), loan_m)` substituted, so its access ends `m` too: what pins the reference is the checker's
loans, which `Rel.early`'s `Wit` now asks for (`Steps/Statements.lean`).
-/

namespace Ochr.Meaning.Regress.CondDep
open Ochr Ochr.Meaning

/-- A backward function an unknown callee may have: the final contents of the two lent places
from the final content `(a, b)` of the returned borrow. -/
def back (c : Nat) (ab : Nat × Nat) : Nat × (Nat × Nat) :=
  (if ab.1 = 0 then ab.2 else c, (ab.1, if ab.1 = 0 then c else ab.2))

/-- It is injective, as a member's backward function must be. -/
theorem back_injective (c : Nat) : Function.Injective (back c) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [back, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  subst h2
  by_cases ha : a = 0
  · simp only [ha, if_true] at h1
    rw [ha, h1]
  · simp only [ha, if_false] at h3
    rw [h3]

/-- The fill of `x` after `k` ended with `(loan_j, loan_m)`, as a meaning: `(back (ψ j, ψ m)).1`
on numbers. -/
noncomputable def fx (j m c : Nat) : SVal := fun ψ =>
  open Classical in if ψ j = .el0 Nat 0 then ψ m else .el0 Nat c

/-- It depends on `m`, at a typed future (both labels hold numbers). -/
theorem fx_dep_m (j m c : Nat) (hjm : j ≠ m) (hc : c ≠ 1) :
    ∃ (ψ : Future) (x : Sem), fx j m c ψ ≠ fx j m c (ψ.upd m x) := by
  refine ⟨fun l => if l = j then .el0 Nat 0 else .el0 Nat 1, .el0 Nat c, ?_⟩
  unfold fx
  have h1 : (fun l => if l = j then Sem.el0 Nat 0 else .el0 Nat 1) j = .el0 Nat 0 := by simp
  have h2 : (Future.upd (fun l => if l = j then Sem.el0 Nat 0 else .el0 Nat 1) m (.el0 Nat c)) j = .el0 Nat 0 := by
    rw [Future.upd_other _ _ hjm]; simp
  rw [if_pos h1, if_pos h2, Future.upd_same]
  have hm : (fun l => if l = j then Sem.el0 Nat 0 else .el0 Nat 1) m = .el0 Nat 1 := by
    simp [Ne.symm hjm]
  rw [hm]
  intro h
  exact hc (by injection h with _ h; exact h.symm)

/-- With `j` fixed to `S(n)`, as ending it early fixes it, it depends on nothing. -/
theorem fx_indep_m (j m c n : Nat) (hjm : j ≠ m) (ψ : Future) (x : Sem) :
    fx j m c ((ψ.upd j (.el0 Nat (n + 1))).upd m x) = fx j m c (ψ.upd j (.el0 Nat (n + 1))) := by
  unfold fx
  rw [Future.upd_other _ _ hjm, Future.upd_same]
  have : ¬ (Sem.el0 Nat (n + 1) = Sem.el0 Nat 0) := by
    intro h; injection h with _ h; exact Nat.succ_ne_zero n h
  rw [if_neg this, if_neg this]

/-- After the early end of `j` (fixed to `S(n)`), the fill means the constant `c` the checker's
state may hold at `x`: the comparison by equality after the ends cannot tell them apart. -/
theorem fx_after_end (j m c n : Nat) (ψ : Future) :
    fx j m c (ψ.upd j (.el0 Nat (n + 1))) = .el0 Nat c := by
  unfold fx
  rw [Future.upd_same]
  have : ¬ (Sem.el0 Nat (n + 1) = Sem.el0 Nat 0) := by
    intro h; injection h with _ h; exact Nat.succ_ne_zero n h
  rw [if_neg this]

end Ochr.Meaning.Regress.CondDep
