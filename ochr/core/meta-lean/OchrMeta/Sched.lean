import OchrMeta.WF
import OchrMeta.Interp

/-! # T1(b), schedule independence: the on-the-nose "end early" statement is FALSE

The proposed core commutation

```
theorem exec_end_early (P : Prog) : ∀ n s s' t ℓ s₁ s₂ v₁ v₂,
    WF s → s.env.holds ℓ = true → endBorrow ℓ s = some s' →
    exec P n s' t = .ok s₁ v₁ → exec P n s t = .ok s₂ v₂ →
    v₁ = v₂ ∧ (s₁ = s₂ ∨ endBorrow ℓ s₂ = some s₁)
```

fails: the relation `R e l := e = l ∨ endBorrow ℓ l = some e` is not preserved by [Assign] to the
*holder* of `ℓ` when `ℓ`'s content contains a live reborrow `loan_m`.

* Lazy side: the holder `x ↦ borrow_ℓ (loan_m, 0)` is overwritten.  [Assign]'s access is deep, so
  it first ends the reborrow `m` (inside the old content), then drops `borrow_ℓ`, ending `ℓ`.
* Eager side: `x ↦ ⊥` (ℓ already ended), so the assignment overwrites `⊥`; nothing is ended, and
  `m` stays live, its loan now sitting in the owner `a` of `ℓ`.

Both runs succeed with value `()`, but the lazy final state is *ahead* of the eager one by the end
of `m` (`endBorrow m s₁ = some s₂`), so neither disjunct holds.  The direction of the lag flips:
after the run the eager state is the one with a borrow still to end.

What survives (checked below on this instance, and fuzzed in `SchedFuzz.lean`: about 2.3M
eager/lazy pairs, no failure): the values agree and the *resolved* states agree
(`endAll s₁ = endAll s₂`); the final states are *joinable* by ends of held borrows.  With several
early ends the lag can be two-sided (`m_two_sided`), so the invariant a proof of T1(b) needs is
joinability (a common descendant under ends), not "one is the other with ℓ ended".

The counterexample state is reachable: `let a = (0,0); let x = &a; let y = &(*x).1` (here run as
assignments into a pre-bound frame, `s0_reachable`) and it is well-formed (`wf_s0`). -/

namespace OchrMeta.Sched
open OchrMeta

def a : Var := .nm "a"
def x : Var := .nm "x"
def y : Var := .nm "y"

/-- Owner `a ↦ loan_0`; holder `x ↦ borrow_0 (loan_1, 0)`; reborrow `y ↦ borrow_1 0` of `(*x).1`. -/
def s0 : St := ⟨[[(y, .borrow 1 .zero), (x, .borrow 0 (.pair (.loan 1) .zero)), (a, .loan 0)]], 2⟩

/-- `s0` with borrow `0` ended early: `x ↦ ⊥`, `a ↦ (loan_1, 0)`. -/
def s0' : St := ⟨[[(y, .borrow 1 .zero), (x, .moved), (a, .pair (.loan 1) .zero)]], 2⟩

/-- `x := 0`: overwrite the holder of borrow `0`. -/
def t : Term := .assign (.var x) .zero

/-- Eager final state: the reborrow `1` is still live. -/
def sEager : St := ⟨[[(y, .borrow 1 .zero), (x, .zero), (a, .pair (.loan 1) .zero)]], 2⟩

/-- Lazy final state: the deep access ended `1`, the drop ended `0`. -/
def sLazy : St := ⟨[[(y, .moved), (x, .zero), (a, .pair .zero .zero)]], 2⟩

/-- A reachable origin for `s0`: `x := &a; y := &(*x).1` from `a ↦ (0,0)`. -/
def init : St := ⟨[[(y, .unit), (x, .unit), (a, .pair .zero .zero)]], 0⟩
def pre : Term :=
  .seq (.assign (.var x) (.borrow (.var a))) (.assign (.var y) (.borrow (.fst (.deref (.var x)))))

theorem s0_reachable : exec [] 3 init pre = .ok s0 .unit := by decide +kernel

theorem wf_s0 : WF s0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    simp [s0, Env.names, Val.names] at hl
    simp [s0]; omega
  · intro F hF b hb
    simp [s0] at hF; subst hF
    simp at hb
    rcases hb with rfl | rfl | rfl
    · exact Or.inr ⟨1, .zero, rfl, rfl⟩
    · exact Or.inr ⟨0, _, rfl, rfl⟩
    · exact Or.inl rfl
  · simp
  · decide
  · decide
  · decide
  · simp
  · decide
  · intro F hF b hb ⟨i, hi⟩
    simp [s0] at hF; subst hF
    simp at hb
    rcases hb with rfl | rfl | rfl <;> simp [y, x, a] at hi

theorem holds_s0 : s0.env.holds 0 = true := by decide
theorem end_s0 : endBorrow 0 s0 = some s0' := by decide +kernel
theorem eager_run : exec [] 2 s0' t = .ok sEager .unit := by decide +kernel
theorem lazy_run : exec [] 2 s0 t = .ok sLazy .unit := by decide +kernel
/-- The lazy final state no longer holds borrow `0`: the second disjunct fails. -/
theorem lazy_end_none : endBorrow 0 sLazy = none := by decide +kernel
/-- The eager final state is behind: ending the reborrow `1` catches it up. -/
theorem eager_catch_up : endBorrow 1 sEager = some sLazy := by decide +kernel
/-- The resolved outcomes agree (the T1(b) corollary survives on this instance). -/
theorem resolved_agree : endAll sEager = endAll sLazy := by decide +kernel

/-- **The on-the-nose `exec_end_early` is false** (for the empty program; `t` makes no calls, so
the same instance refutes it for every `P`). -/
theorem exec_end_early_false : ¬ ∀ (n : Nat) (s s' : St) (t : Term) (ℓ : Nat) (s₁ s₂ : St) (v₁ v₂ : Val),
    WF s → s.env.holds ℓ = true → endBorrow ℓ s = some s' →
    exec [] n s' t = .ok s₁ v₁ → exec [] n s t = .ok s₂ v₂ →
    v₁ = v₂ ∧ (s₁ = s₂ ∨ endBorrow ℓ s₂ = some s₁) := by
  intro h
  obtain ⟨_, h2⟩ := h 2 s0 s0' t 0 sEager sLazy .unit .unit wf_s0 holds_s0 end_s0 eager_run lazy_run
  rcases h2 with h2 | h2
  · exact absurd h2 (by decide)
  · rw [lazy_end_none] at h2; cases h2

/-! ## Several early ends: the lag can be two-sided

With two early ends (`0`, whose content holds the reborrow `1`, and an unrelated `2`), the same
assignment leaves the lazy side ahead on `1` and the eager side ahead on `2`: neither final state
reaches the other by ends, but both reach a common one.  So the invariant for `ends s s'` must be
joinability by ends (a common descendant), not "one is the other plus some ends". -/

def z : Var := .nm "z"
def b : Var := .nm "b"

def m0 : St := ⟨[[(z, .borrow 2 .zero), (b, .loan 2), (y, .borrow 1 .zero),
  (x, .borrow 0 (.pair (.loan 1) .zero)), (a, .loan 0)]], 3⟩
def m0' : St := ⟨[[(z, .moved), (b, .zero), (y, .borrow 1 .zero), (x, .moved),
  (a, .pair (.loan 1) .zero)]], 3⟩
def mEager : St := ⟨[[(z, .moved), (b, .zero), (y, .borrow 1 .zero), (x, .zero),
  (a, .pair (.loan 1) .zero)]], 3⟩
def mLazy : St := ⟨[[(z, .borrow 2 .zero), (b, .loan 2), (y, .moved), (x, .zero),
  (a, .pair .zero .zero)]], 3⟩
def mJoin : St := ⟨[[(z, .moved), (b, .zero), (y, .moved), (x, .zero), (a, .pair .zero .zero)]], 3⟩

theorem wf_m0 : WF m0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    simp [m0, Env.names, Val.names] at hl
    simp [m0]; omega
  · intro F hF b hb
    simp [m0] at hF; subst hF
    simp at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨2, .zero, rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨1, .zero, rfl, rfl⟩
    · exact Or.inr ⟨0, _, rfl, rfl⟩
    · exact Or.inl rfl
  · simp
  · decide
  · decide
  · decide
  · simp
  · decide
  · intro F hF b hb ⟨i, hi⟩
    simp [m0] at hF; subst hF
    simp at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp [z, b, y, x, a] at hi

theorem m0_ends : (endBorrow 0 m0).bind (endBorrow 2) = some m0' := by decide +kernel
theorem m_eager_run : exec [] 2 m0' t = .ok mEager .unit := by decide +kernel
theorem m_lazy_run : exec [] 2 m0 t = .ok mLazy .unit := by decide +kernel
/-- Each side has a borrow the other has already ended ... -/
theorem m_two_sided : mEager.env.holds 1 = true ∧ mLazy.env.holds 1 = false ∧
    mLazy.env.holds 2 = true ∧ mEager.env.holds 2 = false := by decide
/-- ... and ending it joins them. -/
theorem m_join : endBorrow 1 mEager = some mJoin ∧ endBorrow 2 mLazy = some mJoin := by decide +kernel

end OchrMeta.Sched
