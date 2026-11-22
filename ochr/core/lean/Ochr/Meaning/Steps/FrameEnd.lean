import Ochr.Meaning.Steps.FrameRec

/-!
# [End] against the frame relation: the value-level core, and the cells it needs (lead30; docs/31 D203)

The frame property's group 1 (borrow parameters): when the body ends a borrow, in place the label `σ l` ends (its
holder `x` in the callee's frame), in the closure the label `l` (its holder `x'`). `SState.endLabel` is `semEnd`
lifted: every other position reads the label as the holder's value (`v ↦ fun ψ => v (ψ.upd l (x ψ))`). Two clauses of
`FrameRel` must survive that:
- the top frames (`BindRen`): `bindRen_end`, from `renF σ (ψ.upd (σ l) X) = (renF σ ψ).upd l X` (`σ` injective);
- the caller's frames read at the cells' values (`lowerVal`, `cellFuture`): `lowerVal_end`. In place a caller's
  lender of a parameter label `k = σ l` now reads the holder's value; in the closure the CELL of `l` does. They agree
  because `cellFuture` overwrites every parameter label with its cell's value, so the base future's value at `k` does
  not matter, PROVIDED the closure's frame 0 has a cell for every parameter label (`ks.length ≤ cells.length`). A
  callee label `σ l ∉ ks` is at or above the counter at the call, which the caller's frames do not read (`FrameStart`).

**Finding (D203).** `FrameRel` does not say that the closure's frame 0 has `ks.length` bindings (`cellsOf` truncates).
Without it the end of a parameter label breaks `lowerVal`: `lowerVal_end_needs_cells` (kernel-checked, at the level of
values): one parameter label `k`, no cell, a caller's lender reading `ψ k`; after the end the lender reads the holder's
value (`1`), while `cellFuture` with no cell leaves `ψ k`. So `RunFrameS` (and `RunFrame`) need the hypothesis that the
closure's frame 0 has a binding for every parameter label; a run never changes frame 0's length, and at a call
`fixBodyAt` pushes one cell per borrow parameter (`fixStep`).
-/

namespace Ochr.Meaning.Steps.Form.FrameEnd

open Ochr Ochr.Meaning

/-- The renaming commutes with fixing a label: the in-place future fixed at `σ l` is the closure's fixed at `l`. -/
theorem renF_upd {σ : Nat → Nat} (hinj : ∀ a b, σ a = σ b → a = b) (ψ : Future) (l : Nat) (X : Sem) :
    renF σ (ψ.upd (σ l) X) = (renF σ ψ).upd l X := by
  funext m
  simp only [renF, Future.upd]
  by_cases h : m = l
  · subst h; simp
  · rw [if_neg (fun e => h (hinj _ _ e)), if_neg h]

/-- **The top frames after an end** (`BindRen`'s value clause): a value related through `σ`, read with the label fixed
to its holder's value, on each side. -/
theorem bindRen_end {σ : Nat → Nat} (hinj : ∀ a b, σ a = σ b → a = b) {v v' x x' : SVal} {l : Nat}
    (hv : ∀ ψ, v ψ = v' (renF σ ψ)) (hx : ∀ ψ, x ψ = x' (renF σ ψ)) (ψ : Future) :
    v (ψ.upd (σ l) (x ψ)) = v' ((renF σ ψ).upd l (x' (renF σ ψ))) := by
  rw [hv, renF_upd hinj, hx]

/-- `updList` at a list whose keys include `m`, or from two bases agreeing at `m`, gives the same value at `m`. -/
theorem updList_at (ψ ψ' : Future) (xs : List (Nat × Sem)) (m : Nat) (h : m ∈ xs.map (·.1) ∨ ψ m = ψ' m) :
    ψ.updList xs m = ψ'.updList xs m := by
  induction xs generalizing ψ ψ' with
  | nil =>
    rcases h with h | h
    · cases h
    · exact h
  | cons y ys ih =>
    obtain ⟨k, e⟩ := y
    apply ih
    by_cases hk : m = k
    · subst hk; right; simp [Future.upd]
    · rcases h with h | h
      · simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h hk
        · exact .inl h
      · right; simp only [Future.upd, if_neg hk]; exact h

theorem zip_keys {α β : Type _} (ks : List α) (vs : List β) (h : ks.length ≤ vs.length) :
    (ks.zip vs).map (·.1) = ks := by
  induction ks generalizing vs with
  | nil => rfl
  | cons k ks ih =>
    match vs, h with
    | v :: vs, h => simp only [List.zip_cons_cons, List.map_cons, ih vs (by simpa using h)]

/-- **`cellFuture` after an end** agrees, below the counter at the call, with `cellFuture` of the cells after the
closure's end: each cell `c` becomes `fun ψ' => c (ψ'.upd l (x' ψ'))`, the closure's `semEnd`. Needs a cell for every
parameter label, and the ended label a parameter's or one at or above the counter. -/
theorem cellFuture_end {σ : Nat → Nat} (hinj : ∀ a b, σ a = σ b → a = b) (ks : List Nat) (cells : List SVal)
    (hlen : ks.length ≤ cells.length) (n : Nat) {l : Nat} (hl : σ l ∈ ks ∨ n ≤ σ l) (x' : SVal) (ψ : Future)
    (m : Nat) (hm : m < n) :
    cellFuture σ ks cells (ψ.upd (σ l) (x' (renF σ ψ))) m =
      cellFuture σ ks (cells.map fun c ψ' => c (ψ'.upd l (x' ψ'))) ψ m := by
  unfold cellFuture
  rw [renF_upd hinj, List.map_map]
  apply updList_at
  by_cases hm' : m = σ l
  · subst hm'
    rcases hl with hl | hl
    · left; rw [zip_keys _ _ (by simpa using hlen)]; exact hl
    · omega
  · right; simp only [Future.upd, if_neg hm']

/-- **The caller's frames after an end** (`lowerVal`): in place the caller's position reads the label fixed to the
holder's value; it is what the caller's frames at the call read at the cells after the closure's end. -/
theorem lowerVal_end {σ : Nat → Nat} (hinj : ∀ a b, σ a = σ b → a = b) {s₀ : SState} {ks : List Nat}
    (hs₀ : FrameStart s₀ ks) (cells : List SVal) (hlen : ks.length ≤ cells.length) {l : Nat}
    (hl : σ l ∈ ks ∨ s₀.nextLoan ≤ σ l) {x x' v : SVal} (hx : ∀ ψ, x ψ = x' (renF σ ψ)) {p : Pos}
    (hp : p.frameOf < s₀.topIdx) (hv : ∀ ψ, v ψ = s₀.valAt p (cellFuture σ ks cells ψ)) (ψ : Future) :
    v (ψ.upd (σ l) (x ψ)) = s₀.valAt p (cellFuture σ ks (cells.map fun c ψ' => c (ψ'.upd l (x' ψ'))) ψ) := by
  rw [hv, hx]
  exact hs₀.reads p hp _ _ fun m hm => cellFuture_end hinj ks cells hlen s₀.nextLoan hl x' ψ m hm

/-- **Without a cell for the parameter label, `lowerVal` fails after its end** (the finding, at the level of values):
one parameter label `k` (the closure's `0`, `σ 0 = k`), no cell, a caller's position reading `ψ k`, a holder whose value
is the number `1`. After the end in place the caller's position reads `1` at every future; `cellFuture` with no cell
reads `ψ k`, which is not `1` at every future. -/
theorem lowerVal_end_needs_cells (k : Nat) :
    ¬ ∀ ψ : Future, (fun ψ' : Future => ψ' k) (ψ.upd k ((fun _ => Sem.el0 Nat 1 : SVal) ψ)) =
      (fun ψ' : Future => ψ' k) (cellFuture (fun _ => k) [k] ([] : List SVal) ψ) := by
  intro h
  have := h (fun _ => Sem.el0 Nat 0)
  simp [Future.upd, cellFuture, Future.updList] at this

end Ochr.Meaning.Steps.Form.FrameEnd
