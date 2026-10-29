import Ochr.Machine
/-!
# Probe: mechanising (P) against the real machine, layer 2 (a measurement)

Run lemmas for the checker's monad `M` (five layers: `StateT MState`, `ExceptT Fail`,
`ExceptT Exhausted`, `StateT Fuel`, `StateM (Array LogEntry)`): `step` takes every layer apart,
and `step_bind` etc. let `simp only` move through a `do` block without unfolding the stack
(plain `simp` times out at `whnf` on the first `eval`). `eval_zero` is left `sorry` on purpose:
it is the measurement. Unfolding the real `eval` on the term `0` with these lemmas works, but
the proof state is about 50,000 characters, almost all of it bookkeeping (the erasure pre-pass,
`curDecl`/`tailDecl`/`headEval`, the flags, `typing`, `erasedDepth`, the editor's `locs`), each
of which needs its own invariant before a single case of (P) closes. See `notes/stability.md` §7.
-/

namespace Ochr.PProbe
open Ochr

/-- One run of `M`, every layer taken apart. -/
abbrev Res (α : Type) := (Except Exhausted (Except Fail (α × MState)) × Fuel) × Array LogEntry

@[inline] def step {α : Type} (x : M α) (Ω : MState) (fl : Fuel) (lg : Array LogEntry) : Res α :=
  ((((x.run Ω).run).run).run fl).run lg

/-- Continue a run with `f`. -/
@[inline] def cont {α β : Type} (r : Res α) (f : α → MState → Fuel → Array LogEntry → Res β) : Res β :=
  match r with
  | ((.ok (.ok (a, Ω)), fl), lg) => f a Ω fl lg
  | ((.ok (.error e), fl), lg) => ((.ok (.error e), fl), lg)
  | ((.error e, fl), lg) => ((.error e, fl), lg)

theorem step_pure {α} (a : α) Ω fl lg : step (pure a : M α) Ω fl lg = ((.ok (.ok (a, Ω)), fl), lg) := rfl
theorem step_bind {α β} (x : M α) (f : α → M β) Ω fl lg :
    step (x >>= f) Ω fl lg = cont (step x Ω fl lg) fun a Ω' fl' lg' => step (f a) Ω' fl' lg' := by
  simp only [step, cont, bind, StateT.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.run, ExceptT.run]
  rcases x Ω fl lg with ⟨⟨r, fl'⟩, lg'⟩; rcases r with e | (e | ⟨a, Ω'⟩) <;> rfl
theorem step_get Ω fl lg : step (get : M MState) Ω fl lg = ((.ok (.ok (Ω, Ω)), fl), lg) := rfl
theorem step_set (s : MState) Ω fl lg : step (set s : M Unit) Ω fl lg = ((.ok (.ok ((), s)), fl), lg) := rfl
theorem step_modify (g : MState → MState) Ω fl lg :
    step (modify g : M Unit) Ω fl lg = ((.ok (.ok ((), g Ω)), fl), lg) := rfl

theorem step_getFuel Ω fl lg : step (getThe Fuel : M Fuel) Ω fl lg = ((.ok (.ok (fl, Ω)), fl), lg) := rfl
theorem step_modifyFuel (g : Fuel → Fuel) Ω fl lg :
    step (modifyThe Fuel g : M Unit) Ω fl lg = ((.ok (.ok ((), Ω)), g fl), lg) := rfl
theorem step_exhausted {α} (m : String) Ω fl lg :
    step (exhausted m : M α) Ω fl lg = ((.error ⟨m⟩, fl), lg) := rfl
theorem step_throwFail {α} (e : Fail) Ω fl lg :
    step (throw e : M α) Ω fl lg = ((.ok (.error e), fl), lg) := rfl
theorem step_onFail {α} (x : M α) (c : M Unit) Ω fl lg :
    step (onFail x c) Ω fl lg =
      match step x Ω fl lg with
      | ((.ok (.error e), fl'), lg') => cont (step c Ω fl' lg') fun _ Ω'' fl'' lg'' => ((.ok (.error e), fl''), lg'')
      | r => r := by
  simp only [step, onFail]
  sorry

set_option maxHeartbeats 4000000 in
/-- The real `eval` on `0`: it returns `0` and leaves the environment as it was. -/
theorem eval_zero (f : Nat) (Ω : MState) (fl : Fuel) (lg) (hl : Ω.locs.table.isEmpty = true) (hf : 0 < fl.left) :
    ∃ Ω' fl' lg', step (eval (f+3) false .zero) Ω fl lg = ((.ok (.ok ((.zero, none), Ω')), fl'), lg') ∧ Ω'.env = Ω.env := by
  simp only [eval, located, step_bind, step_get, cont, hl, ite_true]
  unfold noteValue
  rw [step_bind]
  unfold evalAt
  simp only [step_bind, step_get, step_modify, step_pure, cont]
  sorry

end Ochr.PProbe
