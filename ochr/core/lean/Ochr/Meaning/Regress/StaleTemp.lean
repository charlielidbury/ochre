import Ochr.Meaning.Regress.CE4_flipped
import Ochr.Meaning.Steps.Sim
import Ochr.Machine

/-!
# The checker's state is not `Below` the reference state after a borrow was held (built)

docs/31, D20 item 1 (second lead, 2026-11-13). Every step statement concludes
`Below (MState.mean … st') s'.toMean`: the checker's state position by position below the
reference run's. `Below` reads EVERY position, temporaries included, and the two states do not
have the same temporaries:

* the reference run parks a borrow in a temporary of the top frame from its creation until it
  is bound (`borrowPlace`, D14), and when the borrow is bound the temporary stays, reading `⊥`
  (`SState.takeLabel`);
* the checker carries a value in flight in its monad, so its frame has no temporary there, and a
  position outside the environment means `err` (`Env.mean`).

`err ⊑ ⊥` is false (`⊥` is below everything, not above), so after any `let r = &y` the checker's
state is not `Below` the reference's. Checked on the accepted program `let r = &y; ()` from the
state where `y = Z` is bound:

* `checkerNoTemps`: the checker accepts it (typed) and its final frame has no temporary
  (a `#guard`: evaluated at build on `Machine.eval`, not kernel-checked);
* `let_borrow_run`: the reference run ends in `aF`, whose temporary `0` reads `⊥` (`aF_temp`);
* `not_below_stale_temp`: so no state with no temporary there is `Below` it.

Consequence: `letIn_step_stmt`, `eval_step_stmt` and `evalCore_step_stmt` are false as stated
(their `Below` conjunct), on the simplest program that holds a borrow. The relation the
statements need compares bindings position by position and borrows in flight by LABEL
(`Steps/Sim.lean`, `Sim`), which does hold here (`sim_stale_temp`).
-/

namespace Ochr.Meaning.Regress.StaleTemp
open Ochr Ochr.Meaning Ochr.Meaning.Regress.CE4flip

/-- `let r = &y; ()`, in a scope where `y` is variable `0`. -/
def tLet : Term := .letIn ⟨"r"⟩ (.borrow (.var 0)) .tt

/-- The checker's state with `y : Nat ↦ Z` bound and no temporary. -/
def stY : MState := { env := #[{ binds := #[{ hint := ⟨"y"⟩, ty := some .tNat, val := .zero }] }] }

/-- The checker accepts `let r = &y; ()` in typed mode, and leaves one binding and no temporary.
Evaluated at build (`#guard`), not proved: the kernel's `decide` on `Machine.eval` times out. -/
def checkerNoTemps : Bool :=
  match (runMachine (Ochr.eval 100 true tLet none) stY 1000).1 with
  | .ok _ st' => st'.env.size == 1 && (st'.env[0]!).binds.size == 1 && (st'.env[0]!).temps.size == 0
  | _ => false
#guard checkerNoTemps

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- `r`'s binding: the borrow's content at `Nat`, labelled `n`. -/
noncomputable def rB (n : Nat) : SBinding :=
  { ty := { TyS.plain (.ty0 Nat) with label := some n }, val := fun _ => .el0 Nat 0,
    decl := K.D.declOf (scopeOf (a2 K n)) (.borrow (.var 0)) }

theorem take_a2 (n : Nat) : (a2 K n).takeLabel n =
    { ((a2 K n).setAt (.temp 0 0) fun _ => .moved) with
      shape := fun p => if p = .temp 0 0 then none else (a2 K n).shape p } := by
  unfold SState.takeLabel; rw [holder_a2]

/-- After `r` is bound: the temporary reads `⊥`, and `r` holds the borrow. -/
noncomputable def a3 (n : Nat) : SState := pushBindShaped (a2 K n) (rB K n)

/-- The reference's state after the `let`: `r` dropped, its borrow ended. -/
noncomputable def aF (n : Nat) : SState := ((a3 K n).endAt n (.bind 0 1)).dropLast

theorem positions_a3 (n : Nat) : (a3 K n).positions = [.bind 0 0, .bind 0 1, .temp 0 0] := by
  unfold a3 pushBindShaped
  simp only [rB, take_a2]
  rw [SState.positions_eq]
  rfl

theorem holder_a3 (n : Nat) : (a3 K n).holderOf n = some (.bind 0 1) := by
  unfold SState.holderOf
  rw [positions_a3]
  unfold a3 pushBindShaped
  simp only [rB, take_a2]
  simp [SState.pushBind, SState.setAt, SState.topIdx, a2]

theorem held_a3 (n : Nat) :
    (match (a3 K n).env.getLast? with
      | some fr => (a3 K n).shape (.bind (a3 K n).topIdx (fr.binds.length - 1))
      | none => none) = some n := by
  unfold a3 pushBindShaped
  simp only [rB, take_a2]
  simp [SState.pushBind, SState.setAt, SState.topIdx, a2]

/-- The reference run of `let r = &y; ()` from `y = Z` ends in `aF`. -/
theorem let_borrow_run (hfl : NoStmt K) (n : Nat) (hint : TyS) :
    run K ρ φ hint tLet (a1 K n) = some ((.el0 Unit (), .plain (.ty0 Unit)), aF K n) := by
  rw [tLet, run_letIn ρ φ K hfl, run_borrow ρ φ K hfl, borrow_a1]
  show ((run K ρ φ hint .tt (a3 K n)).bind fun y => some (y.1, (match (match y.2.env.getLast? with
            | some fr => y.2.shape (.bind y.2.topIdx (fr.binds.length - 1))
            | none => none) with
          | some l => y.2.endLabel l | none => y.2).dropLast)) = _
  have htt : run K ρ φ hint .tt (a3 K n) = some ((.el0 Unit (), .plain (.ty0 Unit)), a3 K n) := rfl
  rw [htt]
  show some ((Sem.el0 Unit (), TyS.plain (.ty0 Unit)), (match (match (a3 K n).env.getLast? with
            | some fr => (a3 K n).shape (.bind (a3 K n).topIdx (fr.binds.length - 1))
            | none => none) with
          | some l => (a3 K n).endLabel l | none => a3 K n).dropLast) = _
  rw [held_a3]
  show some ((Sem.el0 Unit (), TyS.plain (.ty0 Unit)), ((a3 K n).endLabel n).dropLast) = _
  rw [SState.endLabel_eq (holder_a3 K n)]
  rfl

/-- The reference's final state keeps the temporary the borrow was parked in, reading `⊥`. -/
theorem aF_temp (n : Nat) (ψ : Future) : (aF K n).valAt (.temp 0 0) ψ = .moved := by
  have h1 : (aF K n).valAt (.temp 0 0) = ((a3 K n).endAt n (.bind 0 1)).valAt (.temp 0 0) := by
    unfold aF
    apply SState.valAt_dropLast
    unfold SState.dropped
    cases ((a3 K n).endAt n (.bind 0 1)).env.getLast? <;> simp
  rw [h1, SState.endAt_valAt _ _ _ _ (by rw [positions_a3]; simp)]
  simp only [show (Pos.temp 0 0 = Pos.bind 0 1) = False from by simp, if_false]
  unfold a3 pushBindShaped
  simp only [rB, take_a2]
  rfl

end

/-- No state whose frame `0` has no temporary `0` is `Below` a reference state whose temporary
`0` reads `⊥`: a missing position means `err`, and `err ⊑ ⊥` is false. -/
theorem not_below_stale_temp (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment)
    (st : MState) (s : SState) (hst : st.env[0]?.bind (·.temps[0]?) = none)
    (hs : ∀ ψ, s.valAt (.temp 0 0) ψ = .moved) :
    ¬ Below (MState.mean dm C Γ ρ st) s.toMean := by
  intro h
  obtain ⟨ψ, hv, -⟩ := h (fun _ => .err)
  have := hv (.temp 0 0)
  simp only [MState.mean, Env.mean, hst, SState.toMean, hs] at this
  cases this

section
variable (K : RunCtx) (ρ : Assignment)

theorem dropped_aF (n : Nat) : ((a3 K n).endAt n (.bind 0 1)).dropped = some (.bind 0 1) := by
  unfold SState.dropped SState.endAt a3 pushBindShaped
  simp only [rB, take_a2]
  simp [SState.pushBind, SState.setAt, SState.topIdx, SState.mapVals, a2]

theorem a3_y (n : Nat) (ψ : Future) : (a3 K n).valAt (.bind 0 0) ψ = ψ n := by
  unfold a3 pushBindShaped; simp only [rB, take_a2]; rfl

theorem a3_r (n : Nat) (ψ : Future) : (a3 K n).valAt (.bind 0 1) ψ = .el0 Nat 0 := by
  unfold a3 pushBindShaped; simp only [rB, take_a2]; rfl

theorem aF_y (n : Nat) (ψ : Future) : (aF K n).valAt (.bind 0 0) ψ = .el0 Nat 0 := by
  have h1 : (aF K n).valAt (.bind 0 0) = ((a3 K n).endAt n (.bind 0 1)).valAt (.bind 0 0) := by
    unfold aF
    apply SState.valAt_dropLast
    rw [dropped_aF]; simp
  rw [h1, SState.endAt_valAt _ _ _ _ (by rw [positions_a3]; simp)]
  simp only [show (Pos.bind 0 0 = Pos.bind 0 1) = False from by simp, if_false]
  rw [a3_y, a3_r]
  simp [Future.upd]

theorem aF_other (n : Nat) (f i : Nat) (h : (f, i) ≠ (0, 0)) : (aF K n).valAt (.bind f i) = fun _ => .err := by
  apply SState.valAt_of_not_mem
  intro hm
  obtain ⟨hm', hd⟩ := SState.mem_positions_dropLast hm
  rw [SState.endAt_positions, positions_a3] at hm'
  rw [dropped_aF] at hd
  simp only [List.mem_cons, Pos.bind.injEq, reduceCtorEq, List.not_mem_nil, or_false] at hm'
  rcases hm' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h rfl
  · exact hd rfl

/-- **The relation the statements need holds where `Below` fails**: the checker's state after
`let r = &y; ()` (one binding `y ↦ Z`, no temporary) is simulated by the reference's final state
`aF`, whose stale temporary `Sim` does not read. -/
theorem sim_stale_temp (C : CodeMeaning) (n : Nat) : Steps.Sim (MState.mean K.dm C K.Γ ρ stY) (aF K n) := by
  intro φ'
  refine ⟨φ', fun p hp => ?_, fun p l _ hl => ?_, fun f i l hl => ?_⟩
  · cases p with
    | temp f i => exact absurd trivial hp
    | bind f i =>
      by_cases h : (f, i) = (0, 0)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        rw [aF_y]
        exact Sem.le_refl _
      · rw [aF_other K n f i h]
        have : (MState.mean K.dm C K.Γ ρ stY).val φ' (.bind f i) = .err := by
          simp only [MState.mean, Env.mean, stY]
          rcases f with _ | f
          · rcases i with _ | i
            · exact absurd rfl h
            · rfl
          · rfl
        rw [this]
        exact Sem.le_refl _
  · exfalso
    simp only [MState.mean, Env.shape, stY] at hl
    cases p with
    | bind f i => rcases f with _ | f <;> rcases i with _ | i <;> cases hl
    | temp f i => rcases f with _ | f <;> cases hl
  · exfalso
    simp only [MState.mean, Env.shape, stY] at hl
    rcases f with _ | f <;> cases hl

end

end Ochr.Meaning.Regress.StaleTemp
