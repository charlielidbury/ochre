import Ochr.Meaning.Steps.DataNotSplit
import Ochr.Meaning.Steps.ColumnP

/-!
# The column `Not`: its decisions at the checker's table, and an instance of what it assumes of the data model (lead21, 2026-11-22; docs/31 D147)

`parDecNot`: the decisions `split_simNot` reads (`ParDecNot`, and the function's own binding's reading), at every
table aligned with the checker at `stNot` (`DecTab`), by kernel evaluation of the checker's own decision procedures
there, as `ColumnP.parDecP` for `P`. `dataModelB_triv`: a data model meeting `DataModelB` (it covers every
declaration, and reads no parameter type but the error type, so the records' clauses of `CtxFaithful` speak of no
list but the empty one; `B` has no field and no parameter, so the field and parameter clauses are vacuous). So
`split_simNot`'s bundles have instances: `Pre` at the start and the context hypothesis are not empty.
-/

namespace Ochr.Meaning.Steps.Form.ColumnNot

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-! ## The decisions, at a table aligned with the checker at `stNot` -/

namespace Aux

open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal runs_out)
open Ochr.Meaning.Steps.Form.ColumnC.Aux (flagsRun)
open Ochr.Meaning.Steps.Form.ColumnP.Aux (pdRun jmRun)

/-- `.pi (.ind B [])`, recognised. -/
def isPiB : DeclInfo → Bool
  | .pi (.ind "B" []) => true
  | _ => false

theorem isPiB_eq {d : DeclInfo} (h : isPiB d = true) : d = .pi (.ind "B" []) := by
  unfold isPiB at h; split at h
  · rfl
  · cases h

/-- `.ind B []`, recognised. -/
def isIndB : DeclInfo → Bool
  | .ind "B" [] => true
  | _ => false

theorem isIndB_eq {d : DeclInfo} (h : isIndB d = true) : d = .ind "B" [] := by
  unfold isIndB at h; split at h
  · rfl
  · cases h

theorem ok_flags_body : isOk (flagsRun bodyNot) (scopeState stNot RN) 1000 = true := by decide +kernel
theorem val_flags_body : outVal (flagsRun bodyNot) (scopeState stNot RN) 1000 = (false, false) := by decide +kernel
theorem ok_flags_F : isOk (flagsRun ctorF) (scopeState stNot RN) 1000 = true := by decide +kernel
theorem val_flags_F : outVal (flagsRun ctorF) (scopeState stNot RN) 1000 = (false, false) := by decide +kernel
theorem ok_flags_T : isOk (flagsRun ctorT) (scopeState stNot RN) 1000 = true := by decide +kernel
theorem val_flags_T : outVal (flagsRun ctorT) (scopeState stNot RN) 1000 = (false, false) := by decide +kernel
theorem ok_jm : isOk (jmRun bodyNot) (scopeState stNot RN) 1000 = true := by decide +kernel
theorem val_jm0 : (outVal (jmRun bodyNot) (scopeState stNot RN) 1000).isEmpty = true := by decide +kernel
theorem val_jm : outVal (jmRun bodyNot) (scopeState stNot RN) 1000 = [] := List.isEmpty_iff.mp val_jm0
theorem ok_pd_self : isOk (pdRun (.var 1)) (scopeState stNot RN) 1000 = true := by decide +kernel
theorem val_pd_self : isPiB (outVal (pdRun (.var 1)) (scopeState stNot RN) 1000) = true := by decide +kernel
theorem ok_pd_b : isOk (pdRun (.var 0)) (scopeState stNot RN) 1000 = true := by decide +kernel
theorem val_pd_b : isIndB (outVal (pdRun (.var 0)) (scopeState stNot RN) 1000) = true := by decide +kernel

end Aux

/-- **The decisions `split_simNot` reads, at every table aligned with the checker at `stNot`.** -/
theorem parDecNot {D : Decisions} (hd : DecTab D stNot) :
    ParDecNot D ∧ DecNot D := by
  open Ochr.Meaning.Regress.GenNeutralContent in
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hd.flags 100 RN bodyNot _ 1000 _ (runs_out (Ochr.Meaning.Steps.Form.ColumnC.Aux.flagsRun bodyNot) _ 1000
      Aux.ok_flags_body), Aux.val_flags_body]
  · rw [hd.flags 100 RN ctorF _ 1000 _ (runs_out (Ochr.Meaning.Steps.Form.ColumnC.Aux.flagsRun ctorF) _ 1000
      Aux.ok_flags_F), Aux.val_flags_F]
  · rw [hd.flags 100 RN ctorT _ 1000 _ (runs_out (Ochr.Meaning.Steps.Form.ColumnC.Aux.flagsRun ctorT) _ 1000
      Aux.ok_flags_T), Aux.val_flags_T]
  · rw [hd.joinMoves 100 RN [] bodyNot _ 1000 _ (runs_out (Ochr.Meaning.Steps.Form.ColumnP.Aux.jmRun bodyNot) _ 1000
      Aux.ok_jm), Aux.val_jm]
  · exact (hd.placeDecl 100 RN (.var 1) _ 1000 _ (runs_out (Ochr.Meaning.Steps.Form.ColumnP.Aux.pdRun (.var 1)) _ 1000
      Aux.ok_pd_self)).trans (Aux.isPiB_eq Aux.val_pd_self)
  · exact (hd.placeDecl 100 RN (.var 0) _ 1000 _ (runs_out (Ochr.Meaning.Steps.Form.ColumnP.Aux.pdRun (.var 0)) _ 1000
      Aux.ok_pd_b)).trans (Aux.isIndB_eq Aux.val_pd_b)

/-! ## An instance of `DataModelB` -/

/-- A data model covering every declaration, reading every parameter type as the error type. -/
def dmTriv : DataModel := { covers := fun _ => True, recOf := fun _ _ _ => .none, paramTy := fun _ _ _ => TyM.err }

theorem fieldTerm_B (c i : Nat) : fieldTerm declB c i = none := by
  unfold fieldTerm
  rcases c with _ | _ | c <;> simp [declB]

/-- **`DataModelB` has an instance**: `dmTriv`, at every table and every list after `B`. -/
theorem dataModelB_triv (D : Decisions) (rest : List IndDecl := []) : DataModelB dmTriv D rest := by
  refine ⟨trivial, fun _ _ => trivial, fun φ Δ d hd Δ' ρ => ?_⟩
  simp only [List.mem_singleton] at hd; subst hd
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro ps c i e FT _ _ _ _ hft
    rw [fieldTerm_B] at hft; cases hft
  · intro ps j hn PT _ _ hp
    simp [declB] at hp
  · intro ps j A c hl _ _ hps
    have : ps = [] := List.eq_nil_of_length_eq_zero (by rw [hl]; rfl)
    subst this; simp at hps
  · intro ps j v A c _ _ hpt hmem
    exact absurd (hpt ▸ hmem) (DataModel.err_mem_false _ _)
  · intro ps ps' hpt hl _
    have hps : ps = [] := by
      rcases ps with _ | ⟨a, ps⟩
      · rfl
      · exact absurd (hpt 0 (by simp)) (DataModel.err_mem_false _ _)
    subst hps
    have : ps' = [] := List.eq_nil_of_length_eq_zero hl
    subst this; rfl
  · intro ps _ _ c i e hc hi _
    rcases c with _ | _ | c
    · exact absurd hi (by simp [DataLib.arity, declB])
    · exact absurd hi (by simp [DataLib.arity, declB])
    · exact absurd hc (by simp [declB])

/-! ## The start bundles at `stNot` -/

/-- Δ at the start: `σ0 : B`. -/
def ΔN (dm : DataModel) : Nat → TyS := fun σ => if σ = 0 then .plain (tyBM dm) else .plain TyM.err

theorem ckContent_stNot {p : Place} {w : Value} (h : ckContent stNot.env p = some w) :
    (p = .var 1 ∧ w = .gfn "Not") ∨ (p = .var 0 ∧ w = .abs 0) := by
  rcases hp : p.steps with ⟨i, path⟩
  simp only [ckContent, hp] at h
  unfold ckVarPos at h
  by_cases hi : i < 2
  · have hi' : i < stNot.env[stNot.env.size - 1]!.binds.size := hi
    rw [if_pos hi'] at h
    simp only [Option.bind_some] at h
    have hnil : ∀ u : Value, (u = .gfn "Not" ∨ u = .abs 0) → u.follow path = some w → path = [] ∧ w = u := by
      rintro u hu hf
      cases path with
      | nil => simp [Value.follow] at hf; exact ⟨rfl, hf.symm⟩
      | cons s ss => rcases hu with rfl | rfl <;> cases s <;> simp [Value.follow, stepV] at hf
    rcases i with _ | _ | i
    · obtain ⟨rfl, rfl⟩ := hnil _ (.inr rfl) h
      exact .inr ⟨place_var_of_steps hp, rfl⟩
    · obtain ⟨rfl, rfl⟩ := hnil _ (.inl rfl) h
      exact .inl ⟨place_var_of_steps hp, rfl⟩
    · omega
  · have hi' : ¬ i < stNot.env[stNot.env.size - 1]!.binds.size := hi
    rw [if_neg hi'] at h; cases h

theorem bind_stNot {f i : Nat} {b : Binding} (h : stNot.env[f]?.bind (fun fr => fr.binds[i]?) = some b) :
    (f = 1 ∧ i = 0 ∧ b = selfNot) ∨ (f = 1 ∧ i = 1 ∧ b = bB (.abs 0)) := by
  rcases f with _ | _ | f
  · simp [stNot, envB] at h
  · rcases i with _ | _ | i
    · simp [stNot, envB] at h; exact .inl ⟨rfl, rfl, h.symm⟩
    · simp [stNot, envB] at h; exact .inr ⟨rfl, rfl, h.symm⟩
    · simp [stNot, envB] at h
  · simp [stNot, envB] at h

theorem refd_stNot {σ : Nat} (h : stNot.Refd σ) : σ < 1 := by
  refine MState.refd_lt stNot 1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ σ h
  · intro v hv σ hσ; rw [stNot_env, values_envB] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (Bool.false_ne_true hσ).elim
    · have := abs_hasAbs_eq hσ; omega
  · intro f i b T hb hT σ hσ
    rcases bind_stNot hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfNot, bB] at hT <;> subst hT <;>
      exact (Bool.false_ne_true hσ).elim
  · intro f i b P ws j hb hT
    rcases bind_stNot hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfNot, bB] at hT
  · intro G hG σ hσ; simp [stNot] at hG; subst hG; exact (Bool.false_ne_true hσ).elim
  · intro m σ' h; simp [stNot] at h
  · intro σ' v h; simp [stNot] at h
  · intro σ' T h σ hσ
    rcases σ' with _ | σ'
    · simp [stNot] at h; subst h; exact (Bool.false_ne_true hσ).elim
    · simp [stNot] at h

/-- **`Inv` at `Not`'s start**, at a table reading the function's own binding as the checker does. -/
theorem inv_stNot {D : Decisions} {rest : List IndDecl} (hdec : DecNot D) : Inv D (declB :: rest) stNot := by
  have ha : Value.abs 0 ∈ BVals := by simp [BVals]
  have hvals : ∀ v ∈ Env.values stNot.env, v = .gfn "Not" ∨ v = .abs 0 := fun v hv => by
    rw [stNot_env, values_envB] at hv; simpa using hv
  have hpos : ∀ p ∈ allPos stNot.env, p = .bind 1 0 ∨ p = .bind 1 1 := fun p hp => by
    rw [stNot_env, allPos_envB] at hp; simpa using hp
  have hbind : ∀ {f i b}, stNot.env[f]?.bind (fun fr => fr.binds[i]?) = some b →
      (f = 1 ∧ i = 0 ∧ b = selfNot) ∨ (f = 1 ∧ i = 1 ∧ b = bB (.abs 0)) := fun hb => bind_stNot hb
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro p hp; rcases hpos p hp with rfl | rfl <;> exact Bool.false_ne_true
  · intro p _ q _ l h; rw [stNot_env, shape_envB ha] at h; cases h
  · intro v hv l hl; rcases hvals v hv with rfl | rfl <;> cases hl
  · intro l; rw [stNot_env, values_envB]; exact Nat.zero_le _
  · exact ⟨fun a => ⟨a, fun b ⟨p, hp, w, hw, _⟩ => by rcases hpos p hp with rfl | rfl <;> cases hw⟩⟩
  · intro v hv; rcases hvals v hv with rfl | rfl <;> exact Bool.false_ne_true
  · intro σ h; exact refd_stNot h
  · intro T hT σ hσ; simp [stNot] at hT; subst hT; exact (Bool.false_ne_true hσ).elim
  · intro σ r h; simp [stNot] at h
  · rfl
  · intro v hv l hl; rcases hvals v hv with rfl | rfl <;> cases hl
  · intro v hv; rcases hvals v hv with rfl | rfl <;> rfl
  · intro f i b hb T hT; rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfNot, bB] at hT <;> subst hT <;> rfl
  · intro T hT; simp [stNot] at hT; subst hT; rfl
  · intro G hG; simp [stNot] at hG; subst hG; rfl
  · intro v hv; rcases hvals v hv with rfl | rfl <;> rfl
  · intro f i b hb; rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact ⟨fun T hT l => by simp [selfNot] at hT; subst hT; rfl, fun P ws j h => by simp [selfNot] at h⟩
    · exact ⟨fun T hT l => by simp [bB] at hT; subst hT; rfl, fun P ws j h => by simp [bB] at h⟩
  · intro T hT l; simp [stNot] at hT; subst hT; rfl
  · intro G hG l; simp [stNot] at hG; subst hG; rfl
  · intro n σ h; simp [stNot] at h
  · intro σ v h; simp [stNot] at h
  · intro k l hk; rw [stNot_env, liveLoan_envB ha] at hk; cases hk
  · intro pos path _ l hl; rw [stNot_env, liveLoan_envB ha] at hl; cases hl
  · intro v hv l; rcases hvals v hv with rfl | rfl <;> rfl
  · intro v hv; rcases hvals v hv with rfl | rfl <;> rfl
  · intro p w n args hc hpd hfind
    rcases ckContent_stNot hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [show DecideScope.topReadings stNot = RN from rfl, hdec.1] at hpd; cases hpd
    · rfl
  · intro v hv l hl; rcases hvals v hv with rfl | rfl <;> cases hl
  · intro v hv; rcases hvals v hv with rfl | rfl <;> rfl
  · intro p _ h; rcases ckContent_stNot h with ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
  · intro σ r h; simp [stNot] at h
  · intro σ r h; simp [stNot] at h
  · intro σ l h; rcases σ with _ | σ <;> simp [stNot] at h
  · intro l h; exact absurd h (occurs_envB ha stNot stNot_env l)
  -- (K): the function's own binding at its Π-type, the parameter holds no borrow and no function
  · refine (fun f i b hb => ?_)
    · rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · exact fun l c e => (nomatch e)
      · exact fun l c e => (nomatch e)

section
variable {dm : DataModel} {D : Decisions} {φ : Future} {rest : List IndDecl}

theorem absTyM_stNot (ρ : Assignment) :
    MState.absTyM (KNot dm D φ (ΔN dm) rest).dm (KNot dm D φ (ΔN dm) rest).M (KNot dm D φ (ΔN dm) rest).Γ ρ stNot 0 = tyBM dm := by
  show (meanV (KNot dm D φ (ΔN dm) rest) ρ (fun _ => .err) (.plain TyM.err) tyB).asTy = _
  rw [meanV_tyB _ rfl]; rfl

theorem asg_stNot (ρ : Assignment) (hρ : ρ 0 ∈ₛ[dm.read] tyBM dm) : Asg (KNot dm D φ (ΔN dm) rest) ρ stNot := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro σ h _
    obtain rfl : σ = 0 := by have := refd_stNot h; omega
    rw [absTyM_stNot]; exact hρ
  · intro n σ h; simp [stNot] at h
  · intro σ v h; simp [stNot] at h
  · intro σ r h; simp [stNot] at h
  · intro σ h _
    obtain rfl : σ = 0 := by have := refd_stNot h; omega
    rw [absTyM_stNot]; exact tyBM_level dm
  · intro G h; simp only [MState.goalM, stNot, Option.map_some, Option.some.injEq] at h; subst h
    show (meanV (KNot dm D φ (ΔN dm) rest) ρ (fun _ => .err) (.plain TyM.err) tyB).asTy.level.isSome = true
    rw [meanV_tyB _ rfl]; exact tyBM_level dm
  · intro σ h _
    obtain rfl : σ = 0 := by have := refd_stNot h; omega
    show ΔN dm 0 = Value.tyS _ _ _ ρ tyB
    show _ = TyS.plain (meanV (KNot dm D φ (ΔN dm) rest) ρ (fun _ => .err) (.plain TyM.err) tyB).asTy
    rw [meanV_tyB _ rfl]; rfl

/-- **`Pre` at `Not`'s start**, under `DataModelB`, at an assignment giving `σ0` a member of `B`. -/
theorem pre_stNot (hdm : DataModelB dm D rest) (hdec : DecNot D) (ρ : Assignment)
    (hρ : ρ 0 ∈ₛ[dm.read] tyBM dm) : Pre (KNot dm D φ (ΔN dm) rest) ρ stNot := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [norm_stNot]
  · exact ctxS_Not hdm (ΔN dm) rfl rfl
  · exact inv_stNot hdec
  · exact asg_stNot ρ hρ

theorem shape_SMNot (ρ : Assignment) (p : Pos) : (SM' (KNot dm D φ (ΔN dm) rest) ρ stNot).shape p = none := by
  unfold SM'; rw [sstate_shape]; exact shape_envB (by simp [BVals]) p

theorem liveLabels_SMNot (ρ : Assignment) : (SM' (KNot dm D φ (ΔN dm) rest) ρ stNot).liveLabels = [] := by
  unfold SState.liveLabels
  rw [List.filterMap_eq_nil_iff.mpr (fun p _ => shape_SMNot ρ p), List.mergeSort_nil]

theorem rel_stNot (ρ : Assignment) (φ' : Future) :
    Rel (KNot dm D φ (ΔN dm) rest) ρ φ' id stNot (SM' (KNot dm D φ (ΔN dm) rest) ρ stNot) :=
  Rel.start_noLive _ _ _ _ fun l h => by simp [SState.Live, liveLabels_SMNot] at h

/-- **The split's step applied at the column's own start**: the checker's start state for `Not`'s body (any state
with `stNot`'s kernel in the plain mode), the reference's start state read from it (`SM'`) under any assignment
giving `σ0` a member of `B`, at the checker's table there. From the checker's successful `checkTail` of the body
with a continuation keeping the counters in world `T`, the reference's run of the body succeeds with the other
constructor, and `Out` holds at that world's leaf. Assumes the checker fact `SplitNotInv`; of the data model,
`DataModelB` (an instance: `dataModelB_triv`). -/
theorem body_outNot (hSp : SplitNotInv) (hdm : DataModelB dm D rest) (hD : DecTab D stNot) {fuel : Nat}
    {k : Value → Value → M Unit} (hk : KeepsAtT k) {st st' : MState} {bh : Nat} (hkern : Kern stNot st) (hm : Mode st)
    (htd : st.tailDecl = none) (hrun : Runs (Ochr.checkTail fuel bodyNot k) st bh () st') (ρ : Assignment)
    (hρ : ρ 0 ∈ₛ[dm.read] tyBM dm) (hint : TyS) :
    TailOut (KNot dm D φ (ΔN dm) rest) ρ φ id st (SM' (KNot dm D φ (ΔN dm) rest) ρ stNot)
      (runT (KNot dm D φ (ΔN dm) rest) ρ φ true hint bodyNot) k :=
  have hd := parDecNot hD
  split_outNot hSp hdm hd.1 hd.2 hk hkern hm htd hrun ((pre_stNot hdm hd.2 ρ hρ).of_kern hkern)
    ((rel_stNot ρ φ).of_kern hkern) hint

end

/-- The same at the instance `dmTriv`, for every table aligned at `stNot`: the bundles are inhabited. -/
theorem body_outNot_triv (hSp : SplitNotInv) {D : Decisions} (hD : DecTab D stNot) (φ : Future) {fuel : Nat}
    {k : Value → Value → M Unit} (hk : KeepsAtT k) {st st' : MState} {bh : Nat} (hkern : Kern stNot st) (hm : Mode st)
    (htd : st.tailDecl = none) (hrun : Runs (Ochr.checkTail fuel bodyNot k) st bh () st') (ρ : Assignment)
    (hρ : ρ 0 ∈ₛ[dmTriv.read] tyBM dmTriv) (hint : TyS) :
    TailOut (KNot dmTriv D φ (ΔN dmTriv)) ρ φ id st (SM' (KNot dmTriv D φ (ΔN dmTriv)) ρ stNot)
      (runT (KNot dmTriv D φ (ΔN dmTriv)) ρ φ true hint bodyNot) k :=
  body_outNot hSp (dataModelB_triv D) hD hk hkern hm htd hrun ρ hρ hint

/-- One declaration, `inductive X := MkX`, declared AFTER `B`. -/
def declX : IndDecl := { name := "X", ctors := [("MkX", [])] }

/-- **The regression of the one-list ruling with a declared type** (docs/31 D177): the split's step for `Not`,
applied at the column's own start, at a context whose declaration list is `[B, X]` while the checker's state declares
`[B]`. The same step as `body_outNot_triv` (proved from it: `body_outNot` at `rest := [X]`), with `Pre`'s invariant
discharged at the longer list at the start (`inv_stNot`) and at both leaves (`DataNotSplit.inv_envBT`): its clause
(V) (`ShapeFacts.fits`) reads the scrutinee's declared reading from the table (`DecNot`), no longer from the list
having one name. Assumes the checker fact `SplitNotInv`. -/
theorem body_outNot_oneMore (hSp : SplitNotInv) {D : Decisions} (hD : DecTab D stNot) (φ : Future) {fuel : Nat}
    {k : Value → Value → M Unit} (hk : KeepsAtT k) {st st' : MState} {bh : Nat} (hkern : Kern stNot st) (hm : Mode st)
    (htd : st.tailDecl = none) (hrun : Runs (Ochr.checkTail fuel bodyNot k) st bh () st') (ρ : Assignment)
    (hρ : ρ 0 ∈ₛ[dmTriv.read] tyBM dmTriv) (hint : TyS) :
    TailOut (KNot dmTriv D φ (ΔN dmTriv) [declX]) ρ φ id st (SM' (KNot dmTriv D φ (ΔN dmTriv) [declX]) ρ stNot)
      (runT (KNot dmTriv D φ (ΔN dmTriv) [declX]) ρ φ true hint bodyNot) k :=
  body_outNot hSp (dataModelB_triv D [declX]) hD hk hkern hm htd hrun ρ hρ hint

/-- The checker's state at `Not`'s start declares `[B]`, a strict prefix of the context's `[B, X]`. -/
example (D : Decisions) : stNot.inds <+: (KNot dmTriv D (fun _ => .err) (ΔN dmTriv) [declX]).Γ := ⟨[declX], rfl⟩

/-- `B`'s constructor `T` is a member at `dmTriv`, so the assignment `σ0 ↦ T` is one the theorem above speaks of. -/
example : datB dmTriv 0 ∈ₛ[dmTriv.read] tyBM dmTriv := datB_mem dmTriv (by decide)

end Ochr.Meaning.Steps.Form.ColumnNot
