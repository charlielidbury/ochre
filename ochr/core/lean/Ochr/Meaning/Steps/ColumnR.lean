import Ochr.Meaning.Steps.ColumnRSplit
import Ochr.Meaning.Steps.ColumnIRun

/-!
# The column `R`: the knot, from the checker's one split run (lead17, 2026-11-21; docs/31 D134)

`def R (n : Nat) : Nat by n := match n { Z => Z, S m => R(m) }`. The reference's `.fix` clause forms `R`'s closure by
stages (`fixStage`): at an argument of rank `r`, stage `r + 1`, whose body runs with `self` the stage below at the
weakened type. The knot (`FixKnot.stages_below`, here `goodBelow_stg`): stage `b + 1` is good at every number up to `b`
when stage `b` is good below `b`, because in world `S` the body calls `self` at `a - 1 < b` (`fixBodyAt_R`). The closure
is then a member of `Π(n : Nat). Nat` (`column_R_run`; no fact assumed). The simulation of the body at each stage
(`ColumnRSplit.split_simR`, assuming `SplitRInv`) holds with the outer induction hypothesis discharged: at every stage
`b` the context's `R` is the reference's own stage-`b` closure (`column_R_ff`).

The decisions: one table per check, the checker's at the body's start state; what the reference reads of it is
computed by kernel evaluation of the checker's decision procedures at `stR` (`parDecR`, `fixDecR`).
-/

namespace Ochr.Meaning.Steps.Form.ColumnR

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Strict.Witness
open Ochr.Meaning.Steps.Form.ColumnI (piNat nB psI outI NoBorrow liveLabels_of_rel ρAt)
open Ochr.Meaning.Steps.Form.ColumnP (rel_transfer kern_of_env ρS ΔP ΔPS absTyM_nat RI pn0 RefJ RefP dropN setN0)

/-! ## The decisions, at a table aligned with the checker at `stR` -/

namespace Aux

open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal runs_out)
open Ochr.Meaning.Steps.Form.ColumnC.Aux (flagsRun declRun isOther isOther_eq)

abbrev pdRun (p : Place) : M DeclInfo := withLive true (Ochr.placeDecl 100 [] p)
abbrev jmRun (t : Term) : M (List Place) := withLive true (Ochr.jdMoves 100 [] [] t [])
abbrev cpRun : M Bool := Ochr.declCopy 100 .other

theorem ok_flags_body : isOk (flagsRun bodyR) (scopeState stR RI) 1000 = true := by decide +kernel
theorem val_flags_body : outVal (flagsRun bodyR) (scopeState stR RI) 1000 = (false, false) := by decide +kernel
theorem ok_flags_call : isOk (flagsRun callR) (scopeState stR RI) 1000 = true := by decide +kernel
theorem val_flags_call : outVal (flagsRun callR) (scopeState stR RI) 1000 = (false, false) := by decide +kernel
theorem ok_flags_seal : isOk (flagsRun sealR) (scopeState stR []) 1000 = true := by decide +kernel
theorem val_flags_seal : outVal (flagsRun sealR) (scopeState stR []) 1000 = (false, false) := by decide +kernel
theorem ok_flags_n0 : isOk (flagsRun (.place pn0)) (scopeState stR RI) 1000 = true := by decide +kernel
theorem val_flags_n0 : outVal (flagsRun (.place pn0)) (scopeState stR RI) 1000 = (false, false) := by decide +kernel
theorem ok_pd_n0 : isOk (pdRun pn0) (scopeState stR RI) 1000 = true := by decide +kernel
theorem val_pd_n0 : isOther (outVal (pdRun pn0) (scopeState stR RI) 1000) = true := by decide +kernel
theorem ok_pd_n : isOk (pdRun (.var 0)) (scopeState stR RI) 1000 = true := by decide +kernel
theorem val_pd_n : isOther (outVal (pdRun (.var 0)) (scopeState stR RI) 1000) = true := by decide +kernel
theorem ok_cp : isOk cpRun stR 1000 = true := by decide +kernel
theorem val_cp : outVal cpRun stR 1000 = false := by decide +kernel
theorem ok_jm : isOk (jmRun bodyR) (scopeState stR RI) 1000 = true := by decide +kernel
theorem val_jm0 : (match outVal (jmRun bodyR) (scopeState stR RI) 1000 with
    | [.var 0] => true
    | _ => false) = true := by decide +kernel
theorem val_jm : outVal (jmRun bodyR) (scopeState stR RI) 1000 = [.var 0] := by
  have h := val_jm0
  revert h
  generalize outVal (jmRun bodyR) (scopeState stR RI) 1000 = x
  intro h
  split at h
  · rfl
  · cases h

end Aux

/-- **`ParDecR` at every table aligned with the checker at `stR`.** -/
theorem parDecR {D : Decisions} (hd : DecTab D stR) : ParDecR D := by
  open Ochr.Meaning.Regress.GenNeutralContent in
  have hpd : D.placeDecl RI pn0 = .other :=
    (hd.placeDecl 100 RI pn0 _ 1000 _ (runs_out (Aux.pdRun pn0) _ 1000 Aux.ok_pd_n0)).trans
      (Ochr.Meaning.Steps.Form.ColumnC.Aux.isOther_eq Aux.val_pd_n0)
  have hpd0 : D.placeDecl RI (.var 0) = .other :=
    (hd.placeDecl 100 RI (.var 0) _ 1000 _ (runs_out (Aux.pdRun (.var 0)) _ 1000 Aux.ok_pd_n)).trans
      (Ochr.Meaning.Steps.Form.ColumnC.Aux.isOther_eq Aux.val_pd_n)
  have hcp : D.copy .other = false := by
    rw [hd.copy 100 .other _ 1000 _ (runs_out Aux.cpRun _ 1000 Aux.ok_cp), Aux.val_cp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hd.flags 100 RI bodyR _ 1000 _ (runs_out (Ochr.Meaning.Steps.Form.ColumnC.Aux.flagsRun bodyR) _ 1000
      Aux.ok_flags_body), Aux.val_flags_body]
  · rw [hd.flags 100 RI callR _ 1000 _ (runs_out (Ochr.Meaning.Steps.Form.ColumnC.Aux.flagsRun callR) _ 1000
      Aux.ok_flags_call), Aux.val_flags_call]
  · rw [hd.flags 100 RI (.place pn0) _ 1000 _ (runs_out (Ochr.Meaning.Steps.Form.ColumnC.Aux.flagsRun (.place pn0)) _ 1000
      Aux.ok_flags_n0), Aux.val_flags_n0]
  · rw [hpd]; exact hcp
  · rw [hpd0]; exact hcp
  · rw [hd.joinMoves 100 RI [] bodyR _ 1000 _ (runs_out (Aux.jmRun bodyR) _ 1000 Aux.ok_jm), Aux.val_jm]
  · rw [hd.flags 100 [] sealR _ 1000 _ (runs_out (Ochr.Meaning.Steps.Form.ColumnC.Aux.flagsRun sealR) _ 1000
      Aux.ok_flags_seal), Aux.val_flags_seal]

namespace Aux

open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal)
open Ochr.Meaning.Steps.Form.ColumnC.Aux (flagsRun isOther)
open Ochr.Meaning.Steps.Form.ColumnI.Aux (typeDeclRun piSortRun)

theorem ok_td_nat (sc : List DeclInfo) (hsc : sc = [] ∨ sc = [.other]) :
    isOk (typeDeclRun .nat) (scopeState stR sc) 1000 = true := by
  rcases hsc with rfl | rfl <;> decide +kernel
theorem val_td_nat (sc : List DeclInfo) (hsc : sc = [] ∨ sc = [.other]) :
    isOther (outVal (typeDeclRun .nat) (scopeState stR sc) 1000) = true := by
  rcases hsc with rfl | rfl <;> decide +kernel
theorem ok_piSort : isOk (piSortRun (.pi [⟨"n"⟩] [.nat] .nat)) (scopeState stR []) 1000 = true := by decide +kernel
theorem val_piSort : outVal (piSortRun (.pi [⟨"n"⟩] [.nat] .nat)) (scopeState stR []) 1000 = 1 := by decide +kernel
theorem ok_flags_fix : isOk (flagsRun fixR) (scopeState stR []) 1000 = true := by decide +kernel
theorem val_flags_fix : outVal (flagsRun fixR) (scopeState stR []) 1000 = (false, false) := by decide +kernel

end Aux

/-- **The reference `.fix` clause's decisions for `P`, at the empty scope**, at every table aligned with the checker
at `stR` (as `ColumnI.fixDecI` for `I`). -/
theorem fixDecR {D : Decisions} (hd : DecTab D stR) :
    D.typeDecl [] .nat = .other ∧ D.typeDecl [.other] .nat = .other ∧ D.piSort [] (.pi [⟨"n"⟩] [.nat] .nat) = 1 ∧
      D.flags [] fixR = (false, false) := by
  open Ochr.Meaning.Regress.GenNeutralContent in
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hd.typeDecl 100 [] .nat _ 1000 _ (runs_out (ColumnI.Aux.typeDeclRun .nat) _ 1000 (Aux.ok_td_nat [] (.inl rfl)))]
    exact Ochr.Meaning.Steps.Form.ColumnC.Aux.isOther_eq (Aux.val_td_nat [] (.inl rfl))
  · rw [hd.typeDecl 100 [.other] .nat _ 1000 _
      (runs_out (ColumnI.Aux.typeDeclRun .nat) _ 1000 (Aux.ok_td_nat [.other] (.inr rfl)))]
    exact Ochr.Meaning.Steps.Form.ColumnC.Aux.isOther_eq (Aux.val_td_nat [.other] (.inr rfl))
  · rw [hd.piSort 100 [] _ _ 1000 _ (runs_out (ColumnI.Aux.piSortRun _) _ 1000 Aux.ok_piSort), Aux.val_piSort]
  · rw [hd.flags 100 [] fixR _ 1000 _ (runs_out (Ochr.Meaning.Steps.Form.ColumnC.Aux.flagsRun fixR) _ 1000 Aux.ok_flags_fix),
      Aux.val_flags_fix]

/-! ## The start bundles at `stR` -/

theorem bind_envN {v : Value} {f i : Nat} {b : Binding} (h : (envN v)[f]?.bind (fun fr => fr.binds[i]?) = some b) :
    (f = 1 ∧ i = 0 ∧ b = selfR) ∨ (f = 1 ∧ i = 1 ∧ b = { nB with val := v }) := by
  rcases f with _ | _ | f
  · simp [envN] at h
  · rcases i with _ | _ | i
    · simp [envN] at h; exact .inl ⟨rfl, rfl, h.symm⟩
    · simp [envN] at h; exact .inr ⟨rfl, rfl, h.symm⟩
    · simp [envN] at h
  · simp [envN] at h

theorem ckContent_stR {p : Place} {v : Value} (h : ckContent stR.env p = some v) : v = .gfn "R" ∨ v = .abs 0 := by
  rcases hp : p.steps with ⟨i, path⟩
  simp only [ckContent, hp] at h
  unfold ckVarPos at h
  by_cases hi : i < 2
  · have hi' : i < stR.env[stR.env.size - 1]!.binds.size := hi
    rw [if_pos hi'] at h
    simp only [Option.bind_some] at h
    have hv : ∀ w : Value, (w = .gfn "R" ∨ w = .abs 0) → w.follow path = some v → v = .gfn "R" ∨ v = .abs 0 := by
      rintro w hw hf
      cases path with
      | nil => simp [Value.follow] at hf; exact hf ▸ hw
      | cons s ss => rcases hw with rfl | rfl <;> cases s <;> simp [Value.follow, stepV] at hf
    rcases i with _ | _ | i
    · exact hv _ (.inr rfl) h
    · exact hv _ (.inl rfl) h
    · omega
  · have hi' : ¬ i < stR.env[stR.env.size - 1]!.binds.size := hi
    rw [if_neg hi'] at h; cases h

theorem refd_stR {σ : Nat} (h : stR.Refd σ) : σ < 1 := by
  refine MState.refd_lt stR 1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ σ h
  · intro v hv σ hσ; rw [stR_env, values_envN] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (Bool.false_ne_true hσ).elim
    · have := abs_hasAbs_eq hσ; omega
  · intro f i b T hb hT σ hσ; rw [stR_env] at hb
    rcases bind_envN hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfR, nB] at hT <;> subst hT <;>
      exact (Bool.false_ne_true hσ).elim
  · intro f i b P ws j hb hT; rw [stR_env] at hb
    rcases bind_envN hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfR, nB] at hT
  · intro G hG σ hσ; simp [stR] at hG; subst hG; exact (Bool.false_ne_true hσ).elim
  · intro m σ' h; simp [stR] at h
  · intro σ' v h; simp [stR] at h
  · intro σ' T h σ hσ
    rcases σ' with _ | σ'
    · simp [stR] at h; subst h; exact (Bool.false_ne_true hσ).elim
    · simp [stR] at h

theorem inv_stR (D : Decisions) : Inv D [] stR := by
  have ha : Value.abs 0 ∈ NVals := by simp [NVals]
  have hvals : ∀ v ∈ Env.values stR.env, v = .gfn "R" ∨ v = .abs 0 := fun v hv => by
    rw [stR_env, values_envN] at hv; simpa using hv
  have hpos : ∀ p ∈ allPos stR.env, p = .bind 1 0 ∨ p = .bind 1 1 := fun p hp => by
    rw [stR_env, allPos_envN] at hp; simpa using hp
  have hbind : ∀ {f i b}, stR.env[f]?.bind (fun fr => fr.binds[i]?) = some b →
      (f = 1 ∧ i = 0 ∧ b = selfR) ∨ (f = 1 ∧ i = 1 ∧ b = nB) := fun hb => bind_envN hb
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro p hp; rcases hpos p hp with rfl | rfl <;> exact Bool.false_ne_true
  · intro p _ q _ l h; rw [shape_stR] at h; cases h
  · intro v hv l hl; rcases hvals v hv with rfl | rfl <;> cases hl
  · intro l; rw [stR_env, values_envN]; exact Nat.zero_le _
  · exact ⟨fun a => ⟨a, fun b ⟨p, hp, w, hw, _⟩ => by rcases hpos p hp with rfl | rfl <;> cases hw⟩⟩
  · intro v hv; rcases hvals v hv with rfl | rfl <;> exact Bool.false_ne_true
  · intro σ h; exact refd_stR h
  · intro T hT σ hσ; simp [stR] at hT; subst hT; exact (Bool.false_ne_true hσ).elim
  · intro σ r h; simp [stR] at h
  · rfl
  · intro v hv l hl; rcases hvals v hv with rfl | rfl <;> cases hl
  · intro v hv; rcases hvals v hv with rfl | rfl <;> rfl
  · intro f i b hb T hT; rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfR, nB] at hT <;> subst hT <;> rfl
  · intro T hT; simp [stR] at hT; subst hT; rfl
  · intro G hG; simp [stR] at hG; subst hG; rfl
  · intro v hv; rcases hvals v hv with rfl | rfl <;> rfl
  · intro f i b hb; rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact ⟨fun T hT l => by simp [selfR] at hT; subst hT; rfl, fun P ws j h => by simp [selfR] at h⟩
    · exact ⟨fun T hT l => by simp [nB] at hT; subst hT; rfl, fun P ws j h => by simp [nB] at h⟩
  · intro T hT l; simp [stR] at hT; subst hT; rfl
  · intro G hG l; simp [stR] at hG; subst hG; rfl
  · intro n σ h; simp [stR] at h
  · intro σ v h; simp [stR] at h
  · intro k l hk; rw [stR_env, liveLoan_envN ha] at hk; cases hk
  · intro pos path _ l hl; rw [stR_env, liveLoan_envN ha] at hl; cases hl
  · intro v hv l; rcases hvals v hv with rfl | rfl <;> rfl
  · intro v hv; rcases hvals v hv with rfl | rfl <;> rfl
  · intro p v n args _ _ h; simp at h
  · intro v hv l hl; rcases hvals v hv with rfl | rfl <;> cases hl
  · intro v hv; rcases hvals v hv with rfl | rfl <;> rfl
  · intro p _ h; rcases ckContent_stR h with h | h <;> cases h
  · intro σ r h; simp [stR] at h
  · intro σ r h; simp [stR] at h
  · intro σ l h; rcases σ with _ | σ <;> simp [stR] at h
  · intro l h; exact absurd h (occurs_envN ha stR stR_env l)
  -- (K): the function's own binding at its Π-type, the parameter holds no borrow and no function
  · refine (fun f i b hb => ?_)
    · rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · exact ⟨fun l c e => (nomatch e), fun l c e => (nomatch e)⟩
      · exact ⟨fun l c e => (nomatch e), fun l c e => (nomatch e)⟩

section
variable {dm : DataModel} {D : Decisions} {G : Sem × TyS} {b : Nat}

theorem asg_stR (ρ : Assignment) (hρ : ∃ m, ρ 0 = .el0 Nat m) : Asg (KR dm D ΔP G b) ρ stR := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro σ h _
    obtain rfl : σ = 0 := by have := refd_stR h; omega
    rw [absTyM_nat _ _ (st := stR) rfl]; obtain ⟨m, hm⟩ := hρ; exact ⟨m, hm.symm⟩
  · intro n σ h; simp [stR] at h
  · intro σ v h; simp [stR] at h
  · intro σ r h; simp [stR] at h
  · intro σ h _
    obtain rfl : σ = 0 := by have := refd_stR h; omega
    rw [absTyM_nat _ _ (st := stR) rfl]; rfl
  · intro G h; simp only [MState.goalM, stR, Option.map_some, Option.some.injEq] at h; subst h; rfl
  · intro σ h _
    obtain rfl : σ = 0 := by have := refd_stR h; omega
    rfl

theorem pre_stR (hGl : G.2.label = none) (hMB : ∀ Δ, MemBelow (KR dm D Δ G b) G gR b) (ρ : Assignment)
    (hρ : ∃ m, ρ 0 = .el0 Nat m) : Pre (KR dm D ΔP G b) ρ stR := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [norm_stR]
  · exact ctxS_R ΔP hGl hMB rfl rfl
  · exact inv_stR D
  · exact asg_stR ρ hρ

theorem shape_SMR (ρ : Assignment) (p : Pos) : (SM' (KR dm D ΔP G b) ρ stR).shape p = none := by
  unfold SM'; rw [sstate_shape]; exact shape_stR p

theorem liveLabels_SMR (ρ : Assignment) : (SM' (KR dm D ΔP G b) ρ stR).liveLabels = [] := by
  unfold SState.liveLabels
  rw [List.filterMap_eq_nil_iff.mpr (fun p _ => shape_SMR ρ p), List.mergeSort_nil]

theorem rel_stR (ρ : Assignment) (φ' : Future) : Rel (KR dm D ΔP G b) ρ φ' id stR (SM' (KR dm D ΔP G b) ρ stR) :=
  Rel.start_noLive _ _ _ _ fun l h => by simp [SState.Live, liveLabels_SMR] at h

end


/-! ## The body inside the `.fix` clause at stage `b + 1`, and the knot -/

/-- The body's frame at stage `b + 1`, on both sides: `self` the stage-`b` closure at the weakened type, `n` the
number `a`. -/
noncomputable def frR (G : Sem × TyS) (a : Nat) : SFrame :=
  { binds := [{ ty := .plain G.2.m, val := fun _ => G.1, decl := .pi .other },
      { ty := .plain TyM.nat, val := fun _ => .el0 Nat a, decl := .other }] }

section
variable {dm : DataModel} {D : Decisions} {φ : Future} {G : Sem × TyS} {b : Nat}

/-- **The checker's start state, read as a reference state** under `σ0 ↦ a`, in the stage's context: `[{}, frR G a]`
(`G`'s type is `.plain`). -/
theorem env_SMR (hG : G.2 = .plain G.2.m) (ρ : Assignment) (a : Nat) :
    (SM' (KR dm D ΔP G b) (ρAt ρ a) stR).env = [{}, frR G a] := by
  have h0 : Binding.refTy (KR dm D ΔP G b).dm (KR dm D ΔP G b).M (KR dm D ΔP G b).Γ (ρAt ρ a) stR.env 1 0 selfR =
      .plain G.2.m := by
    rw [Binding.refTy_marked _ _ _ _ _ _ _ _ 0 rfl rfl]
    simp [KR, CR, selfR, RunCtx.M, codeMeaning]
    exact hG
  have h1 : Binding.refTy (KR dm D ΔP G b).dm (KR dm D ΔP G b).M (KR dm D ΔP G b).Γ (ρAt ρ a) stR.env 1 1 nB =
      .plain TyM.nat := by
    rw [Binding.refTy_unmarked _ _ _ _ _ _ _ _ rfl]; rfl
  have hv0 : ∀ ψ, Env.mean (KR dm D ΔP G b).dm (KR dm D ΔP G b).M (KR dm D ΔP G b).Γ (ρAt ρ a) ψ stR.env (.bind 1 0) =
      G.1 := mean_stR_self _
  have hv1 : ∀ ψ, Env.mean (KR dm D ΔP G b).dm (KR dm D ΔP G b).M (KR dm D ΔP G b).Γ (ρAt ρ a) ψ stR.env (.bind 1 1) =
      .el0 Nat a := mean_stR_n _
  unfold SM' MState.sstate
  simp only [stR, List.zipIdx, List.map, frR, Nat.zero_add]
  rw [show (#[{}, { binds := #[selfR, nB] }] : Env) = stR.env from rfl, h0, h1]
  simp only [List.cons.injEq, SFrame.mk.injEq, SBinding.mk.injEq, and_true, true_and]
  exact ⟨⟨funext hv0, rfl⟩, funext hv1, rfl⟩

theorem sitesOf_stR (l : Nat) : Env.sitesOf stR.env l = [] := sitesOf_envN (by simp [NVals]) l

/-- **`fixBodyAt`'s state for `R` at stage `b + 1` is the checker's start state** in the stage's context (as
`ColumnP.start_P`, with `self` the stage-`b` closure). -/
theorem start_R (hG : G.2 = .plain G.2.m) (ρ : Assignment) (fb : List PBind × PBind)
    (h1 : fb.1 = [(fun _ => .plain TyM.nat, .other)]) (h2 : fb.2.2 = .other) (a : Nat) :
    ([Sem.el0 Nat a].zip psI).foldl (fixStep fb)
        ((emptyState 0).under.pushBind { ty := .plain G.2.m, val := fun _ => G.1, decl := .pi fb.2.2 }, [], [])
      = (SM' (KR dm D ΔP G b) (ρAt ρ a) stR, [.el0 Nat a], []) := by
  have he := env_SMR (dm := dm) (D := D) (b := b) hG ρ a
  simp only [psI, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, fixStep, h1, h2,
    Bool.false_eq_true, if_false, List.length_nil, List.getElem?_cons_zero, List.nil_append, Prod.mk.injEq, and_true]
  apply ColumnI.sstate_ext
  · rw [he]; rfl
  · funext p
    show p.down?.bind (fun _ => none) = Env.shape stR.env p
    rw [shape_stR]; cases p.down? <;> rfl
  · rfl
  · funext l
    show ([] : List Site) = Env.sitesOf stR.env l
    rw [sitesOf_stR]
  · rfl
  · rfl

end

section
variable {dm : DataModel} {D : Decisions} {φ : Future}

/-- **`R`'s body inside the `.fix` clause at stage `b + 1`**, at every number `a ≤ b`, in any context of `R`'s shape
whose decisions are the checker's (`ParDecR`): `fixBodyAt` with `self` the stage-`b` closure of a function good below
`b` returns a number and no final. In world `S` the body calls `self` at `a - 1 < b`, where the stage closure gives the
function's result (`callGR`). No fact assumed: the run is computed (`runR`). -/
theorem fixBodyAt_R (hd : ParDecR D) {Δ₀ : Nat → TyS} {G₀ : Sem × TyS} {b₀ : Nat} (ρ : Assignment)
    (fb : List PBind × PBind) (h1 : fb.1 = [(fun _ => .plain TyM.nat, .other)]) (h2 : fb.2.2 = .other)
    {b : Nat} {fn : List Sem → Option BodyOut} (hgb : GoodBelow dm.read b fn) {a : Nat} (hab : a ≤ b) :
    ∃ o, fixBodyAt (KR dm D Δ₀ G₀ b₀) ρ φ fb (emptyState 0) psI outI (GR dm.read φ b fn).2.m 0 bodyR
        (GR dm.read φ b fn).1 [.el0 Nat a] = some o ∧ o.result ∈ₛ[dm.read] TyM.nat ∧ o.finals = [] := by
  have hst := start_R (dm := dm) (D := D) (b := b) (G := GR dm.read φ b fn) rfl ρ fb h1 h2 a
  have hrel := rel_stR (dm := dm) (D := D) (G := GR dm.read φ b fn) (b := b) (ρAt ρ a) φ
  have hP := refR_of_rel hrel
  have hts := tySelf_of_rel hrel
  obtain ⟨hZ, hS⟩ := runR (K := KR dm D Δ₀ G₀ b₀) (ρ := ρ) hd hP (movedIn_GR dm.read φ b fn) hts
    (GR_whole dm.read φ b fn hgb) (.inl (GR_mem hgb)) (fb.2.1 [.el0 Nat a])
  have hl : ∀ x : SState, x.liveLabels = [] → (dropN (KR dm D Δ₀ G₀ b₀) x).liveLabels = [] := fun x hx => by
    unfold dropN; rw [Strict.liveLabels_setAt]; exact hx
  have hl0 : (SM' (KR dm D ΔP (GR dm.read φ b fn) b) (ρAt ρ a) stR).liveLabels = [] := liveLabels_SMR _
  unfold fixBodyAt
  dsimp only
  rw [hst]
  dsimp only
  rw [h2, fnErasedD_other, SM.bodyRun_false]     -- main's D142: a data function
  cases a with
  | zero =>
    rw [hZ rfl]
    dsimp only
    rw [hl _ hl0]
    refine ⟨⟨.el0 Nat 0, [], none⟩, ?_, ⟨0, rfl⟩, rfl⟩
    simp [ColumnI.endsOk_nil]; rfl
  | succ a =>
    have ha : a < b := by omega
    obtain ⟨o, ho, hog, -⟩ := hgb a ha
    have hc := callGR (φ := φ) hgb ha ho (.plain TyM.nat) rfl (setN0 (KR dm D Δ₀ G₀ b₀) (SM' (KR dm D ΔP (GR dm.read φ b fn) b) (ρAt ρ (a + 1)) stR))
    rw [hS a _ rfl hc]
    dsimp only
    rw [hl _ (by unfold setN0; rw [Strict.liveLabels_setAt]; exact hl0)]
    refine ⟨⟨o.result, [], none⟩, ?_, hog.1, rfl⟩
    simp [ColumnI.endsOk_nil]; rfl

/-- The `.fix` clause's context for `R`: the stage-`0` context (as `P`'s `KP`). -/
noncomputable def K0R (dm : DataModel) (D : Decisions) (φ : Future) : RunCtx :=
  KR dm D ΔP (GR dm.read φ 0 (fun _ => none)) 0

/-- The binders and codomain the `.fix` clause reads `R`'s signature at, from the empty state. -/
noncomputable def fbR (dm : DataModel) (D : Decisions) (ρ : Assignment) (φ : Future) : List PBind × PBind :=
  (bindsOf (K0R dm D φ) ρ φ (emptyState 0) [.nat],
    fixCod (K0R dm D φ) ρ φ (emptyState 0) (bindsOf (K0R dm D φ) ρ φ (emptyState 0) [.nat]) ([.nat].map Term.isRefTy) .nat,
    (K0R dm D φ).D.typeDecl ((K0R dm D φ).D.teleDecls (scopeOf (emptyState 0)) [.nat]) .nat)

/-- **The reference's stages of `R`'s closure** (`RunCongr.fixStage` under the `.fix` clause's context). -/
noncomputable def stgR (dm : DataModel) (D : Decisions) (ρ : Assignment) (φ : Future) : Nat → List Sem → Option BodyOut :=
  fixStage (K0R dm D φ) ρ φ (fbR dm D ρ φ) 1 (emptyState 0) psI outI (some 0) 0 bodyR

theorem fbR_1 (hDR : DecTab D stR) (ρ : Assignment) : (fbR dm D ρ φ).1 = [(fun _ => .plain TyM.nat, .other)] := by
  obtain ⟨hd1, -, -, -⟩ := fixDecR hDR
  exact ColumnI.bindsOf_nat _ ρ φ _ (by show D.paramDecls [] [.nat] = [.other]; simp [Decisions.paramDecls, Decisions.teleDecls, hd1])

theorem fbR_2 (hDR : DecTab D stR) (ρ : Assignment) : (fbR dm D ρ φ).2.2 = .other := by
  obtain ⟨hd1, hd2, -, -⟩ := fixDecR hDR
  show D.typeDecl (D.teleDecls [] [.nat]) .nat = .other
  simp [Decisions.teleDecls, hd1, hd2]

/-- **The knot** (`FixKnot.stages_below` for `R`): every stage `b` of the reference's closure is good below `b`. By
induction on `b`: from stage `b` good below `b`, stage `b + 1` at a number `a ≤ b` is the body run with `self` the
stage-`b` closure (`fixStage`'s step, by definition), which `fixBodyAt_R` computes. No fact assumed. -/
theorem goodBelow_stg (hDR : DecTab D stR) (ρ : Assignment) : ∀ b, GoodBelow dm.read b (stgR dm D ρ φ b) := by
  have hd := parDecR hDR
  intro b
  induction b with
  | zero => intro m h; exact absurd h (Nat.not_lt_zero _)
  | succ b ih =>
    intro a ha
    obtain ⟨o, ho, hr, hf⟩ := fixBodyAt_R (dm := dm) (φ := φ) hd ρ (fbR dm D ρ φ) (fbR_1 hDR ρ) (fbR_2 hDR ρ) ih
      (Nat.lt_succ_iff.mp ha)
    refine ⟨o, ho, ⟨hr, fun i d hi hd' => ?_⟩, hf⟩
    rcases i with _ | i
    · simp [psI] at hi; subst hi; cases hd'
    · simp [psI] at hi

theorem capOrder_fixR : capOrder fixR = [] := rfl

/-- **`R`'s closure, as the reference's `.fix` clause forms it from the empty state**: the run succeeds at
`Π(n : Nat). Nat`, leaves the state as it was, and the closure (the guarded fixpoint of the stages) is a member of that
type, at a table aligned with the checker at `stR`. No fact assumed: membership is the knot's (`goodBelow_stg`,
`FixKnot.knot_member`'s shape through `closure_mem_of_total'`). -/
theorem column_R_run (ρ : Assignment) (hDR : DecTab D stR) (tl : Bool) (hint' : TyS) :
    ∃ f, runT (K0R dm D φ) ρ φ tl hint' fixR (emptyState 0) =
        some ((f, .plain (piTyAt dm.read 1 psI outI)), emptyState 0) ∧ f ∈ₛ[dm.read] piTyAt dm.read 1 psI outI := by
  obtain ⟨hd1, hd2, hps, hfl⟩ := fixDecR hDR
  have hpd : (K0R dm D φ).D.paramDecls (scopeOf (emptyState 0)) [.nat] = [.other] := by
    show D.paramDecls [] [.nat] = [.other]
    simp [Decisions.paramDecls, Decisions.teleDecls, hd1]
  have hsort : fixSort (K0R dm D φ) (emptyState 0) [⟨"n"⟩] [.nat] .nat = 1 := hps
  have hty : fixTy (K0R dm D φ) ρ φ (emptyState 0) [⟨"n"⟩] [.nat] .nat = piTyAt dm.read 1 psI outI := by
    unfold fixTy; rw [hsort, ColumnI.runDoms_nat _ ρ φ _ hpd, ColumnI.codOf_nat]; rfl
  have hmem : fixClo (K0R dm D φ) ρ φ (emptyState 0) [⟨"n"⟩] [.nat] .nat (some 0) bodyR ∈ₛ[dm.read]
      piTyAt dm.read 1 psI outI := by
    unfold fixClo
    rw [hty, hsort, ColumnI.runDoms_nat _ ρ φ _ hpd, ColumnI.codOf_nat]
    refine closure_mem_of_total' dm.read 1 φ psI outI _ ⟨Nat.le_refl 1, by omega⟩ rfl (fun _ _ => Nat.le_refl 1)
      fun args ha => ?_
    obtain ⟨m, rfl⟩ := domMembers_one ha
    obtain ⟨o, ho, hg, hf⟩ := goodBelow_stg (dm := dm) (φ := φ) hDR ρ (m + 1) m (Nat.lt_succ_self m)
    refine ⟨o, ?_, hg, by rw [hf]; rfl⟩
    show fixStage (K0R dm D φ) ρ φ (fbR dm D ρ φ) 1 (emptyState 0) psI outI (some 0) 0 bodyR
      (fixRank (some 0) [.el0 Nat m] + 1) [.el0 Nat m] = some o
    rw [show fixRank (some 0) [.el0 Nat m] = m from rkR_nat m]
    exact ho
  refine ⟨_, ?_, hmem⟩
  unfold fixR
  rw [run_fix_of_mem tl hint' ⟨"R"⟩ [⟨"n"⟩] [.nat] .nat (some 0) bodyR (emptyState 0) hfl
    (by rw [← fixR, capOrder_fixR]; trivial) (by rw [hty]; exact hmem), hty]
  rfl

end


/-! ## The column, at the checker's own decisions, and from the checker's acceptance -/

/-- **The column `R` at the checker's own decisions**: for every successful `checkTail` of `R`'s body from a state with
`stR`'s kernel (`checkFix`'s body state) in the plain mode with no handed-down reading, with a continuation that keeps
the counters in world `Z`, under the fuel-free table at that state (one table for the check):
(1) the reference's `.fix` clause forms `R`'s closure from the empty state, a member of `Π(n : Nat). Nat` (the knot;
this half assumes nothing);
(2) at EVERY stage `b` of that closure, the body's simulation holds in the stage's context, whose `R` is the
reference's own stage-`b` closure (`fixStage`'s `self` at stage `b + 1`), from every assignment whose entry is at most
`b`: the outer induction hypothesis the step assumed (`GoodBelow`) is discharged by the knot (`goodBelow_stg`).
For every data model, assignment, future, tail flag and hint. ASSUMES 1 fact about the checker, `SplitRInv` (for (2);
stated, guarded, unproved); no model fact. -/
theorem column_R_ff (hSp : SplitRInv) (dm : DataModel) (ρ : Assignment) (φ : Future) {fuel : Nat}
    {k : Value → Value → M Unit} (hk : KeepsAtZR k) {st st' : MState} {bh : Nat} (hkern : Kern stR st) (hm : Mode st)
    (htd : st.tailDecl = none) (h : Runs (Ochr.checkTail fuel bodyR k) st bh () st') (tl : Bool) (hint : TyS) :
    (∃ f, runT (K0R dm (checkerDecisionsFF st) φ) ρ φ tl hint fixR (emptyState 0)
        = some ((f, .plain (piTyAt dm.read 1 psI outI)), emptyState 0) ∧ f ∈ₛ[dm.read] piTyAt dm.read 1 psI outI) ∧
    ∀ (b : Nat) (Δ : Nat → TyS) (ρ' : Assignment), (∀ m, ρ' 0 = .el0 Nat m → m ≤ b) →
      TailSim (KR dm (checkerDecisionsFF st) Δ (GR dm.read φ b (stgR dm (checkerDecisionsFF st) ρ φ b)) b) ρ' φ fuel st
        bodyR k := by
  have hD : DecTab (checkerDecisionsFF st) st :=
    decTab_ff st _ (fun _ => Machine.decide_fuel_agree' _) (Machine.decide_fuel_agree' st)
  have hDR : DecTab (checkerDecisionsFF st) stR := DecTab.of_kern hkern.symm hD
  refine ⟨column_R_run ρ hDR tl hint, fun b Δ ρ' hab => ?_⟩
  exact split_simR hSp (goodBelow_stg hDR ρ b) (parDecR hDR) hk hkern hm htd ρ' hab

/-- **The column `R` from the checker's acceptance of `def R`**: where `checkDef defR` succeeds from the empty state,
there is a state of the check (the body's start) and a run of the body's check from it, such that, under the fuel-free
table there, both halves of `column_R_ff` hold. ASSUMES 2 facts about the checker: `FixRunR`, `SplitRInv`; no model
fact. -/
theorem column_R_def (hF : FixRunR) (hSp : SplitRInv) (dm : DataModel) (ρ : Assignment) (φ : Future)
    {fuel : Nat} {st₁ : MState} (hacc : Runs (checkDef defR) {} fuel () st₁) (tl : Bool) (hint : TyS) :
    ∃ (st : MState) (n : Nat) (k : Value → Value → M Unit),
      (∃ f, runT (K0R dm (checkerDecisionsFF st) φ) ρ φ tl hint fixR (emptyState 0)
        = some ((f, .plain (piTyAt dm.read 1 psI outI)), emptyState 0) ∧ f ∈ₛ[dm.read] piTyAt dm.read 1 psI outI) ∧
      ∀ (b : Nat) (Δ : Nat → TyS) (ρ' : Assignment), (∀ m, ρ' 0 = .el0 Nat m → m ≤ b) →
        TailSim (KR dm (checkerDecisionsFF st) Δ (GR dm.read φ b (stgR dm (checkerDecisionsFF st) ρ φ b)) b) ρ' φ n st
          bodyR k := by
  obtain ⟨n, k, st, st', bh, hk, hm, htd, hkz, h⟩ := hF fuel st₁ hacc
  exact ⟨st, n, k, column_R_ff hSp dm ρ φ hkz hk hm htd h tl hint⟩


end Ochr.Meaning.Steps.Form.ColumnR
