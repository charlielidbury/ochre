import Ochr.Meaning.Steps.ColumnPSplit
import Ochr.Meaning.Steps.ColumnIRun

/-!
# The column `P`: from the checker's one split run to the closure's membership (lead16, 2026-11-21; docs/31 D131)

`def P (n : Nat) : Nat := match n { Z => Z, S m => m }`. The template is column `I` (`Steps/ColumnIRun.lean`):
the start bundles at `stP`; the body's reference run at every number `a` from the checker's start state read
as a reference state under `σ0 ↦ a`, here from the checker's ONE run of the body, which split `σ0`, through the
split's step (`ColumnPSplit.split_outZ`, `split_outS`: the world `a` falls in); `fixBodyAt`'s state equal to
that start state (`start_P`, as `start_I`); the closure a member of `Π(n : Nat). Nat`; the `.fix` run.

The decisions: one table per check (the orchestrator's ruling for lead16), the checker's at the body's start
state (`checkerDecisionsFF` of the state `checkTail` starts from); everything the reference's run of `P` reads
of it is computed by kernel evaluation of the checker's own decision procedures at `stP` (`parDecP`,
`fixDecP`).
-/

namespace Ochr.Meaning.Steps.Form.ColumnP

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Strict.Witness
open Ochr.Meaning.Steps.Form.ColumnI (piNat nB psI outI selfTy selfSem NoBorrow liveLabels_of_rel ρAt frI)

/-! ## The decisions, at a table aligned with the checker at `stP` -/

namespace Aux

open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal runs_out)
open Ochr.Meaning.Steps.Form.ColumnC.Aux (flagsRun declRun isOther isOther_eq)

abbrev pdRun (p : Place) : M DeclInfo := withLive true (Ochr.placeDecl 100 [] p)
abbrev jmRun (t : Term) : M (List Place) := withLive true (Ochr.jdMoves 100 [] [] t [])
abbrev cpRun : M Bool := Ochr.declCopy 100 .other

theorem ok_flags_body : isOk (flagsRun bodyP) (scopeState stP RI) 1000 = true := by decide +kernel
theorem val_flags_body : outVal (flagsRun bodyP) (scopeState stP RI) 1000 = (false, false) := by decide +kernel
theorem ok_flags_n0 : isOk (flagsRun (.place pn0)) (scopeState stP RI) 1000 = true := by decide +kernel
theorem val_flags_n0 : outVal (flagsRun (.place pn0)) (scopeState stP RI) 1000 = (false, false) := by decide +kernel
theorem ok_pd_n0 : isOk (pdRun pn0) (scopeState stP RI) 1000 = true := by decide +kernel
theorem val_pd_n0 : isOther (outVal (pdRun pn0) (scopeState stP RI) 1000) = true := by decide +kernel
theorem ok_pd_n : isOk (pdRun (.var 0)) (scopeState stP RI) 1000 = true := by decide +kernel
theorem val_pd_n : isOther (outVal (pdRun (.var 0)) (scopeState stP RI) 1000) = true := by decide +kernel
theorem ok_cp : isOk cpRun stP 1000 = true := by decide +kernel
theorem val_cp : outVal cpRun stP 1000 = false := by decide +kernel
theorem ok_jm : isOk (jmRun bodyP) (scopeState stP RI) 1000 = true := by decide +kernel
theorem val_jm0 : (match outVal (jmRun bodyP) (scopeState stP RI) 1000 with
    | [.var 0] => true
    | _ => false) = true := by decide +kernel
theorem val_jm : outVal (jmRun bodyP) (scopeState stP RI) 1000 = [.var 0] := by
  have h := val_jm0
  revert h
  generalize outVal (jmRun bodyP) (scopeState stP RI) 1000 = x
  intro h
  split at h
  · rfl
  · cases h

end Aux

/-- **`ParDecP` at every table aligned with the checker at `stP`.** -/
theorem parDecP {D : Decisions} (hd : DecTab D stP) : ParDecP D := by
  open Ochr.Meaning.Regress.GenNeutralContent in
  have hpd : D.placeDecl RI pn0 = .other :=
    (hd.placeDecl 100 RI pn0 _ 1000 _ (runs_out (Aux.pdRun pn0) _ 1000 Aux.ok_pd_n0)).trans
      (Ochr.Meaning.Steps.Form.ColumnC.Aux.isOther_eq Aux.val_pd_n0)
  have hpd0 : D.placeDecl RI (.var 0) = .other :=
    (hd.placeDecl 100 RI (.var 0) _ 1000 _ (runs_out (Aux.pdRun (.var 0)) _ 1000 Aux.ok_pd_n)).trans
      (Ochr.Meaning.Steps.Form.ColumnC.Aux.isOther_eq Aux.val_pd_n)
  have hcp : D.copy .other = false := by
    rw [hd.copy 100 .other _ 1000 _ (runs_out Aux.cpRun _ 1000 Aux.ok_cp), Aux.val_cp]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hd.flags 100 RI bodyP _ 1000 _ (runs_out (Ochr.Meaning.Steps.Form.ColumnC.Aux.flagsRun bodyP) _ 1000
      Aux.ok_flags_body), Aux.val_flags_body]
  · rw [hd.flags 100 RI (.place pn0) _ 1000 _ (runs_out (Ochr.Meaning.Steps.Form.ColumnC.Aux.flagsRun (.place pn0)) _ 1000
      Aux.ok_flags_n0), Aux.val_flags_n0]
  · rw [hpd]; exact hcp
  · rw [hpd0]; exact hcp
  · rw [hd.joinMoves 100 RI [] bodyP _ 1000 _ (runs_out (Aux.jmRun bodyP) _ 1000 Aux.ok_jm), Aux.val_jm]

namespace Aux

open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal)
open Ochr.Meaning.Steps.Form.ColumnC.Aux (flagsRun isOther)
open Ochr.Meaning.Steps.Form.ColumnI.Aux (typeDeclRun piSortRun)

theorem ok_td_nat (sc : List DeclInfo) (hsc : sc = [] ∨ sc = [.other]) :
    isOk (typeDeclRun .nat) (scopeState stP sc) 1000 = true := by
  rcases hsc with rfl | rfl <;> decide +kernel
theorem val_td_nat (sc : List DeclInfo) (hsc : sc = [] ∨ sc = [.other]) :
    isOther (outVal (typeDeclRun .nat) (scopeState stP sc) 1000) = true := by
  rcases hsc with rfl | rfl <;> decide +kernel
theorem ok_piSort : isOk (piSortRun (.pi [⟨"n"⟩] [.nat] .nat)) (scopeState stP []) 1000 = true := by decide +kernel
theorem val_piSort : outVal (piSortRun (.pi [⟨"n"⟩] [.nat] .nat)) (scopeState stP []) 1000 = 1 := by decide +kernel
theorem ok_flags_fix : isOk (flagsRun fixP) (scopeState stP []) 1000 = true := by decide +kernel
theorem val_flags_fix : outVal (flagsRun fixP) (scopeState stP []) 1000 = (false, false) := by decide +kernel

end Aux

/-- **The reference `.fix` clause's decisions for `P`, at the empty scope**, at every table aligned with the checker
at `stP` (as `ColumnI.fixDecI` for `I`). -/
theorem fixDecP {D : Decisions} (hd : DecTab D stP) :
    D.typeDecl [] .nat = .other ∧ D.typeDecl [.other] .nat = .other ∧ D.piSort [] (.pi [⟨"n"⟩] [.nat] .nat) = 1 ∧
      D.flags [] fixP = (false, false) := by
  open Ochr.Meaning.Regress.GenNeutralContent in
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hd.typeDecl 100 [] .nat _ 1000 _ (runs_out (ColumnI.Aux.typeDeclRun .nat) _ 1000 (Aux.ok_td_nat [] (.inl rfl)))]
    exact Ochr.Meaning.Steps.Form.ColumnC.Aux.isOther_eq (Aux.val_td_nat [] (.inl rfl))
  · rw [hd.typeDecl 100 [.other] .nat _ 1000 _
      (runs_out (ColumnI.Aux.typeDeclRun .nat) _ 1000 (Aux.ok_td_nat [.other] (.inr rfl)))]
    exact Ochr.Meaning.Steps.Form.ColumnC.Aux.isOther_eq (Aux.val_td_nat [.other] (.inr rfl))
  · rw [hd.piSort 100 [] _ _ 1000 _ (runs_out (ColumnI.Aux.piSortRun _) _ 1000 Aux.ok_piSort), Aux.val_piSort]
  · rw [hd.flags 100 [] fixP _ 1000 _ (runs_out (Ochr.Meaning.Steps.Form.ColumnC.Aux.flagsRun fixP) _ 1000 Aux.ok_flags_fix),
      Aux.val_flags_fix]

/-! ## The start bundles at `stP` -/

theorem bind_envN {v : Value} {f i : Nat} {b : Binding} (h : (envN v)[f]?.bind (fun fr => fr.binds[i]?) = some b) :
    (f = 1 ∧ i = 0 ∧ b = selfP) ∨ (f = 1 ∧ i = 1 ∧ b = { nB with val := v }) := by
  rcases f with _ | _ | f
  · simp [envN] at h
  · rcases i with _ | _ | i
    · simp [envN] at h; exact .inl ⟨rfl, rfl, h.symm⟩
    · simp [envN] at h; exact .inr ⟨rfl, rfl, h.symm⟩
    · simp [envN] at h
  · simp [envN] at h

theorem ckContent_stP {p : Place} {v : Value} (h : ckContent stP.env p = some v) : v = .gfn "P" ∨ v = .abs 0 := by
  rcases hp : p.steps with ⟨i, path⟩
  simp only [ckContent, hp] at h
  unfold ckVarPos at h
  by_cases hi : i < 2
  · have hi' : i < stP.env[stP.env.size - 1]!.binds.size := hi
    rw [if_pos hi'] at h
    simp only [Option.bind_some] at h
    have hv : ∀ w : Value, (w = .gfn "P" ∨ w = .abs 0) → w.follow path = some v → v = .gfn "P" ∨ v = .abs 0 := by
      rintro w hw hf
      cases path with
      | nil => simp [Value.follow] at hf; exact hf ▸ hw
      | cons s ss => rcases hw with rfl | rfl <;> cases s <;> simp [Value.follow, stepV] at hf
    rcases i with _ | _ | i
    · exact hv _ (.inr rfl) h
    · exact hv _ (.inl rfl) h
    · omega
  · have hi' : ¬ i < stP.env[stP.env.size - 1]!.binds.size := hi
    rw [if_neg hi'] at h; cases h

theorem refd_stP {σ : Nat} (h : stP.Refd σ) : σ < 1 := by
  refine MState.refd_lt stP 1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ σ h
  · intro v hv σ hσ; rw [stP_env, values_envN] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (Bool.false_ne_true hσ).elim
    · have := abs_hasAbs_eq hσ; omega
  · intro f i b T hb hT σ hσ; rw [stP_env] at hb
    rcases bind_envN hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfP, nB] at hT <;> subst hT <;>
      exact (Bool.false_ne_true hσ).elim
  · intro f i b P ws j hb hT; rw [stP_env] at hb
    rcases bind_envN hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfP, nB] at hT
  · intro G hG σ hσ; simp [stP] at hG; subst hG; exact (Bool.false_ne_true hσ).elim
  · intro m σ' h; simp [stP] at h
  · intro σ' v h; simp [stP] at h
  · intro σ' T h σ hσ
    rcases σ' with _ | σ'
    · simp [stP] at h; subst h; exact (Bool.false_ne_true hσ).elim
    · simp [stP] at h

theorem inv_stP (D : Decisions) : Inv D [] stP := by
  have ha : Value.abs 0 ∈ NVals := by simp [NVals]
  have hvals : ∀ v ∈ Env.values stP.env, v = .gfn "P" ∨ v = .abs 0 := fun v hv => by
    rw [stP_env, values_envN] at hv; simpa using hv
  have hpos : ∀ p ∈ allPos stP.env, p = .bind 1 0 ∨ p = .bind 1 1 := fun p hp => by
    rw [stP_env, allPos_envN] at hp; simpa using hp
  have hbind : ∀ {f i b}, stP.env[f]?.bind (fun fr => fr.binds[i]?) = some b →
      (f = 1 ∧ i = 0 ∧ b = selfP) ∨ (f = 1 ∧ i = 1 ∧ b = nB) := fun hb => bind_envN hb
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p hp; rcases hpos p hp with rfl | rfl <;> exact Bool.false_ne_true
  · intro p _ q _ l h; rw [shape_stP] at h; cases h
  · intro v hv l hl; rcases hvals v hv with rfl | rfl <;> cases hl
  · intro l; rw [stP_env, values_envN]; exact Nat.zero_le _
  · exact ⟨fun a => ⟨a, fun b ⟨p, hp, w, hw, _⟩ => by rcases hpos p hp with rfl | rfl <;> cases hw⟩⟩
  · intro v hv; rcases hvals v hv with rfl | rfl <;> exact Bool.false_ne_true
  · intro σ h; exact refd_stP h
  · intro T hT σ hσ; simp [stP] at hT; subst hT; exact (Bool.false_ne_true hσ).elim
  · intro σ r h; simp [stP] at h
  · rfl
  · intro v hv l hl; rcases hvals v hv with rfl | rfl <;> cases hl
  · intro v hv; rcases hvals v hv with rfl | rfl <;> rfl
  · intro f i b hb T hT; rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfP, nB] at hT <;> subst hT <;> rfl
  · intro T hT; simp [stP] at hT; subst hT; rfl
  · intro G hG; simp [stP] at hG; subst hG; rfl
  · intro v hv; rcases hvals v hv with rfl | rfl <;> rfl
  · intro f i b hb; rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact ⟨fun T hT l => by simp [selfP] at hT; subst hT; rfl, fun P ws j h => by simp [selfP] at h⟩
    · exact ⟨fun T hT l => by simp [nB] at hT; subst hT; rfl, fun P ws j h => by simp [nB] at h⟩
  · intro T hT l; simp [stP] at hT; subst hT; rfl
  · intro G hG l; simp [stP] at hG; subst hG; rfl
  · intro n σ h; simp [stP] at h
  · intro σ v h; simp [stP] at h
  · intro k l hk; rw [stP_env, liveLoan_envN ha] at hk; cases hk
  · intro pos path _ l hl; rw [stP_env, liveLoan_envN ha] at hl; cases hl
  · intro v hv l; rcases hvals v hv with rfl | rfl <;> rfl
  · intro v hv; rcases hvals v hv with rfl | rfl <;> rfl
  · intro p v n args _ _ h; simp at h
  · intro v hv l hl; rcases hvals v hv with rfl | rfl <;> cases hl
  · intro v hv; rcases hvals v hv with rfl | rfl <;> rfl
  · intro p _ h; rcases ckContent_stP h with h | h <;> cases h
  · intro σ r h; simp [stP] at h
  · intro σ r h; simp [stP] at h
  · intro σ l h; rcases σ with _ | σ <;> simp [stP] at h
  · intro l h; exact absurd h (occurs_envN ha stP stP_env l)

section
variable {dm : DataModel} {D : Decisions} {φ : Future}

theorem asg_stP (ρ : Assignment) (hρ : ∃ m, ρ 0 = .el0 Nat m) : Asg (KP dm D φ ΔP) ρ stP := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro σ h _
    obtain rfl : σ = 0 := by have := refd_stP h; omega
    rw [absTyM_nat _ _ (st := stP) rfl]; obtain ⟨m, hm⟩ := hρ; exact ⟨m, hm.symm⟩
  · intro n σ h; simp [stP] at h
  · intro σ v h; simp [stP] at h
  · intro σ r h; simp [stP] at h
  · intro σ h _
    obtain rfl : σ = 0 := by have := refd_stP h; omega
    rw [absTyM_nat _ _ (st := stP) rfl]; rfl
  · intro G h; simp only [MState.goalM, stP, Option.map_some, Option.some.injEq] at h; subst h; rfl
  · intro σ h _
    obtain rfl : σ = 0 := by have := refd_stP h; omega
    rfl

theorem pre_stP (ρ : Assignment) (hρ : ∃ m, ρ 0 = .el0 Nat m) : Pre (KP dm D φ ΔP) ρ stP := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [norm_stP]
  · exact ctxS_P ΔP rfl rfl
  · exact inv_stP D
  · exact asg_stP ρ hρ

theorem shape_SMP (ρ : Assignment) (p : Pos) : (SM' (KP dm D φ ΔP) ρ stP).shape p = none := by
  unfold SM'; rw [sstate_shape]; exact shape_stP p

theorem liveLabels_SMP (ρ : Assignment) : (SM' (KP dm D φ ΔP) ρ stP).liveLabels = [] := by
  unfold SState.liveLabels
  rw [List.filterMap_eq_nil_iff.mpr (fun p _ => shape_SMP ρ p), List.mergeSort_nil]

theorem rel_stP (ρ : Assignment) (φ' : Future) : Rel (KP dm D φ ΔP) ρ φ' id stP (SM' (KP dm D φ ΔP) ρ stP) :=
  Rel.start_noLive _ _ _ _ fun l h => by simp [SState.Live, liveLabels_SMP] at h

end

/-! ## The body's reference run at every number, from the checker's one run -/

section
variable {dm : DataModel} {D : Decisions} {φ : Future}

theorem ρAt_zero (ρ : Assignment) (a : Nat) : ρAt ρ a 0 = .el0 Nat a := rfl

/-- **The body's reference run at every number `a`**, from the checker's ONE successful `checkTail` of the body from a
state with `stP`'s kernel (in which `σ0` is an unknown), through the split's step at the start state read as a
reference state under `σ0 ↦ a` (`split_outP`, the world `a` falls in): the run succeeds; its result is `a - 1` at
`Nat` and it leaves no live label (the result and state identified by computing the reference run, `runP`).
ASSUMES the checker fact `SplitPInv`. -/
theorem body_runP (hSp : SplitPInv) (ρ : Assignment) (a : Nat) (hDP : DecTab D stP) {fuel : Nat}
    {k : Value → Value → M Unit} (hk : KeepsAtZ k) {st st' : MState} {bh : Nat} (hkern : Kern stP st) (hm : Mode st)
    (htd : st.tailDecl = none) (h : Runs (Ochr.checkTail fuel bodyP k) st bh () st') (hint : TyS) :
    ∃ r s', runT (KP dm D φ ΔP) (ρAt ρ a) φ true hint bodyP (SM' (KP dm D φ ΔP) (ρAt ρ a) stP) = some (r, s') ∧
      r.1 = .el0 Nat (a - 1) ∧ r.2.m = TyM.nat ∧ s'.liveLabels = [] := by
  have hpd := parDecP hDP
  have hpre : Pre (KP dm D φ ΔP) (ρAt ρ a) st := (pre_stP (ρAt ρ a) ⟨a, rfl⟩).of_kern hkern
  have hrel0 := rel_stP (dm := dm) (D := D) (φ := φ) (ρAt ρ a) φ
  obtain ⟨stl, v, T, -, ρ', Δ', π', r, s', -, hx, -⟩ :=
    split_outP hSp hpd hk hkern hm htd h hpre (hrel0.of_kern hkern) hint
  obtain ⟨hZ, hS⟩ := runP (K := KP dm D φ ΔP) hpd (refP_of_rel hrel0) (movedIn_selfSem dm.read φ) hint
  have hl : ∀ x : SState, x.liveLabels = [] → (dropN (KP dm D φ ΔP) x).liveLabels = [] := fun x hx => by
    unfold dropN; rw [Strict.liveLabels_setAt]; exact hx
  cases a with
  | zero =>
    rw [hZ (ρAt_zero ρ 0)] at hx; cases hx
    exact ⟨_, _, hZ (ρAt_zero ρ 0), rfl, rfl, hl _ (liveLabels_SMP _)⟩
  | succ b =>
    rw [hS b (ρAt_zero ρ (b + 1))] at hx; cases hx
    refine ⟨_, _, hS b (ρAt_zero ρ (b + 1)), rfl, rfl, hl _ ?_⟩
    unfold setN0; rw [Strict.liveLabels_setAt]; exact liveLabels_SMP _

/-- The body's run reads neither the assignment nor the hint (it holds no unknown; in tail position a match
hands its arms its own hint, docs/31 D156, and neither arm reads it). -/
theorem runT_bodyP (K : RunCtx) (ρ ρ' : Assignment) (h h' : TyS) (s : SState) :
    runT K ρ φ true h bodyP s = runT K ρ' φ true h' bodyP s := by
  show runT K ρ φ true h (.matchNat (.var 0) .zero (.place pn0)) s =
    runT K ρ' φ true h' (.matchNat (.var 0) .zero (.place pn0)) s
  have e1 : runT K ρ φ true (tailHint true h) .zero = runT K ρ' φ true (tailHint true h') .zero :=
    funext fun s => by rw [runT, runT]
  have e2 : runT K ρ φ true (tailHint true h) (.place pn0) = runT K ρ' φ true (tailHint true h') (.place pn0) :=
    funext fun s => by rw [runT, runT]
  conv => lhs; rw [runT]
  conv => rhs; rw [runT]
  rw [e1, e2]

/-- **The checker's start state, read as a reference state** under `σ0 ↦ a`: the frames `[{}, frI]`, as for `I`. -/
theorem env_SMP (ρ : Assignment) (a : Nat) : (SM' (KP dm D φ ΔP) (ρAt ρ a) stP).env = [{}, frI dm.read φ a] := by
  have h0 : Binding.refTy (KP dm D φ ΔP).dm (KP dm D φ ΔP).M (KP dm D φ ΔP).Γ (ρAt ρ a) stP.env 1 0 selfP =
      .plain (selfTy dm.read) := by
    rw [Binding.refTy_marked _ _ _ _ _ _ _ _ 0 rfl rfl]
    simp [KP, CP, selfP, RunCtx.M, codeMeaning]
  have h1 : Binding.refTy (KP dm D φ ΔP).dm (KP dm D φ ΔP).M (KP dm D φ ΔP).Γ (ρAt ρ a) stP.env 1 1 nB = .plain TyM.nat := by
    rw [Binding.refTy_unmarked _ _ _ _ _ _ _ _ rfl]; rfl
  have hv0 : ∀ ψ, Env.mean (KP dm D φ ΔP).dm (KP dm D φ ΔP).M (KP dm D φ ΔP).Γ (ρAt ρ a) ψ stP.env (.bind 1 0) =
      selfSem dm.read φ := mean_stP_self _
  have hv1 : ∀ ψ, Env.mean (KP dm D φ ΔP).dm (KP dm D φ ΔP).M (KP dm D φ ΔP).Γ (ρAt ρ a) ψ stP.env (.bind 1 1) =
      .el0 Nat a := mean_stP_n _
  unfold SM' MState.sstate
  simp only [stP, List.zipIdx, List.map, frI, Nat.zero_add]
  rw [show (#[{}, { binds := #[selfP, nB] }] : Env) = stP.env from rfl, h0, h1]
  simp only [List.cons.injEq, SFrame.mk.injEq, SBinding.mk.injEq, and_true, true_and]
  exact ⟨⟨funext hv0, rfl⟩, funext hv1, rfl⟩

theorem sitesOf_stP (l : Nat) : Env.sitesOf stP.env l = [] := sitesOf_envN (by simp [NVals]) l

/-- **`fixBodyAt`'s state for `P` is the checker's start state** (as `ColumnI.start_I`). -/
theorem start_P (ρ : Assignment) (fb : List PBind × PBind) (h1 : fb.1 = [(fun _ => .plain TyM.nat, .other)])
    (h2 : fb.2.2 = .other) (a : Nat) :
    ([Sem.el0 Nat a].zip psI).foldl (fixStep fb)
        ((emptyState 0).under.pushBind { ty := .plain (selfTy dm.read), val := fun _ => selfSem dm.read φ, decl := .pi fb.2.2 }, [], [])
      = (SM' (KP dm D φ ΔP) (ρAt ρ a) stP, [.el0 Nat a], []) := by
  have he := env_SMP (dm := dm) (D := D) (φ := φ) ρ a
  simp only [psI, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, fixStep, h1, h2,
    Bool.false_eq_true, if_false, List.length_nil, List.getElem?_cons_zero, List.nil_append, Prod.mk.injEq, and_true]
  apply ColumnI.sstate_ext
  · rw [he]; rfl
  · funext p
    show p.down?.bind (fun _ => none) = Env.shape stP.env p
    rw [shape_stP]; cases p.down? <;> rfl
  · rfl
  · funext l
    show ([] : List Site) = Env.sitesOf stP.env l
    rw [sitesOf_stP]
  · rfl
  · rfl

/-- **`P`'s body run inside the `.fix` clause**, at every number `a`: `fixBodyAt` returns `a - 1` and no final,
from the checker's one run of the body. ASSUMES `SplitPInv`. -/
theorem fixBodyAt_P (hSp : SplitPInv) (ρ : Assignment) (fb : List PBind × PBind)
    (h1 : fb.1 = [(fun _ => .plain TyM.nat, .other)]) (h2 : fb.2.2 = .other) (hDP : DecTab D stP) {fuel : Nat}
    {k : Value → Value → M Unit} (hk : KeepsAtZ k) {st st' : MState} {bh : Nat} (hkern : Kern stP st) (hm : Mode st)
    (htd : st.tailDecl = none) (h : Runs (Ochr.checkTail fuel bodyP k) st bh () st') (a : Nat) :
    ∃ o, fixBodyAt (KP dm D φ ΔP) ρ φ fb (emptyState 0) psI outI (selfTy dm.read) 0 bodyP (selfSem dm.read φ)
        [.el0 Nat a] = some o ∧ o.result = .el0 Nat (a - 1) ∧ o.finals = [] := by
  obtain ⟨r, s', hr, hr1, -, hl⟩ := body_runP (dm := dm) (φ := φ) hSp ρ a hDP hk hkern hm htd h (fb.2.1 [.el0 Nat a])
  refine ⟨⟨r.1, [], r.2.label⟩, ?_, hr1, rfl⟩
  unfold fixBodyAt
  dsimp only
  rw [start_P (dm := dm) (D := D) (φ := φ) ρ fb h1 h2 a]
  dsimp only
  rw [runT_bodyP (KP dm D φ ΔP) ρ (ρAt ρ a) (fb.2.1 [.el0 Nat a]) (fb.2.1 [.el0 Nat a]), hr]
  dsimp only
  rw [hl]
  simp [ColumnI.endsOk_nil]

theorem capOrder_fixP : capOrder fixP = [] := rfl

/-- **`P`'s closure, as the reference's `.fix` clause forms it from the empty state**: the run succeeds at
`Π(n : Nat). Nat`, leaves the state as it was, and the closure is a member of that type. From the checker's one
successful run of the body, at a table aligned with the checker at `stP`. ASSUMES `SplitPInv`. -/
theorem column_P_run (hSp : SplitPInv) (ρ : Assignment) (hDP : DecTab D stP) {fuel : Nat} {k : Value → Value → M Unit}
    (hk : KeepsAtZ k) {st st' : MState} {bh : Nat} (hkern : Kern stP st) (hm : Mode st) (htd : st.tailDecl = none)
    (h : Runs (Ochr.checkTail fuel bodyP k) st bh () st') (tl : Bool) (hint' : TyS) :
    ∃ f, runT (KP dm D φ ΔP) ρ φ tl hint' fixP (emptyState 0) =
        some ((f, .plain (piTyAt dm.read 1 psI outI)), emptyState 0) ∧ f ∈ₛ[dm.read] piTyAt dm.read 1 psI outI := by
  obtain ⟨hd1, hd2, hps, hfl⟩ := fixDecP hDP
  have hpd : (KP dm D φ ΔP).D.paramDecls (scopeOf (emptyState 0)) [.nat] = [.other] := by
    show D.paramDecls [] [.nat] = [.other]
    simp [Decisions.paramDecls, Decisions.teleDecls, hd1]
  have hsort : fixSort (KP dm D φ ΔP) (emptyState 0) [⟨"n"⟩] [.nat] .nat = 1 := hps
  have h1 : bindsOf (KP dm D φ ΔP) ρ φ (emptyState 0) [.nat] = [(fun _ => .plain TyM.nat, .other)] :=
    ColumnI.bindsOf_nat _ ρ φ _ hpd
  have h2 : (KP dm D φ ΔP).D.typeDecl ((KP dm D φ ΔP).D.teleDecls (scopeOf (emptyState 0)) [.nat]) .nat = .other := by
    show D.typeDecl (D.teleDecls [] [.nat]) .nat = .other
    simp [Decisions.teleDecls, hd1, hd2]
  have hty : fixTy (KP dm D φ ΔP) ρ φ (emptyState 0) [⟨"n"⟩] [.nat] .nat = piTyAt dm.read 1 psI outI := by
    unfold fixTy; rw [hsort, ColumnI.runDoms_nat _ ρ φ _ hpd, ColumnI.codOf_nat]; rfl
  have hmem : fixClo (KP dm D φ ΔP) ρ φ (emptyState 0) [⟨"n"⟩] [.nat] .nat none bodyP ∈ₛ[dm.read]
      piTyAt dm.read 1 psI outI := by
    unfold fixClo
    rw [hty, hsort, ColumnI.runDoms_nat _ ρ φ _ hpd, ColumnI.codOf_nat]
    refine fixClo_mem_nonrec _ 1 (emptyState 0) psI outI _ 0 bodyP ⟨Nat.le_refl 1, by omega⟩ rfl
      (fun _ _ => Nat.le_refl 1) fun args ha => ?_
    obtain ⟨hlen, hargs⟩ := ha
    match args, hlen with
    | [x], _ =>
      obtain ⟨m, hx⟩ := hargs 0 x _ rfl rfl
      subst hx
      obtain ⟨o, ho, hr, hf⟩ := fixBodyAt_P (dm := dm) (D := D) (φ := φ) hSp ρ
        (bindsOf (KP dm D φ ΔP) ρ φ (emptyState 0) [.nat],
          fixCod (KP dm D φ ΔP) ρ φ (emptyState 0) (bindsOf (KP dm D φ ΔP) ρ φ (emptyState 0) [.nat]) .nat,
          (KP dm D φ ΔP).D.typeDecl ((KP dm D φ ΔP).D.teleDecls (scopeOf (emptyState 0)) [.nat]) .nat) h1 h2 hDP hk
        hkern hm htd h m
      refine ⟨o, ho, ⟨?_, fun i d hi hd => ?_⟩, by rw [hf]; rfl⟩
      · rw [hr]; exact ⟨m - 1, rfl⟩
      · rcases i with _ | i
        · simp [psI] at hi; subst hi; cases hd
        · simp [psI] at hi
  refine ⟨_, ?_, hmem⟩
  unfold fixP
  rw [run_fix_of_mem tl hint' ⟨"P"⟩ [⟨"n"⟩] [.nat] .nat none bodyP (emptyState 0) hfl
    (by rw [← fixP, capOrder_fixP]; trivial) (by rw [hty]; exact hmem), hty]
  rfl

end

/-! ## The column, at the checker's own decisions, and from the checker's acceptance -/

/-- **The column `P` at the checker's own decisions**: for every successful `checkTail` of `P`'s body from a state with
`stP`'s kernel (`checkFix`'s body state) in the plain mode with no handed-down reading, with a continuation that keeps
the counters in world `Z`, the reference's `.fix` clause, under the fuel-free table at that state (one table for the
check), forms `P`'s closure from the empty state: the run succeeds at `Π(n : Nat). Nat` and the closure is a member of
it; for every data model, assignment, future, tail flag and hint. ASSUMES 1 fact about the checker, `SplitPInv`
(stated, guarded, unproved); no model fact. -/
theorem column_P_ff (hSp : SplitPInv) (dm : DataModel) (ρ : Assignment) (φ : Future) {fuel : Nat}
    {k : Value → Value → M Unit} (hk : KeepsAtZ k) {st st' : MState} {bh : Nat} (hkern : Kern stP st) (hm : Mode st)
    (htd : st.tailDecl = none) (h : Runs (Ochr.checkTail fuel bodyP k) st bh () st') (tl : Bool) (hint : TyS) :
    ∃ f, runT (KP dm (checkerDecisionsFF st) φ ΔP) ρ φ tl hint fixP (emptyState 0)
        = some ((f, .plain (piTyAt dm.read 1 psI outI)), emptyState 0) ∧ f ∈ₛ[dm.read] piTyAt dm.read 1 psI outI := by
  have hD : DecTab (checkerDecisionsFF st) st :=
    decTab_ff st _ (fun _ => Machine.decide_fuel_agree' _) (Machine.decide_fuel_agree' st)
  exact column_P_run hSp ρ (DecTab.of_kern hkern.symm hD) hk hkern hm htd h tl hint

/-- **The checker's acceptance of `P`, inverted down to its body's check** (a fact about the checker, assumed; the
machine lane's to prove): where `checkDef defP` succeeds from the empty state, `checkFix` ran `checkTail` of the body
(with its return check as the continuation) from a state with `stP`'s kernel, in the plain mode, with no handed-down
reading, and that continuation keeps the counters in world `Z`. Guarded below by `checkDef defP`'s derivation (the
goal, the two worlds in order, world `S`'s fresh unknown `σ1`: world `Z`'s return check named no unknown, the joins,
the two path ends); the start state's kernel is `ParGuards`' (`kernelOk`, recorded at the entry of a body with `P`'s
signature, independent of the body). -/
def FixRunP : Prop :=
  ∀ (fuel : Nat) (st₁ : MState), Runs (checkDef ParGuards.defP) {} fuel () st₁ →
    ∃ (n : Nat) (k : Value → Value → M Unit) (st st' : MState) (bh : Nat),
      Kern stP st ∧ Mode st ∧ st.tailDecl = none ∧ KeepsAtZ k ∧ Runs (Ochr.checkTail n bodyP k) st bh () st'

namespace Guards

/-- The trace of `checkDef defP` from the empty state. -/
def linesOfP (cfg : Config) : List String :=
  match runMachine (checkDef ParGuards.defP) { cfg := cfg } 100000 with
  | (_, _, log) => log.toList.filterMap fun | .line s => some s | _ => none

#guard linesOfP { trace := true } == ["[Def] P: goal Nat", "[Split] σ0 := 0",
  "[Def] P: path ends with type Nat against goal Nat", "[Split] σ0 := S σ1",
  "[Def] P: path ends with type Nat against goal Nat"]
#guard linesOfP { trace := true, derivation := true } == ["[Def] P: goal Nat", "[Split] σ0 := 0", "[Join] n dropped",
  "[Return] P returns it: 0 : Nat, with 0 place(s) held by borrow", "[Def] P: path ends with type Nat against goal Nat",
  "[Split] σ0 := S σ1", "[Read] its declared type is not a copy type: moved out", "[Join] n dropped",
  "[Return] P returns it: σ1 : Nat, with 0 place(s) held by borrow",
  "[Def] P: path ends with type Nat against goal Nat"]

end Guards

/-- **The column `P` from the checker's acceptance of `def P`**: where `checkDef defP` succeeds from the empty state,
there is a state of the check (the body's start, `st`) such that, under the fuel-free table there, the reference forms
`P`'s closure from the empty state, a member of `Π(n : Nat). Nat`. ASSUMES 2 facts about the checker: `FixRunP`,
`SplitPInv`; no model fact. -/
theorem column_P_def (hF : FixRunP) (hSp : SplitPInv) (dm : DataModel) (ρ : Assignment) (φ : Future)
    {fuel : Nat} {st₁ : MState} (hacc : Runs (checkDef ParGuards.defP) {} fuel () st₁) (tl : Bool) (hint : TyS) :
    ∃ st : MState, ∃ f, runT (KP dm (checkerDecisionsFF st) φ ΔP) ρ φ tl hint fixP (emptyState 0)
        = some ((f, .plain (piTyAt dm.read 1 psI outI)), emptyState 0) ∧ f ∈ₛ[dm.read] piTyAt dm.read 1 psI outI := by
  obtain ⟨n, k, st, st', bh, hk, hm, htd, hkz, h⟩ := hF fuel st₁ hacc
  exact ⟨st, column_P_ff hSp dm ρ φ hkz hk hm htd h tl hint⟩

end Ochr.Meaning.Steps.Form.ColumnP
