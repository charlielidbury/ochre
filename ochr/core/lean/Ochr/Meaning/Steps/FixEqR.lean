import Ochr.Meaning.Steps.ColumnR
import Ochr.Meaning.Steps.FrameRec

/-!
# `FixEqG` on `R`, kernel-checked (lead30; docs/31 D202)

The fixpoint clause of the frame property at equal selves (`Steps/FrameRec.FixEqG`), on the first recursive column
`R (n : Nat) : Nat by n := match n { Z => Z, S m => R(m) }`: the reference's function for `R` (the `.fix` clause's
`fixG` from the empty state, stage `rank + 1` at each argument) equals one run of the body with `self` the closure of
that function at the TRUE type `Π(n : Nat). Nat` (`fixBodyAt` at `piT`). At `a + 1` both apply `self` at `a`: the true
closure gives the function at `a`, stage `a + 1`; the stage-`(a + 1)` closure at the weakened type gives stage `a + 1` at
`a` too (`a < a + 1`). Assumes nothing beyond the decision table aligned with the checker at `R`'s generic call
(`DecTab D stR`, as every column).

`fixBodyAt_R_self` is `ColumnR.fixBodyAt_R` with `self` any closure that is whole, moves nothing, is a member of its
type, and whose application at the number below is known: the shape the instance needs for `self` = the true closure.
-/

namespace Ochr.Meaning.Steps.Form.ColumnR

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Ochr.Meaning.Steps.Form.ColumnI (piNat nB psI outI NoBorrow liveLabels_of_rel ρAt)
open Ochr.Meaning.Steps.Form.ColumnP (ΔP RI pn0 RefJ RefP dropN setN0)

section
variable {dm : DataModel} {D : Decisions} {φ : Future}

/-- **`R`'s body inside the `.fix` clause with any `self`** (`fixBodyAt_R` generalised): `self` a whole member of its
(unlabelled) type that moves nothing; at `0` the body returns `0`; at `a + 1` it returns what `self` applied at `a`
returns, whatever the state. No fact assumed: the run is computed (`runR`). -/
theorem fixBodyAt_R_self (hd : ParDecR D) {Δ₀ : Nat → TyS} {G₀ : Sem × TyS} {b₀ : Nat} (ρ : Assignment)
    (fb : List PBind × PBind) (h1 : fb.1 = [(fun _ => .plain TyM.nat, .other)]) (h2 : fb.2.2 = .other)
    (G : Sem × TyS) (hG : G.2 = .plain G.2.m) (hgw : G.1.whole) (hmv : ∀ q, Sem.movedIn G.1 q = [])
    (hgm : G.1 ∈ₛ[dm.read] G.2.m) :
    fixBodyAt (KR dm D Δ₀ G₀ b₀) ρ φ fb (emptyState 0) psI outI G.2.m 0 bodyR G.1 [.el0 Nat 0] =
        some ⟨.el0 Nat 0, [], none⟩ ∧
      ∀ (a : Nat) (v : Sem), (∀ s, callOf dm.read (G.1, .plain G.2.m) [(.el0 Nat a, .plain TyM.nat)] s =
          some ((v, .plain TyM.nat), s)) →
        fixBodyAt (KR dm D Δ₀ G₀ b₀) ρ φ fb (emptyState 0) psI outI G.2.m 0 bodyR G.1 [.el0 Nat (a + 1)] =
          some ⟨v, [], none⟩ := by
  have hl : ∀ x : SState, x.liveLabels = [] → (dropN (KR dm D Δ₀ G₀ b₀) x).liveLabels = [] := fun x hx => by
    unfold dropN; rw [Strict.liveLabels_setAt]; exact hx
  refine ⟨?_, fun a v hc => ?_⟩
  · have hst := start_R (dm := dm) (D := D) (b := 0) (G := G) hG ρ fb h1 h2 0
    have hrel := rel_stR (dm := dm) (D := D) (G := G) (b := 0) (ρAt ρ 0) φ
    have hP := refR_of_rel hrel
    have hts := tySelf_of_rel hrel
    obtain ⟨hZ, -⟩ := runR (K := KR dm D Δ₀ G₀ b₀) (ρ := ρ) hd hP hmv hts hgw (.inl hgm) (fb.2.1 [.el0 Nat 0])
    have hl0 : (SM' (KR dm D ΔP G 0) (ρAt ρ 0) stR).liveLabels = [] := liveLabels_SMR _
    unfold fixBodyAt
    dsimp only
    rw [hst]
    dsimp only
    rw [h2, fnErasedD_other, SM.bodyRun_false]     -- main's D142: `R` returns data
    rw [hZ rfl]
    dsimp only
    rw [hl _ hl0]
    simp [ColumnI.endsOk_nil]; rfl
  · have hst := start_R (dm := dm) (D := D) (b := 0) (G := G) hG ρ fb h1 h2 (a + 1)
    have hrel := rel_stR (dm := dm) (D := D) (G := G) (b := 0) (ρAt ρ (a + 1)) φ
    have hP := refR_of_rel hrel
    have hts := tySelf_of_rel hrel
    obtain ⟨-, hS⟩ := runR (K := KR dm D Δ₀ G₀ b₀) (ρ := ρ) hd hP hmv hts hgw (.inl hgm) (fb.2.1 [.el0 Nat (a + 1)])
    have hl0 : (SM' (KR dm D ΔP G 0) (ρAt ρ (a + 1)) stR).liveLabels = [] := liveLabels_SMR _
    unfold fixBodyAt
    dsimp only
    rw [hst]
    dsimp only
    rw [h2, fnErasedD_other, SM.bodyRun_false]     -- main's D142: `R` returns data
    rw [hS a _ rfl (hc _)]
    dsimp only
    rw [hl _ (by unfold setN0; rw [Strict.liveLabels_setAt]; exact hl0)]
    simp [ColumnI.endsOk_nil]; rfl

end

/-! ## The instance: `R`'s function is one unfolding of itself -/

section
variable {dm : DataModel} {D : Decisions} {φ : Future}

/-- `R`'s function as the `.fix` clause forms it (`fixG`): stage `rank + 1` at each argument. -/
noncomputable def gRfix (dm : DataModel) (D : Decisions) (ρ : Assignment) (φ : Future) : List Sem → Option BodyOut :=
  fun args => stgR dm D ρ φ (fixRank (some 0) args + 1) args

/-- Its closure at the TRUE type `Π(n : Nat). Nat`: the context's `R` (`GlobalsOk.fn`). -/
noncomputable def GRt (dm : DataModel) (D : Decisions) (ρ : Assignment) (φ : Future) : Sem × TyS :=
  (closureAt dm.read 1 φ psI outI (gRfix dm D ρ φ), .plain (piTyAt dm.read 1 psI outI))

theorem gRfix_tot (hDR : DecTab D stR) (ρ : Assignment) (args : List Sem) (ha : DomMembers dm.read psI args) :
    ∃ o, gRfix dm D ρ φ args = some o ∧ Steps.OutGood dm.read psI outI args o ∧
      o.finals.length = (psI.filter (·.isRef)).length := by
  obtain ⟨m, rfl⟩ := domMembers_one ha
  obtain ⟨o, ho, hg, hf⟩ := goodBelow_stg (dm := dm) (φ := φ) hDR ρ (m + 1) m (Nat.lt_succ_self m)
  refine ⟨o, ?_, hg, by rw [hf]; rfl⟩
  show stgR dm D ρ φ (fixRank (some 0) [.el0 Nat m] + 1) [.el0 Nat m] = some o
  rw [show fixRank (some 0) [.el0 Nat m] = m from rkR_nat m]
  exact ho

theorem GRt_mem (hDR : DecTab D stR) (ρ : Assignment) : (GRt dm D ρ φ).1 ∈ₛ[dm.read] (GRt dm D ρ φ).2.m :=
  closure_mem_of_total' dm.read 1 φ psI outI _ ⟨Nat.le_refl 1, by omega⟩ rfl (fun _ _ => Nat.le_refl 1)
    (gRfix_tot hDR ρ)

theorem GRt_whole (hDR : DecTab D stR) (ρ : Assignment) : (GRt dm D ρ φ).1.whole := by
  have hm := GRt_mem (dm := dm) (φ := φ) hDR ρ
  revert hm
  show closureL (lvl0 dm.read) φ (telL (lvl0 dm.read) psI [] PUnit outI).2 _ ∈ₛ[dm.read] _ →
    (closureL (lvl0 dm.read) φ (telL (lvl0 dm.read) psI [] PUnit outI).2 _).whole
  unfold closureL
  split
  · intro _; simp [Sem.whole, lvl0]
  · intro h; exact absurd h (ClosureCE.err_not_mem_pi dm.read _ _)

theorem movedIn_GRt (ρ : Assignment) (q : Place) : Sem.movedIn (GRt dm D ρ φ).1 q = [] := by
  show Sem.movedIn (closureL (lvl0 dm.read) φ (telL (lvl0 dm.read) psI [] PUnit outI).2 _) q = []
  unfold closureL
  split
  · rfl
  · simp [Sem.movedIn]

/-- The true closure applied at a number: the function's value there, the state kept. -/
theorem callGRt (hDR : DecTab D stR) (ρ : Assignment) {m : Nat} {o : BodyOut}
    (ho : gRfix dm D ρ φ [.el0 Nat m] = some o) (s : SState) :
    callOf dm.read (GRt dm D ρ φ) [(.el0 Nat m, .plain TyM.nat)] s = some ((o.result, .plain TyM.nat), s) := by
  obtain ⟨s', hs'⟩ := closure_apply' dm.read 1 φ psI outI (gRfix dm D ρ φ) ⟨Nat.le_refl 1, by omega⟩ rfl
    (fun _ _ => Nat.le_refl 1) (gRfix_tot hDR ρ) [(.el0 Nat m, .plain TyM.nat)] s o (domMembers_nat dm.read m)
    (fun i d hd => by rcases i with _ | i <;> simp [psI] at hd; subst hd; exact Nat.le_refl 1)
    trivial ho
  have hss : s' = s := ColumnJ.callOf_unlabelled_state _ _ _ _ _ _ hs' (fun a ha => by simp at ha; subst ha; rfl) rfl
  subst hss
  exact hs'

/-- **`FixEqG` on `R`, kernel-checked** (docs/31 D202): at every number, the function the `.fix` clause forms for `R`
(stage `rank + 1`) equals one run of the body with `self` its own closure at the true type. Assumes only the table
aligned with the checker at `R`'s generic call. -/
theorem fixEq_R (hDR : DecTab D stR) (ρ : Assignment) (a : Nat) :
    gRfix dm D ρ φ [.el0 Nat a] =
      fixBodyAt (K0R dm D φ) ρ φ (fbR dm D ρ φ) (emptyState 0) psI outI (piTyAt dm.read 1 psI outI) 0 bodyR
        (GRt dm D ρ φ).1 [.el0 Nat a] := by
  have hd := parDecR hDR
  have hT := fixBodyAt_R_self (dm := dm) (D := D) (φ := φ) (Δ₀ := ΔP) (G₀ := GR dm.read φ 0 (fun _ => none)) (b₀ := 0)
    hd ρ (fbR dm D ρ φ) (fbR_1 hDR ρ) (fbR_2 hDR ρ) (GRt dm D ρ φ) rfl (GRt_whole hDR ρ) (movedIn_GRt ρ) (GRt_mem hDR ρ)
  have hgb := goodBelow_stg (dm := dm) (φ := φ) hDR ρ
  have hW : ∀ b, (fixBodyAt (K0R dm D φ) ρ φ (fbR dm D ρ φ) (emptyState 0) psI outI (GR dm.read φ b (stgR dm D ρ φ b)).2.m 0 bodyR
      (GR dm.read φ b (stgR dm D ρ φ b)).1 [.el0 Nat 0] = some ⟨.el0 Nat 0, [], none⟩) ∧
      ∀ (a : Nat) (v : Sem), (∀ s, callOf dm.read ((GR dm.read φ b (stgR dm D ρ φ b)).1,
          .plain (GR dm.read φ b (stgR dm D ρ φ b)).2.m) [(.el0 Nat a, .plain TyM.nat)] s = some ((v, .plain TyM.nat), s)) →
        fixBodyAt (K0R dm D φ) ρ φ (fbR dm D ρ φ) (emptyState 0) psI outI (GR dm.read φ b (stgR dm D ρ φ b)).2.m 0 bodyR
          (GR dm.read φ b (stgR dm D ρ φ b)).1 [.el0 Nat (a + 1)] = some ⟨v, [], none⟩ := fun b =>
    fixBodyAt_R_self (dm := dm) (D := D) (φ := φ) (Δ₀ := ΔP) (G₀ := GR dm.read φ 0 (fun _ => none)) (b₀ := 0)
      hd ρ (fbR dm D ρ φ) (fbR_1 hDR ρ) (fbR_2 hDR ρ) (GR dm.read φ b (stgR dm D ρ φ b)) rfl
      (GR_whole dm.read φ b _ (hgb b)) (movedIn_GR dm.read φ b _) (GR_mem (hgb b))
  rw [show K0R dm D φ = KR dm D ΔP (GR dm.read φ 0 (fun _ => none)) 0 from rfl,
    show piTyAt dm.read 1 psI outI = (GRt dm D ρ φ).2.m from rfl]
  cases a with
  | zero =>
    rw [hT.1]
    show stgR dm D ρ φ (fixRank (some 0) [.el0 Nat 0] + 1) [.el0 Nat 0] = _
    rw [show fixRank (some 0) [.el0 Nat 0] = 0 from rkR_nat 0]
    exact (hW 0).1
  | succ a =>
    obtain ⟨o, ho, -, -⟩ := hgb (a + 1) a (Nat.lt_succ_self a)
    have ho' : gRfix dm D ρ φ [.el0 Nat a] = some o := by
      show stgR dm D ρ φ (fixRank (some 0) [.el0 Nat a] + 1) [.el0 Nat a] = some o
      rw [show fixRank (some 0) [.el0 Nat a] = a from rkR_nat a]; exact ho
    rw [hT.2 a o.result (callGRt hDR ρ ho')]
    show stgR dm D ρ φ (fixRank (some 0) [.el0 Nat (a + 1)] + 1) [.el0 Nat (a + 1)] = _
    rw [show fixRank (some 0) [.el0 Nat (a + 1)] = a + 1 from rkR_nat (a + 1)]
    exact (hW (a + 1)).2 a o.result (fun s => callGR (hgb (a + 1)) (Nat.lt_succ_self a) ho (.plain TyM.nat) rfl s)

end

end Ochr.Meaning.Steps.Form.ColumnR
