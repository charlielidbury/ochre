import Ochr.Meaning.Steps.FixEqR

/-!
# The descent clause and the knot's goodness at `R`, in the column's vocabulary (lead39, 2026-11-28; docs/31 D242)

The brief's task 4, first part: the content of `RecDescG` and of `FnGoodG` at the recursive column's function
`R (n : Nat) : Nat by n := match n { Z => Z, S m => R(m) }`, kernel-checked, in `ColumnR`'s vocabulary (`fbR`, `psI`,
`outI`, `emptyState 0`, `K0R`). Of lead38's three gaps (handoff section 38):
- (iii) the selves may have any fitting codomain while the column's lemma asked a call returning at `Nat`: DISSOLVED.
  `ColumnRRun.runR`'s successor arm takes ANY result of the call; `BodyOut` carries no type; so `fixBodyAt_R_any`
  (`fixBodyAt_R_self` with the call returning at any unlabelled type) is the same proof.
- (i) the vocabulary, and (ii) the context: NOT crossed here. `RecDescG K st` at `R` needs `fbG K …`, `psG`, `outG`,
  `lG` computed by an aligned table (`DecTab K.D stR`, the column's entry condition, as `fbR_1`, `fbR_2`, `val_piSort`
  compute them), and `fixBodyAt K …` equal to `fixBodyAt (K0R …) …` for a `K` that agrees on the data model and the table
  (`runR` is generic in `K` given `ParDecR K.D`; `start_R`, `rel_stR` are stated for `KR`).
-/

namespace Ochr.Meaning.Steps.Form.ColumnR

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Ochr.Meaning.Steps.Form.ColumnI (piNat nB psI outI NoBorrow liveLabels_of_rel ρAt)
open Ochr.Meaning.Steps.Form.ColumnP (ΔP RI pn0 RefJ RefP dropN setN0)

section
variable {dm : DataModel} {D : Decisions} {φ : Future}

/-- **`R`'s body in the `.fix` clause with any `self`, its call returning at ANY type** (gap (iii) of handoff 38):
`fixBodyAt_R_self` with the call's result at an unlabelled type `T`, not only `Nat`. The same proof: `runR`'s successor
arm takes any result. -/
theorem fixBodyAt_R_any (hd : ParDecR D) {Δ₀ : Nat → TyS} {G₀ : Sem × TyS} {b₀ : Nat} (ρ : Assignment)
    (fb : List PBind × PBind) (h1 : fb.1 = [(fun _ => .plain TyM.nat, .other)]) (h2 : fb.2.2 = .other)
    (G : Sem × TyS) (hG : G.2 = .plain G.2.m) (hgw : G.1.whole) (hmv : ∀ q, Sem.movedIn G.1 q = [])
    (hgm : G.1 ∈ₛ[dm.read] G.2.m) :
    fixBodyAt (KR dm D Δ₀ G₀ b₀) ρ φ fb (emptyState 0) psI outI G.2.m 0 bodyR G.1 [.el0 Nat 0] =
        some ⟨.el0 Nat 0, [], none⟩ ∧
      ∀ (a : Nat) (v : Sem) (T : TyS), T.label = none →
        (∀ s, callOf dm.read (G.1, .plain G.2.m) [(.el0 Nat a, .plain TyM.nat)] s = some ((v, T), s)) →
        fixBodyAt (KR dm D Δ₀ G₀ b₀) ρ φ fb (emptyState 0) psI outI G.2.m 0 bodyR G.1 [.el0 Nat (a + 1)] =
          some ⟨v, [], none⟩ := by
  have hl : ∀ x : SState, x.liveLabels = [] → (dropN (KR dm D Δ₀ G₀ b₀) x).liveLabels = [] := fun x hx => by
    unfold dropN; rw [Strict.liveLabels_setAt]; exact hx
  refine ⟨(fixBodyAt_R_self (dm := dm) (φ := φ) hd ρ fb h1 h2 G hG hgw hmv hgm).1, fun a v T hT hc => ?_⟩
  have hst := start_R (dm := dm) (D := D) (b := 0) (G := G) hG ρ fb h1 h2 (a + 1)
  have hrel := rel_stR (dm := dm) (D := D) (G := G) (b := 0) (ρAt ρ (a + 1)) φ
  have hP := refR_of_rel hrel
  have hts := tySelf_of_rel hrel
  obtain ⟨-, hS⟩ := runR (K := KR dm D Δ₀ G₀ b₀) (ρ := ρ) hd hP hmv hts hgw (.inl hgm) (fb.2.1 [.el0 Nat (a + 1)])
  have hl0 : (SM' (KR dm D ΔP G 0) (ρAt ρ (a + 1)) stR).liveLabels = [] := liveLabels_SMR _
  unfold fixBodyAt fixBodyWith
  dsimp only
  rw [hst]
  dsimp only
  rw [h2, fnErasedD_other, SM.bodyRun_false]     -- main's D142: `R` returns data
  rw [hS a _ rfl (hc _)]
  dsimp only
  rw [hl _ (by unfold setN0; rw [Strict.liveLabels_setAt]; exact hl0)]
  simp [ColumnI.endsOk_nil, hT]

end

/-! ## The selves: closures of good functions over `R`'s domain -/

section
variable {dm : DataModel} {D : Decisions} {φ : Future}

/-- A self of `R`'s kind, as `RecDescG` binds it: a closure over `R`'s domain `Nat` at a data codomain that fits level 1,
of a function defined and good (`OutGood'`) at every number. -/
structure SelfR (dm : DataModel) (out : PiCod) (g : List Sem → Option BodyOut) : Prop where
  data : out.isRef = false
  fits : ∀ args, DomMembers dm.read psI args → LevelFit 1 (out.cod args)
  tot : ∀ args, DomMembers dm.read psI args → ∃ o, g args = some o ∧ OutGood' dm.read psI out args o

theorem canon_of_fit1 {T : TyM} (h : LevelFit 1 T) : T.Canon := by
  cases T with
  | t0 _ _ => trivial
  | t1 _ _ => exact absurd h (by simp [LevelFit])
  | t2 _ _ => exact absurd h (by simp [LevelFit])

theorem SelfR.tot' {out : PiCod} {g : List Sem → Option BodyOut} (h : SelfR dm out g) :
    ∀ args, DomMembers dm.read psI args →
      ∃ o, g args = some o ∧ OutGood dm.read psI out args o ∧ o.finals.length = (psI.filter (·.isRef)).length :=
  fun args ha => by obtain ⟨o, h1, h2, -, h3⟩ := h.tot args ha; exact ⟨o, h1, h2, h3⟩

theorem SelfR.mem {out : PiCod} {g : List Sem → Option BodyOut} (h : SelfR dm out g) :
    closureAt dm.read 1 φ psI out g ∈ₛ[dm.read] piTyAt dm.read 1 psI out :=
  closure_mem_of_total' dm.read 1 φ psI out g ⟨Nat.le_refl 1, by omega⟩ h.data h.fits h.tot'

theorem SelfR.whole {out : PiCod} {g : List Sem → Option BodyOut} (h : SelfR dm out g) :
    (closureAt dm.read 1 φ psI out g).whole := by
  have hm := h.mem (φ := φ)
  revert hm
  show closureL (lvl0 dm.read) φ (telL (lvl0 dm.read) psI [] PUnit out).2 _ ∈ₛ[dm.read] _ →
    (closureL (lvl0 dm.read) φ (telL (lvl0 dm.read) psI [] PUnit out).2 _).whole
  unfold closureL
  split
  · intro _; simp [Sem.whole, lvl0]
  · intro h; exact absurd h (ClosureCE.err_not_mem_pi dm.read _ _)

theorem SelfR.movedIn (out : PiCod) (g : List Sem → Option BodyOut) (q : Place) :
    Sem.movedIn (closureAt dm.read 1 φ psI out g) q = [] := by
  show Sem.movedIn (closureL (lvl0 dm.read) φ (telL (lvl0 dm.read) psI [] PUnit out).2 _) q = []
  unfold closureL
  split
  · rfl
  · simp [Sem.movedIn]

/-- A self applied at a number is its function there, at its codomain there, the state unchanged. -/
theorem SelfR.apply {out : PiCod} {g : List Sem → Option BodyOut} (h : SelfR dm out g) (m : Nat) {o : BodyOut}
    (ho : g [.el0 Nat m] = some o) (s : SState) :
    callOf dm.read (closureAt dm.read 1 φ psI out g, .plain (piTyAt dm.read 1 psI out)) [(.el0 Nat m, .plain TyM.nat)] s =
      some ((o.result, .plain (out.cod [.el0 Nat m])), s) := by
  obtain ⟨s', hs'⟩ := closure_apply' dm.read 1 φ psI out g ⟨Nat.le_refl 1, by omega⟩ h.data h.fits h.tot'
    [(.el0 Nat m, .plain TyM.nat)] s o (domMembers_nat dm.read m)
    (fun i d hd => by rcases i with _ | i <;> simp [psI] at hd; subst hd; exact Nat.le_refl 1)
    (canon_of_fit1 (h.fits _ (domMembers_nat dm.read m))) ho
  have hss : s' = s := ColumnJ.callOf_unlabelled_state _ _ _ _ _ _ hs' (fun a ha => by simp at ha; subst ha; rfl) rfl
  subst hss
  exact hs'

/-- **`RecDescG`'s content at `R`, in the column's vocabulary** (docs/31 D242; kernel-checked): for two selves that are
closures of good functions over `R`'s domain, at any fitting data codomains, whose functions agree at every number of
rank below `a`'s, the body's runs at `a` (the `.fix` clause's `fixBodyAt`, the self bound at its own type) agree. At `0`
both return `0`; at `a + 1` both return their function at `a`, which agree. Assumes only the table aligned at `R`'s
generic call, as every column. -/
theorem recDesc_R (hDR : DecTab D stR) (ρ : Assignment) {outX outY : PiCod} {gX gY : List Sem → Option BodyOut}
    (hX : SelfR dm outX gX) (hY : SelfR dm outY gY) (a : Nat)
    (hag : ∀ bs, DomMembers dm.read psI bs → fixRank (some 0) bs < fixRank (some 0) [.el0 Nat a] → gX bs = gY bs) :
    fixBodyAt (K0R dm D φ) ρ φ (fbR dm D ρ φ) (emptyState 0) psI outI (piTyAt dm.read 1 psI outX) 0 bodyR
        (closureAt dm.read 1 φ psI outX gX) [.el0 Nat a] =
      fixBodyAt (K0R dm D φ) ρ φ (fbR dm D ρ φ) (emptyState 0) psI outI (piTyAt dm.read 1 psI outY) 0 bodyR
        (closureAt dm.read 1 φ psI outY gY) [.el0 Nat a] := by
  have hd := parDecR hDR
  have hTX := fixBodyAt_R_any (dm := dm) (D := D) (φ := φ) (Δ₀ := ΔP) (G₀ := GR dm.read φ 0 (fun _ => none)) (b₀ := 0)
    hd ρ (fbR dm D ρ φ) (fbR_1 hDR ρ) (fbR_2 hDR ρ) (closureAt dm.read 1 φ psI outX gX, .plain (piTyAt dm.read 1 psI outX))
    rfl hX.whole (SelfR.movedIn outX gX) hX.mem
  have hTY := fixBodyAt_R_any (dm := dm) (D := D) (φ := φ) (Δ₀ := ΔP) (G₀ := GR dm.read φ 0 (fun _ => none)) (b₀ := 0)
    hd ρ (fbR dm D ρ φ) (fbR_1 hDR ρ) (fbR_2 hDR ρ) (closureAt dm.read 1 φ psI outY gY, .plain (piTyAt dm.read 1 psI outY))
    rfl hY.whole (SelfR.movedIn outY gY) hY.mem
  dsimp only [TyS.plain] at hTX hTY
  rw [show K0R dm D φ = KR dm D ΔP (GR dm.read φ 0 (fun _ => none)) 0 from rfl]
  cases a with
  | zero => rw [hTX.1, hTY.1]
  | succ a =>
    obtain ⟨oX, hoX, -⟩ := hX.tot [.el0 Nat a] (domMembers_nat dm.read a)
    obtain ⟨oY, hoY, -⟩ := hY.tot [.el0 Nat a] (domMembers_nat dm.read a)
    have he : gX [.el0 Nat a] = gY [.el0 Nat a] :=
      hag _ (domMembers_nat dm.read a) (by
        rw [show fixRank (some 0) [Sem.el0 Nat a] = a from rkR_nat a,
          show fixRank (some 0) [Sem.el0 Nat (a + 1)] = a + 1 from rkR_nat (a + 1)]; omega)
    rw [hoX, hoY, Option.some.injEq] at he
    subst he
    rw [hTX.2 a oX.result _ rfl (hX.apply a hoX), hTY.2 a oX.result _ rfl (hY.apply a hoY)]

/-- **`FnGoodG`'s content at `R`, in the column's vocabulary** (docs/31 D242; kernel-checked): `R`'s function type fits
its sort (`PiFits` at level 1) and its function is defined and good at every number. -/
theorem fnGood_R (hDR : DecTab D stR) (ρ : Assignment) :
    PiFits dm.read 1 psI outI (fun _ => True) ∧
      ∀ a, DomMembers dm.read psI a → ∃ o, gRfix dm D ρ φ a = some o ∧ OutGood' dm.read psI outI a o := by
  refine ⟨?_, fun a ha => ?_⟩
  · show 0 + 1 ≤ 3 ∧ _
    exact ⟨by decide, fun _ _ _ => Nat.le_refl 1⟩
  obtain ⟨o, h1, h2, h3⟩ := gRfix_tot (dm := dm) (φ := φ) hDR ρ a ha
  exact ⟨o, h1, h2, fun h => absurd h (by simp [outI]), h3⟩

end

end Ochr.Meaning.Steps.Form.ColumnR
