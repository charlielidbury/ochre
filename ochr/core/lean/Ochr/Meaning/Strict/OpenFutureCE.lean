import Ochr.Meaning.Strict.Witness

/-!
# A good state the relation cannot tell from a checker state, on which a field write is stuck

lead7's counterexample (2026-11-21), kernel-checked on the model side. The invariant `SGood` and the
write rule's tests quantify over TYPED futures, which give each live label an OPEN member of its
recorded type (`⊥` included). The relation `Rel` compares the reference with the checker only at
futures giving each live label a WHOLE member (`TypedLive`). A position may read a live label in a
way only the open futures see.

The state `s₀`: one frame; `z : Nat` reads label `0` (`fun ψ => ψ 0`, lent at its root); `y : Nat`
holds label `0`, recorded at `Nat` with the member `0`; `x : Nat` means `1` where label `0` holds a
number and `0` elsewhere (`xv`). It is good (`s₀_good`). At every future giving label `0` a number,
`x` means `1` (`x_at_numbers`), as the checker's `x = S(Z)` does: the relation sees `1`. The strict
assignment `x.0 := c` fails (`run_stuck`): at the typed future giving label `0` the value `⊥`, `x`
means `0`, which has no predecessor.
-/

namespace Ochr.Meaning.Strict.OpenFutureCE

open Ochr Ochr.Meaning Ochr.Meaning.Strict
open Ochr.Meaning.Strict.FieldWriteCE (D₀ Kc φ₀ nat_mem)
open Ochr.Meaning.Strict.Witness (access_unreached)

open Classical

/-- `x`'s meaning: `1` where label `0` holds a number, `0` elsewhere. -/
noncomputable def xv : SVal := fun ψ => if ∃ n, ψ 0 = .el0 Nat n then .el0 Nat 1 else .el0 Nat 0

def bz : SBinding := { ty := .plain TyM.nat, val := fun ψ => ψ 0 }
def byy : SBinding := { ty := .plain TyM.nat, val := fun _ => .el0 Nat 0 }
noncomputable def bx : SBinding := { ty := .plain TyM.nat, val := xv }

def sh : Pos → Option Nat
  | .bind 0 1 => some 0
  | _ => none

/-- `z`, `y`, `x` (variables 2, 1, 0); `y` holds label `0`, lent at `z`'s root. -/
noncomputable def s₀ : SState where
  env := [{ binds := [bz, byy, bx] }]
  shape := sh
  nextLoan := 1
  lent := fun l => if l = 0 then [⟨.bind 0 0, [], false⟩] else []
  heldTy := fun _ => TyM.nat
  heldMem := fun _ => .el0 Nat 0

theorem positions_s₀ : s₀.positions = [.bind 0 0, .bind 0 1, .bind 0 2] := by
  simp [s₀, SState.positions, List.range']

theorem live_s₀ : s₀.liveLabels = [0] := by
  unfold SState.liveLabels; rw [positions_s₀]; simp [s₀, sh]

theorem sh_some {p : Pos} {l : Nat} (h : sh p = some l) : p = .bind 0 1 ∧ l = 0 := by
  unfold sh at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-- Off label `0`, nothing in `s₀` reads the future. -/
theorem valAt_s₀_indep (p : Pos) (ψ : Future) {l : Nat} (hl : l ≠ 0) (x : Sem) :
    s₀.valAt p (ψ.upd l x) = s₀.valAt p ψ := by
  have h0 : (ψ.upd l x) 0 = ψ 0 := Future.upd_other _ _ (Ne.symm hl)
  cases p with
  | bind f i =>
    rcases f with _ | f
    · rcases i with _ | _ | _ | i
      · exact h0
      · rfl
      · show xv (ψ.upd l x) = xv ψ
        unfold xv; rw [h0]
      · rfl
    · rfl
  | temp f i =>
    rcases f with _ | f
    · rfl
    · rfl

/-- **`s₀` is good.** -/
theorem s₀_good (dm : DataModel) : SGood dm [] φ₀ s₀ := by
  refine ⟨fun ψ hψ f i hp => ?_, fun ψ hψ p l hl => ?_, fun l _ => nat_mem dm 0, fun f i l hl => ?_,
    ⟨fun p ψ ψ' h => ?_, fun r x _ hs ψ ψ' _ => ?_, fun p x hp => ?_⟩, fun p l ⟨ψ, x, hne⟩ => ?_⟩
  · rw [positions_s₀] at hp
    simp only [List.mem_cons, Pos.bind.injEq, List.mem_nil_iff, or_false] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl (hψ.2 0 (by rw [live_s₀]; simp))
    · exact .inl (.mem (nat_mem dm 0))
    · show GoodVal dm [] (xv ψ) TyM.nat
      unfold xv; split
      · exact .inl (.mem (nat_mem dm 1))
      · exact .inl (.mem (nat_mem dm 0))
  · obtain ⟨rfl, rfl⟩ := sh_some hl
    exact .mem (nat_mem dm 0)
  · obtain ⟨he, rfl⟩ := sh_some hl
    cases he; rfl
  · have : ψ = ψ' := funext fun y => h y (.inl trivial)
    rw [this]
  · obtain ⟨rfl, rfl⟩ := sh_some hs
    rfl
  · obtain ⟨rfl, rfl⟩ := sh_some hp
    exact ⟨by rw [positions_s₀]; simp, by decide⟩
  · show l < 1
    by_cases hl : l = 0
    · omega
    · exact absurd (valAt_s₀_indep p ψ hl x).symm hne

/-- **What the relation sees**: at every future giving label `0` a number, `x` means `1`. -/
theorem x_at_numbers (ψ : Future) (h : ∃ n, ψ 0 = .el0 Nat n) : s₀.valAt (.bind 0 2) ψ = .el0 Nat 1 := by
  show xv ψ = _
  unfold xv; rw [if_pos h]

/-- The place `x.0`. -/
def p₀ : Place := .proj 0 (.var 0)

theorem access_s₀ (pos : Pos) (h : pos ≠ .bind 0 0) (hit : List Step → Bool) : s₀.access pos hit = s₀ := by
  refine access_unreached fun l => ?_
  unfold SState.reached
  by_cases hl : l = 0
  · subst hl; simp [s₀, Ne.symm h]
  · simp [s₀, hl]

theorem typedFuture_s₀ : s₀.typedFuture φ₀ 0 = .el0 Nat 0 := by
  show (if 0 ∈ s₀.liveLabels then s₀.heldMem 0 else φ₀ 0) = _
  rw [live_s₀]; simp [s₀]

theorem contentOf_s₀ (dm : DataModel) :
    contentOf (Kc dm) φ₀ p₀ s₀ = some ((.el0 Nat 0, { (TyS.plain TyM.nat) with label := none }, .bind 0 2, [.proj 0]), s₀) := by
  unfold contentOf
  rw [show resolve s₀ p₀ = some (.bind 0 2, [.proj 0]) from rfl]
  dsimp only
  rw [access_s₀ _ (by decide)]
  have hv : s₀.valAt (.bind 0 2) (s₀.typedFuture φ₀) = .el0 Nat 1 :=
    x_at_numbers _ ⟨0, typedFuture_s₀⟩
  have hT : s₀.tyAt (.bind 0 2) = .plain TyM.nat := rfl
  rw [hv, hT]
  simp [Sem.follow, Sem.step, Sem.asNat_el0]

theorem placeTy_s₀ (dm : DataModel) : placeTy (Kc dm) φ₀ p₀ s₀ = .plain TyM.nat := by
  unfold placeTy; rw [contentOf_s₀]; rfl

/-- The typed future giving label `0` the value `⊥`. -/
def ψbot : Future := fun l => if l = 0 then .moved else φ₀ l

theorem ψbot_typed (dm : DataModel) : TypedFut (Kc dm) φ₀ s₀ ψbot := by
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · have : l ≠ 0 := fun e => hl (by rw [e, live_s₀]; simp)
    simp [ψbot, this]
  · rw [live_s₀] at hl
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
    subst hl
    exact .moved _

/-- **The write `x.0 := 0` is undefined at `ψbot`**, so `setContent` fails. -/
theorem setContent_stuck (dm : DataModel) :
    setContent (Kc dm) φ₀ (.bind 0 2) [.proj 0] (.el0 Nat 0) s₀ = none := by
  unfold setContent
  rw [if_neg]
  intro hall
  have h := hall ψbot (ψbot_typed dm)
  have hx : s₀.valAt (.bind 0 2) ψbot = .el0 Nat 0 := by
    show xv ψbot = _
    unfold xv
    rw [if_neg]
    rintro ⟨n, hn⟩
    simp [ψbot] at hn
  have hu : Sem.updAt dm [] (.plain TyM.nat) (fun _ => .el0 Nat 0) [.proj 0] (Sem.el0 Nat 0) = none := by
    rw [Sem.updAt.eq_def]
    simp [Sem.asNat_el0]
  change (Sem.updAt dm [] (.plain TyM.nat) (fun _ => .el0 Nat 0) [.proj 0] (s₀.valAt (.bind 0 2) ψbot)).isSome = true at h
  rw [hx, hu] at h
  cases h

theorem assignAt_stuck (dm : DataModel) : assignAt (Kc dm) φ₀ p₀ (.el0 Nat 0) none s₀ = none := by
  unfold assignAt
  rw [show resolve s₀ p₀ = some (.bind 0 2, [.proj 0]) from rfl]
  dsimp only
  simp only [List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, if_false]
  rw [access_s₀ _ (by decide), setContent_stuck]

/-- **The strict assignment `x.0 := c` is stuck at the good state `s₀`**, though `x` means `1` at
every future the relation compares at (`x_at_numbers`). -/
theorem run_stuck (dm : DataModel) (ρ : Assignment) (hint : TyS) :
    runT (Kc dm) ρ φ₀ false hint (.assign p₀ (.const "c")) s₀ = none := by
  have hconst : ∀ T, runT (Kc dm) ρ φ₀ false T (.const "c") s₀ = some ((.el0 Nat 0, .plain TyM.nat), s₀) := by
    intro T; rw [runT]; rfl
  rw [runT]
  show SM.erasedIf (false, false) _ s₀ = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  simp only [hconst, Option.bind_eq_bind, Option.bind_some]
  rw [placeTy_s₀, if_pos ⟨nat_mem dm 0, fun _ h => by cases h⟩,
    show (TyS.plain TyM.nat).label = none from rfl, assignAt_stuck]

end Ochr.Meaning.Strict.OpenFutureCE
