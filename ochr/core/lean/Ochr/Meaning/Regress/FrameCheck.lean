import Ochr.Meaning.Regress.CallInPlace
import Ochr.Meaning.FrameProp

/-!
# The frame property on the two concrete calls (docs/31 D70; kernel-checked)

`FrameProp.run_frame` relates a body's run in place (the callee's frame pushed on the caller's state)
with its run in the closure's own frame (the caller's frames gone, each borrow parameter's label read
back through a cell). Checked here on the two calls `Regress/CallInPlace.lean` runs both ways, for
any `self` binding (the property compares frames holding the same bindings; which `self` the closure's
meaning binds is the fixpoint's business, `callOf_inPlace`):
- `Id1 (x : &Nat) : &Nat := &*x`, called on `&y` (`y` holding `a`): the states at the call are related
  (`id1_start`), both runs give `a` at the reborrow `1` with the same type, and the states after are
  related (`id1_after`): the reborrow parked in the frame and lent at `*x` on both sides, `y` reading
  the parameter's label `0`, which the closure's cell reads.
- `Inc (x : &Nat) : Unit := *x := S(*x)`, called on `&y`: related at the call (`inc_start`), both give
  `()`, related after (`inc_after`).
-/

namespace Ochr.Meaning.Regress.FrameCheck
open Ochr Ochr.Meaning Ochr.Meaning.Regress.CallInPlace
open Classical

/-- A cell that still reads its label leaves the caller's frames as they were. -/
theorem cellFuture_self (ψ : Future) : cellFuture (fun l => l) [0] [fun ψ => ψ 0] ψ = ψ := by
  funext l
  by_cases hl : l = 0 <;> simp [cellFuture, renF, Future.updList, Future.upd, hl]

/-- A binding of the closure's frame is itself in place, under the identity renaming. -/
theorem bindRen_id (b : SBinding) : BindRen (fun l => l) b b := by
  refine ⟨?_, rfl, rfl, fun ψ => rfl⟩
  cases b with | mk ty v d rb => cases ty with | mk m lab => cases lab <;> rfl

/-- The top-frame clause where both frames hold the same bindings and the in-place one no temporary
(at the call), or one temporary after the cell (after `&*x`). -/
theorem top_same (C : SFrame) (bs : List SBinding) (ts : List SVal) :
    ∃ F F', [SFrame.mk bs ts].getLast? = some F ∧ [C, SFrame.mk bs ts].getLast? = some F' ∧ F.binds.length = F'.binds.length ∧
      (∀ (i : Nat) b b', F.binds[i]? = some b → F'.binds[i]? = some b' → BindRen (fun l => l) b b') ∧
      F'.temps.length = F.temps.length ∧
      ∀ (j : Nat) v, F.temps[j]? = some v → ∃ v', F'.temps[j]? = some v' ∧ ∀ ψ, v ψ = v' (renF (fun l => l) ψ) := by
  refine ⟨_, _, rfl, rfl, rfl, fun i b b' h h' => ?_, rfl, fun j v hv => ⟨v, hv, fun _ => rfl⟩⟩
  have h1 : bs[i]? = some b := by simpa using h
  have h2 : bs[i]? = some b' := by simpa using h'
  rw [h1] at h2; cases h2; exact bindRen_id b

theorem cellsOf_SBs (selfB : SBinding) (d : DeclInfo) (c r : Sem) : cellsOf 1 (SBs selfB d c r) = [fun ψ => ψ 0] := rfl

variable (dm : DataModel) (ρ : Assignment) (φ : Future) (selfB : SBinding) (d : DeclInfo) {r : Sem}

/-- The type `*x` is read at, on both sides. -/
def T₀ : TyS := { (xB (.el0 Nat 0) .other).ty with label := none }

theorem contentOf_SBs_eq (c : Sem) :
    contentOf (Kc dm) φ (.deref (.var 0)) (SBs selfB d c r) = some ((c, T₀, .bind 1 1, [.deref]), SBs selfB d c r) := by
  unfold contentOf
  rw [resolve_SBs]
  dsimp only
  rw [access_SBs, typedFuture_SBs]
  simp [Sem.follow, Sem.step, SState.valAt, SState.tyAt, SBs, xB, T₀]

theorem contentOf_SPg_eq (c : Sem) :
    contentOf (Kc dm) φ (.deref (.var 0)) (SPg selfB d c r) = some ((c, T₀, .bind 1 1, [.deref]), SPg selfB d c r) := by
  unfold contentOf
  rw [resolve_SPg]
  dsimp only
  rw [access_SPg, typedFuture_SPg]
  simp [Sem.follow, Sem.step, SState.valAt, SState.tyAt, SPg, xB, T₀]

/-- The reborrow's type, on both sides. -/
def T₁ : TyS := { T₀ with label := some 1 }

/-- `&*x` in the closure's frame. -/
theorem run_id1_cl (a : Nat) (hint : TyS) (tl : Bool) :
    runT (Kc dm) ρ φ tl hint id1Body (SBs selfB d (.el0 Nat a) r)
      = some ((.el0 Nat a, T₁), SB2 selfB d T₀.m (.el0 Nat a) r) := by
  simp only [id1Body, runT, SM.erasedIf, flags_Kc, Bool.false_eq_true, if_false, SM.stmtIf, SM.strictS,
    SM.guarded_of (contentOk_SBs (r := r) dm φ selfB d (.el0 Nat a))]
  unfold borrowPlace
  simp only [contentOf_SBs_eq, bind, Option.bind]
  simp [Sem.whole, SState.freshLoan, SState.tyAt, SState.valAt, SState.setAt,
    Attack.updAt_deref, Attack.updAt_nil, SState.pushTempShaped, SState.pushTemp, SState.topIdx, SState.setLent,
    SState.setHeldTy, SState.setHeldMem, SBs, SB2, xB, T₁]
  -- the strict borrow: `a` is a `Nat`, `*x`'s type
  rw [if_pos ⟨a, rfl⟩]
  dsimp only
  simp only [Attack.invalidate_noInv (Kc dm) φ (fun _ _ => rfl)]
  rw [if_pos]
  exact ⟨Attack.invalidateOk_noInv (Kc dm) φ (fun _ _ => rfl) _ _, Attack.lentOk_deref (Kc dm) φ (pos := .bind 1 1) (by simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps, SBs, SPg])⟩

/-- `&*x` in place. -/
theorem run_id1_in (a : Nat) (hint : TyS) (tl : Bool) :
    runT (Kc dm) ρ φ tl hint id1Body (SPg selfB d (.el0 Nat a) r)
      = some ((.el0 Nat a, T₁), SPg2 selfB d T₀.m (.el0 Nat a) r) := by
  simp only [id1Body, runT, SM.erasedIf, flags_Kc, Bool.false_eq_true, if_false, SM.stmtIf, SM.strictS,
    SM.guarded_of (contentOk_SPg (r := r) dm φ selfB d (.el0 Nat a))]
  unfold borrowPlace
  simp only [contentOf_SPg_eq, bind, Option.bind]
  simp [Sem.whole, SState.freshLoan, SState.tyAt, SState.valAt, SState.setAt,
    Attack.updAt_deref, Attack.updAt_nil, SState.pushTempShaped, SState.pushTemp, SState.topIdx, SState.setLent,
    SState.setHeldTy, SState.setHeldMem, SPg, SPg2, xB, T₁]
  rw [if_pos ⟨a, rfl⟩]
  dsimp only
  simp only [Attack.invalidate_noInv (Kc dm) φ (fun _ _ => rfl)]
  rw [if_pos]
  exact ⟨Attack.invalidateOk_noInv (Kc dm) φ (fun _ _ => rfl) _ _, Attack.lentOk_deref (Kc dm) φ (pos := .bind 1 1) (by simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps, SBs, SPg])⟩

/-- The caller's frame in place reads label `0` only, below the counter. -/
theorem SPg_start (c : Sem) : FrameStart (SPg selfB d c r) [0] where
  reads := fun p hp ψ ψ' h => by
    have h0 : ψ 0 = ψ' 0 := h 0 (by simp [SPg])
    rcases p with ⟨f, i⟩ | ⟨f, i⟩ <;> simp [Pos.frameOf, SState.topIdx, SPg] at hp <;> subst hp <;>
      rcases i with _ | _ | i <;> simp [SState.valAt, SPg, yFrame, h0]
  ks_lt := by simp [SPg]
  callerHeld := fun p l hp hl => by
    rcases p with ⟨f, i⟩ | ⟨f, i⟩ <;> simp [Pos.frameOf, SState.topIdx, SPg] at hp hl <;> omega
  callerLent := fun p l x hp hl => by
    rcases p with ⟨f, i⟩ | ⟨f, i⟩ <;> simp [Pos.frameOf, SState.topIdx, SPg] at hp hl <;> omega
  ks_nodup := by simp

/-- **`Id1`, at the call**: the in-place state and the closure's frame are related. -/
theorem id1_start (c : Sem) : FrameRel (fun l => l) (SPg selfB d c r) [0] (SPg selfB d c r) (SBs selfB d c r) where
  inj := fun _ _ h => h
  fresh := fun _ => rfl
  frames := ⟨rfl, rfl⟩
  lowerSkel := fun _ _ => rfl
  lowerVal := fun p _ ψ => by
    show _ = (SPg selfB d c r).valAt p (cellFuture (fun l => l) [0] (cellsOf 1 (SBs selfB d c r)) ψ)
    rw [cellsOf_SBs, cellFuture_self]
  lowerShape := fun _ _ => rfl
  top := top_same _ _ _
  topShape := fun p hp => by
    rcases p with ⟨f, i⟩ | ⟨f, i⟩ <;> simp [Pos.frameOf, SState.topIdx, SPg] at hp <;> subst hp <;>
      simp [upPos, SBs, SPg]
  clShape := fun q l hq => by
    by_cases h : q = .bind 1 1
    · exact ⟨.bind 1 1, rfl, h⟩
    · simp [SBs, h] at hq
  held := fun l hl => by
    have h0 : l = 0 := by simpa [SState.Live, liveLabels_SBs] using hl
    subst h0; simp [SPg, SBs, yB]; rfl
  lentTop := fun l x hx _ => by
    constructor
    · intro hm
      by_cases hl : l = 0
      · subst hl; simp [SPg] at hm; subst hm; simp [Pos.frameOf, SState.topIdx, SPg] at hx
      · simp [SPg, hl] at hm
    · intro hm; simp [SBs] at hm
  lentImg := fun m _ _ _ _ => ⟨m, rfl⟩
  lentCl := fun l x hx => by simp [SBs] at hx
  lentCaller := fun _ _ _ _ => rfl
  topLabels := fun l hl => by
    have h0 : l = 0 := by simpa [SState.Live, liveLabels_SBs] using hl
    simp [h0]

theorem cellsOf_SB2 (T : TyM) (c r : Sem) : cellsOf 1 (SB2 selfB d T c r) = [fun ψ => ψ 0] := rfl

/-- **`Id1`, after the body**: related again, the reborrow `1` parked and lent at `*x` on both sides. -/
theorem id1_after (T : TyM) (c c₀ : Sem) :
    FrameRel (fun l => l) (SPg selfB d c₀ r) [0] (SPg2 selfB d T c r) (SB2 selfB d T c r) where
  inj := fun _ _ h => h
  fresh := fun _ => rfl
  frames := ⟨rfl, rfl⟩
  lowerSkel := fun f hf => by
    have : f = 0 := by simp [SState.topIdx, SPg] at hf; omega
    subst this; rfl
  lowerVal := fun p hp ψ => by
    show _ = (SPg selfB d c₀ r).valAt p (cellFuture (fun l => l) [0] (cellsOf 1 (SB2 selfB d T c r)) ψ)
    rw [cellsOf_SB2, cellFuture_self]
    rcases p with ⟨f, i⟩ | ⟨f, i⟩ <;> simp [Pos.frameOf, SState.topIdx, SPg] at hp <;> subst hp <;>
      simp [SState.valAt, SPg, SPg2]
  lowerShape := fun p hp => by
    rcases p with ⟨f, i⟩ | ⟨f, i⟩ <;> simp [Pos.frameOf, SState.topIdx, SPg] at hp <;> subst hp <;>
      simp [SPg, SPg2]
  top := top_same _ _ _
  topShape := fun p hp => by
    rcases p with ⟨f, i⟩ | ⟨f, i⟩ <;> simp [Pos.frameOf, SState.topIdx, SPg] at hp <;> subst hp <;>
      rcases i with _ | _ | i <;> simp [upPos, SB2, SPg2]
  clShape := fun q l hq => by
    by_cases h1 : q = .temp 1 0
    · exact ⟨.temp 1 0, rfl, h1⟩
    · by_cases h2 : q = .bind 1 1
      · exact ⟨.bind 1 1, rfl, h2⟩
      · simp [SB2, h1, h2] at hq
  held := fun l hl => by
    have h01 : l = 0 ∨ l = 1 := by
      have := hl; simp only [SState.Live, liveLabels_SB2] at this; simpa using this
    rcases h01 with rfl | rfl <;> simp [SPg2, SB2, yB] <;> rfl
  lentTop := fun l x hx _ => by
    obtain ⟨pos, path, fill⟩ := x
    by_cases h1 : l = 1
    · subst h1
      rcases pos with ⟨f, i⟩ | ⟨f, i⟩ <;> simp [Pos.frameOf, SState.topIdx, SPg] at hx <;> subst hx <;>
        simp [SPg2, SB2, upPos]
    · by_cases h0 : l = 0
      · subst h0
        rcases pos with ⟨f, i⟩ | ⟨f, i⟩ <;> simp [Pos.frameOf, SState.topIdx, SPg] at hx <;> subst hx <;>
          simp [SPg2, SB2, upPos]
      · simp [SPg2, SB2, h1, h0]
  lentImg := fun m _ _ _ _ => ⟨m, rfl⟩
  lentCl := fun l x hx => by
    by_cases h1 : l = 1
    · subst h1; simp [SB2] at hx; subst hx; exact ⟨.bind 1 1, rfl, rfl⟩
    · simp [SB2, h1] at hx
  lentCaller := fun l p hp hl => by
    rcases p with ⟨f, i⟩ | ⟨f, i⟩ <;> simp [Pos.frameOf, SState.topIdx, SPg] at hp <;> subst hp <;> simp [SPg] at hl
  topLabels := fun l hl => by
    have h01 : l = 0 ∨ l = 1 := by
      have := hl; simp only [SState.Live, liveLabels_SB2] at this; simpa using this
    rcases h01 with rfl | rfl <;> simp [SPg]

/-- **The frame property on `Id1(&y)`**: from the related states at the call, the body runs to the
same result and related states, in place and in the closure's frame. -/
theorem id1_frame (a : Nat) (hint : TyS) (tl : Bool) :
    FrameStart (SPg selfB d (.el0 Nat a) r) [0] ∧
    FrameRel (fun l => l) (SPg selfB d (.el0 Nat a) r) [0] (SPg selfB d (.el0 Nat a) r) (SBs selfB d (.el0 Nat a) r) ∧
    ∃ res s₁ s₁', runT (Kc dm) ρ φ tl hint id1Body (SPg selfB d (.el0 Nat a) r) = some (res, s₁) ∧
      runT (Kc dm) ρ φ tl hint id1Body (SBs selfB d (.el0 Nat a) r) = some (res, s₁') ∧
      FrameRel (fun l => l) (SPg selfB d (.el0 Nat a) r) [0] s₁ s₁' :=
  ⟨SPg_start selfB d _, id1_start selfB d _, _, _, _, run_id1_in dm ρ φ selfB d a hint tl,
    run_id1_cl dm ρ φ selfB d a hint tl, id1_after selfB d _ _ _⟩

/-- **`Inc`, after the body**: the same frames, `x` holding the new content; still related (`y`
reads the parameter's label, which the cell reads). -/
theorem inc_after (c c₀ : Sem) : FrameRel (fun l => l) (SPg selfB d c₀ r) [0] (SPg selfB d c r) (SBs selfB d c r) where
  inj := fun _ _ h => h
  fresh := fun _ => rfl
  frames := ⟨rfl, rfl⟩
  lowerSkel := fun f hf => by
    have : f = 0 := by simp [SState.topIdx, SPg] at hf; omega
    subst this; rfl
  lowerVal := fun p hp ψ => by
    show _ = (SPg selfB d c₀ r).valAt p (cellFuture (fun l => l) [0] (cellsOf 1 (SBs selfB d c r)) ψ)
    rw [cellsOf_SBs, cellFuture_self]
    rcases p with ⟨f, i⟩ | ⟨f, i⟩ <;> simp [Pos.frameOf, SState.topIdx, SPg] at hp <;> subst hp <;>
      simp [SState.valAt, SPg]
  lowerShape := fun _ _ => rfl
  top := top_same _ _ _
  topShape := fun p hp => by
    rcases p with ⟨f, i⟩ | ⟨f, i⟩ <;> simp [Pos.frameOf, SState.topIdx, SPg] at hp <;> subst hp <;>
      simp [upPos, SBs, SPg]
  clShape := (id1_start selfB d c).clShape
  held := fun l hl => (id1_start (r := r) selfB d c).held l hl
  lentTop := fun l x hx hl => (id1_start (r := r) selfB d c).lentTop l x (by simpa [SState.topIdx, SPg] using hx) hl
  lentImg := fun m _ _ _ _ => ⟨m, rfl⟩
  lentCl := (id1_start selfB d c).lentCl
  lentCaller := fun _ _ _ _ => rfl
  topLabels := fun l hl => by
    have h0 : l = 0 := by simpa [SState.Live, liveLabels_SBs] using hl
    simp [h0]

/-! ## `Inc` -/

theorem readPlace_SBs (a : Nat) :
    ∃ T, readPlace (Kc dm) φ (.deref (.var 0)) true (SBs selfB d (.el0 Nat a) r)
      = some ((.el0 Nat a, T), SBs selfB d (.el0 Nat a) r) :=
  ⟨{ T₀ with label := none }, by
    have hg : ReadGood (Kc dm).dm.read T₀.m (.el0 Nat a) := Or.inl ⟨a, rfl⟩
    simp [readPlace, contentOf_SBs_eq, bind, Option.bind, Sem.whole, hg]⟩

theorem setContent_SBs (a b : Nat) :
    setContent (Kc dm) φ (.bind 1 1) [.deref] (.el0 Nat b) (SBs selfB d (.el0 Nat a) r)
      = some (⟨⟩, SBs selfB d (.el0 Nat b) r) := by
  simp [setContent, Attack.updAt_deref, Attack.updAt_nil, SState.setAt, SBs, xB, SState.valAt]

/-- `*x := S(*x)` in the closure's frame (any `self`). -/
theorem run_inc_cl (a : Nat) (hint : TyS) (tl : Bool) :
    runT (Kc dm) ρ φ tl hint incBody (SBs selfB d (.el0 Nat a) r)
      = some ((.el0 Unit (), .plain TyM.unit), SBs selfB d (.el0 Nat (a + 1)) r) := by
  obtain ⟨T', hT'⟩ := readPlace_SBs (r := r) dm φ selfB d a
  have hs : (Sem.el0 Nat a).succ = .el0 Nat (a + 1) := Sem.succ_el0 a
  simp only [incBody, runT, SM.erasedIf, SM.stmtIf, flags_Kc, copy_Kc, hT',
    Bool.false_eq_true, if_false, bind, Option.bind, pure, SM.strictS, hs,
    SM.guarded_of (contentOk_SBs (r := r) dm φ selfB d (.el0 Nat a))]
  -- the strict `S` and the strict write: `a + 1` is a `Nat`, `*x`'s type
  have hm : Sem.el0 Nat (a + 1) ∈ₛ[(Kc dm).dm.read] TyM.nat := ⟨a + 1, rfl⟩
  have hT₀ : T₀.m = TyM.nat := rfl
  simp only [hm, if_true, placeTy, contentOf_SBs_eq, hT₀, labTyOk, TyS.plain, reduceCtorEq, false_implies,
    implies_true, and_true]
  simp only [SM.guarded_of (assignOk_SBs (r := r) dm φ selfB d (.el0 Nat a)), assignAt, resolve_SBs, List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, if_false, access_SBs,
    setContent_SBs]
  simp only [Attack.invalidate_noInv (Kc dm) φ (fun _ _ => rfl)]
  rw [if_pos]
  all_goals first | rfl | exact ⟨Attack.invalidateOk_noInv (Kc dm) φ (fun _ _ => rfl) _ _, Attack.lentOk_deref (Kc dm) φ (pos := .bind 1 1) (by simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps, SBs, SPg])⟩

theorem SP_eq (cd : DeclInfo) (c : Sem) : SP dm ρ φ cd d c r = SPg (selfP dm ρ φ cd) d c r := rfl

/-- **The frame property on `Inc(&y)`**, `self` as the call in place binds it: related at the call,
the same result `()`, related after (`y` reading the parameter's label, the closure's cell reading it). -/
theorem inc_frame (cd : DeclInfo) (a : Nat) (hint : TyS) (tl : Bool) :
    FrameStart (SP dm ρ φ cd d (.el0 Nat a) r) [0] ∧
    FrameRel (fun l => l) (SP dm ρ φ cd d (.el0 Nat a) r) [0] (SP dm ρ φ cd d (.el0 Nat a) r) (SBs (selfP dm ρ φ cd) d (.el0 Nat a) r) ∧
    ∃ res s₁ s₁', runT (Kc dm) ρ φ tl hint incBody (SP dm ρ φ cd d (.el0 Nat a) r) = some (res, s₁) ∧
      runT (Kc dm) ρ φ tl hint incBody (SBs (selfP dm ρ φ cd) d (.el0 Nat a) r) = some (res, s₁') ∧
      FrameRel (fun l => l) (SP dm ρ φ cd d (.el0 Nat a) r) [0] s₁ s₁' := by
  rw [SP_eq]
  have hin := runBody_incP (r := r) dm ρ φ cd d a hint tl
  rw [SP_eq, SP_eq] at hin
  exact ⟨SPg_start _ d _, id1_start _ d _, _, _, _, hin, run_inc_cl dm ρ φ _ d a hint tl,
    inc_after (selfP dm ρ φ cd) d _ _⟩

end Ochr.Meaning.Regress.FrameCheck
