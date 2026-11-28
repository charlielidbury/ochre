import Ochr.Meaning.Steps.ColumnP
import Ochr.Meaning.Steps.RecDescAttack

/-!
# The test of the design, fault (a): `NTr`'s leaf means the number the direct run gives (spine-exp-block, lead38)

EXPERIMENTAL (`spine-exp-block`: the checker of `exp-block-text`). docs/31 D233 found the model misreading a stuck block
with no recursion at all: `NTr (n m : Nat) : Nat := match n { Z => Z, S p => let r = match m { Z => clone(n), S q =>
clone(p) }; r }` (accepted). On main its block is the closure `fix _ (n : Nat) (m : Nat) : Nat := match m { Z =>
clone(n), S _ => clone(n.0) }` applied to `(S(σ2), σ1)`; the model read it as a closure over EVERY value of its
parameters, strictly, which fails at `n = 0` (`StageBlock.step_pred_zero`, `closureL_err_of_none`), so the leaf meant
`err` where the reference's direct run gives a number.

On the experiment the block is the sealed TEXT `⌈let n = S(σ2); let m = σ1; match m { Z => clone(n), S _ => clone(n.0)
}⌉` (pinned: `textNTr_pinned`, the checker's value at `NT`'s hole, structurally). Its meaning (`meanV`'s `.sealed`
clause, the model's `.block` clause) runs the match on the captured values ONLY: **`mean_vNTr`** (kernel-checked,
standard axioms): at every assignment with `ρ σ1 = j`, `ρ σ2 = k` numbers, the text means `k + 1` if `j = 0` and `k`
otherwise; exactly the arm the reference's direct run of `NTr`'s body takes in its arm `n = S(p)` (`p = σ2`): `clone(n)`
is `k + 1`, `clone(p)` is `k`. The decisions read are the aligned table's at the text's scopes (`decNTr`, kernel
evaluation of the checker's procedures). No closure is formed and nothing is asked at other values.
-/

namespace Ochr.Meaning.Steps.Form.BlockTextNTr

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- `NTr`'s block's match over its cells (`m` innermost, `n` below it). -/
def mNTr : Term :=
  .matchNat (.var 0) (.prim "clone" [.place (.var 1)]) (.prim "clone" [.place (.proj 0 (.var 1))])

/-- `NTr`'s block's TEXT, as the experimental checker makes it. -/
def textNTr : Term :=
  .block [(⟨"n"⟩, .val (.succ (.abs 2))), (⟨"m"⟩, .val (.abs 1))] [(.other, .tNat), (.other, .tNat)] [false, false]
    .tNat mNTr

/-- The block's value: its sealed text. -/
def vNTr : Value := .sealed textNTr

/-- **Pinned**: the checker's value of `NT`'s leaf `r` (the same block as `NTr`'s) IS `vNTr`. -/
def textNTr_pinned : Bool :=
  (RecDescAtk.holes "NT").map (fun Ω => (Ω.reverse.find? (·.1 == "r")).map (·.2.2) == some vNTr) == [true]

#guard textNTr_pinned

/-! ## The decisions the text's run reads -/

/-- The scope inside the text, its two cells bound (`m` innermost). -/
abbrev scT : List DeclInfo := [.other, .other]

/-- **The decisions the model's run of `NTr`'s text reads**: the text is neither erased nor a borrow, and inside it the
match and both arms are neither statements nor proofs, and the arms move nothing (both `clone`). -/
structure DecNTr (D : Decisions) : Prop where
  fl0 : D.flags [] textNTr = (false, false)
  do0 : D.declOf [] textNTr = .other
  flM : D.flags scT mNTr = (false, false)
  flZ : D.flags scT (.prim "clone" [.place (.var 1)]) = (false, false)
  flS : D.flags scT (.prim "clone" [.place (.proj 0 (.var 1))]) = (false, false)
  jm : D.joinMoves scT [] mNTr = []

namespace Aux
open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal)
open Ochr.Meaning.Steps.Form.ColumnC.Aux (flagsRun isOther)
open Ochr.Meaning.Steps.Form.ColumnP.Aux (jmRun)
open Ochr.Meaning.Steps.Form.ColumnP (stP)

abbrev doRun (t : Term) : M DeclInfo := withLive true (Ochr.declOf 100 false [] [] t)

theorem ok_fl0 : isOk (flagsRun textNTr) (scopeState stP []) 1000 = true := by decide +kernel
theorem val_fl0 : outVal (flagsRun textNTr) (scopeState stP []) 1000 = (false, false) := by decide +kernel
theorem ok_do0 : isOk (doRun textNTr) (scopeState stP []) 1000 = true := by decide +kernel
theorem val_do0 : isOther (outVal (doRun textNTr) (scopeState stP []) 1000) = true := by decide +kernel
theorem ok_flM : isOk (flagsRun mNTr) (scopeState stP scT) 1000 = true := by decide +kernel
theorem val_flM : outVal (flagsRun mNTr) (scopeState stP scT) 1000 = (false, false) := by decide +kernel
theorem ok_flZ : isOk (flagsRun (.prim "clone" [.place (.var 1)])) (scopeState stP scT) 1000 = true := by decide +kernel
theorem val_flZ : outVal (flagsRun (.prim "clone" [.place (.var 1)])) (scopeState stP scT) 1000 = (false, false) := by
  decide +kernel
theorem ok_flS : isOk (flagsRun (.prim "clone" [.place (.proj 0 (.var 1))])) (scopeState stP scT) 1000 = true := by
  decide +kernel
theorem val_flS : outVal (flagsRun (.prim "clone" [.place (.proj 0 (.var 1))])) (scopeState stP scT) 1000 = (false, false) := by
  decide +kernel
theorem ok_jm : isOk (jmRun mNTr) (scopeState stP scT) 1000 = true := by decide +kernel
theorem val_jm0 : (outVal (jmRun mNTr) (scopeState stP scT) 1000).isEmpty = true := by decide +kernel

end Aux

/-- **`DecNTr` at every table aligned with the checker** (at `P`'s start state: any state with the prelude's `Nat`). -/
theorem decNTr {D : Decisions} (hd : DecTab D ColumnP.stP) : DecNTr D := by
  open Ochr.Meaning.Regress.GenNeutralContent in
  have hfl : ∀ sc t, isOk (ColumnC.Aux.flagsRun t) (scopeState ColumnP.stP sc) 1000 = true →
      D.flags sc t = outVal (ColumnC.Aux.flagsRun t) (scopeState ColumnP.stP sc) 1000 := fun sc t hok =>
    hd.flags 100 sc t _ 1000 _ (runs_out (ColumnC.Aux.flagsRun t) _ 1000 hok)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfl _ _ Aux.ok_fl0, Aux.val_fl0]
  · exact (hd.declOf 100 [] textNTr _ 1000 _ (runs_out (Aux.doRun textNTr) _ 1000 Aux.ok_do0)).trans
      (ColumnC.Aux.isOther_eq Aux.val_do0)
  · rw [hfl _ _ Aux.ok_flM, Aux.val_flM]
  · rw [hfl _ _ Aux.ok_flZ, Aux.val_flZ]
  · rw [hfl _ _ Aux.ok_flS, Aux.val_flS]
  · rw [hd.joinMoves 100 scT [] mNTr _ 1000 _ (runs_out (ColumnP.Aux.jmRun mNTr) _ 1000 Aux.ok_jm)]
    exact List.isEmpty_iff.mp Aux.val_jm0

/-! ## States that hold no borrow -/

section
variable {K : RunCtx} {φ : Future}

theorem live_nil_of_noShape {s : SState} (h : ∀ p, s.shape p = none) : s.liveLabels = [] := by
  unfold SState.liveLabels
  rw [List.filterMap_eq_nil_iff.mpr (fun p _ => h p)]
  simp

theorem accessOk_noShape {s : SState} (h : ∀ p, s.shape p = none) (pos : Pos) (hit : List Step → Bool) :
    AccessOk K φ s pos hit := fun k hk => by
  rw [live_nil_of_noShape h] at hk; exact absurd hk (Nat.not_lt_zero _)

theorem access_noShape {s : SState} (h : ∀ p, s.shape p = none) (pos : Pos) (hit : List Step → Bool) :
    s.access pos hit = s :=
  access_noSites (by rw [live_nil_of_noShape h]; intro l hl; cases hl)

theorem typedFuture_noShape {s : SState} (h : ∀ p, s.shape p = none) : s.typedFuture φ = φ := by
  funext l; unfold SState.typedFuture; rw [live_nil_of_noShape h]; simp

theorem dropTopOk_noShape {s : SState} (h : ∀ p, s.shape p = none) : DropTopOk K φ s := by
  unfold DropTopOk heldTop
  cases hg : s.env.getLast? with
  | none => unfold LetLendersOk; rw [hg]; trivial
  | some fr =>
    simp only [h]
    unfold LetLendersOk; rw [hg]
    exact accessOk_noShape h _ _

theorem letLenders_noShape {s : SState} (h : ∀ p, s.shape p = none) : letLenders s = s := by
  unfold letLenders; split
  · exact access_noShape h _ _
  · rfl

theorem heldTop_noShape {s : SState} (h : ∀ p, s.shape p = none) : heldTop s = none := by
  unfold heldTop; split
  · exact h _
  · rfl

theorem dropTop_noShape_eq {s : SState} (h : ∀ p, s.shape p = none) : dropTop s = s.dropLast := by
  unfold dropTop; rw [heldTop_noShape h, letLenders_noShape h]

theorem dropTop_noShape {s : SState} (h : ∀ p, s.shape p = none) (p : Pos) : (dropTop s).shape p = none := by
  rw [dropTop_noShape_eq h, SState.dropLast_shape]; split <;> simp [h]

end

/-! ## The text's run -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- The cells' runs: each embedded value at its own type, no label. -/
noncomputable def r1 (K : RunCtx) (ρ : Assignment) (φ : Future) : Res :=
  (meanV K ρ φ (.plain .err) (.succ (.abs 2)), { valT K ρ φ (.plain .err) (.succ (.abs 2)) with label := none })
noncomputable def r2 (K : RunCtx) (ρ : Assignment) (φ : Future) : Res :=
  (meanV K ρ φ (.plain .err) (.abs 1), { valT K ρ φ (.plain .err) (.abs 1) with label := none })
noncomputable def rsNTr (K : RunCtx) (ρ : Assignment) (φ : Future) : List Res := [r1 K ρ φ, r2 K ρ φ]

theorem runCells_NTr (s : SState) :
    runCells K ρ φ [(⟨"n"⟩, .val (.succ (.abs 2))), (⟨"m"⟩, .val (.abs 1))] s = some (rsNTr K ρ φ, s) := by
  simp only [runCells, Bind.bind, runT_val_def]; rfl

theorem tys_NTr : capsTys K ρ φ [(.other, .tNat), (.other, .tNat)] = [(.other, .plain TyM.nat), (.other, .plain TyM.nat)] := rfl

/-- The cells' recorded types read: `Nat`, `Nat`. -/
abbrev dNat : DeclInfo × TyS := (.other, .plain TyM.nat)

/-- The state the match runs in: the empty state with the two cells bound (`n`, then `m`). -/
noncomputable def S2 (K : RunCtx) (ρ : Assignment) (φ : Future) : SState :=
  ((emptyState 0).pushBind (cellBind (r1 K ρ φ) dNat)).pushBind (cellBind (r2 K ρ φ) dNat)

theorem S2_shape (p : Pos) : (S2 K ρ φ).shape p = none := rfl

theorem S2_scope : scopeOf (S2 K ρ φ) = scT := rfl

theorem S2_resolve0 : resolve (S2 K ρ φ) (.var 0) = some (.bind 0 1, []) := rfl
theorem S2_resolve1 : resolve (S2 K ρ φ) (.var 1) = some (.bind 0 0, []) := rfl
theorem S2_resolve10 : resolve (S2 K ρ φ) (.proj 0 (.var 1)) = some (.bind 0 0, [.proj 0]) := rfl

theorem S2_val0 (ψ : Future) : (S2 K ρ φ).valAt (.bind 0 1) ψ = ρ 1 := rfl
theorem S2_val1 (ψ : Future) : (S2 K ρ φ).valAt (.bind 0 0) ψ = (ρ 2).succ := rfl
theorem S2_ty0 : (S2 K ρ φ).tyAt (.bind 0 1) = { TyS.plain TyM.nat with label := none } := rfl
theorem S2_ty1 : (S2 K ρ φ).tyAt (.bind 0 0) = { TyS.plain TyM.nat with label := none } := rfl

theorem S2_typedFuture : (S2 K ρ φ).typedFuture φ = φ := typedFuture_noShape S2_shape
theorem S2_access (pos : Pos) (hit : List Step → Bool) : (S2 K ρ φ).access pos hit = S2 K ρ φ :=
  access_noShape S2_shape pos hit

theorem succ_el0 (k : Nat) : (Sem.el0 Nat k).succ = .el0 Nat (k + 1) := by
  show Sem.succAt natRec (.el0 Nat k) = _
  unfold Sem.succAt; rw [Sem.asNat_el0]

/-- **`clone(n)`**: `n`'s content, copied: the state unchanged, no label. -/
theorem runT_cloneN (hd : DecNTr K.D) (hint : TyS) {k : Nat} (h2 : ρ 2 = .el0 Nat k) :
    runT K ρ φ true hint (.prim "clone" [.place (.var 1)]) (S2 K ρ φ) =
      some ((.el0 Nat (k + 1), { (S2 K ρ φ).tyAt (.bind 0 0) with label := none }), S2 K ρ φ) := by
  rw [runT]
  dsimp only
  rw [S2_scope, hd.flZ]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false, SM.headOf]
  rw [SM.guarded_of (by unfold ContentOk; rw [S2_resolve1]; exact accessOk_noShape S2_shape _ _)]
  unfold readPlace contentOf
  rw [S2_resolve1]
  simp only [S2_access, S2_typedFuture, S2_val1, h2, succ_el0, Sem.follow]
  have hw : (Sem.el0 Nat (k + 1)).whole := by simp [Sem.whole]
  have hrg : ReadGood K.dm.read ((S2 K ρ φ).tyAt (.bind 0 0)).m (.el0 Nat (k + 1)) := .inl ⟨k + 1, rfl⟩
  simp only [hw, hrg, not_true_eq_false, if_false, if_true, bind, Option.bind, List.isEmpty_nil]

/-- **`clone(n.0)`**: `n`'s predecessor, copied. -/
theorem runT_cloneN0 (hd : DecNTr K.D) (hint : TyS) {k : Nat} (h2 : ρ 2 = .el0 Nat k) :
    ∃ R, R.label = none ∧ runT K ρ φ true hint (.prim "clone" [.place (.proj 0 (.var 1))]) (S2 K ρ φ) =
      some ((.el0 Nat k, R), S2 K ρ φ) := by
  rw [runT]
  dsimp only
  rw [S2_scope, hd.flS]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false, SM.headOf]
  rw [SM.guarded_of (by unfold ContentOk; rw [S2_resolve10]; exact accessOk_noShape S2_shape _ _)]
  unfold readPlace contentOf
  rw [S2_resolve10]
  simp only [S2_access, S2_typedFuture, S2_val1, h2, succ_el0]
  simp [Sem.follow, Sem.step, Sem.asNat_el0, TyS.plain]
  exact ⟨_, rfl, by simp [Sem.whole], .inl ⟨k, rfl⟩, rfl⟩

theorem S2_lentFuture : (S2 K ρ φ).lentFuture φ = φ := by
  funext l; unfold SState.lentFuture; rw [live_nil_of_noShape S2_shape]; simp

theorem S2_movedPlaces {j k : Nat} (h1 : ρ 1 = .el0 Nat j) (h2 : ρ 2 = .el0 Nat k) :
    movedPlaces φ (S2 K ρ φ) = [] := by
  have hv : ∀ i, i < 2 → ∃ pos, (S2 K ρ φ).varPos i = some pos ∧ Sem.movedIn ((S2 K ρ φ).valAt pos φ) (.var i) = [] := by
    intro i hi
    match i, hi with
    | 0, _ => exact ⟨.bind 0 1, rfl, by rw [S2_val0, h1]; rfl⟩
    | 1, _ => exact ⟨.bind 0 0, rfl, by rw [S2_val1, h2, succ_el0]; rfl⟩
  unfold movedPlaces
  show (List.range 2).flatMap _ = []
  simp only [List.flatMap_eq_nil_iff, List.mem_range]
  intro i hi
  obtain ⟨pos, hp, hm⟩ := hv i hi
  rw [hp]; dsimp only
  rw [S2_lentFuture, S2_shape]; exact hm

/-- **The match on `m`, in tail position** (no [Entry]; the join moves nothing): on `m = 0` the arm `clone(n)`, `k + 1`;
on `m = j + 1` the arm `clone(n.0)`, `k`; the state as it was. -/
theorem runT_mNTr (hd : DecNTr K.D) (hint : TyS) {j k : Nat} (h1 : ρ 1 = .el0 Nat j) (h2 : ρ 2 = .el0 Nat k) :
    ∃ R : TyS, R.label = none ∧
      runT K ρ φ true hint mNTr (S2 K ρ φ) = some ((.el0 Nat (if j = 0 then k + 1 else k), R), S2 K ρ φ) := by
  have hj : JoinDropOk K φ [] mNTr (S2 K ρ φ) ∧ joinDrop K φ [] mNTr (S2 K ρ φ) = S2 K ρ φ := by
    refine ⟨?_, ?_⟩
    · unfold JoinDropOk; rw [S2_scope, hd.jm]; trivial
    · unfold joinDrop; rw [S2_scope, hd.jm]; rfl
  have hflM := hd.flM
  unfold mNTr at hj hflM ⊢
  rw [runT]
  dsimp only
  rw [S2_scope, hflM]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  rw [SM.guarded_of (by unfold TagOk; rw [S2_resolve0]; exact accessOk_noShape S2_shape _ _)]
  unfold tagOf
  rw [S2_resolve0]
  simp only [S2_access, S2_typedFuture, S2_val0, h1]
  have hent : ∀ t s, matchEntry K φ (!true) t s = (s, fun _ s₂ => s₂) := fun t s => rfl
  have hme : ∀ t s, MatchEntryOk K φ (!true) t s := fun t s e => by cases e
  have hZ := runT_cloneN (K := K) (ρ := ρ) (φ := φ) hd hint h2
  obtain ⟨RS, hRS, hS⟩ := runT_cloneN0 (K := K) (ρ := ρ) (φ := φ) hd hint h2
  simp only [bind, Option.bind, hent, obsAt, Sem.follow, optCheck_of (hme _ _), S2_movedPlaces h1 h2, tailHint_true]
  cases j with
  | zero =>
    simp only [natTag, Sem.asNat_el0, if_true]
    rw [hZ]
    simp only [optCheck_of hj.1, hj.2]
    exact ⟨_, rfl, rfl⟩
  | succ i =>
    simp only [natTag, Sem.asNat_el0, Nat.succ_ne_zero, if_false]
    rw [hS]
    simp only [optCheck_of hj.1, hj.2]
    exact ⟨_, hRS, rfl⟩

/-- The cells are members of their recorded types (`Nat`), and hold no borrow. -/
theorem cellsOk_NTr {j k : Nat} (h1 : ρ 1 = .el0 Nat j) (h2 : ρ 2 = .el0 Nat k) :
    CellsOk K.dm.read (emptyState 0) (rsNTr K ρ φ) [dNat, dNat] := by
  have hn1 : ∀ l, (r1 K ρ φ).2.label = some l → False := fun l hl => by simp [r1] at hl
  have hn2 : ∀ l, (r2 K ρ φ).2.label = some l → False := fun l hl => by simp [r2] at hl
  refine ⟨⟨?_, ⟨fun l hl => (hn1 l hl).elim, fun l hl => (hn1 l hl).elim⟩⟩,
    ⟨⟨?_, ⟨fun l hl => (hn2 l hl).elim, fun l hl => (hn2 l hl).elim⟩⟩, trivial⟩⟩
  · show (meanV K ρ φ (.plain TyM.nat) (.abs 2)).succ ∈ₛ[K.dm.read] TyM.nat
    show (ρ 2).succ ∈ₛ[K.dm.read] TyM.nat
    rw [h2, succ_el0]; exact ⟨k + 1, rfl⟩
  · show ρ 1 ∈ₛ[K.dm.read] TyM.nat
    rw [h1]; exact ⟨j, rfl⟩

/-- **The text's run** from the empty state: the cells bound, the match's arm on the captured values, the cells
dropped; the value at `Nat`. -/
theorem runT_textNTr (hd : DecNTr K.D) (hint : TyS) {j k : Nat} (h1 : ρ 1 = .el0 Nat j) (h2 : ρ 2 = .el0 Nat k) :
    ∃ R s', runT K ρ φ false hint textNTr (emptyState 0) = some ((.el0 Nat (if j = 0 then k + 1 else k), R), s') := by
  have hfl := hd.fl0
  have hdo := hd.do0
  unfold textNTr at hfl hdo ⊢
  rw [runT]
  dsimp only
  rw [show scopeOf (emptyState 0) = [] from rfl, hfl]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  unfold SM.strictS
  dsimp only
  rw [runCells_NTr, tys_NTr, show scopeOf (emptyState 0) = [] from rfl, hdo]
  dsimp only
  rw [if_pos (cellsOk_NTr h1 h2)]
  obtain ⟨R, hR, hm⟩ := runT_mNTr (K := K) (ρ := ρ) (φ := φ) hd (.plain (meanV K ρ φ (.plain TyM.err) .tNat).asTy) h1 h2
  have hb : bindCells K φ (runT K ρ φ true (.plain (meanV K ρ φ (.plain TyM.err) .tNat).asTy) mNTr) (rsNTr K ρ φ)
      [dNat, dNat] (emptyState 0) =
      some ((.el0 Nat (if j = 0 then k + 1 else k), R), dropTop (dropTop (S2 K ρ φ))) := by
    simp only [rsNTr, bindCells]
    have e : pushBindShaped (pushBindShaped (emptyState 0) (cellBind (r1 K ρ φ) dNat)) (cellBind (r2 K ρ φ) dNat) =
        S2 K ρ φ := rfl
    rw [e, hm]
    dsimp only
    rw [if_pos (dropTopOk_noShape S2_shape)]
    dsimp only
    rw [if_pos (dropTopOk_noShape (dropTop_noShape S2_shape))]
  rw [hb]
  dsimp only
  rw [if_neg (show ¬ (isRefDecl DeclInfo.other = true) from Bool.false_ne_true)]
  rw [if_pos (show labTyOk _ R.label _ from fun l hl => by rw [hR] at hl; cases hl)]
  dsimp only
  rw [if_pos (show Sem.el0 Nat (if j = 0 then k + 1 else k) ∈ₛ[K.dm.read]
    (TyS.plain (meanV K ρ φ (.plain TyM.err) .tNat).asTy).m from ⟨_, rfl⟩)]
  exact ⟨_, _, rfl⟩

/-- **What `NTr`'s block means on the experiment** (the test of the design, fault (a); docs/31 D233): at every
assignment where `ρ σ1 = j` and `ρ σ2 = k` are numbers, the sealed text means `k + 1` when `j = 0` and `k` otherwise:
the arm the reference's direct run takes, on the captured values only. On main the same leaf meant `err` (the block's
closure asked at `n = 0`, `closureL_err_of_none`). -/
theorem mean_vNTr (hd : DecNTr K.D) (hint : TyS) {j k : Nat} (h1 : ρ 1 = .el0 Nat j) (h2 : ρ 2 = .el0 Nat k) :
    meanV K ρ φ hint vNTr = .el0 Nat (if j = 0 then k + 1 else k) := by
  obtain ⟨R, s', h⟩ := runT_textNTr (K := K) (ρ := ρ) (φ := φ) hd hint h1 h2
  show (match runT K ρ φ false hint textNTr (emptyState 0) with
    | some ((v, _), _) => v
    | none => .err) = _
  rw [h]

end

end Ochr.Meaning.Steps.Form.BlockTextNTr
