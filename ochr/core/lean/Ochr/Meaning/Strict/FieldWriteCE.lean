import Ochr.Meaning.Strict.Comb
import Ochr.Meaning.BotWrite

/-!
# A write below a part read from a live label is `err` at some typed future (kernel-checked)

`setContent pos steps v` writes, at every future `φ'`, `Sem.updAt … steps (old φ')`, and `err` where
that update fails (`getD .err`); the run checks only that it succeeds at the state's typed future
(`SState.typedFuture`: each live label its record). A position whose value READS a live label at a
strict prefix of `steps` has, at the typed futures that give the label another open member (`⊥`, or
another number), a value the path does not enter, so the write leaves `err` there, which is no open
member of anything. `SGood` says nothing that excludes such a position: it does not tie a position's
reads of live labels to the sites [Access] ends (`SState.lent`), so the [Access] before the write
need not end the label.

The state `s₀`: one frame, `x₀ : Nat` reading label `0` whole (`fun ψ => ψ 0`, the lender, with no
site recorded), `x₁ : Nat` holding `0` (`1`), `heldTy 0 = Nat`, `heldMem 0 = 1`. It is good
(`s₀_good`). Moving out `x₀.0` (the predecessor; `setContent … [.0] ⊥`) succeeds (at the typed
future `x₀` reads `1`, whose predecessor is moved out: `S(⊥)`), and leaves `x₀` reading `err` at the
typed future giving label `0` the number `0` (`s₁_bad`). So `OpsPlace.setContent_field_moved_sgood`
is false as stated (`not_setContent_field_moved_sgood`), and with it every lemma that writes at a
field path from a good state alone (the read's move, the join's drop, D112's invalidation).
-/

namespace Ochr.Meaning.Strict.FieldWriteCE

open Ochr Ochr.Meaning

/-- The decisions: nothing a statement or a proof, nothing copied, nothing invalidated. -/
def D₀ : Decisions where
  flags _ _ := (false, false)
  placeDecl _ _ := .other
  declOf _ _ := .other
  copy _ := false
  piSort _ _ := 1
  joinMoves _ _ _ := []
  rePointed _ _ := []
  typeDecl _ _ := .other

/-- A run context at any data model, nothing declared, every global the number `0`. -/
def Kc (dm : DataModel) : RunCtx where
  dm := dm
  Γ := []
  C := { global := fun _ => (.el0 Nat 0, .plain TyM.nat), sealed := fun _ _ _ _ => .err, clo := fun _ _ _ _ _ => .err,
         pi := fun _ _ _ _ _ => TyM.err, paramTy := fun _ _ _ _ => .plain TyM.err }
  D := D₀

/-- The run's future: every label the number `0`. -/
def φ₀ : Future := fun _ => .el0 Nat 0

/-- `x₀ : Nat`, reading label `0` whole. -/
def b₀ : SBinding := { ty := .plain TyM.nat, val := fun ψ => ψ 0 }

/-- `x₁ : Nat`, holding label `0`: the number `1`. -/
def b₁ : SBinding := { ty := .plain TyM.nat, val := fun _ => .el0 Nat 1 }

def sh₀ : Pos → Option Nat
  | .bind 0 1 => some 0
  | _ => none

def s₀ : SState where
  env := [{ binds := [b₀, b₁] }]
  shape := sh₀
  nextLoan := 1
  heldTy := fun _ => TyM.nat
  heldMem := fun _ => .el0 Nat 1

theorem positions_s₀ : s₀.positions = [.bind 0 0, .bind 0 1] := by
  simp [s₀, SState.positions, List.range']

theorem live_s₀ : s₀.liveLabels = [0] := by
  unfold SState.liveLabels; rw [positions_s₀]; simp [s₀, sh₀]

theorem sh₀_some {p : Pos} {l : Nat} (h : sh₀ p = some l) : p = .bind 0 1 ∧ l = 0 := by
  unfold sh₀ at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

theorem nat_mem (dm : DataModel) (n : Nat) : Sem.el0 Nat n ∈ₛ[dm.read] TyM.nat := ⟨n, rfl⟩

/-- Off label `0`, nothing in `s₀` reads the future. -/
theorem valAt_s₀_indep (p : Pos) (ψ : Future) {l : Nat} (hl : l ≠ 0) (x : Sem) :
    s₀.valAt p (ψ.upd l x) = s₀.valAt p ψ := by
  cases p with
  | bind f i =>
    rcases f with _ | f
    · rcases i with _ | _ | i
      · show (ψ.upd l x) 0 = ψ 0
        rw [Future.upd_other _ _ (Ne.symm hl)]
      · rfl
      · rfl
    · rfl
  | temp f i =>
    rcases f with _ | f
    · rfl
    · rfl

/-- **`s₀` is good.** -/
theorem s₀_good (dm : DataModel) : SGood dm [] φ₀ s₀ := by
  refine ⟨fun ψ hψ f i hp => ?_, fun ψ hψ p l hl => ?_, fun l _ => nat_mem dm 1, fun f i l hl => ?_,
    ⟨fun p ψ ψ' h => ?_, fun r x _ hs ψ ψ' _ => ?_, fun p x hp => ?_⟩, fun p l ⟨ψ, x, hne⟩ => ?_⟩
  · rw [positions_s₀] at hp
    simp only [List.mem_cons, Pos.bind.injEq, List.mem_nil_iff, or_false] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl (hψ.2 0 (by rw [live_s₀]; simp))
    · exact .inl (.mem (nat_mem dm 1))
  · obtain ⟨rfl, rfl⟩ := sh₀_some hl
    exact .mem (nat_mem dm 1)
  · obtain ⟨he, rfl⟩ := sh₀_some hl
    cases he; rfl
  · have : ψ = ψ' := funext fun y => h y (.inl trivial)
    rw [this]
  · obtain ⟨rfl, rfl⟩ := sh₀_some hs
    rfl
  · obtain ⟨rfl, rfl⟩ := sh₀_some hp
    exact ⟨by rw [positions_s₀]; simp, by decide⟩
  · show l < 1
    by_cases hl : l = 0
    · omega
    · exact absurd (valAt_s₀_indep p ψ hl x).symm hne

/-- The state after moving out `x₀.0`. -/
noncomputable def s₁ (dm : DataModel) : SState :=
  s₀.setAt (.bind 0 0) fun φ' =>
    (Sem.updAt dm [] (.plain TyM.nat) (fun _ => .moved) [.proj 0] (φ' 0)).getD .err

theorem typedFuture_s₀ : s₀.typedFuture φ₀ 0 = .el0 Nat 1 := by
  show (if 0 ∈ s₀.liveLabels then s₀.heldMem 0 else φ₀ 0) = _
  rw [live_s₀]; simp [s₀]

/-- **Moving out `x₀.0` succeeds** (at the typed future `x₀` reads `1`). -/
theorem setContent_s₀ (dm : DataModel) :
    setContent (Kc dm) φ₀ (.bind 0 0) [.proj 0] .moved s₀ = some (⟨⟩, s₁ dm) := by
  unfold setContent
  have hT : s₀.tyAt (.bind 0 0) = .plain TyM.nat := rfl
  have hv : s₀.valAt (.bind 0 0) = fun ψ => ψ 0 := rfl
  have hu : Sem.updAt dm [] (.plain TyM.nat) (fun _ => .moved) [.proj 0] (.el0 Nat 1) = some (Sem.moved.succ) := by
    rw [Sem.updAt.eq_def]
    simp [Sem.asNat_el0]
    exact ⟨_, rfl, rfl⟩
  simp only [hT, hv, typedFuture_s₀, Kc]
  rw [hu]
  rfl

/-- **The state after is not good**: at the typed future giving label `0` the number `0`, `x₀` reads
`err` (the predecessor of `0` does not exist). -/
theorem s₁_bad (dm : DataModel) : ¬ SGood dm [] φ₀ (s₁ dm) := by
  intro hs
  have hTF : TypedF dm [] φ₀ (s₁ dm) φ₀ := by
    refine ⟨fun _ _ => rfl, fun l _ => ?_⟩
    exact .mem (nat_mem dm 0)
  have hp : Pos.bind 0 0 ∈ (s₁ dm).positions := by
    unfold s₁; rw [SState.positions_setAt, positions_s₀]; simp
  have h := hs.bind φ₀ hTF 0 0 hp
  have hval : (s₁ dm).valAt (.bind 0 0) φ₀ = .err := by
    show (Sem.updAt dm [] (.plain TyM.nat) (fun _ => .moved) [.proj 0] (Sem.el0 Nat 0)).getD .err = .err
    rw [Sem.updAt.eq_def]
    simp [Sem.asNat_el0]
  have hty : ((s₁ dm).tyAt (.bind 0 0)).m = TyM.nat := rfl
  rw [hval, hty] at h
  rcases h with h | ⟨he, -⟩
  · cases h with
    | mem h =>
      obtain ⟨a, ha⟩ := h
      cases ha
  · exact absurd (congrArg TyM.level he) (by decide)

/-- **`setContent_field_moved_sgood` (`OpsPlace`) is false as stated**, at every data model. -/
theorem not_setContent_field_moved_sgood (dm : DataModel) :
    ¬ ∀ (K : RunCtx) (φ : Future) (s s' : SState) (f i : Nat) (steps : List Step), SGood K.dm K.Γ φ s →
      (steps ≠ [] ∧ steps ≠ [.deref]) → setContent K φ (.bind f i) steps .moved s = some (⟨⟩, s') →
      SGood K.dm K.Γ φ s' := fun h =>
  s₁_bad dm (h (Kc dm) φ₀ s₀ (s₁ dm) 0 0 [.proj 0] (s₀_good dm) ⟨by simp, by simp⟩ (setContent_s₀ dm))

/-! ## The run reaches it: a move out of `x₀.0` -/

/-- The place `x₀.0` (`x₀` is variable `1`, `x₁` variable `0`). -/
def p₀ : Place := .proj 0 (.var 1)

theorem resolve_p₀ : resolve s₀ p₀ = some (.bind 0 0, [.proj 0]) := rfl

theorem access_s₀ (pos : Pos) (hit : List Step → Bool) : s₀.access pos hit = s₀ := by
  have hr : s₀.reached pos hit = fun _ => false := funext fun _ => rfl
  have hstep : (s₀.liveLabels.filter (s₀.reached pos hit)).foldl SState.endLabel s₀ = s₀ := by
    rw [hr, live_s₀]; rfl
  unfold SState.access
  rw [live_s₀]
  simp only [List.length_singleton]
  exact hstep

theorem contentOf_p₀ (dm : DataModel) :
    contentOf (Kc dm) φ₀ p₀ s₀ = some ((.el0 Nat 0, { (TyS.plain TyM.nat) with label := none }, .bind 0 0, [.proj 0]), s₀) := by
  unfold contentOf
  rw [resolve_p₀]
  dsimp only
  rw [access_s₀]
  have hv : s₀.valAt (.bind 0 0) (s₀.typedFuture φ₀) = .el0 Nat 1 := typedFuture_s₀
  have hT : s₀.tyAt (.bind 0 0) = .plain TyM.nat := rfl
  rw [hv, hT]
  simp [Sem.follow, Sem.step, Sem.asNat_el0]

/-- **The strict run's move out of `x₀.0` succeeds from the good state `s₀`, and leaves `s₁`.** -/
theorem readPlace_p₀ (dm : DataModel) :
    readPlace (Kc dm) φ₀ p₀ false s₀ = some ((.el0 Nat 0, { (TyS.plain TyM.nat) with label := none }), s₁ dm) := by
  unfold readPlace
  rw [contentOf_p₀]
  have hrg : ReadGood (Kc dm).dm.read ({ (TyS.plain TyM.nat) with label := none } : TyS).m (.el0 Nat 0) :=
    .inl (nat_mem dm 0)
  simp [Sem.whole, hrg, setContent_s₀]

/-- **`OpsPlace.readPlace_fund_all` is false**: the lemma at a read moving out of a field. -/
theorem not_readPlace_fund_all (dm : DataModel) : ¬ FundAt (Kc dm).dm (Kc dm).Γ φ₀ (readPlace (Kc dm) φ₀ p₀ false) :=
  fun h => s₁_bad dm (h s₀ (s₁ dm) _ (s₀_good dm) (readPlace_p₀ dm)).2.2.2

/-- `Kc`'s context obligations hold. -/
theorem fundCtx_Kc (dm : DataModel) : FundCtx (Kc dm) :=
  ⟨fun _ => ⟨.inl (nat_mem dm 0), rfl⟩, fun _ h => absurd h List.not_mem_nil⟩

/-- **The fundamental lemma as stated (`Fund.fund_all`) is false**: at `Kc` (its context holds), the
term `x₀.0` (a move: `D₀` copies nothing), from the good state `s₀`. -/
theorem not_fund_all (dm : DataModel) (ρ : Assignment) :
    ¬ (FundCtx (Kc dm) → ∀ t : Term, t.valsOk (fun v => Fund (Kc dm) ρ φ₀ (.val v)) → Fund (Kc dm) ρ φ₀ t) := by
  intro h
  have hrun : runT (Kc dm) ρ φ₀ false (.plain TyM.err) (.place p₀) s₀ =
      some ((.el0 Nat 0, { (TyS.plain TyM.nat) with label := none }), s₁ dm) := by
    rw [runT]
    exact readPlace_p₀ dm
  exact s₁_bad dm (h (fundCtx_Kc dm) (.place p₀) trivial false _ s₀ (s₁ dm) _ (s₀_good dm) hrun).2.2.2

end Ochr.Meaning.Strict.FieldWriteCE
