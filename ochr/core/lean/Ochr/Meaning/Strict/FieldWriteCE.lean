import Ochr.Meaning.Strict.Comb
import Ochr.Meaning.BotWrite

/-!
# A write below a part read from a live label: the state that made `fund_all` false, now stuck

REGRESS RECORD (kernel-checked). Before the orchestrator's write rule (2026-11-21), `setContent pos
steps v` wrote `Sem.updAt … steps (old φ')` at every future, `err` where that update failed, and
tested only the state's typed future. A position whose value READS a live label at a strict prefix of
`steps` then read `err` at the typed futures giving the label another open member, which is no open
member of anything; `SGood` does not tie a position's reads of live labels to the sites [Access] ends.
That made `OpsPlace.setContent_field_moved_sgood` and `Fund.fund_all` false (kernel-checked here at
the time, commit 9727fbb9's parent).

The state `s₀`: one frame, `x₀ : Nat` reading label `0` whole (`fun ψ => ψ 0`, the lender, with no
site recorded), `x₁ : Nat` holding `0` (`1`), `heldTy 0 = Nat`, `heldMem 0 = 1`. It is good
(`s₀_good`). The state the old run left after moving out `x₀.0` is not (`s₁_bad`). Under the rule,
the write is tested defined at every typed future, and at `φ₀` (label `0` the number `0`) the path
`.0` is absent: the write fails (`setContent_s₀`), the read's move fails (`readPlace_p₀`), and the
term `x₀.0` is stuck at `s₀` (`runT_p₀`). The simulation's obligation (`Meaning/OPEN.md`) is what
keeps related states away from `s₀`.
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
    · exact .inl (.mem (hψ.2 0 (by rw [live_s₀]; simp)))
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

/-- **Moving out `x₀.0` fails** (the orchestrator's write rule, 2026-11-21): at the typed future giving
label `0` the number `0` (`φ₀` itself), the path `.0` is absent, so the test that the write is defined
at every typed future fails. Before the rule the run succeeded here, at the state's own typed future
(`x₀` reads `1`), and left `s₁`. -/
theorem setContent_s₀ (dm : DataModel) :
    setContent (Kc dm) φ₀ (.bind 0 0) [.proj 0] .moved s₀ = none := by
  unfold setContent
  rw [if_neg]
  intro hall
  have hTF : TypedFut (Kc dm) φ₀ s₀ φ₀ := ⟨fun _ _ => rfl, fun _ _ => nat_mem dm 0⟩
  have h := hall φ₀ hTF
  have hu : Sem.updAt dm [] (.plain TyM.nat) (fun _ => .moved) [.proj 0] (Sem.el0 Nat 0) = none := by
    rw [Sem.updAt.eq_def]
    simp [Sem.asNat_el0]
  change (Sem.updAt dm [] (.plain TyM.nat) (fun _ => .moved) [.proj 0] (Sem.el0 Nat 0)).isSome = true at h
  rw [hu] at h
  cases h

/-- **The state after is not good**: at the typed future giving label `0` the number `0`, `x₀` reads
`err` (the predecessor of `0` does not exist). -/
theorem s₁_bad (dm : DataModel) : ¬ SGood dm [] φ₀ (s₁ dm) := by
  intro hs
  have hTF : TypedF dm [] φ₀ (s₁ dm) φ₀ := by
    refine ⟨fun _ _ => rfl, fun l _ => ?_⟩
    exact nat_mem dm 0
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

/-- **The strict run's move out of `x₀.0` fails from `s₀`**: the run is stuck where the write would
leave `err` at a typed future. -/
theorem readPlace_p₀ (dm : DataModel) : readPlace (Kc dm) φ₀ p₀ false s₀ = none := by
  unfold readPlace
  rw [contentOf_p₀]
  have hrg : ReadGood (Kc dm).dm.read ({ (TyS.plain TyM.nat) with label := none } : TyS).m (.el0 Nat 0) :=
    .inl (nat_mem dm 0)
  simp [Sem.whole, hrg, setContent_s₀]

/-- `Kc`'s context obligations hold. -/
theorem fundCtx_Kc (dm : DataModel) : FundCtx (Kc dm) :=
  ⟨fun _ => ⟨.inl (nat_mem dm 0), rfl⟩, fun _ h => absurd h List.not_mem_nil⟩

/-- **The term `x₀.0` is stuck at `s₀`** (a move: `D₀` copies nothing). The simulation's obligation
(`Meaning/OPEN.md`: after the access of a write at `x.p`, `x` reads no live label along `p`) is what
excludes `s₀` from the states related to the checker's: `x₀` reads label `0` whole and nothing ends
it. -/
theorem runT_p₀ (dm : DataModel) (ρ : Assignment) :
    runT (Kc dm) ρ φ₀ false (.plain TyM.err) (.place p₀) s₀ = none := by
  rw [runT]
  exact readPlace_p₀ dm

end Ochr.Meaning.Strict.FieldWriteCE
