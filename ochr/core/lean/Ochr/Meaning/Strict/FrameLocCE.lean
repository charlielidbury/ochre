import Ochr.Meaning.Strict.FrameCE
import Ochr.Meaning.Steps.FrameFrag

/-!
# The frame property as restated by D113 is still false: a value reading a dead label (model6; docs/31 D129)

`FrameProp.run_frame` relates the callee's frame in place and in the closure by `FrameRel`, whose top
clause compares two bindings' values as FUNCTIONS of the future through the renaming
(`∀ ψ, v ψ = v' (renF σ ψ)`). But the run reads a value at ONE future, the state's typed future
(`SState.typedFuture`: each live label its record, the run's future `φ` elsewhere), and the two sides'
typed futures agree through `σ` only at the live labels: at a label `l` that no position holds (ended,
or never held), the closure reads `φ l` and the run in place reads `φ (σ l)`. So a value that reads such
a label is read differently on the two sides, and nothing in `FrameRel`, `FrameStart` or `SGood` (whose
`fresh` clause, `ReadsBelow`, only bounds the labels read by the counter) excludes it.

The counterexample (`run_frame_loc_false`): one variable `x : Nat` on top of an empty frame; in the
closure `x` reads label `0`, at counter `1`; in place it reads label `5`, at counter `6`; the renaming
`l ↦ l + 5` (one to one, the closure's counter onwards to the in-place one). No label is live. At the
future giving `5` the number `1` and every other label `0`, reading `x` gives `1` in place and `0` in the
closure, both runs succeeding.

No state a call makes is of this kind: at a call every binding of the callee's frame is future-free
(`callFrame`, `bodyAt`), and the run keeps every position's dependence within the live labels
(`Locality.Inv1`; ending a label substitutes it away). The repair is a clause of the relation, not of the
run: the closure's frame reads only its live labels (`FT (Live s') v'` for its bindings and temporaries).
The label-free fragment's proof (`Steps/FrameFrag.lean`) carries the strongest form of it, every value
future-free.
-/

namespace Ochr.Meaning.Strict.FrameLocCE

open Ochr Ochr.Meaning Ochr.Meaning.Strict Ochr.Meaning.Strict.Witness
open Ochr.Meaning.Strict.FieldWriteCE (nat_mem)

/-- `x : Nat`, reading label `k`'s final content. -/
def xL (k : Nat) : SBinding := { ty := .plain TyM.nat, val := fun ψ => ψ k, decl := .other }

/-- `[{}, {x}]`, `x` reading label `k`, at counter `c`, nothing held or lent. -/
def sL (k c : Nat) : SState :=
  { env := [{}, { binds := [xL k] }], shape := fun _ => none, nextLoan := c,
    heldTy := fun _ => TyM.nat, heldMem := fun _ => .el0 Nat 0 }

/-- The future: label `5` the number `1`, every other `0`. -/
def φL : Future := fun l => if l = 5 then .el0 Nat 1 else .el0 Nat 0

theorem live_sL (k c : Nat) : (sL k c).liveLabels = [] := by
  unfold SState.liveLabels
  have : ∀ (ps : List Pos), ps.filterMap (fun _ => (none : Option Nat)) = [] := fun ps => by
    induction ps with | nil => rfl | cons _ _ ih => simp [ih]
  simp only [sL, this, List.mergeSort_nil]

theorem positions_sL (k c : Nat) : (sL k c).positions = [.bind 1 0] := by
  simp [sL, SState.positions, List.range']

/-- Reading `x` (moving it: `Dw` copies nothing) gives what `x` reads at `φ`. -/
theorem run_read (dm : DataModel) (ρ : Assignment) (φ : Future) (k c : Nat) (tl : Bool) (hint : TyS)
    (hk : φ k ∈ₛ[dm.read] TyM.nat) (hw : (φ k).whole = true) :
    ∃ r s₁, runT (Kw dm []) ρ φ tl hint (.place (.var 0)) (sL k c) = some (r, s₁) ∧ r.1 = φ k := by
  have hv : (sL k c).varPos 0 = some (.bind 1 0) := by simp [SState.varPos, sL, SState.topIdx]
  have hnr : ∀ l, (sL k c).reached (.bind 1 0) (dataHit []) l = false := fun l => by simp [SState.reached, sL]
  have hc : contentOf (Kw dm []) φ (.var 0) (sL k c) =
      some ((φ k, .plain TyM.nat, .bind 1 0, []), sL k c) := by
    unfold contentOf
    simp only [resolve, Place.steps, hv, Option.map_some]
    rw [Steps.Form.FrameFrag.access_self (fun l _ => hnr l),
      show (sL k c).typedFuture φ = φ from funext fun l => by simp [SState.typedFuture, live_sL]]
    simp [Sem.follow, SState.valAt, SState.tyAt, sL, xL]
  have hok : ContentOk (Kw dm []) φ (.var 0) (sL k c) := by
    simp only [ContentOk, resolve, Place.steps, hv, Option.map_some]
    exact Steps.Form.FrameFrag.accessOk_self _ _ (fun l _ => hnr l)
  have heq : runT (Kw dm []) ρ φ tl hint (.place (.var 0)) (sL k c) = readPlace (Kw dm []) φ (.var 0) false (sL k c) := by
    rw [runT]
    show SM.erasedIf (false, false) (SM.guarded (ContentOk (Kw dm []) φ (.var 0))
      (readPlace (Kw dm []) φ (.var 0) false)) (sL k c) = _
    simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false, SM.guarded_of hok]
  rw [heq]
  unfold readPlace
  rw [hc]
  simp only [Bind.bind, Option.bind, hw, not_true, if_false, Steps.Form.FrameFrag.setContent_nil]
  rw [if_neg (fun hn => hn (.inl hk))]
  exact ⟨_, _, rfl, rfl⟩

/-- The in-place state is good at `φL`. -/
theorem sL_good (dm : DataModel) : SGood dm [] φL (sL 5 6) := by
  have hψ : ∀ ψ, TypedF dm [] φL (sL 5 6) ψ → ψ = φL := fun ψ hψ =>
    funext fun l => hψ.1 l (by rw [live_sL]; exact List.not_mem_nil)
  refine ⟨fun ψ hψ' f i hp => ?_, fun ψ _ p l hl => ?_, fun l hl => ?_, fun f i l hl => ?_,
    ⟨fun p ψ ψ' h => ?_, fun r x _ hs ψ ψ' _ => ?_, fun p x hp => ?_⟩, fun p l ⟨ψ, x, hne⟩ => ?_,
    fun p q l hp _ => ?_⟩
  · rw [positions_sL] at hp
    simp only [List.mem_cons, Pos.bind.injEq, List.mem_nil_iff, or_false] at hp
    obtain ⟨rfl, rfl⟩ := hp
    rw [hψ ψ hψ']
    exact .inl (.mem (by simp [SState.valAt, SState.tyAt, sL, xL, φL]; exact nat_mem dm 1))
  · cases hl
  · rw [live_sL] at hl; cases hl
  · cases hl
  · have : ψ = ψ' := funext fun y => h y (.inl trivial)
    rw [this]
  · cases hs
  · cases hp
  · show l < 6
    by_cases e : l = 5
    · omega
    · exfalso; apply hne
      cases p with
      | bind f i =>
        rcases f with _ | _ | f <;> rcases i with _ | i <;>
          simp [SState.toMean, SState.valAt, sL, xL, Future.upd, Ne.symm e]
      | temp f i => rcases f with _ | _ | f <;> simp [SState.toMean, SState.valAt, sL]
  · cases hp

/-- The two states are related by `FrameRel` at the renaming `l ↦ l + 5`, no parameter. -/
theorem frameRel_L : FrameRel (fun l => l + 5) (sL 5 6) [] (sL 5 6) (sL 0 1) := by
  have hnl : ∀ l, ¬ (sL 0 1).Live l := fun l hl => by simp [SState.Live, live_sL] at hl
  refine ⟨fun l l' h => by omega, fun j => by simp [sL]; omega, ⟨rfl, rfl⟩, fun f _ => rfl, fun p _ ψ => rfl,
    fun p _ => rfl, ?_, fun p _ => by simp [sL], fun q l hq => by simp [sL] at hq, fun l hl => absurd hl (hnl l),
    fun l x _ => by simp [sL], fun m x _ hx => by simp [sL] at hx, fun l x hx => by simp [sL] at hx,
    fun l p _ hp => by simp [sL] at hp, fun l hl => absurd hl (hnl l)⟩
  refine ⟨{ binds := [xL 5] }, { binds := [xL 0] }, by simp [sL], by simp [sL], rfl, fun i b b' h h' => ?_, rfl,
    fun j v hv => by simp at hv⟩
  rcases i with _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at h h'
    subst h h'
    exact ⟨rfl, rfl, rfl, fun ψ => rfl⟩
  · simp at h

theorem frameStart_L : FrameStart (sL 5 6) [] :=
  ⟨fun p hp ψ ψ' _ => by
      rcases p with ⟨f, i⟩ | ⟨f, i⟩ <;> simp [SState.topIdx, sL] at hp <;> subst hp <;> simp [SState.valAt, sL],
    by simp, fun p l _ hp => by simp [sL] at hp, fun p l x _ hp => by simp [sL] at hp, List.nodup_nil⟩

/-- **`FrameProp.run_frame` as restated (D113, the in-place state good) is false**, at every data model:
from `FrameRel`-related states, no parameter, the in-place state good, `FrameStart` met, reading `x` gives
`1` in place and `0` in the closure (`x` reads a dead label, which the two typed futures do not relate). -/
theorem run_frame_loc_false (dm : DataModel) (ρ : Assignment) :
    ¬ ∀ (φ : Future) (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) (_ : FrameStart s₀ ks) (tl : Bool) (hint : TyS)
      (t : Term) (_ : t.idFree = true ∨ ks = []) (s s' : SState) (_ : FrameRel σ s₀ ks s s')
      (_ : SGood dm [] φ s),
      FrameAgree σ s₀ ks (runT (Kw dm []) ρ φ tl hint t s) (runT (Kw dm []) ρ φ tl hint t s') := by
  intro h
  have := h φL (fun l => l + 5) _ [] frameStart_L false (.plain TyM.err) (.place (.var 0)) (.inr rfl) _ _ frameRel_L
    (sL_good dm)
  obtain ⟨r, s₁, h1, e1⟩ := run_read dm ρ φL 5 6 false (.plain TyM.err) (by simp [φL]; exact nat_mem dm 1)
    (by simp [φL, Sem.whole])
  obtain ⟨r', s₁', h2, e2⟩ := run_read dm ρ φL 0 1 false (.plain TyM.err) (by simp [φL]; exact nat_mem dm 0)
    (by simp [φL, Sem.whole])
  rw [h1, h2] at this
  have e := this.1
  rw [e1, e2] at e
  simp [φL] at e

end Ochr.Meaning.Strict.FrameLocCE
