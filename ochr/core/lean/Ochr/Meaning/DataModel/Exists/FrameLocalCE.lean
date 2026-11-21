import Ochr.Meaning.Strict.FrameLocCE

/-!
# `runT_frameLocal` as first written is false: the states' borrow records are not compared (exists3)

`General.runT_frameLocal` (exists2, 2026-11-21) related two states by `DiffAt`: the same shape, counter
and frames but at the positions `X`. It said nothing of the other records of a state: where each borrow
is lent (`lent`), and each borrow's content type and recorded member (`heldTy`, `heldMem`). A place is
read at the typed future (`SState.typedFuture`), which gives each LIVE label its recorded member: so a
binding that reads a live label is read differently at two states that differ only in that record.

The counterexample (`frameLocal_false`): one frame `{y, x}`, `y : Nat` the holder of label `0` (so `0`
is live), `x : Nat` reading label `0`'s final content; the two states differ only in `heldMem 0`
(`1` and `2`). `X` is empty, so `DiffAt` holds with every binding equal. Reading `x` gives `1` at one
and `2` at the other, both runs succeeding.

The repair (`FrameLocal.lean`) compares every record but the values at `X`.
-/

namespace Ochr.Meaning.DataModel.Exists.FrameLocalCE

open Ochr Ochr.Meaning Ochr.Meaning.Strict Ochr.Meaning.Strict.Witness
open Ochr.Meaning.Strict.FieldWriteCE (nat_mem)

/-- `General.DiffAt` as exists2 wrote it (kept here so the refutation is checked in the default build). -/
def DiffAtOld (dm : DataModel) (X : Nat → Prop) (s s' : SState) : Prop :=
  s'.shape = s.shape ∧ s'.nextLoan = s.nextLoan ∧ s'.env.length = s.env.length ∧
    (∀ f, f ≠ 0 → s'.env[f]? = s.env[f]?) ∧
    ∃ fr fr' : SFrame, s.env[0]? = some fr ∧ s'.env[0]? = some fr' ∧ fr'.temps = fr.temps ∧
      fr'.binds.length = fr.binds.length ∧
      ∀ p (b b' : SBinding), fr.binds[p]? = some b → fr'.binds[p]? = some b' →
        b'.ty = b.ty ∧ b'.decl = b.decl ∧
        (b'.val = b.val ∨ (X p ∧ ∀ ψ, (b.val ψ).whole ∧ (b'.val ψ).whole ∧
          b.val ψ ∈ₛ[dm.read] b.ty.m ∧ b'.val ψ ∈ₛ[dm.read] b.ty.m))

/-- `y : Nat`, the holder of label `0`. -/
def yB : SBinding := { ty := .plain TyM.nat, val := fun _ => .el0 Nat 0, decl := .other }
/-- `x : Nat`, reading label `0`'s final content. -/
def xB : SBinding := { ty := .plain TyM.nat, val := fun ψ => ψ 0, decl := .other }

/-- `{y, x}`, `y` holding label `0`, whose recorded member is the number `m`. -/
def sH (m : Nat) : SState :=
  { env := [{ binds := [yB, xB] }], shape := fun p => if p = .bind 0 0 then some 0 else none, nextLoan := 1,
    heldTy := fun _ => TyM.nat, heldMem := fun _ => .el0 Nat m }

theorem live_sH (m : Nat) : (sH m).liveLabels = [0] := by
  simp [SState.liveLabels, SState.positions, sH, List.range']

/-- Reading `x` gives label `0`'s recorded member. -/
theorem run_read (dm : DataModel) (ρ : Assignment) (φ : Future) (m : Nat) (tl : Bool) (hint : TyS) :
    ∃ r s₁, runT (Kw dm []) ρ φ tl hint (.place (.var 0)) (sH m) = some (r, s₁) ∧ r.1 = .el0 Nat m := by
  have hv : (sH m).varPos 0 = some (.bind 0 1) := by simp [SState.varPos, sH, SState.topIdx]
  have hnr : ∀ l, (sH m).reached (.bind 0 1) (dataHit []) l = false := fun l => by simp [SState.reached, sH]
  have htf : (sH m).typedFuture φ 0 = .el0 Nat m := by
    simp only [SState.typedFuture]; rw [live_sH]; simp [sH]
  have hx : (sH m).valAt (.bind 0 1) = fun ψ => ψ 0 := by simp [SState.valAt, sH, xB]
  have hT : (sH m).tyAt (.bind 0 1) = .plain TyM.nat := by simp [SState.tyAt, sH, xB]
  have hc : contentOf (Kw dm []) φ (.var 0) (sH m) =
      some ((.el0 Nat m, .plain TyM.nat, .bind 0 1, []), sH m) := by
    unfold contentOf
    simp only [resolve, Place.steps, hv, Option.map_some]
    rw [Steps.Form.FrameFrag.access_self (fun l _ => hnr l)]
    rw [hx, hT]; dsimp only; rw [htf]; simp [Sem.follow]
  have hok : ContentOk (Kw dm []) φ (.var 0) (sH m) := by
    simp only [ContentOk, resolve, Place.steps, hv, Option.map_some]
    exact Steps.Form.FrameFrag.accessOk_self _ _ (fun l _ => hnr l)
  have heq : runT (Kw dm []) ρ φ tl hint (.place (.var 0)) (sH m) =
      readPlace (Kw dm []) φ (.var 0) false (sH m) := by
    rw [runT]
    show SM.erasedIf (false, false) (SM.guarded (ContentOk (Kw dm []) φ (.var 0))
      (readPlace (Kw dm []) φ (.var 0) false)) (sH m) = _
    simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false, SM.guarded_of hok]
  rw [heq]
  unfold readPlace
  rw [hc]
  have hw : (Sem.el0 Nat m).whole := by simp [Sem.whole]
  simp only [Bind.bind, Option.bind, hw, not_true, if_false, Steps.Form.FrameFrag.setContent_nil]
  rw [if_neg (fun hn => hn (.inl (nat_mem dm m)))]
  exact ⟨_, _, rfl, rfl⟩

/-- **`General.runT_frameLocal` as first written is false**, at every data model: two states that
`DiffAtOld` relates with `X` empty (they differ only in a live borrow's recorded member) read `x`
differently. -/
theorem frameLocal_false (dm : DataModel) (ρ : Assignment) :
    ¬ ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (t : Term)
      (X : Nat → Prop) (s s' : SState) (_ : DiffAtOld K.dm X s s') (_ : s.env.length = 1)
      (_ : ∀ v ∈ t.freeVars, ∀ p, s.varPos v = some (.bind 0 p) → ¬ X p)
      {r : Res} {s₁ : SState} (_ : runT K ρ φ tl h t s = some (r, s₁)),
      ∃ s₁', runT K ρ φ tl h t s' = some (r, s₁') := by
  intro H
  obtain ⟨r, s₁, h1, e1⟩ := run_read dm ρ (fun _ => .err) 1 false (.plain TyM.err)
  obtain ⟨r', s₁', h2, e2⟩ := run_read dm ρ (fun _ => .err) 2 false (.plain TyM.err)
  have hd : DiffAtOld (Kw dm []).dm (fun _ => False) (sH 1) (sH 2) :=
    ⟨rfl, rfl, rfl, fun f hf => by rcases f with _ | f <;> simp_all [sH],
      _, _, rfl, rfl, rfl, rfl, fun p b b' h h' => by simp only at h h'; rw [h] at h'; cases h'; exact ⟨rfl, rfl, .inl rfl⟩⟩
  obtain ⟨s₂, h3⟩ := H (Kw dm []) ρ (fun _ => .err) false (.plain TyM.err) (.place (.var 0)) (fun _ => False) _ _ hd rfl
    (fun _ _ _ _ h => h) h1
  rw [h2] at h3
  cases h3
  rw [e1] at e2
  simp at e2

end Ochr.Meaning.DataModel.Exists.FrameLocalCE
