import Ochr.Meaning.Steps.DropOneAsm
import Ochr.Meaning.Steps.EqJAsm

/-!
# Splits and worlds, assembled from named obligations (docs/31 D76; area (f))

A [Split] on an unknown `σ` checks each arm in its own world (`enterWorld`, `inWorld`, `exitWorld`):
the arm's refinement `σ := r` (`refine`: the substitution over the whole state, the path condition
recorded, the re-normalisation when `σ` is a generalisation's) holds in that world only. The
reference never splits: it runs the arm the assignment selects. So every step of a world is related
to the one reference state under an assignment at which the world's refinements hold, and leaving
the world restores the snapshot, related as it was.

Here: `refine` assembled from the substitution lemma for unknowns (`substEnv_abs_step`, the
induction hypothesis), the record (`refs_sim`, proved) and the re-normalisation (`renormAll_step`);
`exitWorld` assembled from its run (proved) and the restored state's context (a leaf); and
`access_ctx` restated with the decisions extended (the slice's `access_ctx` is false as stated).
-/

namespace Ochr.Meaning.Steps

open Ochr Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **A value naming only old unknowns means the same under an extension** (leaf;
`AssignCongr.meanV_congrA` for the assignment, `DecExtend.meanV_congrD` for the decisions, and `Δ`
read only at the unknowns a value holds). -/
theorem meanV_ext {n : Nat} {ρ' : Assignment} {Δ' : Nat → TyS} {D' : Decisions} (v : Value) (ψ : Future) (hint : TyS)
    (hv : ∀ σ, v.hasAbs σ = true → σ < n) (ha : ∀ σ, σ < n → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ)
    (hd : K.D.AgreeOld n D') :
    meanV { K with Δ := Δ', D := D' } ρ' ψ hint v = meanV K ρ ψ hint v := by
  sorry

/-- A refinement that holds at an assignment holds at an extension of it, and stays well-formed
in a larger table (proved from `meanV_ext`). -/
theorem RefineOk.ext {st st₁ : MState} {σ : Nat} {r : Value} {ρ₁ : Assignment} {Δ₁ : Nat → TyS} {D₁ : Decisions}
    (hr : RefineOk K ρ st σ r) (hsz : st.absTy.size ≤ st₁.absTy.size)
    (ha : ∀ τ, τ < st.absTy.size → ρ₁ τ = ρ τ ∧ Δ₁ τ = K.Δ τ) (hd : K.D.AgreeOld st.absTy.size D₁) :
    RefineOk { K with Δ := Δ₁, D := D₁ } ρ₁ st₁ σ r := by
  obtain ⟨hσ, hlt, habs, hnσ, hloan⟩ := hr
  refine ⟨fun ψ H => ?_, Nat.lt_of_lt_of_le hlt hsz, fun τ hτ => Nat.lt_of_lt_of_le (habs τ hτ) hsz, hnσ, hloan⟩
  rw [meanV_ext K ρ r ψ H habs ha hd, (ha σ hlt).1]
  exact hσ ψ H

theorem SubstShape.trans {st₁ st₂ st₃ : MState} (h₁ : SubstShape st₁ st₂) (h₂ : SubstShape st₂ st₃) :
    SubstShape st₁ st₃ :=
  ⟨fun p => (h₂.1 p).trans (h₁.1 p), h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    Nat.le_trans h₁.2.2.2.1 h₂.2.2.2.1, Nat.le_trans h₁.2.2.2.2 h₂.2.2.2.2⟩

/-- Recording the path condition changes no shape. -/
theorem SubstShape.refs (st : MState) (σ : Nat) (r : Value) :
    SubstShape st { st with refs := (σ, r) :: st.refs } :=
  ⟨fun _ => rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem SubstShape.refl (st : MState) : SubstShape st st :=
  ⟨fun _ => rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩

/-- An extension by nothing. -/
theorem ExtOk.self {st : MState} (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) :
    ExtOk K ρ st st ρ K.Δ K.D := by
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, Decisions.AgreeOld.refl _ _, ?_, ?_⟩
  · have e : ({ K with Δ := K.Δ, D := K.D } : RunCtx) = K := by cases K; rfl
    rw [e]; exact hctx
  · exact hg

theorem ExtOk.trans_le {st₁ st₂ st₃ : MState} {ρ₂ ρ₃ : Assignment} {Δ₂ Δ₃ : Nat → TyS} {D₂ D₃ : Decisions}
    (hsz : st₁.absTy.size ≤ st₂.absTy.size) (h₁ : ExtOk K ρ st₁ st₂ ρ₂ Δ₂ D₂)
    (h₂ : ExtOk { K with Δ := Δ₂, D := D₂ } ρ₂ st₂ st₃ ρ₃ Δ₃ D₃) : ExtOk K ρ st₁ st₃ ρ₃ Δ₃ D₃ := by
  obtain ⟨a1, d1, -, -⟩ := h₁
  obtain ⟨a2, d2, c2, g2⟩ := h₂
  refine ⟨fun σ hσ => ?_, Decisions.AgreeOld.trans d1 d2 hsz, c2, g2⟩
  have hσ2 : σ < st₂.absTy.size := Nat.lt_of_lt_of_le hσ hsz
  exact ⟨(a2 σ hσ2).1.trans (a1 σ hσ).1, (a2 σ hσ2).2.trans (a1 σ hσ).2⟩

/-- **[Split]'s refinement, assembled** (no `sorry` in the body): the substitution (the induction
hypothesis's `substEnv_abs_step`), the path condition recorded (`refs_sim`, proved: it is
`TypedAssignment.refs`'s condition, which the refinement meets at the extension), and, when `σ` is
a generalisation's, the re-normalisation (`renormAll_step`); the extensions composed. -/
theorem refine_step_asm (fuel : Nat) (ih : StepsIHBelow fuel) : refine_step_stmt K ρ φ (fuel + 1) := by
  intro st st' σ r hg hctx s π hs hr bh h
  unfold Ochr.refine at h
  obtain ⟨⟨⟩, st₁, b₁, hsub, h1⟩ := Runs.bind_inv h
  obtain ⟨sh₁, ρ₁, Δ₁, D₁, e₁, hs₁⟩ := (ih.at K ρ φ).substEnv_abs_step st st₁ σ r hg hctx s π hs hr bh hsub
  obtain ⟨_, st₂, b₂, hmod, h2⟩ := Runs.bind_inv h1
  obtain ⟨L, left, log, hmod⟩ := hmod
  simp only [runMachineL_modify, Prod.mk.injEq, Outcome.ok.injEq] at hmod
  obtain ⟨⟨-, hst₂⟩, -⟩ := hmod
  have hr₁ := RefineOk.ext K ρ hr sh₁.2.2.2.1 e₁.1 e₁.2.1
  obtain ⟨hs₂, hg₂, hctx₂⟩ := refs_sim { K with Δ := Δ₁, D := D₁ } ρ₁ φ st₁ σ r s π e₁.2.2.2 e₁.2.2.1 hs₁
    hr₁.1 ⟨hr₁.2.1, hr₁.2.2.1⟩
  rw [hst₂] at hs₂ hg₂ hctx₂
  have sh₂ : SubstShape st st₂ := by rw [← hst₂]; exact sh₁.trans (SubstShape.refs st₁ σ r)
  have e₂ : ExtOk K ρ st st₂ ρ₁ Δ₁ D₁ := ⟨e₁.1, e₁.2.1, hctx₂, hg₂⟩
  obtain ⟨g, st₃, b₃, hget, h3⟩ := Runs.bind_inv h2
  obtain ⟨L, left, log, hget⟩ := hget
  simp only [runMachineL_get, Prod.mk.injEq, Outcome.ok.injEq] at hget
  obtain ⟨⟨hg3, hst3⟩, -⟩ := hget
  rw [← hst3, ← hg3] at h3
  split at h3
  · obtain ⟨sh₃, ρ₃, Δ₃, D₃, e₃, hs₃⟩ :=
      (ih.at { K with Δ := Δ₁, D := D₁ } ρ₁ φ).renormAll_step st₂ st' hg₂ hctx₂ s π hs₂ b₃ h3
    exact ⟨sh₂.trans sh₃, ρ₃, Δ₃, D₃, ExtOk.trans_le K ρ sh₂.2.2.2.1 e₂ e₃, hs₃⟩
  · obtain ⟨L, left, log, h3⟩ := h3
    simp only [runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at h3
    rw [← h3.1.2]
    exact ⟨sh₂, ρ₁, Δ₁, D₁, e₂, hs₂⟩

/-- What `exitWorld` leaves (proved): the snapshot, with the counters and the arm's new unknowns'
types kept. -/
theorem runs_exitWorld_inv {w : World} {st st' : MState} {b : Nat} (h : Runs (Ochr.exitWorld w) st b () st') :
    st'.env = w.saved.env ∧ st'.goal = w.saved.goal ∧ st'.refs = w.saved.refs ∧ st'.neutrals = w.saved.neutrals ∧
      st'.etaRefs = w.saved.etaRefs ∧ st'.inds = w.saved.inds ∧ st'.nextLoan = st.nextLoan ∧
      st'.absTy = w.saved.absTy ++ st.absTy.extract w.saved.absTy.size st.absTy.size := by
  obtain ⟨L, left, log, h⟩ := h
  unfold Ochr.exitWorld at h
  simp only [runMachineL_modify, Prod.mk.injEq, Outcome.ok.injEq] at h
  obtain ⟨⟨-, rfl⟩, -⟩ := h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The restored state's context** (leaf): the snapshot's Ω, goal, path condition and records,
which name only the snapshot's unknowns, so the assignment and `Δ` are typed as at the snapshot; the
arm's unknowns are named by nothing, so `DeltaOk` and `TypedAssignment` ask nothing of them; their
frozen readings are kept (`absDecl`, D96), so the decisions are extended to agree on them. -/
theorem exitWorld_ctx {w : World} {st st' : MState} {b : Nat}
    (hg : Good K.dm K.M K.Γ ρ w.saved) (hctx : CtxOk K ρ w.saved) (h : Runs (Ochr.exitWorld w) st b () st') :
    ∃ D' : Decisions, ExtOk K ρ w.saved st' ρ K.Δ D' := by
  sorry

/-- **Leaving a world, assembled** (no `sorry` in the body): the run restores the snapshot
(`runs_exitWorld_inv`, proved), so the relation is the snapshot's (`Rel.kept`); the context and
goodness are the leaf `exitWorld_ctx`. -/
theorem exitWorld_step_asm (fuel : Nat) (_ih : StepsIHBelow fuel) : exitWorld_step_stmt K ρ φ (fuel + 1) := by
  intro st st' w hg hctx s π hs hgrow bh h
  obtain ⟨henv, hgoal, hrefs, hneut, heta, hinds, hnl, habs⟩ := runs_exitWorld_inv h
  have hsz : w.saved.absTy.size ≤ st'.absTy.size := by rw [habs]; simp
  have hold : ∀ σ, σ < w.saved.absTy.size → st'.absTy[σ]? = w.saved.absTy[σ]? := by
    intro σ hσ
    rw [habs, Array.getElem?_append_left hσ]
  have hk : KeptAfter w.saved st' := ⟨henv, hgoal, hrefs, hinds, hsz, hold, by rw [hnl]; exact hgrow⟩
  obtain ⟨D', he⟩ := exitWorld_ctx K ρ hg hctx h
  exact ⟨henv, hgoal, hrefs, hneut, heta, hsz, hold, D', he, Rel.kept K ρ φ hg hctx hs hk he⟩

/-- **[Access] keeps the run context, with the decisions extended** (leaf; the slice's `access_ctx`
restated, docs/31 D76). An end of a borrow of a dependent type runs [Repack] (`repackCheck`), whose
`lentUnknown` makes an unknown for a part still lent, with a frozen reading (D96), and uses it for
the check only: Ω never names it. So the assignment and `Δ` need no extension (`DeltaOk` and
`TypedAssignment` read only named unknowns), and the decisions do: `CtxOk`'s alignment is asked of
every input, and `declOf` of `.val (.abs σ)` reads the new reading, which the fixed `K.D` need not
give. As stated in `DropOneAsm` (the context unchanged) it is false. -/
theorem access_ctx_ext (fuel : Nat) (st st' : MState) (q : Place) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (h : Runs (do Ochr.accessPath fuel q; Ochr.accessInside fuel q) st b () st') :
    st.absTy.size ≤ st'.absTy.size ∧ ∃ D' : Decisions, K.D.AgreeOld st.absTy.size D' ∧
      CtxOk { K with D := D' } ρ st' := by
  sorry

end

end Ochr.Meaning.Steps
