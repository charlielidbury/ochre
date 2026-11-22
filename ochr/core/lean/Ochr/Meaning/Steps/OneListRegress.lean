import Ochr.Meaning.Steps.Machine.FragFree

/-!
# One declaration list: the fragment theorem at a context whose list is longer than the checker's (lead25; docs/31 D174)

The lead's ruling (docs/34 §18.13): the reference's declaration list is the WHOLE PROGRAM'S at every
stage, and the checker's state at a stage holds a PREFIX of it (`CtxS.inds : st.inds <+: K.Γ`). This
file is the regression that uses the freedom: the fragment theorem (`frag_run_free`, which covers the
columns `B` and `C`) instantiated at a context whose list has a declaration AFTER the checker's. The
checker's state `stC` declares nothing; the context `KCw dm D Γ` declares `Γ`, any list the model
covers with no declaration at `Type₁` (`FundCtx`); `oneMore` is the instance at one declaration `X`.

Nothing the fragment's steps prove reads the context's list beyond what `CtxS`, `Inv`, `SGood` and
`FundCtx` say, and each of those holds at the longer list at the start (`pre_stCw`, `sgood_stCw`,
`fundCtx_KCw`): the theorem goes through with no new fact.
-/

namespace Ochr.Meaning.Steps.Form.OneList

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Ochr.Meaning.Steps.Form.ColumnC (stC CC)
open Ochr.Meaning.Steps.Form.ColumnC.Aux (norm_stC allPos_stC)

/-- `C`'s run context at the declaration list `Γ` (`ColumnC.KC` is the one at `[]`). -/
def KCw (dm : DataModel) (D : Decisions) (Γ : List IndDecl) : RunCtx := { dm := dm, Γ := Γ, C := CC, D := D }

section
variable (dm : DataModel) (D : Decisions) (Γ : List IndDecl) (ρ : Assignment) (φ : Future)

/-- The context's part at the start: the checker's declarations `[]` are a prefix of `Γ`; faithfulness
is asked of none of them. -/
theorem ctxS_stCw (hcov : ∀ d ∈ Γ, dm.covers d) : CtxS (KCw dm D Γ) stC where
  inds := List.nil_prefix
  covers := hcov
  faithful := fun _ h => absurd h List.not_mem_nil
  noLabel := fun _ => rfl
  globals := ⟨fun _ _ h => by simp [stC] at h, fun _ _ h => by simp [stC] at h, fun _ _ _ h => by simp [stC] at h,
    fun _ _ h => by simp [stC] at h, fun _ _ _ h => by simp [stC] at h⟩

theorem asg_stCw : Asg (KCw dm D Γ) ρ stC := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro σ _ h; simp [stC] at h
  · intro n σ h; simp [stC] at h
  · intro σ v h; simp [stC] at h
  · intro σ r h; simp [stC] at h
  · intro σ _ h; simp [stC] at h
  · intro G h; simp [MState.goalM, stC] at h
  · intro σ _ h; simp [stC] at h

theorem pre_stCw (hcov : ∀ d ∈ Γ, dm.covers d) : Pre (KCw dm D Γ) ρ stC := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [norm_stC]
  · exact ctxS_stCw dm D Γ hcov
  · exact Ochr.Meaning.Steps.Form.ColumnC.Aux.inv_stC D
  · exact asg_stCw dm D Γ ρ

theorem positions_SMw : (SM' (KCw dm D Γ) ρ stC).positions = [] := by
  unfold SM'; rw [sstate_positions]; exact allPos_stC

theorem shape_SMw (p : Pos) : (SM' (KCw dm D Γ) ρ stC).shape p = none := by
  cases h : (SM' (KCw dm D Γ) ρ stC).shape p with
  | none => rfl
  | some l =>
    have := mem_allPos_of_shape (l := l) h
    rw [allPos_stC] at this; cases this

theorem liveLabels_SMw : (SM' (KCw dm D Γ) ρ stC).liveLabels = [] := by
  simp [SState.liveLabels, positions_SMw]

theorem valAt_SMw (p : Pos) : (SM' (KCw dm D Γ) ρ stC).valAt p = fun _ => .err :=
  SState.valAt_of_not_mem _ _ (by rw [positions_SMw]; exact List.not_mem_nil)

theorem rel_stCw : Rel (KCw dm D Γ) ρ φ id stC (SM' (KCw dm D Γ) ρ stC) :=
  Rel.start_noLive _ _ _ _ fun l h => by
    simp [SState.Live, liveLabels_SMw] at h

theorem sgood_stCw : Strict.SGood dm Γ φ (SM' (KCw dm D Γ) ρ stC) where
  bind := fun ψ _ f i hp => by rw [positions_SMw] at hp; cases hp
  holder := fun ψ _ p l hl => by rw [shape_SMw] at hl; cases hl
  held := fun l hl => by rw [liveLabels_SMw] at hl; cases hl
  holderTy := fun f i l hl => by rw [shape_SMw] at hl; cases hl
  acyc := ⟨fun p ψ ψ' _ => by rw [valAt_SMw], fun r x hr => (by rw [positions_SMw] at hr; cases hr),
    fun p x hp => (by rw [shape_SMw] at hp; cases hp)⟩
  fresh := fun p l h => by
    obtain ⟨ψ, x, hne⟩ := h
    exact absurd (by show (SM' (KCw dm D Γ) ρ stC).valAt p ψ = (SM' (KCw dm D Γ) ρ stC).valAt p (ψ.upd l x); rw [valAt_SMw]) hne
  uniq := fun p _ l hp _ => by rw [shape_SMw] at hp; cases hp

theorem fundCtx_KCw (hsort : ∀ d ∈ Γ, d.sort ≠ 2) : Strict.FundCtx (KCw dm D Γ) :=
  ⟨fun _ => ⟨.inl ⟨0, rfl⟩, rfl⟩, hsort⟩

end

/-- **The fragment's run theorem at a context whose list is `Γ`** (`frag_run` at `KCw`): the checker's
state declares nothing, the context any list the model covers with no declaration at `Type₁`. Assumes
`FragFacts`, as `frag_run` does. -/
theorem frag_run_wide {D : Decisions} (hf : FragFacts D) (dm : DataModel) (Γ : List IndDecl)
    (hcov : ∀ d ∈ Γ, dm.covers d) (hsort : ∀ d ∈ Γ, d.sort ≠ 2) (ρ : Assignment) (φ : Future) {t : Term}
    {A : FT} (hty : FTy [] t A) {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value}
    {T? : Option Value} (hk : Kern stC st) (hm : Mode st) (htd : st.tailDecl = none) (hD : DecTab D st')
    (h : Runs (Ochr.eval n true t hint) st bh (v, T?) st') :
    ∃ r s', runT (KCw dm D Γ) ρ φ st.tailNext (hintM (KCw dm D Γ) ρ hint) t (SM' (KCw dm D Γ) ρ stC) = some (r, s') ∧
      T? = some A.ty ∧ r.2.m = A.tyM ∧ r.1 ∈ₛ[dm.read] r.2.m := by
  have hP : FSt [] st := fst_stC.kern hk
  obtain ⟨hT, hv, -⟩ := hf.run [] t A n hint st st' bh v T? hty hP
    ((pre_stCw dm D Γ ρ hcov).of_kern hk).inv.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hm (.inl htd) hD h
  have hfl : D.flags (scopeOf (SM' (KCw dm D Γ) ρ stC)) t = (false, false) := by
    rw [scopeOf_sstate']; exact (hf.dec [] t A stC hty fst_stC).1
  obtain ⟨ρ', Δ', π', r, s', -, hx, hmean, hagree, -, -, -⟩ :=
    frag_sim (K := KCw dm D Γ) (φ := φ) hf (fundCtx_KCw dm D Γ hsort) [] t A hty n (KCw dm D Γ).Δ ρ
      st st' true hint v T? (SM' (KCw dm D Γ) ρ stC) id hP rfl hm (.inl htd) ((pre_stCw dm D Γ ρ hcov).of_kern hk)
      ((rel_stCw dm D Γ ρ φ).of_kern hk) (sgood_stCw dm D Γ ρ φ) (hty.valsOk _) (fun σ hσ => hty.absBelow _ σ hσ)
      hty.noHole hfl (fun e => by cases e) hD bh h
  have hm2 : r.2.m = A.tyM := by rw [← hagree A.ty hT]; cases A <;> rfl
  refine ⟨r, s', hx, hT, hm2, ?_⟩
  rw [hm2, ← hmean, ← meanV_eq_mean]
  cases A with
  | nat => obtain ⟨k, hk⟩ := (hv : v.Num).vmean; rw [hk]; exact ⟨k, rfl⟩
  | unit => rw [show v = .unit from hv]; first | exact ⟨(), rfl⟩ | rfl | trivial
  | ref =>
    obtain ⟨l, c, rfl, hc⟩ := hv
    obtain ⟨k, hk⟩ := hc.vmean
    show Value.mean _ _ _ _ _ _ c ∈ₛ[dm.read] TyM.nat
    rw [hk]; exact ⟨k, rfl⟩

/-- One declaration, `inductive X := MkX`, declared AFTER the checker's (empty) list. -/
def declX : IndDecl := { name := "X", ctors := [("MkX", [])] }

/-- **The regression** (docs/31 D174): the fragment theorem with no assumed fact (`frag_run_free`'s
statement), at a context whose list is `[X]` while the checker's state declares nothing, for every data
model covering `X`, at the checker's fuel-free table. -/
theorem oneMore (dm : DataModel) (hX : dm.covers declX) (ρ : Assignment) (φ : Future) {t : Term} {A : FT}
    (hty : FTy [] t A) {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stC st) (hm : Mode st) (htd : st.tailDecl = none)
    (h : Runs (Ochr.eval n true t hint) st bh (v, T?) st') :
    ∃ r s', runT (KCw dm (checkerDecisionsFF st') [declX]) ρ φ st.tailNext
        (hintM (KCw dm (checkerDecisionsFF st') [declX]) ρ hint) t (SM' (KCw dm (checkerDecisionsFF st') [declX]) ρ stC)
          = some (r, s') ∧
      T? = some A.ty ∧ r.2.m = A.tyM ∧ r.1 ∈ₛ[dm.read] r.2.m :=
  frag_run_wide ((Machine.fragOpen_ff st').facts (Machine.placeLocal_ff st' _) (fun _ _ => rfl)) dm [declX]
    (fun d hd => by simp only [List.mem_singleton] at hd; subst hd; exact hX)
    (fun d hd => by simp only [List.mem_singleton] at hd; subst hd; decide) ρ φ hty hk hm htd
    (decTab_ff st' _ (fun _ => Machine.decide_fuel_agree' _) (Machine.decide_fuel_agree' st')) h

end Ochr.Meaning.Steps.Form.OneList
