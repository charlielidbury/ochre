import Ochr.Meaning.Steps.MasterLet
import Ochr.Meaning.Steps.Machine.SeqInv

/-!
# The master induction's `;` step, typed and unerased, in general (lead23, 2026-11-22; docs/31 D157)

`seq_coreK`/`stepSeq_typed`: the step for `u; w` from the induction hypothesis, for every first term and tail,
every value and type, every state with a frame meeting `Pre`, every related good reference state, at every
erased depth, for a TYPED run of a sequence whose reading the table decides and does not make a proof. Its proof
is `letIn_core`'s without the push, the drop being a discarded value's (`dropValue`), not a binding's:

* `seqInvD` (a fact about the checker alone, PROVED here: the machine lane's `seqInvR` with the depth free and
  the discard exposed for every value, where `SeqInvR` gave it only for a value holding nothing);
* `SeqTailDecl` (a fact about the table, NEW, guarded): the table reads `u; w` as `w` at the same scope, as the
  checker's `declOf` does (`Decide.lean`'s `.seq` clause runs `u`'s for its errors and returns `w`'s);
* `DropValueG` (the discard, NEW; the inversion of `dropValue` is the checker's, the relation across the end the
  model's): the checker's discard of the first value (`dropValue`) is matched by the reference's (`DiscardOk`,
  `discardEnd`: the borrow the value holds ends), with `Pre` and `Rel` after, keeping the mode, the frames and
  the top readings, only growing the counters. The fragment's `seqI_core`/`seqB_core` are its instances at a
  number, `()` and a borrow of a number;
* `ValsCongrA` (the model's, as for the `let`): the tail's embedded values at the extension.

(I) gives `SGood` after `u` (`Strict.fund_all`) and after the discard (`endLabel_sgood`, as `fund_seq`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

/-- **`evalCore` of a typed `u; w`, at any erased depth, the discard exposed**: `u` evaluated with no hint from
the entry state itself; its value discarded (`dropValue`); the tail's state is the discard's end with the
sequence's reading handed down and its tail flag set (`Kern`, the mode the same); `w` evaluated with no hint. -/
def SeqInvD : Prop :=
  ∀ (n : Nat) (u w : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value)
    (D : Decisions),
    DecTab D st' →
    Runs (Ochr.evalCore (n + 1) true (.seq u w) hint) st bh (v, T?) st' →
    ∃ (st₁ s₄ stW : MState) (v₀ : Value) (T₀ : Option Value) (bh₁ bh₃ bh₂ : Nat),
      Runs (Ochr.eval n true u none) st bh₁ (v₀, T₀) st₁ ∧ DecTab D st₁ ∧
      Runs (Ochr.dropValue n v₀ T₀) st₁ bh₃ () s₄ ∧ DecTab D s₄ ∧
      Form.Kern s₄ stW ∧ Form.ModeEq s₄ stW ∧ stW.tailDecl = st.curDecl ∧ stW.tailNext = st.curTail ∧
      Runs (Ochr.eval n true w none) stW bh₂ (v, T?) st'

/-- **`SeqInvD`, PROVED** (`seqInvR`'s proof). -/
theorem seqInvD : SeqInvD := by
  intro n u w hint st st' bh v T? D hD h
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨hw1, hw2⟩ := runs_wanted_inv hw
  subst hw1 hw2
  simp only [Term.placeOperand?] at h
  rw [runs_get_bind] at h
  obtain ⟨⟨v₀, T₀⟩, s₃, b₃, hu, h₁⟩ := Runs.bind_inv h
  clear h
  obtain ⟨_, s₄, b₄, hdv, h₂⟩ := Runs.bind_inv h₁
  clear h₁
  unfold demand at h₂
  peel h₂
  simp only [Bool.true_or, if_true] at h₂
  simp only at hdv
  have hD₄ : DecTab D s₄ := DecTab.back hD ((TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans
    (Runs.grows (grows_eval _ _ _ _) h₂))
  refine ⟨s₃, s₄, { s₄ with tailDecl := s₁.curDecl, tailNext := s₁.curTail, wantTy := s₁.wantHere }, v₀, T₀, _, _, b₄,
    hu, ?_, hdv, hD₄,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, h₂⟩
  exact DecTab.back hD₄ (Runs.grows (grows_dropValue _ _ _) hdv)

end Ochr.Meaning.Steps.Machine

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-! ## The facts the general step assumes -/

/-- **The table reads `u; w` as `w` at the same scope** (a fact about the table, NEW): as the checker's `declOf`
does (`Decide.lean`: `.seq u w => sub u; declOf … w`). It makes the reading a sequence hands its tail
(`tailDecl := curDecl`) the table's reading of the tail. -/
def SeqTailDecl (D : Decisions) : Prop :=
  ∀ (sc : List DeclInfo) (u w : Term), D.declOf sc (.seq u w) = D.declOf sc w

/-- **The discard of a sequence's first value, on both sides** (NEW; the fragment's `seqI_core`'s and
`seqB_core`'s drop for every value): from the checker's state with the value `v₀` in flight at `T₀`, meeting
`Pre`, related to the reference's state after the first term, whose result `ru` the value means and whose label
is the value's held borrow, renamed: the checker's `dropValue` is matched by the reference's discard (its strict
test `DiscardOk` passes, and `discardEnd` ends the borrow the value holds), with `Pre` and `Rel` after, the mode,
the frames and the top readings kept (`Kept`), the counters only grown. -/
def DropValueG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st₁ s₄ : MState) (v₀ : Value)
    (T₀ : Option Value) (ru : Res) (s₁ : SState) (n bh : Nat),
    0 < st₁.env.size →
    Pre K ρ (st₁.withTempT v₀ T₀) → Rel K ρ φ π (st₁.withTempT v₀ T₀) s₁ → Strict.SGood K.dm K.Γ φ s₁ →
    meanV K ρ (fun l => φ (π l)) ru.2 v₀ = ru.1 → ru.2.label = (Value.heldLabel v₀).map π →
    Runs (Ochr.dropValue n v₀ T₀) st₁ bh () s₄ →
    DiscardOk K φ ru.2 s₁ ∧ (st₁.absTy.size ≤ s₄.absTy.size ∧ st₁.nextLoan ≤ s₄.nextLoan) ∧
      Pre K ρ s₄ ∧ Rel K ρ φ π s₄ (discardEnd ru.2 s₁) ∧ Kept st₁ s₄

namespace SeqGuards

open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)

-- `SeqTailDecl` at the checker's `declOf`: `(); #0` read in the scope `[.other]` is `#0` read there (`.other`),
-- and `#0; ()` is `.unit`
#guard outVal (withLive true (Ochr.declOf 100 false [] [] (.seq .tt (.place (.var 0)))))
    (scopeState LetGuards.stLL [.other]) 100000 ==
  outVal (withLive true (Ochr.declOf 100 false [] [] (.place (.var 0)))) (scopeState LetGuards.stLL [.other]) 100000
#guard outVal (withLive true (Ochr.declOf 100 false [] [] (.seq (.place (.var 0)) .tt)))
    (scopeState LetGuards.stLL [.other]) 100000 == .unit

-- `DropValueG`'s checker half at a concrete discard: `dropValue` of a number keeps the state
#guard isOk (Ochr.dropValue 100 (.succ .zero) (some .tNat)) LetGuards.stLL 100000
#guard let st' := outSt (Ochr.dropValue 100 (.succ .zero) (some .tNat)) LetGuards.stLL 100000
  st'.env.size == LetGuards.stLL.env.size && DecideScope.topReadings st' == DecideScope.topReadings LetGuards.stLL &&
  !st'.copying && !st'.inPlace && !st'.headEval && st'.erasedDepth == 0

end SeqGuards

/-! ## The step -/

section
variable {K : RunCtx} {φ : Future}

/-- **A typed, unerased `u; w`, at `evalCore`, in general.** -/
theorem seq_coreK (hST : SeqTailDecl K.D) (hDV : DropValueG) (hVC : ValsCongrA) (hc : Strict.FundCtx K)
    {ρ : Assignment} {m : Nat} {u w : Term} (ih : IH K φ (m + 3)) :
    CoreSimK K ρ φ (m + 1) (.seq u w) (fun st => 0 < st.env.size) (· = true) := by
  intro st st' typed hint v T? s π hne hty hm hctl htn htd hcd hp hr hS hv hab hhb hnh hfl _ hD bh h
  subst hty
  obtain ⟨st₁, s₄, stW, v₀, T₀, bh₁, bh₃, bh₂, hru, hD₁, hdv, -, hkW, hmeW, htdW, htnW, hrw⟩ :=
    Machine.seqInvD m u w hint st st' bh v T? K.D hD h
  have habu : u.absBelow st.absTy.size := fun σ hσ => hab σ (by simp [Term.anyAtom, hσ])
  have habw : w.absBelow st.absTy.size := fun σ hσ => hab σ (by simp [Term.anyAtom, hσ])
  have hnhu : u.hasHolePrim = false := by simp [Term.hasHolePrim] at hnh; exact hnh.1
  have hnhw : w.hasHolePrim = false := by simp [Term.hasHolePrim] at hnh; exact hnh.2
  -- the step for `u`, from the entry state itself
  have hOu := (ih m (by omega) K.Δ ρ).1 u st st₁ true none v₀ T₀ s π hm (fun _ => htn) hne (.inl htd) hp hr hS
    hv.1 habu (hintBelow_none _) hnhu (fun e => by cases e) hD₁ bh₁ hru
  replace hOu := outK_of_outLK hOu
  rw [htn] at hOu
  obtain ⟨⟨ρ₁, Δ₁, π₁, ru, s₁, he₁, hxu, hmu, hau, hlu, hp₁, hr₁⟩, hK₁⟩ := hOu
  have hxu' : runT K ρ φ false (.plain TyM.err) u s = some (ru, s₁) := hxu
  obtain ⟨-, -, -, hS₁⟩ := Strict.fund_all hc u hv.1 false (.plain TyM.err) s s₁ ru hS hxu'
  -- the discard, on both sides
  obtain ⟨hdok, ⟨hga, hgl⟩, hP₄, hR₄, hK₄⟩ := hDV { K with Δ := Δ₁ } ρ₁ φ π₁ st₁ s₄ v₀ T₀ ru s₁ m bh₃
    (by rw [hK₁.size]; exact hne) hp₁ hr₁ hS₁ hmu hlu hdv
  have hS₂ : Strict.SGood K.dm K.Γ φ (discardEnd ru.2 s₁) := by
    unfold discardEnd; unfold DiscardOk at hdok; split
    · rename_i l hl; rw [hl] at hdok; exact Strict.endLabel_sgood hS₁ _ hdok
    · exact hS₁
  -- the step for `w`, at the extended context
  have hKW : Kept st stW := (hK₁.trans hK₄).trans (Kept.of_kern hkW hmeW)
  have htdW' : stW.tailDecl = none ∨ stW.tailDecl = some (K.D.declOf (DecideScope.topReadings stW) w) :=
    .inr (by rw [htdW, hcd, hKW.top, hST])
  have habW : st.absTy.size ≤ stW.absTy.size := by
    rw [← hkW.absTy]; exact Nat.le_trans he₁.abs hga
  have hagree : ∀ σ, w.anyAtom (· == .abs σ) = true → AgreeA K Δ₁ ρ ρ₁ σ := fun σ hσ => by
    obtain ⟨a, d⟩ := he₁.agree σ (habw σ hσ)
    exact ⟨a.symm, d.symm⟩
  have hOw := (ih m (by omega) Δ₁ ρ₁).1 w stW st' true none v T? (discardEnd ru.2 s₁) π₁
    (hm.of_modeEq hKW.mode) (fun _ => htnW.trans (hctl rfl)) (by rw [hKW.size]; exact hne) htdW'
    (hP₄.of_kern hkW) (hR₄.of_kern hkW) hS₂ (hVC K Δ₁ ρ ρ₁ φ w hagree hv.2) (absBelow_mono habw habW) (hintBelow_none _) hnhw
    (fun e => by cases e) hD bh₂ hrw
  replace hOw := outK_of_outLK hOw
  rw [htnW] at hOw
  obtain ⟨⟨ρ₂, Δ₂, π₂, rw', s₃, he₂, hxw, hmw, haw, hlw, hp₂, hr₂⟩, hK₂⟩ := hOw
  have hxw' : runT K ρ φ st.curTail (.plain TyM.err) w (discardEnd ru.2 s₁) = some (rw', s₃) := by
    rw [runT_congrA K Δ₁ ρ ρ₁ φ _ w _ _ hagree]; exact hxw
  have hext : Ext K ρ π st st' ρ₂ Δ₂ π₂ :=
    ((he₁.grow hga hgl).congr rfl rfl hkW.absTy hkW.nextLoan).trans he₂
  refine ⟨⟨ρ₂, Δ₂, π₂, rw', s₃, hext, ?_, hmw, haw, hlw, hp₂, hr₂⟩, hKW.trans hK₂⟩
  -- the reference's sequence: a typed sequence is not in tail position (`hctl`), so its tail runs at no hint
  have hth : tailHint st.curTail (hintM K ρ hint) = .plain TyM.err := by rw [hctl rfl]; rfl
  rw [runT_seq _ _ u w s hfl]
  simp only [bind, Option.bind]
  rw [hxu']
  simp only
  rw [SM.guardMod_of (show DiscardOk K φ ru.2 s₁ from hdok)]
  simp only
  rw [hth]; exact hxw'

/-- **The step for a typed `;` the table reads as decided data, in general**, with what the run keeps.
ASSUMES 3 facts: `SeqTailDecl` (table), `DropValueG` (part checker, part model), `ValsCongrA` (model); and
`Strict.FundCtx K`. -/
theorem stepSeq_typed (hST : SeqTailDecl K.D) (hDV : DropValueG) (hVC : ValsCongrA) (hc : Strict.FundCtx K) :
    ∀ n, IH K φ n → ∀ (Δ : Nat → TyS) (ρ : Assignment) (u w : Term),
      EvalSimK { K with Δ := Δ } ρ φ n (.seq u w)
        (fun st => 0 < st.env.size ∧ K.D.declOf (DecideScope.topReadings st) (.seq u w) ≠ .any ∧
          (K.D.declOf (DecideScope.topReadings st) (.seq u w)).isProof = false) (· = true) := by
  intro n ih Δ ρ u w
  by_cases hn : n < 3
  · intro st st' typed hint v T? s π _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bh h
    exact absurd h (Machine.evalLow n typed _ hint st st' bh _ hn (fun w e => by cases e))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  have hc' : CoreSimK { K with Δ := Δ } ρ φ (m + 1) (.seq u w)
      (fun st => 0 < st.env.size ∧ K.D.declOf (DecideScope.topReadings st) (.seq u w) ≠ .any ∧
        (K.D.declOf (DecideScope.topReadings st) (.seq u w)).isProof = false) (· = true) :=
    fun st st' typed hint v T? s π hP => seq_coreK (K := { K with Δ := Δ }) hST hDV hVC ⟨hc.globals, hc.sorts⟩ ih
      st st' typed hint v T? s π hP.1
  exact eval_of_coreK (K := { K with Δ := Δ }) Machine.evalInvD
    (fun a b hk ha => ⟨by rw [← ColumnC.size_of_erase hk.env]; exact ha.1,
      by rw [← ColumnC.topReadings_kern hk]; exact ha.2⟩)
    (fun w e => by cases e) (fun f as h e => by cases e) (fun st hst => hst.2) hc'

end

end Ochr.Meaning.Steps.Form.Master
