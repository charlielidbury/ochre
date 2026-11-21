import Ochr.Meaning.Rules.Sound
import Ochr.Meaning.Regress.GenNeutralContent
import Ochr.Meaning.Consistency

/-!
# The rules trial: two of the area's statements are false (kernel-checked)

Found by writing part A, whose rules each list what their soundness needs.

1. **`conv_sound_stmt` is false** (`conv_sound_stmt_false`). Conversion is untyped and the
   model is typed: the machine's [Conv-unit] rewrites `And(True, Nat)` to `Nat` wherever it meets
   it, and an `Eq` whose side is that ill-typed value is a member of `Prop` whatever its sides
   mean. `Eq(Nat, And(True, Nat), Nat)` and `Eq(Nat, Nat, Nat)` are convertible to the checker
   (no state change), both are members of `Prop`, and they mean different propositions. The
   statement's only hypotheses on the values are membership at the top; what is missing is a
   typing fact about the values inside (part A's `SynSound`), which no step statement has.
2. **`mkEqM_step_stmt` is false** (`mkEqM_step_stmt_false`): `mkEqM` answers `False` for `⊥`
   against any value that is not `⊥` ([Eq-disj] at `⊥`, D84), and the statement has no
   hypothesis on the sides, so a side that means `moved` without being `⊥` (here an unknown the
   state does not reference, which the assignment sends to `moved`; equally a borrow of `⊥`)
   makes the computed `False` mean the true `moved = moved`. Part A's `eqTo_sound` has the
   hypothesis that a side that is not `⊥` does not mean `moved`, and membership of the sides,
   which the statement also lacks.

Both are stated at every run context that admits the start state (`CtxOk`), as
`Regress/UntypedNil` does: the existence of a data model is the chain's open leaf.
-/

namespace Ochr.Meaning.Rules.Counter
open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Regress.GenNeutralContent

/-- `TyM.prop P = TyM.prop Q` with `Q` true makes `P` true. -/
theorem prop_true_of_eq {P Q : Prop} (h : TyM.prop P = TyM.prop Q) (hq : Q) : P := by
  unfold TyM.prop at h
  injection h with hA _
  exact (cast hA.symm (PLift.up hq)).down

theorem err_ne_nat : TyM.err ≠ TyM.nat := by
  intro h
  unfold TyM.err TyM.nat at h
  injection h with hA _
  exact (cast hA.symm (0 : Nat)).elim

/-! ## 1. `conv_sound_stmt` -/

/-- `Eq(Nat, And(True, Nat), Nat)`: an `Eq` whose left side is an ill-typed `And`. -/
def vBad : Value := .tEq .tNat (.tInd "And" [vTrue, .tNat]) .tNat
/-- `Eq(Nat, Nat, Nat)`. -/
def vGood : Value := .tEq .tNat .tNat .tNat

/-- The checker's comparison accepts them and changes nothing: the `Eq` clause compares the sides,
and the unit laws rewrite `And(True, Nat)` to `Nat`. -/
theorem runs_conv : Runs (Ochr.conv 5 vBad vGood) S 10 true S := ⟨#[], _, _, rfl⟩

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

theorem mean_vBad (hΓ : K.Γ = []) (hint : TyS) :
    meanV K ρ φ hint vBad = .ty (TyM.prop (Sem.ty TyM.err = Sem.ty TyM.nat)) := by
  -- STRICT experiment: FALSE now. The strict `Eq` means `err` (its left side, a type, is no
  -- member of `Nat`), so `vBad` is no member of `Prop`: counterexample 1 dies
  sorry

theorem mean_vGood (hint : TyS) :
    meanV K ρ φ hint vGood = .ty (TyM.prop (Sem.ty TyM.nat = Sem.ty TyM.nat)) := by
  -- STRICT experiment: FALSE now, for the same reason (`Nat` is no member of `Nat`)
  sorry

/-- A proposition is a member of `Prop`. -/
theorem prop_pmem (P : Prop) : DataModel.pmem K.dm.read K.Γ (.ty (TyM.prop P)) (TyM.univ 0) :=
  DataModel.pmem_of_mem K.dm.read K.Γ (by simp [Sem.whole]) ⟨ULift.up P, rfl⟩

/-- **`conv_sound_stmt` is false** at every run context that admits `S` (`a : Nat ↦ 0`) and every
assignment, future and fuel from 5: the two `Eq`s above are convertible to the checker, members
of `Prop`, and mean `⟦And(True, Nat)⟧ = ⟦Nat⟧` (false: `K.Γ` is `S`'s, empty, so the `And` means
the error type; with the library declared it means a proposition, still not `Nat`) and
`⟦Nat⟧ = ⟦Nat⟧`. -/
theorem conv_sound_stmt_false (hctx : CtxOk K ρ S) : ¬ conv_sound_stmt K ρ φ 5 := by
  intro h
  have hΓ : K.Γ = [] := hctx.inds
  have hv := prop_pmem K (Sem.ty TyM.err = Sem.ty TyM.nat)
  have hw := prop_pmem K (Sem.ty TyM.nat = Sem.ty TyM.nat)
  rw [← mean_vBad K ρ φ hΓ (.plain (TyM.univ 0))] at hv
  rw [← mean_vGood K ρ φ (.plain (TyM.univ 0))] at hw
  obtain ⟨he, -⟩ := h S S vBad vGood (TyM.univ 0) (good_S K ρ) hctx hv hw 10 runs_conv
  rw [mean_vBad K ρ φ hΓ, mean_vGood] at he
  injection he with he
  exact err_ne_nat (Sem.ty.inj (prop_true_of_eq he rfl))

/-! ## 2. `mkEqM_step_stmt` -/

/-- The library's `False`. -/
def dFalse : IndDecl := { name := "False", sort := 0 }

/-- `a : Nat ↦ 0` with the library's `False` declared. -/
def SF : MState := { env := #[{ binds := #[natB] }], inds := [dFalse] }

/-! `SF` is `Good` at every assignment: `GenNeutralContent.good_S`'s proof, at `SF`. -/

theorem bindAt_SF (f i : Nat) (b : Binding) (h : SF.env[f]?.bind (fun fr => fr.binds[i]?) = some b) :
    f = 0 ∧ i = 0 ∧ b = natB := by
  rcases f with _ | f <;> rcases i with _ | i
  · simp [SF] at h; exact ⟨rfl, rfl, h.symm⟩
  all_goals simp [SF] at h

theorem posTyM_SF (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (p : Pos) (T : TyM)
    (h : MState.posTyM dm C Γ ρ SF p = some T) : p = .bind 0 0 ∧ T = TyM.nat := by
  cases p with
  | temp f i => simp [MState.posTyM] at h
  | bind f i =>
    rcases f with _ | f <;> rcases i with _ | i
    · simp [MState.posTyM, SF, natB, Value.tyM, Value.mean, Sem.asTy] at h
      exact ⟨rfl, h.symm⟩
    all_goals simp [MState.posTyM, SF] at h

theorem good_SF (K : RunCtx) (ρ : Assignment) : Good K.dm K.M K.Γ ρ SF := by
  have hA : allPos SF.env = [.bind 0 0] := by decide +kernel
  have hV : Env.values SF.env = [.zero] := by rw [Env.values, hA]; rfl
  refine ⟨⟨fun σ _ h => by simp [SF] at h, fun n σ h => by simp [SF] at h, fun σ v h => by simp [SF] at h,
      fun σ r h => by simp [SF] at h⟩,
    ⟨?_, fun σ _ h => by simp [SF] at h, fun G h => by simp [MState.goalM, SF] at h⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro φ _ p T hp
    obtain ⟨rfl, rfl⟩ := posTyM_SF K.dm K.M K.Γ ρ p T hp
    have e : Env.mean K.dm K.M K.Γ ρ φ SF.env (.bind 0 0) = .el0 Nat 0 := rfl
    rw [e]; exact DataModel.pmem_of_mem K.dm.read K.Γ (by simp [Sem.whole]) (by simp [Sem.mem, TyM.nat, Code0.enc])
  · rw [hA]; intro p hp; simp at hp; subst hp; show ¬ (Value.zero.hasBorrow = true); decide
  · rw [hA]; intro p hp q hq _ _ _; simp at hp hq; rw [hp, hq]
  · rw [hV]; intro v hv l hl; simp at hv; subst hv; simp [Value.outerLoans] at hl
  · intro l; rw [hV]; simp [Value.outerLoans]
  · have h0 : valAt SF.env (.bind 0 0) = .zero := rfl
    exact ⟨fun a => ⟨a, fun b ⟨p, hp, w, hw, _⟩ => by
      rw [hA] at hp; simp at hp; subst hp; rw [h0] at hw; cases hw⟩⟩
  · unfold WF4; rw [hV]; intro v hv; simp at hv; subst hv; decide
  · exact MState.refd_lt SF _
      (by rw [hV]; intro v hv σ h; simp at hv; subst hv; simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h)
      (fun f i b T hb hT σ h => by
        obtain ⟨_, _, rfl⟩ := bindAt_SF f i b hb
        simp [natB] at hT; subst hT; simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h)
      (fun f i b P ws j hb hT => by obtain ⟨_, _, rfl⟩ := bindAt_SF f i b hb; simp [natB] at hT)
      (fun G hG => by simp [SF] at hG) (fun m σ' h => by simp [SF] at h) (fun σ' v h => by simp [SF] at h)
      (fun σ' T h => by simp [SF] at h)
  · intro T hT; simp [SF] at hT
  · intro σ r h; simp [SF] at h
  · simp [SF]
  · rw [hV]; intro v hv l hl; simp at hv; subst hv; simp [Value.loans] at hl
  · intro p T _ f i b _ hb A hA'
    obtain ⟨_, _, rfl⟩ := bindAt_SF f i b hb
    simp [natB] at hA'
  · rw [hV]; intro v hv; simp at hv; subst hv; decide
  · intro f i b hb T hT
    obtain ⟨_, _, rfl⟩ := bindAt_SF f i b hb
    simp [natB] at hT; subst hT; decide
  · intro T hT; simp [SF] at hT
  · intro G hG; simp [SF] at hG
  · intro p hp _; rw [hA] at hp; simp at hp; subst hp; exact ⟨_, rfl⟩
  · intro v hv; rw [hV] at hv; simp at hv; subst hv; rfl
  · intro f i b hb
    obtain ⟨_, _, rfl⟩ := bindAt_SF f i b hb
    exact ⟨fun T hT l => by simp [natB] at hT; subst hT; rfl, fun P ws j h => by simp [natB] at h⟩
  · intro T hT; simp [SF] at hT
  · intro G hG; simp [SF] at hG
  · intro n σ h; simp [SF] at h
  · intro σ v h; simp [SF] at h
  · have h0 : valAt SF.env (.bind 0 0) = .zero := rfl
    refine ⟨?_, ?_, ?_⟩
    · intro k l _ _ x hx
      simp [Env.sitesOf, hA, h0, Value.sitesOf] at hx
    · intro pos path _ l _ x hx
      simp [Env.sitesOf, hA, h0, Value.sitesOf] at hx
    · refine ⟨?_, ?_⟩
      · intro v hv l; rw [hV] at hv; simp at hv; subst hv; rfl
      · intro v hv; rw [hV] at hv; simp at hv; subst hv; rfl


/-- `Eq(Nat, ⊥, σ₀)` computes to `False` ([Eq-disj] at `⊥`), and changes nothing. -/
theorem runs_mkEqM : Runs (Ochr.mkEqM 5 .tNat .bot (.abs 0)) SF 10 vFalse SF := ⟨#[], _, _, rfl⟩

/-- **`mkEqM_step_stmt` is false** at every run context that admits `SF` and every assignment
sending the unknown `σ₀` (which `SF` does not reference) to `moved`: the computed `False` means the
false proposition (`Assembly.false_means_empty`), the statement asks it to mean `⟦⊥⟧ = ⟦σ₀⟧`, which
is `moved = moved`. -/
theorem mkEqM_step_stmt_false (hctx : CtxOk K ρ SF) (h0 : ρ 0 = .moved) : ¬ mkEqM_step_stmt K ρ φ 5 := by
  intro h
  have hΓ : K.Γ = [dFalse] := hctx.inds
  have hcov : K.dm.covers dFalse := hctx.covers dFalse (by rw [hΓ]; simp)
  have hF := Assembly.false_means_empty K.dm dFalse ⟨rfl, rfl, rfl⟩ hcov
  obtain ⟨-, ρ', Δ', D', -, hP⟩ := h SF SF .tNat .bot (.abs 0) vFalse (good_SF K ρ) hctx
    (fun _ => rfl) 10 runs_mkEqM
  have e := hP φ (.plain TyM.err)
  have lhs : meanV { K with Δ := Δ', D := D' } ρ' φ (.plain TyM.err) vFalse = .ty (TyM.prop False) := by
    show meanV { K with Δ := Δ', D := D' } ρ' φ (.plain TyM.err) (.tInd "False" []) = _
    simp only [meanV, hΓ]
    simp [dFalse, meanParams, DataModel.strictInd, DataModel.paramsOk]
    exact hF
  rw [lhs] at e
  simp only [meanV, h0] at e
  injection e with e
  exact prop_true_of_eq e trivial

end

end Ochr.Meaning.Rules.Counter

#print axioms Ochr.Meaning.Rules.Counter.conv_sound_stmt_false
#print axioms Ochr.Meaning.Rules.Counter.mkEqM_step_stmt_false
