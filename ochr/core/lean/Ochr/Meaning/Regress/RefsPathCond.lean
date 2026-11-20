import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.PosLib

/-!
# A refinement record is a path condition (built)

`MState.refs` holds the [Split] refinements made in this world (`σ := r`). `State.lean` classed it
as an input of decisions only, never of meanings, and `Good` read no part of it. But the checker
reads it back into the state: a sealed program already generalised in this world is replaced by
its record's unknown with the refinements since substituted (`canonNeutral`, `recordedNeutral`:
`expandRefs refs (.abs σ)`). That value means the program only where the assignment meets the
refinements, which nothing in `Good` said.

The state `S` (`a : Nat ↦ σ₁`; `σ₀, σ₁ : Nat`; the record `⌈0⌉ := σ₀`; the refinement
`σ₀ := S σ₁`) meets every clause of `Good` except the new one at the assignment `ρ₇` (`σ₀ ↦ 0`,
`σ₁ ↦ 7`): the generalisation record holds (`⌈0⌉` means `0`), and nothing asked `σ₀ = S σ₁`
(`good_but_refs`). There `canonNeutral ⌈0⌉` runs to `S σ₁` (kernel-evaluated), which means `8`
where `⌈0⌉` means `0` (`canon_changes_meaning`): `canonNeutral_step_stmt` was false at `S`. With
the clause `TypedAssignment.refs` (each record `σ := r` says `ρ σ = ⟦r⟧`), `S` is not `Good` at
`ρ₇` (`not_good`).
-/

namespace Ochr.Meaning.Regress.RefsPathCond
open Ochr Ochr.Meaning Ochr.Meaning.Steps

def natB : Binding := { hint := ⟨"a"⟩, ty := some .tNat, val := .abs 1 }
/-- `a : Nat ↦ σ₁`; `σ₀ σ₁ : Nat`; `⌈0⌉ := σ₀`; `σ₀ := S σ₁`. -/
def S : MState :=
  { env := #[{ binds := #[natB] }], absTy := #[.tNat, .tNat], nextAbs := 2,
    neutrals := [(.sealed .zero, 0)], refs := [(0, .succ (.abs 1))] }

/-- `σ₀ ↦ 0` (what `⌈0⌉` means), `σ₁ ↦ 7`. -/
def ρ₇ : Assignment := fun σ => if σ = 0 then .el0 Nat 0 else .el0 Nat 7

def outSt {α : Type} (f : M α) (st : MState) (fuel : Nat) : MState :=
  match runMachine f st fuel with
  | (.ok _ s, _, _) => s
  | _ => default
def outVal {α : Type} [Inhabited α] (f : M α) (st : MState) (fuel : Nat) : α :=
  match runMachine f st fuel with
  | (.ok a _, _, _) => a
  | _ => default
def isOk {α : Type} (f : M α) (st : MState) (fuel : Nat) : Bool :=
  match runMachine f st fuel with
  | (.ok _ _, _, _) => true
  | _ => false

theorem runs_out {α : Type} [Inhabited α] (f : M α) (st : MState) (fuel : Nat)
    (h : isOk f st fuel = true) : Runs f st fuel (outVal f st fuel) (outSt f st fuel) := by
  unfold isOk at h; unfold Runs outVal outSt
  rcases e : runMachine f st fuel with ⟨o, left, log⟩
  rw [e] at h
  cases o with
  | ok a s => exact ⟨#[], left, log, (show runMachineL f st fuel #[] = runMachine f st fuel from rfl).trans e⟩
  | fail _ => simp at h
  | exhausted _ => simp at h

def isS1 : Value → Bool
  | .succ (.abs 1) => true
  | _ => false
theorem isS1_eq {v : Value} (h : isS1 v = true) : v = .succ (.abs 1) := by
  match v, h with
  | .succ (.abs 1), _ => rfl

abbrev canon : M Value := Ochr.canonNeutral (.sealed .zero)
theorem ok : isOk canon S 10 = true := by decide +kernel
theorem val : outVal canon S 10 = .succ (.abs 1) := isS1_eq (by decide +kernel)
theorem runs : Runs canon S 10 (.succ (.abs 1)) (outSt canon S 10) := val ▸ runs_out canon S 10 ok

/-- `⌈0⌉` means `0`, its canonical form `S σ₁` means `8`. -/
theorem canon_changes_meaning (K : RunCtx) (φ : Future) (hint : TyS) :
    meanV K ρ₇ φ hint (.succ (.abs 1)) ≠ meanV K ρ₇ φ hint (.sealed .zero) := by
  have e1 : meanV K ρ₇ φ hint (.succ (.abs 1)) = .el0 Nat 8 := by
    simp [meanV, ρ₇, Sem.succ, Sem.asNat, Sem.as]
  have e2 : meanV K ρ₇ φ hint (.sealed .zero) = .el0 Nat 0 := by
    simp only [meanV, run]
    rfl
  rw [e1, e2]
  intro h
  cases h

/-! ## `S` is `Good` at `ρ₇` (every clause but the refinement records) -/

theorem bindAt_S (f i : Nat) (b : Binding) (h : S.env[f]?.bind (fun fr => fr.binds[i]?) = some b) :
    f = 0 ∧ i = 0 ∧ b = natB := by
  rcases f with _ | f <;> rcases i with _ | i
  · simp [S] at h; exact ⟨rfl, rfl, h.symm⟩
  all_goals simp [S] at h

theorem posTyM_S (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (p : Pos) (T : TyM)
    (h : MState.posTyM dm C Γ ρ S p = some T) : p = .bind 0 0 ∧ T = .ty0 Nat := by
  cases p with
  | temp f i => simp [MState.posTyM] at h
  | bind f i =>
    rcases f with _ | f <;> rcases i with _ | i
    · simp [MState.posTyM, S, natB, Value.tyM, Value.mean, Sem.asTy] at h
      exact ⟨rfl, h.symm⟩
    all_goals simp [MState.posTyM, S] at h

theorem absTyM_S (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (σ : Nat) (hσ : σ < 2) :
    MState.absTyM dm C Γ ρ S σ = .ty0 Nat := by
  rcases σ with _ | _ | σ
  · simp [MState.absTyM, S, Value.tyM, Value.mean, Sem.asTy]
  · simp [MState.absTyM, S, Value.tyM, Value.mean, Sem.asTy]
  · omega

theorem mem_ρ₇ (σ : Nat) : ρ₇ σ ∈ₛ .ty0 Nat := by
  unfold ρ₇; split <;> simp [Sem.mem]

/-- The typed assignment's clauses as they stood: each referenced unknown an element of its type,
the generalisation and η records. -/
theorem ta_S (K : RunCtx) :
    (∀ σ, S.Refd σ → σ < S.absTy.size → ρ₇ σ ∈ₛ MState.absTyM K.dm K.M K.Γ ρ₇ S σ) ∧
    (∀ n σ, (n, σ) ∈ S.neutrals →
      ρ₇ σ = Value.mean K.dm K.M K.Γ ρ₇ (fun _ => .err) (.plain (MState.absTyM K.dm K.M K.Γ ρ₇ S σ)) n) ∧
    (∀ σ v, (σ, v) ∈ S.etaRefs →
      ρ₇ σ = Value.mean K.dm K.M K.Γ ρ₇ (fun _ => .err) (.plain (MState.absTyM K.dm K.M K.Γ ρ₇ S σ)) v) := by
  refine ⟨fun σ _ hσ => ?_, fun n σ h => ?_, fun σ v h => by simp [S] at h⟩
  · have hσ' : σ < 2 := hσ
    rw [absTyM_S _ _ _ _ σ hσ']; exact mem_ρ₇ σ
  · simp only [S, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    show ρ₇ 0 = meanV K ρ₇ (fun _ => .err) (.plain (MState.absTyM K.dm K.M K.Γ ρ₇ S 0)) (.sealed .zero)
    simp only [meanV, run]
    rfl

theorem rest_S (K : RunCtx) : Membership K.dm K.M K.Γ ρ₇ S ∧ WF K.dm K.M K.Γ ρ₇ S := by
  have hA : allPos S.env = [.bind 0 0] := by decide +kernel
  have hV : Env.values S.env = [.abs 1] := by rw [Env.values, hA]; rfl
  have h0 : valAt S.env (.bind 0 0) = .abs 1 := rfl
  refine ⟨⟨?_, fun σ _ hσ => ?_, fun G h => by simp [MState.goalM, S] at h⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro φ _ p T hp
    obtain ⟨rfl, rfl⟩ := posTyM_S K.dm K.M K.Γ ρ₇ p T hp
    have e : Env.mean K.dm K.M K.Γ ρ₇ φ S.env (.bind 0 0) = .el0 Nat 7 := rfl
    rw [e]; exact DataModel.pmem_of_mem K.Γ (by simp [Sem.whole]) (by simp [Sem.mem])
  · have hσ' : σ < 2 := hσ
    rw [absTyM_S _ _ _ _ σ hσ']; rfl
  · rw [hA]; intro p hp; simp at hp; subst hp; rw [h0]; decide
  · rw [hA]; intro p hp q hq _ _ _; simp at hp hq; rw [hp, hq]
  · rw [hV]; intro v hv l hl; simp at hv; subst hv; simp [Value.outerLoans] at hl
  · intro l; rw [hV]; simp [Value.outerLoans]
  · exact ⟨fun a => ⟨a, fun b ⟨p, hp, w, hw, _⟩ => by
      rw [hA] at hp; simp at hp; subst hp; rw [h0] at hw; cases hw⟩⟩
  · unfold WF4; rw [hV]; intro v hv; simp at hv; subst hv; decide
  · have h2 : S.absTy.size = 2 := rfl
    rw [h2]
    refine MState.refd_lt S _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hV]; intro v hv σ h; simp at hv; subst hv
      simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h
      omega
    · intro f i b T hb hT σ h
      obtain ⟨_, _, rfl⟩ := bindAt_S f i b hb
      simp [natB] at hT; subst hT; simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h
    · intro f i b P ws j hb hT; obtain ⟨_, _, rfl⟩ := bindAt_S f i b hb; simp [natB] at hT
    · intro G hG; simp [S] at hG
    · intro m σ' h σ hσ
      simp [S] at h; obtain ⟨rfl, rfl⟩ := h
      rcases hσ with rfl | h
      · decide
      · simp [Value.hasAbs, Value.anyAtom, Term.anyAtom, BEq.beq, Value.beq] at h
    · intro σ' v h; simp [S] at h
    · intro σ' T h σ hσ
      rcases σ' with _ | _ | σ'
      all_goals simp [S] at h
      all_goals subst h; simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at hσ
  · intro T hT σ h; simp [S] at hT
    rcases hT with rfl | rfl <;> simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h
  · intro σ r h
    simp [S] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨by decide, fun τ hτ => ?_⟩
    simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at hτ
    show τ < 2; omega
  · rfl
  · rw [hV]; intro v hv l hl; simp at hv; subst hv; simp [Value.loans] at hl
  · intro p T _ f i b _ hb A hA'
    obtain ⟨_, _, rfl⟩ := bindAt_S f i b hb
    simp [natB] at hA'
  · rw [hV]; intro v hv; simp at hv; subst hv; decide
  · intro f i b hb T hT
    obtain ⟨_, _, rfl⟩ := bindAt_S f i b hb
    simp [natB] at hT; subst hT; decide
  · intro T hT; simp [S] at hT; rcases hT with rfl | rfl <;> decide
  · intro G hG; simp [S] at hG
  · intro p hp _; rw [hA] at hp; simp at hp; subst hp; exact ⟨_, rfl⟩
  · intro v hv; rw [hV] at hv; simp at hv; subst hv; rfl
  · intro f i b hb
    obtain ⟨_, _, rfl⟩ := bindAt_S f i b hb
    exact ⟨fun T hT l => by simp [natB] at hT; subst hT; rfl, fun P ws j h => by simp [natB] at h⟩
  · intro T hT l; simp [S] at hT; rcases hT with rfl | rfl <;> rfl
  · intro G hG; simp [S] at hG
  · intro n σ h l; simp [S] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · intro σ v h; simp [S] at h
  · intro k l _ _ _ x hx
    simp [Env.sitesOf, hA, h0, Value.sitesOf] at hx

/-! ## The statement as it stood, refuted; the clause that excludes `S` -/

/-- `Good` as it stood (spine e1b8600e): the typed assignment without the refinement records. -/
def GoodOld (K : RunCtx) (ρ : Assignment) (st : MState) : Prop :=
  ((∀ σ, st.Refd σ → σ < st.absTy.size → ρ σ ∈ₛ MState.absTyM K.dm K.M K.Γ ρ st σ) ∧
    (∀ n σ, (n, σ) ∈ st.neutrals →
      ρ σ = Value.mean K.dm K.M K.Γ ρ (fun _ => .err) (.plain (MState.absTyM K.dm K.M K.Γ ρ st σ)) n) ∧
    (∀ σ v, (σ, v) ∈ st.etaRefs →
      ρ σ = Value.mean K.dm K.M K.Γ ρ (fun _ => .err) (.plain (MState.absTyM K.dm K.M K.Γ ρ st σ)) v)) ∧
  Membership K.dm K.M K.Γ ρ st ∧ WF K.dm K.M K.Γ ρ st

/-- `canonNeutral_step_stmt` as it stood, over `GoodOld`. -/
def canonNeutral_step_stmt_old (K : RunCtx) (ρ : Assignment) (_fuel : Nat) : Prop :=
  ∀ (st st' : MState) (v v' : Value) (hint : TyS)
    (_hg : GoodOld K ρ st) (_hctx : CtxOk K ρ st) (bh : Nat) (_h : Runs (Ochr.canonNeutral v) st bh v' st'),
    (∀ φ, meanV K ρ φ hint v' = meanV K ρ φ hint v) ∧ st'.core = st.core

theorem goodOld_S (K : RunCtx) : GoodOld K ρ₇ S := ⟨ta_S K, rest_S K⟩

/-- **`canonNeutral_step_stmt` as it stood is false** at every context admitting `S`. -/
theorem canon_step_false (K : RunCtx) (hctx : CtxOk K ρ₇ S) : ¬ canonNeutral_step_stmt_old K ρ₇ 10 := by
  intro h
  obtain ⟨hm, -⟩ := h S _ (.sealed .zero) (.succ (.abs 1)) (.plain (.ty0 Nat)) (goodOld_S K) hctx 10 runs
  exact canon_changes_meaning K (fun _ => .err) _ (hm (fun _ => .err))

/-- **With the refinement records a path condition, `S` is not `Good` at `ρ₇`**: the record
`σ₀ := S σ₁` asks `0 = 8`. -/
theorem not_good (K : RunCtx) : ¬ Good K.dm K.M K.Γ ρ₇ S := by
  rintro ⟨ht, -, -⟩
  have h := ht.refs 0 (.succ (.abs 1)) (by simp [S])
  rw [absTyM_S _ _ _ _ 0 (by decide)] at h
  have e : Value.mean K.dm K.M K.Γ ρ₇ (fun _ => .err) (.plain (.ty0 Nat)) (.succ (.abs 1)) = .el0 Nat 8 := by
    simp [Value.mean, ρ₇, Sem.succ, Sem.asNat, Sem.as]
  rw [e] at h
  simp [ρ₇] at h

end Ochr.Meaning.Regress.RefsPathCond
