import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.PosLib

/-!
# Generalising a value that is not the place's content (built)

`generalizeNeutral_step_stmt` (and the simulation form `Steps/DropOne.generalizeNeutral_sim`) asked
nothing of the generalised value `n`: no hypothesis says it is the content of the place `p`, or
holds no loan. The checker's `generalizeNeutral fuel p n` types the fresh unknown `σ` by `p`'s
type and records `n := σ`, so the record makes `σ` referenced and the typed assignment owes
`⟦n⟧ ∈ ⟦type of p⟧`, which nothing gives.

From `a : Nat ↦ 0` (a `Good` state at every assignment, `good_S`), generalising `⋆` at `a` runs
(`runs`, evaluated by the kernel) and records `⋆ := σ₀ : Nat`; at the statement's assignment
`ρ.ext σ₀ ⟦⋆⟧` the state is not `Good`, since `⋆` means a proof and not a number (`not_good`). So
the statement is false at every context that admits the start state (`step_false`).

The callers never generalise such a value: `evalMatch` generalises the place's content
(`matchContent p`), `movedPlace` the program at the prefix it follows. The fix adds the
hypotheses the callers have: `n` is the content of `p`, and holds no loan.
-/

namespace Ochr.Meaning.Regress.GenNeutralContent
open Ochr Ochr.Meaning Ochr.Meaning.Steps

def natB : Binding := { hint := ⟨"a"⟩, ty := some .tNat, val := .zero }
/-- `a : Nat ↦ 0`. -/
def S : MState := { env := #[{ binds := #[natB] }] }

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

/-- The statement as it stood (spine c319b2ee): no hypothesis on `n`. -/
def generalizeNeutral_step_stmt_old (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (n : Value) (σ : Nat)
    (_hg : Good K.dm K.M K.Γ ρ st) (_hctx : CtxOk K ρ st)
    (bh : Nat) (_h : Runs (Ochr.generalizeNeutral fuel p n) st bh σ st'),
    let ρ' := ρ.ext σ (meanV K ρ φ (.plain (MState.absTyM K.dm K.M K.Γ ρ st' σ)) n)
    Exact (MState.mean K.dm K.M K.Γ ρ' st') (MState.mean K.dm K.M K.Γ ρ st) ∧
    Good K.dm K.M K.Γ ρ' st'

/-- The run: generalise `⋆` at `a`. -/
abbrev gen : M Nat := Ochr.generalizeNeutral 10 (.var 0) .proof
abbrev S' : MState := outSt gen S 10

def isRec : List (Value × Nat) → Bool
  | [(.proof, 0)] => true
  | _ => false
def isNatTy : List Value → Bool
  | [.tNat] => true
  | _ => false

theorem isRec_eq {l : List (Value × Nat)} (h : isRec l = true) : l = [(.proof, 0)] := by
  match l, h with
  | [(.proof, 0)], _ => rfl
theorem isNatTy_eq {l : List Value} (h : isNatTy l = true) : l = [.tNat] := by
  match l, h with
  | [.tNat], _ => rfl

theorem ok : isOk gen S 10 = true := by decide +kernel
theorem val : outVal gen S 10 = 0 := by decide +kernel
theorem rec_S' : S'.neutrals = [(.proof, 0)] := isRec_eq (by decide +kernel)
theorem absTy_S' : S'.absTy.toList = [.tNat] := isNatTy_eq (by decide +kernel)

theorem runs : Runs gen S 10 0 S' := val ▸ runs_out gen S 10 ok

/-- At the statement's assignment, the state after the run is not `Good`: `σ₀` is referenced by
its record and typed `Nat`, and `⟦⋆⟧` is no number. -/
theorem not_good (K : RunCtx) (ρ : Assignment) (φ : Future) :
    ¬ Good K.dm K.M K.Γ (ρ.ext 0 (meanV K ρ φ (.plain (MState.absTyM K.dm K.M K.Γ ρ S' 0)) .proof)) S' := by
  rintro ⟨ht, -, -⟩
  have hr : S'.Refd 0 := .neutral .proof 0 (by rw [rec_S']; simp) (.inl rfl)
  have hsz : 0 < S'.absTy.size := by
    rw [← Array.length_toList, absTy_S']; decide
  have h0 : S'.absTy[0]? = some .tNat := by
    rw [← Array.getElem?_toList, absTy_S']; rfl
  have hm := ht.mem 0 hr hsz
  simp only [MState.absTyM, h0, Assignment.ext] at hm
  exact absurd hm (by simp [meanV, Value.tyM, Value.mean, Sem.asTy, Sem.mem])

/-! ## The start state is `Good` at every assignment -/

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

theorem good_S (K : RunCtx) (ρ : Assignment) : Good K.dm K.M K.Γ ρ S := by
  have hA : allPos S.env = [.bind 0 0] := by decide +kernel
  have hV : Env.values S.env = [.zero] := by rw [Env.values, hA]; rfl
  refine ⟨⟨fun σ _ h => by simp [S] at h, fun n σ h => by simp [S] at h, fun σ v h => by simp [S] at h,
      fun σ r h => by simp [S] at h⟩,
    ⟨?_, fun σ _ h => by simp [S] at h, fun G h => by simp [MState.goalM, S] at h⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro φ _ p T hp
    obtain ⟨rfl, rfl⟩ := posTyM_S K.dm K.M K.Γ ρ p T hp
    have e : Env.mean K.dm K.M K.Γ ρ φ S.env (.bind 0 0) = .el0 Nat 0 := rfl
    rw [e]; exact DataModel.pmem_of_mem K.Γ (by simp [Sem.whole]) (by simp [Sem.mem])
  · rw [hA]; intro p hp; simp at hp; subst hp; show ¬ (Value.zero.hasBorrow = true); decide
  · rw [hA]; intro p hp q hq _ _ _; simp at hp hq; rw [hp, hq]
  · rw [hV]; intro v hv l hl; simp at hv; subst hv; simp [Value.outerLoans] at hl
  · intro l; rw [hV]; simp [Value.outerLoans]
  · have h0 : valAt S.env (.bind 0 0) = .zero := rfl
    exact ⟨fun a => ⟨a, fun b ⟨p, hp, w, hw, _⟩ => by
      rw [hA] at hp; simp at hp; subst hp; rw [h0] at hw; cases hw⟩⟩
  · unfold WF4; rw [hV]; intro v hv; simp at hv; subst hv; decide
  · exact MState.refd_lt S _
      (by rw [hV]; intro v hv σ h; simp at hv; subst hv; simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h)
      (fun f i b T hb hT σ h => by
        obtain ⟨_, _, rfl⟩ := bindAt_S f i b hb
        simp [natB] at hT; subst hT; simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h)
      (fun f i b P ws j hb hT => by obtain ⟨_, _, rfl⟩ := bindAt_S f i b hb; simp [natB] at hT)
      (fun G hG => by simp [S] at hG) (fun m σ' h => by simp [S] at h) (fun σ' v h => by simp [S] at h)
      (fun σ' T h => by simp [S] at h)
  · intro T hT; simp [S] at hT
  · intro σ r h; simp [S] at h
  · simp [S]
  · rw [hV]; intro v hv l hl; simp at hv; subst hv; simp [Value.loans] at hl
  · intro p T _ f i b _ hb A hA'
    obtain ⟨_, _, rfl⟩ := bindAt_S f i b hb
    simp [natB] at hA'
  · rw [hV]; intro v hv; simp at hv; subst hv; decide
  · intro f i b hb T hT
    obtain ⟨_, _, rfl⟩ := bindAt_S f i b hb
    simp [natB] at hT; subst hT; decide
  · intro T hT; simp [S] at hT
  · intro G hG; simp [S] at hG
  · intro p hp _; rw [hA] at hp; simp at hp; subst hp; exact ⟨_, rfl⟩
  · intro v hv; rw [hV] at hv; simp at hv; subst hv; rfl
  · intro f i b hb
    obtain ⟨_, _, rfl⟩ := bindAt_S f i b hb
    exact ⟨fun T hT l => by simp [natB] at hT; subst hT; rfl, fun P ws j h => by simp [natB] at h⟩
  · intro T hT; simp [S] at hT
  · intro G hG; simp [S] at hG
  · intro n σ h; simp [S] at h
  · intro σ v h; simp [S] at h
  · intro k l _ _ x hx
    have h0 : valAt S.env (.bind 0 0) = .zero := rfl
    simp [Env.sitesOf, hA, h0, Value.sitesOf] at hx

/-- **`generalizeNeutral_step_stmt` as it stood is false** at fuel 10, at every context that admits
the start state: the run's end state is not `Good` at the statement's assignment. -/
theorem step_false (K : RunCtx) (ρ : Assignment) (φ : Future) (hctx : CtxOk K ρ S) :
    ¬ generalizeNeutral_step_stmt_old K ρ φ 10 := by
  intro h
  exact not_good K ρ φ (h S S' (.var 0) .proof 0 (good_S K ρ) hctx 10 runs).2

/-! ## (WF6) as first written is not kept

With `absTy.size ≤ nextAbs`, the state `S₁` (`S` with the counter at `1` and no unknown typed) met
the clause; generalising `a`'s own content `0` (so the fixed statement's hypotheses hold) names the
unknown `σ₁` but types it at index `0`, and `a` then holds `σ₁` with only one unknown typed. The
clause is now `absTy.size = nextAbs` (`WF.lean`). -/

/-- (WF6) as first written. -/
def WF6le (st : MState) : Prop :=
  (∀ v ∈ Env.values st.env, ∀ σ, v.hasAbs σ → σ < st.absTy.size) ∧
  (∀ T ∈ st.absTy.toList, ∀ σ, T.hasAbs σ → σ < st.absTy.size) ∧
  (∀ G, st.goal = some G → ∀ σ, G.hasAbs σ → σ < st.absTy.size) ∧
  st.absTy.size ≤ st.nextAbs ∧
  ∀ v ∈ Env.values st.env, ∀ l ∈ v.loans, l < st.nextLoan

def S₁ : MState := { S with nextAbs := 1 }
abbrev gen₁ : M Nat := Ochr.generalizeNeutral 10 (.var 0) .zero
abbrev S₁' : MState := outSt gen₁ S₁ 10

/-- The fixed statement's hypotheses: `0` is `a`'s content, and holds no loan. -/
theorem content₁ : Runs (Ochr.content (.var 0)) S₁ 0 .zero S₁ := ⟨#[], _, _, rfl⟩
theorem free₁ (l : Nat) : Value.zero.hasLoan l = false := rfl

theorem ok₁ : isOk gen₁ S₁ 10 = true := by decide +kernel
theorem val₁ : outVal gen₁ S₁ 10 = 1 := by decide +kernel
theorem runs₁ : Runs gen₁ S₁ 10 1 S₁' := val₁ ▸ runs_out gen₁ S₁ 10 ok₁

theorem wf6_le_not_kept : WF6le S₁ ∧ ¬ WF6le S₁' := by
  have hA : allPos S₁.env = [.bind 0 0] := by decide +kernel
  have hV : Env.values S₁.env = [.zero] := by rw [Env.values, hA]; rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hV]; intro v hv σ h; simp at hv; subst hv; simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h
  · intro T hT; simp [S₁, S] at hT
  · intro G hG; simp [S₁, S] at hG
  · simp [S₁, S]
  · rw [hV]; intro v hv l hl; simp at hv; subst hv; simp [Value.loans] at hl
  · rintro ⟨h1, -⟩
    have hv : (Env.values S₁'.env).map (fun v => v.hasAbs 1) = [true] := by decide +kernel
    have hsz : S₁'.absTy.size = 1 := by decide +kernel
    obtain ⟨v, hv, hv1⟩ : ∃ v ∈ Env.values S₁'.env, v.hasAbs 1 = true := by
      rcases e : Env.values S₁'.env with _ | ⟨v, vs⟩
      · rw [e] at hv; cases hv
      · rw [e] at hv; simp only [List.map_cons, List.cons.injEq] at hv
        exact ⟨v, by simp, hv.1⟩
    have := h1 v hv 1 hv1
    omega

end Ochr.Meaning.Regress.GenNeutralContent
