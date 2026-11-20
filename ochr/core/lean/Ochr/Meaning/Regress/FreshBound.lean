import Ochr.Meaning.Steps.DropOneAsm
import Ochr.Meaning.PosLib

/-!
# A record naming the counter (built)

(WF6) bounded the unknowns of Ω's values, of Δ's types and of the goal by the counter, but not those
of stored and deferred types or of the records, though its docstring said stored types were
bounded. A record naming the counter itself then met every clause: in `S` (`a : Nat ↦ 0`, no
unknown typed, the counter at `0`, the record `0 := σ₀`), the path condition `ρ σ₀ = ⟦0⌉` is met at
`ρ₀` (everything `0`), and nothing else reads `σ₀` (`goodOld_S`).

A fresh unknown (`freshAbs`) is the counter, `σ₀`. `freshAbs_sim` concluded `Good` at `ρ₀.ext σ₀ v`
for ANY `v` (nothing in the state names the fresh unknown, it said): at `v = 1` the record asks
`1 = 0` (`not_good_ext`, at every `Δ'`), so the statement was false at every context that admits
`S` (`fresh_false`; the type `Nat` and the program `0` meet `GenTy`, `genTy_S`).

The checker never names an unknown at or above its counter (fresh names are never reused). (WF6)
now bounds every unknown `MState.Refd` names and every [Split] refinement's (`WF.lean`), which
excludes `S` (`not_wf6`).
-/

namespace Ochr.Meaning.Regress.FreshBound
open Ochr Ochr.Meaning Ochr.Meaning.Steps

def natB : Binding := { hint := ⟨"a"⟩, ty := some .tNat, val := .zero }
/-- `a : Nat ↦ 0`; no unknown typed; the record `0 := σ₀`. -/
def S : MState := { env := #[{ binds := #[natB] }], neutrals := [(.zero, 0)] }

/-- Everything `0`. -/
def ρ₀ : Assignment := fun _ => .el0 Nat 0

/-- (WF6) as it stood (spine f3a24eda). -/
def WF6old (st : MState) : Prop :=
  (∀ v ∈ Env.values st.env, ∀ σ, v.hasAbs σ → σ < st.absTy.size) ∧
  (∀ T ∈ st.absTy.toList, ∀ σ, T.hasAbs σ → σ < st.absTy.size) ∧
  (∀ G, st.goal = some G → ∀ σ, G.hasAbs σ → σ < st.absTy.size) ∧
  st.absTy.size = st.nextAbs ∧
  ∀ v ∈ Env.values st.env, ∀ l ∈ v.loans, l < st.nextLoan

/-- `Good` as it stood: (WF6) in its old form. -/
def GoodOld (K : RunCtx) (ρ : Assignment) (st : MState) : Prop :=
  TypedAssignment K.dm K.M K.Γ ρ st ∧ Membership K.dm K.M K.Γ ρ st ∧
  (WF1 st.env ∧ WF2 st.env ∧ WF3 st.env ∧ WF4 st.env ∧ WF6old st ∧ WF7 K.dm K.M K.Γ ρ st ∧ WF8 st ∧
    WF9 K.dm K.M K.Γ ρ st ∧ WF10 K.Γ st ∧ WF11 st ∧ WF12 st.env)

theorem bindAt_S (f i : Nat) (b : Binding) (h : S.env[f]?.bind (fun fr => fr.binds[i]?) = some b) :
    f = 0 ∧ i = 0 ∧ b = natB := by
  rcases f with _ | f <;> rcases i with _ | i
  · simp [S] at h; exact ⟨rfl, rfl, h.symm⟩
  all_goals simp [S] at h

theorem posTyM_S (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (p : Pos) (T : TyM)
    (h : MState.posTyM dm C Γ ρ S p = some T) : p = .bind 0 0 ∧ T = TyM.nat := by
  cases p with
  | temp f i => simp [MState.posTyM] at h
  | bind f i =>
    rcases f with _ | f <;> rcases i with _ | i
    · simp [MState.posTyM, S, natB, Value.tyM, Value.mean, Sem.asTy] at h
      exact ⟨rfl, h.symm⟩
    all_goals simp [MState.posTyM, S] at h

theorem hA : allPos S.env = [.bind 0 0] := by decide +kernel
theorem hV : Env.values S.env = [.zero] := by rw [Env.values, hA]; rfl

/-- `S` met every clause of `Good` as it stood, at `ρ₀`. -/
theorem goodOld_S (K : RunCtx) : GoodOld K ρ₀ S := by
  refine ⟨⟨fun σ _ h => by simp [S] at h, fun n σ h => ?_, fun σ v h => by simp [S] at h,
      fun σ r h => by simp [S] at h⟩,
    ⟨?_, fun σ _ h => by simp [S] at h, fun G h => by simp [MState.goalM, S] at h⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [S, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · intro φ _ p T hp
    obtain ⟨rfl, rfl⟩ := posTyM_S K.dm K.M K.Γ ρ₀ p T hp
    have e : Env.mean K.dm K.M K.Γ ρ₀ φ S.env (.bind 0 0) = .el0 Nat 0 := rfl
    rw [e]; exact DataModel.pmem_of_mem K.Γ (by simp [Sem.whole]) (by simp [Sem.mem, TyM.nat, Code0.enc])
  · rw [hA]; intro p hp; simp at hp; subst hp; show ¬ (Value.zero.hasBorrow = true); decide
  · rw [hA]; intro p hp q hq _ _ _; simp at hp hq; rw [hp, hq]
  · rw [hV]; intro v hv l hl; simp at hv; subst hv; simp [Value.outerLoans] at hl
  · intro l; rw [hV]; simp [Value.outerLoans]
  · have h0 : valAt S.env (.bind 0 0) = .zero := rfl
    exact ⟨fun a => ⟨a, fun b ⟨p, hp, w, hw, _⟩ => by
      rw [hA] at hp; simp at hp; subst hp; rw [h0] at hw; cases hw⟩⟩
  · unfold WF4; rw [hV]; intro v hv; simp at hv; subst hv; decide
  · rw [hV]; intro v hv σ h; simp at hv; subst hv; simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h
  · intro T hT; simp [S] at hT
  · intro G hG; simp [S] at hG
  · rfl
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
  · intro n σ h l
    simp only [S, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · intro σ v h; simp [S] at h
  · intro k l _ _ x hx
    have h0 : valAt S.env (.bind 0 0) = .zero := rfl
    simp [Env.sitesOf, hA, h0, Value.sitesOf] at hx

/-- The type `Nat` and the program `0` meet `GenTy` at `S`. -/
theorem genTy_S (K : RunCtx) : GenTy K ρ₀ S .tNat .zero where
  abs τ h := by simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h
  nabs τ h := by simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h
  loanFree l := rfl
  refOk := rfl
  level := by simp [Value.tyM, Value.mean, Sem.asTy, TyM.level, TyM.nat, Code0.level]
  mem := by simp [Value.tyM, Value.mean, Sem.asTy, meanV, Sem.mem, TyM.nat, Code0.enc]

/-- The state after the fresh unknown: `σ₀ : Nat`. -/
def S' : MState := { S with nextAbs := S.nextAbs + 1, absTy := S.absTy.push .tNat }

/-- At `ρ₀.ext σ₀ 1` the record `0 := σ₀` asks `1 = 0`, at every `Δ'`. -/
theorem not_good_ext (K : RunCtx) (Δ' : Nat → TyS) :
    ¬ Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ (ρ₀.ext S.nextAbs (.el0 Nat 1)) S' := by
  rintro ⟨ta, -, -⟩
  have h := ta.neutral .zero 0 (by simp [S', S])
  have e : Value.mean K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ (ρ₀.ext S.nextAbs (.el0 Nat 1)) (fun _ => .err)
      (.plain (MState.absTyM K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ (ρ₀.ext S.nextAbs (.el0 Nat 1)) S' 0)) .zero
      = .el0 Nat 0 := rfl
  rw [e] at h
  simp [Assignment.ext, S] at h

/-- `freshAbs_sim` as it stood, over `GoodOld` (its `Good` conclusion; the others are not needed). -/
def freshAbs_stmt_old (K : RunCtx) (ρ : Assignment) (φ : Future) : Prop :=
  ∀ (st : MState) (T n : Value) (s : SState) (π : Nat → Nat) (v : Sem),
    GoodOld K ρ st → CtxOk K ρ st → Rel K ρ φ π st s → GenTy K ρ st T n →
    ∃ Δ' : Nat → TyS, Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ (ρ.ext st.nextAbs v)
      { st with nextAbs := st.nextAbs + 1, absTy := st.absTy.push T }

/-- **`freshAbs_sim` as it stood is false** at every context that admits `S` and a related
reference state. -/
theorem fresh_false (K : RunCtx) (φ : Future) (hctx : CtxOk K ρ₀ S) (s : SState) (π : Nat → Nat)
    (hs : Rel K ρ₀ φ π S s) : ¬ freshAbs_stmt_old K ρ₀ φ := by
  intro h
  obtain ⟨Δ', hg⟩ := h S .tNat .zero s π (.el0 Nat 1) (goodOld_S K) hctx hs (genTy_S K)
  exact not_good_ext K Δ' hg

/-- **(WF6) as restated excludes `S`**: the record names `σ₀`, which has no type. -/
theorem not_wf6 : ¬ WF6 S := by
  rintro ⟨h, -⟩
  have := h 0 (.neutral .zero 0 (by simp [S]) (.inl rfl))
  simp [S] at this

end Ochr.Meaning.Regress.FreshBound
