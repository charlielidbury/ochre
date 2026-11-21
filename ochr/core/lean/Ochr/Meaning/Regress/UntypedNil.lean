import Ochr.Meaning.Regress.GenNeutralContent
import Ochr.Meaning.DataModel.Program
import Ochr.Meaning.Steps.Sim

/-!
# An untyped run of an unannotated constructor has no reference run (built; docs/31 D20 item 4)

`evalCore_step_stmt` and `eval_step_stmt` conclude, for every term run typed OR untyped, that the
reference run of the term does not fail. docs/31 D20 item 4 said this is false of untyped runs of
arbitrary text, read off the clauses and never kernel-checked; D59, D61 and D89 changed both sides
since. Checked here, at fuel 10: from `a : Nat ↦ 0` with `List` declared (`SL`, `Good` at every
assignment, `good_SL`), the checker's UNTYPED run of `Nil` with no parameter written and no hint
succeeds (`runs`, evaluated by the kernel) and returns the bare constructor value `Nil` with no
parameters recorded and no type; the reference's `.ctor` clause cannot solve `List`'s parameter (no
field, no hint) and fails (`run_nil_none`). So both statements, as they stood, are false at every
context that admits `SL` and reads `Nil` as neither a statement nor erased (`evalCore_untyped_false`,
`eval_untyped_false`); the restricted ones exclude the run (`hok_excludes`).

Accepted code does not do this: the typed check of the code rejects a constructor whose parameters
nothing determines, and the untyped run reads the same hints (D88, D89). So the statements are
restricted to untyped runs of code whose reference run succeeds (`hok`), as the call steps state
already (docs/31 D62); for a body, the callee's meaning being a member of its type gives it.
-/

namespace Ochr.Meaning.Regress.UntypedNil
open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Regress.GenNeutralContent
open Ochr.Meaning.DataModel.Program (listD)

/-- `a : Nat ↦ 0`, with `List` declared. -/
def SL : MState := { env := #[{ binds := #[natB] }], inds := [listD] }

/-- `Nil`, its parameter not written. -/
def nil0 : Term := .ctor "List" 0 ⟨"Nil"⟩ [] []

/-- The checker's untyped run of `Nil` with no hint, through `evalCore` and through `eval`. -/
abbrev evC : M (Value × Option Value) := Ochr.evalCore 10 false nil0 none
abbrev ev : M (Value × Option Value) := Ochr.eval 10 false nil0 none

/-- The bare `Nil`, no parameter recorded, no type. -/
def isBareNil : Value × Option Value → Bool
  | (.ind "List" 0 _ [] [], none) => true
  | _ => false

theorem isBareNil_eq {p : Value × Option Value} (h : isBareNil p = true) :
    ∃ x, p = (.ind "List" 0 x [] [], none) := by
  unfold isBareNil at h; split at h
  · exact ⟨_, rfl⟩
  · cases h

theorem okC : isOk evC SL 10 = true := by decide +kernel
theorem runsC : ∃ x, Runs evC SL 10 (.ind "List" 0 x [] [], none) (outSt evC SL 10) := by
  obtain ⟨x, hx⟩ := isBareNil_eq (show isBareNil (outVal evC SL 10) = true by decide +kernel)
  exact ⟨x, hx ▸ runs_out evC SL 10 okC⟩
theorem ok : isOk ev SL 10 = true := by decide +kernel
theorem runs : ∃ x, Runs ev SL 10 (.ind "List" 0 x [] [], none) (outSt ev SL 10) := by
  obtain ⟨x, hx⟩ := isBareNil_eq (show isBareNil (outVal ev SL 10) = true by decide +kernel)
  exact ⟨x, hx ▸ runs_out ev SL 10 ok⟩

/-! ## The start state is `Good` at every assignment (as `GenNeutralContent.good_S`) -/

theorem bindAt_SL (f i : Nat) (b : Binding) (h : SL.env[f]?.bind (fun fr => fr.binds[i]?) = some b) :
    f = 0 ∧ i = 0 ∧ b = natB := by
  rcases f with _ | f <;> rcases i with _ | i
  · simp [SL, natB] at h; exact ⟨rfl, rfl, h.symm⟩
  all_goals simp [SL, natB] at h

theorem posTyM_SL (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (p : Pos) (T : TyM)
    (h : MState.posTyM dm C Γ ρ SL p = some T) : p = .bind 0 0 ∧ T = TyM.nat := by
  cases p with
  | temp f i => simp [MState.posTyM] at h
  | bind f i =>
    rcases f with _ | f <;> rcases i with _ | i
    · simp [MState.posTyM, SL, natB, Value.tyM, Value.mean, Sem.asTy] at h
      exact ⟨rfl, h.symm⟩
    all_goals simp [MState.posTyM, SL] at h

theorem good_SL (K : RunCtx) (ρ : Assignment) : Good K.dm K.M K.Γ ρ SL := by
  have hA : allPos SL.env = [.bind 0 0] := by decide +kernel
  have hV : Env.values SL.env = [.zero] := by rw [Env.values, hA]; rfl
  refine ⟨⟨fun σ _ h => by simp [SL, natB] at h, fun n σ h => by simp [SL, natB] at h, fun σ v h => by simp [SL, natB] at h,
      fun σ r h => by simp [SL, natB] at h⟩,
    ⟨?_, fun σ _ h => by simp [SL, natB] at h, fun G h => by simp [MState.goalM, SL] at h⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro φ _ p T hp
    obtain ⟨rfl, rfl⟩ := posTyM_SL K.dm K.M K.Γ ρ p T hp
    have e : Env.mean K.dm K.M K.Γ ρ φ SL.env (.bind 0 0) = .el0 Nat 0 := rfl
    rw [e]; exact DataModel.pmem_of_mem K.dm K.Γ (by simp [Sem.whole]) (by simp [Sem.mem, TyM.nat, Code0.enc])
  · rw [hA]; intro p hp; simp at hp; subst hp; show ¬ (Value.zero.hasBorrow = true); decide
  · rw [hA]; intro p hp q hq _ _ _; simp at hp hq; rw [hp, hq]
  · rw [hV]; intro v hv l hl; simp at hv; subst hv; simp [Value.outerLoans] at hl
  · intro l; rw [hV]; simp [Value.outerLoans]
  · have h0 : valAt SL.env (.bind 0 0) = .zero := rfl
    exact ⟨fun a => ⟨a, fun b ⟨p, hp, w, hw, _⟩ => by
      rw [hA] at hp; simp at hp; subst hp; rw [h0] at hw; cases hw⟩⟩
  · unfold WF4; rw [hV]; intro v hv; simp at hv; subst hv; decide
  · exact MState.refd_lt SL _
      (by rw [hV]; intro v hv σ h; simp at hv; subst hv; simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h)
      (fun f i b T hb hT σ h => by
        obtain ⟨_, _, rfl⟩ := bindAt_SL f i b hb
        simp [natB] at hT; subst hT; simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h)
      (fun f i b P ws j hb hT => by obtain ⟨_, _, rfl⟩ := bindAt_SL f i b hb; simp [natB] at hT)
      (fun G hG => by simp [SL, natB] at hG) (fun m σ' h => by simp [SL, natB] at h) (fun σ' v h => by simp [SL, natB] at h)
      (fun σ' T h => by simp [SL, natB] at h)
  · intro T hT; simp [SL, natB] at hT
  · intro σ r h; simp [SL, natB] at h
  · simp [SL, natB]
  · rw [hV]; intro v hv l hl; simp at hv; subst hv; simp [Value.loans] at hl
  · intro p T _ f i b _ hb A hA'
    obtain ⟨_, _, rfl⟩ := bindAt_SL f i b hb
    simp [natB] at hA'
  · rw [hV]; intro v hv; simp at hv; subst hv; decide
  · intro f i b hb T hT
    obtain ⟨_, _, rfl⟩ := bindAt_SL f i b hb
    simp [natB] at hT; subst hT; decide
  · intro T hT; simp [SL, natB] at hT
  · intro G hG; simp [SL, natB] at hG
  · intro p hp _; rw [hA] at hp; simp at hp; subst hp; exact ⟨_, rfl⟩
  · intro v hv; rw [hV] at hv; simp at hv; subst hv; rfl
  · intro f i b hb
    obtain ⟨_, _, rfl⟩ := bindAt_SL f i b hb
    exact ⟨fun T hT l => by simp [natB] at hT; subst hT; rfl, fun P ws j h => by simp [natB] at h⟩
  · intro T hT; simp [SL, natB] at hT
  · intro G hG; simp [SL, natB] at hG
  · intro n σ h; simp [SL, natB] at h
  · intro σ v h; simp [SL, natB] at h
  · have h0 : valAt SL.env (.bind 0 0) = .zero := rfl
    refine ⟨?_, ?_, ?_⟩
    · intro k l _ _ x hx
      simp [Env.sitesOf, hA, h0, Value.sitesOf] at hx
    · intro pos path _ l _ x hx
      simp [Env.sitesOf, hA, h0, Value.sitesOf] at hx
    · refine ⟨?_, ?_⟩
      · intro v hv l; rw [hV] at hv; simp at hv; subst hv; rfl
      · intro v hv; rw [hV] at hv; simp at hv; subst hv; rfl

/-! ## The reference has no run of it -/

/-- **The reference cannot run `Nil` with no parameter written and no hint**: the `.ctor` clause
solves `List`'s parameter from neither the fields (there are none) nor the hint, and fails. -/
theorem run_nil_none (K : RunCtx) (ρ : Assignment) (φ : Future) (s : SState)
    (hΓ : K.Γ = [listD]) (hfl : K.D.flags (scopeOf s) nil0 = (false, false)) :
    run K ρ φ (.plain .err) nil0 s = none := by
  have hfl' : K.D.flags (scopeOf s) (Term.ctor "List" 0 ⟨"Nil"⟩ [] []) = (false, false) := hfl
  simp [run, runT, nil0, SM.erasedIf, hfl', hΓ, listD, runParams, runFields, SM.stmtIf, TyS.plain,
    TyM.err, bind, pure, TyS.data, TyM.dataRec?, ctorOut, SM.fail, SM.strictS]

/-! ## The statements as they stood (spine 6f434832), with no restriction of untyped runs -/

def evalCore_step_stmt_old (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (t : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (_hg : Good K.dm K.M K.Γ ρ st) (_hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (_hs : Rel K ρ φ π st s)
    (_hns : K.D.flags (scopeOf s) t = (false, false))
    (bh : Nat) (_h : Runs (Ochr.evalCore fuel typed t hint) st bh (v, T?) st'),
    ∃ ρ' π', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧ (∀ l, l < st.nextLoan → π' l = π l) ∧
      ∃ r s', run K ρ' φ (hintM K ρ hint) t s = some (r, s') ∧
        meanV K ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧
        (∀ T, T? = some T → StrAgree K ρ' T r.2) ∧
        Rel K ρ' φ π' st' s' ∧ Good K.dm K.M K.Γ ρ' st'

def eval_step_stmt_old (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (t : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (_hg : Good K.dm K.M K.Γ ρ st) (_hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (_hs : Rel K ρ φ π st s)
    (bh : Nat) (_h : Runs (Ochr.eval fuel typed t hint) st bh (v, T?) st'),
    ∃ ρ' π', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧ (∀ l, l < st.nextLoan → π' l = π l) ∧
      ∃ r s', run K ρ' φ (hintM K ρ hint) t s = some (r, s') ∧
        meanV K ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧
        (∀ T, T? = some T → (K.D.flags (scopeOf s) t).2 = false → StrAgree K ρ' T r.2) ∧
        Rel K ρ' φ π' st' s' ∧ Good K.dm K.M K.Γ ρ' st'

/-- **`evalCore_step_stmt` as it stood is false of an untyped run** (fuel 10), at every context that admits
`SL` and reads `Nil` as neither a statement nor erased: the checker's run succeeds, the reference's
from the related state (`Rel.start`) fails. -/
theorem evalCore_untyped_false (K : RunCtx) (ρ : Assignment) (φ : Future) (hctx : CtxOk K ρ SL)
    (hfl : K.D.flags (scopeOf (SM' K ρ SL)) nil0 = (false, false)) : ¬ evalCore_step_stmt_old K ρ φ 10 := by
  intro h
  obtain ⟨x, hr⟩ := runsC
  obtain ⟨ρ', π', -, -, r, s', hrun, -⟩ :=
    h SL _ false nil0 none _ none (good_SL K ρ) hctx (SM' K ρ SL) id (Rel.start K ρ φ SL (fun l hl => by
      exfalso; simp [SState.Live, SState.liveLabels, SM', MState.sstate, Env.shape, SL, natB, valAt, allPos, SState.positions] at hl)) hfl 10 hr
  rw [show hintM K ρ none = .plain .err from rfl, run_nil_none K ρ' φ _ hctx.inds hfl] at hrun
  cases hrun

/-- **`eval_step_stmt` as it stood is false of an untyped run** (fuel 10), likewise: `eval` classifies `Nil` as
neither erased nor a statement and runs it as `evalCore` does. -/
theorem eval_untyped_false (K : RunCtx) (ρ : Assignment) (φ : Future) (hctx : CtxOk K ρ SL)
    (hfl : K.D.flags (scopeOf (SM' K ρ SL)) nil0 = (false, false)) : ¬ eval_step_stmt_old K ρ φ 10 := by
  intro h
  obtain ⟨x, hr⟩ := runs
  obtain ⟨ρ', π', -, -, r, s', hrun, -⟩ :=
    h SL _ false nil0 none _ none (good_SL K ρ) hctx (SM' K ρ SL) id (Rel.start K ρ φ SL (fun l hl => by
      exfalso; simp [SState.Live, SState.liveLabels, SM', MState.sstate, Env.shape, SL, natB, valAt, allPos, SState.positions] at hl)) 10 hr
  rw [show hintM K ρ none = .plain .err from rfl, run_nil_none K ρ' φ _ hctx.inds hfl] at hrun
  cases hrun

/-- The restricted statements exclude this run: its reference run fails, so their `hok` does not
hold of it. -/
theorem hok_excludes (K : RunCtx) (ρ : Assignment) (hctx : CtxOk K ρ SL) (φ : Future)
    (hfl : K.D.flags (scopeOf (SM' K ρ SL)) nil0 = (false, false)) :
    ¬ (run K ρ φ (hintM K ρ none) nil0 (SM' K ρ SL)).isSome := by
  rw [show hintM K ρ none = .plain .err from rfl, run_nil_none K ρ φ _ hctx.inds hfl]; simp

end Ochr.Meaning.Regress.UntypedNil
