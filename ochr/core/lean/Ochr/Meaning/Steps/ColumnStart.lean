import Ochr.Meaning.Steps.ColumnLet
import Ochr.Meaning.DecisionsFF
import Ochr.Meaning.Regress.GenNeutralContent
import Ochr.Meaning.Steps.Sim

/-!
# The column's program at its start: every hypothesis of a step, instantiated (lead7)

`def C : Nat := let x = S(Z); x`. `checkDef`'s constant branch evaluates the body from a state with
one empty frame (`modify fun s => { s with env := #[{}], … }`), with the goal `Nat` as the hint. The
kernel of that state (`Kern`) is `stC`'s: one empty frame, no globals, no declarations, no unknowns,
no labels, no goal. Here every bundle of hypotheses a step takes is instantiated at `stC` and the
run context `KC dm D`, and each is a theorem (kernel-checked):

* the checker's side: `Mode`, `Pre` (`CtxS`, `Inv`, `Asg`);
* the reference's: the checker's state read as a reference state (`SM'`), related (`Rel`, by
  `Rel.start`) and good (`SGood`);
* the context: `FundCtx`;
* the term: `valsOk`, `absBelow`, `hasHolePrim`;
* the decisions, wherever the column reads them, at any table aligned with the checker at `stC`
  (`DecTab D stC`): by the checker's own decision procedures, run at the scope states (kernel
  evaluation, `decide +kernel`, as `Regress/OpenFalse.lean` does).

The checker's run of the body itself is not kernel-evaluable (the variable read goes through code
the kernel does not unfold); it is `#guard`ed in `Steps/ColumnC.lean`, where the column is applied.
-/

namespace Ochr.Meaning.Steps.Form.ColumnC

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- The body of `def C : Nat := let x = S(Z); x`. -/
def bodyC : Term := .letIn ⟨"x"⟩ (.succ .zero) (.place (.var 0))

/-- The kernel of the state `checkDef` evaluates a constant's body from: one empty frame. -/
def stC : MState := { env := #[{}] }

/-- No globals are read; each means `0 : Nat`. -/
def CC : CodeMeaning :=
  { global := fun _ => (.el0 Nat 0, .plain TyM.nat), sealed := fun _ _ _ _ => .err, clo := fun _ _ _ _ _ => .err,
    pi := fun _ _ _ _ _ => TyM.err, paramTy := fun _ _ _ _ => .plain TyM.err }

/-- The run's context: no declarations, the decisions `D`. -/
def KC (dm : DataModel) (D : Decisions) : RunCtx := { dm := dm, Γ := [], C := CC, D := D }

/-- The reading of `S(Z)`, which `x` is bound at (the checker's: `other`). -/
def duC : DeclInfo := .other

variable (dm : DataModel) (D : Decisions) (ρ : Assignment) (φ : Future)

/-! ## The checker's side -/

/-! Auxiliaries: `stC` has one empty frame, so it has no position, no value, no live loan, no
binding, no unknown, no record, no goal and no global; every clause below is vacuous for that. -/
namespace Aux

theorem norm_stC : stC.norm = stC := by simp [stC, MState.norm, Env.erase, Frame.erase]

theorem allPos_stC : allPos stC.env = [] := by rw [allPos_eq]; simp [stC, frameAllPos]

theorem values_stC : Env.values stC.env = [] := by simp [Env.values, allPos_stC]

theorem liveLoan_stC (l : Nat) : liveLoan stC.env l = false := by
  simp [liveLoan, findBorrow, allPos_stC]

theorem bind_stC (f i : Nat) : stC.env[f]?.bind (fun fr => fr.binds[i]?) = none := by
  rcases f with _ | f <;> simp [stC]

theorem ckContent_stC (p : Place) : ckContent stC.env p = none := by
  simp [ckContent, ckVarPos, stC]

theorem not_refd_stC (σ : Nat) : ¬ stC.Refd σ := by
  intro h
  have := MState.refd_lt stC 0 (by simp [values_stC]) (fun f i b T hb => by simp [bind_stC] at hb)
    (fun f i b P ws j hb => by simp [bind_stC] at hb) (fun G hG => by simp [stC] at hG)
    (fun m σ' h => by simp [stC] at h) (fun σ' v h => by simp [stC] at h) (fun σ' T h => by simp [stC] at h) σ h
  omega

theorem occurs_stC (l : Nat) : ¬ stC.Occurs l := by
  rintro ⟨v, hv, -⟩; simp [values_stC] at hv

theorem ctxS_stC : CtxS (KC dm D) stC where
  inds := List.prefix_refl _
  covers := fun _ h => absurd h List.not_mem_nil
  faithful := fun _ h => absurd h List.not_mem_nil
  noLabel := fun _ => rfl
  globals := ⟨fun _ _ h => by simp [stC] at h, fun _ _ h => by simp [stC] at h, fun _ _ _ h => by simp [stC] at h,
    fun _ _ h => by simp [stC] at h, fun _ _ _ h => by simp [stC] at h⟩

/-- At every declaration list (the one-list ruling, docs/31 D174: the context's list is the whole
program's; `stC` holds no value, so no clause reads it). -/
theorem inv_stC {Γ : List IndDecl} : Inv D Γ stC := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  -- (WF1)
  · intro p hp; simp [allPos_stC] at hp
  · intro p hp; simp [allPos_stC] at hp
  -- (WF2)
  · intro v hv; simp [values_stC] at hv
  · intro l; simp [values_stC]
  -- (WF3)
  · exact ⟨fun a => ⟨a, fun b ⟨p, hp, _⟩ => by simp [allPos_stC] at hp⟩⟩
  -- (WF4)
  · intro v hv; simp [values_stC] at hv
  -- (WF6)
  · intro σ h; exact absurd h (not_refd_stC σ)
  · intro T hT; simp [stC] at hT
  · intro σ r h; simp [stC] at h
  · rfl
  · intro v hv; simp [values_stC] at hv
  -- (WF8)
  · intro v hv; simp [values_stC] at hv
  · intro f i b hb; simp [bind_stC] at hb
  · intro T hT; simp [stC] at hT
  · intro G hG; simp [stC] at hG
  -- (WF10)
  · intro v hv; simp [values_stC] at hv
  -- (WF11)
  · intro f i b hb; simp [bind_stC] at hb
  · intro T hT; simp [stC] at hT
  · intro G hG; simp [stC] at hG
  · intro n σ h; simp [stC] at h
  · intro σ v h; simp [stC] at h
  -- (WF12), (WF14): no live loan
  · intro k l hk; simp [liveLoan_stC] at hk
  · intro pos path _ l hl; simp [liveLoan_stC] at hl
  -- (WF15), (WF16)
  · intro v hv; simp [values_stC] at hv
  · intro v hv; simp [values_stC] at hv
  -- `ShapeFacts`
  · intro p v n args h; simp [ckContent_stC] at h
  · intro v hv; simp [values_stC] at hv
  · intro v hv; simp [values_stC] at hv
  · intro p _ h; simp [ckContent_stC] at h
  · intro σ r h; simp [stC] at h
  · intro σ r h; simp [stC] at h
  · intro σ l h; simp [stC] at h
  -- the label counter
  · intro l h; exact absurd h (occurs_stC l)

theorem asg_stC : Asg (KC dm D) ρ stC := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro σ _ h; simp [stC] at h
  · intro n σ h; simp [stC] at h
  · intro σ v h; simp [stC] at h
  · intro σ r h; simp [stC] at h
  · intro σ _ h; simp [stC] at h
  · intro G h; simp [MState.goalM, stC] at h
  · intro σ _ h; simp [stC] at h

end Aux

open Aux

theorem mode_stC : Mode stC := ⟨rfl, rfl, rfl, rfl⟩

theorem topReadings_stC : DecideScope.topReadings stC = [] := rfl

theorem pre_stC : Pre (KC dm D) ρ stC := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [norm_stC]
  · exact ctxS_stC dm D
  · exact inv_stC D
  · exact asg_stC dm D ρ

/-! ## The reference's side -/

/-! Auxiliaries: read as a reference state, `stC` has no position, so no shape entry, no live
label, and every position reads `err` at every future. -/
namespace Aux

theorem positions_SM : (SM' (KC dm D) ρ stC).positions = [] := by
  unfold SM'; rw [sstate_positions]; exact allPos_stC

theorem shape_SM (p : Pos) : (SM' (KC dm D) ρ stC).shape p = none := by
  cases h : (SM' (KC dm D) ρ stC).shape p with
  | none => rfl
  | some l =>
    have := mem_allPos_of_shape (l := l) h
    rw [allPos_stC] at this; cases this

theorem liveLabels_SM : (SM' (KC dm D) ρ stC).liveLabels = [] := by
  simp [SState.liveLabels, positions_SM]

theorem valAt_SM (p : Pos) : (SM' (KC dm D) ρ stC).valAt p = fun _ => .err :=
  SState.valAt_of_not_mem _ _ (by rw [positions_SM]; exact List.not_mem_nil)

end Aux

theorem rel_stC : Rel (KC dm D) ρ φ id stC (SM' (KC dm D) ρ stC) :=
  Rel.start_noLive _ _ _ _ fun l h => by
    simp [SState.Live, liveLabels_SM] at h

theorem sgood_stC : Strict.SGood dm [] φ (SM' (KC dm D) ρ stC) where
  bind := fun ψ _ f i hp => by rw [positions_SM] at hp; cases hp
  holder := fun ψ _ p l hl => by rw [shape_SM] at hl; cases hl
  held := fun l hl => by rw [liveLabels_SM] at hl; cases hl
  holderTy := fun f i l hl => by rw [shape_SM] at hl; cases hl
  acyc := ⟨fun p ψ ψ' _ => by rw [valAt_SM], fun r x hr => (by rw [positions_SM] at hr; cases hr),
    fun p x hp => (by rw [shape_SM] at hp; cases hp)⟩
  fresh := fun p l h => by
    obtain ⟨ψ, x, hne⟩ := h
    exact absurd (by show (SM' (KC dm D) ρ stC).valAt p ψ = (SM' (KC dm D) ρ stC).valAt p (ψ.upd l x); rw [valAt_SM]) hne
  uniq := fun p _ l hp _ => by rw [shape_SM] at hp; cases hp

/-! ## The context and the term -/

theorem fundCtx_KC : Strict.FundCtx (KC dm D) :=
  ⟨fun _ => ⟨.inl ⟨0, rfl⟩, rfl⟩, fun _ h => absurd h List.not_mem_nil⟩

theorem valsOk_bodyC (K : RunCtx) : bodyC.valsOk (Strict.ValsP K ρ φ) := by
  simp [bodyC, Term.valsOk]

theorem absBelow_bodyC (m : Nat) : bodyC.absBelow m := by
  intro σ h
  simp [bodyC, Term.anyAtom] at h

theorem hasHolePrim_bodyC : bodyC.hasHolePrim = false := by
  decide

/-! ## The decisions the column reads, at a table aligned with the checker at `stC` -/

/-! Auxiliaries: the checker's decision procedures, run as `DecTab` runs them at the scope states of
`stC` (fuel `100` for the procedure, `1000` for the run's budget), succeed with the answers below
(kernel evaluation, as `Regress/OpenFalse.lean` does). -/
namespace Aux

open Ochr.Meaning.Regress.GenNeutralContent (outSt outVal isOk runs_out)

/-- The run `DecTab.flags` reads, at fuel `100`. -/
abbrev flagsRun (t : Term) : M (Bool × Bool) := do
  let d ← withLive true (Ochr.declOf 100 false [] [] t)
  pure ((← Ochr.preFlags t d).getD (false, false))

/-- The run `DecTab.declOf` reads, at fuel `100`. -/
abbrev declRun (t : Term) : M DeclInfo := withLive true (Ochr.declOf 100 false [] [] t)

def isOther : DeclInfo → Bool
  | .other => true
  | _ => false

theorem isOther_eq {d : DeclInfo} (h : isOther d = true) : d = duC := by
  cases d <;> first | rfl | cases h

/-- The column's readings are decided and no proofs (`EvalInv`'s conditions). -/
theorem duC_ok : duC ≠ .any ∧ duC.isProof = false := ⟨fun e => (by cases e), rfl⟩

def isAny : DeclInfo → Bool
  | .any => true
  | _ => false

theorem ok_flags_bodyC : isOk (flagsRun bodyC) (scopeState stC []) 1000 = true := by decide +kernel
theorem val_flags_bodyC : outVal (flagsRun bodyC) (scopeState stC []) 1000 = (false, false) := by decide +kernel
theorem ok_flags_SZ : isOk (flagsRun (.succ .zero)) (scopeState stC []) 1000 = true := by decide +kernel
theorem val_flags_SZ : outVal (flagsRun (.succ .zero)) (scopeState stC []) 1000 = (false, false) := by
  decide +kernel
theorem ok_flags_Z : isOk (flagsRun .zero) (scopeState stC []) 1000 = true := by decide +kernel
theorem val_flags_Z : outVal (flagsRun .zero) (scopeState stC []) 1000 = (false, false) := by decide +kernel
theorem ok_declOf_SZ : isOk (declRun (.succ .zero)) (scopeState stC []) 1000 = true := by decide +kernel
theorem val_declOf_SZ : isOther (outVal (declRun (.succ .zero)) (scopeState stC []) 1000) = true := by
  decide +kernel
theorem ok_declOf_body : isOk (declRun bodyC) (scopeState stC []) 1000 = true := by decide +kernel
theorem val_declOf_body : isOther (outVal (declRun bodyC) (scopeState stC []) 1000) = true := by
  decide +kernel
theorem ok_declOf_x : isOk (declRun (.place (.var 0))) (scopeState stC [duC]) 1000 = true := by decide +kernel
theorem val_declOf_x : isOther (outVal (declRun (.place (.var 0))) (scopeState stC [duC]) 1000) = true := by
  decide +kernel
theorem ok_declOf_Z : isOk (declRun .zero) (scopeState stC []) 1000 = true := by decide +kernel
theorem val_declOf_Z : isAny (outVal (declRun .zero) (scopeState stC []) 1000) = false := by decide +kernel
theorem val_declOf_Z_proof : (outVal (declRun .zero) (scopeState stC []) 1000).isProof = false := by decide +kernel
theorem ok_flags_x : isOk (flagsRun (.place (.var 0))) (scopeState stC [duC]) 1000 = true := by decide +kernel
theorem val_flags_x : outVal (flagsRun (.place (.var 0))) (scopeState stC [duC]) 1000 = (false, false) := by
  decide +kernel

end Aux

section
variable {D} (hd : DecTab D stC)
include hd

open Ochr.Meaning.Regress.GenNeutralContent (runs_out)

theorem flags_bodyC : D.flags [] bodyC = (false, false) := by
  rw [hd.flags 100 [] bodyC _ 1000 _ (runs_out (flagsRun bodyC) _ 1000 ok_flags_bodyC), val_flags_bodyC]

theorem flags_SZ : D.flags [] (.succ .zero) = (false, false) := by
  rw [hd.flags 100 [] (.succ .zero) _ 1000 _ (runs_out (flagsRun (.succ .zero)) _ 1000 ok_flags_SZ), val_flags_SZ]

theorem flags_Z : D.flags [] .zero = (false, false) := by
  rw [hd.flags 100 [] .zero _ 1000 _ (runs_out (flagsRun .zero) _ 1000 ok_flags_Z), val_flags_Z]

theorem declOf_SZ : D.declOf [] (.succ .zero) = duC := by
  rw [hd.declOf 100 [] (.succ .zero) _ 1000 _ (runs_out (declRun (.succ .zero)) _ 1000 ok_declOf_SZ)]
  exact isOther_eq val_declOf_SZ

theorem flags_x : D.flags [duC] (.place (.var 0)) = (false, false) := by
  rw [hd.flags 100 [duC] (.place (.var 0)) _ 1000 _ (runs_out (flagsRun (.place (.var 0))) _ 1000 ok_flags_x),
    val_flags_x]

theorem declOf_bodyC : D.declOf [] bodyC = duC := by
  rw [hd.declOf 100 [] bodyC _ 1000 _ (runs_out (declRun bodyC) _ 1000 ok_declOf_body)]
  exact isOther_eq val_declOf_body

theorem declOf_x : D.declOf [duC] (.place (.var 0)) = duC := by
  rw [hd.declOf 100 [duC] (.place (.var 0)) _ 1000 _ (runs_out (declRun (.place (.var 0))) _ 1000 ok_declOf_x)]
  exact isOther_eq val_declOf_x

/-- `Z`'s reading is decided and no proof (`EvalInv`'s conditions). -/
theorem declOf_Z_ok : D.declOf [] .zero ≠ .any ∧ (D.declOf [] .zero).isProof = false := by
  rw [hd.declOf 100 [] .zero _ 1000 _ (runs_out (declRun .zero) _ 1000 ok_declOf_Z)]
  exact ⟨fun e => (by have h := val_declOf_Z; rw [e] at h; cases h), val_declOf_Z_proof⟩

/-- The reading the checker hands the `let`'s tail (the `let`'s own, at the empty frame) is the
tail's own reading (at `x`'s): both `other` (EvalInv's tail-reading condition at the tail). -/
theorem declOf_body_x : D.declOf [] bodyC = D.declOf [duC] (.place (.var 0)) := by
  rw [hd.declOf 100 [] bodyC _ 1000 _ (runs_out (declRun bodyC) _ 1000 ok_declOf_body),
    hd.declOf 100 [duC] (.place (.var 0)) _ 1000 _ (runs_out (declRun (.place (.var 0))) _ 1000 ok_declOf_x),
    isOther_eq val_declOf_body, isOther_eq val_declOf_x]

end

end Ochr.Meaning.Steps.Form.ColumnC
