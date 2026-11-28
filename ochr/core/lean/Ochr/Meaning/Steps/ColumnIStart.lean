import Ochr.Meaning.Steps.ParBody
import Ochr.Meaning.Steps.ColumnStart
import Ochr.Meaning.ClosureStage

/-!
# The column `I` at its body's start: the start-state bundles (lead14)

`def I (n : Nat) : Nat := S(n)` (the core body `S(#0)`, `ParBody.bodyI`; the surface's `S(n)` is a call
of `succFn`, whose body this is, docs/31 D124). `I` has no `by`, so `checkDef` checks it with `I` NOT in Σ (main's
D147: it is added after its check, as a constant is): `checkFix` checks the body from the generic state
(`Steps/ParGuards.lean` records it): frame 0 empty, frame 1 holding the own-name slot `()` at `Unit`, unnamed, read
`.unit`, unmarked (main's D148, `pushSelf`), then `n ↦ σ0` at `Nat` read `.other`; `Δ = [Nat]`, the goal `Nat`, Σ
empty. Its kernel (`MState.norm`) is `stI`. (Until the model's half of R-dec, docs/31 D296, the kernel held
`I ↦ .gfn "I"` at its Π-type, MARKED, and Σ held `I`, the states before D147/D148.)

The run context `KI dm D φ`: no declarations; no function under check (`cur = none`: a check without `by` names none);
`Δ 0 = Nat`. The reference's closure frame binds the slot `()` at `Unit` (`unitSlot`), as the checker does.

Every bundle a step takes is instantiated here at `stI` and `KI dm D φ`, for an assignment giving
`σ0` a number (`ρ 0 ∈ Nat`): `Pre` (`CtxS`, `Inv`, `Asg`), `Rel` (by `Rel.start_noLive`: no label),
`SGood` (the stage closure is a member of the weakened type, `ClosureStage.stage_mem`; `ρ 0` of `Nat`).
-/

namespace Ochr.Meaning.Steps.Form.ColumnI

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- `Π(n : Nat). Nat`, as the checker stores it. -/
def piNat : Value := .tPi [] (.pi [⟨"n"⟩] [.nat] .nat) []

/-- `I`'s `fix` term. -/
def fixI : Term := .fix ⟨"I"⟩ [⟨"n"⟩] [.nat] .nat none bodyI

/-- `I`'s global, as `checkDef` pushes it before checking the body. -/
def gI : GDef := { name := "I", ty := piNat, fn? := some fixI, val := .gfn "I" }

/-- The function's binding of itself, marked (`recUid`), as the checker made it before main's D148 (kept for the
guards that pin the difference). -/
def selfB : Binding := { hint := ⟨"I"⟩, ty := some piNat, val := .gfn "I", decl := .pi .other, recUid := some 0 }

/-- The own-name slot of a function without `by` (main's D148, `pushSelf`): `()` at `Unit`, unnamed, read `.unit`,
unmarked. -/
def unitB : Binding := { hint := ⟨"_"⟩, ty := some .tUnit, val := .unit, decl := .unit }

/-- The parameter's binding: the unknown `σ0`. -/
def nB : Binding := { hint := ⟨"n"⟩, ty := some .tNat, val := .abs 0, decl := .other }

/-- The kernel of the body's start state (since main's D147/D148: the slot `()`, `I` not in Σ). -/
def stI : MState :=
  { env := #[{}, { binds := #[unitB, nB] }], nextAbs := 1, absTy := #[.tNat], absDecl := #[.other],
    goal := some .tNat }

/-- The parameter's domain and the codomain, as the reference reads `Π(n : Nat). Nat`. -/
def psI : List PiDom := [⟨false, fun _ => TyM.nat⟩]
def outI : PiCod := ⟨false, fun _ => TyM.nat⟩

/-- The stage-0 closure's type: `Π(n : Nat). Unit` (the weakened codomain at bound `0`). -/
noncomputable def selfTy (R : DataRead) : TyM := piTyAt R 1 psI (weakCod 1 (fixRank none) 0 outI)

/-- The stage-0 closure: `()` at every argument. -/
noncomputable def selfSem (R : DataRead) (φ : Future) : Sem :=
  closureAt R 1 φ psI (weakCod 1 (fixRank none) 0 outI) (stageFn 1 psI (fixRank none) 0 (fun _ => none))

/-- The globals: `I` means its stage-0 closure; nothing else is read. -/
noncomputable def CI (R : DataRead) (φ : Future) : CodeMeaning :=
  { global := fun n => if n = "I" then (selfSem R φ, .plain (selfTy R)) else (.el0 Nat 0, .plain TyM.nat),
    sealed := fun _ _ _ _ => .err, clo := fun _ _ _ _ _ => .err,
    pi := fun _ _ _ _ _ => TyM.err, paramTy := fun _ _ _ _ => .plain TyM.err }

/-- Δ: `σ0` is a number. -/
def ΔI : Nat → TyS := fun σ => if σ = 0 then .plain TyM.nat else .plain TyM.err

/-- The run's context while `I`'s body is checked: no function under check (no `by`, D147). -/
noncomputable def KI (dm : DataModel) (D : Decisions) (φ : Future) : RunCtx :=
  { dm := dm, Γ := [], C := CI dm.read φ, D := D, Δ := ΔI, cur := none }

variable (dm : DataModel) (D : Decisions) (ρ : Assignment) (φ φ' : Future)

namespace Aux

theorem norm_stI : stI.norm = stI := by
  simp [stI, MState.norm, Env.erase, Frame.erase]

theorem allPos_stI : allPos stI.env = [.bind 1 0, .bind 1 1] := by
  rw [allPos_eq]; simp [stI, frameAllPos, List.range_succ]

theorem values_stI : Env.values stI.env = [.unit, .abs 0] := by
  rw [Env.values, allPos_stI]; rfl

theorem liveLoan_stI (l : Nat) : liveLoan stI.env l = false := by
  rw [liveLoan, findBorrow, allPos_stI]; rfl

theorem bind_stI {f i : Nat} {b : Binding} (h : stI.env[f]?.bind (fun fr => fr.binds[i]?) = some b) :
    (f = 1 ∧ i = 0 ∧ b = unitB) ∨ (f = 1 ∧ i = 1 ∧ b = nB) := by
  rcases f with _ | _ | f
  · simp [stI] at h
  · rcases i with _ | _ | i
    · simp [stI] at h; exact .inl ⟨rfl, rfl, h.symm⟩
    · simp [stI] at h; exact .inr ⟨rfl, rfl, h.symm⟩
    · simp [stI] at h
  · simp [stI] at h

theorem ckContent_stI {p : Place} {v : Value} (h : ckContent stI.env p = some v) : v = .unit ∨ v = .abs 0 := by
  rcases hp : p.steps with ⟨i, path⟩
  simp only [ckContent, hp] at h
  unfold ckVarPos at h
  by_cases hi : i < 2
  · have hi' : i < stI.env[stI.env.size - 1]!.binds.size := hi
    rw [if_pos hi'] at h
    simp only [Option.bind_some] at h
    have hv : ∀ w : Value, (w = .unit ∨ w = .abs 0) → w.follow path = some v → v = .unit ∨ v = .abs 0 := by
      rintro w hw hf
      cases path with
      | nil => simp [Value.follow] at hf; exact hf ▸ hw
      | cons s ss => rcases hw with rfl | rfl <;> cases s <;> simp [Value.follow, stepV] at hf
    rcases i with _ | _ | i
    · exact hv _ (.inr rfl) h
    · exact hv _ (.inl rfl) h
    · omega
  · have hi' : ¬ i < stI.env[stI.env.size - 1]!.binds.size := hi
    rw [if_neg hi'] at h; cases h

theorem not_refd_ge {σ : Nat} (h : stI.Refd σ) : σ < 1 := by
  refine MState.refd_lt stI 1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ σ h
  · intro v hv σ hσ; rw [values_stI] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (Bool.false_ne_true hσ).elim
    · have := abs_hasAbs_eq hσ; omega
  · intro f i b T hb hT σ hσ
    rcases bind_stI hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [unitB, nB] at hT <;> subst hT <;>
      exact (Bool.false_ne_true hσ).elim
  · intro f i b P ws j hb hT
    rcases bind_stI hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [unitB, nB] at hT
  · intro G hG σ hσ; simp [stI] at hG; subst hG; exact (Bool.false_ne_true hσ).elim
  · intro m σ' h; simp [stI] at h
  · intro σ' v h; simp [stI] at h
  · intro σ' T h σ hσ
    rcases σ' with _ | σ'
    · simp [stI] at h; subst h; exact (Bool.false_ne_true hσ).elim
    · simp [stI] at h

theorem occurs_stI (l : Nat) : ¬ stI.Occurs l := by
  rintro ⟨v, hv, h⟩; rw [values_stI] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> exact Bool.false_ne_true h

theorem mem_values {v : Value} (hv : v ∈ Env.values stI.env) : v = .unit ∨ v = .abs 0 := by
  rw [values_stI] at hv; simpa using hv

theorem mem_allPos {p : Pos} (hp : p ∈ allPos stI.env) : p = .bind 1 0 ∨ p = .bind 1 1 := by
  rw [allPos_stI] at hp; simpa using hp

theorem shape_stI (p : Pos) : Env.shape stI.env p = none := by
  unfold Env.shape
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · rfl
    · rcases i with _ | _ | i <;> rfl
    · rfl
  · rcases f with _ | _ | f
    · rfl
    · rfl
    · rfl

theorem inv_stI : Inv D [] stI := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  -- (WF1)
  · intro p hp; rcases mem_allPos hp with rfl | rfl <;> exact Bool.false_ne_true
  · intro p _ q _ l h; rw [shape_stI] at h; cases h
  -- (WF2)
  · intro v hv l hl; rcases mem_values hv with rfl | rfl <;> cases hl
  · intro l; rw [values_stI]; exact Nat.zero_le _
  -- (WF3)
  · exact ⟨fun a => ⟨a, fun b ⟨p, hp, w, hw, _⟩ => by rcases mem_allPos hp with rfl | rfl <;> cases hw⟩⟩
  -- (WF4)
  · intro v hv; rcases mem_values hv with rfl | rfl <;> exact Bool.false_ne_true
  -- (WF6)
  · intro σ h; exact not_refd_ge h
  · intro T hT σ hσ; simp [stI] at hT; subst hT; exact (Bool.false_ne_true hσ).elim
  · intro σ r h; simp [stI] at h
  · rfl
  · intro v hv l hl; rcases mem_values hv with rfl | rfl <;> cases hl
  -- (WF8)
  · intro v hv; rcases mem_values hv with rfl | rfl <;> rfl
  · intro f i b hb T hT; rcases bind_stI hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [unitB, nB] at hT <;> subst hT <;> rfl
  · intro T hT; simp [stI] at hT; subst hT; rfl
  · intro G hG; simp [stI] at hG; subst hG; rfl
  -- (WF10)
  · intro v hv; rcases mem_values hv with rfl | rfl <;> rfl
  -- (WF11)
  · intro f i b hb; rcases bind_stI hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact ⟨fun T hT l => by simp [unitB] at hT; subst hT; rfl, fun P ws j h => by simp [unitB] at h⟩
    · exact ⟨fun T hT l => by simp [nB] at hT; subst hT; rfl, fun P ws j h => by simp [nB] at h⟩
  · intro T hT l; simp [stI] at hT; subst hT; rfl
  · intro G hG l; simp [stI] at hG; subst hG; rfl
  · intro n σ h; simp [stI] at h
  · intro σ v h; simp [stI] at h
  -- (WF12), (WF14): no live loan
  · intro k l hk; simp [liveLoan_stI] at hk
  · intro pos path _ l hl; simp [liveLoan_stI] at hl
  -- (WF15), (WF16)
  · intro v hv l; rcases mem_values hv with rfl | rfl <;> rfl
  · intro v hv; rcases mem_values hv with rfl | rfl <;> rfl
  -- `ShapeFacts`
  · intro p v n args _ _ h; simp at h
  · intro v hv l hl; rcases mem_values hv with rfl | rfl <;> cases hl
  · intro v hv; rcases mem_values hv with rfl | rfl <;> rfl
  · intro p _ h; rcases ckContent_stI h with h | h <;> cases h
  · intro σ r h; simp [stI] at h
  · intro σ r h; simp [stI] at h
  · intro σ l h; rcases σ with _ | σ <;> simp [stI] at h
  -- the label counter
  · intro l h; exact absurd h (occurs_stI l)
  -- (K): `I`'s own binding and global at `Π(n : Nat). Nat`; the parameter an unknown
  · refine (fun f i b hb => ?_)
    · rcases f with _ | _ | f
      · simp [stI] at hb
      · rcases i with _ | _ | i
        · simp only [stI] at hb; cases hb
          exact ⟨fun l c e => (nomatch e), fun l c e => (nomatch e)⟩
        · simp only [stI] at hb; cases hb
          exact ⟨fun l c e => (nomatch e), fun l c e => (nomatch e)⟩
        · simp [stI] at hb
      · simp [stI] at hb

theorem find_none {n : String} {g : GDef} (h : stI.globals.find? (·.name == n) = some g) : False := by
  simp [stI] at h

theorem ctxS_stI : CtxS (KI dm D φ) stI where
  inds := List.prefix_refl _
  covers := fun _ h => absurd h List.not_mem_nil
  faithful := fun _ h => absurd h List.not_mem_nil
  noLabel := fun n => by simp only [KI, CI]; split <;> rfl
  globals := {
    ty := fun n g hf _ => (find_none hf).elim
    const := fun n g hf _ => (find_none hf).elim
    fn := fun n g t hf _ _ => (find_none hf).elim
    mem := fun n g hf _ => (find_none hf).elim
    fixEq := fun n _ _ _ _ _ _ _ hf _ _ => (find_none hf).elim
    accepted := fun n _ _ _ _ _ _ _ hf _ _ => (find_none hf).elim
    retKind := fun n _ _ _ _ _ _ _ hf _ _ => (find_none hf).elim
    codeValFree := fun n g t hf _ => (find_none hf).elim
    memBelow := fun n g b hf _ => (find_none hf).elim }

theorem absTyM_stI (K : RunCtx) : MState.absTyM K.dm K.M K.Γ ρ stI 0 = TyM.nat := by
  unfold MState.absTyM; rfl

theorem asg_stI (hρ : ∃ m, ρ 0 = .el0 Nat m) : Asg (KI dm D φ) ρ stI := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro σ _ h
    have : σ = 0 := by simp [stI] at h; omega
    subst this; rw [absTyM_stI]; obtain ⟨m, hm⟩ := hρ; exact ⟨m, hm.symm⟩
  · intro n σ h; simp [stI] at h
  · intro σ v h; simp [stI] at h
  · intro σ r h; simp [stI] at h
  · intro σ _ h
    have : σ = 0 := by simp [stI] at h; omega
    subst this; rw [absTyM_stI]; rfl
  · intro G h; simp only [MState.goalM, stI, Option.map_some, Option.some.injEq] at h; subst h; rfl
  · intro σ _ h
    have : σ = 0 := by simp [stI] at h; omega
    subst this; rfl

end Aux

open Aux

theorem pre_stI (hρ : ∃ m, ρ 0 = .el0 Nat m) : Pre (KI dm D φ) ρ stI := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [norm_stI]
  · exact ctxS_stI dm D φ
  · exact inv_stI D
  · exact asg_stI dm D ρ φ hρ

/-! ## The reference's side -/

namespace Aux

variable {dm D ρ φ}

/-- Read as a reference state, `stI`'s positions mean the same at every future: the function's
binding its global's meaning, the parameter's `ρ 0`. -/
theorem valAt_SM_eq (p : Pos) (ψ : Future) :
    (SM' (KI dm D φ) ρ stI).valAt p ψ =
      match p with
      | .bind 1 0 => .el0 Unit ()
      | .bind 1 1 => ρ 0
      | _ => .err := by
  unfold SM'; rw [sstate_valAt]
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · rfl
    · rcases i with _ | _ | i
      · rfl
      · rfl
      · rfl
    · rfl
  · rcases f with _ | _ | f <;> rfl

theorem valAt_SM_const (p : Pos) (ψ ψ' : Future) :
    (SM' (KI dm D φ) ρ stI).valAt p ψ = (SM' (KI dm D φ) ρ stI).valAt p ψ' := by
  rw [valAt_SM_eq, valAt_SM_eq]

theorem positions_SM : (SM' (KI dm D φ) ρ stI).positions = [.bind 1 0, .bind 1 1] := by
  unfold SM'; rw [sstate_positions]; exact allPos_stI

theorem shape_SM (p : Pos) : (SM' (KI dm D φ) ρ stI).shape p = none := by
  unfold SM'; rw [sstate_shape]; exact shape_stI p

theorem liveLabels_SM : (SM' (KI dm D φ) ρ stI).liveLabels = [] := by
  simp [SState.liveLabels, positions_SM, shape_SM]

theorem tyAt_SM_self : ((SM' (KI dm D φ) ρ stI).tyAt (.bind 1 0)).m = TyM.unit := by
  unfold SM'
  rw [sstate_tyAt_bind _ _ _ _ _ 1 0 { binds := #[unitB, nB] } unitB rfl rfl,
    Binding.refTy_unmarked _ _ _ _ _ _ _ _ rfl]
  rfl

theorem tyAt_SM_n : ((SM' (KI dm D φ) ρ stI).tyAt (.bind 1 1)).m = TyM.nat := by
  unfold SM'
  rw [sstate_tyAt_bind _ _ _ _ _ 1 1 { binds := #[unitB, nB] } nB rfl rfl,
    Binding.refTy_unmarked _ _ _ _ _ _ _ _ rfl]
  rfl

end Aux

open Aux

theorem rel_stI : Rel (KI dm D φ) ρ φ' id stI (SM' (KI dm D φ) ρ stI) :=
  Rel.start_noLive _ _ _ _ fun l h => by
    simp [SState.Live, liveLabels_SM] at h

/-- The stage-0 closure is a member of the weakened type (`ClosureStage.stage_mem`, nothing to show
below bound `0`). -/
theorem selfSem_mem (R : DataRead) (φ : Future) : selfSem R φ ∈ₛ[R] selfTy R :=
  stage_mem R 1 φ psI outI (fixRank none) 0 (fun _ => none) ⟨Nat.le_refl 1, by omega⟩ rfl
    (fun _ _ h => absurd h (Nat.not_lt_zero _)) (fun _ _ h => absurd h (Nat.not_lt_zero _))

theorem sgood_stI (hρ : ∃ m, ρ 0 = .el0 Nat m) : Strict.SGood dm [] φ' (SM' (KI dm D φ) ρ stI) where
  bind := fun ψ _ f i hp => by
    rw [positions_SM] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false, Pos.bind.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [valAt_SM_eq, tyAt_SM_self]
      exact Strict.goodVal_of_mem dm.read_wholeFields [] (unit_mem dm.read)
    · rw [valAt_SM_eq, tyAt_SM_n]
      obtain ⟨m, hm⟩ := hρ
      exact Strict.goodVal_of_mem dm.read_wholeFields [] (show ρ 0 ∈ₛ[dm.read] TyM.nat from ⟨m, hm.symm⟩)
  holder := fun ψ _ p l hl => by rw [shape_SM] at hl; cases hl
  held := fun l hl => by rw [liveLabels_SM] at hl; cases hl
  holderTy := fun f i l hl => by rw [shape_SM] at hl; cases hl
  acyc := ⟨fun p ψ ψ' _ => valAt_SM_const p ψ ψ', fun r x _ hr => (by rw [shape_SM] at hr; cases hr),
    fun p x hp => (by rw [shape_SM] at hp; cases hp)⟩
  fresh := fun p l h => by
    obtain ⟨ψ, x, hne⟩ := h
    exact absurd (valAt_SM_const p ψ (ψ.upd l x)) hne
  uniq := fun p _ l hp _ => by rw [shape_SM] at hp; cases hp

/-! ## The decisions `I`'s body reads, at a table aligned with the checker at `stI`

The checker's decision procedures, run as `DecTab` runs them at the scope states of `stI` (kernel
evaluation), answer `ParBody.ParDecI` at the top frame's readings `[.other, .unit]`. -/

theorem topReadings_stI : DecideScope.topReadings stI = [.other, .unit] := rfl

namespace Aux

open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal runs_out)

abbrev flagsRun (t : Term) : M (Bool × Bool) := Ochr.Meaning.Steps.Form.ColumnC.Aux.flagsRun t
abbrev declRun (t : Term) : M DeclInfo := Ochr.Meaning.Steps.Form.ColumnC.Aux.declRun t
abbrev isOther (d : DeclInfo) : Bool := Ochr.Meaning.Steps.Form.ColumnC.Aux.isOther d

def RI : List DeclInfo := [.other, .unit]

theorem ok_flags_x : isOk (flagsRun (.place (.var 0))) (scopeState stI RI) 1000 = true := by decide +kernel
theorem val_flags_x : outVal (flagsRun (.place (.var 0))) (scopeState stI RI) 1000 = (false, false) := by
  decide +kernel
theorem ok_declOf_x : isOk (declRun (.place (.var 0))) (scopeState stI RI) 1000 = true := by decide +kernel
theorem val_declOf_x : isOther (outVal (declRun (.place (.var 0))) (scopeState stI RI) 1000) = true := by
  decide +kernel
theorem ok_flags_body : isOk (flagsRun bodyI) (scopeState stI RI) 1000 = true := by decide +kernel
theorem val_flags_body : outVal (flagsRun bodyI) (scopeState stI RI) 1000 = (false, false) := by decide +kernel
theorem ok_declOf_body : isOk (declRun bodyI) (scopeState stI RI) 1000 = true := by decide +kernel
theorem val_declOf_body : isOther (outVal (declRun bodyI) (scopeState stI RI) 1000) = true := by decide +kernel

end Aux

/-- **`ParDecI` at `I`'s body**, at every table aligned with the checker at `stI`. -/
theorem parDecI {D : Decisions} (hd : DecTab D stI) : ParDecI D [.other, .unit] := by
  refine ⟨?_, ?_, ?_⟩
  · show D.flags Aux.RI _ = _
    rw [hd.flags 100 Aux.RI (.place (.var 0)) _ 1000 _
      (Regress.GenNeutralContent.runs_out (Aux.flagsRun (.place (.var 0))) _ 1000 Aux.ok_flags_x), Aux.val_flags_x]
  · show D.declOf Aux.RI _ = _
    rw [hd.declOf 100 Aux.RI (.place (.var 0)) _ 1000 _
      (Regress.GenNeutralContent.runs_out (Aux.declRun (.place (.var 0))) _ 1000 Aux.ok_declOf_x)]
    exact Ochr.Meaning.Steps.Form.ColumnC.Aux.isOther_eq Aux.val_declOf_x
  · show D.declOf Aux.RI _ = _
    rw [hd.declOf 100 Aux.RI bodyI _ 1000 _
      (Regress.GenNeutralContent.runs_out (Aux.declRun bodyI) _ 1000 Aux.ok_declOf_body)]
    exact Ochr.Meaning.Steps.Form.ColumnC.Aux.isOther_eq Aux.val_declOf_body

/-- The body is neither a statement nor a proof, at every table aligned with the checker at `stI`. -/
theorem flags_bodyI {D : Decisions} (hd : DecTab D stI) : D.flags [.other, .unit] bodyI = (false, false) := by
  show D.flags Aux.RI _ = _
  rw [hd.flags 100 Aux.RI bodyI _ 1000 _
    (Regress.GenNeutralContent.runs_out (Aux.flagsRun bodyI) _ 1000 Aux.ok_flags_body), Aux.val_flags_body]

namespace Aux

open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal)

/-- The runs `DecTab.typeDecl` and `DecTab.piSort` read, at fuel `100`. -/
abbrev typeDeclRun (T : Term) : M DeclInfo := withLive true (Ochr.typeDecl 100 false [] [] T)
abbrev piSortRun (t : Term) : M Nat := withLive true (Ochr.sortOf 100 (.tPi [] t []))

theorem ok_td_nat (sc : List DeclInfo) (hsc : sc = [] ∨ sc = [.other]) :
    isOk (typeDeclRun .nat) (scopeState stI sc) 1000 = true := by
  rcases hsc with rfl | rfl <;> decide +kernel
theorem val_td_nat (sc : List DeclInfo) (hsc : sc = [] ∨ sc = [.other]) :
    isOther (outVal (typeDeclRun .nat) (scopeState stI sc) 1000) = true := by
  rcases hsc with rfl | rfl <;> decide +kernel
theorem ok_piSort : isOk (piSortRun (.pi [⟨"n"⟩] [.nat] .nat)) (scopeState stI []) 1000 = true := by decide +kernel
theorem val_piSort : outVal (piSortRun (.pi [⟨"n"⟩] [.nat] .nat)) (scopeState stI []) 1000 = 1 := by decide +kernel
theorem ok_flags_fix : isOk (flagsRun fixI) (scopeState stI []) 1000 = true := by decide +kernel
theorem val_flags_fix : outVal (flagsRun fixI) (scopeState stI []) 1000 = (false, false) := by decide +kernel

end Aux

/-- **The reference `.fix` clause's decisions for `I`, at the empty scope** (where a global's `fix`
is formed, `stateOf 0 []`), at every table aligned with the checker at `stI`: the parameter and the
codomain read `.other`, the Π-type has sort `1` (`Type₀`), the `fix` is neither a statement nor a proof. -/
theorem fixDecI {D : Decisions} (hd : DecTab D stI) :
    D.typeDecl [] .nat = .other ∧ D.typeDecl [.other] .nat = .other ∧ D.piSort [] (.pi [⟨"n"⟩] [.nat] .nat) = 1 ∧
      D.flags [] fixI = (false, false) := by
  open Ochr.Meaning.Regress.GenNeutralContent in
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hd.typeDecl 100 [] .nat _ 1000 _ (runs_out (Aux.typeDeclRun .nat) _ 1000 (Aux.ok_td_nat [] (.inl rfl)))]
    exact Ochr.Meaning.Steps.Form.ColumnC.Aux.isOther_eq (Aux.val_td_nat [] (.inl rfl))
  · rw [hd.typeDecl 100 [.other] .nat _ 1000 _
      (runs_out (Aux.typeDeclRun .nat) _ 1000 (Aux.ok_td_nat [.other] (.inr rfl)))]
    exact Ochr.Meaning.Steps.Form.ColumnC.Aux.isOther_eq (Aux.val_td_nat [.other] (.inr rfl))
  · rw [hd.piSort 100 [] _ _ 1000 _ (runs_out (Aux.piSortRun _) _ 1000 Aux.ok_piSort), Aux.val_piSort]
  · rw [hd.flags 100 [] fixI _ 1000 _ (runs_out (Aux.flagsRun fixI) _ 1000 Aux.ok_flags_fix), Aux.val_flags_fix]

/-- `n ↦ σ0` at `Nat`. -/
theorem absVar_stI : AbsVar 0 stI := ⟨1, 1, nB, 0, rfl, rfl, rfl, rfl, rfl⟩

end Ochr.Meaning.Steps.Form.ColumnI
