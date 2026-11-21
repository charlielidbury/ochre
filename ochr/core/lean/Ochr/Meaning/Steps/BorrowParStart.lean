import Ochr.Meaning.Steps.BorrowPar
import Ochr.Meaning.Steps.Sim
import Ochr.Meaning.Steps.ColumnIRun

/-!
# `W`'s and `K`'s body start: the model's state is related to the checker's (lead19, 2026-11-21; docs/31 D138, D140)

The reference runs a closure's body from `fixBodyAt`'s state (docs/31 D126, stage 2): frame 0 the parameter's CELL
`r° ↦ ψ l` at the content type, the top frame `self` then the parameter holding the argument, shaped with the fresh
label `l`, whose record (`heldMem`) is the argument and held type (`heldTy`) the content type. Since docs/31 D138
(built by the nineteenth lead) `fixStep` also records the cell as `l`'s one LOAN site (`setLent l [⟨cell, [], loan⟩]`),
as the checker's cell `r° ↦ loan₀` is label `0`'s one site (`Env.sitesOf`).

Before D138 no such state was related to the checker's start state (`Rel.sites` failed at label `0`; the eighteenth
lead's `rel_start_false`). Now every clause of `Rel` holds (`rel_startW`, `rel_startK`): for every data model, table,
future, number `m` the parameter's content is, and every `fb` that reads the parameter at `Nat` with its declared
reading, the checker's start state (`stW`, `stK`) under `σ0 ↦ m` is related, with no renaming, to the state
`fixBodyAt` builds at the argument `m`. The clauses: the same frames with the same types and readings (`skel`); the
label `0` issued on both sides (`fresh`); the same meanings, the cell `ψ 0` on both sides, `self` the stage-0
closure, `r` the number `m` (`sim`); the holder `r` of label `0` on both sides; the cell the label's one site on both
sides (`sites`, the clause D138 repaired); the record `m`, a whole member of `Nat`, the holder's type (`records`).
-/

namespace Ochr.Meaning.Steps.Form.ColumnW

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- `&Nat`'s domain, as the `.fix` clause reads it. -/
def psW : List PiDom := [⟨true, fun _ => TyM.nat⟩]

/-- `W`'s codomain `Nat` and `K`'s `&Nat`, as the `.fix` clause reads them. -/
def outW : PiCod := ⟨false, fun _ => TyM.nat⟩
def outK : PiCod := ⟨true, fun _ => TyM.nat⟩

/-- **The reference's body state for a function with one borrow parameter** at argument `a` (`fixBodyAt`'s, given the
binding of itself `sb`, the binders `fb` the `.fix` clause read, and the parameter's domain `d`, a borrow). -/
noncomputable def startS (fb : List PBind × PBind) (sb : SBinding) (d : PiDom) (a : Sem) : SState :=
  (([a].zip [d]).foldl (fixStep fb) ((emptyState 0).under.pushBind sb, [], [])).1

/-- The cell, as `fixStep` pushes it: label `0`'s final content at the content type `Nat`. -/
def cellS : SBinding := { ty := .plain TyM.nat, val := fun ψ => ψ 0, decl := .other }

/-- The parameter, as `fixStep` pushes it: the argument `a`, holder of label `0`, read `d`. -/
def parS (a : Sem) (d : DeclInfo) : SBinding := { ty := { (TyS.plain TyM.nat) with label := some 0 }, val := fun _ => a, decl := d }

/-- **The body state, written out**: frame 0 the cell, frame 1 `self` and the parameter; label `0` held by the parameter,
lent at the cell (D138), its record `a` at `Nat`. -/
noncomputable def SBW (sb : SBinding) (d : DeclInfo) (a : Sem) : SState :=
  { env := [{ binds := [cellS] }, { binds := [sb, parS a d] }],
    shape := fun p => if p = .bind 1 1 then some 0 else none, nextLoan := 1,
    lent := fun m => if m = 0 then [⟨.bind 0 0, [], false⟩] else [],
    heldTy := fun m => if m = 0 then TyM.nat else TyM.err,
    heldMem := fun m => if m = 0 then a else .err }

theorem startS_eq (fb : List PBind × PBind) {d : DeclInfo} (h1 : fb.1 = [(fun _ => .plain TyM.nat, d)]) (sb : SBinding)
    (a : Sem) : startS fb sb ⟨true, fun _ => TyM.nat⟩ a = SBW sb d a := by
  simp only [startS, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, fixStep, h1,
    if_true, List.length_nil, List.getElem?_cons_zero]
  simp [emptyState, SState.under, SState.pushCell, SState.freshLoan, SState.pushBind, SState.topIdx, pushBindShaped,
    SState.takeLabel, SState.holderOf, SState.positions, SState.setLent, SState.setHeldMem, SState.setHeldTy, SBW, cellS,
    parS, List.range']
  repeat' first | rfl | apply And.intro | funext
  all_goals first | rfl | (split <;> rfl) | (rename_i p; cases p <;> rfl) | skip

/-! ## The context while the body is checked -/

/-- The stage-0 closure's type for a function with one borrow parameter and the codomain `out` (the weakened codomain
at bound `0`), and the closure (`()` everywhere): `self` for a non-recursive function, never read. -/
noncomputable def selfTyB (R : DataRead) (out : PiCod) : TyM := piTyAt R 1 psW (weakCod 1 (fixRank none) 0 out)
noncomputable def selfSemB (R : DataRead) (φ : Future) (out : PiCod) : Sem :=
  closureAt R 1 φ psW (weakCod 1 (fixRank none) 0 out) (stageFn 1 psW (fixRank none) 0 (fun _ => none))

/-- The globals: the function `name` means its stage-0 closure; nothing else is read. -/
noncomputable def CB (name : String) (out : PiCod) (R : DataRead) (φ : Future) : CodeMeaning :=
  { global := fun n => if n = name then (selfSemB R φ out, .plain (selfTyB R out)) else (.el0 Nat 0, .plain TyM.nat),
    sealed := fun _ _ _ _ => .err, clo := fun _ _ _ _ _ => .err,
    pi := fun _ _ _ _ _ => TyM.err, paramTy := fun _ _ _ _ => .plain TyM.err }

/-- The run's context while the body of `name` (codomain `out`) is checked: no declarations, `σ0` a number, the function
being checked at bound `0` (as `ColumnI.KI`). -/
noncomputable def KB (name : String) (out : PiCod) (dm : DataModel) (D : Decisions) (φ : Future) : RunCtx :=
  { dm := dm, Γ := [], C := CB name out dm.read φ, D := D, Δ := ColumnI.ΔI, cur := some (name, 0) }

/-- `self`'s binding, as `fixBodyAt` pushes it for a non-recursive function (`cd`: the codomain's declared reading). -/
noncomputable def selfS (R : DataRead) (φ : Future) (out : PiCod) (cd : DeclInfo) : SBinding :=
  { ty := .plain (selfTyB R out), val := fun _ => selfSemB R φ out, decl := .pi cd }

/-! ## The checker's start states, generically -/

/-- The function's binding of itself, marked, at the Π-type `piX` read `.pi cd`. -/
def selfX (name : String) (piX : Value) (cd : DeclInfo) : Binding :=
  { hint := ⟨name⟩, ty := some piX, val := .gfn name, decl := .pi cd, recUid := some 0 }

/-- The start environment: the cell in frame 0; `self` and `r ↦ borrow₀ σ0` in frame 1. -/
def envB (name : String) (piX : Value) (cd : DeclInfo) : Env :=
  #[{ binds := #[cellR] }, { binds := #[selfX name piX cd, rB (.borrow 0 (.abs 0))] }]

theorem stW_env : stW.env = envB "W" piW .other := rfl
theorem stK_env : stK.env = envB "K" piK (.ref .other) := rfl

namespace Start

variable {name : String} {piX : Value} {cd : DeclInfo}

theorem allPos_envB : allPos (envB name piX cd) = [.bind 0 0, .bind 1 0, .bind 1 1] := by
  rw [allPos_eq]; simp [envB, frameAllPos, List.range_succ]

theorem shape_envB (p : Pos) : Env.shape (envB name piX cd) p = if p = .bind 1 1 then some 0 else none := by
  unfold Env.shape
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · rcases i with _ | i <;> rfl
    · rcases i with _ | _ | i <;> rfl
    · rfl
  · rcases f with _ | _ | f <;> rfl

theorem sitesOf_envB (l : Nat) :
    Env.sitesOf (envB name piX cd) l = if l = 0 then [⟨.bind 0 0, [], false⟩] else [] := by
  unfold Env.sitesOf; rw [allPos_envB]
  by_cases hl : l = 0
  · subst hl; rfl
  · have : (0 = l) = False := propext ⟨fun h => hl h.symm, False.elim⟩
    simp [valAt, envB, selfX, cellR, rB, Value.sitesOf, hl, this]

theorem liveLoan_envB {l : Nat} (h : liveLoan (envB name piX cd) l = true) : l = 0 := by
  rw [liveLoan, findBorrow, allPos_envB] at h
  by_cases hl : l = 0
  · exact hl
  · have hb : (0 == l) = false := by simp; omega
    simp [List.find?, valAt, envB, selfX, cellR, rB, Value.holdsBorrow, hb] at h

end Start

open Start

/-! ## The relation at the start -/

section
variable (dm : DataModel) (D : Decisions) (ρ : Assignment) (φ φ' : Future)

theorem positions_SBW (sb : SBinding) (d : DeclInfo) (a : Sem) :
    (SBW sb d a).positions = [.bind 0 0, .bind 1 0, .bind 1 1] := by
  simp [SBW, SState.positions, List.range']

theorem liveLabels_SBW (sb : SBinding) (d : DeclInfo) (a : Sem) : (SBW sb d a).liveLabels = [0] := by
  unfold SState.liveLabels; rw [positions_SBW]; simp [SBW]

theorem holderTy_SBW (sb : SBinding) (d : DeclInfo) (a : Sem) : holderTy (SBW sb d a) 0 = TyM.nat := by
  have hh : (SBW sb d a).holderOf 0 = some (.bind 1 1) := by
    unfold SState.holderOf; rw [positions_SBW]; simp [SBW]
  unfold holderTy; rw [hh]; rfl

/-- **The checker's start state of a function with one borrow parameter `r : &Nat` is related to `fixBodyAt`'s**
(docs/31 D138 built), every clause of `Rel`, with no renaming, at every future: under `σ0 ↦ m`, against the state
with the cell, `self` (the stage-0 closure) and `r` holding `m`, label `0` held by `r`, lent at the cell, recorded `m`. -/
theorem rel_startB (name : String) (piX : Value) (hpi : ∃ caps t rd, piX = .tPi caps t rd) (cd : DeclInfo) (out : PiCod)
    (st : MState) (hst : st.env = envB name piX cd) (hnl : st.nextLoan = 1) (m : Nat) :
    Rel (KB name out dm D φ) (ColumnI.ρAt ρ m) φ' id st (SBW (selfS dm.read φ out cd) (.ref .other) (.el0 Nat m)) := by
  obtain ⟨caps, t, rd, rfl⟩ := hpi
  have hmean : ∀ ψ p, Env.mean (KB name out dm D φ).dm (KB name out dm D φ).M (KB name out dm D φ).Γ (ColumnI.ρAt ρ m) ψ
      (envB name (.tPi caps t rd) cd) p = (SBW (selfS dm.read φ out cd) (.ref .other) (.el0 Nat m)).valAt p ψ := by
    intro ψ p
    rcases p with ⟨f, i⟩ | ⟨f, i⟩
    · rcases f with _ | _ | f
      · rcases i with _ | i
        · rfl
        · rfl
      · rcases i with _ | _ | i
        · show ((KB name out dm D φ).C.global name).1 = _
          simp [KB, CB, SBW, selfS, SState.valAt]
        · rfl
        · rfl
      · rfl
    · rcases f with _ | _ | f <;> rfl
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  -- skel
  · have h0 : Binding.refTy (KB name out dm D φ).dm (KB name out dm D φ).M (KB name out dm D φ).Γ (ColumnI.ρAt ρ m)
        (envB name (.tPi caps t rd) cd) 1 0 (selfX name (.tPi caps t rd) cd) = .plain (selfTyB dm.read out) := by
      rw [Binding.refTy_marked _ _ _ _ _ _ _ _ 0 rfl rfl]
      simp [KB, CB, selfX, RunCtx.M, codeMeaning]
    unfold SM' MState.sstate
    rw [hst]
    simp only [envB, List.zipIdx, List.map, Nat.zero_add]
    rw [show (#[{ binds := #[cellR] }, { binds := #[selfX name (.tPi caps t rd) cd, rB (.borrow 0 (.abs 0))] }] : Env)
      = envB name (.tPi caps t rd) cd from rfl, h0]
    rfl
  -- fresh
  · intro l hl _; rw [hnl] at hl; exact hl
  -- sim
  · intro ψ _ p _
    show Env.mean _ _ _ _ _ st.env p = _
    rw [hst]; exact hmean ψ p
  · intro p l _ h
    show (SBW _ _ _).shape p = some l
    change Env.shape st.env p = some l at h
    rw [hst, shape_envB] at h
    simp only [SBW]; exact h
  · intro p l _ h
    refine ⟨l, ?_, rfl⟩
    show Env.shape st.env p = some l
    rw [hst, shape_envB]; exact h
  · intro f i l h
    change Env.shape st.env (.temp f i) = some l at h
    rw [hst, shape_envB] at h; simp at h
  · intro f j l h
    simp [SBW] at h
  -- inj
  · intro l l' _ _ h; exact h
  -- sites
  · intro l hl x
    rw [hst] at hl ⊢
    obtain rfl := liveLoan_envB hl
    rw [sitesOf_envB]
    rfl
  -- holders
  · intro p l h
    rw [positions_SBW]
    simp only [SBW] at h
    split at h
    · rename_i hp; subst hp; simp
    · cases h
  -- records
  · intro l hl
    have : l = 0 := by
      have h := hl; unfold SState.Live at h; rw [liveLabels_SBW] at h; simpa using h
    subst this
    refine ⟨by simp [SBW, Sem.whole], ?_⟩
    rw [holderTy_SBW]
    exact ⟨m, rfl⟩

/-- **`W`'s start**: the checker's start state for `W` (`stW`) under `σ0 ↦ m` is related to `fixBodyAt`'s body state
at the argument `m`, for every `fb` the `.fix` clause reads `&Nat` with at `Nat`, `.ref .other`, and the codomain
`Nat` at `.other`. No assumed fact. -/
theorem rel_startW (fb : List PBind × PBind) (h1 : fb.1 = [(fun _ => .plain TyM.nat, .ref .other)]) (h2 : fb.2.2 = .other)
    (m : Nat) :
    Rel (KB "W" outW dm D φ) (ColumnI.ρAt ρ m) φ' id stW
      (startS fb (selfS dm.read φ outW fb.2.2) ⟨true, fun _ => TyM.nat⟩ (.el0 Nat m)) := by
  rw [startS_eq fb h1, h2]
  exact rel_startB dm D ρ φ φ' "W" piW ⟨_, _, _, rfl⟩ .other outW stW stW_env rfl m

/-- **`K`'s start**: the same for `K` (`stK`), whose codomain `&Nat` is read `.ref .other`. No assumed fact. -/
theorem rel_startK (fb : List PBind × PBind) (h1 : fb.1 = [(fun _ => .plain TyM.nat, .ref .other)])
    (h2 : fb.2.2 = .ref .other) (m : Nat) :
    Rel (KB "K" outK dm D φ) (ColumnI.ρAt ρ m) φ' id stK
      (startS fb (selfS dm.read φ outK fb.2.2) ⟨true, fun _ => TyM.nat⟩ (.el0 Nat m)) := by
  rw [startS_eq fb h1, h2]
  exact rel_startB dm D ρ φ φ' "K" piK ⟨_, _, _, rfl⟩ (.ref .other) outK stK stK_env rfl m

end

end Ochr.Meaning.Steps.Form.ColumnW
