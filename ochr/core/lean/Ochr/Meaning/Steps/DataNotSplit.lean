import Ochr.Meaning.Steps.DataNotRun
import Ochr.Meaning.Steps.ColumnPSplit

/-!
# The column `Not`: the split's step in the tail form (lead21, 2026-11-22; docs/31 D147)

`split_simNot`: `TailSim` for `Not`'s body from every state with `stNot`'s kernel, in the context `KNot` (the
declarations `[B]`, the global `Not` its stage-0 closure, any `Δ` meeting `Pre`), at a table deciding as the checker
does (`ParDecNot`), for every continuation that keeps the counters in world `T` (`KeepsAtT`). Assumes the checker
fact `SplitNotInv`; what it asks of the data model is in `Pre` (its `CtxS`: the model covers `B` and is faithful to
`[B]`), a hypothesis of every step, discharged at the column's start by `DataModelB`.

Under an assignment `ρ` the unknown `σ0 : B` means a member of `B`, so one of its two constructors (`mem_B`: in
EVERY data model, since they have no field). The leaf is that constructor's world: `Out` with `ρ' = ρ` and
`Δ' = Δ` (no world makes an unknown). On the reference's side the run is `runNot`'s, the state kept; the relation
follows the checker's state through the refinement (the unknown's meaning replaced by the constructor value's,
equal under `ρ`: `rel_transfer`), and nothing else changes.
-/

namespace Ochr.Meaning.Steps.Form.ColumnNot

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Ochr.Meaning.Steps.Form.ColumnI (NoBorrow liveLabels_of_rel)
open Ochr.Meaning.Steps.Form.ColumnP (rel_transfer kern_of_env absTyM_nat)

/-! ## The context -/

/-- `Π(b : B). B` as the reference reads it: the domain and the codomain `B`. -/
def psN (dm : DataModel) : List PiDom := [⟨false, fun _ => tyBM dm⟩]
def outN (dm : DataModel) : PiCod := ⟨false, fun _ => tyBM dm⟩

/-- The stage-0 closure's type: `Π(b : B). Unit` (the weakened codomain at bound `0`). -/
noncomputable def selfTyN (dm : DataModel) : TyM := piTyAt dm.read 1 (psN dm) (weakCod 1 (fixRank none) 0 (outN dm))

/-- The stage-0 closure: `()` at every argument. -/
noncomputable def selfSemN (dm : DataModel) (φ : Future) : Sem :=
  closureAt dm.read 1 φ (psN dm) (weakCod 1 (fixRank none) 0 (outN dm)) (stageFn 1 (psN dm) (fixRank none) 0 (fun _ => none))

/-- The globals: `Not` means its stage-0 closure; nothing else is read. -/
noncomputable def CN (dm : DataModel) (φ : Future) : CodeMeaning :=
  { global := fun n => if n = "Not" then (selfSemN dm φ, .plain (selfTyN dm)) else (.el0 Nat 0, .plain TyM.nat),
    sealed := fun _ _ _ _ => .err, clo := fun _ _ _ _ _ => .err,
    pi := fun _ _ _ _ _ => TyM.err, paramTy := fun _ _ _ _ => .plain TyM.err }

/-- The run's context while `Not`'s body is checked, at the unknowns' types `Δ`: the declarations `B :: rest`, the
whole program's list of which the checker's `[B]` is a prefix (docs/31 D174; `rest = []` is the column as first
built, D147). -/
noncomputable def KNot (dm : DataModel) (D : Decisions) (φ : Future) (Δ : Nat → TyS) (rest : List IndDecl := []) :
    RunCtx :=
  { dm := dm, Γ := declB :: rest, C := CN dm φ, D := D, Δ := Δ, cur := some ("Not", 0) }

/-- **What the column assumes of the data model** (one named hypothesis): it covers `B` and is faithful to the
declarations `[B]` (`CtxFaithful`: `B`'s field and parameter types, of which there are none, and the records at
parameter lists, which for a declaration without parameters constrain only junk lists). An instance:
`dataModelB_triv`. -/
def DataModelB (dm : DataModel) (D : Decisions) (rest : List IndDecl := []) : Prop :=
  dm.covers declB ∧ (∀ d ∈ rest, dm.covers d) ∧ ∀ φ Δ, DeclsFaithful (KNot dm D φ Δ rest) [declB]

section
variable {dm : DataModel} {D : Decisions} {φ : Future} {rest : List IndDecl}

theorem find_gNot {n : String} {g : GDef} (h : [gNot].find? (·.name == n) = some g) : n = "Not" ∧ g = gNot := by
  simp only [List.find?_cons, List.find?_nil] at h
  split at h
  · rename_i hn; cases h; exact ⟨(beq_iff_eq.mp hn).symm, rfl⟩
  · cases h

/-- **The context's part at every state of `Not`'s body** (any `Δ`), under `DataModelB`. -/
theorem ctxS_Not (hdm : DataModelB dm D rest) (Δ : Nat → TyS) {st : MState} (hg : st.globals = [gNot])
    (hi : st.inds = [declB]) : CtxS (KNot dm D φ Δ rest) st where
  inds := hi ▸ ⟨rest, rfl⟩
  covers := fun d h => by
    simp only [KNot, List.mem_cons] at h
    rcases h with rfl | h
    · exact hdm.1
    · exact hdm.2.1 d h
  faithful := hi ▸ hdm.2.2 φ Δ
  noLabel := fun n => by simp only [KNot, CN]; split <;> rfl
  globals := {
    ty := fun n g hf hc => by rw [hg] at hf; exact absurd (by rw [(find_gNot hf).1]; rfl) hc
    const := fun n g hf hn => by rw [hg] at hf; rw [(find_gNot hf).2] at hn; cases hn
    fn := fun n g t hf _ hc => by rw [hg] at hf; exact absurd (by rw [(find_gNot hf).1]; rfl) hc
    mem := fun n g hf hc => by rw [hg] at hf; exact absurd (by rw [(find_gNot hf).1]; rfl) hc
    memBelow := fun n g b hf hcur => by
      rw [hg] at hf
      obtain ⟨rfl, rfl⟩ := find_gNot hf
      simp only [KNot, Option.some.injEq, Prod.mk.injEq, true_and] at hcur
      subst hcur
      refine ⟨1, φ, psN dm, outN dm, fun _ => none,
        ⟨Nat.le_succ_of_le (Nat.le_succ 1), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩,
        fun _ _ _ h => absurd h (Nat.not_lt_zero _), ?_, ?_, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
      · simp only [KNot, CN]; rfl
      · simp only [KNot, CN]; rfl }

/-- The meaning of `B` as the checker's type value. -/
theorem meanV_tyB (K : RunCtx) (hΓ : K.Γ.find? (·.name == "B") = some declB) (ρ : Assignment) (ψ : Future)
    (h : TyS) : meanV K ρ ψ h tyB = .ty (tyBM K.dm) := by
  simp only [meanV, tyB, hΓ]
  try dsimp only
  rw [if_pos (by simp [meanParams])]
  simp [meanParams, tyBM, recB, DataModel.tyM]

/-- The meaning of a constructor value of `B`. -/
theorem meanV_ctorB (K : RunCtx) (hΓ : K.Γ.find? (·.name == "B") = some declB) (ρ : Assignment) (ψ : Future)
    (h : TyS) (c : Nat) (x : Hint) : meanV K ρ ψ h (.ind "B" c x [] []) = datB K.dm c := by
  simp only [meanV, hΓ]
  simp [meanParams, meanFields, declB, datB, recB, DataModel.ctorR]

end

/-! ## The frames of the split's states -/

/-- The values `b` holds along the split: `σ0`, `T`, `F`. -/
def BVals : List Value := [.abs 0, vT, vF]

theorem stNot_env : stNot.env = envB (.abs 0) := rfl

theorem allPos_envB (v : Value) : allPos (envB v) = [.bind 1 0, .bind 1 1] := by
  rw [allPos_eq]; simp [envB, frameAllPos, List.range_succ]

theorem values_envB (v : Value) : Env.values (envB v) = [.gfn "Not", v] := by
  rw [Env.values, allPos_envB]; rfl

theorem shape_envB {v : Value} (hv : v ∈ BVals) (p : Pos) : Env.shape (envB v) p = none := by
  simp only [BVals, List.mem_cons, List.not_mem_nil, or_false] at hv
  unfold Env.shape
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · rfl
    · rcases i with _ | _ | i
      · rfl
      · rcases hv with rfl | rfl | rfl <;> rfl
      · rfl
    · rfl
  · rcases f with _ | _ | f <;> rfl

theorem liveLoan_envB {v : Value} (hv : v ∈ BVals) (l : Nat) : liveLoan (envB v) l = false := by
  simp only [BVals, List.mem_cons, List.not_mem_nil, or_false] at hv
  rw [liveLoan, findBorrow, allPos_envB]
  rcases hv with rfl | rfl | rfl <;> rfl

theorem sitesOf_envB {v : Value} (hv : v ∈ BVals) (l : Nat) : Env.sitesOf (envB v) l = [] := by
  simp only [BVals, List.mem_cons, List.not_mem_nil, or_false] at hv
  unfold Env.sitesOf; rw [allPos_envB]
  rcases hv with rfl | rfl | rfl <;> simp [valAt, envB, selfNot, bB, Value.sitesOf, vT, vF, Value.sitesOfFields]

theorem occurs_envB {v : Value} (hv : v ∈ BVals) (st : MState) (he : st.env = envB v) (l : Nat) : ¬ st.Occurs l := by
  simp only [BVals, List.mem_cons, List.not_mem_nil, or_false] at hv
  rintro ⟨w, hw, h⟩
  rw [he, values_envB] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact Bool.false_ne_true h
  · rcases hv with rfl | rfl | rfl <;> exact Bool.false_ne_true h

section
variable {dm : DataModel} {D : Decisions} {φ : Future} {rest : List IndDecl}

/-- The skeleton of a state with `envB v`'s frames: the function's own binding at `selfTyN`, `b` at `B`. -/
theorem skel_envB (Δ : Nat → TyS) (ρ : Assignment) (st : MState) (v : Value) (he : st.env = envB v) :
    (SM' (KNot dm D φ Δ rest) ρ st).env.map (fun fr => fr.binds.map bindSkel) =
      [[], [(selfTyN dm, .pi (.ind "B" [])), (tyBM dm, .ind "B" [])]] := by
  unfold SM' MState.sstate; rw [he]
  have h0 : Binding.refTy (KNot dm D φ Δ rest).dm (KNot dm D φ Δ rest).M (KNot dm D φ Δ rest).Γ ρ (envB v) 1 0 selfNot =
      .plain (selfTyN dm) := by
    rw [Binding.refTy_marked _ _ _ _ _ _ _ _ 0 rfl rfl]
    simp [KNot, CN, selfNot, RunCtx.M, codeMeaning]
  have h1 : Binding.refTy (KNot dm D φ Δ rest).dm (KNot dm D φ Δ rest).M (KNot dm D φ Δ rest).Γ ρ (envB v) 1 1 (bB v) =
      .plain (tyBM dm) := by
    rw [Binding.refTy_unmarked _ _ _ _ _ _ _ _ rfl]
    show TyS.plain (meanV (KNot dm D φ Δ rest) ρ (fun _ => .err) (.plain TyM.err) tyB).asTy = _
    rw [meanV_tyB _ rfl]; rfl
  simp only [envB, List.zipIdx, List.map, Nat.zero_add]
  simp only [bindSkel]; erw [h0, h1]; rfl

/-- A position of `envB v` other than `b` means what it means in any other such state. -/
theorem mean_envB_other (Δ Δ' : Nat → TyS) (ρ ρ' : Assignment) (ψ ψ' : Future) (v v' : Value) {p : Pos}
    (hp : p ≠ .bind 1 1) :
    Env.mean (KNot dm D φ Δ' rest).dm (KNot dm D φ Δ' rest).M (KNot dm D φ Δ' rest).Γ ρ' ψ' (envB v') p =
      Env.mean (KNot dm D φ Δ rest).dm (KNot dm D φ Δ rest).M (KNot dm D φ Δ rest).Γ ρ ψ (envB v) p := by
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · rfl
    · rcases i with _ | _ | i
      · rfl
      · exact absurd rfl hp
      · rfl
    · rfl
  · rcases f with _ | _ | f <;> rfl

theorem mean_envB_b (Δ : Nat → TyS) (ρ : Assignment) (ψ : Future) (v : Value) :
    Env.mean (KNot dm D φ Δ rest).dm (KNot dm D φ Δ rest).M (KNot dm D φ Δ rest).Γ ρ ψ (envB v) (.bind 1 1) =
      Value.mean (KNot dm D φ Δ rest).dm (KNot dm D φ Δ rest).M (KNot dm D φ Δ rest).Γ ρ ψ
        (Value.tyS (KNot dm D φ Δ rest).dm (KNot dm D φ Δ rest).M (KNot dm D φ Δ rest).Γ ρ tyB) v := rfl

theorem mean_stNot_self (Δ : Nat → TyS) (ρ : Assignment) (ψ : Future) :
    Env.mean (KNot dm D φ Δ rest).dm (KNot dm D φ Δ rest).M (KNot dm D φ Δ rest).Γ ρ ψ stNot.env (.bind 1 0) = selfSemN dm φ := by
  show ((KNot dm D φ Δ rest).C.global "Not").1 = _
  simp [KNot, CN]

/-- Two states with `envB`'s frames whose `b` means the same are read alike (`MState.mean`). -/
theorem mean_envB_eq (Δ Δ' : Nat → TyS) (ρ ρ' : Assignment) {st st' : MState} {v v' : Value}
    (he : st.env = envB v) (he' : st'.env = envB v') (hv : v ∈ BVals) (hv' : v' ∈ BVals)
    (hn : ∀ ψ, Env.mean (KNot dm D φ Δ' rest).dm (KNot dm D φ Δ' rest).M (KNot dm D φ Δ' rest).Γ ρ' ψ (envB v') (.bind 1 1) =
      Env.mean (KNot dm D φ Δ rest).dm (KNot dm D φ Δ rest).M (KNot dm D φ Δ rest).Γ ρ ψ (envB v) (.bind 1 1)) :
    MState.mean (KNot dm D φ Δ' rest).dm (KNot dm D φ Δ' rest).M (KNot dm D φ Δ' rest).Γ ρ' st' =
      MState.mean (KNot dm D φ Δ rest).dm (KNot dm D φ Δ rest).M (KNot dm D φ Δ rest).Γ ρ st := by
  unfold MState.mean
  rw [he, he', allPos_envB, allPos_envB]
  congr 1
  · funext ψ p
    by_cases hp : p = .bind 1 1
    · subst hp; exact hn ψ
    · exact mean_envB_other Δ Δ' ρ ρ' ψ ψ v v' hp
  · funext p; rw [shape_envB hv, shape_envB hv']

/-- **A reference state related to `Not`'s start state reads as `RefNot`.** -/
theorem refNot_of_rel {Δ : Nat → TyS} {ρ : Assignment} {π : Nat → Nat} {s : SState}
    (hr : Rel (KNot dm D φ Δ rest) ρ φ π stNot s) : RefNot ρ φ (selfSemN dm φ) s := by
  have hab : Value.abs 0 ∈ BVals := by simp [BVals]
  have hlive : s.liveLabels = [] := liveLabels_of_rel hr (shape_envB hab)
  have hF : RelF φ s φ ∧ TypedLive (KNot dm D φ Δ rest) s φ :=
    ⟨fun _ _ => rfl, fun l hl => absurd hl (by show l ∉ s.liveLabels; rw [hlive]; simp)⟩
  have hshape : ∀ p, s.shape p = none := by
    intro p
    rcases e : s.shape p with _ | l
    · rfl
    · have hp := hr.holders p l e
      have : l ∈ s.liveLabels := by
        unfold SState.liveLabels
        rw [List.mem_mergeSort]
        exact List.mem_filterMap.mpr ⟨p, hp, e⟩
      rw [hlive] at this; cases this
  have hsk := congrArg (fun L => L.map List.length) hr.skel
  have hlen : s.env.map (fun fr => fr.binds.length) = [0, 2] := by
    have : (SM' (KNot dm D φ Δ rest) ρ stNot).env.map (fun fr => (fr.binds.map bindSkel).length) = [0, 2] := by
      simp [SM', MState.sstate, stNot, envB]
    simpa [List.map_map, Function.comp_def, ← this] using hsk.symm
  obtain ⟨fr0, fr1, hen, h1⟩ : ∃ fr0 fr1, s.env = [fr0, fr1] ∧ fr1.binds.length = 2 := by
    rcases he : s.env with _ | ⟨fr0, _ | ⟨fr1, _ | ⟨fr2, rest⟩⟩⟩ <;> rw [he] at hlen <;> simp at hlen
    exact ⟨fr0, fr1, rfl, hlen.2⟩
  refine ⟨hlive, hshape, ?_, ?_, ⟨fr1, ?_, h1⟩, ?_, ?_, ?_⟩
  · rw [scopeOf_rel hr]; rfl
  · exact rel_resolve_ck _ ρ φ stNot s π (.var 0) (.bind 1 1) hr rfl
  · rw [hen]; rfl
  · unfold SState.topIdx; rw [hen]; rfl
  · rw [← hr.sim.1 φ hF (.bind 1 1) (by simp [IsTemp])]; rfl
  · rw [← hr.sim.1 φ hF (.bind 1 0) (by simp [IsTemp])]
    exact mean_stNot_self (dm := dm) (D := D) (φ := φ) (rest := rest) Δ ρ (fun l => φ (π l))

/-- **The relation across a refinement that changes no meaning** (`rel_transfer` at `envB`'s frames). -/
theorem rel_refineB {Δ : Nat → TyS} {ρ : Assignment} {π : Nat → Nat} {st' : MState} {s : SState} {v' : Value}
    (hr : Rel (KNot dm D φ Δ rest) ρ φ π stNot s) (he' : st'.env = envB v') (hv' : v' ∈ BVals) (hl : st'.nextLoan = 0)
    (hn : ∀ ψ, Env.mean (KNot dm D φ Δ rest).dm (KNot dm D φ Δ rest).M (KNot dm D φ Δ rest).Γ ρ ψ (envB v') (.bind 1 1) = ρ 0) :
    Rel (KNot dm D φ Δ rest) ρ φ π st' s :=
  have hv : Value.abs 0 ∈ BVals := by simp [BVals]
  rel_transfer (Δ' := Δ) hr (by
      show (SM' (KNot dm D φ Δ rest) ρ st').env.map (fun fr => fr.binds.map bindSkel) = _
      rw [skel_envB _ _ _ _ he', skel_envB _ _ _ _ stNot_env])
    (mean_envB_eq Δ Δ ρ ρ stNot_env he' hv hv' hn) hl
    (fun l => ⟨fun h => absurd h (occurs_envB hv' st' he' l), fun h => absurd h (occurs_envB hv stNot stNot_env l)⟩)
    (fun l => by rw [he', stNot_env, liveLoan_envB hv', liveLoan_envB hv])
    (fun l => by rw [he', stNot_env, sitesOf_envB hv', sitesOf_envB hv])

/-- `b` holding a constructor of `B` means it. -/
theorem mean_envB_ctor (Δ : Nat → TyS) (ρ : Assignment) (ψ : Future) (c : Nat) (x : Hint) :
    Env.mean (KNot dm D φ Δ rest).dm (KNot dm D φ Δ rest).M (KNot dm D φ Δ rest).Γ ρ ψ (envB (.ind "B" c x [] [])) (.bind 1 1) =
      datB dm c :=
  meanV_ctorB (KNot dm D φ Δ rest) rfl ρ ψ (Value.tyS (KNot dm D φ Δ rest).dm (KNot dm D φ Δ rest).M (KNot dm D φ Δ rest).Γ ρ tyB) c x

/-- **World `T`'s leaf is related to the reference's state after the match** (the refinement; the arm and the join
change nothing). -/
theorem rel_leafT {Δ : Nat → TyS} {ρ : Assignment} {π : Nat → Nat} {s : SState}
    (hr : Rel (KNot dm D φ Δ rest) ρ φ π stNot s) (h0 : ρ 0 = datB dm 0) : Rel (KNot dm D φ Δ rest) ρ φ π leafT s :=
  rel_refineB hr rfl (by simp [BVals]) rfl (fun ψ => by rw [h0]; exact mean_envB_ctor Δ ρ ψ 0 _)

/-- **World `F`'s leaf is related to the reference's state after the match.** -/
theorem rel_leafF {Δ : Nat → TyS} {ρ : Assignment} {π : Nat → Nat} {s : SState}
    (hr : Rel (KNot dm D φ Δ rest) ρ φ π stNot s) (h0 : ρ 0 = datB dm 1) : Rel (KNot dm D φ Δ rest) ρ φ π leafF s :=
  rel_refineB hr rfl (by simp [BVals]) rfl (fun ψ => by rw [h0]; exact mean_envB_ctor Δ ρ ψ 1 _)

end

/-! ## The leaves, with the value in flight: `Pre` -/

/-- The constructor values. -/
def CVals : List Value := [vT, vF]

/-- A leaf's frames with `b ↦ v` and the value `t` in flight. -/
def envBT (v t : Value) : Env := #[{}, { binds := #[selfNot, bB v], temps := #[t] }]

theorem allPos_envBT (v t : Value) : allPos (envBT v t) = [.bind 1 0, .bind 1 1, .temp 1 0] := by
  rw [allPos_eq]; simp [envBT, frameAllPos, List.range_succ]

theorem values_envBT (v t : Value) : Env.values (envBT v t) = [.gfn "Not", v, t] := by
  rw [Env.values, allPos_envBT]; rfl

theorem bind_envBT {v t : Value} {f i : Nat} {b : Binding}
    (h : (envBT v t)[f]?.bind (fun fr => fr.binds[i]?) = some b) :
    (f = 1 ∧ i = 0 ∧ b = selfNot) ∨ (f = 1 ∧ i = 1 ∧ b = bB v) := by
  rcases f with _ | _ | f
  · simp [envBT] at h
  · rcases i with _ | _ | i
    · simp [envBT] at h; exact .inl ⟨rfl, rfl, h.symm⟩
    · simp [envBT] at h; exact .inr ⟨rfl, rfl, h.symm⟩
    · simp [envBT] at h
  · simp [envBT] at h

theorem shape_envBT {v t : Value} (hv : v ∈ CVals) (ht : t ∈ CVals) (p : Pos) : Env.shape (envBT v t) p = none := by
  simp only [CVals, List.mem_cons, List.not_mem_nil, or_false] at hv ht
  unfold Env.shape
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · rfl
    · rcases i with _ | _ | i
      · rfl
      · rcases hv with rfl | rfl <;> rfl
      · rfl
    · rfl
  · rcases f with _ | _ | f
    · rfl
    · rcases i with _ | i
      · rcases ht with rfl | rfl <;> rfl
      · rfl
    · rfl

theorem liveLoan_envBT {v t : Value} (hv : v ∈ CVals) (ht : t ∈ CVals) (l : Nat) : liveLoan (envBT v t) l = false := by
  simp only [CVals, List.mem_cons, List.not_mem_nil, or_false] at hv ht
  rw [liveLoan, findBorrow, allPos_envBT]
  rcases hv with rfl | rfl <;> rcases ht with rfl | rfl <;> rfl

theorem place_var_of_steps {p : Place} {i : Nat} (h : p.steps = (i, [])) : p = .var i := by
  cases p with
  | var j => simp [Place.steps] at h; rw [h]
  | deref q => simp [Place.steps] at h
  | proj j q => simp [Place.steps] at h
  | field g q => simp [Place.steps] at h

theorem ckContent_envBT {v t : Value} (hv : v ∈ CVals) {p : Place} {w : Value} (h : ckContent (envBT v t) p = some w) :
    (p = .var 1 ∧ w = .gfn "Not") ∨ (p = .var 0 ∧ w = v) := by
  simp only [CVals, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hp : p.steps with ⟨i, path⟩
  simp only [ckContent, hp] at h
  unfold ckVarPos at h
  by_cases hi : i < 2
  · have hi' : i < (envBT v t)[(envBT v t).size - 1]!.binds.size := hi
    rw [if_pos hi'] at h
    simp only [Option.bind_some] at h
    have hnil : ∀ u : Value, (u = .gfn "Not" ∨ u = vT ∨ u = vF) → u.follow path = some w → path = [] ∧ w = u := by
      rintro u hu hf
      cases path with
      | nil => simp [Value.follow] at hf; exact ⟨rfl, hf.symm⟩
      | cons s ss =>
        rcases hu with rfl | rfl | rfl <;> cases s <;> simp [Value.follow, stepV, vT, vF] at hf
        all_goals (rename_i j; rcases j with _ | j <;> simp at hf)
    rcases i with _ | _ | i
    · obtain ⟨rfl, rfl⟩ := hnil v (by rcases hv with rfl | rfl <;> simp) h
      exact .inr ⟨place_var_of_steps hp, rfl⟩
    · obtain ⟨rfl, rfl⟩ := hnil _ (.inl rfl) h
      exact .inl ⟨place_var_of_steps hp, rfl⟩
    · omega
  · have hi' : ¬ i < (envBT v t)[(envBT v t).size - 1]!.binds.size := hi
    rw [if_neg hi'] at h; cases h

/-- **`Inv` at a leaf with its value in flight**, at a table reading the function's own binding as the checker does
(not as a declaration of `B`: `ShapeFacts`' (V) reads the place's declared reading). -/
theorem inv_envBT {D : Decisions} {rest : List IndDecl} (hdec : DecNot D) {st : MState} {v t : Value}
    (hv : v ∈ CVals) (ht : t ∈ CVals) (he : st.env = envBT v t) (hA : st.absTy = #[tyB]) (hn : st.nextAbs = 1)
    (hrefs : st.refs = [(0, v)]) (hg : st.goal = some tyB) (hneu : st.neutrals = []) (heta : st.etaRefs = [])
    (hd : st.absDecl = #[.other]) : Inv D (declB :: rest) st := by
  have hv' := hv; have ht' := ht
  simp only [CVals, List.mem_cons, List.not_mem_nil, or_false] at hv' ht'
  have hvals : ∀ w ∈ Env.values st.env, w = .gfn "Not" ∨ w = vT ∨ w = vF := fun w hw => by
    rw [he, values_envBT] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr hv'
    · exact .inr ht'
  have hpos : ∀ p ∈ allPos st.env, p = .bind 1 0 ∨ p = .bind 1 1 ∨ p = .temp 1 0 := fun p hp => by
    rw [he, allPos_envBT] at hp; simpa using hp
  have hshape : ∀ p, Env.shape st.env p = none := fun p => by rw [he]; exact shape_envBT hv ht p
  have hlive : ∀ l, liveLoan st.env l = false := fun l => by rw [he]; exact liveLoan_envBT hv ht l
  have hbind : ∀ {f i b}, st.env[f]?.bind (fun fr => fr.binds[i]?) = some b →
      (f = 1 ∧ i = 0 ∧ b = selfNot) ∨ (f = 1 ∧ i = 1 ∧ b = bB v) := fun hb => by rw [he] at hb; exact bind_envBT hb
  have hocc : ∀ l, ¬ st.Occurs l := by
    rintro l ⟨w, hw, h⟩
    rcases hvals w hw with rfl | rfl | rfl <;> exact Bool.false_ne_true h
  have hAT : ∀ T ∈ st.absTy.toList, T = tyB := fun T hT => by rw [hA] at hT; simpa using hT
  have hrefd : ∀ σ, st.Refd σ → σ < st.absTy.size := by
    refine MState.refd_lt st _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro w hw σ hσ; rcases hvals w hw with rfl | rfl | rfl <;> exact (Bool.false_ne_true hσ).elim
    · intro f i b T hb hT σ hσ
      rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfNot, bB] at hT <;> subst hT <;>
        exact (Bool.false_ne_true hσ).elim
    · intro f i b P ws j hb hT
      rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfNot, bB] at hT
    · intro G hG σ hσ; rw [hg] at hG; cases hG; exact (Bool.false_ne_true hσ).elim
    · intro m σ' h; rw [hneu] at h; cases h
    · intro σ' w h; rw [heta] at h; cases h
    · intro σ' T h σ hσ
      have := hAT T (Array.mem_toList_iff.mpr (Array.mem_of_getElem? h)); subst this
      exact (Bool.false_ne_true hσ).elim
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  -- (WF1)
  · intro p hp
    rcases hpos p hp with rfl | rfl | rfl <;> rw [he]
    · exact Bool.false_ne_true
    · rcases hv' with rfl | rfl <;> exact Bool.false_ne_true
    · rcases ht' with rfl | rfl <;> exact Bool.false_ne_true
  · intro p _ q _ l h; rw [hshape] at h; cases h
  -- (WF2)
  · intro w hw l hl; rcases hvals w hw with rfl | rfl | rfl <;> cases hl
  · intro l
    have : (Env.values st.env).flatMap Value.outerLoans = [] := by
      rw [he, values_envBT]
      rcases hv' with rfl | rfl <;> rcases ht' with rfl | rfl <;> rfl
    rw [this]; exact Nat.zero_le _
  -- (WF3)
  · refine ⟨fun a => ⟨a, fun b ⟨p, hp, w, hw, _⟩ => ?_⟩⟩
    rcases hpos p hp with rfl | rfl | rfl <;> rw [he] at hw
    · cases hw
    · rcases hv' with rfl | rfl <;> cases hw
    · rcases ht' with rfl | rfl <;> cases hw
  -- (WF4)
  · intro w hw; rcases hvals w hw with rfl | rfl | rfl <;> exact Bool.false_ne_true
  -- (WF6)
  · exact hrefd
  · intro T hT σ hσ; rw [hAT T hT] at hσ; exact (Bool.false_ne_true hσ).elim
  · intro σ r h; rw [hrefs] at h; simp only [List.mem_singleton, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨by rw [hA]; decide, fun τ hτ => ?_⟩
    rcases hv' with rfl | rfl <;> exact (Bool.false_ne_true hτ).elim
  · rw [hA, hn]; rfl
  · intro w hw l hl; rcases hvals w hw with rfl | rfl | rfl <;> cases hl
  -- (WF8)
  · intro w hw; rcases hvals w hw with rfl | rfl | rfl <;> rfl
  · intro f i b hb T hT; rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfNot, bB] at hT <;> subst hT <;> rfl
  · intro T hT; rw [hAT T hT]; rfl
  · intro G hG; rw [hg] at hG; cases hG; rfl
  -- (WF10)
  · intro w hw; rcases hvals w hw with rfl | rfl | rfl <;> rfl
  -- (WF11)
  · intro f i b hb; rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact ⟨fun T hT l => by simp [selfNot] at hT; subst hT; rfl, fun P ws j h => by simp [selfNot] at h⟩
    · exact ⟨fun T hT l => by simp [bB] at hT; subst hT; rfl, fun P ws j h => by simp [bB] at h⟩
  · intro T hT l; rw [hAT T hT]; rfl
  · intro G hG l; rw [hg] at hG; cases hG; rfl
  · intro n σ h; rw [hneu] at h; cases h
  · intro σ w h; rw [heta] at h; cases h
  -- (WF12), (WF14): no live loan
  · intro k l hk; simp [hlive] at hk
  · intro pos path _ l hl; simp [hlive] at hl
  -- (WF15), (WF16)
  · intro w hw l; rcases hvals w hw with rfl | rfl | rfl <;> rfl
  · intro w hw; rcases hvals w hw with rfl | rfl | rfl <;> rfl
  -- `ShapeFacts`
  · intro p w n args hc hpd hfind
    have htop : DecideScope.topReadings st = RN := by
      unfold DecideScope.topReadings; rw [he]; rfl
    rw [he] at hc
    rcases ckContent_envBT hv hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [htop, hdec.1] at hpd; cases hpd
    · -- at the whole program's list `B :: rest` the place's name is not forced by the list: it is the table's
      -- declared reading of `b` (`DecNot`, from the table aligned with the checker; docs/31 D177)
      rw [htop, hdec.2] at hpd; cases hpd
      rcases hv' with rfl | rfl <;> rfl
  · intro w hw l hl; rcases hvals w hw with rfl | rfl | rfl <;> cases hl
  · intro w hw; rcases hvals w hw with rfl | rfl | rfl <;> rfl
  · intro p _ h; rw [he] at h
    rcases ckContent_envBT hv h with ⟨-, h'⟩ | ⟨-, h'⟩
    · cases h'
    · rcases hv' with rfl | rfl <;> simp [vT, vF] at h'
  · intro σ r h; rw [heta] at h; cases h
  · intro σ r h; rw [heta] at h; cases h
  · intro σ l h; rw [hd] at h; rcases σ with _ | σ <;> simp at h
  -- the label counter
  · intro l h; exact absurd h (hocc l)

/-- World `T`'s leaf with `F` in flight (the kernel; `leafT.withTempT F (some B)` but for the temporary's stored
type). -/
def ltT : MState := { leafT with env := envBT vT vF }

/-- World `F`'s leaf with `T` in flight. -/
def lfT : MState := { leafF with env := envBT vF vT }

theorem norm_ltT : ltT.norm = ltT := by simp [ltT, leafT, stNot, envBT, MState.norm, Env.erase, Frame.erase]
theorem norm_lfT : lfT.norm = lfT := by simp [lfT, leafF, stNot, envBT, MState.norm, Env.erase, Frame.erase]

theorem kern_ltT : Kern ltT (leafT.withTempT vF (some tyB)) :=
  ⟨by simp [ltT, leafT, envBT, envB, MState.withTempT, Env.erase, Frame.erase], rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl⟩

theorem kern_lfT : Kern lfT (leafF.withTempT vT (some tyB)) :=
  ⟨by simp [lfT, leafF, envBT, envB, MState.withTempT, Env.erase, Frame.erase], rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl⟩

section
variable {dm : DataModel} {D : Decisions} {φ : Future} {rest : List IndDecl}

/-- `B`'s type has a level. -/
theorem tyBM_level (dm : DataModel) : (tyBM dm).level.isSome = true := by
  simp [tyBM, DataModel.tyR, declB, TyM.level]; rfl

/-- **`Pre` at a leaf with its value in flight**, under `ρ` with `σ0` the leaf's constructor. -/
theorem pre_leafB (hdm : DataModelB dm D rest) (hdec : DecNot D) (Δ : Nat → TyS)
    (ρ : Assignment) {st : MState} {v t : Value} {c : Nat} {x : Hint} (hvc : v = .ind "B" c x [] [])
    (hv : v ∈ CVals) (ht : t ∈ CVals) (h0 : ρ 0 = datB dm c) (he : st.env = envBT v t) (hA : st.absTy = #[tyB])
    (hn : st.nextAbs = 1) (hrefs : st.refs = [(0, v)]) (hg : st.goal = some tyB) (hneu : st.neutrals = [])
    (heta : st.etaRefs = []) (hd : st.absDecl = #[.other]) (hgl : st.globals = [gNot]) (hi : st.inds = [declB])
    (hnorm : st.norm = st) : Pre (KNot dm D φ Δ rest) ρ st := by
  have hv' := hv; have ht' := ht
  simp only [CVals, List.mem_cons, List.not_mem_nil, or_false] at hv' ht'
  have hnr : ∀ σ, ¬ st.Refd σ := fun σ h => by
    have h2 := MState.refd_lt st 0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ σ h
    · omega
    · intro w hw σ hσ; rw [he, values_envBT] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact (Bool.false_ne_true hσ).elim
      · rcases hv' with rfl | rfl <;> exact (Bool.false_ne_true hσ).elim
      · rcases ht' with rfl | rfl <;> exact (Bool.false_ne_true hσ).elim
    · intro f i b T hb hT σ hσ; rw [he] at hb
      rcases bind_envBT hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfNot, bB] at hT <;> subst hT <;>
        exact (Bool.false_ne_true hσ).elim
    · intro f i b P ws j hb hT; rw [he] at hb
      rcases bind_envBT hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfNot, bB] at hT
    · intro G hG σ hσ; rw [hg] at hG; cases hG; exact (Bool.false_ne_true hσ).elim
    · intro m σ' h; rw [hneu] at h; cases h
    · intro σ' w h; rw [heta] at h; cases h
    · intro σ' T h σ hσ
      rw [hA] at h
      rcases σ' with _ | σ'
      · simp at h; subst h; exact (Bool.false_ne_true hσ).elim
      · simp at h
  refine ⟨?_, ?_, ?_⟩ <;> rw [hnorm]
  · exact ctxS_Not hdm Δ hgl hi
  · exact inv_envBT hdec hv ht he hA hn hrefs hg hneu heta hd
  · refine ⟨⟨fun σ h => absurd h (hnr σ), ?_, ?_, ?_⟩, fun σ h => absurd h (hnr σ), ?_, fun σ h => absurd h (hnr σ)⟩
    · intro n σ h; rw [hneu] at h; cases h
    · intro σ w h; rw [heta] at h; cases h
    · intro σ r h; rw [hrefs] at h; simp only [List.mem_singleton, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      rw [h0, hvc]
      exact (meanV_ctorB (KNot dm D φ Δ rest) rfl ρ (fun _ => .err)
        (.plain (MState.absTyM (KNot dm D φ Δ rest).dm (KNot dm D φ Δ rest).M (KNot dm D φ Δ rest).Γ ρ st 0)) c x).symm
    · intro G h; rw [MState.goalM, hg] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
      show (meanV (KNot dm D φ Δ rest) ρ (fun _ => .err) (.plain TyM.err) tyB).asTy.level.isSome = true
      rw [meanV_tyB _ rfl]; exact tyBM_level dm

theorem pre_ltT (hdm : DataModelB dm D rest) (hdec : DecNot D) (Δ : Nat → TyS)
    (ρ : Assignment) (h0 : ρ 0 = datB dm 0) : Pre (KNot dm D φ Δ rest) ρ ltT :=
  pre_leafB hdm hdec Δ ρ rfl (by simp only [CVals, List.mem_cons]; exact .inl rfl) (by simp [CVals]) h0 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl norm_ltT

theorem pre_lfT (hdm : DataModelB dm D rest) (hdec : DecNot D) (Δ : Nat → TyS)
    (ρ : Assignment) (h0 : ρ 0 = datB dm 1) : Pre (KNot dm D φ Δ rest) ρ lfT :=
  pre_leafB hdm hdec Δ ρ rfl (by simp only [CVals, List.mem_cons]; exact .inr (.inl rfl)) (by simp [CVals]) h0 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    norm_lfT

end

/-! ## The split's step -/

/-- The stage-0 closure has no moved part. -/
theorem movedIn_selfSemN (dm : DataModel) (φ : Future) (q : Place) : Sem.movedIn (selfSemN dm φ) q = [] := by
  show Sem.movedIn (closureL (lvl0 dm.read) φ (telL (lvl0 dm.read) (psN dm) [] PUnit
    (weakCod 1 (fixRank none) 0 (outN dm))).2 _) q = []
  unfold closureL
  split
  · rfl
  · simp [Sem.movedIn]

theorem norm_stNot : stNot.norm = stNot := by simp [stNot, envB, MState.norm, Env.erase, Frame.erase]

theorem inertO_ctorB (c : Nat) (x : Hint) : (Value.ind "B" c x [] []).InertO :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ _ => by simp [Value.sitesOf, Value.sitesOfFields], rfl⟩

section
variable {dm : DataModel} {D : Decisions} {φ : Future} {rest : List IndDecl}

/-- **The split's step, in the tail form** (`TailOut` at every hint): from a checker state with `stNot`'s kernel in
the plain mode with no handed-down reading, every successful `checkTail` of `Not`'s body with a continuation that
keeps the counters in world `T`, every assignment meeting `Pre` and every reference state related to it: the
reference's run of the body in tail position succeeds, and at the leaf of the world the assignment selects `k` ran
on the checker's value and `Out` holds. Assumes the checker fact `SplitNotInv` and the decisions `ParDecNot` and the
function's own binding's reading (`hdec`), which the table aligned with the checker at `stNot` gives. -/
theorem split_outNot (hSp : SplitNotInv) (hdm : DataModelB dm D rest) {Δ : Nat → TyS} (hd : ParDecNot D)
    (hdec : DecNot D) {fuel : Nat} {k : Value → Value → M Unit}
    (hk : KeepsAtT k) {st st' : MState} {bh : Nat} (hkern : Kern stNot st) (hm : Mode st) (htd : st.tailDecl = none)
    (hrun : Runs (Ochr.checkTail fuel bodyNot k) st bh () st') {ρ : Assignment} {π : Nat → Nat} {s : SState}
    (hpre : Pre (KNot dm D φ Δ rest) ρ st) (hr : Rel (KNot dm D φ Δ rest) ρ φ π st s) (hint : TyS) :
    TailOut (KNot dm D φ Δ rest) ρ φ π st s (runT (KNot dm D φ Δ rest) ρ φ true hint bodyNot) k := by
  obtain ⟨⟨stlT, bkT, stkT, hkT, hrT⟩, ⟨stlF, bkF, stkF, hkF, hrF⟩⟩ := hSp fuel k st st' bh hkern hm htd hk hrun
  have hr0 : Rel (KNot dm D φ Δ rest) ρ φ π stNot s := hr.of_kern hkern.symm
  have hp0 : Pre (KNot dm D φ Δ rest) ρ stNot := hpre.of_kern hkern.symm
  have hrefd : stNot.norm.Refd 0 := by
    rw [norm_stNot]; exact .val (.abs 0) (by rw [stNot_env, values_envB]; simp) rfl
  obtain ⟨c, hc, h0⟩ : ∃ c, c < 2 ∧ ρ 0 = datB dm c := by
    have h := hp0.asg.asg.mem 0 hrefd (by rw [norm_stNot]; decide)
    rw [norm_stNot] at h
    have e : MState.absTyM (KNot dm D φ Δ rest).dm (KNot dm D φ Δ rest).M (KNot dm D φ Δ rest).Γ ρ stNot 0 = tyBM dm := by
      show (meanV (KNot dm D φ Δ rest) ρ (fun _ => .err) (.plain TyM.err) tyB).asTy = _
      rw [meanV_tyB _ rfl]; rfl
    rw [e] at h
    exact mem_B dm h
  have hP := refNot_of_rel hr0
  have hrun' := runNot (K := KNot dm D φ Δ rest) hd rfl hP (movedIn_selfSemN dm φ) hint hc h0
  have hsz : st.absTy.size = 1 := by rw [← hkern.absTy]; rfl
  rcases c with _ | _ | c
  · refine ⟨stlT, vF, tyB, ⟨bkT, stkT, hrT⟩, ρ, Δ, π, (datB dm 1, .plain (tyBM dm)), s,
      ⟨?_, ?_, fun σ hσ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩, hrun', meanV_ctorB _ rfl _ _ _ 1 _, ?_, rfl, ?_, ?_⟩
    · rw [hsz, ← hkT.absTy]; decide
    · rw [← hkT.nextLoan, ← hkern.nextLoan]; exact Nat.le_refl _
    · intro T e; cases e
      show (meanV (KNot dm D φ Δ rest) ρ (fun _ => .err) (.plain TyM.err) tyB).asTy = tyBM dm
      rw [meanV_tyB _ rfl]; rfl
    · exact (pre_ltT hdm hdec Δ ρ h0).of_kern (kern_ltT.trans (hkT.withTempT _ _))
    · exact rel_withTempT_inertO ((rel_leafT hr0 h0).of_kern hkT) (inertO_ctorB 1 _) _
  · refine ⟨stlF, vT, tyB, ⟨bkF, stkF, hrF⟩, ρ, Δ, π, (datB dm 0, .plain (tyBM dm)), s,
      ⟨?_, ?_, fun σ hσ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩, hrun', meanV_ctorB _ rfl _ _ _ 0 _, ?_, rfl, ?_, ?_⟩
    · rw [hsz, ← hkF.absTy]; decide
    · rw [← hkF.nextLoan, ← hkern.nextLoan]; exact Nat.le_refl _
    · intro T e; cases e
      show (meanV (KNot dm D φ Δ rest) ρ (fun _ => .err) (.plain TyM.err) tyB).asTy = tyBM dm
      rw [meanV_tyB _ rfl]; rfl
    · exact (pre_lfT hdm hdec Δ ρ h0).of_kern (kern_lfT.trans (hkF.withTempT _ _))
    · exact rel_withTempT_inertO ((rel_leafF hr0 h0).of_kern hkF) (inertO_ctorB 0 _) _
  · omega

/-- **`Not`'s body, simulated in the tail form** (`TailSim`): assumes the checker fact `SplitNotInv`; of the data
model, `DataModelB`. -/
theorem split_simNot (hSp : SplitNotInv) (hdm : DataModelB dm D rest) {Δ : Nat → TyS} (hd : ParDecNot D)
    (hdec : DecNot D) {fuel : Nat} {k : Value → Value → M Unit} (hk : KeepsAtT k)
    {st : MState} (hkern : Kern stNot st) (hm : Mode st) (htd : st.tailDecl = none) (ρ : Assignment) :
    TailSim (KNot dm D φ Δ rest) ρ φ fuel st bodyNot k :=
  fun _ _ _ _ hpre hr _ hrun => split_outNot hSp hdm hd hdec hk hkern hm htd hrun hpre hr _

end

end Ochr.Meaning.Steps.Form.ColumnNot
