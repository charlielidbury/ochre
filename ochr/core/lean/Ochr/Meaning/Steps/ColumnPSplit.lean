import Ochr.Meaning.Steps.ColumnPRun

/-!
# The column `P`: the split's step in the tail form (lead16, 2026-11-21; docs/31 D131)

`split_simP`: `TailSim` for `P`'s body from every state with `stP`'s kernel, in the context `KP` (the global `P`
its stage-0 closure, `Δ` giving `σ0` the type `Nat`), at a table deciding as the checker does (`ParDecP`), for
every continuation that keeps the counters in world `Z` (`KeepsAtZ`). Assumes the checker fact `SplitPInv`.

Under an assignment `ρ` with `ρ 0 = 0` the leaf is world `Z`'s: `Out` with `ρ' = ρ`, `Δ' = Δ`. With
`ρ 0 = a + 1` it is world `S`'s: `Out` with `ρ'` giving the fresh `σ1` the number `a` and `Δ'` its type `Nat`
(`ΔPS`); the leaf's path condition `σ0 = S(σ1)` holds of `ρ'`. On the reference's side the run is
`ColumnPRun.runP`'s; the relation follows the checker's state through the refinement (the unknown's meaning
replaced by an equal one: `rel_transfer`), the arm's move of `n.0` and the join's drop of `n`
(`botWrite_rel`, twice).
-/

namespace Ochr.Meaning.Steps.Form.ColumnP

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Ochr.Meaning.Steps.Form.ColumnI (piNat nB psI outI selfTy selfSem NoBorrow liveLabels_of_rel)

/-! ## The relation, across a change of the checker's state that changes no meaning -/

/-- **The relation reads the checker's state through its reading** (`SM'`'s skeleton, the meaning, the label
counter, the labels that occur, the live loans and their sites): a change of the checker's state, the assignment
and `Δ` that keeps all of these keeps the relation, with the reference state as it was. -/
theorem rel_transfer {K : RunCtx} {ρ ρ' : Assignment} {φ : Future} {π : Nat → Nat} {Δ' : Nat → TyS}
    {st st' : MState} {s : SState} (hr : Rel K ρ φ π st s)
    (e1 : (SM' { K with Δ := Δ' } ρ' st').env.map (fun fr => fr.binds.map bindSkel) =
      (SM' K ρ st).env.map (fun fr => fr.binds.map bindSkel))
    (e2 : MState.mean K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st' = MState.mean K.dm K.M K.Γ ρ st)
    (hl : st'.nextLoan = st.nextLoan) (e3 : ∀ l, st'.Occurs l ↔ st.Occurs l)
    (e4 : ∀ l, liveLoan st'.env l = liveLoan st.env l) (e5 : ∀ l, Env.sitesOf st'.env l = Env.sitesOf st.env l) :
    Rel { K with Δ := Δ' } ρ' φ π st' s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, hr.holders, hr.records⟩
  · rw [e1]; exact hr.skel
  · intro l hl' ho; rw [hl] at hl'; exact hr.fresh l hl' ((e3 l).mp ho)
  · rw [e2]; exact hr.sim
  · intro l l' h1 h2; rw [e4] at h1 h2; exact hr.inj l l' h1 h2
  · intro l h x; rw [e5]; rw [e4] at h; exact hr.sites l h x

/-! ## `stP` -/

theorem shape_stP (p : Pos) : Env.shape stP.env p = none := by
  unfold Env.shape
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · rfl
    · rcases i with _ | _ | i <;> rfl
    · rfl
  · rcases f with _ | _ | f <;> rfl

theorem noBorrow_stP : NoBorrow stP.env := shape_stP

section
variable {dm : DataModel} {D : Decisions} {φ : Future} {Δ : Nat → TyS}

theorem mean_stP_n (ρ : Assignment) (ψ : Future) :
    Env.mean (KP dm D φ Δ).dm (KP dm D φ Δ).M (KP dm D φ Δ).Γ ρ ψ stP.env (.bind 1 1) = ρ 0 := rfl

theorem mean_stP_self (ρ : Assignment) (ψ : Future) :
    Env.mean (KP dm D φ Δ).dm (KP dm D φ Δ).M (KP dm D φ Δ).Γ ρ ψ stP.env (.bind 1 0) = selfSem dm.read φ := by
  show ((KP dm D φ Δ).C.global "P").1 = _
  simp [KP, CP]

/-- **A reference state related to `P`'s start state reads as `RefP`.** -/
theorem refP_of_rel {ρ : Assignment} {π : Nat → Nat} {s : SState} (hr : Rel (KP dm D φ Δ) ρ φ π stP s) :
    RefP ρ φ (selfSem dm.read φ) s := by
  have hlive : s.liveLabels = [] := liveLabels_of_rel hr noBorrow_stP
  have hF : RelF φ s φ ∧ TypedLive (KP dm D φ Δ) s φ :=
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
    have : (SM' (KP dm D φ Δ) ρ stP).env.map (fun fr => (fr.binds.map bindSkel).length) = [0, 2] := by
      simp [SM', MState.sstate, stP]
    simpa [List.map_map, Function.comp_def, ← this] using hsk.symm
  obtain ⟨fr0, fr1, hen, h1⟩ : ∃ fr0 fr1, s.env = [fr0, fr1] ∧ fr1.binds.length = 2 := by
    rcases he : s.env with _ | ⟨fr0, _ | ⟨fr1, _ | ⟨fr2, rest⟩⟩⟩ <;> rw [he] at hlen <;> simp at hlen
    exact ⟨fr0, fr1, rfl, hlen.2⟩
  refine ⟨⟨hlive, hshape, ?_, ?_⟩, ⟨fr1, ?_, h1⟩, ?_, ?_, ?_, ?_⟩
  · rw [scopeOf_rel hr]; rfl
  · exact rel_resolve_ck _ ρ φ stP s π (.var 0) (.bind 1 1) hr rfl
  · rw [hen]; rfl
  · unfold SState.topIdx; rw [hen]; rfl
  · rw [← hr.sim.1 φ hF (.bind 1 1) (by simp [IsTemp])]; exact mean_stP_n (dm := dm) (D := D) (φ := φ) (Δ := Δ) ρ (fun l => φ (π l))
  · rw [← hr.sim.1 φ hF (.bind 1 0) (by simp [IsTemp])]; exact mean_stP_self (dm := dm) (D := D) (φ := φ) (Δ := Δ) ρ (fun l => φ (π l))
  · rw [(rel_bind_ty hr (b := nB) (f := 1) (j := 1) rfl (hp := rfl)).2]; rfl

end

/-! ## The frames of the split's states -/

/-- The frames with `n ↦ v`. -/
def envN (v : Value) : Env := #[{}, { binds := #[selfP, { nB with val := v }] }]

/-- The values `n` holds along the split: `σ0`, `Z`, `S(σ1)`, `S(⊥)`, `⊥`. -/
def NVals : List Value := [.abs 0, .zero, .succ (.abs 1), .succ .bot, .bot]

theorem stP_env : stP.env = envN (.abs 0) := rfl
theorem envBot_eq : envBot = envN .bot := rfl

theorem setAtE_envN (v w : Value) : Env.setAtE (envN v) (.bind 1 1) w = envN w := by
  simp [Env.setAtE, envN, nB]

theorem allPos_envN (v : Value) : allPos (envN v) = [.bind 1 0, .bind 1 1] := by
  rw [allPos_eq]; simp [envN, frameAllPos, List.range_succ]

theorem values_envN (v : Value) : Env.values (envN v) = [.gfn "P", v] := by
  rw [Env.values, allPos_envN]; rfl

theorem valAt_envN_n (v : Value) : valAt (envN v) (.bind 1 1) = v := rfl

theorem shape_envN {v : Value} (hv : v ∈ NVals) (p : Pos) : Env.shape (envN v) p = none := by
  simp only [NVals, List.mem_cons, List.not_mem_nil, or_false] at hv
  unfold Env.shape
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · rfl
    · rcases i with _ | _ | i
      · rfl
      · rcases hv with rfl | rfl | rfl | rfl | rfl <;> rfl
      · rfl
    · rfl
  · rcases f with _ | _ | f <;> rfl

theorem liveLoan_envN {v : Value} (hv : v ∈ NVals) (l : Nat) : liveLoan (envN v) l = false := by
  simp only [NVals, List.mem_cons, List.not_mem_nil, or_false] at hv
  rw [liveLoan, findBorrow, allPos_envN]
  rcases hv with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem sitesOf_envN {v : Value} (hv : v ∈ NVals) (l : Nat) : Env.sitesOf (envN v) l = [] := by
  simp only [NVals, List.mem_cons, List.not_mem_nil, or_false] at hv
  unfold Env.sitesOf; rw [allPos_envN]
  rcases hv with rfl | rfl | rfl | rfl | rfl <;> simp [valAt, envN, selfP, nB, Value.sitesOf]

theorem occurs_envN {v : Value} (hv : v ∈ NVals) (st : MState) (he : st.env = envN v) (l : Nat) : ¬ st.Occurs l := by
  simp only [NVals, List.mem_cons, List.not_mem_nil, or_false] at hv
  rintro ⟨w, hw, h⟩
  rw [he, values_envN] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact Bool.false_ne_true h
  · rcases hv with rfl | rfl | rfl | rfl | rfl <;> exact Bool.false_ne_true h

theorem wf1_envN {v : Value} (hv : v ∈ NVals) : WF1 (envN v) := by
  refine ⟨fun p hp => ?_, fun p _ q _ l h => by rw [shape_envN hv] at h; cases h⟩
  rw [allPos_envN] at hp
  simp only [NVals, List.mem_cons, List.not_mem_nil, or_false] at hv hp
  rcases hp with rfl | rfl
  · exact Bool.false_ne_true
  · rcases hv with rfl | rfl | rfl | rfl | rfl <;> exact Bool.false_ne_true

section
variable {dm : DataModel} {D : Decisions} {φ : Future}

/-- The skeleton of a state with `envN v`'s frames: the function's own binding at `selfTy`, `n` at `Nat`. -/
theorem skel_envN (Δ : Nat → TyS) (ρ : Assignment) (st : MState) (v : Value) (he : st.env = envN v) :
    (SM' (KP dm D φ Δ) ρ st).env.map (fun fr => fr.binds.map bindSkel) =
      [[], [(selfTy dm.read, .pi .other), (TyM.nat, .other)]] := by
  unfold SM' MState.sstate; rw [he]
  have h0 : Binding.refTy (KP dm D φ Δ).dm (KP dm D φ Δ).M (KP dm D φ Δ).Γ ρ (envN v) 1 0 selfP = .plain (selfTy dm.read) := by
    rw [Binding.refTy_marked _ _ _ _ _ _ _ _ 0 rfl rfl]
    simp [KP, CP, selfP, RunCtx.M, codeMeaning]
  have h1 : Binding.refTy (KP dm D φ Δ).dm (KP dm D φ Δ).M (KP dm D φ Δ).Γ ρ (envN v) 1 1 { nB with val := v } = .plain TyM.nat := by
    rw [Binding.refTy_unmarked _ _ _ _ _ _ _ _ rfl]; rfl
  simp only [envN, List.zipIdx, List.map, Nat.zero_add]
  simp only [bindSkel]; erw [h0, h1]; rfl

/-- A position of `envN v` other than `n` means what it means in any other such state. -/
theorem mean_envN_other (Δ Δ' : Nat → TyS) (ρ ρ' : Assignment) (ψ ψ' : Future) (v v' : Value) {p : Pos}
    (hp : p ≠ .bind 1 1) :
    Env.mean (KP dm D φ Δ').dm (KP dm D φ Δ').M (KP dm D φ Δ').Γ ρ' ψ' (envN v') p =
      Env.mean (KP dm D φ Δ).dm (KP dm D φ Δ).M (KP dm D φ Δ).Γ ρ ψ (envN v) p := by
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · rfl
    · rcases i with _ | _ | i
      · rfl
      · exact absurd rfl hp
      · rfl
    · rfl
  · rcases f with _ | _ | f <;> rfl

theorem mean_envN_n (Δ : Nat → TyS) (ρ : Assignment) (ψ : Future) (v : Value) :
    Env.mean (KP dm D φ Δ).dm (KP dm D φ Δ).M (KP dm D φ Δ).Γ ρ ψ (envN v) (.bind 1 1) =
      Value.mean (KP dm D φ Δ).dm (KP dm D φ Δ).M (KP dm D φ Δ).Γ ρ ψ (.plain TyM.nat) v := rfl

end

/-! ## The split's states, and the relation through them -/

/-- World `Z` after its refinement: `n ↦ Z`, the record `0 := Z`. -/
def stZ0 : MState :=
  { env := envN .zero, globals := [gP], nextAbs := 1, absTy := #[.tNat], absDecl := #[.other], goal := some .tNat,
    refs := [(0, .zero)] }

/-- World `S` after its refinement: the fresh `σ1 : Nat`, `n ↦ S(σ1)`, the record `0 := S(σ1)`. -/
def stS0 : MState :=
  { env := envN (.succ (.abs 1)), globals := [gP], nextAbs := 2, absTy := #[.tNat, .tNat],
    absDecl := #[.other, .other], goal := some .tNat, refs := [(0, .succ (.abs 1))] }

/-- `ρ` extended by world `S`'s fresh unknown: `σ1` is the predecessor `a`. -/
def ρS (ρ : Assignment) (a : Nat) : Assignment := fun σ => if σ = 1 then .el0 Nat a else ρ σ

section
variable {dm : DataModel} {D : Decisions} {φ : Future}

/-- Two states with `envN`'s frames whose `n` means the same are read alike (`MState.mean`). -/
theorem mean_envN_eq (Δ Δ' : Nat → TyS) (ρ ρ' : Assignment) {st st' : MState} {v v' : Value}
    (he : st.env = envN v) (he' : st'.env = envN v') (hv : v ∈ NVals) (hv' : v' ∈ NVals)
    (hn : ∀ ψ, Value.mean (KP dm D φ Δ').dm (KP dm D φ Δ').M (KP dm D φ Δ').Γ ρ' ψ (.plain TyM.nat) v' =
      Value.mean (KP dm D φ Δ).dm (KP dm D φ Δ).M (KP dm D φ Δ).Γ ρ ψ (.plain TyM.nat) v) :
    MState.mean (KP dm D φ Δ').dm (KP dm D φ Δ').M (KP dm D φ Δ').Γ ρ' st' =
      MState.mean (KP dm D φ Δ).dm (KP dm D φ Δ).M (KP dm D φ Δ).Γ ρ st := by
  unfold MState.mean
  rw [he, he', allPos_envN, allPos_envN]
  congr 1
  · funext ψ p
    by_cases hp : p = .bind 1 1
    · subst hp; rw [mean_envN_n, mean_envN_n]; exact hn ψ
    · exact mean_envN_other Δ Δ' ρ ρ' ψ ψ v v' hp
  · funext p; rw [shape_envN hv, shape_envN hv']

/-- The relation across a refinement that changes no meaning (`rel_transfer` at `envN`'s frames). -/
theorem rel_refine {Δ Δ' : Nat → TyS} {ρ ρ' : Assignment} {π : Nat → Nat} {st' : MState} {s : SState} {v' : Value}
    (hr : Rel (KP dm D φ Δ) ρ φ π stP s) (he' : st'.env = envN v') (hv' : v' ∈ NVals) (hl : st'.nextLoan = 0)
    (hn : ∀ ψ, Value.mean (KP dm D φ Δ').dm (KP dm D φ Δ').M (KP dm D φ Δ').Γ ρ' ψ (.plain TyM.nat) v' = ρ 0) :
    Rel (KP dm D φ Δ') ρ' φ π st' s :=
  have hv : Value.abs 0 ∈ NVals := by simp [NVals]
  rel_transfer (Δ' := Δ') hr (by
      show (SM' (KP dm D φ Δ') ρ' st').env.map (fun fr => fr.binds.map bindSkel) = _
      rw [skel_envN _ _ _ _ he', skel_envN _ _ _ _ stP_env])
    (mean_envN_eq Δ Δ' ρ ρ' stP_env he' hv hv' hn) hl
    (fun l => ⟨fun h => absurd h (occurs_envN hv' st' he' l), fun h => absurd h (occurs_envN hv stP stP_env l)⟩)
    (fun l => by rw [he', stP_env, liveLoan_envN hv', liveLoan_envN hv])
    (fun l => by rw [he', stP_env, sitesOf_envN hv', sitesOf_envN hv])

theorem kern_of_env {a b : MState} (he : a.env = b.env) (hg : a.globals = b.globals) (hi : a.inds = b.inds)
    (hl : a.nextLoan = b.nextLoan) (hna : a.nextAbs = b.nextAbs) (ht : a.absTy = b.absTy) (hd : a.absDecl = b.absDecl)
    (hr : a.refs = b.refs) (he2 : a.etaRefs = b.etaRefs) (hgo : a.goal = b.goal) (hn : a.neutrals = b.neutrals)
    (hs : a.liveScope = b.liveScope) : Kern a b :=
  ⟨by rw [he], hg, hi, hl, hna, ht, hd, hr, he2, hgo, hn, hs⟩

/-- **World `Z`'s leaf is related to the reference's state after the match** (the refinement, then the join's
drop of `n`). -/
theorem rel_leafZ {Δ : Nat → TyS} {ρ : Assignment} {π : Nat → Nat} {s : SState}
    (hr : Rel (KP dm D φ Δ) ρ φ π stP s) (h0 : ρ 0 = .el0 Nat 0) :
    Rel (KP dm D φ Δ) ρ φ π leafZ (dropN (KP dm D φ Δ) s) := by
  have hz : Value.zero ∈ NVals := by simp [NVals]
  have h₀ : Rel (KP dm D φ Δ) ρ φ π stZ0 s := rel_refine (Δ' := Δ) hr rfl hz rfl (fun _ => h0.symm)
  have hsp : Pos.bind 1 1 ∈ s.positions := (rel_bind_ty hr (b := nB) (f := 1) (j := 1) rfl (hp := rfl)).1
  have h₁ := botWrite_rel (KP dm D φ Δ) ρ φ stZ0 s π 1 1 [] .bot h₀ (wf1_envN hz)
    (by show _ ∈ allPos (envN _); rw [allPos_envN]; simp) hsp (by show Value.updAt _ [] _ = _; rw [Value.updAt])
    (fun _ => shape_envN hz _) (fun l hl => by simp [stZ0, liveLoan_envN hz] at hl)
    ⟨rfl, rfl⟩ (fun _ => by rw [NatAlong]; trivial)
  refine h₁.of_kern (kern_of_env ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
  show Env.setAtE (envN .zero) (.bind 1 1) .bot = envBot
  rw [setAtE_envN]; rfl

/-- **World `S`'s leaf is related to the reference's state after the match**, under `ρ` extended by `σ1 ↦ a` and
`Δ` by `σ1 : Nat` (the refinement, the arm's move of `n.0`, the join's drop of `n`). -/
theorem rel_leafS {Δ : Nat → TyS} {ρ : Assignment} {π : Nat → Nat} {s : SState} {a : Nat}
    (hr : Rel (KP dm D φ Δ) ρ φ π stP s) (h0 : ρ 0 = .el0 Nat (a + 1)) :
    Rel (KP dm D φ ΔPS) (ρS ρ a) φ π leafS (dropN (KP dm D φ ΔPS) (setN0 (KP dm D φ Δ) s)) := by
  have hS : Value.succ (.abs 1) ∈ NVals := by simp [NVals]
  have hSb : Value.succ .bot ∈ NVals := by simp [NVals]
  have h₀ : Rel (KP dm D φ ΔPS) (ρS ρ a) φ π stS0 s := rel_refine (Δ' := ΔPS) hr rfl hS rfl (fun ψ => by
    show (Value.mean _ _ _ (ρS ρ a) ψ (.plain TyM.nat) (.abs 1)).succ = _
    rw [h0]; show (Sem.el0 Nat a).succ = _; rw [Sem.succ_el0])
  have hsp : Pos.bind 1 1 ∈ s.positions := (rel_bind_ty hr (b := nB) (f := 1) (j := 1) rfl (hp := rfl)).1
  have h₁ := botWrite_rel (KP dm D φ ΔPS) (ρS ρ a) φ stS0 s π 1 1 [.proj 0] (.succ .bot) h₀ (wf1_envN hS)
    (by show _ ∈ allPos (envN _); rw [allPos_envN]; simp) hsp
    (by show Value.updAt _ [.proj 0] (.succ (.abs 1)) = _; simp [Value.updAt])
    (fun e => by cases e) (fun l hl => by simp [stS0, liveLoan_envN hS] at hl)
    ⟨rfl, rfl⟩ (fun ψ => by
      show NatAlong _ _ _ _ _ [.proj 0] (Value.succ (.abs 1))
      rw [NatAlong]
      refine ⟨⟨a, ?_⟩, by rw [NatAlong]; trivial⟩
      show (ρS ρ a 1).asNat = some a
      simp [ρS, Sem.asNat_el0])
  have he₁ : Env.setAtE stS0.env (.bind 1 1) (.succ .bot) = envN (.succ .bot) := setAtE_envN _ _
  have h₂ := botWrite_rel (KP dm D φ ΔPS) (ρS ρ a) φ { stS0 with env := Env.setAtE stS0.env (.bind 1 1) (.succ .bot) }
    _ π 1 1 [] .bot h₁ (by rw [he₁]; exact wf1_envN hSb)
    (by rw [he₁]; show _ ∈ allPos (envN _); rw [allPos_envN]; simp)
    (by rw [SState.positions_setAt]; exact hsp) (by rw [he₁]; show Value.updAt _ [] _ = _; rw [Value.updAt])
    (fun _ => by rw [he₁]; exact shape_envN hSb _) (fun l hl => by rw [he₁, liveLoan_envN hSb] at hl; cases hl)
    (by rw [he₁]; exact ⟨rfl, rfl⟩) (fun _ => by rw [NatAlong]; trivial)
  refine h₂.of_kern (kern_of_env ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
  show Env.setAtE (Env.setAtE (envN (.succ (.abs 1))) (.bind 1 1) (.succ .bot)) (.bind 1 1) .bot = envBot
  rw [setAtE_envN, setAtE_envN]; rfl

end

/-! ## The leaves, with the value in flight: `Pre` -/

/-- A leaf's frames with the value `t` in flight (`withTempT` but for the temporary's stored type). -/
def envT (t : Value) : Env := #[{}, { binds := #[selfP, nBot], temps := #[t] }]

/-- The values in flight at the leaves. -/
def TVals : List Value := [.zero, .abs 1]

theorem allPos_envT (t : Value) : allPos (envT t) = [.bind 1 0, .bind 1 1, .temp 1 0] := by
  rw [allPos_eq]; simp [envT, frameAllPos, List.range_succ]

theorem values_envT (t : Value) : Env.values (envT t) = [.gfn "P", .bot, t] := by
  rw [Env.values, allPos_envT]; rfl

theorem bind_envT {t : Value} {f i : Nat} {b : Binding} (h : (envT t)[f]?.bind (fun fr => fr.binds[i]?) = some b) :
    (f = 1 ∧ i = 0 ∧ b = selfP) ∨ (f = 1 ∧ i = 1 ∧ b = nBot) := by
  rcases f with _ | _ | f
  · simp [envT] at h
  · rcases i with _ | _ | i
    · simp [envT] at h; exact .inl ⟨rfl, rfl, h.symm⟩
    · simp [envT] at h; exact .inr ⟨rfl, rfl, h.symm⟩
    · simp [envT] at h
  · simp [envT] at h

theorem mem_values_envT {t v : Value} (ht : t ∈ TVals) (hv : v ∈ Env.values (envT t)) :
    v = .gfn "P" ∨ v = .bot ∨ v = .zero ∨ v = .abs 1 := by
  rw [values_envT] at hv
  simp only [TVals, List.mem_cons, List.not_mem_nil, or_false] at hv ht
  rcases hv with rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · rcases ht with rfl | rfl
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr rfl))

theorem shape_envT {t : Value} (ht : t ∈ TVals) (p : Pos) : Env.shape (envT t) p = none := by
  simp only [TVals, List.mem_cons, List.not_mem_nil, or_false] at ht
  unfold Env.shape
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · rfl
    · rcases i with _ | _ | i <;> rfl
    · rfl
  · rcases f with _ | _ | f
    · rfl
    · rcases i with _ | i
      · rcases ht with rfl | rfl <;> rfl
      · rfl
    · rfl

theorem liveLoan_envT {t : Value} (ht : t ∈ TVals) (l : Nat) : liveLoan (envT t) l = false := by
  simp only [TVals, List.mem_cons, List.not_mem_nil, or_false] at ht
  rw [liveLoan, findBorrow, allPos_envT]
  rcases ht with rfl | rfl <;> rfl

theorem ckContent_envT {t : Value} {p : Place} {v : Value} (h : ckContent (envT t) p = some v) :
    v = .gfn "P" ∨ v = .bot := by
  rcases hp : p.steps with ⟨i, path⟩
  simp only [ckContent, hp] at h
  unfold ckVarPos at h
  by_cases hi : i < 2
  · have hi' : i < (envT t)[(envT t).size - 1]!.binds.size := hi
    rw [if_pos hi'] at h
    simp only [Option.bind_some] at h
    have hv : ∀ w : Value, (w = .gfn "P" ∨ w = .bot) → w.follow path = some v → v = .gfn "P" ∨ v = .bot := by
      rintro w hw hf
      cases path with
      | nil => simp [Value.follow] at hf; exact hf ▸ hw
      | cons s ss => rcases hw with rfl | rfl <;> cases s <;> simp [Value.follow, stepV] at hf
    rcases i with _ | _ | i
    · exact hv _ (.inr rfl) h
    · exact hv _ (.inl rfl) h
    · omega
  · have hi' : ¬ i < (envT t)[(envT t).size - 1]!.binds.size := hi
    rw [if_neg hi'] at h; cases h

/-- The unknowns a leaf state names are below its table's size. -/
theorem refd_envT {st : MState} {t : Value} (ht : t ∈ TVals) (he : st.env = envT t)
    (hA : ∀ T ∈ st.absTy.toList, T = .tNat) (hsz : 2 ≤ st.absTy.size ∨ t = .zero)
    (hg : st.goal = some .tNat) (hneu : st.neutrals = []) (heta : st.etaRefs = []) :
    ∀ σ, st.Refd σ → σ < st.absTy.size := by
  refine MState.refd_lt st _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro v hv σ hσ; rw [he] at hv
    rcases mem_values_envT ht hv with rfl | rfl | rfl | rfl
    · exact (Bool.false_ne_true hσ).elim
    · exact (Bool.false_ne_true hσ).elim
    · exact (Bool.false_ne_true hσ).elim
    · have := abs_hasAbs_eq hσ; subst this
      rcases hsz with h | h
      · omega
      · subst h; rw [values_envT] at hv; simp at hv
  · intro f i b T hb hT σ hσ; rw [he] at hb
    rcases bind_envT hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfP, nBot, nB] at hT <;> subst hT <;>
      exact (Bool.false_ne_true hσ).elim
  · intro f i b P ws j hb hT; rw [he] at hb
    rcases bind_envT hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfP, nBot, nB] at hT
  · intro G hG σ hσ; rw [hg] at hG; cases hG; exact (Bool.false_ne_true hσ).elim
  · intro m σ' h; rw [hneu] at h; cases h
  · intro σ' v h; rw [heta] at h; cases h
  · intro σ' T h σ hσ
    have := hA T (Array.mem_toList_iff.mpr (Array.mem_of_getElem? h)); subst this
    exact (Bool.false_ne_true hσ).elim

/-- **`Inv` at a leaf with its value in flight.** -/
theorem inv_envT {D : Decisions} {st : MState} {t : Value} (ht : t ∈ TVals) (he : st.env = envT t)
    (hA : ∀ T ∈ st.absTy.toList, T = .tNat) (hsz : 2 ≤ st.absTy.size ∨ t = .zero)
    (hn : st.absTy.size = st.nextAbs)
    (hrefs : ∀ σ r, (σ, r) ∈ st.refs → σ < st.absTy.size ∧ ∀ τ, r.hasAbs τ = true → τ < st.absTy.size)
    (hg : st.goal = some .tNat) (hneu : st.neutrals = []) (heta : st.etaRefs = [])
    (hdecl : ∀ (σ l : Nat), st.absDecl[σ]? ≠ some (DeclInfo.sort l)) : Inv D [] st := by
  have hvals : ∀ v ∈ Env.values st.env, v = .gfn "P" ∨ v = .bot ∨ v = .zero ∨ v = .abs 1 := fun v hv => by
    rw [he] at hv; exact mem_values_envT ht hv
  have hpos : ∀ p ∈ allPos st.env, p = .bind 1 0 ∨ p = .bind 1 1 ∨ p = .temp 1 0 := fun p hp => by
    rw [he, allPos_envT] at hp; simpa using hp
  have hshape : ∀ p, Env.shape st.env p = none := fun p => by rw [he]; exact shape_envT ht p
  have hlive : ∀ l, liveLoan st.env l = false := fun l => by rw [he]; exact liveLoan_envT ht l
  have hbind : ∀ {f i b}, st.env[f]?.bind (fun fr => fr.binds[i]?) = some b →
      (f = 1 ∧ i = 0 ∧ b = selfP) ∨ (f = 1 ∧ i = 1 ∧ b = nBot) := fun hb => by rw [he] at hb; exact bind_envT hb
  have hocc : ∀ l, ¬ st.Occurs l := by
    rintro l ⟨v, hv, h⟩
    rcases hvals v hv with rfl | rfl | rfl | rfl <;> exact Bool.false_ne_true h
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  -- (WF1)
  · intro p hp
    rcases hpos p hp with rfl | rfl | rfl <;> rw [he]
    · exact Bool.false_ne_true
    · exact Bool.false_ne_true
    · simp only [TVals, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> exact Bool.false_ne_true
  · intro p _ q _ l h; rw [hshape] at h; cases h
  -- (WF2)
  · intro v hv l hl; rcases hvals v hv with rfl | rfl | rfl | rfl <;> cases hl
  · intro l
    have : (Env.values st.env).flatMap Value.outerLoans = [] := by
      rw [he, values_envT]
      simp only [TVals, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> rfl
    rw [this]; exact Nat.zero_le _
  -- (WF3)
  · refine ⟨fun a => ⟨a, fun b ⟨p, hp, w, hw, _⟩ => ?_⟩⟩
    rcases hpos p hp with rfl | rfl | rfl <;> rw [he] at hw
    · cases hw
    · cases hw
    · simp only [TVals, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> cases hw
  -- (WF4)
  · intro v hv; rcases hvals v hv with rfl | rfl | rfl | rfl <;> exact Bool.false_ne_true
  -- (WF6)
  · exact refd_envT ht he hA hsz hg hneu heta
  · intro T hT σ hσ; rw [hA T hT] at hσ; exact (Bool.false_ne_true hσ).elim
  · exact hrefs
  · exact hn
  · intro v hv l hl; rcases hvals v hv with rfl | rfl | rfl | rfl <;> cases hl
  -- (WF8)
  · intro v hv; rcases hvals v hv with rfl | rfl | rfl | rfl <;> rfl
  · intro f i b hb T hT; rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfP, nBot, nB] at hT <;> subst hT <;> rfl
  · intro T hT; rw [hA T hT]; rfl
  · intro G hG; rw [hg] at hG; cases hG; rfl
  -- (WF10)
  · intro v hv; rcases hvals v hv with rfl | rfl | rfl | rfl <;> rfl
  -- (WF11)
  · intro f i b hb; rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact ⟨fun T hT l => by simp [selfP] at hT; subst hT; rfl, fun P ws j h => by simp [selfP] at h⟩
    · exact ⟨fun T hT l => by simp [nBot, nB] at hT; subst hT; rfl, fun P ws j h => by simp [nBot, nB] at h⟩
  · intro T hT l; rw [hA T hT]; rfl
  · intro G hG l; rw [hg] at hG; cases hG; rfl
  · intro n σ h; rw [hneu] at h; cases h
  · intro σ v h; rw [heta] at h; cases h
  -- (WF12), (WF14): no live loan
  · intro k l hk; simp [hlive] at hk
  · intro pos path _ l hl; simp [hlive] at hl
  -- (WF15), (WF16)
  · intro v hv l; rcases hvals v hv with rfl | rfl | rfl | rfl <;> rfl
  · intro v hv; rcases hvals v hv with rfl | rfl | rfl | rfl <;> rfl
  -- `ShapeFacts`
  · intro p v n args _ _ h; simp at h
  · intro v hv l hl; rcases hvals v hv with rfl | rfl | rfl | rfl <;> cases hl
  · intro v hv; rcases hvals v hv with rfl | rfl | rfl | rfl <;> rfl
  · intro p _ h; rw [he] at h; rcases ckContent_envT h with h | h <;> cases h
  · intro σ r h; rw [heta] at h; cases h
  · intro σ r h; rw [heta] at h; cases h
  · intro σ l h; exact absurd h (hdecl σ l)
  -- the label counter
  · intro l h; exact absurd h (hocc l)

/-- World `Z`'s leaf with `Z` in flight (the kernel; `leafZ.withTempT Z (some Nat)` but for the temporary's
stored type). -/
def lzT : MState :=
  { env := envT .zero, globals := [gP], nextAbs := 1, absTy := #[.tNat], absDecl := #[.other], goal := some .tNat,
    refs := [(0, .zero)] }

/-- World `S`'s leaf with `σ1` in flight. -/
def lsT : MState :=
  { env := envT (.abs 1), globals := [gP], nextAbs := 2, absTy := #[.tNat, .tNat], absDecl := #[.other, .other],
    goal := some .tNat, refs := [(0, .succ (.abs 1))] }

theorem norm_lzT : lzT.norm = lzT := by simp [lzT, envT, MState.norm, Env.erase, Frame.erase]
theorem norm_lsT : lsT.norm = lsT := by simp [lsT, envT, MState.norm, Env.erase, Frame.erase]

theorem kern_lzT : Kern lzT (leafZ.withTempT .zero (some .tNat)) :=
  ⟨by simp [lzT, leafZ, envT, envBot, nBot, MState.withTempT, Env.erase, Frame.erase], rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl⟩

theorem kern_lsT : Kern lsT (leafS.withTempT (.abs 1) (some .tNat)) :=
  ⟨by simp [lsT, leafS, envT, envBot, nBot, MState.withTempT, Env.erase, Frame.erase], rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl⟩

section
variable {dm : DataModel} {D : Decisions} {φ : Future}

theorem find_gP {n : String} {g : GDef} (h : [gP].find? (·.name == n) = some g) : n = "P" ∧ g = gP := by
  simp only [List.find?_cons, List.find?_nil] at h
  split at h
  · rename_i hn; cases h; exact ⟨(beq_iff_eq.mp hn).symm, rfl⟩
  · cases h

/-- **The context's part at every state of `P`'s body** (any `Δ`): no declarations, `P`'s global its stage-0
closure, the function being checked. -/
theorem ctxS_P (Δ : Nat → TyS) {st : MState} (hg : st.globals = [gP]) (hi : st.inds = []) : CtxS (KP dm D φ Δ) st where
  inds := hi.symm
  covers := fun _ h => absurd h List.not_mem_nil
  faithful := fun _ _ => ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
     fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩⟩
  noLabel := fun n => by simp only [KP, CP]; split <;> rfl
  globals := {
    ty := fun n g hf hc => by rw [hg] at hf; exact absurd (by rw [(find_gP hf).1]; rfl) hc
    const := fun n g hf hn => by rw [hg] at hf; rw [(find_gP hf).2] at hn; cases hn
    fn := fun n g t hf _ hc => by rw [hg] at hf; exact absurd (by rw [(find_gP hf).1]; rfl) hc
    mem := fun n g hf hc => by rw [hg] at hf; exact absurd (by rw [(find_gP hf).1]; rfl) hc
    memBelow := fun n g b hf hcur => by
      rw [hg] at hf
      obtain ⟨rfl, rfl⟩ := find_gP hf
      simp only [KP, Option.some.injEq, Prod.mk.injEq, true_and] at hcur
      subst hcur
      refine ⟨1, φ, psI, outI, fun _ => none, ⟨Nat.le_succ_of_le (Nat.le_succ 1), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩,
        fun _ _ _ h => absurd h (Nat.not_lt_zero _), ?_, ?_, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
      · simp only [KP, CP]; rfl
      · simp only [KP, CP]; rfl }

theorem absTyM_nat (K : RunCtx) (ρ : Assignment) {st : MState} {σ : Nat} (h : st.absTy[σ]? = some .tNat) :
    MState.absTyM K.dm K.M K.Γ ρ st σ = TyM.nat := by
  unfold MState.absTyM; rw [h]; rfl

/-- **`Pre` at world `Z`'s leaf**, `Z` in flight, under `ρ` with `σ0 = 0`. -/
theorem pre_lzT (Δ : Nat → TyS) (ρ : Assignment) (h0 : ρ 0 = .el0 Nat 0) : Pre (KP dm D φ Δ) ρ lzT := by
  have hz : Value.zero ∈ TVals := by simp [TVals]
  have hnr : ∀ σ, ¬ lzT.Refd σ := fun σ h => by
    have h2 := MState.refd_lt lzT 0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ σ h
    · omega
    · intro v hv σ hσ
      rcases mem_values_envT hz hv with rfl | rfl | rfl | rfl <;>
        first | exact (Bool.false_ne_true hσ).elim | (rw [show lzT.env = envT .zero from rfl, values_envT] at hv; simp at hv)
    · intro f i b T hb hT σ hσ
      rcases bind_envT hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfP, nBot, nB] at hT <;> subst hT <;>
        exact (Bool.false_ne_true hσ).elim
    · intro f i b P ws j hb hT; rcases bind_envT hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfP, nBot, nB] at hT
    · intro G hG σ hσ; simp [lzT] at hG; subst hG; exact (Bool.false_ne_true hσ).elim
    · intro m σ' h; simp [lzT] at h
    · intro σ' v h; simp [lzT] at h
    · intro σ' T h σ hσ
      rcases σ' with _ | σ'
      · simp [lzT] at h; subst h; exact (Bool.false_ne_true hσ).elim
      · simp [lzT] at h
  refine ⟨?_, ?_, ?_⟩ <;> rw [norm_lzT]
  · exact ctxS_P Δ rfl rfl
  · exact inv_envT hz rfl (by simp [lzT]) (.inr rfl) rfl
      (fun σ r h => by simp [lzT] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨by decide, fun τ hτ => by cases hτ⟩)
      rfl rfl rfl (fun σ l => by rcases σ with _ | σ <;> simp [lzT])
  · refine ⟨⟨fun σ h => absurd h (hnr σ), ?_, ?_, ?_⟩, fun σ h => absurd h (hnr σ), ?_, fun σ h => absurd h (hnr σ)⟩
    · intro n σ h; simp [lzT] at h
    · intro σ v h; simp [lzT] at h
    · intro σ r h; simp [lzT] at h; obtain ⟨rfl, rfl⟩ := h; exact h0
    · intro G h; simp only [MState.goalM, lzT, Option.map_some, Option.some.injEq] at h; subst h; rfl

/-- **`Pre` at world `S`'s leaf**, `σ1` in flight, under `ρ` extended by `σ1 ↦ a` and `Δ` by `σ1 : Nat`, where
`σ0 = a + 1`. -/
theorem pre_lsT (ρ : Assignment) {a : Nat} (h0 : ρ 0 = .el0 Nat (a + 1)) :
    Pre (KP dm D φ ΔPS) (ρS ρ a) lsT := by
  have hs : Value.abs 1 ∈ TVals := by simp [TVals]
  have hlt : ∀ σ, lsT.Refd σ → σ < 2 := refd_envT (st := lsT) hs rfl (by simp [lsT]) (.inl (by decide)) rfl rfl rfl
  have hty : ∀ σ, σ < 2 → lsT.absTy[σ]? = some .tNat := fun σ h => by
    rcases σ with _ | _ | σ
    · rfl
    · rfl
    · omega
  have hmem : ∀ σ, σ < 2 → ∃ m, ρS ρ a σ = .el0 Nat m := fun σ h => by
    rcases σ with _ | _ | σ
    · exact ⟨a + 1, by simp [ρS, h0]⟩
    · exact ⟨a, by simp [ρS]⟩
    · omega
  refine ⟨?_, ?_, ?_⟩ <;> rw [norm_lsT]
  · exact ctxS_P ΔPS rfl rfl
  · exact inv_envT hs rfl (by simp [lsT]) (.inl (by decide)) rfl
      (fun σ r h => by
        simp [lsT] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨by decide, fun τ hτ => by have := abs_hasAbs_eq hτ; subst this; decide⟩)
      rfl rfl rfl (fun σ l => by rcases σ with _ | _ | σ <;> simp [lsT])
  · refine ⟨⟨fun σ h _ => ?_, ?_, ?_, ?_⟩, fun σ h _ => ?_, ?_, fun σ h _ => ?_⟩
    · rw [absTyM_nat _ _ (hty σ (hlt σ h))]; obtain ⟨m, hm⟩ := hmem σ (hlt σ h); exact ⟨m, hm.symm⟩
    · intro n σ h; simp [lsT] at h
    · intro σ v h; simp [lsT] at h
    · intro σ r h; simp [lsT] at h; obtain ⟨rfl, rfl⟩ := h
      show ρS ρ a 0 = (ρS ρ a 1).succ
      simp [ρS, h0, Sem.succ_el0]
    · rw [absTyM_nat _ _ (hty σ (hlt σ h))]; rfl
    · intro G h; simp only [MState.goalM, lsT, Option.map_some, Option.some.injEq] at h; subst h; rfl
    · have := hlt σ h
      show ΔPS σ = deltaOf _ _ lsT σ
      unfold deltaOf; rw [hty σ this]; simp [ΔPS, this]; rfl

end

/-! ## The split's step -/

/-- The stage-0 closure has no moved part. -/
theorem movedIn_selfSem (R : DataRead) (φ : Future) (q : Place) : Sem.movedIn (selfSem R φ) q = [] := by
  show Sem.movedIn (closureL (lvl0 R) φ (telL (lvl0 R) psI [] PUnit (weakCod 1 (fixRank none) 0 outI)).2 _) q = []
  unfold closureL
  split
  · rfl
  · simp [Sem.movedIn]

theorem norm_stP : stP.norm = stP := by simp [stP, MState.norm, Env.erase, Frame.erase]

section
variable {dm : DataModel} {D : Decisions} {φ : Future}

/-- **The split's step, in the tail form** (`TailOut` at every hint): from a checker state with `stP`'s kernel in the
plain mode with no handed-down reading, every successful `checkTail` of `P`'s body with a continuation that keeps the
counters in world `Z`, every assignment meeting `Pre` and every reference state related to it: the reference's run of
the body in tail position succeeds, and at the leaf of the world the assignment selects `k` ran on the checker's value
and `Out` holds. Assumes the checker fact `SplitPInv` and the decisions `ParDecP` (`parDecP` gives them at the table
aligned with the checker at `stP`). -/
theorem split_outP (hSp : SplitPInv) {Δ : Nat → TyS} (hd : ParDecP D) {fuel : Nat} {k : Value → Value → M Unit}
    (hk : KeepsAtZ k) {st st' : MState} {bh : Nat} (hkern : Kern stP st) (hm : Mode st) (htd : st.tailDecl = none)
    (hrun : Runs (Ochr.checkTail fuel bodyP k) st bh () st') {ρ : Assignment} {π : Nat → Nat} {s : SState}
    (hpre : Pre (KP dm D φ Δ) ρ st) (hr : Rel (KP dm D φ Δ) ρ φ π st s) (hint : TyS) :
    TailOut (KP dm D φ Δ) ρ φ π st s (runT (KP dm D φ Δ) ρ φ true hint bodyP) k := by
  obtain ⟨⟨stlZ, bkZ, stkZ, hkZ, hrZ⟩, ⟨stlS, bkS, stkS, hkS, hrS⟩⟩ := hSp fuel k st st' bh hkern hm htd hk hrun
  have hr0 : Rel (KP dm D φ Δ) ρ φ π stP s := hr.of_kern hkern.symm
  have hp0 : Pre (KP dm D φ Δ) ρ stP := hpre.of_kern hkern.symm
  have hrefd : stP.Refd 0 := .val (.abs 0) (by rw [stP_env, values_envN]; simp) rfl
  have hrefd' : stP.norm.Refd 0 := by rw [norm_stP]; exact hrefd
  obtain ⟨m, hm0⟩ : ∃ m, ρ 0 = .el0 Nat m := by
    have h := hp0.asg.asg.mem 0 hrefd' (by rw [norm_stP]; decide)
    rw [norm_stP, absTyM_nat _ _ (st := stP) rfl] at h
    obtain ⟨m, hm⟩ := h; exact ⟨m, hm.symm⟩
  have hΔ0 : Δ 0 = .plain TyM.nat := by
    have h := hp0.asg.delta 0 hrefd' (by rw [norm_stP]; decide)
    rw [norm_stP] at h; exact h
  have hP := refP_of_rel hr0
  obtain ⟨hZ, hS⟩ := runP (K := KP dm D φ Δ) hd hP (movedIn_selfSem dm.read φ) hint
  have hsz : st.absTy.size = 1 := by rw [← hkern.absTy]; rfl
  cases m with
  | zero =>
    refine ⟨stlZ, .zero, .tNat, ⟨bkZ, stkZ, hrZ⟩, ρ, Δ, π, (.el0 Nat 0, .plain TyM.nat), dropN (KP dm D φ Δ) s,
      ⟨?_, ?_, fun σ hσ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩, hZ hm0, rfl, fun T e => by cases e; rfl, rfl, ?_, ?_⟩
    · rw [hsz, ← hkZ.absTy]; decide
    · rw [← hkZ.nextLoan, ← hkern.nextLoan]; exact Nat.le_refl _
    · exact (pre_lzT Δ ρ hm0).of_kern (kern_lzT.trans (hkZ.withTempT _ _))
    · exact rel_withTempT_num ((rel_leafZ hr0 hm0).of_kern hkZ) .zero _
  | succ a =>
    refine ⟨stlS, .abs 1, .tNat, ⟨bkS, stkS, hrS⟩, ρS ρ a, ΔPS, π, (.el0 Nat a, .plain TyM.nat),
      dropN (KP dm D φ ΔPS) (setN0 (KP dm D φ Δ) s),
      ⟨?_, ?_, fun σ hσ => ?_, fun _ _ => rfl⟩, hS a hm0, ?_, fun T e => by cases e; rfl, rfl, ?_, ?_⟩
    · rw [hsz, ← hkS.absTy]; decide
    · rw [← hkS.nextLoan, ← hkern.nextLoan]; exact Nat.le_refl _
    · rw [hsz] at hσ
      obtain rfl : σ = 0 := by omega
      exact ⟨rfl, by show ΔPS 0 = Δ 0; rw [hΔ0]; rfl⟩
    · show ρS ρ a 1 = _; simp [ρS]
    · exact (pre_lsT ρ hm0).of_kern (kern_lsT.trans (hkS.withTempT _ _))
    · exact rel_withTempT_inertA ((rel_leafS hr0 hm0).of_kern hkS) (abs_inertA 1) _

/-- **`P`'s body, simulated in the tail form** (`TailSim`): assumes the checker fact `SplitPInv`. -/
theorem split_simP (hSp : SplitPInv) {Δ : Nat → TyS} (hd : ParDecP D) {fuel : Nat} {k : Value → Value → M Unit}
    (hk : KeepsAtZ k) {st : MState} (hkern : Kern stP st) (hm : Mode st) (htd : st.tailDecl = none) (ρ : Assignment) :
    TailSim (KP dm D φ Δ) ρ φ fuel st bodyP k :=
  fun _ _ _ _ hpre hr _ hrun => split_outP hSp hd hk hkern hm htd hrun hpre hr _

end

end Ochr.Meaning.Steps.Form.ColumnP
