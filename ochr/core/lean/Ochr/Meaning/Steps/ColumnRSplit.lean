import Ochr.Meaning.Steps.ColumnRRun
import Ochr.Meaning.Steps.ColumnPSplit

/-!
# The column `R`: the split's step in the tail form, at the stage's context (lead17, 2026-11-21; docs/31 D134)

`ColumnP`'s split (D131) for `R`'s body, whose arm in world `S` is the recursive call. The context is the stage's:
`KR dm D Δ G b` (`cur = some ("R", b)`, the global `R` meaning `G`), and `G` is the stage-`b` closure at the weakened
type (`GR`) of a function `fn` good below `b` (the outer induction hypothesis, which `Pre` carries as
`GlobalsOk.memBelow`). In world `S` the reference's call of its binding of itself at `m = a - 1` and the meaning of the
checker's sealed value `⌈R(σ1)⌉` are the same `callOf` of `G` at `m` (`ClosureStage.stage_apply`), defined because
`m < b` (the entry condition `a ≤ b`). Assumes the checker fact `SplitRInv`.
-/

namespace Ochr.Meaning.Steps.Form.ColumnR

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Ochr.Meaning.Steps.Form.ColumnI (piNat nB psI outI NoBorrow liveLabels_of_rel)
open Ochr.Meaning.Steps.Form.ColumnP (rel_transfer kern_of_env ρS ΔP ΔPS absTyM_nat RI pn0 RefJ RefP dropN setN0)

/-! ## The context at stage `b + 1` -/

/-- The globals while `R`'s body is checked: `R` means `G`. -/
noncomputable def CR (G : Sem × TyS) : CodeMeaning :=
  { global := fun n => if n = "R" then G else (.el0 Nat 0, .plain TyM.nat),
    sealed := fun _ _ _ _ => .err, clo := fun _ _ _ _ _ => .err,
    pi := fun _ _ _ _ _ => TyM.err, paramTy := fun _ _ _ _ => .plain TyM.err }

/-- **The run's context while `R`'s body is checked at stage `b + 1`**: `R` means `G`, the definition being checked
at bound `b`. -/
noncomputable def KR (dm : DataModel) (D : Decisions) (Δ : Nat → TyS) (G : Sem × TyS) (b : Nat) : RunCtx :=
  { dm := dm, Γ := [], C := CR G, D := D, Δ := Δ, cur := some ("R", b) }

/-- The rank `R` decreases on: its parameter's. -/
noncomputable def rkR : List Sem → Nat := fixRank (some 0)

theorem decRank_gR (K : RunCtx) : decRank K gR = rkR := by
  funext args; unfold decRank rkR fixRank; simp only [gR, fixR]
  cases args[0]? <;> rfl

/-- **The stage-`b` closure of `fn` at the weakened type**: what the reference's `fixStage (b + 1)` binds for
`self`, and what the context's `R` means at stage `b + 1`. -/
noncomputable def GR (R : DataRead) (φ : Future) (b : Nat) (fn : List Sem → Option BodyOut) : Sem × TyS :=
  (closureAt R 1 φ psI (weakCod 1 rkR b outI) (stageFn 1 psI rkR b fn), .plain (piTyAt R 1 psI (weakCod 1 rkR b outI)))

/-- The outer induction hypothesis: `fn` is defined and good at every number below `b`. -/
def GoodBelow (R : DataRead) (b : Nat) (fn : List Sem → Option BodyOut) : Prop :=
  ∀ m, m < b → ∃ o, fn [.el0 Nat m] = some o ∧ Steps.OutGood R psI outI [.el0 Nat m] o ∧ o.finals = []

theorem domMembers_one {R : DataRead} {args : List Sem} (h : DomMembers R psI args) : ∃ m, args = [.el0 Nat m] := by
  obtain ⟨hlen, hargs⟩ := h
  match args, hlen with
  | [x], _ =>
    obtain ⟨m, hx⟩ := hargs 0 x _ rfl rfl
    exact ⟨m, by rw [← hx]; rfl⟩

theorem domMembers_nat (R : DataRead) (m : Nat) : DomMembers R psI [.el0 Nat m] :=
  ⟨rfl, fun i a d ha hd => by
    rcases i with _ | i
    · simp [psI] at ha hd; subst ha; subst hd; exact ⟨m, rfl⟩
    · simp at ha⟩

theorem rkR_nat (m : Nat) : rkR [.el0 Nat m] = m := by
  show semHeight (.el0 Nat m) = m; simp [semHeight, Sem.asNat_el0]

/-- **The context's `R` is under `MemBelow` at `b`** where `fn` is good below `b` (`GlobalsOk.memBelow`'s
content: the outer induction hypothesis). -/
theorem memBelow_GR {dm : DataModel} {D : Decisions} {φ : Future} {Δ : Nat → TyS} {b : Nat}
    {fn : List Sem → Option BodyOut} (hgb : GoodBelow dm.read b fn) :
    MemBelow (KR dm D Δ (GR dm.read φ b fn) b) (GR dm.read φ b fn) gR b := by
  refine ⟨1, φ, psI, outI, fn, ⟨Nat.le_succ_of_le (Nat.le_succ 1), fun _ _ _ => Nat.le_refl 1⟩, fun _ args _ _ => ⟨trivial, fun i d hi => ?_⟩,
    ?_, ?_, fun args ha hlt => ?_⟩
  · rcases i with _ | i
    · simp [psI] at hi; subst hi; exact Nat.le_refl 1
    · simp [psI] at hi
  · rw [decRank_gR]; rfl
  · rw [decRank_gR]; rfl
  · obtain ⟨m, rfl⟩ := domMembers_one ha
    rw [decRank_gR, rkR_nat] at hlt
    obtain ⟨o, ho, hg, hf⟩ := hgb m hlt
    exact ⟨o, ho, hg, fun h => by simp [outI] at h, by rw [hf]; rfl⟩

/-- **The call of the stage closure below the bound**: at a number `m < b` where `fn` gives `o` (any unlabelled type),
`callOf` gives `o`'s result at `Nat` and keeps the state (`ClosureStage.stage_apply`). -/
theorem callGR {R : DataRead} {φ : Future} {b : Nat} {fn : List Sem → Option BodyOut} (hgb : GoodBelow R b fn)
    {m : Nat} (hm : m < b) {o : BodyOut} (ho : fn [.el0 Nat m] = some o) (T : TyS) (hT : T.label = none) (s : SState) :
    callOf R (GR R φ b fn) [(.el0 Nat m, T)] s = some ((o.result, .plain TyM.nat), s) := by
  obtain ⟨s', hs'⟩ := stage_apply R 1 φ psI outI rkR b fn ⟨Nat.le_refl 1, by omega⟩ rfl (fun _ _ _ => Nat.le_refl 1)
    (fun args ha hlt => by
      obtain ⟨m', rfl⟩ := domMembers_one ha
      rw [rkR_nat] at hlt
      obtain ⟨o', h1, h2, h3⟩ := hgb m' hlt
      exact ⟨o', h1, h2, by rw [h3]; rfl⟩)
    [(.el0 Nat m, T)] s o (domMembers_nat R m)
    (fun i d hi => by
      rcases i with _ | i
      · simp [psI] at hi; subst hi; exact Nat.le_refl 1
      · simp [psI] at hi)
    (by show rkR [.el0 Nat m] < b; rw [rkR_nat]; exact hm) trivial ho
  have hss := ColumnJ.callOf_unlabelled_state _ _ _ _ _ _ hs' (fun a ha => by simp at ha; subst ha; exact hT) rfl
  subst hss
  exact hs'

/-- The stage closure is a member of its weakened type, where `fn` is good below the bound. -/
theorem GR_mem {R : DataRead} {φ : Future} {b : Nat} {fn : List Sem → Option BodyOut} (hgb : GoodBelow R b fn) :
    (GR R φ b fn).1 ∈ₛ[R] (GR R φ b fn).2.m :=
  stage_mem R 1 φ psI outI rkR b fn ⟨Nat.le_refl 1, by omega⟩ rfl (fun _ _ _ => Nat.le_refl 1)
    (fun args ha hlt => by
      obtain ⟨m', rfl⟩ := domMembers_one ha
      rw [rkR_nat] at hlt
      obtain ⟨o', h1, h2, h3⟩ := hgb m' hlt
      exact ⟨o', h1, h2, by rw [h3]; rfl⟩)

theorem GR_whole (R : DataRead) (φ : Future) (b : Nat) (fn : List Sem → Option BodyOut) (hgb : GoodBelow R b fn) :
    (GR R φ b fn).1.whole := by
  have hm := GR_mem (φ := φ) hgb
  revert hm
  show closureL (lvl0 R) φ (telL (lvl0 R) psI [] PUnit (weakCod 1 rkR b outI)).2 _ ∈ₛ[R] _ →
    (closureL (lvl0 R) φ (telL (lvl0 R) psI [] PUnit (weakCod 1 rkR b outI)).2 _).whole
  unfold closureL
  split
  · intro _; simp [Sem.whole, lvl0]
  · intro h; exact absurd h (ClosureCE.err_not_mem_pi R _ _)

theorem movedIn_GR (R : DataRead) (φ : Future) (b : Nat) (fn : List Sem → Option BodyOut) (q : Place) :
    Sem.movedIn (GR R φ b fn).1 q = [] := by
  show Sem.movedIn (closureL (lvl0 R) φ (telL (lvl0 R) psI [] PUnit (weakCod 1 rkR b outI)).2 _) q = []
  unfold closureL
  split
  · rfl
  · simp [Sem.movedIn]

theorem inertO_vR : vR.InertO :=
  ⟨fun l => by simp [vR, sealR, Value.anyAtom, Term.anyAtom, Term.anyAtomList, BEq.beq, Value.beq], fun _ => rfl,
    fun _ _ _ => rfl, rfl⟩

/-! ## `stR` -/

theorem shape_stR (p : Pos) : Env.shape stR.env p = none := by
  unfold Env.shape
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · rfl
    · rcases i with _ | _ | i <;> rfl
    · rfl
  · rcases f with _ | _ | f <;> rfl

theorem noBorrow_stR : NoBorrow stR.env := shape_stR

section
variable {dm : DataModel} {D : Decisions} {φ : Future} {Δ : Nat → TyS} {G : Sem × TyS} {b : Nat}

theorem mean_stR_n (ρ : Assignment) (ψ : Future) :
    Env.mean (KR dm D Δ G b).dm (KR dm D Δ G b).M (KR dm D Δ G b).Γ ρ ψ stR.env (.bind 1 1) = ρ 0 := rfl

theorem mean_stR_self (ρ : Assignment) (ψ : Future) :
    Env.mean (KR dm D Δ G b).dm (KR dm D Δ G b).M (KR dm D Δ G b).Γ ρ ψ stR.env (.bind 1 0) = G.1 := by
  show ((KR dm D Δ G b).C.global "R").1 = _
  simp [KR, CR]

/-- **A reference state related to `P`'s start state reads as `RefP`.** -/
theorem refR_of_rel {ρ : Assignment} {π : Nat → Nat} {s : SState} (hr : Rel (KR dm D Δ G b) ρ φ π stR s) :
    RefP ρ φ G.1 s := by
  have hlive : s.liveLabels = [] := liveLabels_of_rel hr noBorrow_stR
  have hF : RelF φ s φ ∧ TypedLive (KR dm D Δ G b) s φ :=
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
    have : (SM' (KR dm D Δ G b) ρ stR).env.map (fun fr => (fr.binds.map bindSkel).length) = [0, 2] := by
      simp [SM', MState.sstate, stR]
    simpa [List.map_map, Function.comp_def, ← this] using hsk.symm
  obtain ⟨fr0, fr1, hen, h1⟩ : ∃ fr0 fr1, s.env = [fr0, fr1] ∧ fr1.binds.length = 2 := by
    rcases he : s.env with _ | ⟨fr0, _ | ⟨fr1, _ | ⟨fr2, rest⟩⟩⟩ <;> rw [he] at hlen <;> simp at hlen
    exact ⟨fr0, fr1, rfl, hlen.2⟩
  refine ⟨⟨hlive, hshape, ?_, ?_⟩, ⟨fr1, ?_, h1⟩, ?_, ?_, ?_, ?_⟩
  · rw [scopeOf_rel hr]; rfl
  · exact rel_resolve_ck _ ρ φ stR s π (.var 0) (.bind 1 1) hr rfl
  · rw [hen]; rfl
  · unfold SState.topIdx; rw [hen]; rfl
  · rw [← hr.sim.1 φ hF (.bind 1 1) (by simp [IsTemp])]; exact mean_stR_n (dm := dm) (D := D) (Δ := Δ) (G := G) (b := b) ρ (fun l => φ (π l))
  · rw [← hr.sim.1 φ hF (.bind 1 0) (by simp [IsTemp])]; exact mean_stR_self (dm := dm) (D := D) (Δ := Δ) (G := G) (b := b) ρ (fun l => φ (π l))
  · rw [(rel_bind_ty hr (b := nB) (f := 1) (j := 1) rfl (hp := rfl)).2]; rfl

end

/-- The function's own binding is read at `G`'s type in a reference state related to `R`'s start. -/
theorem tySelf_of_rel {dm : DataModel} {D : Decisions} {φ : Future} {Δ : Nat → TyS} {G : Sem × TyS} {b : Nat}
    {ρ : Assignment} {π : Nat → Nat} {s : SState} (hr : Rel (KR dm D Δ G b) ρ φ π stR s) :
    (s.tyAt (.bind 1 0)).m = G.2.m := by
  rw [(rel_bind_refTy hr (b := selfR) (f := 1) (j := 0) rfl).2, Binding.refTy_marked _ _ _ _ _ _ _ _ 0 rfl rfl]
  simp [KR, CR, selfR, RunCtx.M, codeMeaning]

/-! ## The frames of the split's states -/

/-- The frames with `n ↦ v`. -/
def envN (v : Value) : Env := #[{}, { binds := #[selfR, { nB with val := v }] }]

/-- The values `n` holds along the split: `σ0`, `Z`, `S(σ1)`, `S(⊥)`, `⊥`. -/
def NVals : List Value := [.abs 0, .zero, .succ (.abs 1), .succ .bot, .bot]

theorem stR_env : stR.env = envN (.abs 0) := rfl
theorem envBot_eq : envBot = envN .bot := rfl

theorem setAtE_envN (v w : Value) : Env.setAtE (envN v) (.bind 1 1) w = envN w := by
  simp [Env.setAtE, envN, nB]

theorem allPos_envN (v : Value) : allPos (envN v) = [.bind 1 0, .bind 1 1] := by
  rw [allPos_eq]; simp [envN, frameAllPos, List.range_succ]

theorem values_envN (v : Value) : Env.values (envN v) = [.gfn "R", v] := by
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
  rcases hv with rfl | rfl | rfl | rfl | rfl <;> simp [valAt, envN, selfR, nB, Value.sitesOf]

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
variable {dm : DataModel} {D : Decisions} {φ : Future} {G : Sem × TyS} {b : Nat}

/-- The skeleton of a state with `envN v`'s frames: the function's own binding at `G`'s type, `n` at `Nat`. -/
theorem skel_envN (Δ : Nat → TyS) (ρ : Assignment) (st : MState) (v : Value) (he : st.env = envN v) :
    (SM' (KR dm D Δ G b) ρ st).env.map (fun fr => fr.binds.map bindSkel) =
      [[], [(G.2.m, .pi .other), (TyM.nat, .other)]] := by
  unfold SM' MState.sstate; rw [he]
  have h0 : Binding.refTy (KR dm D Δ G b).dm (KR dm D Δ G b).M (KR dm D Δ G b).Γ ρ (envN v) 1 0 selfR = G.2 := by
    rw [Binding.refTy_marked _ _ _ _ _ _ _ _ 0 rfl rfl]
    simp [KR, CR, selfR, RunCtx.M, codeMeaning]
  have h1 : Binding.refTy (KR dm D Δ G b).dm (KR dm D Δ G b).M (KR dm D Δ G b).Γ ρ (envN v) 1 1 { nB with val := v } = .plain TyM.nat := by
    rw [Binding.refTy_unmarked _ _ _ _ _ _ _ _ rfl]; rfl
  simp only [envN, List.zipIdx, List.map, Nat.zero_add]
  simp only [bindSkel]; erw [h0, h1]; rfl

/-- A position of `envN v` other than `n` means what it means in any other such state. -/
theorem mean_envN_other (Δ Δ' : Nat → TyS) (ρ ρ' : Assignment) (ψ ψ' : Future) (v v' : Value) {p : Pos}
    (hp : p ≠ .bind 1 1) :
    Env.mean (KR dm D Δ' G b).dm (KR dm D Δ' G b).M (KR dm D Δ' G b).Γ ρ' ψ' (envN v') p =
      Env.mean (KR dm D Δ G b).dm (KR dm D Δ G b).M (KR dm D Δ G b).Γ ρ ψ (envN v) p := by
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
    Env.mean (KR dm D Δ G b).dm (KR dm D Δ G b).M (KR dm D Δ G b).Γ ρ ψ (envN v) (.bind 1 1) =
      Value.mean (KR dm D Δ G b).dm (KR dm D Δ G b).M (KR dm D Δ G b).Γ ρ ψ (.plain TyM.nat) v := rfl

end

/-! ## The split's states, and the relation through them -/

/-- World `Z` after its refinement: `n ↦ Z`, the record `0 := Z`. -/
def stZ0 : MState :=
  { env := envN .zero, globals := [gR], nextAbs := 1, absTy := #[.tNat], absDecl := #[.other], goal := some .tNat,
    refs := [(0, .zero)] }

/-- World `S` after its refinement: the fresh `σ1 : Nat`, `n ↦ S(σ1)`, the record `0 := S(σ1)`. -/
def stS0 : MState :=
  { env := envN (.succ (.abs 1)), globals := [gR], nextAbs := 2, absTy := #[.tNat, .tNat],
    absDecl := #[.other, .other], goal := some .tNat, refs := [(0, .succ (.abs 1))] }

section
variable {dm : DataModel} {D : Decisions} {φ : Future} {G : Sem × TyS} {b : Nat}

/-- Two states with `envN`'s frames whose `n` means the same are read alike (`MState.mean`). -/
theorem mean_envN_eq (Δ Δ' : Nat → TyS) (ρ ρ' : Assignment) {st st' : MState} {v v' : Value}
    (he : st.env = envN v) (he' : st'.env = envN v') (hv : v ∈ NVals) (hv' : v' ∈ NVals)
    (hn : ∀ ψ, Value.mean (KR dm D Δ' G b).dm (KR dm D Δ' G b).M (KR dm D Δ' G b).Γ ρ' ψ (.plain TyM.nat) v' =
      Value.mean (KR dm D Δ G b).dm (KR dm D Δ G b).M (KR dm D Δ G b).Γ ρ ψ (.plain TyM.nat) v) :
    MState.mean (KR dm D Δ' G b).dm (KR dm D Δ' G b).M (KR dm D Δ' G b).Γ ρ' st' =
      MState.mean (KR dm D Δ G b).dm (KR dm D Δ G b).M (KR dm D Δ G b).Γ ρ st := by
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
    (hr : Rel (KR dm D Δ G b) ρ φ π stR s) (he' : st'.env = envN v') (hv' : v' ∈ NVals) (hl : st'.nextLoan = 0)
    (hn : ∀ ψ, Value.mean (KR dm D Δ' G b).dm (KR dm D Δ' G b).M (KR dm D Δ' G b).Γ ρ' ψ (.plain TyM.nat) v' = ρ 0) :
    Rel (KR dm D Δ' G b) ρ' φ π st' s :=
  have hv : Value.abs 0 ∈ NVals := by simp [NVals]
  rel_transfer (Δ' := Δ') hr (by
      show (SM' (KR dm D Δ' G b) ρ' st').env.map (fun fr => fr.binds.map bindSkel) = _
      rw [skel_envN _ _ _ _ he', skel_envN _ _ _ _ stR_env])
    (mean_envN_eq Δ Δ' ρ ρ' stR_env he' hv hv' hn) hl
    (fun l => ⟨fun h => absurd h (occurs_envN hv' st' he' l), fun h => absurd h (occurs_envN hv stR stR_env l)⟩)
    (fun l => by rw [he', stR_env, liveLoan_envN hv', liveLoan_envN hv])
    (fun l => by rw [he', stR_env, sitesOf_envN hv', sitesOf_envN hv])

/-- **World `Z`'s leaf is related to the reference's state after the match** (the refinement, then the join's
drop of `n`). -/
theorem rel_leafZR {Δ : Nat → TyS} {ρ : Assignment} {π : Nat → Nat} {s : SState}
    (hr : Rel (KR dm D Δ G b) ρ φ π stR s) (h0 : ρ 0 = .el0 Nat 0) :
    Rel (KR dm D Δ G b) ρ φ π leafZR (dropN (KR dm D Δ G b) s) := by
  have hz : Value.zero ∈ NVals := by simp [NVals]
  have h₀ : Rel (KR dm D Δ G b) ρ φ π stZ0 s := rel_refine (Δ' := Δ) hr rfl hz rfl (fun _ => h0.symm)
  have hsp : Pos.bind 1 1 ∈ s.positions := (rel_bind_ty hr (b := nB) (f := 1) (j := 1) rfl (hp := rfl)).1
  have h₁ := botWrite_rel (KR dm D Δ G b) ρ φ stZ0 s π 1 1 [] .bot h₀ (wf1_envN hz)
    (by show _ ∈ allPos (envN _); rw [allPos_envN]; simp) hsp (by show Value.updAt _ [] _ = _; rw [Value.updAt])
    (fun _ => shape_envN hz _) (fun l hl => by simp [stZ0, liveLoan_envN hz] at hl)
    ⟨rfl, rfl⟩ (fun _ => by rw [NatAlong]; trivial)
  refine h₁.of_kern (kern_of_env ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
  show Env.setAtE (envN .zero) (.bind 1 1) .bot = envBot
  rw [setAtE_envN]; rfl

/-- **World `S`'s leaf is related to the reference's state after the match**, under `ρ` extended by `σ1 ↦ a` and
`Δ` by `σ1 : Nat` (the refinement, the arm's move of `n.0`, the join's drop of `n`). -/
theorem rel_leafSR {Δ : Nat → TyS} {ρ : Assignment} {π : Nat → Nat} {s : SState} {a : Nat}
    (hr : Rel (KR dm D Δ G b) ρ φ π stR s) (h0 : ρ 0 = .el0 Nat (a + 1)) :
    Rel (KR dm D ΔPS G b) (ρS ρ a) φ π leafSR (dropN (KR dm D ΔPS G b) (setN0 (KR dm D Δ G b) s)) := by
  have hS : Value.succ (.abs 1) ∈ NVals := by simp [NVals]
  have hSb : Value.succ .bot ∈ NVals := by simp [NVals]
  have h₀ : Rel (KR dm D ΔPS G b) (ρS ρ a) φ π stS0 s := rel_refine (Δ' := ΔPS) hr rfl hS rfl (fun ψ => by
    show (Value.mean _ _ _ (ρS ρ a) ψ (.plain TyM.nat) (.abs 1)).succ = _
    rw [h0]; show (Sem.el0 Nat a).succ = _; rw [Sem.succ_el0])
  have hsp : Pos.bind 1 1 ∈ s.positions := (rel_bind_ty hr (b := nB) (f := 1) (j := 1) rfl (hp := rfl)).1
  have h₁ := botWrite_rel (KR dm D ΔPS G b) (ρS ρ a) φ stS0 s π 1 1 [.proj 0] (.succ .bot) h₀ (wf1_envN hS)
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
  have h₂ := botWrite_rel (KR dm D ΔPS G b) (ρS ρ a) φ { stS0 with env := Env.setAtE stS0.env (.bind 1 1) (.succ .bot) }
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

theorem hasAbs_vR {σ : Nat} (h : vR.hasAbs σ = true) : σ = 1 := by
  simp [vR, sealR, Value.hasAbs, Value.anyAtom, Term.anyAtom, Term.anyAtomList] at h
  rcases h with h | h | h
  · simp [BEq.beq, Value.beq] at h
  · simp [BEq.beq, Value.beq] at h
  · simp [BEq.beq, Value.beq] at h; omega

/-- A leaf's frames with the value `t` in flight (`withTempT` but for the temporary's stored type). -/
def envT (t : Value) : Env := #[{}, { binds := #[selfR, nBot], temps := #[t] }]

/-- The values in flight at the leaves. -/
def TVals : List Value := [.zero, vR]

theorem allPos_envT (t : Value) : allPos (envT t) = [.bind 1 0, .bind 1 1, .temp 1 0] := by
  rw [allPos_eq]; simp [envT, frameAllPos, List.range_succ]

theorem values_envT (t : Value) : Env.values (envT t) = [.gfn "R", .bot, t] := by
  rw [Env.values, allPos_envT]; rfl

theorem bind_envT {t : Value} {f i : Nat} {b : Binding} (h : (envT t)[f]?.bind (fun fr => fr.binds[i]?) = some b) :
    (f = 1 ∧ i = 0 ∧ b = selfR) ∨ (f = 1 ∧ i = 1 ∧ b = nBot) := by
  rcases f with _ | _ | f
  · simp [envT] at h
  · rcases i with _ | _ | i
    · simp [envT] at h; exact .inl ⟨rfl, rfl, h.symm⟩
    · simp [envT] at h; exact .inr ⟨rfl, rfl, h.symm⟩
    · simp [envT] at h
  · simp [envT] at h

theorem mem_values_envT {t v : Value} (ht : t ∈ TVals) (hv : v ∈ Env.values (envT t)) :
    v = .gfn "R" ∨ v = .bot ∨ v = .zero ∨ v = vR := by
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
    v = .gfn "R" ∨ v = .bot := by
  rcases hp : p.steps with ⟨i, path⟩
  simp only [ckContent, hp] at h
  unfold ckVarPos at h
  by_cases hi : i < 2
  · have hi' : i < (envT t)[(envT t).size - 1]!.binds.size := hi
    rw [if_pos hi'] at h
    simp only [Option.bind_some] at h
    have hv : ∀ w : Value, (w = .gfn "R" ∨ w = .bot) → w.follow path = some v → v = .gfn "R" ∨ v = .bot := by
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
    · have := hasAbs_vR hσ; subst this
      rcases hsz with h | h
      · omega
      · subst h; rw [values_envT] at hv; simp [vR] at hv
  · intro f i b T hb hT σ hσ; rw [he] at hb
    rcases bind_envT hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfR, nBot, nB] at hT <;> subst hT <;>
      exact (Bool.false_ne_true hσ).elim
  · intro f i b P ws j hb hT; rw [he] at hb
    rcases bind_envT hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfR, nBot, nB] at hT
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
  have hvals : ∀ v ∈ Env.values st.env, v = .gfn "R" ∨ v = .bot ∨ v = .zero ∨ v = vR := fun v hv => by
    rw [he] at hv; exact mem_values_envT ht hv
  have hpos : ∀ p ∈ allPos st.env, p = .bind 1 0 ∨ p = .bind 1 1 ∨ p = .temp 1 0 := fun p hp => by
    rw [he, allPos_envT] at hp; simpa using hp
  have hshape : ∀ p, Env.shape st.env p = none := fun p => by rw [he]; exact shape_envT ht p
  have hlive : ∀ l, liveLoan st.env l = false := fun l => by rw [he]; exact liveLoan_envT ht l
  have hbind : ∀ {f i b}, st.env[f]?.bind (fun fr => fr.binds[i]?) = some b →
      (f = 1 ∧ i = 0 ∧ b = selfR) ∨ (f = 1 ∧ i = 1 ∧ b = nBot) := fun hb => by rw [he] at hb; exact bind_envT hb
  have hocc : ∀ l, ¬ st.Occurs l := by
    rintro l ⟨v, hv, h⟩
    rcases hvals v hv with rfl | rfl | rfl | rfl <;> exact Bool.false_ne_true h
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
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
  · intro f i b hb T hT; rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfR, nBot, nB] at hT <;> subst hT <;> rfl
  · intro T hT; rw [hA T hT]; rfl
  · intro G hG; rw [hg] at hG; cases hG; rfl
  -- (WF10)
  · intro v hv; rcases hvals v hv with rfl | rfl | rfl | rfl <;> rfl
  -- (WF11)
  · intro f i b hb; rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact ⟨fun T hT l => by simp [selfR] at hT; subst hT; rfl, fun P ws j h => by simp [selfR] at h⟩
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
  -- (K): `R`'s own binding at `Π(n : Nat). Nat`, the parameter `⊥`
  · refine (fun f i b hb => ?_)
    rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact ⟨fun l c e => (nomatch e), fun l c e => (nomatch e)⟩
    · exact ⟨fun l c e => (nomatch e), fun l c e => (nomatch e)⟩

/-- World `Z`'s leaf with `Z` in flight (the kernel; `leafZR.withTempT Z (some Nat)` but for the temporary's
stored type). -/
def lzT : MState :=
  { env := envT .zero, globals := [gR], nextAbs := 1, absTy := #[.tNat], absDecl := #[.other], goal := some .tNat,
    refs := [(0, .zero)] }

/-- World `S`'s leaf with `⌈R(σ1)⌉` in flight. -/
def lsT : MState :=
  { env := envT vR, globals := [gR], nextAbs := 2, absTy := #[.tNat, .tNat], absDecl := #[.other, .other],
    goal := some .tNat, refs := [(0, .succ (.abs 1))] }

theorem norm_lzT : lzT.norm = lzT := by simp [lzT, envT, MState.norm, Env.erase, Frame.erase]
theorem norm_lsT : lsT.norm = lsT := by simp [lsT, envT, MState.norm, Env.erase, Frame.erase]

theorem kern_lzT : Kern lzT (leafZR.withTempT .zero (some .tNat)) :=
  ⟨by simp [lzT, leafZR, envT, envBot, nBot, MState.withTempT, Env.erase, Frame.erase], rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem kern_lsT : Kern lsT (leafSR.withTempT vR (some .tNat)) :=
  ⟨by simp [lsT, leafSR, envT, envBot, nBot, MState.withTempT, Env.erase, Frame.erase], rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

section
variable {dm : DataModel} {D : Decisions} {φ : Future} {G : Sem × TyS} {b : Nat}

theorem find_gR {n : String} {g : GDef} (h : [gR].find? (·.name == n) = some g) : n = "R" ∧ g = gR := by
  simp only [List.find?_cons, List.find?_nil] at h
  split at h
  · rename_i hn; cases h; exact ⟨(beq_iff_eq.mp hn).symm, rfl⟩
  · cases h

/-- **The context's part at every state of `P`'s body** (any `Δ`): no declarations, `P`'s global its stage-0
closure, the function being checked. -/
theorem ctxS_R (Δ : Nat → TyS) (hGl : G.2.label = none) (hMB : ∀ Δ, MemBelow (KR dm D Δ G b) G gR b) {st : MState}
    (hg : st.globals = [gR]) (hi : st.inds = []) : CtxS (KR dm D Δ G b) st where
  inds := hi ▸ List.nil_prefix
  covers := fun _ h => absurd h List.not_mem_nil
  faithful := fun _ h => by rw [hi] at h; exact absurd h List.not_mem_nil
  noLabel := fun n => by simp only [KR, CR]; split; exact hGl; rfl
  globals := {
    ty := fun n g hf hc => by rw [hg] at hf; exact absurd (by rw [(find_gR hf).1]; rfl) hc
    const := fun n g hf hn => by rw [hg] at hf; rw [(find_gR hf).2] at hn; cases hn
    fn := fun n g t hf _ hc => by rw [hg] at hf; exact absurd (by rw [(find_gR hf).1]; rfl) hc
    mem := fun n g hf hc => by rw [hg] at hf; exact absurd (by rw [(find_gR hf).1]; rfl) hc
    fixEq := fun n _ _ _ _ _ _ _ hf hc _ => by rw [hg] at hf; exact absurd (by rw [(find_gR hf).1]; rfl) hc
    accepted := fun n _ _ _ _ _ _ _ hf hc _ => by rw [hg] at hf; exact absurd (by rw [(find_gR hf).1]; rfl) hc
    retKind := fun n _ _ _ _ _ _ _ hf hc _ => by rw [hg] at hf; exact absurd (by rw [(find_gR hf).1]; rfl) hc
    codeValFree := fun n g t hf ht => by
      rw [hg] at hf; obtain ⟨-, rfl⟩ := find_gR hf
      simp only [gR, Option.some.injEq] at ht; subst ht; rfl
    memBelow := fun n g b' hf hcur => by
      rw [hg] at hf
      obtain ⟨rfl, rfl⟩ := find_gR hf
      simp only [KR, Option.some.injEq, Prod.mk.injEq, true_and] at hcur
      subst hcur
      show MemBelow (KR dm D Δ G b) ((CR G).global "R") gR b
      simp only [CR, if_true]; exact hMB Δ }

/-- **`Pre` at world `Z`'s leaf**, `Z` in flight, under `ρ` with `σ0 = 0`. -/
theorem pre_lzTR (hGl : G.2.label = none) (hMB : ∀ Δ, MemBelow (KR dm D Δ G b) G gR b) (Δ : Nat → TyS) (ρ : Assignment)
    (h0 : ρ 0 = .el0 Nat 0) : Pre (KR dm D Δ G b) ρ lzT := by
  have hz : Value.zero ∈ TVals := by simp [TVals]
  have hnr : ∀ σ, ¬ lzT.Refd σ := fun σ h => by
    have h2 := MState.refd_lt lzT 0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ σ h
    · omega
    · intro v hv σ hσ
      rcases mem_values_envT hz hv with rfl | rfl | rfl | rfl <;>
        first | exact (Bool.false_ne_true hσ).elim | (rw [show lzT.env = envT .zero from rfl, values_envT] at hv; simp [vR] at hv)
    · intro f i b T hb hT σ hσ
      rcases bind_envT hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfR, nBot, nB] at hT <;> subst hT <;>
        exact (Bool.false_ne_true hσ).elim
    · intro f i b P ws j hb hT; rcases bind_envT hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfR, nBot, nB] at hT
    · intro G hG σ hσ; simp [lzT] at hG; subst hG; exact (Bool.false_ne_true hσ).elim
    · intro m σ' h; simp [lzT] at h
    · intro σ' v h; simp [lzT] at h
    · intro σ' T h σ hσ
      rcases σ' with _ | σ'
      · simp [lzT] at h; subst h; exact (Bool.false_ne_true hσ).elim
      · simp [lzT] at h
  refine ⟨?_, ?_, ?_⟩ <;> rw [norm_lzT]
  · exact ctxS_R Δ hGl hMB rfl rfl
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
theorem pre_lsTR (hGl : G.2.label = none) (hMB : ∀ Δ, MemBelow (KR dm D Δ G b) G gR b) (ρ : Assignment) {a : Nat}
    (h0 : ρ 0 = .el0 Nat (a + 1)) :
    Pre (KR dm D ΔPS G b) (ρS ρ a) lsT := by
  have hs : vR ∈ TVals := by simp [TVals]
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
  · exact ctxS_R ΔPS hGl hMB rfl rfl
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

theorem norm_stR : stR.norm = stR := by simp [stR, MState.norm, Env.erase, Frame.erase]

section
variable {dm : DataModel} {D : Decisions} {φ : Future}

/-- **The split's step, in the tail form, at stage `b + 1`** (`TailOut` at every hint): from a checker state with `stR`'s
kernel in the plain mode with no handed-down reading, every successful `checkTail` of `R`'s body with a continuation
that keeps the counters in world `Z`, in the context whose `R` is the stage-`b` closure of a function `fn` good below
`b` (`GoodBelow`, the outer induction hypothesis), every assignment meeting `Pre` whose entry `ρ σ0` is at most `b` (the
entry condition: the knot's step at stage `b + 1`), and every reference state related to it: the reference's run of the
body in tail position succeeds, and at the leaf of the world the assignment selects `k` ran on the checker's value and
`Out` holds. In world `S` the checker's value is the sealed call `⌈R(σ1)⌉` and the reference's is the stage closure
called at `a = ρ σ0 - 1 < b`: the same `callOf` (`callGR`, `mean_vR`). Assumes the checker fact `SplitRInv` and the
decisions `ParDecR` (`parDecR` gives them at the table aligned with the checker at `stR`); no model fact. -/
theorem split_outR (hSp : SplitRInv) {Δ : Nat → TyS} {b : Nat} {fn : List Sem → Option BodyOut}
    (hgb : GoodBelow dm.read b fn) (hd : ParDecR D) {fuel : Nat} {k : Value → Value → M Unit}
    (hk : KeepsAtZR k) {st st' : MState} {bh : Nat} (hkern : Kern stR st) (hm : Mode st) (htd : st.tailDecl = none)
    (hrun : Runs (Ochr.checkTail fuel bodyR k) st bh () st') {ρ : Assignment} {π : Nat → Nat} {s : SState}
    (hab : ∀ m, ρ 0 = .el0 Nat m → m ≤ b)
    (hpre : Pre (KR dm D Δ (GR dm.read φ b fn) b) ρ st) (hr : Rel (KR dm D Δ (GR dm.read φ b fn) b) ρ φ π st s)
    (hint : TyS) :
    TailOut (KR dm D Δ (GR dm.read φ b fn) b) ρ φ π st s (runT (KR dm D Δ (GR dm.read φ b fn) b) ρ φ true hint bodyR) k := by
  obtain ⟨⟨stlZ, bkZ, stkZ, hkZ, hrZ⟩, ⟨stlS, bkS, stkS, hkS, hrS⟩⟩ := hSp fuel k st st' bh hkern hm htd hk hrun
  have hr0 : Rel (KR dm D Δ (GR dm.read φ b fn) b) ρ φ π stR s := hr.of_kern hkern.symm
  have hp0 : Pre (KR dm D Δ (GR dm.read φ b fn) b) ρ stR := hpre.of_kern hkern.symm
  have hrefd : stR.Refd 0 := .val (.abs 0) (by rw [stR_env, values_envN]; simp) rfl
  have hrefd' : stR.norm.Refd 0 := by rw [norm_stR]; exact hrefd
  obtain ⟨m, hm0⟩ : ∃ m, ρ 0 = .el0 Nat m := by
    have h := hp0.asg.asg.mem 0 hrefd' (by rw [norm_stR]; decide)
    rw [norm_stR, absTyM_nat _ _ (st := stR) rfl] at h
    obtain ⟨m, hm⟩ := h; exact ⟨m, hm.symm⟩
  have hΔ0 : Δ 0 = .plain TyM.nat := by
    have h := hp0.asg.delta 0 hrefd' (by rw [norm_stR]; decide)
    rw [norm_stR] at h; exact h
  have hP := refR_of_rel hr0
  have hts := tySelf_of_rel hr0
  have hMB : ∀ Δ', MemBelow (KR dm D Δ' (GR dm.read φ b fn) b) (GR dm.read φ b fn) gR b := fun _ => memBelow_GR hgb
  obtain ⟨hZ, hS⟩ := runR (K := KR dm D Δ (GR dm.read φ b fn) b) hd hP (movedIn_GR dm.read φ b fn) hts
    (GR_whole dm.read φ b fn hgb) (.inl (GR_mem hgb)) hint
  have hsz : st.absTy.size = 1 := by rw [← hkern.absTy]; rfl
  cases m with
  | zero =>
    refine ⟨stlZ, .zero, .tNat, ⟨bkZ, stkZ, hrZ⟩, ρ, Δ, π, (.el0 Nat 0, .plain TyM.nat), dropN (KR dm D Δ (GR dm.read φ b fn) b) s,
      ⟨?_, ?_, fun σ hσ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩, hZ hm0, rfl, fun T e => by cases e; rfl, rfl, ?_, ?_⟩
    · rw [hsz, ← hkZ.absTy]; decide
    · rw [← hkZ.nextLoan, ← hkern.nextLoan]; exact Nat.le_refl _
    · exact (pre_lzTR rfl hMB Δ ρ hm0).of_kern (kern_lzT.trans (hkZ.withTempT _ _))
    · exact rel_withTempT_num ((rel_leafZR hr0 hm0).of_kern hkZ) .zero _
  | succ a =>
    have ha : a < b := by have := hab (a + 1) hm0; omega
    obtain ⟨o, ho, -, -⟩ := hgb a ha
    have hc := callGR (φ := φ) hgb ha ho (.plain TyM.nat) rfl (setN0 (KR dm D Δ (GR dm.read φ b fn) b) s)
    have hx := hS a _ hm0 hc
    refine ⟨stlS, vR, .tNat, ⟨bkS, stkS, hrS⟩, ρS ρ a, ΔPS, π, (o.result, .plain TyM.nat),
      dropN (KR dm D ΔPS (GR dm.read φ b fn) b) (setN0 (KR dm D Δ (GR dm.read φ b fn) b) s),
      ⟨?_, ?_, fun σ hσ => ?_, fun _ _ => rfl⟩, hx, ?_, fun T e => by cases e; exact strAgree_tNat, rfl, ?_, ?_⟩
    · rw [hsz, ← hkS.absTy]; decide
    · rw [← hkS.nextLoan, ← hkern.nextLoan]; exact Nat.le_refl _
    · rw [hsz] at hσ
      obtain rfl : σ = 0 := by omega
      exact ⟨rfl, by show ΔPS 0 = Δ 0; rw [hΔ0]; rfl⟩
    · refine mean_vR (K := { KR dm D Δ (GR dm.read φ b fn) b with Δ := ΔPS }) hd.2.2.2.2.2.2 _ (s' := emptyState 0) ?_
      have e1 : ({ KR dm D Δ (GR dm.read φ b fn) b with Δ := ΔPS } : RunCtx).C.global "R" = GR dm.read φ b fn := by
        simp [KR, CR]
      rw [e1]
      exact callGR (φ := φ) hgb ha ho _ rfl (emptyState 0)
    · exact (pre_lsTR rfl hMB ρ hm0).of_kern (kern_lsT.trans (hkS.withTempT _ _))
    · exact rel_withTempT_inertO ((rel_leafSR hr0 hm0).of_kern hkS) inertO_vR _

/-- **`R`'s body at stage `b + 1`, simulated in the tail form** (`TailSim` from every assignment whose entry is at most
`b`): assumes the checker fact `SplitRInv`. -/
theorem split_simR (hSp : SplitRInv) {Δ : Nat → TyS} {b : Nat} {fn : List Sem → Option BodyOut}
    (hgb : GoodBelow dm.read b fn) (hd : ParDecR D) {fuel : Nat} {k : Value → Value → M Unit}
    (hk : KeepsAtZR k) {st : MState} (hkern : Kern stR st) (hm : Mode st) (htd : st.tailDecl = none) (ρ : Assignment)
    (hab : ∀ m, ρ 0 = .el0 Nat m → m ≤ b) :
    TailSim (KR dm D Δ (GR dm.read φ b fn) b) ρ φ fuel st bodyR k :=
  fun _ _ _ _ hpre hr _ hrun => split_outR hSp hgb hd hk hkern hm htd hrun hab hpre hr _

end

end Ochr.Meaning.Steps.Form.ColumnR
