import Ochr.Meaning.Steps.RecDescR
import Ochr.Meaning.Steps.FixEqDesc

/-!
# The knot at `R` in the general vocabulary: `R`'s fixpoint equation from the column's entry condition alone (lead40, 2026-11-28; docs/31 D246)

The brief's task 4. `FixEqDesc.fixEqG_of` derives the fixpoint equation of every accepted global from two clauses of
the context, `RecDescG` and `FnGoodG`, stated for every global of a state, in the vocabulary of the frame lemma (`fbG`,
`psG`, `outG`, `lG`, `formG`, any context `K`). lead39 kernel-checked their CONTENTS at the recursive column's function
`R (n : Nat) : Nat by n := match n { Z => Z, S m => R(m) }` in the column's vocabulary (`fbR`, `psI`, `outI`, `1`,
`emptyState 0`, the column's context `K0R`), and left two gaps:
- (i) the vocabulary: at a context whose decision table is aligned with the checker at `R`'s generic call
  (`DecTab K.D stR`, the column's entry condition), `fbG`, `psG`, `outG`, `lG`, `formG` ARE the column's (`fbG_R`, …);
- (ii) the context: the column's lemmas are about the column's context `KR` (the definition under check), the general
  clauses about any `K`; but the run of `R`'s body reads of its context only the data model and the decisions
  (`ColumnRRun.runR` is generic in `K` given `ParDecR K.D`), so the column's computations hold at every `K`
  (`fixBodyAt_RK`, `fixBodyAt_R_anyK`).
Crossed here, per code: `fixEqAt_of` is `fixEqG_of` for one global's code (`RecDescAt`, `FnGoodAt` are the two clauses'
bodies at that code), and `fixEqAt_R` is `R`'s fixpoint equation at every context with the aligned table, assuming
nothing else.
-/

namespace Ochr.Meaning.Steps.Form.FixEqDesc

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- `RecDescG`'s body at one global's code. -/
def RecDescAt (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term) : Prop :=
  ∀ (args : List Sem), DomMembers K.dm.read (psG K ρ φ ds) args →
    ∀ (outX outY : PiCod) (gX gY : List Sem → Option BodyOut),
      outX.isRef = (outG K ρ φ ds c).isRef → outY.isRef = (outG K ρ φ ds c).isRef →
      PiFits K.dm.read (lG K hs ds c) (psG K ρ φ ds) outX (fun _ => True) →
      PiFits K.dm.read (lG K hs ds c) (psG K ρ φ ds) outY (fun _ => True) →
      (∀ a, DomMembers K.dm.read (psG K ρ φ ds) a → ∃ o, gX a = some o ∧ OutGood' K.dm.read (psG K ρ φ ds) outX a o) →
      (∀ a, DomMembers K.dm.read (psG K ρ φ ds) a → ∃ o, gY a = some o ∧ OutGood' K.dm.read (psG K ρ φ ds) outY a o) →
      (∀ bs, DomMembers K.dm.read (psG K ρ φ ds) bs → fixRank dec bs < fixRank dec args →
        gX bs = gY bs ∧ outX.cod bs = outY.cod bs) →
      fixBodyAt K ρ φ (fbG K ρ φ ds c) formG (psG K ρ φ ds) (outG K ρ φ ds c)
          (piTyAt K.dm.read (lG K hs ds c) (psG K ρ φ ds) outX) 0 body
          (closureAt K.dm.read (lG K hs ds c) φ (psG K ρ φ ds) outX gX) args =
        fixBodyAt K ρ φ (fbG K ρ φ ds c) formG (psG K ρ φ ds) (outG K ρ φ ds c)
          (piTyAt K.dm.read (lG K hs ds c) (psG K ρ φ ds) outY) 0 body
          (closureAt K.dm.read (lG K hs ds c) φ (psG K ρ φ ds) outY gY) args

/-- `FnGoodG`'s body at one global's code. -/
def FnGoodAt (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term) : Prop :=
  PiFits K.dm.read (lG K hs ds c) (psG K ρ φ ds) (outG K ρ φ ds c) (fun _ => True) ∧
    ∀ a, DomMembers K.dm.read (psG K ρ φ ds) a →
      ∃ o, GG K ρ φ hs ds c dec body a = some o ∧ OutGood' K.dm.read (psG K ρ φ ds) (outG K ρ φ ds c) a o

/-- `FixEqG`'s body at one global's code. -/
def FixEqAt (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term) : Prop :=
  ∀ (args : List Sem), DomMembers K.dm.read (psG K ρ φ ds) args →
    GG K ρ φ hs ds c dec body args =
      fixBodyWith K ρ φ (fbG K ρ φ ds c) formG (psG K ρ φ ds) (outG K ρ φ ds c) 0 body
        (selfSlot dec (selfG K ρ φ hs ds c dec body) (.plain (piTG K ρ φ hs ds c)) (fbG K ρ φ ds c).2.2) args

/-- `stage_agree` at one code. -/
theorem stage_agreeAt {hs : List Hint} {ds : List Term} {c : Term} {j : Nat} {body : Term}
    (hdesc : RecDescAt K ρ φ hs ds c (some j) body) (hg : FnGoodAt K ρ φ hs ds c (some j) body) :
    ∀ m a, DomMembers K.dm.read (psG K ρ φ ds) a → fixRank (some j) a < m →
      stG K ρ φ hs ds c (some j) body m a = GG K ρ φ hs ds c (some j) body a := by
  obtain ⟨hfit, hgood⟩ := hg
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro a ha hlt
    cases m with
    | zero => exact absurd hlt (Nat.not_lt_zero _)
    | succ k =>
      have hk := ih k (Nat.lt_succ_self k)
      have hr := ih (fixRank (some j) a) hlt
      have gk : ∀ b, DomMembers K.dm.read (psG K ρ φ ds) b → fixRank (some j) b < k →
          ∃ o, stG K ρ φ hs ds c (some j) body k b = some o ∧ OutGood' K.dm.read (psG K ρ φ ds) (outG K ρ φ ds c) b o :=
        fun b hb hl => by rw [hk b hb hl]; exact hgood b hb
      have gr : ∀ b, DomMembers K.dm.read (psG K ρ φ ds) b → fixRank (some j) b < fixRank (some j) a →
          ∃ o, stG K ρ φ hs ds c (some j) body (fixRank (some j) a) b = some o ∧
            OutGood' K.dm.read (psG K ρ φ ds) (outG K ρ φ ds c) b o :=
        fun b hb hl => by rw [hr b hb hl]; exact hgood b hb
      rw [stG_succ, GG_eq, stG_succ]
      refine hdesc a ha _ _ _ _ rfl rfl (piFits_weakCod hfit _ _) (piFits_weakCod hfit _ _)
        (stageFn_good' hfit gk) (stageFn_good' hfit gr) (fun b hb hlt' => ⟨?_, ?_⟩)
      · have h1 : fixRank (some j) b < k := by omega
        simp only [stageFn, if_pos h1, if_pos hlt']
        rw [hk b hb h1, hr b hb hlt']
      · have h1 : fixRank (some j) b < k := by omega
        simp only [weakCod, if_pos h1, if_pos hlt']

/-- **The fixpoint equation at one code** (`fixEqG_of` per code): from the two clauses' bodies at that code. -/
theorem fixEqAt_of {hs : List Hint} {ds : List Term} {c : Term} {dec : Option Nat} {body : Term}
    (hd : RecDescAt K ρ φ hs ds c dec body) (hg : FnGoodAt K ρ φ hs ds c dec body) :
    FixEqAt K ρ φ hs ds c dec body := by
  intro args hargs
  -- R-dec (docs/31 D296): without `by` the equation is the definition
  cases dec with
  | none => rfl
  | some j =>
  obtain ⟨hfit, hgood⟩ := hg
  have hagree := stage_agreeAt K ρ φ hd ⟨hfit, hgood⟩
  have gr : ∀ b, DomMembers K.dm.read (psG K ρ φ ds) b → fixRank (some j) b < fixRank (some j) args →
      ∃ o, stG K ρ φ hs ds c (some j) body (fixRank (some j) args) b = some o ∧
        OutGood' K.dm.read (psG K ρ φ ds) (outG K ρ φ ds c) b o :=
    fun b hb hl => by rw [hagree _ b hb hl]; exact hgood b hb
  rw [GG_eq, stG_succ]
  refine hd args hargs _ _ _ _ rfl rfl (piFits_weakCod hfit _ _) hfit
    (stageFn_good' hfit gr) hgood (fun b hb hlt => ⟨?_, ?_⟩)
  · simp only [stageFn, if_pos hlt]
    exact hagree _ b hb hlt
  · simp only [weakCod, if_pos hlt]

end

end Ochr.Meaning.Steps.Form.FixEqDesc

/-! ## Gap (ii): the column's computations of `R`'s body at every context -/

namespace Ochr.Meaning.Steps.Form.ColumnR

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Ochr.Meaning.Steps.Form.ColumnI (piNat nB psI outI NoBorrow liveLabels_of_rel ρAt)
open Ochr.Meaning.Steps.Form.ColumnP (ΔP RI pn0 RefJ RefP dropN setN0)

section
variable {φ : Future}

/-- **`fixBodyAt_R` at any context whose table makes `R`'s decisions** (gap (ii)): the run of `R`'s body reads of its
context only the data model and the decisions (`runR` is generic in `K`); the start state is the column's, read at
`K`'s data model and decisions. -/
theorem fixBodyAt_RK (K : RunCtx) (hd : ParDecR K.D) (ρ : Assignment)
    (fb : List PBind × PBind) (h1 : fb.1 = [(fun _ => .plain TyM.nat, .other)]) (h2 : fb.2.2 = .other)
    {b : Nat} {fn : List Sem → Option BodyOut} (hgb : GoodBelow K.dm.read b fn) {a : Nat} (hab : a ≤ b) :
    ∃ o, fixBodyAt K ρ φ fb (emptyState 0) psI outI (GR K.dm.read φ b fn).2.m 0 bodyR
        (GR K.dm.read φ b fn).1 [.el0 Nat a] = some o ∧ o.result ∈ₛ[K.dm.read] TyM.nat ∧ o.finals = [] := by
  have hst := start_R (dm := K.dm) (D := K.D) (b := b) (G := GR K.dm.read φ b fn) rfl ρ fb h1 h2 a
  have hrel := rel_stR (dm := K.dm) (D := K.D) (G := GR K.dm.read φ b fn) (b := b) (ρAt ρ a) φ
  have hP := refR_of_rel hrel
  have hts := tySelf_of_rel hrel
  obtain ⟨hZ, hS⟩ := runR (K := K) (ρ := ρ) hd hP (movedIn_GR K.dm.read φ b fn) hts
    (GR_whole K.dm.read φ b fn hgb) (.inl (GR_mem hgb)) (fb.2.1 [.el0 Nat a])
  have hl : ∀ x : SState, x.liveLabels = [] → (dropN K x).liveLabels = [] := fun x hx => by
    unfold dropN; rw [Strict.liveLabels_setAt]; exact hx
  have hl0 : (SM' (KR K.dm K.D ΔP (GR K.dm.read φ b fn) b) (ρAt ρ a) stR).liveLabels = [] := liveLabels_SMR _
  unfold fixBodyAt fixBodyWith
  dsimp only
  rw [hst]
  dsimp only
  rw [h2, fnErasedD_other, SM.bodyRun_false]     -- main's D142: `R` returns data
  cases a with
  | zero =>
    rw [hZ rfl]
    dsimp only
    rw [hl _ hl0]
    refine ⟨⟨.el0 Nat 0, [], none⟩, ?_, ⟨0, rfl⟩, rfl⟩
    simp [ColumnI.endsOk_nil]; rfl
  | succ a =>
    have ha : a < b := by omega
    obtain ⟨o, ho, hog, -⟩ := hgb a ha
    have hc := callGR (φ := φ) hgb ha ho (.plain TyM.nat) rfl
      (setN0 K (SM' (KR K.dm K.D ΔP (GR K.dm.read φ b fn) b) (ρAt ρ (a + 1)) stR))
    rw [hS a _ rfl hc]
    dsimp only
    rw [hl _ (by unfold setN0; rw [Strict.liveLabels_setAt]; exact hl0)]
    refine ⟨⟨o.result, [], none⟩, ?_, hog.1, rfl⟩
    simp [ColumnI.endsOk_nil]; rfl

/-- **`fixBodyAt_R_any` at any context whose table makes `R`'s decisions** (gap (ii)): with `self` a whole member that
moves nothing, the body returns `0` at `0`, and at `a + 1` what `self` applied at `a` returns. -/
theorem fixBodyAt_R_anyK (K : RunCtx) (hd : ParDecR K.D) (ρ : Assignment)
    (fb : List PBind × PBind) (h1 : fb.1 = [(fun _ => .plain TyM.nat, .other)]) (h2 : fb.2.2 = .other)
    (G : Sem × TyS) (hG : G.2 = .plain G.2.m) (hgw : G.1.whole) (hmv : ∀ q, Sem.movedIn G.1 q = [])
    (hgm : G.1 ∈ₛ[K.dm.read] G.2.m) :
    fixBodyAt K ρ φ fb (emptyState 0) psI outI G.2.m 0 bodyR G.1 [.el0 Nat 0] = some ⟨.el0 Nat 0, [], none⟩ ∧
      ∀ (a : Nat) (v : Sem) (T : TyS), T.label = none →
        (∀ s, callOf K.dm.read (G.1, .plain G.2.m) [(.el0 Nat a, .plain TyM.nat)] s = some ((v, T), s)) →
        fixBodyAt K ρ φ fb (emptyState 0) psI outI G.2.m 0 bodyR G.1 [.el0 Nat (a + 1)] = some ⟨v, [], none⟩ := by
  have hl : ∀ x : SState, x.liveLabels = [] → (dropN K x).liveLabels = [] := fun x hx => by
    unfold dropN; rw [Strict.liveLabels_setAt]; exact hx
  refine ⟨?_, fun a v T hT hc => ?_⟩
  · have hst := start_R (dm := K.dm) (D := K.D) (b := 0) (G := G) hG ρ fb h1 h2 0
    have hrel := rel_stR (dm := K.dm) (D := K.D) (G := G) (b := 0) (ρAt ρ 0) φ
    have hP := refR_of_rel hrel
    have hts := tySelf_of_rel hrel
    obtain ⟨hZ, -⟩ := runR (K := K) (ρ := ρ) hd hP hmv hts hgw (.inl hgm) (fb.2.1 [.el0 Nat 0])
    have hl0 : (SM' (KR K.dm K.D ΔP G 0) (ρAt ρ 0) stR).liveLabels = [] := liveLabels_SMR _
    unfold fixBodyAt fixBodyWith
    dsimp only
    rw [hst]
    dsimp only
    rw [h2, fnErasedD_other, SM.bodyRun_false]     -- main's D142: `R` returns data
    rw [hZ rfl]
    dsimp only
    rw [hl _ hl0]
    simp [ColumnI.endsOk_nil]; rfl
  · have hst := start_R (dm := K.dm) (D := K.D) (b := 0) (G := G) hG ρ fb h1 h2 (a + 1)
    have hrel := rel_stR (dm := K.dm) (D := K.D) (G := G) (b := 0) (ρAt ρ (a + 1)) φ
    have hP := refR_of_rel hrel
    have hts := tySelf_of_rel hrel
    obtain ⟨-, hS⟩ := runR (K := K) (ρ := ρ) hd hP hmv hts hgw (.inl hgm) (fb.2.1 [.el0 Nat (a + 1)])
    have hl0 : (SM' (KR K.dm K.D ΔP G 0) (ρAt ρ (a + 1)) stR).liveLabels = [] := liveLabels_SMR _
    unfold fixBodyAt fixBodyWith
    dsimp only
    rw [hst]
    dsimp only
    rw [h2, fnErasedD_other, SM.bodyRun_false]     -- main's D142: `R` returns data
    rw [hS a _ rfl (hc _)]
    dsimp only
    rw [hl _ (by unfold setN0; rw [Strict.liveLabels_setAt]; exact hl0)]
    simp [ColumnI.endsOk_nil, hT]

end

end Ochr.Meaning.Steps.Form.ColumnR

/-! ## Gap (i): the frame lemma's vocabulary at `R`'s code is the column's, under the aligned table; the assembly -/

namespace Ochr.Meaning.Steps.Form.ColumnR

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.FixEqDesc
open Ochr.Meaning.Steps.Form.ColumnI (piNat nB psI outI NoBorrow liveLabels_of_rel ρAt)

section
variable {φ : Future} (K : RunCtx) (ρ : Assignment)

theorem formG_R : formG = emptyState 0 := rfl

end

/-- **What the vocabulary and the knot read of a decision table at `R`'s code** (lead46: the column's entry condition
`DecTab K.D stR` was used only through these, and it is false at the top's tables, which hold the library's declarations
and `R`'s entry; `Top.RT.decR_of` proves `DecR` at every state whose Σ starts with `R`'s entry): the column's
`ParDecR` and the reference `.fix` clause's four decisions (`fixDecR`). -/
def DecR (D : Decisions) : Prop :=
  ParDecR D ∧ D.typeDecl [] .nat = .other ∧ D.typeDecl [.other] .nat = .other ∧
    D.piSort [] (.pi [⟨"n"⟩] [.nat] .nat) = 1 ∧ D.flags [] fixR = (false, false)

/-- A table aligned with the checker at `stR` decides `R`'s code as `DecR` says. -/
theorem decR_of_stR {D : Decisions} (hd : DecTab D stR) : DecR D := ⟨parDecR hd, fixDecR hd⟩

section
variable {φ : Future} (K : RunCtx) (ρ : Assignment)

theorem paramDecls_R (hDR : DecR K.D) : K.D.paramDecls (scopeOf formG) [.nat] = [.other] := by
  obtain ⟨hd1, -, -, -⟩ := hDR.2
  show K.D.paramDecls [] [.nat] = [.other]
  simp [Decisions.paramDecls, Decisions.teleDecls, hd1]

theorem psG_R (hDR : DecR K.D) : psG K ρ φ [.nat] = psI :=
  ColumnI.runDoms_nat K ρ φ formG (paramDecls_R K hDR)

theorem outG_R : outG K ρ φ [.nat] .nat = outI := ColumnI.codOf_nat K ρ φ formG _ _

theorem lG_R (hDR : DecR K.D) : lG K [⟨"n"⟩] [.nat] .nat = 1 := (hDR.2).2.2.1

theorem fbG_R1 (hDR : DecR K.D) : (fbG K ρ φ [.nat] .nat).1 = [(fun _ => .plain TyM.nat, .other)] :=
  ColumnI.bindsOf_nat K ρ φ formG (paramDecls_R K hDR)

theorem fbG_R2 (hDR : DecR K.D) : (fbG K ρ φ [.nat] .nat).2.2 = .other := by
  obtain ⟨hd1, hd2, -, -⟩ := hDR.2
  show K.D.typeDecl (K.D.teleDecls [] [.nat]) .nat = .other
  simp [Decisions.teleDecls, hd1, hd2]

/-- **The knot at `R`, at every context**: every stage of `R`'s closure as the `.fix` clause forms it at `K` is good
below its bound (`goodBelow_stg` with `fixBodyAt_RK`). -/
theorem goodBelow_stgK (hDR : DecR K.D) :
    ∀ b, GoodBelow K.dm.read b (fixStage K ρ φ (fbG K ρ φ [.nat] .nat) 1 (emptyState 0) psI outI (some 0) 0 bodyR b) := by
  have hd := hDR.1
  intro b
  induction b with
  | zero => intro m h; exact absurd h (Nat.not_lt_zero _)
  | succ b ih =>
    intro a ha
    obtain ⟨o, ho, hr, hf⟩ := fixBodyAt_RK (φ := φ) K hd ρ (fbG K ρ φ [.nat] .nat) (fbG_R1 K ρ hDR) (fbG_R2 K ρ hDR) ih
      (Nat.lt_succ_iff.mp ha)
    refine ⟨o, ho, ⟨hr, fun i d hi hd' => ?_⟩, hf⟩
    rcases i with _ | i
    · simp [psI] at hi; subst hi; cases hd'
    · simp [psI] at hi

/-- **`FnGoodG`'s body at `R`, in the general vocabulary, at every context with the aligned table** (gap (i) and (ii)
crossed): `R`'s function type fits level `1` and its function is defined and good at every number. -/
theorem fnGoodAt_R (hDR : DecR K.D) : FnGoodAt K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR := by
  unfold FnGoodAt
  rw [psG_R K ρ hDR, outG_R K ρ, lG_R K hDR]
  refine ⟨⟨by decide, fun _ _ _ => Nat.le_refl 1⟩, fun a ha => ?_⟩
  obtain ⟨m, rfl⟩ := domMembers_one ha
  obtain ⟨o, ho, hg, hf⟩ := goodBelow_stgK (φ := φ) K ρ hDR (m + 1) m (Nat.lt_succ_self m)
  refine ⟨o, ?_, hg, fun h => absurd h (by simp [outI]), by rw [hf]; rfl⟩
  show fixStage K ρ φ (fbG K ρ φ [.nat] .nat) (lG K [⟨"n"⟩] [.nat] .nat) formG (psG K ρ φ [.nat]) (outG K ρ φ [.nat] .nat)
    (some 0) 0 bodyR (fixRank (some 0) [.el0 Nat m] + 1) [.el0 Nat m] = some o
  rw [psG_R K ρ hDR, outG_R K ρ, lG_R K hDR, show fixRank (some 0) [.el0 Nat m] = m from rkR_nat m]
  exact ho

/-- **`RecDescG`'s body at `R`, in the general vocabulary, at every context with the aligned table** (`recDesc_R` with
gaps (i) and (ii) crossed). -/
theorem recDescAt_R (hDR : DecR K.D) : RecDescAt K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR := by
  have hd := hDR.1
  unfold RecDescAt
  rw [psG_R K ρ hDR, outG_R K ρ, lG_R K hDR, formG_R]
  intro args hargs outX outY gX gY hrX hrY hfX hfY hgX hgY hag
  have hX : SelfR K.dm outX gX := ⟨hrX, fun a ha => hfX.2 a ha trivial, hgX⟩
  have hY : SelfR K.dm outY gY := ⟨hrY, fun a ha => hfY.2 a ha trivial, hgY⟩
  obtain ⟨a, rfl⟩ := domMembers_one hargs
  have hTX := fixBodyAt_R_anyK (φ := φ) K hd ρ (fbG K ρ φ [.nat] .nat) (fbG_R1 K ρ hDR) (fbG_R2 K ρ hDR)
    (closureAt K.dm.read 1 φ psI outX gX, .plain (piTyAt K.dm.read 1 psI outX)) rfl hX.whole (SelfR.movedIn outX gX) hX.mem
  have hTY := fixBodyAt_R_anyK (φ := φ) K hd ρ (fbG K ρ φ [.nat] .nat) (fbG_R1 K ρ hDR) (fbG_R2 K ρ hDR)
    (closureAt K.dm.read 1 φ psI outY gY, .plain (piTyAt K.dm.read 1 psI outY)) rfl hY.whole (SelfR.movedIn outY gY) hY.mem
  dsimp only [TyS.plain] at hTX hTY
  cases a with
  | zero => rw [hTX.1, hTY.1]
  | succ a =>
    obtain ⟨oX, hoX, -⟩ := hX.tot [.el0 Nat a] (domMembers_nat K.dm.read a)
    obtain ⟨oY, hoY, -⟩ := hY.tot [.el0 Nat a] (domMembers_nat K.dm.read a)
    have he : gX [.el0 Nat a] = gY [.el0 Nat a] :=
      (hag _ (domMembers_nat K.dm.read a) (by
        rw [show fixRank (some 0) [Sem.el0 Nat a] = a from rkR_nat a,
          show fixRank (some 0) [Sem.el0 Nat (a + 1)] = a + 1 from rkR_nat (a + 1)]; omega)).1
    rw [hoX, hoY, Option.some.injEq] at he
    subst he
    rw [hTX.2 a oX.result _ rfl (hX.apply a hoX), hTY.2 a oX.result _ rfl (hY.apply a hoY)]

/-- **`R`'s FIXPOINT EQUATION in the general vocabulary, from the column's entry condition alone** (docs/31 D246; the
brief's task 4): at every context whose decision table is aligned with the checker at `R`'s generic call, the function the
`.fix` clause forms for `R`'s code (`GG`) is one run of its body with its own closure bound (`fixBodyAt`, `selfG`), at
every member argument. `FixEqDesc.fixEqAt_of` (the per-code `fixEqG_of`) from `recDescAt_R` and `fnGoodAt_R`. -/
theorem fixEqAt_R (hDR : DecR K.D) : FixEqAt K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR :=
  fixEqAt_of K ρ φ (recDescAt_R K ρ hDR) (fnGoodAt_R K ρ hDR)

end

end Ochr.Meaning.Steps.Form.ColumnR
