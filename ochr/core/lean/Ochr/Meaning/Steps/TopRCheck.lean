import Ochr.Meaning.Steps.TopRStart

/-!
# The acceptance test at `R`: `R`'s check inverted (`FixCheckAt`'s witness; lead46, docs/31 D259 on)

`checkDef`'s function branch and `checkFix`'s prefix, inverted at `def R` from the stage's Σ (no global, the stage's
declarations `I`), down to the body's tail check: the generic state is `st0R I u` (the column's `stRm` with the stage's
declarations and the check's fresh mark `u`), the continuation is `fixCont`, and the state after the check's
`restoreKeep` only extends the tables of the state after the body's check. The steps whose fuel is an argument are run
by the kernel at every fuel above a few (`runs_inv_eval`), the rest peeled.
-/

namespace Ochr.Meaning.Steps.Form.Top.RT

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master
open Ochr.Meaning.Steps.Machine Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form.ColumnR
open Ochr.Meaning.Steps.Form.ColumnI (psI outI ρAt nB piNat)

/-- A run whose outcome the kernel computes at every log. -/
theorem runs_inv_eval {α : Type} {x : M α} {st st' : MState} {b : Nat} {a a₀ : α} {s₀ : MState}
    (h : Runs x st b a st') (he : ∀ L, (runMachineL x st b L).1 = .ok a₀ s₀) : a = a₀ ∧ st' = s₀ := by
  obtain ⟨L, left, log, e⟩ := h
  have h2 := he L
  rw [e] at h2
  simp only [Outcome.ok.injEq] at h2
  exact h2

/-- A run the kernel computes to exhaustion has no successful outcome. -/
theorem runs_false_eval {α : Type} {x : M α} {st st' : MState} {b : Nat} {a : α}
    (h : Runs x st b a st') (he : ∀ L, ∃ m, (runMachineL x st b L).1 = .exhausted m) : False := by
  obtain ⟨L, left, log, e⟩ := h
  obtain ⟨m, h2⟩ := he L
  rw [e] at h2
  cases h2

theorem runs_modelSignature_R {st st' : MState} {b : Nat} {m : Bool}
    (h : Runs (modelSignature [⟨"n"⟩] [.nat] .nat) st b m st') : m = false ∧ st' = st := by
  rcases b with _ | b
  · exact (runs_false_eval h fun _ => ⟨_, rfl⟩).elim
  · exact runs_inv_eval h fun _ => rfl

theorem runs_absAt_nat {k : Nat} {st st' : MState} {b : Nat} {v : Value}
    (h : Runs (absAt k .other .tNat) st b v st') :
    v = .abs st.nextAbs ∧
      st' = { st with nextAbs := st.nextAbs + 1, absTy := st.absTy.push .tNat, absDecl := st.absDecl.push .other } := by
  rcases k with _ | _ | _ | _ | _ | k
  all_goals first
    | exact (runs_false_eval h fun _ => ⟨_, rfl⟩).elim
    | exact runs_inv_eval h fun _ => rfl

theorem runs_readingAgrees_nat {k : Nat} {hn : Hint} {v : Value} (hv : v ≠ .proof) {st st' : MState} {b : Nat} {u : PUnit}
    (h : Runs (readingAgrees k hn .tNat .other v) st b u st') : st' = st := by
  rcases k with _ | _ | k
  · exact (runs_false_eval h fun _ => ⟨_, rfl⟩).elim
  · exact (runs_false_eval h fun _ => ⟨_, rfl⟩).elim
  · have e : (v == Value.proof) = false := by cases v <;> first | rfl | exact absurd rfl hv
    exact (runs_inv_eval h fun _ => by simp [readingAgrees, e, isPropV]; rfl).2


theorem runs_refineDecl_other {st st' : MState} {b : Nat} {r : DeclInfo}
    (h : Runs (refineDecl .other) st b r st') : r = .other ∧ st' = st := runs_inv_eval h fun _ => rfl

/-- `restoreKeep` of a snapshot with an empty [Rec] stack, where the run kept the counters and records: the snapshot
with the run's next mark. -/
theorem runs_restoreKeep_nil {saved cur st' : MState} {b : Nat} {u : PUnit}
    (h : Runs (restoreKeep saved) cur b u st') (hrs : saved.recStack = []) (ha : cur.nextAbs = saved.nextAbs)
    (hl : cur.nextLoan = saved.nextLoan) (hn : cur.neutrals = saved.neutrals) (he : cur.etaRefs = saved.etaRefs)
    (ht : cur.absTy = saved.absTy) (hd : cur.absDecl = saved.absDecl) :
    st' = { saved with nextRecUid := cur.nextRecUid } := by
  unfold restoreKeep at h
  have := runs_modify_inv h
  subst this
  simp only [hrs, List.map_nil, ha, hl, hn, he, ht, hd]
  congr 1
  simp

/-- **`Nat` as a type, at an empty [Rec] stack** (`Machine.runs_evalType_nat`, keeping the stack): `Nat`, the state as it
was but for the next mark. -/
theorem runs_evalType_nat' {n : Nat} {st st' : MState} {bh : Nat} {v : Value}
    (h : Runs (Ochr.evalType n .nat) st bh v st') (hh : st.headEval = false) (htd : st.tailDecl = none)
    (hrs : st.recStack = []) : v = .tNat ∧ ∃ nr, st' = { st with nextRecUid := nr } := by
  cases n with
  | zero =>
    have e : Ochr.evalType 0 Term.nat = inStatement (exhausted "out of fuel") := rfl
    rw [e, Machine.inStatement_eq] at h
    obtain ⟨b₁, cur, b₂, hx, hr⟩ := Machine.Runs.privately_inv h
    obtain ⟨b₃, cur', hx', rfl⟩ := Machine.Runs.withErased_inv hx
    simp only [Machine.runs_exhausted_iff] at hx'
  | succ k =>
    rw [Machine.evalType_succ, Machine.inStatement_eq] at h
    obtain ⟨b₁, cur, b₂, hx, hr⟩ := Machine.Runs.privately_inv h
    obtain ⟨b₃, cur', hx', rfl⟩ := Machine.Runs.withErased_inv hx
    obtain ⟨vT, s₁, b₄, hev, h₁⟩ := Runs.bind_inv hx'
    obtain ⟨rfl, hk, -, -⟩ := Machine.eval_nat_inv hev hh htd
    simp only at h₁
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h₁
    exact ⟨rfl, _, runs_restoreKeep_nil hr hrs hk.nextAbs.symm hk.nextLoan.symm hk.neutrals.symm hk.etaRefs.symm
      hk.absTy.symm hk.absDecl.symm⟩

/-- `checkFix`'s continuation only extends the tables. -/
theorem grows_fixCont (n : Nat) (name : String) (v T : Value) : GrowsM (fixCont n name v T) :=
  Machine.growsM_of_growsIn fun G => by
    have hCv : ∀ (G : Machine.Tab) (f : Nat) (v w : Value), Machine.GrowsIn G (Ochr.conv f v w) :=
      fun G f => (Machine.machineGrows f).conv
    have hBR : ∀ (G : Machine.Tab) (f : Nat) (what : String) (v T : Value) (lent : List Place) (lw : String),
        Machine.GrowsIn G (Ochr.bodyReturns f what v T lent lw) := fun G f => (Machine.machineGrows f).bodyReturns
    have hPF : ∀ (G : Machine.Tab) (f : Nat), Machine.GrowsIn G (Ochr.popFrame f) := fun G f => (Machine.machineGrows f).popFrame
    unfold fixCont
    grows_goI

set_option maxHeartbeats 8000000 in
/-- **`R`'s check, inverted to its body's tail check** (PROVED, from any declarations `I` and the empty Σ): an accepted
`def R` appended `R`'s entry (`model` false), checked the body by `checkTail` with `checkFix`'s continuation from the
generic state `st0R I u` (`u` the check's fresh mark), and its `restoreKeep` only extended the tables of the state the
body's check left; Σ after is `R`'s entry, the declarations `I`. -/
theorem R_check_inv {I : List IndDecl} {fuel : Nat} {st' : MState}
    (hr : (runMachine (checkItem (.defn defR)) { globals := [], inds := I } fuel).1 = .ok () st') :
    ∃ (n bh u : Nat) (st₁ : MState), Runs (Ochr.checkTail n bodyR (fixCont n "R")) (st0R I u) bh () st₁ ∧
      TablesGrow st₁ st' ∧ st'.globals = [gR] ∧ st'.inds = I := by
  have h := Machine.runs_of_runMachine_fst hr
  unfold checkItem at h
  obtain ⟨_, s₀₀, b₀₀, hsh, h⟩ := Runs.bind_inv h
  have hs0 : s₀₀ = { globals := [], inds := I } := by
    unfold seedHoles at hsh
    rw [Machine.runs_get_bind] at hsh
    exact (runs_pure_inv hsh).2
  subst hs0
  unfold checkDef at h
  obtain ⟨dcl, s₁, b₁, hd, h₁⟩ := Runs.bind_inv h
  clear h
  have := runs_keep (Machine.keep_declared _) hd; subst this
  dsimp only at h₁
  have e1 : ((defR.cod :: defR.doms).any (Term.mentionsConst defR.name)) = false := rfl
  have e2 : (!((defR.cod :: defR.doms).all Term.refTopOk && defR.body.refsOk)) = false := rfl
  by_cases hd1 : dcl = true
  · simp only [hd1, if_true] at h₁
    exact absurd h₁ (fun h => by obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact runs_err_false he)
  simp only [hd1, e1, e2, Bool.false_eq_true, if_false] at h₁
  obtain ⟨fl, s₂, b₂, hfl, h₂⟩ := Runs.bind_inv h₁
  clear h₁
  have := runs_keep Machine.keep_fuelLeft hfl; subst this
  obtain ⟨_, s₃, b₃, hdo, h₃⟩ := Runs.bind_inv h₂
  clear h₂
  have := runs_keep (keep_discard ((decideKeep _).2.2.2.2.2.2.2.2.1 _ _ _ _)) hdo; subst this
  obtain ⟨_, s₄, b₄, hu, h₄⟩ := Runs.bind_inv h₃
  clear h₃
  have := runs_keep (Machine.keep_undeclaredCheck _ _) hu; subst this
  simp only [defR, List.isEmpty_cons, Bool.false_eq_true, if_false, Option.isSome_none] at h₄
  obtain ⟨model, s₅, b₅, hms, h₅⟩ := Runs.bind_inv h₄
  clear h₄
  obtain ⟨rfl, rfl⟩ := runs_modelSignature_R hms
  simp only [Machine.runs_modify_bind, Bool.false_eq_true, if_false, bind_assoc, runs_pure_bind', pure_bind] at h₅
  obtain ⟨f, s₆, b₆, hf6, h₆⟩ := Runs.bind_inv h₅
  clear h₅
  have := runs_keep Machine.keep_fuelLeft hf6; subst this
  obtain ⟨_, s₇, b₇, hfix, h₇⟩ := Runs.bind_inv h₆
  clear h₆
  have hs7 : st' = s₇ := (runs_pure_inv h₇).2
  subst hs7
  clear h₇
  rcases f with _ | k
  · unfold checkFix at hfix; simp only [Machine.runs_exhausted_iff] at hfix
  unfold checkFix at hfix
  have hHO : headOnly (fun d p => p.root == d + [Term.nat].length) 0 bodyR = true := by decide
  simp only [borrowParamCheck, Option.isNone_some, Bool.false_and, Bool.false_eq_true, if_false, if_true, ite_true,
    Machine.runs_get_bind, Machine.runs_modify_bind, bind_assoc, runs_pure_bind', pure_bind, hHO, Bool.and_false,
    Bool.not_true, Bool.and_true] at hfix
  obtain ⟨pf, s₈, b₈, hpf, h₈⟩ := Runs.bind_inv hfix
  clear hfix
  obtain ⟨rfl, rfl⟩ := Machine.runs_paramFlags_nat hpf
  obtain ⟨pd, s₉, b₉, hpd, h₉⟩ := Runs.bind_inv h₈
  clear h₈
  obtain ⟨rfl, rfl⟩ := Machine.runs_paramDecls_nat hpd
  simp only [pushFrame, Machine.runs_modify_bind, bind_assoc] at h₉
  obtain ⟨_, s₁₀, b₁₀, hpc, h₁₀⟩ := Runs.bind_inv h₉
  clear h₉
  have := Machine.runs_pushCaps_nil hpc; subst this
  simp only [List.zip_cons_cons, List.zip_nil_left, List.zip_nil_right, List.forIn_cons, List.forIn_nil, bind_assoc] at h₁₀
  obtain ⟨A, s₁₁, b₁₁, hA, h₁₁⟩ := Runs.bind_inv h₁₀
  clear h₁₀
  obtain ⟨rfl, nr₁, rfl⟩ := runs_evalType_nat' hA rfl rfl rfl
  simp only [bind_assoc] at h₁₁
  obtain ⟨p₁, s₁₂, b₁₂, hp1, h₁₂⟩ := Runs.bind_inv h₁₁
  clear h₁₁
  obtain ⟨rfl, rfl⟩ := Machine.runs_isPropV_nat hp1
  simp only [Bool.false_eq_true, if_false, bind_assoc] at h₁₂
  obtain ⟨c, s₁₃, b₁₃, hc, h₁₃⟩ := Runs.bind_inv h₁₂
  clear h₁₂
  obtain ⟨rfl, rfl⟩ := runs_absAt_nat hc
  obtain ⟨_, s₁₄, b₁₄, hra, h₁₄⟩ := Runs.bind_inv h₁₃
  clear h₁₃
  have := runs_readingAgrees_nat (by intro e; cases e) hra; subst this
  obtain ⟨rd, s₁₅, b₁₅, hrd, h₁₅⟩ := Runs.bind_inv h₁₄
  clear h₁₄
  obtain ⟨rfl, rfl⟩ := runs_refineDecl_other hrd
  simp only [pushBind, topIdx, modifyFrame, Machine.runs_get_bind, Machine.runs_modify_bind, bind_assoc,
    runs_pure_bind', pure_bind] at h₁₅
  clear hpc hpd hpf hA hp1 hc hra hrd hf6 hfl hdo hu hms hd hsh hr h e1 e2
  obtain ⟨g, s₁₆, b₁₆, hg, h₁₆⟩ := Runs.bind_inv h₁₅
  clear h₁₅
  obtain ⟨rfl, nr₂, rfl⟩ := runs_evalType_nat' hg rfl rfl rfl
  obtain ⟨_, s₁₇, b₁₇, htr, h₁₇⟩ := Runs.bind_inv h₁₆
  clear h₁₆
  obtain ⟨-, rfl⟩ := runs_inv_eval htr fun _ => rfl
  obtain ⟨F1, s₁₈, b₁₈, hpop, h₁₈⟩ := Runs.bind_inv h₁₇
  clear h₁₇
  obtain ⟨rfl, rfl⟩ := runs_inv_eval hpop fun _ => rfl
  simp only [Machine.runs_get_bind, Machine.runs_modify_bind, bind_assoc] at h₁₈
  rcases k with _ | k
  · obtain ⟨_, _, _, hx, -⟩ := Runs.bind_inv h₁₈
    unfold pushCaps at hx; simp only [Machine.runs_exhausted_iff] at hx
  obtain ⟨_, s₁₉, b₁₉, hpc2, h₁₉⟩ := Runs.bind_inv h₁₈
  clear h₁₈
  have := Machine.runs_pushCaps_nil hpc2; subst this
  obtain ⟨_, s₂₀, b₂₀, hmc, h₂₀⟩ := Runs.bind_inv h₁₉
  clear h₁₉
  obtain ⟨-, rfl⟩ := runs_inv_eval hmc fun _ => rfl
  simp only [Machine.runs_get_bind, Machine.runs_modify_bind, bind_assoc] at h₂₀
  obtain ⟨_, s₂₁, b₂₁, hml, h₂₁⟩ := Runs.bind_inv h₂₀
  clear h₂₀
  obtain ⟨-, rfl⟩ := runs_inv_eval hml fun _ => rfl
  obtain ⟨_, s₂₂, b₂₂, hfor, h₂₂⟩ := Runs.bind_inv h₂₁
  clear h₂₁
  obtain ⟨-, rfl⟩ := runs_inv_eval hfor fun _ => rfl
  have hcond : ((#[].push (if (Value.tNat == Value.tNat || false) = true then some 0 else none))[0]?.join.isNone = true)
      = False := by
    have : (Value.tNat == Value.tNat) = true := by decide
    simp [this]
  simp only [hcond, if_false, Machine.runs_modify_bind, bind_assoc] at h₂₂
  obtain ⟨cl, s₂₃, b₂₃, hcl, h₂₃⟩ := Runs.bind_inv h₂₂
  clear h₂₂
  obtain ⟨rfl, rfl⟩ := Machine.runs_fnClass_piNat hcl
  simp only [withErasedIf, bne_self_eq_false, Bool.false_eq_true, if_false] at h₂₃
  obtain ⟨_, st₁, b₂₄, hct, hrk⟩ := Runs.bind_inv h₂₃
  clear h₂₃
  have hS0 : Runs (Ochr.checkTail (k + 1) bodyR (fixCont (k + 1) "R")) (st0R I nr₂) b₂₃ () st₁ := hct
  have hg0 : TablesGrow (st0R I nr₂) st₁ :=
    Runs.grows (Machine.growsM_of_growsIn fun G => (Machine.machineGrows (k + 1)).checkTail bodyR _
      fun v T => Machine.growsIn_of_growsM (grows_fixCont (k + 1) "R" v T)) hS0
  have hsv : TablesGrow { globals := [] ++ [gE false], inds := I } st₁ :=
    TablesGrow.trans (show TablesGrow { globals := [] ++ [gE false], inds := I } (st0R I nr₂) from
      ⟨rfl, rfl, Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _), Nat.zero_le _, Nat.le_refl _⟩) hg0
  have h1 := restoreKeep_grows hsv hrk
  refine ⟨k + 1, b₂₃, nr₂, st₁, hS0, h1, ?_, ?_⟩
  · rw [h1.globals, hg0.globals]; rfl
  · rw [h1.inds, hg0.inds]; rfl

end Ochr.Meaning.Steps.Form.Top.RT
