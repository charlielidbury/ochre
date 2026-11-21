import Ochr.Meaning.Steps.ColumnJ

/-!
# Frame locality of a global's meaning: `GlobalsOk.fn` for the global `I` (model6, 2026-11-21; docs/31 D129)

A program's start state with an earlier global, `J`'s (`def J2`, `def J`), needs `Pre`, whose
`GlobalsOk.fn` asks the context's meaning of the global `I` to be the closure the `.fix` clause forms
for it AT EVERY assignment and future, with the clause's type the global's. The context fixes ONE meaning
for `I`; the clause runs `I`'s code under the assignment and future it is given. So the fact needed is
frame locality of closed code: the meaning of a closure with no capture, whose code holds no loan and no
unknown, does not depend on the assignment or the future (`meanV_clo_closed`, from the run's locality
lemmas `meanV_congr` and `meanV_congrA`, both proved), nor, for `I`, on the context's own entry for `I`
(`clo_I_ctx`: `I`'s code reads no global; by computation). Then `J`'s context with `I` meaning that
closure (`fJ`) meets `GlobalsOk.fn` (`fn_clause_I`), assuming three decisions of the table at the empty
scope that the checker's table makes (`I`'s `fix` not a proof; its Π-type at sort 1; its parameter read
`.other`).
-/

namespace Ochr.Meaning.Steps.Form.GlobalsLocal

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open ColumnI ColumnJ

/-- **Frame locality of closed code** (the assignment and the future): a closure with no capture whose
code holds no loan and no unknown means the same at every assignment and future, in a context whose
globals carry no label. -/
theorem meanV_clo_closed (K : RunCtx) (hK : ∀ n, (K.C.global n).2.label = none) (t : Term)
    (hl : ∀ l, (Value.clo [] t []).anyAtom (· == .loan l) = false)
    (ha : ∀ σ, (Value.clo [] t []).anyAtom (· == .abs σ) = false)
    (ρ ρ' : Assignment) (φ φ' : Future) :
    meanV K ρ φ (.plain .err) (.clo [] t []) = meanV K ρ' φ' (.plain .err) (.clo [] t []) := by
  rw [meanV_congr K ρ φ φ' (.plain .err) _ hK (fun l h => by
    simp only [Value.hasLoanM] at h; rw [hl l] at h; cases h)]
  exact meanV_congrA K K.Δ ρ ρ' φ' _ _ (fun σ h => by rw [ha σ] at h; cases h)

/-- `I`'s meaning in `J`'s context: the closure the `.fix` clause forms for `I`, read at any assignment and
future (`fn_I`) and under any entry for `I` (`clo_I_ctx`). -/
noncomputable def fJ (dm : DataModel) (D : Decisions) : Sem :=
  meanV (KJ dm D .err) (fun _ => .err) noFuture (.plain .err) (.clo [] fixI [])

/-- `I`'s closure does not read the context's entry for `I` (its code reads no global). -/
theorem clo_I_ctx (dm : DataModel) (D : Decisions) (f g : Sem) (ρ : Assignment) (φ : Future) :
    meanV (KJ dm D f) ρ φ (.plain .err) (.clo [] fixI []) = meanV (KJ dm D g) ρ φ (.plain .err) (.clo [] fixI []) :=
  rfl

/-- **`I`'s entry in `J`'s context is its closure at every assignment and future.** -/
theorem fn_I (dm : DataModel) (D : Decisions) (ρ : Assignment) (φ : Future) :
    fJ dm D = meanV (KJ dm D (fJ dm D)) ρ φ (.plain .err) (.clo [] fixI []) := by
  show meanV (KJ dm D .err) (fun _ => .err) noFuture (.plain .err) (.clo [] fixI []) = _
  rw [clo_I_ctx dm D .err (fJ dm D)]
  exact meanV_clo_closed _ (fun _ => rfl) fixI (fun _ => rfl) (fun _ => rfl) _ _ _ _

/-- **The `.fix` clause's type for `I` is `I`'s declared type**, `Π(n : Nat). Nat` at sort 1, where the
table makes `I`'s `fix` no proof, its Π-type at sort 1 and its parameter read `.other`. -/
theorem fix_I_ty (dm : DataModel) (D : Decisions) (f : Sem) (ρ : Assignment) (φ : Future)
    (hfl : (D.flags [] fixI).2 = false) (hps : D.piSort [] (.pi [⟨"n"⟩] [.nat] .nat) = 1)
    (hpd : D.paramDecls [] [.nat] = [.other]) (r : Res) (s' : SState)
    (h : run (KJ dm D f) ρ φ (.plain .err) fixI (stateOf 0 []) = some (r, s')) :
    r.2.m = piTyAt dm.read 1 psI outI := by
  unfold run fixI at h
  rw [run_fix_def] at h
  have hsc : scopeOf (stateOf 0 []) = [] := rfl
  have hpd' : (KJ dm D f).D.paramDecls (scopeOf (stateOf 0 [])) [.nat] = [.other] := hpd
  rw [runDoms_nat _ ρ φ _ hpd', codOf_nat] at h
  have hsort : (KJ dm D f).D.piSort (scopeOf (stateOf 0 [])) (.pi [⟨"n"⟩] [.nat] .nat) = 1 := hps
  rw [hsort] at h
  unfold SM.erasedIf at h
  rw [if_neg (show ¬ ((KJ dm D f).D.flags (scopeOf (stateOf 0 [])) (.fix ⟨"I"⟩ [⟨"n"⟩] [.nat] .nat none bodyI)).2 = true by
    show ¬ (D.flags [] fixI).2 = true; rw [hfl]; decide)] at h
  rcases SM.stmtIf_some h with ⟨-, hx⟩ | ⟨-, -, -, r₀, s₀, hx, rfl⟩
  all_goals
    split at hx
    · unfold SM.strictS at hx
      dsimp only at hx
      split at hx
      · simp only [Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, -⟩ := hx
        rfl
      · cases hx
    · cases hx

/-- **`GlobalsOk.fn` for the global `I`, in `J`'s context with `I` meaning `fJ`** (the clause as
`Steps/Statements.GlobalsOk` states it, for every state whose globals are `[I]`, `stJ` and `stJ2`'s).
Assumes 3 decisions of the table at the empty scope (`I`'s `fix` not a proof, its Π-type at sort 1, its
parameter read `.other`); no fact about the checker's run, no model fact. -/
theorem fn_clause_I (dm : DataModel) (D : Decisions) (hfl : (D.flags [] fixI).2 = false)
    (hps : D.piSort [] (.pi [⟨"n"⟩] [.nat] .nat) = 1) (hpd : D.paramDecls [] [.nat] = [.other])
    (st : MState) (hg : st.globals = [gI]) :
    ∀ n g t, st.globals.find? (·.name == n) = some g → g.fn? = some t →
      ((KJ dm D (fJ dm D)).cur.map (·.1)) ≠ some n → ∀ ρ φ,
      ((KJ dm D (fJ dm D)).C.global n).1 = meanV (KJ dm D (fJ dm D)) ρ φ (.plain .err) (.clo [] t []) ∧
      ∀ r s', run (KJ dm D (fJ dm D)) ρ φ (.plain .err) t (stateOf 0 []) = some (r, s') →
        r.2.m = ((KJ dm D (fJ dm D)).C.global n).2.m := by
  intro n g t hf ht _ ρ φ
  rw [hg] at hf
  have hgI : g = gI := by
    simp only [List.find?] at hf
    split at hf
    · exact (Option.some.inj hf).symm
    · cases hf
  subst hgI
  have htI : t = fixI := (Option.some.inj ht).symm
  subst htI
  exact ⟨fn_I dm D ρ φ, fun r s' h => fix_I_ty dm D _ ρ φ hfl hps hpd r s' h⟩

namespace Aux

open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal)
open Ochr.Meaning.Steps.Form.ColumnC.Aux (isOther flagsRun)
open Ochr.Meaning.Steps.Form.CallGuards (stJ)

theorem ok_td_natJ : isOk (ColumnI.Aux.typeDeclRun .nat) (scopeState stJ []) 1000 = true := by decide +kernel
theorem val_td_natJ : isOther (outVal (ColumnI.Aux.typeDeclRun .nat) (scopeState stJ []) 1000) = true := by
  decide +kernel
theorem ok_piSortJ : isOk (ColumnI.Aux.piSortRun (.pi [⟨"n"⟩] [.nat] .nat)) (scopeState stJ []) 1000 = true := by
  decide +kernel
theorem val_piSortJ : outVal (ColumnI.Aux.piSortRun (.pi [⟨"n"⟩] [.nat] .nat)) (scopeState stJ []) 1000 = 1 := by
  decide +kernel
theorem ok_flags_fixJ : isOk (flagsRun fixI) (scopeState stJ []) 1000 = true := by decide +kernel
theorem val_flags_fixJ : outVal (flagsRun fixI) (scopeState stJ []) 1000 = (false, false) := by decide +kernel

end Aux

open Ochr.Meaning.Steps.Form.CallGuards (stJ) in
/-- **The three decisions `fn_clause_I` assumes, at every table aligned with the checker at `J`'s start**
(`stJ`, globals `[I]`): by evaluation of the checker's own decision functions. -/
theorem fixDecJ {D : Decisions} (hd : DecTab D stJ) :
    (D.flags [] fixI).2 = false ∧ D.piSort [] (.pi [⟨"n"⟩] [.nat] .nat) = 1 ∧ D.paramDecls [] [.nat] = [.other] := by
  open Ochr.Meaning.Regress.GenNeutralContent in
  have htd : D.typeDecl [] .nat = .other := by
    rw [hd.typeDecl 100 [] .nat _ 1000 _ (runs_out (ColumnI.Aux.typeDeclRun .nat) _ 1000 Aux.ok_td_natJ)]
    exact Ochr.Meaning.Steps.Form.ColumnC.Aux.isOther_eq Aux.val_td_natJ
  refine ⟨?_, ?_, ?_⟩
  · rw [hd.flags 100 [] fixI _ 1000 _ (Regress.GenNeutralContent.runs_out (Ochr.Meaning.Steps.Form.ColumnC.Aux.flagsRun fixI) _ 1000
      Aux.ok_flags_fixJ), Aux.val_flags_fixJ]
  · rw [hd.piSort 100 [] _ _ 1000 _ (Regress.GenNeutralContent.runs_out (ColumnI.Aux.piSortRun _) _ 1000 Aux.ok_piSortJ),
      Aux.val_piSortJ]
  · simp [Decisions.paramDecls, Decisions.teleDecls, htd]

/-- **`GlobalsOk.fn` for `I` at `J`'s start, at every table aligned with the checker there**: no assumed
fact. -/
theorem fn_clause_I_tab (dm : DataModel) (D : Decisions) (hd : DecTab D Ochr.Meaning.Steps.Form.CallGuards.stJ)
    (st : MState) (hg : st.globals = [gI]) :
    ∀ n g t, st.globals.find? (·.name == n) = some g → g.fn? = some t →
      ((KJ dm D (fJ dm D)).cur.map (·.1)) ≠ some n → ∀ ρ φ,
      ((KJ dm D (fJ dm D)).C.global n).1 = meanV (KJ dm D (fJ dm D)) ρ φ (.plain .err) (.clo [] t []) ∧
      ∀ r s', run (KJ dm D (fJ dm D)) ρ φ (.plain .err) t (stateOf 0 []) = some (r, s') →
        r.2.m = ((KJ dm D (fJ dm D)).C.global n).2.m :=
  let ⟨hfl, hps, hpd⟩ := fixDecJ hd
  fn_clause_I dm D hfl hps hpd st hg

section
variable {dm : DataModel} {D : Decisions} {ρ : Assignment} {φ : Future}

/-- **The call of `I`'s meaning at any number `a`**: `a + 1` at `Nat`, the state as it was (`ColumnJ.callOf_fI`
at `0`, generalised; for `J2`'s call at `1`, docs/31 D128's step (2)). Assumes what `callOf_fI` does: the
checker's typed run of `I`'s body at its generic call and the checker facts `VarNumAInv`, `InvNumA` (the
others are proved: `EvalInv`, `SuccInv`, `InvSteps`, `EvalLow` are the machine lane's). -/
theorem callOf_fI_at (hE : EvalInv) (hS : SuccInv) (hI : InvSteps) (hV : VarNumAInv) (hN : InvNumA) (hlow : EvalLow)
    (hDI : DecTab D stI) {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stI st) (hm : Mode st) (htd : st.tailDecl = none) (hD : DecTab D st')
    (h : Runs (Ochr.eval n true bodyI hint) st bh (v, T?) st') (a : Nat) (s : SState) :
    callOf dm.read (fI dm D ρ φ, .plain (piTyAt dm.read 1 psI outI)) [(.el0 Nat a, .plain TyM.nat)] s =
      some ((.el0 Nat (a + 1), .plain TyM.nat), s) := by
  obtain ⟨o, ho, hr, -⟩ := gIf_run (dm := dm) (ρ := ρ) (φ := φ) hE hS hI hV hN hlow hDI hk hm htd hD h a
  obtain ⟨s', hs'⟩ := closure_apply' dm.read 1 φ psI outI (gIf dm D ρ φ) ⟨Nat.le_refl 1, by omega⟩ rfl
    (fun _ _ => Nat.le_refl 1) (gIf_tot hE hS hI hV hN hlow hDI hk hm htd hD h) [(.el0 Nat a, .plain TyM.nat)] s o
    ⟨rfl, fun i x d hx hd => by
      rcases i with _ | i
      · simp [psI] at hx hd; subst hx; subst hd; exact ⟨a, rfl⟩
      · simp at hx⟩
    (fun i d hd => by rcases i with _ | i <;> simp [psI] at hd; subst hd; exact Nat.le_refl 1)
    trivial ho
  have hss : s' = s := callOf_unlabelled_state _ _ _ _ _ _ hs' (fun a ha => by simp at ha; subst ha; rfl) rfl
  subst hss
  unfold fI
  rw [hs', hr]
  rfl

end

/-- `GlobalsOk.fn` for `I` in `J`'s context also at every table aligned with the checker at `I`'s generic
call (`stI`; `ColumnI.fixDecI` gives the same three decisions). -/
theorem fn_clause_I_tabI (dm : DataModel) (D : Decisions) (hd : DecTab D stI) (st : MState) (hg : st.globals = [gI]) :
    ∀ n g t, st.globals.find? (·.name == n) = some g → g.fn? = some t →
      ((KJ dm D (fJ dm D)).cur.map (·.1)) ≠ some n → ∀ ρ φ,
      ((KJ dm D (fJ dm D)).C.global n).1 = meanV (KJ dm D (fJ dm D)) ρ φ (.plain .err) (.clo [] t []) ∧
      ∀ r s', run (KJ dm D (fJ dm D)) ρ φ (.plain .err) t (stateOf 0 []) = some (r, s') →
        r.2.m = ((KJ dm D (fJ dm D)).C.global n).2.m := by
  obtain ⟨hd1, -, hps, hfl⟩ := fixDecI hd
  exact fn_clause_I dm D (by rw [hfl]) hps (by simp [Decisions.paramDecls, Decisions.teleDecls, hd1]) st hg

section
variable {dm : DataModel} {D : Decisions} {ρ : Assignment} {φ : Future}

open Classical

open Ochr.Meaning.Strict.Witness (fixClo fixTy run_fix_of_mem) in
/-- **`fJ` is `fI`** at a table aligned with the checker at `I`'s generic call (`stI`), where the checker
ran `I`'s body: the closure `J`'s context gives `I` is the one column `I`'s membership is about, at every
assignment and future. So `GlobalsOk.mem` for `I` in `KJ dm D (fJ dm D)` is `ColumnJ.fI_mem` at such a
table. Assumes what `fI_mem` does (checker facts `VarNumAInv`, `InvNumA`; the others are the machine
lane's). -/
theorem fJ_eq_fI (hE : EvalInv) (hS : SuccInv) (hI : InvSteps) (hV : VarNumAInv) (hN : InvNumA) (hlow : EvalLow)
    (hDI : DecTab D stI) {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stI st) (hm : Mode st) (htd : st.tailDecl = none) (hD : DecTab D st')
    (h : Runs (Ochr.eval n true bodyI hint) st bh (v, T?) st') :
    fJ dm D = fI dm D ρ φ := by
  obtain ⟨hd1, -, hps, hfl⟩ := fixDecI hDI
  have e1 : fJ dm D = meanV (KJ dm D .err) ρ φ (.plain .err) (.clo [] fixI []) :=
    meanV_clo_closed _ (fun _ => rfl) fixI (fun _ => rfl) (fun _ => rfl) _ _ _ _
  have hfix : fixClo (KJ dm D .err) ρ φ (stateOf 0 []) [⟨"n"⟩] [.nat] .nat none bodyI = fI dm D ρ φ := by
    rw [← fixClo_I (dm := dm) (ρ := ρ) (φ := φ) hDI]; rfl
  have hpd : (KJ dm D .err).D.paramDecls (scopeOf (stateOf 0 [])) [.nat] = [.other] := by
    show D.paramDecls [] [.nat] = [.other]
    simp [Decisions.paramDecls, Decisions.teleDecls, hd1]
  have hty : fixTy (KJ dm D .err) ρ φ (stateOf 0 []) [⟨"n"⟩] [.nat] .nat = piTyAt dm.read 1 psI outI := by
    unfold fixTy Strict.Witness.fixSort
    rw [runDoms_nat _ ρ φ _ hpd, codOf_nat]
    show piTyAt dm.read (D.piSort [] _) psI outI = _
    rw [hps]
  have hrun := run_fix_of_mem (K := KJ dm D .err) (ρ := ρ) (φ := φ) false (.plain .err) ⟨"I"⟩ [⟨"n"⟩] [.nat] .nat none
    bodyI (stateOf 0 []) hfl (by show FoldOk _ _ [] _; trivial)
    (by rw [hfix, hty]; exact fI_mem hE hS hI hV hN hlow hDI hk hm htd hD h)
  rw [e1]
  show (if CapsOk dm.read [] [] then
      (match runT (KJ dm D .err) ρ φ false (.plain .err) fixI (stateOf 0 (capsState [] [])) with
        | some ((w, _), _) => w
        | none => .err) else .err) = _
  rw [if_pos (show CapsOk dm.read [] [] from trivial)]
  unfold fixI
  rw [show capsState [] [] = [] from rfl, hrun]
  exact hfix

/-- **`GlobalsOk.mem`'s content for `I` in `J`'s context**: `fJ` is a member of `Π(n : Nat). Nat`, at a
table aligned with the checker at `stI`, from the checker's run of `I`'s body (`fJ_eq_fI`, `fI_mem`). -/
theorem fJ_mem (hE : EvalInv) (hS : SuccInv) (hI : InvSteps) (hV : VarNumAInv) (hN : InvNumA) (hlow : EvalLow)
    (hDI : DecTab D stI) {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stI st) (hm : Mode st) (htd : st.tailDecl = none) (hD : DecTab D st')
    (h : Runs (Ochr.eval n true bodyI hint) st bh (v, T?) st') :
    fJ dm D ∈ₛ[dm.read] piTyAt dm.read 1 psI outI := by
  rw [fJ_eq_fI (ρ := fun _ => .err) (φ := noFuture) hE hS hI hV hN hlow hDI hk hm htd hD h]
  exact fI_mem hE hS hI hV hN hlow hDI hk hm htd hD h

end

end Ochr.Meaning.Steps.Form.GlobalsLocal
