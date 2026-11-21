import Ochr.Meaning.Steps.FragSim
import Ochr.Meaning.Steps.ColumnBFF
import Ochr.Meaning.Steps.Machine.ReadInv
import Ochr.Meaning.Steps.Machine.PlaceLocalFF

/-!
# The fragment's run theorem (lead12)

`frag_run`: for every closed term of the fragment (`FTy [] t A`), every successful typed run of the
checker's `eval` from the constant-body start state (`ColumnC.stC`, one empty frame) makes the strict
run of the term succeed from the reference state, with a member of its type at the type the checker
gives (a borrow is typed by its content's type, `FT.tyM`). It is `frag_sim` at the start state, whose
hypotheses there are kernel-checked (`pre_stC`, `rel_stC`, `sgood_stC`, `fundCtx_KC`, `fst_stC`).

`frag_run_ff`: the same at the checker's fuel-free decision table, with every fact the machine lane
has proved discharged (`FragOpen.facts`): it assumes exactly the facts still to prove (`FragOpen`).
`B`'s and `C`'s bodies are fragment terms (`fty_bodyB`, `fty_bodyC`).
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open ColumnC (stC KC CC pre_stC rel_stC sgood_stC fundCtx_KC topReadings_stC bodyC)
open ColumnB (bodyB)

/-- The constant-body start state is a fragment state with no variables. -/
theorem fst_stC : FSt [] stC := by
  have hA : allPos stC.env = [] := ColumnC.Aux.allPos_stC
  refine ⟨fun q hq => ?_, fun f i hq => ?_, fun q _ _ hq => ?_, fun q _ _ _ _ hq => ?_, fun q _ hq => ?_,
    fun q _ _ hq => ?_, fun i A hi => ?_, fun f j _ _ _ _ hq => ?_, fun f j b l hb _ => ?_, by show 0 < 1; omega⟩ <;>
    (try rw [hA] at hq) <;> (try exact absurd hq List.not_mem_nil)
  · cases hi
  · exfalso
    rcases f with _ | f
    · simp [stC] at hb
    · simp [stC] at hb

/-- How the reference types a value of a fragment type: a number, `()`, and a borrow by its content's
type (`Nat`), labelled. -/
def FT.tyM : FT → TyM
  | .nat => .nat
  | .unit => .unit
  | .ref => .nat

/-- **The fragment's run theorem**: for every closed fragment term `t : A`, every successful typed run
of the checker's `eval` on it from a state with the constant-body start state's kernel (in mode, no
reading handed down) makes the strict run of `t` from the reference start state succeed, with a
member of its type, the type the checker gives (`StrAgree`: `FT.tyM`). Assumes the facts of
`FragFacts` (about the checker alone and its table); every other hypothesis of `frag_sim` is
discharged here. -/
theorem frag_run {D : Decisions} (hf : FragFacts D) (dm : DataModel) (ρ : Assignment) (φ : Future) {t : Term}
    {A : FT} (hty : FTy [] t A) {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value}
    {T? : Option Value} (hk : Kern stC st) (hm : Mode st) (htd : st.tailDecl = none) (hD : DecTab D st')
    (h : Runs (Ochr.eval n true t hint) st bh (v, T?) st') :
    ∃ r s', runT (KC dm D) ρ φ st.tailNext (hintM (KC dm D) ρ hint) t (SM' (KC dm D) ρ stC) = some (r, s') ∧
      T? = some A.ty ∧ r.2.m = A.tyM ∧ r.1 ∈ₛ[dm.read] r.2.m := by
  have hP : FSt [] st := fst_stC.kern hk
  obtain ⟨hT, hv, -⟩ := hf.run [] t A n hint st st' bh v T? hty hP hm (.inl htd) hD h
  have hfl : D.flags (scopeOf (SM' (KC dm D) ρ stC)) t = (false, false) := by
    rw [scopeOf_sstate']; exact (hf.dec [] t A stC hty fst_stC).1
  obtain ⟨ρ', Δ', π', r, s', -, hx, hmean, hagree, -, -, -⟩ :=
    frag_sim (K := KC dm D) (φ := φ) hf (fundCtx_KC dm D) [] t A hty n (KC dm D).Δ ρ
      st st' true hint v T? (SM' (KC dm D) ρ stC) id hP rfl hm (.inl htd) ((pre_stC dm D ρ).of_kern hk)
      ((rel_stC dm D ρ φ).of_kern hk) (sgood_stC dm D ρ φ) (hty.valsOk _) (fun σ hσ => hty.absBelow _ σ hσ)
      hty.noHole hfl (fun e => by cases e) hD bh h
  have hm2 : r.2.m = A.tyM := by rw [← hagree A.ty hT]; cases A <;> rfl
  refine ⟨r, s', hx, hT, hm2, ?_⟩
  rw [hm2, ← hmean, ← meanV_eq_mean]
  cases A with
  | nat => obtain ⟨k, hk⟩ := (hv : v.Num).vmean; rw [hk]; exact ⟨k, rfl⟩
  | unit => rw [show v = .unit from hv]; first | exact ⟨(), rfl⟩ | rfl | trivial
  | ref =>
    obtain ⟨l, c, rfl, hc⟩ := hv
    obtain ⟨k, hk⟩ := hc.vmean
    show Value.mean _ _ _ _ _ _ c ∈ₛ[dm.read] TyM.nat
    rw [hk]; exact ⟨k, rfl⟩

/-! ## At the checker's fuel-free table, with the machine lane's theorems -/

/-- **The facts of `FragFacts` not yet proved** (18; the machine lane's and the decisions' lane's queue,
`OPEN.md`). -/
structure FragOpen (D : Decisions) : Prop where
  run : FragRun D
  dec : FragDec D
  low : EvalLow
  varLent : VarLentInv
  varBot : VarBotInv
  dropBor : DropBorrowInv
  dropLent : DropLentFail
  borLent : BorrowLentInv
  borBot : BorrowBotInv
  seqBor : SeqBorInv
  asgVar : AssignVarInv
  asgDeref : AssignDerefInvF
  invEnd : InvEnd
  bindUnit : InvBindUnit
  popUnit : InvPopUnit
  lendG : InvLendG
  popBot : InvPopBot
  setBotNum : InvSetBotNum

/-- **`FragFacts` from the facts not yet proved**: the other eleven are the machine lane's theorems
(`EvalInv`, `ZeroInv`, `SuccInv`, `VarNumInv`, `InvSteps`, `LetInv`, `DropNoopInv`, `SeqInv`,
`BorrowNumInv`) and the table's (`PlaceLocal`, the empty invalidation). -/
theorem FragOpen.facts {D : Decisions} (ho : FragOpen D) (hPL : PlaceLocal D)
    (hNI : ∀ sc p, D.invalidated sc p = []) : FragFacts D :=
  ⟨Machine.evalInvR, Machine.zeroInv, succInv, Machine.varNumInv, ho.varLent, ho.varBot, ho.invEnd, Machine.invSteps,
    ho.low, ho.dec, ho.run, hPL, letInv, Machine.dropNoopInv, ho.dropBor, ho.dropLent, ho.popUnit, ho.bindUnit,
    Machine.seqInv, Machine.borrowNumInv, ho.borLent, ho.borBot, ho.lendG, hNI, ho.seqBor, ho.popBot, ho.asgVar,
    ho.setBotNum, ho.asgDeref⟩

/-- **The fragment's run theorem at the checker's fuel-free table**: `frag_run` with the table's facts
(`Machine.placeLocal_ff`, the empty invalidation, `decTab_ff`) and the machine lane's theorems
discharged; it assumes exactly the facts not yet proved (`FragOpen`). -/
theorem frag_run_ff (dm : DataModel) (ρ : Assignment) (φ : Future) {t : Term} {A : FT} (hty : FTy [] t A) {n : Nat}
    {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stC st) (hm : Mode st) (htd : st.tailDecl = none)
    (h : Runs (Ochr.eval n true t hint) st bh (v, T?) st') (ho : FragOpen (checkerDecisionsFF st')) :
    ∃ r s', runT (KC dm (checkerDecisionsFF st')) ρ φ st.tailNext (hintM (KC dm (checkerDecisionsFF st')) ρ hint) t
        (SM' (KC dm (checkerDecisionsFF st')) ρ stC) = some (r, s') ∧
      T? = some A.ty ∧ r.2.m = A.tyM ∧ r.1 ∈ₛ[dm.read] r.2.m :=
  frag_run (ho.facts (Machine.placeLocal_ff st' _) (fun _ _ => rfl)) dm ρ φ hty hk hm htd
    (decTab_ff st' _ (fun _ => Machine.decide_fuel_agree' _) (Machine.decide_fuel_agree' st')) h

/-! ## The two columns' programs are fragment terms -/

/-- `C`'s body, `let x = S(Z); x`, is a fragment term of type `Nat`. -/
theorem fty_bodyC : FTy [] bodyC .nat :=
  .letIn [] _ _ _ .nat .nat (.succ [] _ (.zero [])) (.var [.nat] 0 rfl)

/-- `B`'s body, `let x = S(Z); let y = &x; *y := Z; x`, is a fragment term of type `Nat`. -/
theorem fty_bodyB : FTy [] bodyB .nat :=
  .letIn [] _ _ _ .nat .nat (.succ [] _ (.zero [])) (.letIn [.nat] _ _ _ .ref .nat (.bor [.nat] 0 rfl)
    (.seq [.ref, .nat] _ _ .unit .nat (.asgD [.ref, .nat] 0 _ rfl (.zero _)) (.var [.ref, .nat] 1 rfl)))

/-- `B` as an instance of the fragment's run theorem (`column_B_free` proves more of `B`, its value
`0`, with no assumed fact; this is the same program under the fragment's assumptions). -/
theorem bodyB_frag_run_ff (dm : DataModel) (ρ : Assignment) (φ : Future) {n : Nat} {st st' : MState} {bh : Nat}
    {v : Value} {T? : Option Value} (hk : Kern stC st) (hm : Mode st) (htd : st.tailDecl = none)
    (h : Runs (Ochr.eval n true bodyB (some .tNat)) st bh (v, T?) st') (ho : FragOpen (checkerDecisionsFF st')) :
    ∃ r s', runT (KC dm (checkerDecisionsFF st')) ρ φ st.tailNext
        (hintM (KC dm (checkerDecisionsFF st')) ρ (some .tNat)) bodyB (SM' (KC dm (checkerDecisionsFF st')) ρ stC) =
        some (r, s') ∧ r.2.m = TyM.nat ∧ r.1 ∈ₛ[dm.read] TyM.nat := by
  obtain ⟨r, s', hx, -, hm2, hmem⟩ := frag_run_ff dm ρ φ fty_bodyB hk hm htd h ho
  rw [hm2] at hmem
  exact ⟨r, s', hx, hm2, hmem⟩

end Ochr.Meaning.Steps.Form
