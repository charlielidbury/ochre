import Ochr.Meaning.Steps.Machine.FragFacts
import Ochr.Meaning.Steps.Machine.FragInv
import Ochr.Meaning.Steps.Machine.FragRuns
import Ochr.Meaning.Steps.Machine.FragEndRuns
import Ochr.Meaning.Steps.Machine.FragEnds
import Ochr.Meaning.Steps.Machine.FragAssign
import Ochr.Meaning.Steps.Machine.FragDecs
import Ochr.Meaning.Steps.Machine.FragRunProof

/-!
# The fragment's run theorem with no assumed fact (machine lane, machine7)

`frag_run_free`: `FragTop.frag_run_ff` (the fragment's run theorem at the checker's fuel-free decision
table) with its assumption bundle `FragOpen` (the eighteen facts about the checker it was stated over)
built from the machine lane's theorems: no assumed fact remains.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope
open Ochr.Meaning.Steps.Form
open ColumnC (stC KC)

/-- **The eighteen facts `frag_run_ff` assumed, at the fuel-free table, all proved.** -/
theorem fragOpen_ff (st' : MState) : FragOpen (checkerDecisionsFF st') :=
  ⟨fragRun (fragDec st' _), fragDec st' _, evalLow, varLentInv, varBotInv, dropBorrowInv, dropLentFail, borrowLentInv,
    borrowBotInv, seqBorInv, assignVarInv, assignDerefInvF, invEnd, invBindUnit, invPopUnit, invLendG, invPopBot,
    invSetBotNum⟩

/-- **The fragment's run theorem at the checker's fuel-free table, with no assumed fact**: a typed run
of a closed fragment term from the checker's start state (up to its kernel) has a reference run, from
the start state's meaning, whose type is the term's and whose value is in that type's meaning. -/
theorem frag_run_free (dm : DataModel) (ρ : Assignment) (φ : Future) {t : Term} {A : Form.FT} (hty : FTy [] t A) {n : Nat}
    {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stC st) (hm : Mode st) (htd : st.tailDecl = none)
    (h : Runs (Ochr.eval n true t hint) st bh (v, T?) st') :
    ∃ r s', runT (KC dm (checkerDecisionsFF st')) ρ φ st.tailNext (hintM (KC dm (checkerDecisionsFF st')) ρ hint) t
        (SM' (KC dm (checkerDecisionsFF st')) ρ stC) = some (r, s') ∧
      T? = some A.ty ∧ r.2.m = A.tyM ∧ r.1 ∈ₛ[dm.read] r.2.m :=
  frag_run_ff dm ρ φ hty hk hm htd h (fragOpen_ff st')

end Ochr.Meaning.Steps.Machine
