import Ochr.Meaning.Steps.BlockQ
import Ochr.Meaning.Steps.CallJ2Fn

/-!
# The column `Q`: the reference's run of the body, and what the closed-off block means (lead18, 2026-11-21; docs/31 D137)

The reference does not close anything off. `runT`'s `.succ` clause runs the match NOT in tail position: [Access] for
the tag of `n` (the number `ρ σ0`), then [Entry] (`matchEntry`: the block's captures, read as a decision,
`Decisions.blockCaps`, each accessed; here `n`, by move, and the access changes nothing), then the ONE arm the tag
selects, then the join's drop of `n` (`joinDrop`), exactly `P`'s run but for the entry (`ColumnP.runP` is the tail
case). The result: on `0`, `0`; on `a + 1`, `a`; in both, `n` moved.

The checker's value is the sealed program `⌈anonQ(σ0)⌉`. Its meaning (`meanV`'s `.sealed` clause) is the run of the
call `anonQ(σ0)` from the empty state: the head is the closure value `anonQ`, whose meaning is the closure the `.fix`
clause forms of `anonFix` (no capture; a member of `Π(n : Nat). Nat` because its body runs to a number at every number);
the argument is `ρ σ0`; the call runs the body `matchQ` IN TAIL POSITION in the closure's frame `[{}, {_, n ↦ ρ σ0}]`
(`FrameJ2.closureJ2`, the frame `I`'s closure runs in: the same parameter, the same stage-0 `self`), which is `P`'s
run (`ColumnP.runP`). So the block's meaning and the reference's direct run are the same arm of the same code on the
same number: `mean_vQ` and `runMatchQ` give the same result at every assignment.

The decisions read are got by kernel evaluation of the checker's procedures at `stQ` (`parDecQ`); the block's captures
are not in `DecTab` (they read values: `Decisions.blockCaps`, `DecAligned.blockCaps`) and are taken as the decision
`D.blockCaps RIu [] matchQ = ([n], [(n, move)])`, which `ckBlockCaps` computes at `stQ` (`Aux.val_bc`).
-/

namespace Ochr.Meaning.Steps.Form.ColumnQ

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Strict.Witness
open Ochr.Meaning.Steps.Form.ColumnI (piNat nB psI outI selfTy selfSem)
open Ochr.Meaning.Steps.Form.ColumnP (RIu pn0 ParDecP RefJ RefP dropN setN0 nBot)

/-! ## The decisions -/

/-- The domain the block's code declares, as a Π-term. -/
def anonPi : Term := .pi [⟨"n"⟩] [.val .tNat] (.val .tNat)

/-- **The decisions the reference's run of `Q`'s body and the meaning of its block read**: `P`'s (`ParDecP`: the match
and its arm in the scope `RIu`, which is also the block's body's scope); the body `S(…)` neither a statement nor a proof;
the block's captures (`n` by move; the place `movedPlace` is asked of, `n`); and, at the empty scope where the sealed
program runs, its call and its `fix` neither a statement nor a proof, its parameter and codomain read `.other`, its sort
`1`. -/
structure ParDecQ (D : Decisions) : Prop where
  p : ParDecP D RIu
  flBody : D.flags RIu bodyQ = (false, false)
  caps : D.blockCaps RIu [] matchQ = ([.var 0], [(.var 0, 2)])
  flSeal : D.flags [] sealQ = (false, false)
  flFix : D.flags [] anonFix = (false, false)
  td0 : D.typeDecl [] (.val .tNat) = .other
  td1 : D.typeDecl [.other] (.val .tNat) = .other
  srt : D.piSort [] anonPi = 1

namespace Aux

open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal runs_out)
open Ochr.Meaning.Steps.Form.ColumnC.Aux (flagsRun isOther isOther_eq)
open Ochr.Meaning.Steps.Form.ColumnI.Aux (typeDeclRun piSortRun)
open Ochr.Meaning.Steps.Form.ColumnP.Aux (pdRun jmRun cpRun)

theorem ok_fl_body : isOk (flagsRun bodyQ) (scopeState stQ RIu) 1000 = true := by decide +kernel
theorem val_fl_body : outVal (flagsRun bodyQ) (scopeState stQ RIu) 1000 = (false, false) := by decide +kernel
theorem ok_fl_m : isOk (flagsRun matchQ) (scopeState stQ RIu) 1000 = true := by decide +kernel
theorem val_fl_m : outVal (flagsRun matchQ) (scopeState stQ RIu) 1000 = (false, false) := by decide +kernel
theorem ok_fl_n0 : isOk (flagsRun (.place pn0)) (scopeState stQ RIu) 1000 = true := by decide +kernel
theorem val_fl_n0 : outVal (flagsRun (.place pn0)) (scopeState stQ RIu) 1000 = (false, false) := by decide +kernel
theorem ok_pd_n0 : isOk (pdRun pn0) (scopeState stQ RIu) 1000 = true := by decide +kernel
theorem val_pd_n0 : isOther (outVal (pdRun pn0) (scopeState stQ RIu) 1000) = true := by decide +kernel
theorem ok_pd_n : isOk (pdRun (.var 0)) (scopeState stQ RIu) 1000 = true := by decide +kernel
theorem val_pd_n : isOther (outVal (pdRun (.var 0)) (scopeState stQ RIu) 1000) = true := by decide +kernel
theorem ok_cp : isOk cpRun stQ 1000 = true := by decide +kernel
theorem val_cp : outVal cpRun stQ 1000 = false := by decide +kernel
theorem ok_jm : isOk (jmRun matchQ) (scopeState stQ RIu) 1000 = true := by decide +kernel
theorem val_jm0 : (match outVal (jmRun matchQ) (scopeState stQ RIu) 1000 with
    | [.var 0] => true
    | _ => false) = true := by decide +kernel
theorem ok_fl_seal : isOk (flagsRun sealQ) (scopeState stQ []) 1000 = true := by decide +kernel
theorem val_fl_seal : outVal (flagsRun sealQ) (scopeState stQ []) 1000 = (false, false) := by decide +kernel
theorem ok_fl_fix : isOk (flagsRun anonFix) (scopeState stQ []) 1000 = true := by decide +kernel
theorem val_fl_fix : outVal (flagsRun anonFix) (scopeState stQ []) 1000 = (false, false) := by decide +kernel
theorem ok_td (sc : List DeclInfo) (hsc : sc = [] ∨ sc = [.other]) :
    isOk (typeDeclRun (.val .tNat)) (scopeState stQ sc) 1000 = true := by
  rcases hsc with rfl | rfl <;> decide +kernel
theorem val_td (sc : List DeclInfo) (hsc : sc = [] ∨ sc = [.other]) :
    isOther (outVal (typeDeclRun (.val .tNat)) (scopeState stQ sc) 1000) = true := by
  rcases hsc with rfl | rfl <;> decide +kernel
theorem ok_sort : isOk (piSortRun anonPi) (scopeState stQ []) 1000 = true := by decide +kernel
theorem val_sort : outVal (piSortRun anonPi) (scopeState stQ []) 1000 = 1 := by decide +kernel
theorem val_jm : outVal (jmRun matchQ) (scopeState stQ RIu) 1000 = [.var 0] := by
  have h := val_jm0
  revert h
  generalize outVal (jmRun matchQ) (scopeState stQ RIu) 1000 = x
  intro h
  split at h
  · rfl
  · cases h

end Aux

/-- **`ParDecQ` at every table aligned with the checker at `stQ`** whose block captures are the checker's there (the one
block of the body is entered at a state with `stQ`'s kernel: `DecAligned.blockCaps` at that state). -/
theorem parDecQ {D : Decisions} (hd : DecTab D stQ)
    (hbc : D.blockCaps RIu [] matchQ = ([.var 0], [(.var 0, 2)])) : ParDecQ D := by
  open Ochr.Meaning.Regress.GenNeutralContent in
  have hpd : D.placeDecl RIu pn0 = .other :=
    (hd.placeDecl 100 RIu pn0 _ 1000 _ (runs_out (ColumnP.Aux.pdRun pn0) _ 1000 Aux.ok_pd_n0)).trans
      (ColumnC.Aux.isOther_eq Aux.val_pd_n0)
  have hpd0 : D.placeDecl RIu (.var 0) = .other :=
    (hd.placeDecl 100 RIu (.var 0) _ 1000 _ (runs_out (ColumnP.Aux.pdRun (.var 0)) _ 1000 Aux.ok_pd_n)).trans
      (ColumnC.Aux.isOther_eq Aux.val_pd_n)
  have hcp : D.copy .other = false := by
    rw [hd.copy 100 .other _ 1000 _ (runs_out ColumnP.Aux.cpRun _ 1000 Aux.ok_cp), Aux.val_cp]
  have hfl : ∀ sc t, isOk (ColumnC.Aux.flagsRun t) (scopeState stQ sc) 1000 = true →
      D.flags sc t = outVal (ColumnC.Aux.flagsRun t) (scopeState stQ sc) 1000 := fun sc t hok =>
    hd.flags 100 sc t _ 1000 _ (runs_out (ColumnC.Aux.flagsRun t) _ 1000 hok)
  have htd : ∀ sc, (sc = [] ∨ sc = [.other]) → D.typeDecl sc (.val .tNat) = .other := fun sc hsc => by
    rw [hd.typeDecl 100 sc _ _ 1000 _ (runs_out (ColumnI.Aux.typeDeclRun _) _ 1000 (Aux.ok_td sc hsc))]
    exact ColumnC.Aux.isOther_eq (Aux.val_td sc hsc)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, hbc, ?_, ?_, htd [] (.inl rfl), htd [.other] (.inr rfl), ?_⟩
  · rw [hfl _ _ Aux.ok_fl_m, Aux.val_fl_m]
  · rw [hfl _ _ Aux.ok_fl_n0, Aux.val_fl_n0]
  · rw [hpd]; exact hcp
  · rw [hpd0]; exact hcp
  · rw [hd.joinMoves 100 RIu [] matchQ _ 1000 _ (runs_out (ColumnP.Aux.jmRun matchQ) _ 1000 Aux.ok_jm), Aux.val_jm]
  · rw [hfl _ _ Aux.ok_fl_body, Aux.val_fl_body]
  · rw [hfl _ _ Aux.ok_fl_seal, Aux.val_fl_seal]
  · rw [hfl _ _ Aux.ok_fl_fix, Aux.val_fl_fix]
  · rw [hd.piSort 100 [] _ _ 1000 _ (runs_out (ColumnI.Aux.piSortRun _) _ 1000 Aux.ok_sort), Aux.val_sort]

end Ochr.Meaning.Steps.Form.ColumnQ
