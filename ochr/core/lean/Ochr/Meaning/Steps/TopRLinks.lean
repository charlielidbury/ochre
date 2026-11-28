import Ochr.Meaning.Steps.TopRCheck

/-!
# The acceptance test at `R`: the function's eight links (`FixG`; lead46, docs/31 D259 on)

`FixG` at `R`'s program, every link proved, the witness the inversion of `R`'s check (`R_check_inv`). One clause is
assumed: that `checkFix`'s continuation keeps the tables' invariant at every value and type (`KeepsTab`, a clause of
`FixCheckAt` that `TailAt` asks of every continuation; a whole-machine fact, owed by the machine lane since D250, not a
fact about `R`).
-/

namespace Ochr.Meaning.Steps.Form.Top.RT

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master
open Ochr.Consistency Ochr.Surface Ochr.Meaning.Assembly
open Ochr.Meaning.Steps.Form.ColumnR

/-- **`checkFix`'s continuation keeps the tables' invariant** (MACHINE; the clause of `FixCheckAt` that `TailAt` asks of
every continuation, `KeepsTab`; a whole-machine fact, owed by the machine lane since docs/31 D250: `fixCont` runs [Return],
the frame's pop and the conversion, which reach the whole machine). At `R`'s name. -/
def KeepsTabFixR : Prop := ∀ (n : Nat) (v T : Value), KeepsTab (fixCont n "R" none v T)

/-- **`FixG` at `R`'s program** (PROVED but for `KeepsTabFixR`): the witness of `R`'s check inverted (`R_check_inv`), and
the eight links: `FixCheckAt` (the inversion), `FixFitsAt`, `FixStartAt` (`fixStart_R`), `BodyCongrAt`, `FixLeafAt`,
`FixPartsAt`, `FixClosedAt`, `FixFlagAt`. -/
theorem fixG_R (hkt : KeepsTabFixR) (dm : DataModel) {items : List Item} (hr : ResolvesTo pq F items) :
    FixG dm (chainDecisions F) (indsOf {} F items) F items := by
  intro P d st' hin _ hrun _ hfaith hcov hΓP _
  obtain ⟨rfl, hPg, hPm⟩ := atStage_R hr hin
  have hrun' := hrun
  rw [hPg] at hrun'
  obtain ⟨n, bh, u, st₁, hct, hgr, hg', hi'⟩ := R_check_inv hrun'
  have hg2 : st'.globals = gE false :: [] := hg'
  refine ⟨⟨n, st0R P.inds u, st₁, bh, false, none⟩, ?_, fixFits_R P st' hg2, ?_, bodyCongr_R _ P st',
    fixLeaf_R P st' hg2 _, fixParts_R P st' hg2, fixClosed_R, fixFlag_R P st' hg2⟩
  · refine ⟨⟨rfl, rfl, rfl⟩, rfl, (by show 0 < 2; omega), rfl, by rw [hPg]; rfl, hct, fun v T => grows_fixCont n "R" none v T,
      fun v T => hkt n v T, by rw [hg', hPg]; rfl, by rw [hg']; rfl⟩
  · exact fixStart_R hr hin hPg hPm hg' hi' hfaith hcov hΓP _ u rfl hgr

end Ochr.Meaning.Steps.Form.Top.RT
