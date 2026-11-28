import Ochr.Meaning.Conv.Hyps

/-!
# (H5) the library's `True` and `False`, proved (conv1, 2026-11-28)

Two of `LibOk`'s three fields hold of every data model on the proof line, given only that the
declarations named `True` and `False` are the `Prelude`'s (a `Prop`-sorted declaration without
parameters, with one constructor without fields; with no constructor): a `Prop`-sorted declaration
means `prop (Nonempty car)` (`DataModel.tyR`), and the least set has a member exactly when a
constructor's fields can be filled (`DataLib.mem_iff`). The third field, `And`, needs the record's
field shapes at the parameters (the data model's faithfulness, `RecordsFaithful`), and stays read.
-/

namespace Ochr.Meaning.Conv
open Ochr Ochr.Meaning Ochr.Meaning.DataModel

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem meanV_tInd_nil {n : String} {d : IndDecl} (hd : K.Γ.find? (·.name == n) = some d) (hint : TyS) :
    meanV K ρ φ hint (.tInd n []) = .ty (K.dm.tyM d []) := by
  simp only [meanV, hd]
  have e : meanParams K ρ φ d 0 [] [] = [] := by simp [meanParams]
  rw [e, if_pos (paramsOk_nil K.dm d)]

/-- **`LibOk.tru`**: the `Prelude`'s `True` means truth. -/
theorem lib_true {d : IndDecl} (hd : K.Γ.find? (·.name == "True") = some d) (hs : d.sort = 0)
    (hc : 0 < d.ctors.length) (ha : DataLib.arity d 0 = 0) (hint : TyS) :
    meanV K ρ φ hint vTrue = .ty (TyM.prop True) := by
  rw [show vTrue = .tInd "True" [] from rfl, meanV_tInd_nil hd]
  simp only [DataModel.tyM, DataModel.tyR, hs, beq_self_eq_true, if_true]
  congr 2
  refine propext ⟨fun _ => trivial, fun _ => ?_⟩
  have hm : K.dm.Mem d (K.dm.recOf d []) (.dat d.name (K.dm.recOf d []) 0 []) :=
    (DataLib.mem_iff K.dm.sig d _ _).2 ⟨⟨0, hc⟩, [], rfl, by simp only [ha]; rfl⟩
  obtain ⟨x, -⟩ := (K.dm.mem_iff_meanC d _ _).1 hm
  exact ⟨x⟩

/-- **`LibOk.fls`**: the `Prelude`'s `False` means falsity. -/
theorem lib_false {d : IndDecl} (hd : K.Γ.find? (·.name == "False") = some d) (hs : d.sort = 0)
    (hc : d.ctors = []) (hint : TyS) :
    meanV K ρ φ hint vFalse = .ty (TyM.prop False) := by
  rw [show vFalse = .tInd "False" [] from rfl, meanV_tInd_nil hd]
  simp only [DataModel.tyM, DataModel.tyR, hs, beq_self_eq_true, if_true]
  congr 2
  refine propext ⟨fun ⟨x⟩ => ?_, False.elim⟩
  have hm : K.dm.Mem d (K.dm.recOf d []) (K.dm.meanC x) := (K.dm.mem_iff_meanC d _ _).2 ⟨x, rfl⟩
  obtain ⟨⟨c, hc'⟩, -, -, -⟩ := (DataLib.mem_iff K.dm.sig d _ _).1 hm
  rw [hc] at hc'
  exact absurd hc' (Nat.not_lt_zero _)

end

end Ochr.Meaning.Conv
