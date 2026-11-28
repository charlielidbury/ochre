import Ochr.Meaning.Conv.Hyps
import Ochr.Meaning.DataLib.Universal

/-!
# (H7) `FieldTyIdx`, proved (conv1, 2026-11-28)

The old attempt's data-layer obligation "a field's type reads, of the earlier fields, only the index
fields" (D64) holds of every data model on the proof line: its signature is the universal one, whose
shape reads the earlier fields only through `projIdx` (`DataLib.uShape_idx`).
-/

namespace Ochr.Meaning.Conv
open Ochr Ochr.Meaning Ochr.Meaning.DataLib

theorem projIdx_congr (d : IndDecl) (c : Nat) (e e' : List Sem) (hl : e.length = e'.length)
    (h : ∀ k ∈ d.indexFields c, k < e.length → e[k]? = e'[k]?) :
    projIdx d c (e.map Sem.small) = projIdx d c (e'.map Sem.small) := by
  unfold projIdx
  apply List.ext_getElem
  · simp [hl]
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_zipIdx]
    split
    · rename_i hk
      have hk' : k < e.length := by simpa using h1
      have := h k (by simpa using hk) hk'
      rw [List.getElem?_eq_getElem hk', List.getElem?_eq_getElem (hl ▸ hk')] at this
      simp only [Option.some.injEq] at this
      rw [this]
    · rfl

/-- **(H7) PROVED**: a field's type reads only the index fields. -/
theorem fieldTyIdx (K : RunCtx) : FieldTyIdx K := by
  intro d r c j e e' hl h
  show K.dm.shapeTy (uShape d r c j (e.map Sem.small)) = K.dm.shapeTy (uShape d r c j (e'.map Sem.small))
  rw [uShape_idx d r c j _ _ (projIdx_congr d c e e' hl h)]

end Ochr.Meaning.Conv
