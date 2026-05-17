import Pss.Mpss.Reductions

/-! # `Pss.Mpss.SubRed` — re-export shim for MPSS subtyping reduction

The MPSS subtype reduction `MSubRed` and its reflexive-transitive closure
`MSubRedStar` are defined in `Pss.Mpss.Reductions`. `MSubRed` depends on
`MEqRed` via the `Ms-Equ` constructor.

This module is the public surface for `MSubRed`.

Public surface:

* `MSubRed`, `MSubRed.pro`, `.top`, `.equ`, `.app`, `.fun_`, `.fOp`
* `MSubRedStar`
* `MSubRed.lc_left`, `MSubRed.lc_right`
-/

namespace Pss

/-- Paper-style notation for MPSS subtyping reduction:
`Γ ;ₘ s ⊢ u ⟶≤ v`. -/
notation:50 Γ " ;ₘ " s " ⊢ " u " ⟶≤ " v => MSubRed Γ s u v

/-- Many-step subtyping-reduction notation. -/
notation:50 Γ " ;ₘ " s " ⊢ " u " ⟶≤* " v => MSubRedStar Γ s u v

end Pss
