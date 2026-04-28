import Pss.Mpss.Reductions

/-! # `Pss.Mpss.EqRed` — re-export shim for MPSS equivalence reduction

The MPSS equivalence reduction `MEqRed` and its reflexive-transitive
closure `MEqRedStar` are defined in `Pss.Mpss.Reductions` together with
`MSubRed` (which depends on `MEqRed` via `Ms-Equ`).

This module is the public surface for `MEqRed` — downstream modules that
only need equivalence reduction (and not subtyping reduction) import
this shim.

Public surface:

* `MEqRed`, `MEqRed.pro`, `.bet`, `.top`, `.app`, `.var`, `.fun_`, `.tAp`, `.fOp`
* `MEqRedStar`
* `MEqRed.lc_left`, `MEqRed.lc_right`

The optional notation `Γ ; s ⊢ u ⟶≡ v` is provided here for paper-style
display; downstream files may use either the named term or the notation.
-/

namespace Pss

/-- Paper-style notation for MPSS equivalence reduction. We bundle the
context and stack into a single string-form for readability:
`Γ ;ₘ s ⊢ u ⟶≡ v`. -/
notation:50 Γ " ;ₘ " s " ⊢ " u " ⟶≡ " v => MEqRed Γ s u v

/-- Many-step equivalence-reduction notation. -/
notation:50 Γ " ;ₘ " s " ⊢ " u " ⟶≡* " v => MEqRedStar Γ s u v

end Pss
