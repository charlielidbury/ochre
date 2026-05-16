import Och.Subtyping
import Och.EvalSubst
import Och.Soundness.EvalSubstLemmas
import Och.Soundness.CloseAll

/-!
# Structural arm lemmas for `subCheckSubst` soundness

In the pure de Bruijn regime, `closeAll` and `closeAllAt` are the
identity, so these lemmas reduce to direct applications of the
`Subtype'` structural rules (`.lam`, `.iota_cong`, `.fix_cong`).

The old `openFreshTop` / `closeAll_openFresh` bridge is no longer
needed — the engine now recurses directly on the raw body without
any substitution, so the IH is already in the right form.
-/

namespace Och.Soundness

open SubstEval

/-! ## Structural arm lemmas

Since `closeAll d e = e` in the pure de Bruijn regime, these
simplify to direct rule applications. -/

/-- C2: lam-lam structural arm. -/
theorem subCheckSubst_arm_lam_lam_struct
    {S : Seen} {Γ : Ctx} {d : Nat}
    {domA bodyA domB bodyB : Expr}
    (ih_dom : Subtype' S Γ (closeAll d domB) (closeAll d domA))
    (ih_body : Subtype' S (closeAll d domB :: Γ)
        (closeAllAt 1 d bodyA) (closeAllAt 1 d bodyB)) :
    Subtype' S Γ
      (closeAll d (.lam domA bodyA))
      (closeAll d (.lam domB bodyB)) := by
  -- closeAll is identity, closeAllAt is identity
  simp only [closeAll, closeAllAt] at *
  exact .lam ih_dom ih_body

/-- C3: iota-iota structural arm. -/
theorem subCheckSubst_arm_iota_iota_struct
    {S : Seen} {Γ : Ctx} {d : Nat}
    {annA bodyA annB bodyB : Expr}
    (ih_ann : Subtype' S Γ (closeAll d annA) (closeAll d annB))
    (ih_body : Subtype' S (closeAll d annB :: Γ)
        (closeAllAt 1 d bodyA) (closeAllAt 1 d bodyB)) :
    Subtype' S Γ
      (closeAll d (.iota annA bodyA))
      (closeAll d (.iota annB bodyB)) := by
  simp only [closeAll, closeAllAt] at *
  exact .iota_cong ih_ann ih_body

/-- C4: fix-fix structural arm. -/
theorem subCheckSubst_arm_fix_fix_struct
    {S : Seen} {Γ : Ctx} {d : Nat}
    {annA bodyA annB bodyB : Expr}
    (ih_ann : Subtype' S Γ (closeAll d annA) (closeAll d annB))
    (ih_body : Subtype' S (closeAll d annB :: Γ)
        (closeAllAt 1 d bodyA) (closeAllAt 1 d bodyB)) :
    Subtype' S Γ
      (closeAll d (.fix annA bodyA))
      (closeAll d (.fix annB bodyB)) := by
  simp only [closeAll, closeAllAt] at *
  exact .fix_cong ih_ann ih_body

/-! ## Composed arm lemmas

In the pure de Bruijn regime, the body IH translation is trivial
(no openFreshTop bridge needed). These composed forms are kept for
API compatibility with `SubCheckSubstSoundness.lean`. -/

/-- C2 (lam-lam) composed. The `closedAtLvl`/`lvarLT` hypotheses
    are vestigial (always true in the new regime) but retained for
    signature compatibility. -/
theorem subCheckSubst_arm_lam_lam
    {S : Seen} {Γ : Ctx} {d : Nat}
    {domA bodyA domB bodyB : Expr}
    (_hclA : True) (_hclB : True)
    (_hlvA : True) (_hlvB : True)
    (ih_dom : Subtype' S Γ (closeAll d domB) (closeAll d domA))
    (ih_body : Subtype' S (closeAll d domB :: Γ)
        (closeAll (d + 1) bodyA)
        (closeAll (d + 1) bodyB)) :
    Subtype' S Γ
      (closeAll d (.lam domA bodyA))
      (closeAll d (.lam domB bodyB)) := by
  simp only [closeAll, closeAllAt] at *
  exact .lam ih_dom ih_body

/-- C3 (iota-iota structural) composed. -/
theorem subCheckSubst_arm_iota_iota
    {S : Seen} {Γ : Ctx} {d : Nat}
    {annA bodyA annB bodyB : Expr}
    (_hclA : True) (_hclB : True)
    (_hlvA : True) (_hlvB : True)
    (ih_ann : Subtype' S Γ (closeAll d annA) (closeAll d annB))
    (ih_body : Subtype' S (closeAll d annB :: Γ)
        (closeAll (d + 1) bodyA)
        (closeAll (d + 1) bodyB)) :
    Subtype' S Γ
      (closeAll d (.iota annA bodyA))
      (closeAll d (.iota annB bodyB)) := by
  simp only [closeAll, closeAllAt] at *
  exact .iota_cong ih_ann ih_body

/-- C4 (fix-fix structural) composed. -/
theorem subCheckSubst_arm_fix_fix
    {S : Seen} {Γ : Ctx} {d : Nat}
    {annA bodyA annB bodyB : Expr}
    (_hclA : True) (_hclB : True)
    (_hlvA : True) (_hlvB : True)
    (ih_ann : Subtype' S Γ (closeAll d annA) (closeAll d annB))
    (ih_body : Subtype' S (closeAll d annB :: Γ)
        (closeAll (d + 1) bodyA)
        (closeAll (d + 1) bodyB)) :
    Subtype' S Γ
      (closeAll d (.fix annA bodyA))
      (closeAll d (.fix annB bodyB)) := by
  simp only [closeAll, closeAllAt] at *
  exact .fix_cong ih_ann ih_body

end Och.Soundness
