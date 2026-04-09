import Och.Simple.CheckSoundness
import Och.Simple.Macro
import Och.Simple.Std.Bool
import Och.Simple.Std.Nat
import Och.Simple.Std.Mu

/-!
# Tests for check soundness

Each `check_implies_Sub` application takes a `check fuel Γ a b = some true`
proof (computed by `rfl` / `native_decide`) and produces a `Sub Γ a b` derivation.
-/

set_option autoImplicit false

namespace Och.Simple.CheckSoundnessTests

open Expr Std

-- ============================================================
-- Basic tests: these exercise the proved cases
-- ============================================================

-- [Refl]: ⊤ ⊑ ⊤
noncomputable example : Sub [] .top .top :=
  check_implies_Sub (by native_decide : check 10 [] [] .top .top = some true)

-- [Top]: BOOL ⊑ ⊤
noncomputable example : Sub [] BOOL .top :=
  check_implies_Sub (by native_decide : check 10 [] [] BOOL .top = some true)

-- [Refl]: BOOL ⊑ BOOL
noncomputable example : Sub [] BOOL BOOL :=
  check_implies_Sub (by native_decide : check 10 [] [] BOOL BOOL = some true)

-- [Var]: x:⊤ ⊢ x ⊑ ⊤
noncomputable example : Sub [.top] (.var 0) .top :=
  check_implies_Sub (by native_decide : check 10 [] [.top] (.var 0) .top = some true)

-- [Lam]: contravariant domain
noncomputable example : Sub [] (.lam .top (.var 0)) (.lam (.lam .top .top) (.var 0)) :=
  check_implies_Sub (by native_decide : check 10 [] [] (.lam .top (.var 0)) (.lam (.lam .top .top) (.var 0)) = some true)

-- [Asc-L]: (TRUE : BOOL) ⊑ BOOL
noncomputable example : Sub [] (.asc TRUE BOOL) BOOL :=
  check_implies_Sub (by native_decide : check 100 [] [] (.asc TRUE BOOL) BOOL = some true)

-- [Asc-R]: TRUE ⊑ (TRUE : BOOL)
noncomputable example : Sub [] TRUE (.asc TRUE BOOL) :=
  check_implies_Sub (by native_decide : check 100 [] [] TRUE (.asc TRUE BOOL) = some true)

-- ============================================================
-- Mu tests
-- ============================================================

-- CONST_TOP ⊑ ⊤ via muUnfoldL
noncomputable example : Sub [] CONST_TOP .top :=
  check_implies_Sub (by native_decide : check 100 [] [] CONST_TOP .top = some true)

-- SELF_ID ⊑ ⊤
noncomputable example : Sub [] SELF_ID .top :=
  check_implies_Sub (by native_decide : check 100 [] [] SELF_ID .top = some true)

-- SELF_ID ⊑ (⊤ → ⊤) — now provable! annotation trust gap is fixed
noncomputable example : Sub [] SELF_ID (.lam .top .top) :=
  check_implies_Sub (by native_decide : check 100 [] [] SELF_ID (.lam .top .top) = some true)

-- DIVERGE ⊑ (⊤ → ⊤) — now provable! annotation trust gap is fixed
noncomputable example : Sub [] DIVERGE (.lam .top .top) :=
  check_implies_Sub (by native_decide : check 100 [] [] DIVERGE (.lam .top .top) = some true)

-- CONST_TOP ⊑ CONST_TOP (refl)
noncomputable example : Sub [] CONST_TOP CONST_TOP :=
  check_implies_Sub (by native_decide : check 100 [] [] CONST_TOP CONST_TOP = some true)

-- ============================================================
-- Nat tests
-- ============================================================

-- ZERO ⊑ NAT
noncomputable example : Sub [] ZERO NAT :=
  check_implies_Sub (by native_decide : check 100 [] [] ZERO NAT = some true)

-- NAT ⊑ ⊤
noncomputable example : Sub [] NAT .top :=
  check_implies_Sub (by native_decide : check 100 [] [] NAT .top = some true)

-- ============================================================
-- Negative test: check returns false, so check_implies_Sub doesn't apply
-- ============================================================

-- ⊤ ⊑ BOOL fails (check returns some false)
example : check 10 [] [] .top BOOL = some false := by native_decide

end Och.Simple.CheckSoundnessTests
