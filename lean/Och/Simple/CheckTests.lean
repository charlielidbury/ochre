import Och.Simple.Check
import Och.Simple.Macro
import Och.Simple.Std.Bool
import Och.Simple.Std.Nat
import Och.Simple.Std.DBool
import Och.Simple.Std.DNat
import Och.Simple.Std.Mu
import Och.Simple.Std.Unit
import Och.Simple.Std.Pair

/-!
# Tests for the Sub decision procedure

Runs `check` on all existing Sub derivation tests and aspirational tests.
Reports which ones the algorithm handles.
-/

set_option autoImplicit false

namespace Och.Simple.CheckTests

open Och.Simple Expr Std

private def ck (a b : Expr) : Option Bool := check 100 [] a b
private def ckG (Γ : Ctx) (a b : Expr) : Option Bool := check 100 Γ a b

/-- ID = λb:BOOL. (b BOOL TRUE FALSE : BOOL) -/
private def ID : Expr := .lam BOOL (.asc (.app (.app (.app (.var 0) BOOL) TRUE) FALSE) BOOL)

-- ============================================================
-- Tests from Tests.lean (all should pass)
-- ============================================================

section FromTests

-- [Refl]: ⊤ ⊑ ⊤
example : ck .top .top = some true := rfl

-- [Top]: anything ⊑ ⊤
example : ck (.var 0) .top = some true := rfl
example : ck BOOL .top = some true := rfl

-- [Refl]: BOOL ⊑ BOOL
example : ck BOOL BOOL = some true := rfl

-- TRUE ⊑ BOOL
example : ck TRUE BOOL = some true := rfl

-- FALSE ⊑ BOOL
example : ck FALSE BOOL = some true := rfl

-- (TRUE : BOOL) ⊑ BOOL
example : ck (.asc TRUE BOOL) BOOL = some true := rfl

-- TRUE ⊑ (TRUE : BOOL) via [Asc-R]
example : ck TRUE (.asc TRUE BOOL) = some true := rfl

-- [Var] x:⊤ ⊢ x ⊑ ⊤
example : ckG [.top] (.var 0) .top = some true := rfl

-- Contravariant domain: (λ⊤. 0) ⊑ (λ(λ⊤.⊤). 0)
example : ck (.lam .top (.var 0)) (.lam (.lam .top .top) (.var 0)) = some true := rfl

-- ID ⊑ (BOOL → BOOL)
example : ck ID (.lam BOOL BOOL) = some true := rfl

end FromTests

-- ============================================================
-- Tests from Bool.lean
-- ============================================================

section FromBool

example : ck TRUE BOOL = some true := rfl
example : ck FALSE BOOL = some true := rfl
example : ck BOOL .top = some true := rfl
example : ck (.asc TRUE BOOL) BOOL = some true := rfl
example : ck TRUE (.asc TRUE BOOL) = some true := rfl

end FromBool

-- ============================================================
-- Tests from Nat.lean
-- ============================================================

section FromNat

-- ZERO ⊑ NAT
example : ck ZERO NAT = some true := rfl

-- ONE ⊑ NAT
example : ck ONE NAT = some true := rfl

-- NAT ⊑ ⊤
example : ck NAT .top = some true := rfl

end FromNat

-- ============================================================
-- Tests from MuTests.lean
-- ============================================================

section FromMuTests

-- CONST_TOP ⊑ ⊤
example : ck CONST_TOP .top = some true := rfl

-- SELF_ID ⊑ ⊤
example : ck SELF_ID .top = some true := rfl

-- SELF_ID ⊑ (⊤ → ⊤)
example : ck SELF_ID (.lam .top .top) = some true := rfl

-- DIVERGE ⊑ (⊤ → ⊤)
example : ck DIVERGE (.lam .top .top) = some true := rfl

-- CONST_TOP ⊑ CONST_TOP (refl)
example : ck CONST_TOP CONST_TOP = some true := rfl

end FromMuTests

-- ============================================================
-- Tests from DBool.lean
-- ============================================================

section FromDBool

-- dtrue ⊑ ⊤
example : ck dtrue .top = some true := rfl

-- dfalse ⊑ ⊤
example : ck dfalse .top = some true := rfl

-- dBool ⊑ ⊤
example : ck dBool .top = some true := rfl

-- Self-subtyping
example : ck dtrue dtrue = some true := rfl
example : ck dfalse dfalse = some true := rfl
example : ck dBool dBool = some true := rfl

end FromDBool

-- ============================================================
-- Tests from DNat.lean
-- ============================================================

section FromDNat

example : ck dzero .top = some true := rfl
example : ck dsucc .top = some true := rfl
example : ck dNat .top = some true := rfl
example : ck done_ .top = some true := rfl

example : ck dzero dzero = some true := rfl
example : ck dsucc dsucc = some true := rfl
example : ck dNat dNat = some true := rfl

end FromDNat

-- ============================================================
-- Aspirational Category A: Self-type intro (Sub.muR)
-- ============================================================

section CategoryA

-- A1: dtrue ⊑ dBool -- PASSES with muR!
example : ck dtrue dBool = some true := rfl

-- A2: dfalse ⊑ dBool -- PASSES with muR!
example : ck dfalse dBool = some true := rfl

-- A3: dzero ⊑ dNat -- PASSES with muR!
example : ck dzero dNat = some true := rfl

-- A4: done_ ⊑ dNat -- FAILS: needs BetaR (type-level computation)
-- dsucc has annotation ⊤→⊤ which loses dependent return type info.
-- The unfolded body contains dsucc applications inside types (P (dsucc pred))
-- which need beta-reduction to compare against dNat's structure.
#eval check 500 [] done_ dNat  -- some false

end CategoryA

-- ============================================================
-- Negative tests (should return false)
-- ============================================================

section Negative

-- ⊤ ⊑ BOOL — should fail
example : ck .top BOOL = some false := rfl

-- ⊤ ⊑ λ⊤.0 — should fail
example : ck .top (.lam .top (.var 0)) = some false := rfl

-- FALSE ⊑ TRUE — let's see
#eval ck FALSE TRUE

end Negative

-- ============================================================
-- Performance: how much fuel is needed?
-- ============================================================

section FuelTests

-- TRUE ⊑ BOOL needs how much fuel?
#eval check 1 [] TRUE BOOL
#eval check 5 [] TRUE BOOL
#eval check 10 [] TRUE BOOL

-- ID ⊑ (BOOL → BOOL)
#eval check 5 [] ID (.lam BOOL BOOL)
#eval check 10 [] ID (.lam BOOL BOOL)
#eval check 20 [] ID (.lam BOOL BOOL)
#eval check 50 [] ID (.lam BOOL BOOL)

end FuelTests

-- ============================================================
-- Summary
-- ============================================================

#eval do
  let tests : List (String × Option Bool) := [
    ("TRUE ⊑ BOOL", check 200 [] TRUE BOOL),
    ("FALSE ⊑ BOOL", check 200 [] FALSE BOOL),
    ("ZERO ⊑ NAT", check 200 [] ZERO NAT),
    ("ONE ⊑ NAT", check 200 [] ONE NAT),
    ("ID ⊑ (BOOL→BOOL)", check 200 [] ID (.lam BOOL BOOL)),
    ("SELF_ID ⊑ (⊤→⊤)", check 200 [] SELF_ID (.lam .top .top)),
    ("DIVERGE ⊑ (⊤→⊤)", check 200 [] DIVERGE (.lam .top .top)),
    ("dtrue ⊑ dBool", check 200 [] dtrue dBool),
    ("dfalse ⊑ dBool", check 200 [] dfalse dBool),
    ("dzero ⊑ dNat", check 200 [] dzero dNat),
    ("done_ ⊑ dNat", check 200 [] done_ dNat)
  ]
  let mut result : String := ""
  for (name, r) in tests do
    let status := match r with
      | some true => "PASS"
      | some false => "FAIL"
      | none => "FUEL"
    result := result ++ s!"{status}: {name}\n"
  return result

end Och.Simple.CheckTests
