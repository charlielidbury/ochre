import Och.Simple.Macro
import Och.Simple.Subtype
import Och.Simple.Eval
import Och.Simple.Std.Bool
import Och.Simple.Std.Nat
import Och.Simple.Std.Pair
import Och.Simple.Std.Unit

/-!
# Aspirational Tests for Simple Och

Tests that SHOULD work in a more complete system but currently DON'T.
Organized by what feature is missing.
-/

set_option autoImplicit false

namespace Och.Simple.Std.Aspirational

open Och.Simple Expr

private def ev (e : Expr) : Option Expr := eval 200 e

-- Free variable markers for testing (since soch{...} cannot contain .var literals)
private def x₁ : Expr := .var 1
private def x₂ : Expr := .var 2
private def x₃ : Expr := .var 3
private def x₄₂ : Expr := .var 42
private def x₉₉ : Expr := .var 99

-- ============================================================
-- ASPIRATIONAL: Needs mu for recursive types
-- ============================================================

-- LIST = μ(list : ⊤). λ(a : ⊤). λ(r : ⊤). λ(cons : λ(hd : a). λ(tl : list a). r). λ(nil : r). r
-- Simple Och has no μ, so we cannot define recursive types.

-- def LIST := soch{ μ(list : ⊤). λ(a : ⊤). λ(r : ⊤). λ(cons : λ(hd : a). λ(tl : list a). r). λ(nil : r). r }
-- def NIL  := soch{ μ(nil : LIST). λ(a : ⊤). λ(r : ⊤). λ(cons : λ(hd : a). λ(tl : LIST a). r). λ(n : r). n }
-- def CONS := soch{ λ(a : ⊤). λ(hd : a). λ(tl : LIST a).
--   μ(self : LIST a). λ(r : ⊤). λ(cons : λ(hd' : a). λ(tl' : LIST a). r). λ(nil : r). cons hd tl }

-- TREE = μ(tree : ⊤). λ(a : ⊤). λ(r : ⊤). λ(leaf : a → r). λ(node : tree a → tree a → r). r
-- def TREE := soch{ μ(tree : ⊤). λ(a : ⊤). λ(r : ⊤). λ(leaf : a → r). λ(node : λ(_ : tree a). λ(_ : tree a). r). r }

-- Factorial would need both mu and Nat recursion
-- def FACT := soch{ μ(fact : NAT → NAT). λ(n : NAT). n NAT ONE (λ(pred : NAT). MUL n (fact pred)) }

-- FOLD over lists
-- def FOLD := soch{ λ(a : ⊤). λ(b : ⊤). μ(fold : LIST a → b → (a → b → b) → b).
--   λ(xs : LIST a). λ(z : b). λ(f : a → b → b).
--     xs b (λ(hd : a). λ(tl : LIST a). f hd (fold tl z f)) z }

-- ============================================================
-- ASPIRATIONAL: Needs BetaR for type-level computation
-- ============================================================

-- SUCC ZERO should evaluate to something equivalent to ONE at the type level.
-- Currently the subtype checker does not perform beta-reduction on the RHS,
-- so `SUCC ZERO ⊑ NAT` cannot be checked (the app doesn't reduce).

-- example : Sub [] (soch{ SUCC ZERO }) NAT := sorry  -- needs BetaR

-- Type-level application: applying a type function and checking the result
-- example : Sub [] (soch{ (λ(a : ⊤). a → a) BOOL }) (soch{ BOOL → BOOL }) := sorry  -- needs BetaR

-- ADD at type level: ADD ONE TWO ⊑ NAT
-- example : Sub [] (soch{ ADD ONE TWO }) NAT := sorry  -- needs BetaR

-- Evaluation confirms these compute correctly at the value level:
example : ev (soch{ SUCC ZERO ⊤ x₉₉ (λ(x : ⊤). x) })
  = some x₉₉ := rfl

-- But we cannot express "SUCC ZERO ⊑ NAT" in the subtype relation without BetaR.
-- Specifically, Sub.app gives us R[0 := a] on the LHS, but there is no rule
-- to beta-reduce on the RHS of ⊑.

-- ============================================================
-- ASPIRATIONAL: Needs more power (dependent elimination, universes, etc.)
-- ============================================================

-- Dependent pair elimination: given a pair (n, arr) where arr's type depends on n,
-- we need dependent elimination to project and maintain the dependency.
-- In full Och this works via self-types; Simple Och lacks the expressive power.

-- Universe polymorphism: UNIT and BOOL live at the same "level" as ⊤.
-- A stratified universe hierarchy would allow e.g. Type₀ : Type₁.

-- Leibniz equality: EQ = λ(a : ⊤). λ(x : a). λ(y : a). λ(P : a → ⊤). P x → P y
-- This can be written but proving anything with it requires BetaR.
-- def EQ : Expr := soch{ λ(a : ⊤). λ(x : a). λ(y : a). λ(P : a → ⊤). P x → P y }

-- ============================================================
-- ASPIRATIONAL: Interesting but untested (larger programs)
-- ============================================================

-- Church-encoded multiplication
-- MUL = λ(n : NAT). λ(m : NAT). λ(a : ⊤). λ(z : a). λ(f : a → a). n a z (m a z f)
-- Wait, that's not right. MUL should be:
-- MUL = λ(n : NAT). λ(m : NAT). λ(a : ⊤). λ(z : a). λ(f : a → a). n a z (λ(x : a). m a x f)
-- Actually the standard Church encoding is:
-- MUL = λ(n : NAT). λ(m : NAT). n NAT ZERO (λ(acc : NAT). ADD acc m)
-- but this requires SUCC/ADD to reduce at the type level (BetaR again).

-- Power: POW = λ(base : NAT). λ(exp : NAT). exp NAT ONE (λ(acc : NAT). MUL acc base)

-- Boolean-to-Nat conversion (requires BetaR to typecheck the IF):
-- BOOL_TO_NAT = λ(b : BOOL). IF b NAT ONE ZERO

-- Nested pairs: TRIPLE a b c = PAIR a (PAIR b c)
-- This works at the value level right now:
private def TRIPLE_VAL : Expr :=
  soch{ λ(a : ⊤). λ(b : ⊤). λ(c : ⊤). λ(x : a). λ(y : b). λ(z : c).
    MkPair ⊤ ⊤ x (MkPair ⊤ ⊤ y z) }

-- Evaluation works for triples:
example : ev (.app (.app (.app FST .top) .top)
    (.app (.app (.app (.app (.app (.app TRIPLE_VAL .top) .top) .top) x₁) x₂) x₃))
  = some x₁ := rfl

-- SWAP: swap elements of a pair
private def SWAP : Expr :=
  soch{ λ(a : ⊤). λ(b : ⊤). λ(p : PAIR a b).
    MkPair b a (SND a b p) (FST a b p) }

-- SWAP works at value level:
private def swapped : Expr := .app (.app (.app SWAP .top) .top)
    (.app (.app (.app (.app MkPair .top) .top) x₄₂) x₉₉)
example : ev (.app (.app (.app FST .top) .top) swapped) = some x₉₉ := rfl
example : ev (.app (.app (.app SND .top) .top) swapped) = some x₄₂ := rfl

-- Composition: COMPOSE f g x = f (g x)
private def COMPOSE : Expr :=
  soch{ λ(a : ⊤). λ(b : ⊤). λ(c : ⊤).
    λ(f : b → c). λ(g : a → b). λ(x : a). f (g x) }

-- Compose id id = id (at value level)
private def idFn : Expr := soch{ λ(x : ⊤). x }
example : ev (.app (.app (.app (.app (.app (.app COMPOSE .top) .top) .top) idFn) idFn) x₄₂)
  = some x₄₂ := rfl

end Och.Simple.Std.Aspirational
