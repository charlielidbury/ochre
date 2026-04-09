import Och.Simple.Macro
import Och.Simple.Subtype
import Och.Simple.Eval
import Och.Simple.Std.Nat
import Och.Simple.Std.Bool
import Och.Simple.Std.Unit

/-!
# Fixpoint combinator and recursive examples for Simple Och

Uses mu for general recursion. Demonstrates what works (typing recursive
functions via Sub.mu) and what diverges.
-/

set_option autoImplicit false

namespace Och.Simple.Std

open Och.Simple Expr

-- ============================================================
-- Definitions
-- ============================================================

/-- CONST_TOP: mu(s:T). T — body ignores self, unfolds to T. -/
def CONST_TOP : Expr := soch{ μ(s : ⊤). ⊤ }

/-- SELF_ID: mu(self : T -> T). λx:T. x — identity via fixpoint. -/
def SELF_ID : Expr := soch{ μ(self : ⊤ → ⊤). λ(x : ⊤). x }

/-- DIVERGE: mu(f : T -> T). λx:T. f x — diverges when applied. -/
def DIVERGE : Expr := soch{ μ(f : ⊤ → ⊤). λ(x : ⊤). f x }

/-- OMEGA: mu(x:T). x x — self-application. Pure divergence. -/
def OMEGA : Expr := soch{ μ(x : ⊤). x x }

/-- FIX: mu(f:T). f — trivial fixpoint, always diverges. -/
def FIX : Expr := soch{ μ(f : ⊤). f }

/-- Recursive identity on "nats" (non-thunked, diverges concretely).
    toZero = mu(self : T -> T). λn:T. ISZERO n T ZERO (self ZERO) -/
def toZero_bad : Expr := soch{
  μ(self : ⊤ → ⊤). λ(n : ⊤). ISZERO n ⊤ ZERO (self ZERO)
}

/-- Thunked version: uses UNIT to thunk branches so concrete eval terminates.
    toZero = mu(self : T -> T). λn:T. ISZERO n (UNIT -> T) (λ_. ZERO) (λ_. self ZERO) TT -/
def toZero : Expr := soch{
  μ(self : ⊤ → ⊤). λ(n : ⊤). ISZERO n (UNIT → ⊤) (λ(_ : UNIT). ZERO) (λ(_ : UNIT). self ZERO) TT
}

/-- Nested mu: mu(a:T). mu(b:T). mu(c:T). T -/
def NESTED_MU : Expr := soch{ μ(a : ⊤). μ(b : ⊤). μ(c : ⊤). ⊤ }

/-- mu returning a lambda, then applied:
    mu(f : T -> T). λx:T. mu(g:T). x -/
def NESTED_MU_LAM : Expr := soch{ μ(f : ⊤ → ⊤). λ(x : ⊤). μ(g : ⊤). x }

-- ============================================================
-- Evaluation tests
-- ============================================================

private def ev (e : Expr) : Option Expr := eval 200 e

-- CONST_TOP unfolds to T
example : ev CONST_TOP = some .top := rfl

-- SELF_ID unfolds to λx. x
example : ev SELF_ID = some (soch{ λ(x : ⊤). x }) := rfl

-- SELF_ID applied to T = T
example : ev (soch{ SELF_ID ⊤ }) = some .top := rfl

-- DIVERGE alone produces a lambda (one mu unfolding)
example : (ev DIVERGE).isSome = true := rfl

-- DIVERGE applied diverges
example : eval 10 (soch{ DIVERGE ⊤ }) = none := rfl
example : eval 50 (soch{ DIVERGE ⊤ }) = none := by native_decide

-- OMEGA diverges
example : eval 10 OMEGA = none := rfl
example : eval 50 OMEGA = none := by native_decide

-- FIX diverges
example : eval 1 FIX = none := rfl
example : eval 100 FIX = none := rfl

-- toZero_bad with ZERO: in CBN this terminated because only the selected branch
-- was evaluated. In CBV, ALL arguments are evaluated before the function call,
-- so `self ZERO` in the "else" branch is evaluated even when not needed.
-- This causes divergence — the classic CBN vs CBV difference.
-- (CBN: terminates; CBV: diverges)
example : eval 200 (.app toZero_bad ZERO) = none := by native_decide

-- toZero (thunked) terminates: toZero ZERO = ZERO
example : (ev (soch{ toZero ZERO })).isSome = true := rfl

-- NESTED_MU: 3 levels of unfolding, then T
example : eval 4 NESTED_MU = some .top := rfl
example : eval 2 NESTED_MU = none := rfl

-- NESTED_MU_LAM applied
example : ev (.app NESTED_MU_LAM .top) = some .top := rfl
example : ev (.app NESTED_MU_LAM (.var 42)) = some (.var 42) := rfl

-- mu inside ascription: ascription erased, then mu unfolds
example : ev (.asc CONST_TOP .top) = some .top := rfl

-- Identity applied to mu: (λx.x) (mu(s:T). T) = T
example : ev (soch{ (λ(x : ⊤). x) CONST_TOP }) = some .top := rfl

-- mu with redex body: mu(s:T). (λx:T. x) T = T
def MU_REDEX : Expr := soch{ μ(s : ⊤). (λ(x : ⊤). x) ⊤ }
example : ev MU_REDEX = some .top := rfl

-- ============================================================
-- Sub derivations
-- ============================================================

-- CONST_TOP <= T
example : Sub [] CONST_TOP .top :=
  Sub.mu [] .top .top .top
    (Sub.refl [] .top)
    (Sub.refl [.top] .top)

-- SELF_ID <= (T -> T) via mu rule
example : Sub [] SELF_ID (.lam .top .top) :=
  Sub.mu [] (.lam .top .top) (.lam .top (.var 0)) (.lam .top .top)
    (Sub.refl [] (.lam .top .top))
    (Sub.lam [.lam .top .top] .top .top (.var 0) .top
      (Sub.refl [.lam .top .top] .top)
      (Sub.top [.top, .lam .top .top] (.var 0)))

-- DIVERGE <= (T -> T) via mu rule
-- Body check: [(T->T)] |- λx:T. f x <= (T->T)
-- [Lam]: T <= T and [T, (T->T)] |- f x <= T (by Top)
example : Sub [] DIVERGE (.lam .top .top) :=
  Sub.mu [] (.lam .top .top) (.lam .top (.app (.var 1) (.var 0))) (.lam .top .top)
    (Sub.refl [] (.lam .top .top))
    (Sub.lam [.lam .top .top] .top .top (.app (.var 1) (.var 0)) .top
      (Sub.refl [.lam .top .top] .top)
      (Sub.top [.top, .lam .top .top] (.app (.var 1) (.var 0))))

-- ============================================================
-- ASPIRATIONAL: Category D — Recursive types/functions
-- ============================================================

-- ASPIRATIONAL: LIST encoding using mu
-- LIST = mu(list : T). λa:T. λr:T. λcons:(λhd:a. λtl:(list a). r). λnil:r. r
-- Flip condition: needs mu expressiveness + possibly Sub.muR for constructor typing
-- def LIST : Expr := soch{
--   μ(list : ⊤). λ(a : ⊤). λ(r : ⊤).
--     λ(cons : λ(hd : a). λ(tl : list a). r). λ(nil : r). r
-- }

-- ASPIRATIONAL: FOLD over lists
-- Flip condition: LIST + recursive function typing
-- def FOLD : Expr := soch{ ... }

-- ASPIRATIONAL: Factorial
-- FACT = mu(fact : NAT -> NAT). λn:NAT. ISZERO n NAT ONE (MUL n (fact (PRED n)))
-- Needs: MUL, PRED, and thunking for concrete eval
-- Flip condition: Full arithmetic + thunking strategy
-- def FACT : Expr := soch{ ... }

end Och.Simple.Std
