import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Soundness
import Och.Tests

/-!
# Dependent Scott-encoded Natural Numbers

Scott-style dependent Nat where the return type of elimination depends
on the value being eliminated. This enables functions like `appendArrays`
to have precise return types (e.g., `Array (add n m) T`) instead of
using `Type` as the return type.

## Design

```
dNat = μ(dNat : Type).
  let dzero = μ(dzero : dNat). λP:(dNat→Type). λz:(P dzero). λs:Type. z
  let dsucc = μ(dsucc : dNat→dNat).
    λn:dNat. λP:(dNat→Type). λz:(P dzero).
    λs:(∀pred:dNat. P pred → P (dsucc pred)).
    s n (n P z s)
  λP:(dNat→Type). λz:(P dzero).
  λs:(∀pred:dNat. P pred → P (dsucc pred)).
  P dNat
```

Key properties:
- Scott-style: eliminates one level (zero or succ pred)
- Dependent: return type P can depend on the nat value
- dzero has λs:Type (s unused, domain is Top for covariance)
- dsucc's s: `s n (n P z s)` — applies s to pred and recursive result
- Nested mus work because mu-as-value prevents eager cascading evaluation
-/

open Expr Named

namespace DSNat

-- ============================================================
-- Helpers
-- ============================================================

/-- Motive type: dNat → Type -/
def motiveTy (dNat : Named) : Named := .lam "_" dNat .type

/-- Type of the s parameter: ∀pred:dNat. P pred → P (dsucc pred) -/
def succParamTy (dNat dsucc : Named) : Named :=
  .lam "pred" dNat
    (.lam "_" (.app (.var "P") (.var "pred"))
      (.app (.var "P") (.app dsucc (.var "pred"))))

/-- Let-binding: `let x : T = val in body` as `(λx:T. body) val` -/
def «let» (name : String) (ty val body : Named) : Named :=
  .app (.lam name ty body) val

-- ============================================================
-- Core definitions
-- ============================================================

/-- dzero value: μ(dzero : dNat). λP:(dNat→Type). λz:(P dzero). λs:Type. z -/
def dzeroVal (dNat : Named) : Named :=
  .mu "dzero" dNat
    (.lam "P" (motiveTy dNat)
      (.lam "z" (.app (.var "P") (.var "dzero"))
        (.lam "s" .type
          (.var "z"))))

/-- dsucc value: μ(dsucc : dNat→dNat). λn:dNat. λP. λz:(P dzero). λs:(succTy). s n (n P z s) -/
def dsuccVal (dNat dzero : Named) : Named :=
  .mu "dsucc" (.lam "_" dNat dNat)
    (.lam "n" dNat
      (.lam "P" (motiveTy dNat)
        (.lam "z" (.app (.var "P") dzero)
          (.lam "s" (succParamTy dNat (.var "dsucc"))
            (.app (.app (.var "s") (.var "n"))
              (.app (.app (.app (.var "n") (.var "P")) (.var "z")) (.var "s")))))))

/-- dNat type: mu with let-bound dzero and dsucc -/
def dNat_n : Named :=
  .mu "dNat" .type
    («let» "dzero" (.var "dNat") (dzeroVal (.var "dNat"))
      («let» "dsucc" (.lam "_" (.var "dNat") (.var "dNat")) (dsuccVal (.var "dNat") (.var "dzero"))
        (.lam "P" (motiveTy (.var "dNat"))
          (.lam "z" (.app (.var "P") (.var "dzero"))
            (.lam "s" (succParamTy (.var "dNat") (.var "dsucc"))
              (.app (.var "P") (.var "dNat")))))))

def dNat_e : Expr := n dNat_n

/-- Standalone dzero (references full dNat) -/
def dzero_n : Named := dzeroVal dNat_n
def dzero_e : Expr := n dzero_n

/-- Standalone dsucc (references full dNat and dzero) -/
def dsucc_n : Named := dsuccVal dNat_n dzero_n
def dsucc_e : Expr := n dsucc_n

-- ============================================================
-- Computation tests
-- ============================================================

-- dzero P z s = z
example : concEval 50
  (.app (.app (.app dzero_e (.lam dNat_e Nat')) (n zero'_n)) (.lam dNat_e (n one'_n)))
  = some zero' := by native_decide

-- dsucc dzero eliminates: (dsucc dzero) P z s = s dzero (dzero P z s) = s dzero z
-- Using P = λ_.Nat, z = zero, s = λpred.λ_.one:
-- s dzero z = (λpred.λ_.one) dzero z = one
example : concEval 50
  (.app (.app (.app (.app dsucc_e dzero_e) (.lam dNat_e Nat')) (n zero'_n))
    (.lam dNat_e (.lam Nat' (n one'_n))))
  = some one' := by native_decide

-- Non-dependent case analysis: dcase n = zero→0, succ _→1
private def dcase_n : Named :=
  .lam "n" dNat_n
    (.app (.app (.app (.var "n")
      (.lam "_" dNat_n Nat'_n))   -- P = λ_. Nat (constant motive)
      zero'_n)                     -- zero case: 0
      (.lam "_" dNat_n (.lam "_" Nat'_n one'_n)))  -- succ case: λpred. λ_. 1
private def dcase_e := n dcase_n

example : concEval 50 (.app dcase_e dzero_e) = some zero' := by native_decide
example : concEval 50 (.app dcase_e (.app dsucc_e dzero_e)) = some one' := by native_decide

-- ============================================================
-- Subtype checking tests
-- ============================================================

-- dsucc dzero ⊑ dNat
example : subCheck 50 (.app dsucc_e dzero_e) dNat_e = true := by native_decide

-- dzero ⊑ dNat — currently investigating why this fails
-- The issue is that after self-intro unfolds dNat, the let-bindings
-- produce a dzero_subst that may differ structurally from the standalone
-- dzero_e. See debugging below.
-- example : subCheck 200 dzero_e dNat_e = true := by native_decide

-- ============================================================
-- Debugging: dzero ⊑ dNat
-- ============================================================

-- When subCheckNF checks dzero ⊑ dNat:
-- 1. dNat is a mu → self-intro: check dzero ⊑ body[self:=dNat]
-- 2. body[self:=dNat] has let-bindings → absEval normalizes to:
--    λP. λz:(P dzero_subst). λs:(...). P dNat
--    where dzero_subst is dzeroVal with dNat substituted
-- 3. dzero is a mu → self-elim: check dzero_body[self:=dzero] ⊑ that
--    = λP. λz:(P dzero). λs:Type. z
-- 4. Lam ⊑ lam: contravariant domains, covariant body.
--    - P domain: same ✓
--    - z domain: (P dzero_subst) ⊑ (P dzero) contravariant →
--      need dzero ⊑ dzero_subst. Are these the same term?

-- Extract dNat's body and substitute self=dNat, then normalize.
-- This is what subCheckNF sees after self-intro.
def dNat_body : Expr :=
  match dNat_e with
  | .mu _ann body => body
  | e => e

def dNat_unfolded : Expr := dNat_body.subst 0 dNat_e

-- Normalize the unfolded body (beta-reduces the let-bindings)
#eval absEval 50 [] dNat_unfolded

-- Extract dzero's body and substitute self=dzero, then normalize.
-- This is what subCheckNF sees after self-elim.
def dzero_body : Expr :=
  match dzero_e with
  | .mu _ann body => body
  | e => e

def dzero_unfolded : Expr := dzero_body.subst 0 dzero_e

#eval absEval 50 [] dzero_unfolded

-- Compare the z-parameter domains from both sides.
-- dNat's normalized body should have z:(P dzero_subst)
-- dzero's normalized body should have z:(P dzero)
-- If dzero_subst == dzero, subCheckNF can verify the subtyping.

#eval do
  let a ← absEval 50 [] dNat_unfolded
  let b ← absEval 50 [] dzero_unfolded
  match a, b with
  | .lam _ (.lam domZ_a _), .lam _ (.lam domZ_b _) =>
    return s!"z-domains equal: {decide (domZ_a = domZ_b)}"
  | _, _ => return "unexpected structure"

-- Print the z-domains for inspection
#eval do
  let a ← absEval 50 [] dNat_unfolded
  match a with
  | .lam _ (.lam domZ _) => return some domZ
  | _ => return none

#eval do
  let b ← absEval 50 [] dzero_unfolded
  match b with
  | .lam _ (.lam domZ _) => return some domZ
  | _ => return none

end DSNat
