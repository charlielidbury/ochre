import Och.Macro
import Och.Eval
import Och.TyCheck
import Och.SubCheckVal
import Och.Std.Nat
import Och.Std.Unit
import Och.Std.Pair
import Och.Std.DNat
import Och.Std.Array

/-!
# Finite sets `DFin n` — dependent index bounded by a dNat

`DFin n` is the type of natural numbers strictly less than `n`. It is the
canonical test-bench for dependent types: `DFin n` is populated exactly
when `n = dsucc pred`, and a value of `DFin (dsucc pred)` is either `DFZ`
(the least element) or `DFS q` for some `q : DFin pred`.

```
DBot   = ι b. λ_:Type. b        -- uninhabited (see below)

DFin n = n.elim (λ_:dNat. Type)
          DBot                        -- DFin dzero: uninhabited
          (λpred:dNat.               -- DFin (dsucc pred):
            ι self:dNat.             -- Scott-encoded two-arm sum;
              λP:(self → Type).      --   `self:dNat` witnesses
              λfz:(P self).          --   DFin-inhabitant ⊑ dNat
              λfs:(λq:(DFin pred). P self).
              P self)

DFZ n   = ι self:dNat. λP:(self → Type). λfz:(P self). λfs:((DFin n) → Type). fz
DFS n q = ι self:dNat. λP:(self → Type). λfz:Type. λfs:(λq2:(DFin n). P self). fs q
```

The `ι self:dNat` annotation (rather than `Type`) is what makes
`dzero ⊑ DFin n` typecheck directly: `dzero`'s ι-body has the same
three-argument Scott shape as `DFin (dsucc _)`'s, and both annotations
coincide as `dNat`, so the ι-ι structural path closes without needing
a separate `DFZ` wrapper. `dsucc m` unfortunately does *not* reduce
to an ι with a compatible body shape, so `done_`/`dtwo`/... still
need the explicit `DFS` wrapper — see the "dNat as DFin elements"
test block below.

**Why `DBot`, not `Type`.** The first attempt used `Type` for the
`DFin dzero` branch on the grounds that no constructor ever produces a
`DFin dzero` anyway. That made `DFin dtwo ⊑ DFin done_` wrongly pass:
`DFin done_`'s `fs` parameter had domain `(F dzero) → P self = Type →
P self`, and by standard contravariance `(Type → X) ⊑ (DFin done_ → X)`
(a function accepting everything is a subtype of one accepting less),
so the dependent-index check collapsed. Replacing the branch with a
true bottom — `ι b. λ_:Type. b`, where the body references `self`
non-trivially so `v ⊑ DBot` generally fails — restores the
discrimination: `DFin done_ ⊄ DBot`, so the contravariant step is
genuinely constrained.

## Why this is the poster child for dependent types

`indexArrD : ∀T n. Array_ n T → DFin n → T` is safe out-of-bounds
indexing. A caller who passes `DFS dtwo (DFS done_ (DFZ dzero)) : DFin
dthree` where the array has length `dtwo` is rejected *at type-check
time*, not at runtime. This is precisely what `appendVec_wrong`
demonstrates for lengths; `DFin` demonstrates it for indices.
-/

namespace Std

-- ============================================================
-- Type and constructors
-- ============================================================

/-- Bottom: a degenerate ι whose body is `λ_:Type. self`. Substituting
`self ↦ v` gives `λ_:Type. v`, which is not a value most things coincide
with — so `v ⊑ DBot` is generally false. Unlike `Type`, `DBot` is *not* a
supertype of arbitrary values, so using `DBot` in a contravariant
position genuinely constrains. -/
def DBot := och{ ι b. λ_:Type. b }

def DFin := och{
  fix F:(dNat → Type).
    λn:dNat.
      n (λ_:dNat. Type)
        DBot
        (λpred:dNat.
          ι self:dNat.                    -- self is a dNat (subtype witness)
            λP:(self → Type).
            λfz:(P self).
            λfs:(λq:(F pred). P self).
            P self)
}

/-- Least element: `DFZ n : DFin (dsucc n)`. Same ι-body as `dzero`, with
annotation `dNat` so the subtype check `DFZ n ⊑ DFin (dsucc n)` succeeds
via `ι-ι` structural (both annotated `dNat`). -/
def DFZ := och{
  λn:dNat.
    ι self:dNat.
      λP:(self → Type).
      λfz:(P self).
      λfs:((DFin n) → Type).
      fz
}

/-- Successor: `DFS n q : DFin (dsucc n)` given `q : DFin n`. -/
def DFS := och{
  λn:dNat. λq:(DFin n).
    ι self:dNat.
      λP:(self → Type).
      λfz:Type.
      λfs:(λq2:(DFin n). P self).
      fs q
}

-- Convenient canonical elements
def dfin0_1 := och{ DFZ dzero }                            -- 0 : DFin 1
def dfin0_2 := och{ DFZ done_ }                            -- 0 : DFin 2
def dfin1_2 := och{ DFS done_ (DFZ dzero) }                 -- 1 : DFin 2
def dfin0_3 := och{ DFZ dtwo }                             -- 0 : DFin 3
def dfin1_3 := och{ DFS dtwo (DFZ done_) }                  -- 1 : DFin 3
def dfin2_3 := och{ DFS dtwo (DFS done_ (DFZ dzero)) }       -- 2 : DFin 3

-- ============================================================
-- Tests: subtype checks at the declared type
-- ============================================================

section Tests

-- ── Positive: correctly-sized indices inhabit DFin n ─────────

example : NbE.subCheck 2000 dfin0_1 (och{ DFin done_ })  = .ok true := by native_decide
example : NbE.subCheck 2000 dfin0_2 (och{ DFin dtwo })   = .ok true := by native_decide
example : NbE.subCheck 2000 dfin1_2 (och{ DFin dtwo })   = .ok true := by native_decide
example : NbE.subCheck 4000 dfin0_3 (och{ DFin dthree }) = .ok true := by native_decide
example : NbE.subCheck 4000 dfin1_3 (och{ DFin dthree }) = .ok true := by native_decide
example : NbE.subCheck 4000 dfin2_3 (och{ DFin dthree }) = .ok true := by native_decide

-- ── Negative: size mismatches rejected ──────────────────────

-- DFZ dzero : DFin 1 ⊄ DFin 2 (too small)
example : NbE.subCheck 2000 dfin0_1 (och{ DFin dtwo })   = .ok false := by native_decide

-- DFS done_ (DFZ dzero) : DFin 2 ⊄ DFin 3 (too small)
example : NbE.subCheck 2000 dfin1_2 (och{ DFin dthree }) = .ok false := by native_decide

-- DFS dtwo (DFZ done_) : DFin 3 ⊄ DFin 2 (too big). Without `DBot` in the
-- dzero branch this wrongly passed: `F dzero = Type` made the fs
-- parameter contravariantly top, collapsing the dependent index check.
example : NbE.subCheck 2000 dfin1_3 (och{ DFin dtwo })   = .ok false := by native_decide

-- Distinct DFin types are not subtypes of each other either way.
example : NbE.subCheck 2000 (och{ DFin dtwo }) (och{ DFin done_ }) = .ok false := by native_decide
example : NbE.subCheck 2000 (och{ DFin done_ }) (och{ DFin dtwo }) = .ok false := by native_decide

-- Type is not a DFin n (even though DBot ⊑ Type).
example : NbE.subCheck 2000 Expr.type (och{ DFin done_ })          = .ok false := by native_decide

-- DFZ done_ : DFin 2 is not a DFin 1.
example : NbE.subCheck 2000 (och{ DFZ done_ }) (och{ DFin done_ })  = .ok false := by native_decide

-- Wrong-shape rejection
example : NbE.subCheck 2000 zero_ (och{ DFin done_ })   = .ok false := by native_decide

-- ── dNat values as DFin elements (partial result) ──
--
-- With the self-type annotation `ι self:dNat`, `dzero` is directly
-- accepted as a `DFin n` element for any n ≥ 1 — no `DFZ` wrapper needed.
-- This is because `dzero` and `DFZ n` both evaluate to ι's with identical
-- body shape and matching annotation `dNat`.
example : NbE.subCheck 2000 dzero (och{ DFin done_ }) = .ok true := by native_decide
example : NbE.subCheck 2000 dzero (och{ DFin dtwo })  = .ok true := by native_decide

-- `dzero` is still correctly rejected from `DBot` (= `DFin dzero`).
example : NbE.subCheck 2000 dzero DBot = .ok false := by native_decide

-- *Successor* dNat values (`done_`, `dtwo`, ...) are NOT accepted
-- directly as DFin elements. `dsucc m : dNat` evaluates to a λ that
-- passes `m : dNat` to its `s`-branch, but `DFin (dsucc pred)`'s `fs`
-- branch requires `q : DFin pred` — strictly tighter. Contravariantly,
-- `dNat ⊑ DFin pred` is (correctly) false, so the lam-lam contravariant
-- check on the branch type fails. To use `dsucc m` as a DFin, you must
-- wrap in `DFS` to assert the predecessor bound.
example : NbE.subCheck 2000 done_ (och{ DFin dtwo })  = .ok false := by native_decide
example : NbE.subCheck 2000 dtwo  (och{ DFin dthree }) = .ok false := by native_decide

end Tests

-- ============================================================
-- indexArrD — safe out-of-bounds indexing
-- ============================================================

/-- `indexArrD T n arr f` = the `f`-th element of `arr`, where
`arr : Array_ n T` and `f : DFin n`. The `dzero` branch is statically
unreachable (no value of type `DFin dzero` exists since it reduces to
`DBot`), but the type-checker still demands a T — we supply a divergent
`fix loop:T. loop`. -/
def indexArrD := och{
  fix self:(λT:Type. λn:dNat. (Array_ n T) → (DFin n) → T).
    λT:Type. λn:dNat.
      n (λm:dNat. (Array_ m T) → (DFin m) → T)
        (λarr:(Array_ dzero T). λf:(DFin dzero). (fix loop:T. loop))
        (λpred:dNat. λarr:(Array_ (dsucc pred) T). λf:(DFin (dsucc pred)).
          f (λ_:(DFin (dsucc pred)). T)
            (fst_ arr)
            (λq:(DFin pred). self T pred (snd_ arr) q))
}

section IndexTests
open Expr

-- An Array of 3 Nats: [one, two, three]
private def arr3 := och{
  pair_ Nat_ (Pair Nat_ (Pair Nat_ Unit_))
    one_
    (pair_ Nat_ (Pair Nat_ Unit_)
      two_
      (pair_ Nat_ Unit_
        three_
        unit_))
}

-- ── Positive computation: indexing returns the right element ──

example : concEval 10000 (och{ indexArrD Nat_ dthree arr3 dfin0_3 })
        = concEval 10000 one_   := by native_decide
example : concEval 10000 (och{ indexArrD Nat_ dthree arr3 dfin1_3 })
        = concEval 10000 two_   := by native_decide
example : concEval 10000 (och{ indexArrD Nat_ dthree arr3 dfin2_3 })
        = concEval 10000 three_ := by native_decide

-- ── Negative computation: wrong answer rejected ──

example : concEval 10000 (och{ indexArrD Nat_ dthree arr3 dfin0_3 })
        ≠ concEval 10000 two_ := by native_decide

-- ── Type-level safety lives at the subtype level ──
--
-- `indexArrD` itself does not pass `NbE.typeCheck` at its declared type
-- `λT. λn. Array_ n T → DFin n → T` — the same A6-family incompleteness
-- that blocks `appendArrays` (see Array.lean). Concrete uses of
-- `indexArrD` also fail `NbE.typeCheck` for this reason, whether the DFin
-- index is correct or not, so the bidirectional checker can't
-- discriminate here.
--
-- The dependent-type discipline shows up where it counts: at the *DFin
-- value* subtype check. Constructing a wrong-size index is what a
-- mistaken caller would actually write, and the subtype relation
-- rejects it — see the "Negative subtype checks" block above, in
-- particular `dfin2_3 : DFin dthree ⊄ DFin dtwo` (the subtype Och would
-- reject at the `indexArrD arr2` callsite).

end IndexTests

end Std
