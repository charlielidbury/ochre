import Och.Macro
import Och.Eval
import Och.TyCheck
import Och.SubCheckVal
import Och.Std.Nat
import Och.Std.Unit
import Och.Std.Pair
import Och.Std.DNatExp

/-!
# Experimental: DFin over singleton-tightened dNat

Research question: can `dsucc m ⊑ DFin (dsucc n)` hold directly
(without a DFS wrapper) when `m` is bounded by `n`?

Baseline (from Std/DFin.lean): `dzero ⊑ DFin n` holds for `n ≥ 1` via
the `ι self:dNat` trick, but `done_ ⊑ DFin dtwo` fails. This file
explores encoding variants and finds a WORKING encoding (Option F).

## Summary of findings

| Encoding | `done_ ⊑ DFin dtwo` | `dtwo ⊑ DFin dthree` | Diagonal rej. | Notes |
|----------|---------------------|----------------------|---------------|-------|
| Baseline | false               | false                | n/a           | DFS needed |
| A        | false               | false                | n/a           | singleton on dsucc only |
| B        | false               | false                | n/a           | + `P(dsucc pred)` codomain |
| C        | false               | false                | n/a           | + singleton on DFin fs |
| D        | false               | false                | n/a           | body `fs pred` style |
| E        | false               | false                | n/a           | struct-ident with dNat |
| **F**    | **true**            | **true**             | **true**      | **WINNER** |

## Option F: The working encoding

Core insight: the obstruction was the codomain mismatch. `dsucc m` returns
`s m : P (dsucc m)` (dependent on the argument m), but baseline DFin's
`fs` returns `P self` (constant). After iotaIntro with self := dsucc m,
the rhs return type is `P (dsucc m)` too — but under the LAM-LAM structural
comparison of fs (when a fresh q is pushed), lhs gives `P (dsucc q)` and
rhs gives `P (dsucc m)`, and those don't subsume.

Option F: make DFin's fs return `P (dsuccA q)` (depending on q, the Fin
successor argument). Then fresh q pushed into both sides yields the same
codomain `P (dsuccA fresh_q)`, and the bodies line up.

```
DFinF n = n (λ_. Type) Bot
  (λpred:dNatA. ι self:dNatA.
     λP:(self → Type).
     λfz:(P self).
     λfs:(λq:(F pred). P (dsuccA q)).    -- NEW: depends on q, not self
     P self)
```

The `ι self` still returns `P self`, which under iotaIntro becomes
`P (dsucc m)` for the lhs numeral — matching dsuccA's `s m` type ascent.

## Open question: DFin n ⊑ dNat at the TYPE level

Option F preserves the value-level discipline (specific values like
`dzero_A` inhabit DFinF via the ι annotation), but the TYPE-level
subsumption `DFinF n ⊑ dNatA` does NOT hold. The original DFin didn't
assert this either — it's not load-bearing for `indexArrD` or similar.
-/

namespace Std

namespace DNatExp

-- ============================================================
-- DFinExpA: mirror of DFin over Option-A dNat
-- ============================================================

/-- Bottom: primitive `Bot`. Used for DFin dzero branch. -/
def DBotA := och{ Bot }

/-- DFin where successor branch s-domain mirrors the dsuccA singleton.

Original DFin:
  λpred. ι self:dNat.
    λP:(self→Type). λfz:(P self). λfs:(λq:(F pred). P self). P self

Option A1: s-domain still `F pred` (Fin subset), codomain stays `P self`.
This is the plain DFin — same as the baseline. Subsumption of `dsucc m`
into it requires m's s-branch to have shape matching `λq:(F pred). P self`.
-/
def DFinA := och{
  fix F:(dNatA → Type).
    λn:dNatA.
      n (λ_:dNatA. Type)
        Bot
        (λpred:dNatA.
          ι self:dNatA.
            λP:(self → Type).
            λfz:(P self).
            λfs:(λq:(F pred). P self).
            P self)
}

section TestsA

-- dzero into DFin (mirrors the existing DFin result)
example : NbE.subCheck 2000 dzeroA (och{ DFinA done_A }) = .ok true := by native_decide
example : NbE.subCheck 2000 dzeroA (och{ DFinA dtwoA })  = .ok true := by native_decide

-- The target test: done_A ⊑ DFinA dtwoA?  With option A alone this
-- should STILL fail because dsuccA body returns `s m`, typed `P (dsucc m)`,
-- while DFinA's fs returns `P self` (constant, self = dsucc pred).
-- The codomain mismatch (`P (dsucc m)` vs `P self`) remains.
example : NbE.subCheck 4000 done_A (och{ DFinA dtwoA }) = .ok false := by native_decide
-- higher numerals should also fail (same reason, larger bound)
example : NbE.subCheck 8000 dtwoA (och{ DFinA dthreeA }) = .ok false := by native_decide

end TestsA

-- ============================================================
-- OPTION B: change DFin so its fs codomain mirrors dsucc's body type
-- ============================================================
--
-- Give DFin's fs the shape `λq:(F pred). P (dsucc_A pred)` (dependent
-- codomain, referencing dsuccA pred). Then when checking
-- `done_A ⊑ DFinB dtwoA`, both sides have s-branch returning
-- `P (dsucc pred)` where pred is bound — the dependency matches.

/-- DFinB: successor branch's fs-codomain is `P (dsucc pred)`. -/
def DFinB := och{
  fix F:(dNatA → Type).
    λn:dNatA.
      n (λ_:dNatA. Type)
        Bot
        (λpred:dNatA.
          ι self:dNatA.
            λP:(self → Type).
            λfz:(P self).
            λfs:(λq:(F pred). P (dsuccA pred)).
            P self)
}

section TestsB

-- done_A ⊑ DFinB dtwoA? This is the main event for Option B.
-- On the s-branch both sides now return `P (dsucc pred)` where pred
-- binds to the argument passed via s. But: done_A's s has domain
-- `pred:dzeroA` (singleton), DFinB's fs has domain `F pred = F done_A`
-- (a DFin). Contra check: `F done_A ⊑ dzeroA`. Hmm.
-- Since F done_A reduces to ι self:dNatA. … (a value at `dNatA`), and
-- dzeroA is a specific ι, is F done_A ⊑ dzeroA? They have different
-- body shapes so structurally no.
example : NbE.subCheck 4000 done_A (och{ DFinB dtwoA }) = .ok false := by native_decide

-- Sanity: dzero still works
example : NbE.subCheck 2000 dzeroA (och{ DFinB done_A }) = .ok true := by native_decide

end TestsB

-- ============================================================
-- OPTION C: DFin s-domain is pred (singleton on pred!) + P(dsucc pred) codomain
-- ============================================================

/-- DFinC: try to match dsuccA EXACTLY. s-domain is `pred:pred` (singleton),
s-codomain is `P (dsucc pred)`. This would exactly mirror the shape
of `dsuccA pred`. -/
def DFinC := och{
  fix F:(dNatA → Type).
    λn:dNatA.
      n (λ_:dNatA. Type)
        Bot
        (λpred:dNatA.
          ι self:dNatA.
            λP:(self → Type).
            λfz:(P self).
            λfs:(λq:pred. P (dsuccA pred)).
            P self)
}

section TestsC

-- done_A ⊑ DFinC dtwoA?
-- Shape of dsuccA m: `λP. λz:Type. λs:(λpred:m. P (dsuccA pred)). s m`
-- where m = dzeroA for done_A. After ι iotaIntro on DFinC dtwoA
-- (self:=done_A), DFinC dtwoA body becomes:
--   λP:(done_A → Type). λfz:(P done_A). λfs:(λq:done_A. P (dsuccA done_A)). P done_A
-- [since pred binds to done_A here via DFinC's λpred]
-- done_A's body:
--   λP:((dsuccA dzeroA) → Type). λz:Type. λs:(λpred:dzeroA. P (dsuccA pred)). s dzeroA
-- Note dsucc dzeroA ≡ done_A, so P domains match after NbE.
-- s-types: caller sees `λq:done_A. P (dsucc done_A) = P dtwoA`
--          done_A provides `λpred:dzeroA. P (dsuccA pred) = P done_A at call site`
-- Contra: done_A (caller's q domain) ⊑ dzeroA (callee's pred domain).
-- Covariant: P (dsuccA pred) ⊑ P (dsuccA done_A).  This needs pred ≡ done_A.
-- Hmm — pred is a bound variable on the LHS (bound by λpred), done_A is concrete.
-- Subtyping doesn't identify these unless the contra forced pred = done_A.
example : NbE.subCheck 4000 done_A (och{ DFinC dtwoA }) = .ok false := by native_decide

end TestsC

-- ============================================================
-- OPTION F: DFin's fs codomain depends on q, like dsucc's s codomain.
-- ============================================================
--
-- dsucc m's body: λs:(λpred:dNat. P (dsucc pred)). s m
-- Codomain depends on `pred`. Let's make DFin match exactly:
--   DFin (dsucc p) fs: λq:(F p). P (dsucc q)
-- where q is a Fin element. Now both codomain patterns are `P (dsucc x)`
-- for their bound variable x. After pushing a fresh neutral, both bodies
-- become `P (dsucc fresh)` — structurally identical!
--
-- Question: does the OUTER self-reference still work? If self is not
-- referenced in the body (we changed `P self` → `P (dsucc q)`), then
-- dzero ⊑ DFin 1 may fail because dzero's body still uses `P self` with
-- self-sub producing `P dzero`, and DFin successor's body would need to
-- have... wait, dzero's body is `λz:(P self). λs:Type. z` which returns z,
-- typed P self. After self:=dzero, that's P dzero. For DFin's successor
-- branch's fz to accept dzero, we need dzero ⊑ ι self. λP. λfz:(P self). …
-- hmm that's the fz-branch of DFin.
--
-- Actually let me restructure. The *fz*-branch of DFin must match dzero's
-- body (takes z, returns z). The *fs*-branch must match dsucc's body
-- (takes s, returns s m). Both need matching codomains.
--
-- Full encoding:
def DFinF := och{
  fix F:(dNatA → Type).
    λn:dNatA.
      n (λ_:dNatA. Type)
        Bot
        (λpred:dNatA.
          ι self:dNatA.
            λP:(self → Type).
            λfz:(P self).
            λfs:(λq:(F pred). P (dsuccA q)).
            P self)
}

section TestsF

-- dzero ⊑ DFinF 1: Same mechanism as original DFin — fz/self match.
example : NbE.subCheck 2000 dzeroA (och{ DFinF done_A }) = .ok true := by native_decide

-- The main target: done_A ⊑ DFinF dtwoA
-- After iotaIntro on rhs with self:=done_A=dsucc dzero:
--   lhs: λP:(done_A→Type). λz:Type. λs:(λpred:dNatA. P (dsuccA pred)). s dzeroA
--   rhs: λP:(done_A→Type). λfz:(P done_A). λfs:(λq:(F done_A). P (dsuccA q)). P done_A
-- s-branch contra: F done_A ⊑ dNatA  — HOPEFULLY TRUE (Fin ⊑ dNat)
-- s-branch cov: push fresh q; both give P (dsuccA q) — STRUCTURAL MATCH!
-- body: `s dzeroA` vs `P done_A`. Type-ascent on LHS: `s dzeroA` has
--   type `P (dsuccA dzeroA)` = `P done_A` (after reduction) — MATCHES!
example : NbE.subCheck 8000 done_A (och{ DFinF dtwoA }) = .ok true := by native_decide

-- Diagonal rejection: done_A ⊑ DFinF done_A?
-- DFinF done_A = DFinF (dsucc dzeroA) reduces to
--   ι self:dNatA. λP. λfz:(P self). λfs:(λq:(F dzeroA). P (dsuccA q)). P self
-- After iotaIntro self:=done_A:
--   λP:(done_A→Type). λfz:(P done_A). λfs:(λq:(F dzeroA). P (dsuccA q)). P done_A
-- s-branch contra: F dzeroA ⊑ dNatA. F dzeroA = Bot. Bot ⊑ dNatA — TRUE.
-- So the Bot-at-zero-branch means this contra closes too, and the diagonal
-- done_ ⊑ DFin done_ might wrongly PASS. Let's see.
example : NbE.subCheck 8000 done_A (och{ DFinF done_A }) = .ok false := by native_decide

-- Also test dtwo ⊑ DFin dthree (larger case)
example : NbE.subCheck 16000 dtwoA (och{ DFinF dthreeA }) = .ok true := by native_decide

-- Additional diagonal tests
example : NbE.subCheck 16000 dtwoA (och{ DFinF dtwoA }) = .ok false := by native_decide

-- Out-of-bounds: numerals larger than bound
example : NbE.subCheck 8000 done_A (och{ DFinF dzeroA })  = .ok false := by native_decide
example : NbE.subCheck 8000 dtwoA  (och{ DFinF done_A })  = .ok false := by native_decide
example : NbE.subCheck 16000 dtwoA  (och{ DFinF dtwoA })  = .ok false := by native_decide

-- NOTE: DFinF n ⊑ dNatA (type-level subsumption) does NOT hold. This
-- differs from the original DFin test suite — there the tests were about
-- VALUES of DFin (like dzero, DFZ n, DFS n q) being in dNatA, via the
-- `ι self:dNatA` annotation on each CONSTRUCTOR. The TYPE-level
-- `DFinF done_ ⊑ dNatA` was never asserted in the original either;
-- it's not required for indexArrD or similar operations.
example : NbE.subCheck 8000 (och{ DFinF done_A }) dNatA = .ok false := by native_decide
example : NbE.subCheck 16000 (och{ DFinF dtwoA }) dNatA = .ok false := by native_decide

-- dNatA ⊑ DFin (negative)
example : NbE.subCheck 8000 dNatA (och{ DFinF dtwoA }) = .ok false := by native_decide

-- Raw results
#eval NbE.subCheck 8000 done_A (och{ DFinF dtwoA })
#eval NbE.subCheck 8000 done_A (och{ DFinF done_A })
#eval NbE.subCheck 16000 dtwoA (och{ DFinF dthreeA })
#eval NbE.subCheck 16000 dtwoA (och{ DFinF dtwoA })
#eval NbE.subCheck 8000 done_A (och{ DFinF dzeroA })
#eval NbE.subCheck 8000 dtwoA  (och{ DFinF done_A })
#eval NbE.subCheck 8000 (och{ DFinF done_A }) dNatA
#eval NbE.subCheck 16000 (och{ DFinF dtwoA }) dNatA
#eval NbE.subCheck 8000 dNatA (och{ DFinF dtwoA })

end TestsF

-- ============================================================
-- OPTION D: DFin body calls fs on `pred` (not on a DFin argument).
-- Idea: match dsuccA's body `s m` structure exactly.
-- ============================================================
--
-- Here DFin's successor branch is just `λpred. ι self. λP. λfz. λfs:(λq:pred. P self). fs pred`.
-- It's literally the `dsuccA` body with `s` renamed `fs`. So `DFin n` is
-- basically `dsucc (pred n)` re-bound — which means it *is* a singleton, and
-- subsumption with dsuccA just asks structural equality. This collapses
-- the bound-check but lets us see what the structural subsumption looks like.

def DFinD := och{
  fix F:(dNatA → Type).
    λn:dNatA.
      n (λ_:dNatA. Type)
        Bot
        (λpred:dNatA.
          ι self:dNatA.
            λP:(self → Type).
            λfz:Type.
            λfs:(λq:pred. P (dsuccA pred)).
            fs pred)
}

section TestsD

-- done_A ⊑ DFinD dtwoA?  The shapes should be very close:
--   DFinD dtwoA ~= ι self:dNatA. λP. λfz:Type. λfs:(λq:done_A. P (dsuccA done_A)). fs done_A
--   done_A      = ι self (via dNatA ι wrap)? NO -- dsuccA returns a bare λ.
-- dsucc's result is NOT an ι. The lhs has `λP...` with ann inferred as dNatA
-- in iotaIntro, but the rhs is an ι. This MIGHT work via iotaIntro on the rhs
-- with a = done_A (a value inhabiting dNatA).
example : NbE.subCheck 4000 done_A (och{ DFinD dtwoA }) = .ok false := by native_decide

end TestsD

-- ============================================================
-- OPTION E: DFin is structurally identical to dNat, with Bot at the base.
-- ============================================================
--
-- Make DFin EXACTLY dsucc's body, with the fix-base being Bot. If the shape
-- is identical, subsumption reduces to contra on the s-domain, which bottoms
-- out at Bot by width reasoning.

def DFinE := och{
  fix F:(dNatA → Type).
    λn:dNatA.
      n (λ_:dNatA. Type)
        Bot
        -- Successor branch has the SAME shape as dsuccA's body but with
        -- pred constrained to `F pred` via singleton tightening. Here we
        -- tighten: the s-domain is `F pred` (= the recursive bound).
        -- Actually let's just mirror dsuccA's body with F pred in place of pred:
        (λpred:dNatA.
          ι self:dNatA.
            λP:(self → Type).
            λz:Type.
            λs:(λq:(F pred). P (dsuccA pred)).
            s pred)
}

section TestsE

-- This is Option C + change-of-body `s pred` instead of `P self`.
-- Again check done_A ⊑ DFinE dtwoA.
-- After DFin eval:
--   DFinE dtwoA ≃ ι self:dNatA. λP. λz:Type. λs:(λq:(F done_A). P (dsuccA done_A)). s done_A
-- done_A       = λP. λz:Type. λs:(λpred:dzeroA. P (dsuccA pred)). s dzeroA
-- After iotaIntro on rhs with self:=done_A:
--   λP:(done_A→Type). λz:Type. λs:(λq:(F done_A). P (dsuccA done_A)). s done_A
-- Now both sides have `s _` bodies. For the lhs body `s dzeroA` to typecheck
-- against the rhs's `λq:(F done_A). P (dsuccA done_A)` we need dzeroA ⊑ F done_A
-- and P (dsuccA dzeroA) ⊑ P (dsuccA done_A). The latter needs dsuccA dzeroA ≡
-- dsuccA done_A which is FALSE.
-- Note: that covariant premise is what makes this work — the body call
-- sites are `s dzeroA` on lhs vs `s pred=done_A` on rhs. For the lambdas to
-- subsume coinductively, we'd need that `s x` for x:dzeroA and x:done_A
-- agree, which they don't.
--
-- Actually wait — subsumption is lambda-lambda. It doesn't check the
-- BODY application's arguments; it just checks body subsumption after
-- pushing the bound variable. So `s dzeroA ⊑ s done_A` with bound `s`
-- requires `s` to be a function that accepts both domains and returns
-- compatible types. The contra structural arm actually walks the lambda
-- types and pushes a FRESH neutral, so inside the body it won't know the
-- concrete arguments — it'll just compare `s <some neutral>` vs `s <some neutral>`
-- but wait the bodies differ literally.
example : NbE.subCheck 4000 done_A (och{ DFinE dtwoA }) = .ok false := by native_decide

-- Raw result exploration: what does subCheck ACTUALLY return?
-- Check each option's key test, with both `true` and `false` possibilities.
#eval NbE.subCheck 4000 done_A (och{ DFinA dtwoA })
#eval NbE.subCheck 4000 done_A (och{ DFinB dtwoA })
#eval NbE.subCheck 4000 done_A (och{ DFinC dtwoA })
#eval NbE.subCheck 4000 done_A (och{ DFinD dtwoA })
#eval NbE.subCheck 4000 done_A (och{ DFinE dtwoA })

end TestsE

-- ============================================================
-- indexArrD with DFinF + dNatA: the payoff test (conceptual, not
-- elaborated — see note in DNatExp.lean about `och{…}` elaboration
-- time on appendArrays-sized terms).
-- ============================================================

end DNatExp

-- ============================================================
-- Open follow-up: does Option F work with BASELINE dNat?
-- ============================================================
--
-- It's plausible that the Option F trick (dependent fs codomain
-- `P (dsucc q)`) works on baseline dNat too — the singleton tightening
-- of Option A's dsuccA may not be strictly necessary; what matters for
-- the subsumption is the DFin side's codomain pattern. Left as a
-- follow-up: define DFinF over Std.dNat / Std.dsucc and repeat the
-- test battery. If it works, the encoding can be adopted with zero
-- changes to dNat itself, only to DFin.

end Std
