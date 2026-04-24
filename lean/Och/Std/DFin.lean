import Och.Macro
import Och.Eval
import Och.TyCheck
import Och.SubCheckVal
import Och.Std.DNat

/-!
# Finite sets `DFin n` — dependent index bounded by a dNat (Option F)

`DFin n` is the type of natural numbers strictly less than `n`. It is
the canonical test-bench for dependent types.

```
DFin n = n.elim (λ_:dNat. Type)
          Bot                          -- DFin dzero: uninhabited (primitive)
          (λpred:dNat.                 -- DFin (dsucc pred):
            ι self:dNat.               -- self witnesses DFin ⊑ dNat
              λP:(self → Type).
              λfz:(P self).
              λfs:(λq:(DFin pred). P (dsucc q)).   -- **Option F**: codomain depends on q
              P self)
```

## Option F encoding (winner from `.claude/worktrees/agent-a726638d`)

The Option F insight: make `DFin`'s `fs`-branch return a type that
depends on its `q`-argument (`P (dsucc q)`), rather than the constant
`P self`. Paired with the singleton-tightened `dsucc` (see
`Std/DNat.lean`, Option A), this makes

  `dsucc m ⊑ DFin (dsucc n)` when `m ⊑ n`

hold directly — without a `DFS` wrapper. The key mechanics:

1. `dsucc m`'s body returns `s m`, typed `P (dsucc m)` — depends on m.
2. `DFin (dsucc pred)`'s `fs` under iotaIntro with `self := dsucc m`
   has codomain `P (dsucc q)` — depends on q.
3. The lam-lam structural check on `fs` pushes fresh q on both sides:
   both give `P (dsucc q)` — structural match.
4. `fs` contra: `DFin pred ⊑ m` (via singleton tightening on dsucc).
5. Body `s m ⊑ P self` after iotaIntro `self := dsucc m` reduces to
   `P (dsucc m) ⊑ P (dsucc m)` — refl.

With this encoding, we no longer need separate `DFZ`/`DFS` constructors
— naturals (dzero, done_, dtwo, ...) inhabit `DFin n` directly by
subsumption when they're bounded by n. See `indexArr` below.

## `Bot` (primitive)

The `DFin dzero` branch is the primitive `Bot` type from core
(`Expr.bot`). `Bot ⊑ e` holds universally via `[S-BotL]`, so inside
the zero-length branch of a pattern-match on `n` the index `i:DFin dzero`
discharges any result-type T by `Bot ⊑ T`. Previously this repo used a
definable `DBot = ι b. λ_:Type. b`; the primitive version doesn't have
structural collisions with other ι-shaped values.
-/

namespace Std

-- ============================================================
-- Type (no constructors needed — dNat values subsume directly)
-- ============================================================

/-- `DFin n`, Option F encoding. The `fs`-branch codomain is
`P (dsucc q)` (dependent on the q argument), mirroring `dsucc m`'s
result type `P (dsucc m)`. Paired with the singleton-tightened
`dsucc` (`Std/DNat.lean`, Option A), this gives the `dsucc m ⊑ DFin n`
subsumption directly. -/
def DFin := och{
  fix F:(dNat → Type).
    λn:dNat.
      n (λ_:dNat. Type)
        Bot
        (λpred:dNat.
          ι self:dNat.                    -- self is a dNat (subtype witness)
            λP:(self → Type).
            λfz:(P self).
            λfs:(λq:(F pred). P (dsucc q)).   -- Option F: codomain depends on q
            P self)
}

-- ============================================================
-- Tests: the unified truth table for dNat ⊑ DFin
-- ============================================================

section Tests

-- ── Positive: naturals inhabit DFin n directly (no wrapper) ──
--
-- With Option F's dependent fs-codomain plus Option A's singleton
-- dsucc, naturals subsume into DFin whenever they're < the bound.

example : NbE.subCheck 2000 dzero (och{ DFin done_ })   = .ok true := by native_decide
example : NbE.subCheck 2000 dzero (och{ DFin dtwo })    = .ok true := by native_decide
example : NbE.subCheck 2000 dzero (och{ DFin dthree })  = .ok true := by native_decide
example : NbE.subCheck 4000 done_ (och{ DFin dtwo })    = .ok true := by native_decide
example : NbE.subCheck 8000 done_ (och{ DFin dthree })  = .ok true := by native_decide
example : NbE.subCheck 16000 dtwo  (och{ DFin dthree }) = .ok true := by native_decide

-- ── Negative: diagonal and out-of-bounds rejected ──

-- Diagonal: n ⊄ DFin n (DFin n doesn't contain its own index)
example : NbE.subCheck 8000 done_  (och{ DFin done_ })  = .ok false := by native_decide
example : NbE.subCheck 16000 dtwo   (och{ DFin dtwo })  = .ok false := by native_decide

-- Out-of-bounds: n ⊄ DFin m for n ≥ m
example : NbE.subCheck 8000 done_ (och{ DFin dzero })   = .ok false := by native_decide
example : NbE.subCheck 8000 dtwo  (och{ DFin done_ })   = .ok false := by native_decide
example : NbE.subCheck 16000 dthree (och{ DFin dtwo })  = .ok false := by native_decide

-- dNat itself is too wide to inhabit DFin n.
example : NbE.subCheck 8000 dNat  (och{ DFin dtwo })    = .ok false := by native_decide

-- Width monotonicity: smaller DFin embeds into larger (Option F gives us this)
example : NbE.subCheck 4000 (och{ DFin done_ }) (och{ DFin dtwo })  = .ok true  := by native_decide
-- Larger DFin does NOT embed into smaller (out-of-bounds).
example : NbE.subCheck 2000 (och{ DFin dtwo })  (och{ DFin done_ }) = .ok false := by native_decide

-- Type is not a DFin n.
example : NbE.subCheck 2000 Expr.type (och{ DFin done_ }) = .ok false := by native_decide

-- Bot ⊑ DFin n (via S-BotL, the primitive rule)
example : NbE.subCheck 2000 (och{ Bot }) (och{ DFin dtwo })  = .ok true := by native_decide

-- DFin n ⊑ dNat at the TYPE level does NOT hold (Option F trade-off).
-- This wasn't required by indexArrD or other ops — only value-level
-- subsumption of specific naturals into DFin n matters. Documented
-- in DFinExp.lean's Option F analysis.
example : NbE.subCheck 8000 (och{ DFin done_ }) dNat    = .ok false := by native_decide
example : NbE.subCheck 16000 (och{ DFin dtwo })  dNat   = .ok false := by native_decide

end Tests

end Std
