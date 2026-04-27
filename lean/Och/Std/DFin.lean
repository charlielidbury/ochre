import Och.Macro
import Och.Eval
import Och.TyCheck
import Och.SubCheckVal
import Och.Std.DNat
import Och.TypedNbE
import Och.EvalSubst

/-!
# Finite sets `Fin n` — bounded by `Nat_` (Option F)

`Fin n` is the type of natural numbers strictly less than `n`. It's the
canonical test-bench for dependent types.

```
Fin n = n.elim (λ_:Nat_. Type)
         Bot                            -- Fin zero_: uninhabited (primitive)
         (λpred:Nat_.                   -- Fin (succ_ pred):
           ι self:Nat_.                 -- self witnesses Fin ⊑ Nat_
             λP:(self → Type).
             λfz:(P self).
             λfs:(λq:(Fin pred). P (succ_ q)).   -- **Option F**: codomain depends on q
             P self)
```

## Option F encoding

The `fs`-branch codomain is `P (succ_ q)` (dependent on q), rather than
the constant `P self`. Paired with the singleton-tightened `succ_` (see
`Std/DNat.lean`, Option A), this gives `succ_ m ⊑ Fin (succ_ n)` when
`m ⊑ n` directly — without `FZ`/`FS` wrappers.

Mechanics: after iotaIntro with `self := succ_ m`, both sides'
`fs`-codomain read `P (succ_ q)` under a fresh q, which structurally
matches. The contra on `fs`'s domain (`Fin pred ⊑ m`) leverages Option
A's singleton.

## Unified Nat/Fin

Naturals flow into Fin by subsumption: write the Nat literal at a
Fin-typed position and the subtype check carries it. No separate
constructors needed. See `indexArr` in `Std/Array.lean` for the payoff.

## `Bot` (primitive)

The `Fin zero_` branch is primitive `Bot` (`Expr.bot`). `Bot ⊑ e`
universally via `[S-BotL]`, so in the `Fin zero_` branch of a
pattern-match, `i : Fin zero_` discharges any result-type T.
-/

namespace Std

def Fin := och{
  fix F:(Nat_ → Type).
    λn:Nat_.
      n (λ_:Nat_. Type)
        Bot
        (λpred:Nat_.
          ι self:Nat_.
            λP:(self → Type).
            λfz:(P self).
            λfs:(λq:(F pred). P (succ_ q)).   -- Option F: codomain depends on q
            P self)
}

-- ============================================================
-- Truth table: naturals inhabit Fin by subsumption
-- ============================================================

section Tests

-- ── Positive: naturals inhabit Fin n directly (no wrapper) ──

example : SubstEval.subCheckT 2000 zero_ (och{ Fin one_ })    = .ok true := by native_decide
example : SubstEval.subCheckT 2000 zero_ (och{ Fin two_ })    = .ok true := by native_decide
example : SubstEval.subCheckT 2000 zero_ (och{ Fin three_ })  = .ok true := by native_decide
example : SubstEval.subCheckT 4000 one_  (och{ Fin two_ })    = .ok true := by native_decide
example : SubstEval.subCheckT 8000 one_  (och{ Fin three_ })  = .ok true := by native_decide

-- `two_ ⊑ Fin three_` was previously commented because env-based subCheck
-- couldn't close it at any tractable fuel. The production substitution-
-- based `SubstEval.subCheckT` (lean/Och/EvalSubst.lean, see
-- docs/ideas/eval-subst-vs-env-benchmark.md §6) closes it in ~35 ms.
-- The env-based `NbE.subCheckT` *also* now closes (~320 ms) but at the
-- cost of significant native_decide elaboration time at this fuel; we
-- only check the subst path here as the production test.
example : SubstEval.subCheckT 16000 two_ (och{ Fin three_ }) = .ok true := by native_decide

-- ── Negative: diagonal and out-of-bounds rejected ──

-- Diagonal: n ⊄ Fin n
example : SubstEval.subCheckT 8000 one_   (och{ Fin one_ })   = .ok false := by native_decide
example : SubstEval.subCheckT 16000 two_  (och{ Fin two_ }) = .ok false := by native_decide

-- Out-of-bounds: n ⊄ Fin m for n ≥ m
example : SubstEval.subCheckT 8000 one_  (och{ Fin zero_ })   = .ok false := by native_decide
example : SubstEval.subCheckT 8000 two_  (och{ Fin one_ })    = .ok false := by native_decide
example : SubstEval.subCheckT 16000 three_ (och{ Fin two_ }) = .ok false := by native_decide

-- Nat_ itself is too wide to inhabit Fin n.
example : SubstEval.subCheckT 8000 Nat_  (och{ Fin two_ })    = .ok false := by native_decide

-- Width monotonicity: smaller Fin embeds into larger.
example : SubstEval.subCheckT 4000 (och{ Fin one_ }) (och{ Fin two_ })  = .ok true := by native_decide
example : SubstEval.subCheckT 2000 (och{ Fin two_ }) (och{ Fin one_ })  = .ok false := by native_decide

-- Type is not a Fin n.
example : SubstEval.subCheckT 2000 Expr.type (och{ Fin one_ })    = .ok false := by native_decide

-- Bot ⊑ Fin n (via S-BotL, the primitive rule).
example : SubstEval.subCheckT 2000 (och{ Bot }) (och{ Fin two_ })  = .ok true := by native_decide

-- Fin n ⊑ Nat_ at the TYPE level does NOT hold (Option F tradeoff).
-- Not required by indexArr / other ops — only value-level subsumption
-- of specific naturals into Fin n matters in practice.
example : SubstEval.subCheckT 8000 (och{ Fin one_ }) Nat_     = .ok false := by native_decide

end Tests

end Std
