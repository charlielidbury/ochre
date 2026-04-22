import Och.Macro
import Och.Eval
import Och.SubCheckVal
import Och.TyCheck
import Och.Std.Nat

/-!
# Finite sets `Fin n` as a subtype of `Nat`

The non-dependent variant of `DFin`. `Fin n` shares `Nat`'s eliminator
interface — same three-argument Scott shape — so every `Fin n` value
flows naturally into any `Nat`-consuming context. The only difference
is `s`'s domain: `Nat` takes a `Nat` as the predecessor, `Fin (succ p)`
takes a `Fin p`.

```
Nat = fix N. λX:Type. λz:X. λs:(N → X). X

Fin = fix F:(Nat → Type). λn:Nat.
  n Type
    Bot                                       -- Fin zero (primitive!)
    (λp:Nat. λX:Type. λz:X. λs:(F p → X). X)  -- Fin (succ p)
```

## What subtypings hold

- **`Fin n ⊑ Nat`** — every Fin value is a Nat. The contra chain
  `Fin (succ p) ⊑ Nat` → `F p ⊑ Nat` recurses on the predecessor and
  bottoms at `Bot ⊑ Nat`, which holds by `[S-BotL]` (Bot is the
  universal lower bound).
- **`Fin m ⊑ Fin n` for `m ≤ n`** — width-monotonicity. Fin is
  literally "values less than n" as a subset, so smaller-indexed Fins
  embed into larger ones.

## Specific Nat constructors flow into Fin

Because `Std.Nat` uses the **singleton encoding** (each numeral's
`s`-type is its predecessor value), the individual numerals `zero_`,
`one_`, `two_`, ... are naturally subtypes of `Fin n` for large-enough
`n`. No `FZ`/`FS` wrappers needed — just write the Nat literal and
subsumption does the work.

## What doesn't hold (and correctly)

- **`Fin n ⊄ Fin m` for `n > m`** — a value in Fin 3 may exceed
  Fin 2's bound, so no subtype.
- **`Nat ⊄ Fin n`** — most Nats are too big.
- **`n_ ⊄ Fin m_` for `n_ > m_`** — a specific numeral that exceeds
  the bound is rejected.

## Bot as primitive

`Bot` is now a primitive of the core calculus (`Expr.bot`), with the
declarative `[S-BotL]` rule `Bot ⊑ e` and a single algorithmic arm
`| .bot, _ => .ok true`. This replaces the previous definable
`fix B. λX:Type. λz:X. λs:(B → X). s B` hack, which worked but was
fragile to changes in Scott numerals or the subtype algorithm.
See `docs/ideas/bottom.md`.
-/

namespace Std

-- ============================================================
-- Bottom (for the Fin zero branch)
-- ============================================================

/-- Bot: primitive bottom type. `Bot ⊑ e` for every `e` via `[S-BotL]`.

Previously encoded definably as
`fix B. λX:Type. λz:X. λs:(B → X). s B`; the primitive version
removes the fragility of that encoding (structural collisions with
other Scott-shaped values under subtype changes). -/
def «Bot» := och{ Bot }

-- ============================================================
-- Fin type and constructors
-- ============================================================

def Fin := och{
  fix F:(Nat_ → Type). λn:Nat_.
    n Type
      Bot
      (λp:Nat_. λX:Type. λz:X. λs:((F p) → X). X)
}

-- Note: no `FZ`/`FS` constructors. With the singleton-encoded Scott
-- numerals from `Std.Nat`, `zero_` naturally inhabits `Fin n` for
-- n ≥ 1, `one_` inhabits `Fin n` for n ≥ 2, etc., via the width-
-- monotonicity subtyping. So you just write the Nat literal; no
-- wrapping needed.

-- ============================================================
-- Tests
-- ============================================================

section Tests

-- ── The user-requested subtyping tests ──
--
-- With the singleton encoding of Scott numerals (each numeral's
-- `s`-type is its predecessor value), specific Nat numerals now
-- flow into both `Nat` and `Fin n` for large-enough `n`.

-- YES: `two_ ⊑ Nat`
example : NbE.subCheck 2000 two_ Nat_ = .ok true := by native_decide

-- YES: `two_ ⊑ Fin four_`
example : NbE.subCheck 4000 two_ (och{ Fin four_ }) = .ok true := by native_decide

-- NO: `two_ ⊑ Fin one_` (2 exceeds Fin 1's bound of {0})
example : NbE.subCheck 2000 two_ (och{ Fin one_ }) = .ok false := by native_decide

-- YES: `Fin three_ ⊑ Nat` (every Fin value is a Nat)
example : NbE.subCheck 4000 (och{ Fin three_ }) Nat_ = .ok true := by native_decide

-- NO: `Nat ⊑ Fin three_` (not every Nat is bounded)
example : NbE.subCheck 2000 Nat_ (och{ Fin three_ }) = .ok false := by native_decide

-- NO: `one_ ⊑ Fin zero_` — correctly rejected (unlike what we feared,
-- the Bot issue doesn't propagate here because `one_`'s body calls
-- `s` on a concrete argument, and the resulting type-ascent step
-- `X ⊑ z-variable` can't close). Good.
example : NbE.subCheck 2000 one_ (och{ Fin zero_ }) = .ok false := by native_decide

-- NO: the "equal index" diagonal — `n_ ⊑ Fin n_` should fail
-- (Fin n doesn't contain its own index as a value). Previously these
-- passed wrongly because the old Bot (`fix B. λX. λz:X. λs:(B → X). z`)
-- had the same body shape as `zero_`, so `zero_ ⊑ Bot` closed
-- structurally and cascaded.
--
-- The fix: give Bot a body that no Scott numeral can match —
-- `s B` (the fix self-reference fed into its own eliminator). That
-- infinite self-recursion doesn't match any terminating numeral,
-- so `zero_ ⊄ Bot` and the diagonal is correctly rejected.
example : NbE.subCheck 2000 zero_ (och{ Fin zero_ }) = .ok false := by native_decide
example : NbE.subCheck 2000 one_  (och{ Fin one_  }) = .ok false := by native_decide
example : NbE.subCheck 2000 two_  (och{ Fin two_  }) = .ok false := by native_decide

-- ============================================================
-- Primitive Bot: dedicated tests (docs/ideas/bottom.md)
-- ============================================================

-- Bot ⊑ everything ([S-BotL])
example : NbE.subCheck 200 «Bot» Nat_                    = .ok true := by native_decide
example : NbE.subCheck 200 «Bot» Std.Bool                = .ok true := by native_decide
example : NbE.subCheck 200 «Bot» (och{ Fin three_ })     = .ok true := by native_decide
example : NbE.subCheck 200 «Bot» Expr.type               = .ok true := by native_decide
-- Refl (via the S-BotL arm, which fires before structural)
example : NbE.subCheck 200 «Bot» «Bot»                   = .ok true := by native_decide
-- Only Bot ⊑ Bot on the RHS (no dual `_, .bot => .ok false` rule;
-- rejection emerges from fall-through)
example : NbE.subCheck 200 Nat_     «Bot»                = .ok false := by native_decide
example : NbE.subCheck 200 zero_    «Bot»                = .ok false := by native_decide
example : NbE.subCheck 200 Expr.type «Bot»               = .ok false := by native_decide

-- Bidirectional restriction: tyCheck accepts Bot at type `Type`;
-- rejects it at a non-Type type. (The rejection at non-Type types
-- emerges as `.error` via the tyInfer fallback, not `.ok false` —
-- tyInfer errors on `.bot`, and tyCheckFallback propagates that.)
example : NbE.typeCheck 200 (och{ Bot }) Expr.type = .ok true := by native_decide
example : (NbE.typeCheck 200 (och{ Bot }) Nat_).isOk = false := by native_decide

-- tyInfer rejects Bot as a value (no synthesized type).
example : (NbE.tyInfer 200 #[] [] (och{ Bot })).isOk = false := by native_decide

end Tests

end Std
