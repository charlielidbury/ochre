import Och.Macro
import Och.Eval
import Och.SubCheckVal
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
Bot = fix B. λX:Type. λz:X. λs:(B → X). z    -- Nat-shaped bottom

Fin = fix F:(Nat → Type). λn:Nat.
  n Type
    Bot                                       -- Fin zero
    (λp:Nat. λX:Type. λz:X. λs:(F p → X). X)  -- Fin (succ p)
```

## What subtypings hold

- **`Fin n ⊑ Nat`** — every Fin value is a Nat. The contra chain
  `Fin (succ p) ⊑ Nat` → `F p ⊑ Nat` recurses on the predecessor and
  bottoms at `Bot ⊑ Nat`, which holds because `Bot` is shape-matched
  to `Nat` (fix + same three-argument Scott body, body returns `z`).
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

## Bot encoding: a self-recursing body to break the zero-collision

Bot is `fix B. λX:Type. λz:X. λs:(B → X). s B` — the body `s B` feeds
the fix itself into its own eliminator, an infinite self-recursion.
This is load-bearing: an earlier version with body `z` (structurally
identical to `zero_`'s body) made `zero_ ⊑ Bot` pass algorithmically,
which cascaded into the `n_ ⊑ Fin n_` diagonal all passing wrongly.
The `s B` body has no terminating Scott-numeral match, so the
collision is broken, while `Bot ⊑ Nat` still closes because the
contra recursion lets seen-set coinduction fire and the body `s B`
type-ascends to `X` through `s : Bot → X`.
-/

namespace Std

-- ============================================================
-- Bottom (for the Fin zero branch)
-- ============================================================

/-- Bot: Nat-shaped so `Bot ⊑ Nat` closes, but with a self-referential
body `s B` that distinguishes it structurally from `zero_` (whose body
is just `z`).

An earlier version used body `z` and ran into the "off-by-one"
diagonal — `zero_ ⊑ Bot` closed algorithmically because both sides
had the same shape, which then cascaded to `n_ ⊑ Fin n_` all passing
wrongly. Changing the body to `s B` — the fix self-reference fed back
into its own eliminator — forces an infinite recursion that no
terminating Scott numeral's body matches, while `Bot ⊑ Nat` still
closes via seen-set coinduction on the contra chain (the body check
passes by type-ascent through `s`). -/
def Bot := och{ fix B. λX:Type. λz:X. λs:(B → X). s B }

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

end Tests

end Std
