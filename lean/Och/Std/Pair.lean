import Och.Macro
import Och.Eval
import Och.SubCheckVal
import Och.Std.DNat
import Och.Std.Bool
import Och.Std.Unit

/-!
# Och Std: Pair (binary product, Church-style)

The type constructor and the value constructor are separate:

  Pair  A B     = ΠX:Type. (A → B → X) → X        — the type
  pair_ A B a b = ΛX. λk. k a b                    — the constructor
  fst_  p       = p Type (λa. λ_. a)
  snd_  p       = p Type (λ_. λb. b)

`pair_ A B a b ⊑ Pair A B` holds via *type-ascent* through the
continuation `k`: the body `k a b` has synthesised type `X` (from
`k : A → B → X`, after checking `a : A` and `b : B`), and `X ⊑ X`.
This replaces the earlier "Pair is its own constructor" design,
which relied on covariant neutral-app congruence (`k a b ⊑ k A B`)
— sound only when `k` is covariant in both arguments, which is not
guaranteed (`SoundnessAudit.lean`, A1).

`fst_`/`snd_` stay monomorphic at `Pair Type Type`. Any `Pair A B`
coerces to `Pair Type Type` via `A ⊑ Type`, `B ⊑ Type`
(type-in-type, A2), so they accept any pair without explicit type
arguments. The cost is precision: `fst_ p : Type`, not `: A`. For
precise projections, write the eliminator inline (`p A (λa _. a)`).
-/

namespace Std

def Pair := och{
  λA:Type. λB:Type. λX:Type. λk:(A → B → X). X
}

def pair_ := och{
  λA:Type. λB:Type. λa:A. λb:B. λX:Type. λk:(A → B → X). k a b
}

def fst_ := och{
  λp:(Pair Type Type). p Type (λa:Type. λb:Type. a)
}

def snd_ := och{
  λp:(Pair Type Type). p Type (λa:Type. λb:Type. b)
}

private def p12 := och{ pair_ Nat_ Nat_ one_ two_ }

-- ── Positive computation tests ──────────────────────────────

example : concEval 100 (och{ fst_ p12 }) = concEval 100 one_ := by
  native_decide

example : concEval 100 (och{ snd_ p12 }) = concEval 100 two_ := by
  native_decide

-- ── Positive subtype checks ─────────────────────────────────

-- pair_ Nat Nat 1 2 : Pair Nat Nat (via type-ascent through k).
-- Under the unified Nat_ (dNat-style), the subsumption `two_ ⊑ Nat_`
-- on k's second argument needs more fuel (was fuel 100 on Scott Nat).
example : NbE.subCheck 1000 p12 (och{ Pair Nat_ Nat_ }) = .ok true := by
  native_decide

-- pair_ Bool Bool true false : Pair Bool Bool
example : NbE.subCheck 100
    (och{ pair_ Bool Bool true_ false_ })
    (och{ Pair Bool Bool })
  = .ok true := by native_decide

-- fst β-reduces through the constructor: fst (pair_ … true true) ⊑ true
example : NbE.subCheck 100
    (och{ fst_ (pair_ Bool Bool true_ true_) }) true_
  = .ok true := by native_decide

-- fst_ accepts any concrete pair via `Pair A B ⊑ Pair Type Type`
example : NbE.subCheck 100 fst_ (och{ Pair Nat_ Nat_ → Type })
  = .ok true := by native_decide

example : NbE.subCheck 100 snd_ (och{ Pair Nat_ Nat_ → Type })
  = .ok true := by native_decide

-- ── Negative computation tests ──────────────────────────────

example : concEval 100 (och{ fst_ p12 }) ≠ concEval 100 two_ := by
  native_decide

example : concEval 100 (och{ snd_ p12 }) ≠ concEval 100 one_ := by
  native_decide

-- ── Negative subtype checks ─────────────────────────────────

-- `Pair` is covariant in both arguments (the body is the
-- parametric `X`, so the only occurrence of `A`/`B` is in `k`'s
-- domain — contravariant-of-contravariant = covariant). With
-- the bidirectional neutral-app rule this is *soundly* derived,
-- unlike the old `k l r` body (SoundnessAudit A1).
example : NbE.subCheck 200 (och{ Pair zero_ unit_ }) (och{ Pair Nat_ Unit_ })
  = .ok true := by native_decide
-- …and the witness that broke the old encoding is now
-- consistent (substitution principle holds):
example : NbE.subCheck 200
    (och{ (Pair zero_ unit_) (zero_ → Unit_) })
    (och{ (Pair Nat_  Unit_) (zero_ → Unit_) })
  = .ok true := by native_decide

example : NbE.subCheck 100 fst_ Nat_ = .ok false := by native_decide

example : NbE.subCheck 1000 p12 Bool = .ok false := by native_decide

example : NbE.subCheck 100
    (och{ fst_ (pair_ Bool Bool true_ true_) }) false_
  = .ok false := by native_decide

end Std
