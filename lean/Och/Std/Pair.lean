import Och.Macro
import Och.Eval
import Och.EvalSubst
import Och.Std.DNat
import Och.Std.Bool
import Och.Std.Unit
import Och.API

/-!
# Och Std: Pair (binary product, Church-style)

The type constructor and the value constructor are separate:

  Pair  A B     = ΠX:Type. (A → B → X) → X        — the type
  pair_ A B a b = ΛX. λk. k a b                    — the constructor
  fst_  T p     = p T (λa. λ_. a)       — returns T
  snd_  T p     = p T (λ_. λb. b)       — returns T

`pair_ A B a b ⊑ Pair A B` holds via *type-ascent* through the
continuation `k`: the body `k a b` has synthesised type `X` (from
`k : A → B → X`, after checking `a : A` and `b : B`), and `X ⊑ X`.
This replaces the earlier "Pair is its own constructor" design,
which relied on covariant neutral-app congruence (`k a b ⊑ k A B`)
— sound only when `k` is covariant in both arguments, which is not
guaranteed (`SoundnessAudit.lean`, A1).

`fst_ T`/`snd_ T` take a single type parameter `T` for the
component being projected. The other component's type is erased to
`Type` in the domain annotation (`Pair T Type` / `Pair Type T`),
so any concrete pair coerces in via `B ⊑ Type`. This gives precise
return types (`fst_ T p : T`) while keeping call sites lightweight
(only the returned component's type is needed).
-/

namespace Std

def Pair := och{
  λA:Type. λB:Type. λX:Type. λk:(A → B → X). X
}

def pair_ := och{
  λA:Type. λB:Type. λa:A. λb:B. λX:Type. λk:(A → B → X). k a b
}

def fst_ := och{
  λT:Type. λp:(Pair T Type). p T (λa:T. λb:Type. a)
}

def snd_ := och{
  λT:Type. λp:(Pair Type T). p T (λa:Type. λb:T. b)
}

private def p12 := och{ pair_ Nat_ Nat_ one_ two_ }

-- ── Positive computation tests ──────────────────────────────

example : concEval 100 (och{ fst_ Nat_ p12 }) = concEval 100 one_ := by
  native_decide

example : concEval 100 (och{ snd_ Nat_ p12 }) = concEval 100 two_ := by
  native_decide

-- ── Positive subtype checks ─────────────────────────────────

-- pair_ Nat Nat 1 2 : Pair Nat Nat (via type-ascent through k).
-- Under the unified Nat_ (dNat-style), the subsumption `two_ ⊑ Nat_`
-- on k's second argument needs more fuel (was fuel 100 on Scott Nat).
example : Och.checkSubtype 200 p12 (och{ Pair Nat_ Nat_ }) = .ok true := by
  native_decide

-- pair_ Bool Bool true false : Pair Bool Bool
example : Och.checkSubtype 100
    (och{ pair_ Bool Bool true_ false_ })
    (och{ Pair Bool Bool })
  = .ok true := by native_decide

-- fst β-reduces through the constructor: fst Bool (pair_ … true true) ⊑ true
example : Och.checkSubtype 100
    (och{ fst_ Bool (pair_ Bool Bool true_ true_) }) true_
  = .ok true := by native_decide

-- fst_ T accepts any concrete pair whose first component is T
example : Och.checkSubtype 100 (och{ fst_ Nat_ }) (och{ Pair Nat_ Nat_ → Nat_ })
  = .ok true := by native_decide

example : Och.checkSubtype 100 (och{ snd_ Nat_ }) (och{ Pair Nat_ Nat_ → Nat_ })
  = .ok true := by native_decide

-- ── Negative computation tests ──────────────────────────────

example : concEval 100 (och{ fst_ Nat_ p12 }) ≠ concEval 100 two_ := by
  native_decide

example : concEval 100 (och{ snd_ Nat_ p12 }) ≠ concEval 100 one_ := by
  native_decide

-- ── Negative subtype checks ─────────────────────────────────

-- `Pair` is covariant in both arguments (the body is the
-- parametric `X`, so the only occurrence of `A`/`B` is in `k`'s
-- domain — contravariant-of-contravariant = covariant). With
-- the bidirectional neutral-app rule this is *soundly* derived,
-- unlike the old `k l r` body (SoundnessAudit A1).
example : Och.checkSubtype 200 (och{ Pair zero_ unit_ }) (och{ Pair Nat_ Unit_ })
  = .ok true := by native_decide
-- ...and the witness that broke the old encoding is now
-- consistent (substitution principle holds):
example : Och.checkSubtype 200
    (och{ (Pair zero_ unit_) (zero_ → Unit_) })
    (och{ (Pair Nat_  Unit_) (zero_ → Unit_) })
  = .ok true := by native_decide

example : Och.checkSubtype 100 (och{ fst_ Nat_ }) Nat_ = .ok false := by native_decide

example : Och.checkSubtype 200 p12 Bool = .ok false := by native_decide

example : Och.checkSubtype 100
    (och{ fst_ Bool (pair_ Bool Bool true_ true_) }) false_
  = .ok false := by native_decide

end Std
