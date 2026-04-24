import Och.Macro
import Och.Eval
import Och.SubCheckVal
import Och.Std.Bool
import Och.Std.Nat
import Och.Std.Unit
import Och.Std.Pair

/-!
# Experimental: Singleton-tightened Dependent Naturals

Research goal: adapt the Scott-Nat singleton trick to the dependent
`dNat`/`DFin` so that `dsucc m ⊑ DFin (dsucc n)` can close without
a DFS wrapper.

This file explores several encodings. See the header of each section
for the hypothesis being tested.

## Baseline (Option 0, same as Std.DNat) for reference

```
dzero = ι self:Type. λP:(self → Type). λz:(P self). λs:Type. z
dNat  = fix N. ι self:N.
  let dsucc = fix dsucc:(N → N).
    λm:N. λP:((dsucc m)→Type). λz:Type. λs:(λpred:N. P (dsucc pred)). s m
  in
  λP:(N→Type). λz:(P dzero). λs:(λpred:N. P (dsucc pred)). P self
dsucc m = λP. λz:Type. λs:(λpred:dNat. P (dsucc pred)). s m
```

Problem: `λpred:dNat` is too wide. When checking `done_ ⊑ DFin (dsucc n)`,
DFin's `s` branch demands `λq:(DFin n). P self`, so contra requires
`DFin n ⊑ dNat` (true — Fin values are Nats) BUT done_'s body calls
`s dzero` with type `P (dsucc dzero)`, while DFin's `s` returns
`P self` (constant). The codomain mismatch is what blocks.

## Option A: singleton `λpred:m`, keep dependent codomain

```
dsucc m = λP. λz:Type. λs:(λpred:m. P (dsucc pred)). s m
```

The s-domain is tightened to the singleton `{m}`. When checking
`dsucc m ⊑ DFin (dsucc n)` structurally, we need
`DFin n ⊑ m` on the contra (DFin's domain vs dsucc's domain).
For `done_ ⊑ DFin dtwo`, that's `DFin done_ ⊑ dzero`. Since done_'s
body calls `s dzero` and that use is typed `P (dsucc dzero)`, we need
codomain ≡ ...

We also need dNat's internal copy of dsucc to match.

## Option B: match DFin's s-codomain — dsucc returns `P self` style

Keep dsucc's body as an ι with `self:A` so the codomain is `P self`:

```
dsucc m = ι self:?.
  λP:(self → Type). λz:Type. λs:(λpred:?. P self). s m
```

Then we still need `ι self` and DFin's `ι self:dNat` to line up.
-/

namespace Std

namespace DNatExp

-- ============================================================
-- OPTION A: Singleton-tighten dsucc's s-domain to m itself
-- ============================================================

-- dzero unchanged (no s-branch to tighten).
def dzeroA := och{
  ι self. λP:(self → Type). λz:(P self). λs:Type. z
}

/-- Singleton-tightened dNat: s-branch domain is `pred:N` (= dNat).
Note the outer eliminator's s-branch still uses `λpred:N` since it
has to accept any dNat predecessor, not a specific one. -/
def dNatA := och{
  fix N. ι self:N.
    let dsucc = fix dsucc:(N → N).
      λm:N. λP:((dsucc m) → Type). λz:Type. λs:(λpred:m. P (dsucc pred)). s m in
    λP:(N → Type). λz:(P dzeroA). λs:(λpred:N. P (dsucc pred)). P self
}

/-- Top-level dsucc for Option A: singleton `pred:m`. -/
def dsuccA := och{
  fix dsucc:(dNatA → dNatA).
    λm:dNatA. λP:((dsucc m) → Type). λz:Type. λs:(λpred:m. P (dsucc pred)). s m
}

def done_A := och{ dsuccA dzeroA }
def dtwoA  := och{ dsuccA done_A }
def dthreeA := och{ dsuccA dtwoA }

-- Smoke: do numerals still subsume dNatA?
example : NbE.subCheck 400 dzeroA dNatA = .ok true := by native_decide
example : NbE.subCheck 400 done_A dNatA = .ok true := by native_decide
example : NbE.subCheck 800 dtwoA  dNatA = .ok true := by native_decide

-- Negative sanity
example : NbE.subCheck 400 dNatA dzeroA = .ok false := by native_decide
example : NbE.subCheck 400 dzeroA done_A = .ok false := by native_decide

-- Larger numerals
example : NbE.subCheck 1600 dthreeA dNatA = .ok true := by native_decide

-- isZero: non-dependent case analysis
def disZeroA := och{
  λn:dNatA. n (λ_:dNatA. Std.Bool) Std.true_ (λpred:dNatA. Std.false_)
}

example : concEval 200 (och{ disZeroA dzeroA }) = some Std.true_ := by native_decide
example : concEval 200 (och{ disZeroA done_A }) = some Std.false_ := by native_decide
example : concEval 200 (och{ disZeroA dtwoA }) = some Std.false_ := by native_decide

-- predecessor
def dpredA := och{
  λn:dNatA. n (λ_:dNatA. dNatA) dzeroA (λpred:dNatA. pred)
}

example : concEval 200 (och{ dpredA dzeroA }) = concEval 200 dzeroA := by native_decide
example : concEval 200 (och{ dpredA done_A }) = concEval 200 dzeroA := by native_decide
example : concEval 200 (och{ dpredA dtwoA }) = concEval 200 done_A := by native_decide

-- Dependent elimination test
private def depMotiveA := och{
  λn:dNatA. n (λ_:dNatA. Type) Nat_ (λpred:dNatA. Std.Bool)
}

example : concEval 200 (och{ depMotiveA dzeroA }) = concEval 200 Nat_ := by native_decide
example : concEval 200 (och{ depMotiveA done_A }) = concEval 200 Std.Bool := by native_decide

-- dadd over option-A dNat
def daddA := och{
  fix dadd:(dNatA → dNatA → dNatA).
    λn:dNatA. λm:dNatA.
      n (λ_:dNatA. dNatA) m (λpred:dNatA. dsuccA (dadd pred m))
}

-- NOTE: `daddA done_A dtwoA = dthreeA` DOES pass but the native_decide
-- takes ~5 minutes to elaborate. Verified once; left commented to keep
-- builds fast during iteration.
-- example : concEval 2000 (och{ daddA done_A dtwoA }) = concEval 2000 dthreeA := by native_decide

-- ============================================================
-- Array over dNatA (the appendArrays target)
-- ============================================================

def Array_A := och{
  fix Arr:(dNatA → Type → Type).
    λn:dNatA. λT:Type.
      n (λ_:dNatA. Type) Unit_ (λpred:dNatA. Pair T (Arr pred T))
}

-- Array_A dzero = Unit
example : NbE.nf 200 (och{ Array_A dzeroA Nat_ }) = NbE.nf 200 Unit_ := by native_decide
-- Array_A 1 = Pair Nat Unit
example : NbE.nf 400 (och{ Array_A done_A Nat_ }) = NbE.nf 400 (och{ Pair Nat_ Unit_ }) := by
  native_decide

-- appendArrays using Option-A dNat with the dependent motive that requires
-- genuine dependent elimination (what Scott Nat couldn't do).
--
-- NOTE: The `och{…}` macro elaboration of this specific expression takes
-- a very long time (unfolds many `fix`/`ι`/let layers). The conceptual
-- shape is identical to Array.lean's `appendArrays`; we omit it here
-- because it doesn't add semantic value to the research question beyond
-- "operations compose as they did in the original". The research question
-- is specifically about subtype structure, which lives in DFinExp.lean.
--
-- def appendArraysA := och{
--   fix self:(λT:Type. λn1:dNatA. λn2:dNatA. Array_A n1 T → Array_A n2 T → Array_A (daddA n1 n2) T).
--     λT:Type. λn1:dNatA. λn2:dNatA. λarr1:(Array_A n1 T). λarr2:(Array_A n2 T).
--       n1
--         (λn:dNatA. Array_A n T → Array_A (daddA n n2) T)
--         (λarr:(Array_A dzeroA T). arr2)
--         (λpred:dNatA. λarr:(Array_A (dsuccA pred) T).
--           pair_ T (Array_A (daddA pred n2) T)
--             (fst_ arr) (self T pred n2 (snd_ arr) arr2))
--         arr1
-- }

end DNatExp

end Std
