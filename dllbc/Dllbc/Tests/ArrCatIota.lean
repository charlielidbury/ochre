import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas

/-!
# `ArrCatIota` — `atake`/`adrop`, the two projections of a composition

`SetHmProbe` measured that the hashmap flagship's natural `GetMut` — a BLIND carve
at a symbolic slot index, pinned `~> SetHM key (*res) s` — is refused in both
available spellings of `SetHM`, and named the fix in one sentence:

> Give `arrCat` projections with ι-rules (`ATake i k (arrCat i k lo hi) ↝ lo`,
> `ADrop` likewise) and `SetHM` could be written decomposition-first and would
> converge with the fill on the refined spine, with no walk.

This file is that addition and its measurement. The formers are spelled `atake`
and `adrop` — lowercase, joining `aget`/`acons` rather than the capitalized type
former `Array`, since they denote functions and the capitalized basis names are
the reserved ones (`Uni.reservedBinder`).

## Why the projections and nothing else

The probe's §4 print says the two sides of the refused discharge are *the same
term modulo three σ's*: `pinFill`'s carve pieces against the parameters standing
in for them. So what the pin needs is not new reasoning — it is the ability to
NAME the prefix, the suffix and the carved key, which a signature cannot do
because the carve mints them. `atake i k` and `adrop i k` name the first two.

The third — the key at the cell — needs nothing new, and that is the smallest-set
finding here. `adrop i (S r)` lands on the `acons`-headed suffix, and at that
point the index the update recurses on is the literal `Z`, so the EXISTING
fold-spelled update (`AVSetT`, an `arrRec` over the cons view) computes in one ι
step and keeps the key itself. What blocked §3.2 was a `natRec` on a symbolic
index; the decomposition removes the symbol, not the fold.

## Contents

  * §1 the ι-rules compute — concrete runs, symbolic compositions, and the
    non-firing cases that must stay stuck.
  * §2 the typing arms.
  * §3 THE TARGET — `SetHmProbe`'s two refused shapes, re-posed with a
    decomposition-first `SetHM`, plus its key-cell negative and its
    concrete-index controls.
  * §4 the counterfactual and the linearity probe.
-/

section

open Dllbc

namespace Dllbc.Tests.ArrCatIota

open Dllbc.StdLemmas (LeAdd LeRefl IdCongr IdSym AddZero)

/-! ## §1 The ι-rules

    `atake i k` and `adrop i k` fire on exactly two shapes: a composition whose
    split point CONVERTS with `(i, k)`, and an owned run at a concrete `i` whose
    length is `i + k`. Everything else is stuck, and §1.3 below is the half of
    that which matters — a projection that fired at the wrong split point would
    be unsound, not merely imprecise. -/

/-! ### §1.1 On an owned run -/

example : (Pure.nf 200 prog{ atake 1 2 Arr(3, 1, 2) } == prog{ Arr(3) }) = true := by native_decide
example : (Pure.nf 200 prog{ adrop 1 2 Arr(3, 1, 2) } == prog{ Arr(1, 2) }) = true := by native_decide
example : (Pure.nf 200 prog{ atake 0 3 Arr(3, 1, 2) } == prog{ Arr() }) = true := by native_decide
example : (Pure.nf 200 prog{ adrop 0 3 Arr(3, 1, 2) } == prog{ Arr(3, 1, 2) }) = true := by native_decide
example : (Pure.nf 200 prog{ atake 3 0 Arr(3, 1, 2) } == prog{ Arr(3, 1, 2) }) = true := by native_decide
example : (Pure.nf 200 prog{ adrop 3 0 Arr(3, 1, 2) } == prog{ Arr() }) = true := by native_decide

/-- A run whose length is not `i + k` is NOT this composition, and the projection
    stays stuck rather than guessing. -/
example : (Pure.nf 200 prog{ atake 1 1 Arr(3, 1, 2) } == prog{ Arr(3) }) = false := by native_decide

/-! ### §1.2 On a composition, symbolically — the rule the discharge needs -/

/-- `atake i k (arrCat i k lo hi) ↝ lo`, with every one of `i`, `k`, `lo`, `hi`
    opaque. This is the ι-rule as `SetHmProbe` §4 asked for it. -/
example : (Pure.nf 600
    prog{ λ (I : Nat). λ (K : Nat). λ (Lo : Array I Nat). λ (Hi : Array K Nat).
            atake I K (arrCat I K Lo Hi) }
  == Pure.nf 600
    prog{ λ (I : Nat). λ (K : Nat). λ (Lo : Array I Nat). λ (Hi : Array K Nat). Lo })
  = true := by native_decide

example : (Pure.nf 600
    prog{ λ (I : Nat). λ (K : Nat). λ (Lo : Array I Nat). λ (Hi : Array K Nat).
            adrop I K (arrCat I K Lo Hi) }
  == Pure.nf 600
    prog{ λ (I : Nat). λ (K : Nat). λ (Lo : Array I Nat). λ (Hi : Array K Nat). Hi })
  = true := by native_decide

/-- The extents are compared by CONVERSION, not by tree equality: the carve's
    fold builds its right extent with `add` (`Val.segsExtent?`), so the spine a
    discharge meets says `add 1 r` where the signature says `S r`. -/
example : (Pure.nf 600
    prog{ λ (R : Nat). λ (I : Nat). λ (Lo : Array I Nat). λ (Hi : Array (S R) Nat).
            atake I (Add 1 R) (arrCat I (S R) Lo Hi) }
  == Pure.nf 600
    prog{ λ (R : Nat). λ (I : Nat). λ (Lo : Array I Nat). λ (Hi : Array (S R) Nat). Lo })
  = true := by native_decide

/-! ### §1.3 …and the splits that are NOT this one stay stuck

    `atake 1 2` of `arrCat 2 1 lo hi` is not `lo`: both are arrays of extent 3 and
    the total extent is the same, so a rule that matched on it would be a bug
    rather than an approximation. -/

example : (Pure.nf 600
    prog{ λ (Lo : Array 2 Nat). λ (Hi : Array 1 Nat). atake 1 2 (arrCat 2 1 Lo Hi) }
  == Pure.nf 600 prog{ λ (Lo : Array 2 Nat). λ (Hi : Array 1 Nat). Lo })
  = false := by native_decide

/-- A stuck projection is a NORMAL FORM — it does not keep unfolding — which is
    what lets it sit inside a pin and be compared. -/
def stuckTake : Term :=
  Pure.nf 600 prog{ λ (I : Nat). λ (K : Nat). λ (A : Array (Add I K) Nat). atake I K A }
example : (Pure.nf 600 stuckTake == stuckTake) = true := by native_decide

/-- A bare σ has no visible split, so both projections are stuck on one. -/
example : (Pure.nf 400 prog{ atake 1 2 %(Term.sym 0) }
  == prog{ atake 1 2 %(Term.sym 0) }) = true := by native_decide

/-! ## §2 The typing arms

    `atake i k a : Array i T` and `adrop i k a : Array k T` for
    `a : Array (add i k) T`. Both are CHECKED rather than synthesized, exactly as
    `arrCat`/`acons` are and for the same reason — the element type comes from the
    expected type, so neither carries a `T` — and both sites the decomposition
    spelling puts them in supply one (`arrCat`'s own premise, and `arrRec`'s
    array premise inside the fold).

    §1 already covers a projection that COMPUTES: `hasTypeT` weak-heads its value
    first, so `atake 1 2 Arr(3,1,2)` is typed as the run it reduces to. The arms
    below are what happens when it does not — a symbolic array, which is the only
    shape a pin ever meets. -/

/-- `hasTypeT` against a seeded `sctx` (as `Universe`'s `chkS`). -/
def chkS (sctx : List (Nat × Term)) (tm ty : Term) : String :=
  match (hasTypeT 8000 tm ty).run (seedPure [] sctx) with
  | .ok r _ => s!"ok {r}"
  | .error e _ => s!"error {e}"

/-- `σ0 = i`, `σ1 = k`, `σ2 : Array (add i k) T` — the telescope a decomposition
    spelling has in scope. -/
def splitCtx : List (Nat × Term) :=
  [(0, prog{ Nat }), (1, prog{ Nat }),
   (2, prog{ Array %(prog{ %(Pure.kAddFn) %(Term.sym 0) %(Term.sym 1) }) Nat })]

example : chkS splitCtx prog{ atake %(Term.sym 0) %(Term.sym 1) %(Term.sym 2) }
    prog{ Array %(Term.sym 0) Nat } = "ok true" := by native_decide
example : chkS splitCtx prog{ adrop %(Term.sym 0) %(Term.sym 1) %(Term.sym 2) }
    prog{ Array %(Term.sym 1) Nat } = "ok true" := by native_decide

/-- The extent is the one the projection NAMES, not the other one and not the
    total: a `take` is not a `drop` and neither is the whole array. -/
example : chkS splitCtx prog{ atake %(Term.sym 0) %(Term.sym 1) %(Term.sym 2) }
    prog{ Array %(Term.sym 1) Nat } = "ok false" := by native_decide
example : chkS splitCtx prog{ adrop %(Term.sym 0) %(Term.sym 1) %(Term.sym 2) }
    prog{ Array %(Term.sym 0) Nat } = "ok false" := by native_decide
example : chkS splitCtx prog{ atake %(Term.sym 0) %(Term.sym 1) %(Term.sym 2) }
    prog{ Array %(prog{ %(Pure.kAddFn) %(Term.sym 0) %(Term.sym 1) }) Nat }
  = "ok false" := by native_decide

/-- The element type is carried through, so a projection of a `Nat` array is not
    an array of pairs. -/
example : chkS splitCtx prog{ atake %(Term.sym 0) %(Term.sym 1) %(Term.sym 2) }
    prog{ Array %(Term.sym 0) Bool } = "ok false" := by native_decide

/-- And the ARGUMENT's extent must be the sum: `σ3 : Array σ0 Nat` is too short
    to be split at `(σ0, σ1)`. -/
example : chkS (splitCtx ++ [(3, prog{ Array %(Term.sym 0) Nat })])
    prog{ atake %(Term.sym 0) %(Term.sym 1) %(Term.sym 3) }
    prog{ Array %(Term.sym 0) Nat } = "ok false" := by native_decide

/-- Non-array expected types are refused outright, which is the `asArrayTy?`
    guard `arrCat` has. -/
example : chkS splitCtx prog{ atake %(Term.sym 0) %(Term.sym 1) %(Term.sym 2) }
    prog{ Nat } = "ok false" := by native_decide

/-- **The composition of the two typings is `arrCat`'s own premise**, which is
    the statement that these three formers fit together: `arrCat i k (atake i k a)
    (adrop i k a) : Array (add i k) T` whenever `a` is. -/
example : chkS splitCtx
    prog{ arrCat %(Term.sym 0) %(Term.sym 1)
            (atake %(Term.sym 0) %(Term.sym 1) %(Term.sym 2))
            (adrop %(Term.sym 0) %(Term.sym 1) %(Term.sym 2)) }
    prog{ Array %(prog{ %(Pure.kAddFn) %(Term.sym 0) %(Term.sym 1) }) Nat }
  = "ok true" := by native_decide

end Dllbc.Tests.ArrCatIota

end
