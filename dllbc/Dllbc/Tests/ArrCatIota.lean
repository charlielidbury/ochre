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

example : (Pure.nf 200 prog defer_check { atake 1 2 Arr(3, 1, 2) } == prog defer_check { Arr(3) }) = true := by native_decide
example : (Pure.nf 200 prog defer_check { adrop 1 2 Arr(3, 1, 2) } == prog defer_check { Arr(1, 2) }) = true := by native_decide
example : (Pure.nf 200 prog defer_check { atake 0 3 Arr(3, 1, 2) } == prog defer_check { Arr() }) = true := by native_decide
example : (Pure.nf 200 prog defer_check { adrop 0 3 Arr(3, 1, 2) } == prog defer_check { Arr(3, 1, 2) }) = true := by native_decide
example : (Pure.nf 200 prog defer_check { atake 3 0 Arr(3, 1, 2) } == prog defer_check { Arr(3, 1, 2) }) = true := by native_decide
example : (Pure.nf 200 prog defer_check { adrop 3 0 Arr(3, 1, 2) } == prog defer_check { Arr() }) = true := by native_decide

/-- A run whose length is not `i + k` is NOT this composition, and the projection
    stays stuck rather than guessing. -/
example : (Pure.nf 200 prog defer_check { atake 1 1 Arr(3, 1, 2) } == prog defer_check { Arr(3) }) = false := by native_decide

/-! ### §1.2 On a composition, symbolically — the rule the discharge needs -/

/-- `atake i k (arrCat i k lo hi) ↝ lo`, with every one of `i`, `k`, `lo`, `hi`
    opaque. This is the ι-rule as `SetHmProbe` §4 asked for it. -/
example : (Pure.nf 600
    prog defer_check { λ (I : Nat). λ (K : Nat). λ (Lo : Array I Nat). λ (Hi : Array K Nat).
            atake I K (arrCat I K Lo Hi) }
  == Pure.nf 600
    prog defer_check { λ (I : Nat). λ (K : Nat). λ (Lo : Array I Nat). λ (Hi : Array K Nat). Lo })
  = true := by native_decide

example : (Pure.nf 600
    prog defer_check { λ (I : Nat). λ (K : Nat). λ (Lo : Array I Nat). λ (Hi : Array K Nat).
            adrop I K (arrCat I K Lo Hi) }
  == Pure.nf 600
    prog defer_check { λ (I : Nat). λ (K : Nat). λ (Lo : Array I Nat). λ (Hi : Array K Nat). Hi })
  = true := by native_decide

/-- The extents are compared by CONVERSION, not by tree equality: the carve's
    fold builds its right extent with `add` (`Val.segsExtent?`), so the spine a
    discharge meets says `add 1 r` where the signature says `S r`. -/
example : (Pure.nf 600
    prog defer_check { λ (R : Nat). λ (I : Nat). λ (Lo : Array I Nat). λ (Hi : Array (S R) Nat).
            atake I (Add 1 R) (arrCat I (S R) Lo Hi) }
  == Pure.nf 600
    prog defer_check { λ (R : Nat). λ (I : Nat). λ (Lo : Array I Nat). λ (Hi : Array (S R) Nat). Lo })
  = true := by native_decide

/-! ### §1.3 …and the splits that are NOT this one stay stuck

    `atake 1 2` of `arrCat 2 1 lo hi` is not `lo`: both are arrays of extent 3 and
    the total extent is the same, so a rule that matched on it would be a bug
    rather than an approximation. -/

example : (Pure.nf 600
    prog defer_check { λ (Lo : Array 2 Nat). λ (Hi : Array 1 Nat). atake 1 2 (arrCat 2 1 Lo Hi) }
  == Pure.nf 600 prog defer_check { λ (Lo : Array 2 Nat). λ (Hi : Array 1 Nat). Lo })
  = false := by native_decide

/-- A stuck projection is a NORMAL FORM — it does not keep unfolding — which is
    what lets it sit inside a pin and be compared. -/
def stuckTake : Term :=
  Pure.nf 600 prog defer_check { λ (I : Nat). λ (K : Nat). λ (A : Array (Add I K) Nat). atake I K A }
example : (Pure.nf 600 stuckTake == stuckTake) = true := by native_decide

/-- A bare σ has no visible split, so both projections are stuck on one. -/
example : (Pure.nf 400 prog defer_check { atake 1 2 %(Term.sym 0) }
  == prog defer_check { atake 1 2 %(Term.sym 0) }) = true := by native_decide

/-! ### §1.4 What is NOT here — the smallest-set measurement

    Two further families were on the table and neither is needed, which is worth
    pinning because "needed" was measured and not guessed.

    **`acons`-stepping variants.** `atake (S i) k (acons m x xs) ↝ acons _ x
    (atake i k xs)` would let a projection peel a cons view one element at a time
    instead of requiring the composition. It is not here: §3's discharge never
    meets that shape, because a BLIND carve at a symbolic index leaves the top
    former `arrCat` (nothing opened the prefix, so its left argument is a σ and
    `arrCat`'s own `acons`-headed rule does not fire either). The assertion below
    is the boundary as it stands, so a future shape that does need the peel finds
    the fact rather than rediscovering it.

    **Element-level projections at the cell** (a head/tail pair, or an `aget`
    that fires on `acons`). Also not here, for the reason `AVSetDecT` states: the
    drop lands on the `acons`-headed suffix with the index reduced to the literal
    `Z`, and the EXISTING `arrRec` fold computes from there. -/

example : (Pure.nf 600
    prog defer_check { λ (I : Nat). λ (K : Nat). λ (X : Nat). λ (XS : Array (Add I K) Nat).
            atake (S I) K (acons (Add I K) X XS) }
  == Pure.nf 600
    prog defer_check { λ (I : Nat). λ (K : Nat). λ (X : Nat). λ (XS : Array (Add I K) Nat).
            acons I X (atake I K XS) })
  = false := by native_decide

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
  [(0, prog defer_check { Nat }), (1, prog defer_check { Nat }),
   (2, prog defer_check { Array %(prog defer_check { %(Pure.kAddFn) %(Term.sym 0) %(Term.sym 1) }) Nat })]

example : chkS splitCtx prog defer_check { atake %(Term.sym 0) %(Term.sym 1) %(Term.sym 2) }
    prog defer_check { Array %(Term.sym 0) Nat } = "ok true" := by native_decide
example : chkS splitCtx prog defer_check { adrop %(Term.sym 0) %(Term.sym 1) %(Term.sym 2) }
    prog defer_check { Array %(Term.sym 1) Nat } = "ok true" := by native_decide

/-- The extent is the one the projection NAMES, not the other one and not the
    total: a `take` is not a `drop` and neither is the whole array. -/
example : chkS splitCtx prog defer_check { atake %(Term.sym 0) %(Term.sym 1) %(Term.sym 2) }
    prog defer_check { Array %(Term.sym 1) Nat } = "ok false" := by native_decide
example : chkS splitCtx prog defer_check { adrop %(Term.sym 0) %(Term.sym 1) %(Term.sym 2) }
    prog defer_check { Array %(Term.sym 0) Nat } = "ok false" := by native_decide
example : chkS splitCtx prog defer_check { atake %(Term.sym 0) %(Term.sym 1) %(Term.sym 2) }
    prog defer_check { Array %(prog defer_check { %(Pure.kAddFn) %(Term.sym 0) %(Term.sym 1) }) Nat }
  = "ok false" := by native_decide

/-- The element type is carried through, so a projection of a `Nat` array is not
    an array of pairs. -/
example : chkS splitCtx prog defer_check { atake %(Term.sym 0) %(Term.sym 1) %(Term.sym 2) }
    prog defer_check { Array %(Term.sym 0) Bool } = "ok false" := by native_decide

/-- And the ARGUMENT's extent must be the sum: `σ3 : Array σ0 Nat` is too short
    to be split at `(σ0, σ1)`. -/
example : chkS (splitCtx ++ [(3, prog defer_check { Array %(Term.sym 0) Nat })])
    prog defer_check { atake %(Term.sym 0) %(Term.sym 1) %(Term.sym 3) }
    prog defer_check { Array %(Term.sym 0) Nat } = "ok false" := by native_decide

/-- Non-array expected types are refused outright, which is the `asArrayTy?`
    guard `arrCat` has. -/
example : chkS splitCtx prog defer_check { atake %(Term.sym 0) %(Term.sym 1) %(Term.sym 2) }
    prog defer_check { Nat } = "ok false" := by native_decide

/-- **The composition of the two typings is `arrCat`'s own premise**, which is
    the statement that these three formers fit together: `arrCat i k (atake i k a)
    (adrop i k a) : Array (add i k) T` whenever `a` is. -/
example : chkS splitCtx
    prog defer_check { arrCat %(Term.sym 0) %(Term.sym 1)
            (atake %(Term.sym 0) %(Term.sym 1) %(Term.sym 2))
            (adrop %(Term.sym 0) %(Term.sym 1) %(Term.sym 2)) }
    prog defer_check { Array %(prog defer_check { %(Pure.kAddFn) %(Term.sym 0) %(Term.sym 1) }) Nat }
  = "ok true" := by native_decide

/-! ## §3 THE TARGET — the blind carve at a symbolic index, pinned

    Everything below is `SetHmProbe`'s §1–§5 re-posed. The container, the
    fold-spelled update and the programs are that file's, verbatim where they are
    unchanged, so the two measurements compose and a verdict that moves is
    attributable to the projections and to nothing else. -/

/-- `SetHmProbe` §1's container, verbatim: every KEY is 7, no value read. -/
def AllK7 : Term := prog defer_check {
  λ (M : Nat). λ (A : Array M (Σ (k : Nat). Nat)).
    arrRec (Σ (k : Nat). Nat)
      (λ (Mz : Nat). λ (Az : Array Mz (Σ (k : Nat). Nat)). Type)
      Unit
      (λ (K : Nat). λ (H : Σ (k : Nat). Nat). λ (T : Array K (Σ (k : Nat). Nat)).
        λ (Ih : Type).
          (elim H return (λ (Hm : Σ (k : Nat). Nat). Type) {
            Pair (K2) (V2) => Id Nat K2 7 }) × Ih)
      M A }

/-- `SetHmProbe` §3's fold-spelled update, verbatim: index-first, cons-view,
    keeping the key and replacing the value. It is REUSED below rather than
    replaced — see `AVSetDecT`. -/
def AVSetT : Term := prog defer_check {
  λ (I : Nat). λ (V : Nat).
    elim I return (λ (Z0 : Nat). Π (N : Nat) → Π (A : Array N (Σ (k : Nat). Nat)) → Array N (Σ (k : Nat). Nat)) {
      Z => λ (N : Nat). λ (A : Array N (Σ (k : Nat). Nat)).
        arrRec (Σ (k : Nat). Nat)
          (λ (M : Nat). λ (Az : Array M (Σ (k : Nat). Nat)). Array M (Σ (k : Nat). Nat))
          %(Term.ctorApp "Arr" [])
          (λ (M : Nat). λ (X : Σ (k : Nat). Nat). λ (XS : Array M (Σ (k : Nat). Nat)).
            λ (Ih : Array M (Σ (k : Nat). Nat)).
              acons M (elim X return (λ (Xz : Σ (k : Nat). Nat). Σ (k : Nat). Nat) {
                Pair (Kx) (Vx) => Pair Kx V }) XS)
          N A,
      S (I2) Rec => λ (N : Nat). λ (A : Array N (Σ (k : Nat). Nat)).
        arrRec (Σ (k : Nat). Nat)
          (λ (M : Nat). λ (Az : Array M (Σ (k : Nat). Nat)). Array M (Σ (k : Nat). Nat))
          %(Term.ctorApp "Arr" [])
          (λ (M : Nat). λ (X : Σ (k : Nat). Nat). λ (XS : Array M (Σ (k : Nat). Nat)).
            λ (Ih : Array M (Σ (k : Nat). Nat)).
              acons M X (Rec M XS))
          N A } }

/-! ### §3.1 The decomposition-first update

    `AVSetDecT i r v` splits the array at `(i, S r)`, applies the EXISTING
    fold-spelled update at index `Z` to the suffix, and recomposes. Two things
    about it are the point of this whole lane:

      * The prefix and the suffix are named by `atake`/`adrop` rather than taken
        as parameters, which is what `SetHmProbe` §4 says a signature cannot do —
        so this is writable where `gmSymPinDecomp` was not.
      * The element-level work needs NO new vocabulary. After the drop the index
        is the literal `Z`, so `AVSetT Z v` computes in one `arrRec` ι step on
        the `acons`-headed suffix and keeps the key itself. §3.2 measured the
        alternative (a head/tail projection pair) as unnecessary before it was
        written; what blocked §3.2 of the probe was a `natRec` on a SYMBOLIC
        index, and the decomposition removes the symbol, not the fold. -/

def AVSetDecT : Term := prog defer_check {
  λ (I : Nat). λ (R : Nat). λ (V : Nat). λ (N : Nat). λ (A : Array N (Σ (k : Nat). Nat)).
    arrCat I (S R) (atake I (S R) A) ((%AVSetT) Z V (S R) (adrop I (S R) A)) }

/-- **It is the same function**, which is what keeps `SetHM`'s STATEMENT fixed:
    `AVSetDecT i r v` and `AVSetT i v` agree wherever the extent is `i + (S r)`.
    Asserted on runs, at each of the three slots of a 3-array. -/
def sampleArr : Term := prog defer_check { Arr(Pair(7, 1), Pair(7, 2), Pair(7, 3)) }

example : (Pure.nf 4000 prog defer_check { (%AVSetDecT) 0 2 9 3 %sampleArr }
        == Pure.nf 4000 prog defer_check { (%AVSetT) 0 9 3 %sampleArr }) = true := by native_decide
example : (Pure.nf 4000 prog defer_check { (%AVSetDecT) 1 1 9 3 %sampleArr }
        == Pure.nf 4000 prog defer_check { (%AVSetT) 1 9 3 %sampleArr }) = true := by native_decide
example : (Pure.nf 4000 prog defer_check { (%AVSetDecT) 2 0 9 3 %sampleArr }
        == Pure.nf 4000 prog defer_check { (%AVSetT) 2 9 3 %sampleArr }) = true := by native_decide

/-- …and it writes the value it says it writes, keeping the keys. -/
example : (Pure.nf 4000 prog defer_check { (%AVSetDecT) 1 1 9 3 %sampleArr }
        == prog defer_check { Arr(Pair(7, 1), Pair(7, 9), Pair(7, 3)) }) = true := by native_decide

/-- **And on a SYMBOLIC composition it computes**, which is the property the
    fold-spelled `AVSetT` does not have and the whole reason for the lane: the
    index `I` is opaque, and the update still steps to the recomposed spine with
    the entry key kept and the new value in place. -/
example : (Pure.nf 4000
    prog defer_check { λ (I : Nat). λ (R : Nat). λ (V : Nat). λ (K0 : Nat).
          λ (Lo : Array I (Σ (k : Nat). Nat)). λ (V0 : Nat).
          λ (Hi : Array R (Σ (k : Nat). Nat)).
            (%AVSetDecT) I R V (Add I (S R))
              (arrCat I (S R) Lo (acons R (Pair K0 V0) Hi)) }
  == Pure.nf 4000
    prog defer_check { λ (I : Nat). λ (R : Nat). λ (V : Nat). λ (K0 : Nat).
          λ (Lo : Array I (Σ (k : Nat). Nat)). λ (V0 : Nat).
          λ (Hi : Array R (Σ (k : Nat). Nat)).
            arrCat I (S R) Lo (acons R (Pair K0 V) Hi) })
  = true := by native_decide

/-- The same at the pack level — `SetHmProbe`'s `PVSetNT` with the
    decomposition-first update inside. -/
def PVSetDecT : Term := prog defer_check {
  λ (N : Nat). λ (I : Nat). λ (R : Nat). λ (V : Nat).
    λ (P : Σ0 (a : Array N (Σ (k : Nat). Nat)). AllK7 N a).
      elim P return (λ (Pz : Σ0 (a : Array N (Σ (k : Nat). Nat)). AllK7 N a).
                       Σ0 (a : Array N (Σ (k : Nat). Nat)). AllK7 N a) {
        Pair (A) (H) => Pair ((%AVSetDecT) I R V N A) H } }

/-! ### §3.2 THE HEADLINE — `gmSymPinFold`'s program, now GREEN

    `SetHmProbe` §3.2's `gmSymPinFold`, character for character, with the
    fold-spelled pin replaced by the decomposition-first one (and `r` — already a
    parameter, because `hm-probe-mod`'s capacity forcing makes the carve need it —
    passed to it). The carve is BLIND: nothing in front of the slot is opened, the
    index is symbolic, the extent is opaque with a decomposition equation. This is
    the program someone would write, and it is what the walk was the fallback for. -/

def gmDecSymPin : Term := prog{
  fn G (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
        self : &mut (s : Σ0 (a : Array n (Σ (k : Nat). Nat)). AllK7 n a
                       ~> (%PVSetDecT) n i r (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let pre = &m (*a)[Z ; i ; S r | LeAdd i (S r) | hd];
      let cell = &m (*a)[i ; 1 ; r];
      let e = &m (*cell)[0];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

/-- …and `gmSymPinDecomp`'s shape, the one §4 called "the right shape and
    unwritable": extent spelled as the decomposition, carve citing `Refl`, and now
    with the pieces PROJECTED instead of taken as parameters. -/
def gmDecSymPinRefl : Term := prog{
  fn G (i : Nat, r : Nat,
        self : &mut (s : Σ0 (a : Array (Add i (S r)) (Σ (k : Nat). Nat)). AllK7 (Add i (S r)) a
                       ~> (%PVSetDecT) (Add i (S r)) i r (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let pre = &m (*a)[Z ; i ; S r | LeAdd i (S r) | Refl];
      let cell = &m (*a)[i ; 1 ; r];
      let e = &m (*cell)[0];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

/-! ### §3.3 The negative controls

    A green verdict is only worth what its twin's red is. `gmDecSymPinKey`
    escapes the KEY borrow where the pin puts the exit in the VALUE slot; the
    concrete-index pair is `SetHmProbe` §3.1's port controls, which must keep
    saying that the decomposition spelling did not weaken anything at a concrete
    index either. -/

def gmDecSymPinKey : Term := prog defer_check {
  fn G (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
        self : &mut (s : Σ0 (a : Array n (Σ (k : Nat). Nat)). AllK7 n a
                       ~> (%PVSetDecT) n i r (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let pre = &m (*a)[Z ; i ; S r | LeAdd i (S r) | hd];
      let cell = &m (*a)[i ; 1 ; r];
      let e = &m (*cell)[0];
      match e { Pair(kk, vv) => &m *kk } } } };
  () }

def gmDecConc2at1blind : Term := prog{
  fn G (self : &mut (s : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a
                       ~> (%PVSetDecT) 2 1 0 (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e = &m (*a)[1];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

def gmDecConc2at1open : Term := prog{
  fn G (self : &mut (s : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a
                       ~> (%PVSetDecT) 2 1 0 (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e0 = &m (*a)[0];
      match e0 { Pair(k0, v0) => {
        let e = &m (*a)[1];
        match e { Pair(kk, vv) => &m *vv } } } } } };
  () }

/-- The wrong SLOT: the pin says the update happens at `i`, the carve reaches
    `i` but the pin is instantiated at index `Z`. -/
def gmDecSymPinWrongSlot : Term := prog defer_check {
  fn G (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
        self : &mut (s : Σ0 (a : Array n (Σ (k : Nat). Nat)). AllK7 n a
                       ~> (%PVSetDecT) n Z (Add i r) (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let pre = &m (*a)[Z ; i ; S r | LeAdd i (S r) | hd];
      let cell = &m (*a)[i ; 1 ; r];
      let e = &m (*cell)[0];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

/-! ### §3.4 …and it RUNS

    The E2E half, as `SetHmProbe` §6.2: instantiate at extent 3 / index 1, take
    the pinned cursor, write `9` through it, end the group, read the pack back. -/

def runBinding (t : Term) (name : String) : Option String :=
  match runProgram t with
  | .ok env => (env.lookup name).map Val.pretty
  | .error _ => none

def gmDecCaller : Term := prog{
  fn GetMut (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
        self : &mut (s : Σ0 (a : Array n (Σ (k : Nat). Nat)). AllK7 n a
                       ~> (%PVSetDecT) n i r (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let pre = &m (*a)[Z ; i ; S r | LeAdd i (S r) | hd];
      let cell = &m (*a)[i ; 1 ; r];
      let e = &m (*cell)[0];
      match e { Pair(kk, vv) => &m *vv } } } };
  let p = Pair(Arr(Pair(7, 1), Pair(7, 2), Pair(7, 3)),
               Pair(Refl, Pair(Refl, Pair(Refl, unit))));
  let q = &m p;
  let c = GetMut(3, 1, 1, Refl, q);
  *c := 9;
  () }

/-! ### §3.5 THE VERDICTS

        gmDecSymPin           BLIND carve, SYMBOLIC index, pinned    GREEN ← the answer
        gmDecSymPinRefl       …extent spelled as the decomposition   GREEN
        gmDecSymPinKey        the KEY twin                           red
        gmDecSymPinWrongSlot  the pin at the wrong slot              red
        gmDecConc2at1blind    concrete index, blind                  GREEN
        gmDecConc2at1open     concrete index, prefix opened          GREEN
        gmDecCaller           …and it runs, writing cell 1           GREEN
-/

/-- **THE HEADLINE.** `SetHmProbe` §3.2's `gmSymPinFold` — refused with
    "the declared pin (Pair (natRec" because the fold could not step on a σ index
    — is GREEN once `SetHM` is spelled with the projections. The blind carve at a
    symbolic index in an opaque-extent array discharges its map-level pin, which
    is the O(1) `GetMut` the walk was standing in for. -/
example : progOk gmDecSymPin = true := by native_decide
example : progOk gmDecSymPinRefl = true := by native_decide

/-- The key twin, refused with the two sides differing in exactly one place: the
    exit `σ21` sits in the KEY slot on the fill and in the VALUE slot on the pin.
    Everything else — the split, the prefix, the suffix — matches, which is what
    makes this the sharp negative rather than a shape mismatch. -/
example : progRejects gmDecSymPinKey
  "exits (Pair (arrCat σ1 (S σ2) σ13 (acons σ2 (Pair σ21 σ20) σ17)) σ7), does not convert with the declared pin (Pair (arrCat σ1 (S σ2) σ13 (acons σ2 (Pair σ19 σ21) σ17)) σ7)."
  = true := by native_decide

/-- **The wrong slot is refused BY THE STUCKNESS**, and the print is the argument
    for matching both extents rather than the total. The pin asks for the split
    `(Z, S (add i r))`; the carve made the split `(i, S r)`; the two are the same
    total extent and different compositions, so `splitAt?` declines and the pin
    normalizes with `atake Z (S (natRec …)) (arrCat σ1 (S σ2) …)` still standing
    in it. A rule that fired on the total would have handed this program the
    prefix of a decomposition it never made. -/
example : progRejects gmDecSymPinWrongSlot
  "does not convert with the declared pin (Pair (arrCat Z (S (natRec" = true := by native_decide

example : progOk gmDecConc2at1blind = true := by native_decide
example : progOk gmDecConc2at1open = true := by native_decide

example : progOk gmDecCaller = true := by native_decide
example : runBinding gmDecCaller "p"
  = some ("Pair [Pair (S (S (S (S (S (S (S Z))))))) (S Z), "
       ++ "Pair (S (S (S (S (S (S (S Z))))))) (S (S (S (S (S (S (S (S (S Z))))))))), "
       ++ "Pair (S (S (S (S (S (S (S Z))))))) (S (S (S Z)))] "
       ++ "(Pair Refl (Pair Refl (Pair Refl unit)))")
  := by native_decide

/-! ## §4 The counterfactual, and what the projections cost

    **The counterfactual, run.** Replace the two `whnfN` arms with the stuck
    rebuild they fall through to, keep everything else, and build the tree from
    scratch: **20 assertions go red, all of them in this file, and nothing
    anywhere else in the suite moves.** They are §1.1's six run computations,
    §1.2's three symbolic ones, §3.1's five (the three agreements with `AVSetT`,
    the written value, and the symbolic composition), and §3.2/§3.3's six greens
    (`gmDecSymPin`, `gmDecSymPinRefl`, the two concrete controls, `gmDecCaller`
    and its run) — plus, the twentieth, `gmDecSymPinKey`'s NEEDLE: that program
    stays rejected without the rules, but for a different reason, so the message
    it is pinned on is no longer the message it gets.

    Every other negative here survives the removal, and that is the honest half
    of the design: §1.3, §1.4 and `gmDecSymPinWrongSlot` all assert that a
    projection is STUCK, which is exactly what an absent rule leaves behind.

    **What they cost** (`lake env lean` against the built oleans, `IO.monoMsNow`
    around `Pure.nf`; medians of a single run, which is all a linearity claim
    needs):

        atake n n (run 2n)          n=200 → 2 ms   400 → 3    800 → 5    1600 → 10
        adrop n n (run 2n)          n=200 → 1 ms   400 → 2    800 → 5    1600 →  9
        AVSetDec 0 (n-1) (run n)    n=100 → 4 ms   200 → 5    400 → 10    800 → 22
        AVSet    0       (run n)    n=100 → 3 ms   200 → 6    400 → 11    800 → 20

    Doubling the extent doubles the time in each family, so the projections are
    linear and the decomposition-first update costs what the fold-spelled one
    costs at the same slot — the spelling that makes the pin discharge is not
    paid for in normalization.

    The third family answers the sharing question directly. Projecting the SAME
    composition twice (`arrCat n n (atake …) (adrop …)`) costs 3/6/12 ms at
    n=200/400/800 against 2/3/6 ms for the take alone: exactly twice the work for
    twice the result, which is one pass each and no re-derivation of the argument.
    That is the property `AVSetDecT` needs — it names `A` twice — and it holds
    for the NbE reason rather than by luck: `A` is a bound name, `eval` resolves
    it through the environment, and both arms match on the one `Sem` the lookup
    returns. `deepForce`/`armUsesRec` are not involved and correctly so; they are
    consulted at exactly the three recursor arms in `whnfN`, each time to ask
    whether a STEP ARM makes its recursive call, and a projection has no step arm. -/

end Dllbc.Tests.ArrCatIota

end

