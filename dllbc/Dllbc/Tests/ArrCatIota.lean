import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas

/-!
# `ArrCatIota` — the `atake`/`adrop` array projections

This file tests the `atake`/`adrop` array projections and their ι-rules
(`atake i k (arrCat i k lo hi) ↝ lo`, `adrop` likewise), which let a program
name the prefix and suffix that a carve mints. With them, an update at a
symbolic slot index can be written decomposition-first, and its pinned
contract discharges without walking the array element by element.

Why: a carve at a symbolic index mints pieces no signature can name, and
naming them is exactly what the projections add. The element at the cell
needs no further vocabulary — after the drop the update recurses on the
literal `Z`, so the existing fold-spelled update computes in one ι step.
-/

section

open Dllbc

namespace Dllbc.Tests.ArrCatIota

open Dllbc.StdLemmas (LeAdd LeRefl IdCongr IdSym AddZero)

/-! ## §1 The ι-rules

    `atake i k` and `adrop i k` fire on two shapes: a composition whose split
    point converts with `(i, k)`, and an owned run of length `i + k`. Anything
    else stays stuck — firing at the wrong split point would be unsound, not
    just imprecise. -/

/-! ### §1.1 On an owned run -/

example : (Pure.nf 200 prog defer_check { atake 1 2 Arr(3, 1, 2) } == prog defer_check { Arr(3) }) = true := by native_decide
example : (Pure.nf 200 prog defer_check { adrop 1 2 Arr(3, 1, 2) } == prog defer_check { Arr(1, 2) }) = true := by native_decide
example : (Pure.nf 200 prog defer_check { atake 0 3 Arr(3, 1, 2) } == prog defer_check { Arr() }) = true := by native_decide
example : (Pure.nf 200 prog defer_check { adrop 0 3 Arr(3, 1, 2) } == prog defer_check { Arr(3, 1, 2) }) = true := by native_decide
example : (Pure.nf 200 prog defer_check { atake 3 0 Arr(3, 1, 2) } == prog defer_check { Arr(3, 1, 2) }) = true := by native_decide
example : (Pure.nf 200 prog defer_check { adrop 3 0 Arr(3, 1, 2) } == prog defer_check { Arr() }) = true := by native_decide

/-- A run whose length is not `i + k` is not this composition, so the
    projection stays stuck rather than guessing. -/
example : (Pure.nf 200 prog defer_check { atake 1 1 Arr(3, 1, 2) } == prog defer_check { Arr(3) }) = false := by native_decide

/-! ### §1.2 On a composition, symbolically -/

/-- `atake i k (arrCat i k lo hi) ↝ lo`, with `i`, `k`, `lo`, `hi` all opaque. -/
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

/-- The extents are compared by conversion, not by tree equality: the carve's
    fold builds its right extent with `add` (`Val.segsExtent?`), so the spine a
    discharge meets says `add 1 r` where the signature says `S r`. -/
example : (Pure.nf 600
    prog defer_check { λ (R : Nat). λ (I : Nat). λ (Lo : Array I Nat). λ (Hi : Array (S R) Nat).
            atake I (Add 1 R) (arrCat I (S R) Lo Hi) }
  == Pure.nf 600
    prog defer_check { λ (R : Nat). λ (I : Nat). λ (Lo : Array I Nat). λ (Hi : Array (S R) Nat). Lo })
  = true := by native_decide

/-! ### §1.3 …and splits that are not this one stay stuck

    `atake 1 2` of `arrCat 2 1 lo hi` is not `lo`: both are arrays of extent 3
    and the total extent is the same, so a rule that matched on the total
    would be a bug, not an approximation. -/

example : (Pure.nf 600
    prog defer_check { λ (Lo : Array 2 Nat). λ (Hi : Array 1 Nat). atake 1 2 (arrCat 2 1 Lo Hi) }
  == Pure.nf 600 prog defer_check { λ (Lo : Array 2 Nat). λ (Hi : Array 1 Nat). Lo })
  = false := by native_decide

/-- A stuck projection is a normal form — it does not keep unfolding — which is
    what lets it sit inside a pin and be compared. -/
def stuckTake : Term :=
  Pure.nf 600 prog defer_check { λ (I : Nat). λ (K : Nat). λ (A : Array (Add I K) Nat). atake I K A }
example : (Pure.nf 600 stuckTake == stuckTake) = true := by native_decide

/-- A bare σ has no visible split, so both projections are stuck on one. -/
example : (Pure.nf 400 prog defer_check { atake 1 2 %(Term.sym 0) }
  == prog defer_check { atake 1 2 %(Term.sym 0) }) = true := by native_decide

/-! ### §1.4 Two rules that are not needed

    **`acons`-stepping.** `atake (S i) k (acons m x xs) ↝ acons _ x (atake i k
    xs)` would let a projection peel a cons view one element at a time instead
    of requiring the composition. It is not needed: a carve at a symbolic
    index never opens the prefix, so the array stays headed by `arrCat`, and
    `arrCat`'s own `acons`-headed rule does not fire either.

    **Element-level projections at the cell** (a head/tail pair, or an `aget`
    that fires on `acons`) are also not needed: after the drop the index is
    the literal `Z`, and the existing `arrRec` fold computes from there. -/

example : (Pure.nf 600
    prog defer_check { λ (I : Nat). λ (K : Nat). λ (X : Nat). λ (XS : Array (Add I K) Nat).
            atake (S I) K (acons (Add I K) X XS) }
  == Pure.nf 600
    prog defer_check { λ (I : Nat). λ (K : Nat). λ (X : Nat). λ (XS : Array (Add I K) Nat).
            acons I X (atake I K XS) })
  = false := by native_decide

/-! ## §2 The typing arms

    `atake i k a : Array i T` and `adrop i k a : Array k T` for
    `a : Array (add i k) T`. Both are checked rather than synthesized, like
    `arrCat`/`acons` and for the same reason: the element type comes from the
    expected type, so neither carries a `T`.

    §1 covers a projection that computes: `hasTypeT` weak-heads its value first,
    so `atake 1 2 Arr(3,1,2)` is typed as the run it reduces to. The arms below
    cover the case a pin actually meets — a symbolic array that does not
    reduce. -/

/-- Runs `hasTypeT` against a seeded context, reporting `ok`/`error` as a
    string for comparison in assertions. -/
def chkS (sctx : List (Nat × Term)) (tm ty : Term) : String :=
  match (hasTypeT 8000 tm ty).run (seedPure [] sctx) with
  | .ok r _ => s!"ok {r}"
  | .error e _ => s!"error {e}"

/-- `σ₀ = i`, `σ₁ = k`, `σ₂ : Array (add i k) T` — the telescope a decomposition
    spelling has in scope. -/
def splitCtx : List (Nat × Term) :=
  [(0, prog defer_check { Nat }), (1, prog defer_check { Nat }),
   (2, prog defer_check { Array %(prog defer_check { %(Pure.kAddFn) %(Term.sym 0) %(Term.sym 1) }) Nat })]

example : chkS splitCtx prog defer_check { atake %(Term.sym 0) %(Term.sym 1) %(Term.sym 2) }
    prog defer_check { Array %(Term.sym 0) Nat } = "ok true" := by native_decide
example : chkS splitCtx prog defer_check { adrop %(Term.sym 0) %(Term.sym 1) %(Term.sym 2) }
    prog defer_check { Array %(Term.sym 1) Nat } = "ok true" := by native_decide

/-- The extent is the one the projection names, not the other one and not the
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

/-- The argument's extent must be the sum: `σ3 : Array σ0 Nat` is too short to
    be split at `(σ0, σ1)`. -/
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

/-! ## §3 The target — a blind carve at a symbolic index, pinned

    The container, the fold-spelled update, and the programs below keep the
    same shapes as the update they compare against, so a verdict that moves is
    attributable to the projections alone. -/

/-- The container: an array of key-value pairs where every key is 7. -/
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

/-- The fold-spelled update: walks the cons view index-first, keeping the key
    and replacing the value at the target index. `AVSetDecT` below wraps it
    rather than replacing it. -/
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

    `AVSetDecT i r v` splits the array at `(i, S r)`, applies the existing
    fold-spelled update at index `Z` to the suffix, and recomposes.

      * The prefix and the suffix are named by `atake`/`adrop` instead of being
        taken as parameters — a signature alone cannot name pieces a carve
        mints.
      * The element-level work needs no new vocabulary: after the drop, the
        index is the literal `Z`, so `AVSetT Z v` computes in one `arrRec`
        ι step on the `acons`-headed suffix and keeps the key. -/

def AVSetDecT : Term := prog defer_check {
  λ (I : Nat). λ (R : Nat). λ (V : Nat). λ (N : Nat). λ (A : Array N (Σ (k : Nat). Nat)).
    arrCat I (S R) (atake I (S R) A) ((%AVSetT) Z V (S R) (adrop I (S R) A)) }

/-- The two updates agree wherever the extent is `i + (S r)`: `AVSetDecT i r v`
    and `AVSetT i v` compute the same array. Checked at each of the three
    slots of a 3-element array. -/
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

/-- On a symbolic composition it still computes: with the index `I` opaque,
    the update steps to the recomposed spine with the entry key kept and the
    new value in place. The fold-spelled `AVSetT` alone cannot do this, since
    it needs a concrete index to recurse on. -/
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

/-- The same update at the pack level: unwraps the Σ0, applies `AVSetDecT`, and
    rewraps with the same proof component. -/
def PVSetDecT : Term := prog defer_check {
  λ (N : Nat). λ (I : Nat). λ (R : Nat). λ (V : Nat).
    λ (P : Σ0 (a : Array N (Σ (k : Nat). Nat)). AllK7 N a).
      elim P return (λ (Pz : Σ0 (a : Array N (Σ (k : Nat). Nat)). AllK7 N a).
                       Σ0 (a : Array N (Σ (k : Nat). Nat)). AllK7 N a) {
        Pair (A) (H) => Pair ((%AVSetDecT) I R V N A) H } }

/-! ### §3.2 The blind carve, pinned

    `gmDecSymPin` carves an array at a symbolic index `i` with nothing in
    front of the slot opened, and its pin is the decomposition-first update.
    This is the program a caller would naturally write for an O(1) update at a
    symbolic index. -/

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

/-- The same carve with the extent spelled directly as the decomposition
    `Add i (S r)` and the carve citing `Refl`, rather than carrying a separate
    equality hypothesis. -/
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

    `gmDecSymPinKey` escapes the key borrow where the pin declares the exit in
    the value slot, and must be rejected. The concrete-index pair checks that
    the decomposition spelling does not weaken anything at a concrete index
    either. -/

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

/-! ### §3.4 …and it runs

    End-to-end: instantiate at extent 3, index 1; take the pinned cursor;
    write `9` through it; end the group; read the pack back. -/

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

/-! ### §3.5 Verdicts

        gmDecSymPin           blind carve, symbolic index, pinned    green (the target case)
        gmDecSymPinRefl       …extent spelled as the decomposition   green
        gmDecSymPinKey        the key twin                           red
        gmDecSymPinWrongSlot  the pin at the wrong slot              red
        gmDecConc2at1blind    concrete index, blind                  green
        gmDecConc2at1open     concrete index, prefix opened          green
        gmDecCaller           …and it runs, writing cell 1           green
-/

/-- The blind carve at a symbolic index, in an array of opaque extent, type-
    checks once the update is spelled with the projections: this is the O(1)
    `GetMut` case, with no element-by-element walk needed. -/
example : progOk gmDecSymPin = true := by native_decide
example : progOk gmDecSymPinRefl = true := by native_decide

/-- The key twin: everything matches except that the fill's exit sits in the
    key slot while the pin declares it in the value slot. It is rejected with
    the two sides differing in exactly that one place. -/
example : progRejects gmDecSymPinKey
  "exits (Pair (arrCat σ₁ (S σ₂) σ₁₃ (acons σ₂ (Pair σ₂₁ σ₂₀) σ₁₇)) σ₇), does not convert with the declared pin (Pair (arrCat σ₁ (S σ₂) σ₁₃ (acons σ₂ (Pair σ₁₉ σ₂₁) σ₁₇)) σ₇)."
  = true := by native_decide

/-- The wrong slot is refused by stuckness, not by a failed comparison: the pin
    asks for the split `(Z, S (add i r))` while the carve made the split
    `(i, S r)`. Same total extent, different compositions, so `splitAt?`
    declines and the projection stays stuck in the normal form. A rule that
    matched on the total extent alone would have handed this program a prefix
    it never carved. -/
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

    **Counterfactual.** Replacing the two `atake`/`adrop` ι-rules with the
    stuck rebuild they fall through to turns 20 assertions red, all in this
    file and nothing elsewhere in the suite: the run computations of §1.1, the
    symbolic ones of §1.2, the five agreements and computations of §3.1, and
    the six greens of §3.2/§3.3. A twentieth case, `gmDecSymPinKey`, still gets
    rejected without the rules, but for a different reason, so its pinned
    message changes too. Every other negative survives the removal, since
    §1.3, §1.4 and `gmDecSymPinWrongSlot` all assert that a projection stays
    stuck, which is exactly what an absent rule leaves behind.

    **Cost** (medians from `IO.monoMsNow` around `Pure.nf`, run against the
    built oleans):

        atake n n (run 2n)          n=200 → 2 ms   400 → 3    800 → 5    1600 → 10
        adrop n n (run 2n)          n=200 → 1 ms   400 → 2    800 → 5    1600 →  9
        AVSetDec 0 (n-1) (run n)    n=100 → 4 ms   200 → 5    400 → 10    800 → 22
        AVSet    0       (run n)    n=100 → 3 ms   200 → 6    400 → 11    800 → 20

    Doubling the extent doubles the time in each family: the projections are
    linear, and the decomposition-first update costs the same as the
    fold-spelled one at the same slot.

    Projecting the same composition twice (`arrCat n n (atake …) (adrop …)`)
    costs 3/6/12 ms at n=200/400/800 against 2/3/6 ms for the take alone —
    twice the work for twice the result, with no re-derivation of the shared
    argument. `AVSetDecT` needs exactly this, since it names `A` twice: `A` is
    a bound name, `eval` resolves it once through the environment, and both
    arms match on the same `Sem` the lookup returns. `deepForce`/`armUsesRec`
    play no role here, since they apply only at recursor step arms, and a
    projection has no step arm. -/

end Dllbc.Tests.ArrCatIota

end

