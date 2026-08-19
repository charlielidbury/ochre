import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas

/-!
# `SetHmProbe` — does a pin discharge at a SYMBOLIC carve index?

The flagship's `GetMut` was drafted to reach its slot by a BLIND carve at a
symbolic index (`i = Mod key cap`, extent `n` opaque with `Le 1 n`) with the pin
`~> SetHM key (*res) s` on its parameter. `OpaqueFill.lean` §7.6 measured that pin
at CONCRETE indices only: it discharges when the body's flow opened the prefix
(`gmPin2at1`, `gmPin3at2`) and is refused at a blind carve (`gmPin2at1blind`).
This file asks the question where the flagship actually lives — index symbolic,
extent symbolic — and the answer changes GetMut's ARCHITECTURE, not its spec.

Everything here is library. No kernel change was needed and none is proposed.

## The finding, in three lines

  * **The blind carve at a symbolic index cannot be pinned, in EITHER spelling.**
    Index-first fold (`gmSymPinFold`) and decomposition-by-`arrCat`
    (`gmSymPinDecomp`) are both refused, and the two prints say they are refused
    for DIFFERENT reasons — §3.2 and §4 below.
  * **The symbolic EXTENT is not the problem.** `gmSymAt0` and `gmSymAt1` pin a
    symbolic-extent array at index `Z` and index `1` and both are GREEN. What the
    fold needs is not a known length; it is that every element in FRONT of the
    target has been opened by the body's own flow.
  * **So the shape that works is a WALK**, and it works: `walkDecls` recurses on
    the index opening one element per step, `packWalk` does the same under the
    intrinsically packed container, and `packWalkCaller` runs it. This is
    `BorrowRefoundGoals`' `NthPin` — the list get_mut law — transposed to arrays.
    The recursion is what makes every `natRec` the pin owes get taken in a branch
    where the index is a CONSTRUCTOR.

## What that costs the flagship

A walking `GetMut` is O(cap) in slot-index steps where Aeneas' is O(1), so this is
a real divergence to record, not a free rewrite. It buys the map-level pin exactly
as the spec fixes it; nothing about `SetHM`'s STATEMENT has to change, only how
the body reaches the cell. `SetHM` should be spelled index-first (`AVSetT`'s
shape) — the spelling `PVSetNT` lifts to the pack here.

## What would make the blind carve work

§4 is the print to take to that discussion. Its two sides are the same term modulo
three σ's: `pinFill`'s prefix/suffix/key against the parameters standing in for
them. The decomposition spelling is the RIGHT shape and is unwritable for one
reason — the carve mints the prefix and suffix, and a signature has no syntax to
name them. Give `arrCat` projections with ι-rules (`ATake i k (arrCat i k lo hi) ↝
lo`, `ADrop` likewise) and `SetHM` could be written decomposition-first and would
converge with the fill on the refined spine, with no walk. That is a contained,
purely computational addition — but it is a kernel change, so it is named here and
not attempted.
-/

section

open Dllbc

namespace Dllbc.Tests.SetHmProbe

open Dllbc.StdLemmas (LeAdd LeRefl IdCongr IdSym AddZero)

/-- The error message, verbatim, for the both-sides prints. -/
def errOf (t : Term) : String :=
  match checkProgram t prog{ Unit } with | .ok _ => "OK" | .error e => e

/-! ## §1 The container — `OpaqueFill`'s `AllK7`, at a SYMBOLIC extent

    `AllK7 n a` folds over the whole array asserting every KEY is 7 and reading no
    value. It is the flagship's `HMInv` reduced to the one clause that makes the
    question sharp: an escaping VALUE borrow cannot break it and an escaping KEY
    borrow can. Reused verbatim from §7.5/§7.6 so the two measurements compose. -/

def AllK7 : Term := prog{
  λ (M : Nat). λ (A : Array M (Σ (k : Nat). Nat)).
    arrRec (Σ (k : Nat). Nat)
      (λ (Mz : Nat). λ (Az : Array Mz (Σ (k : Nat). Nat)). Type)
      Unit
      (λ (K : Nat). λ (H : Σ (k : Nat). Nat). λ (T : Array K (Σ (k : Nat). Nat)).
        λ (Ih : Type).
          (elim H return (λ (Hm : Σ (k : Nat). Nat). Type) {
            Pair (K2) (V2) => Id Nat K2 7 }) × Ih)
      M A }

/-! ## §2 THE BASELINE: does the symbolic carve work at all, pin-free?

    Before asking about a pin, pin down what the un-pinned program does — the same
    A/B §7.5 used. `symCarveUnit` carves at a symbolic `i` inside the pack and
    escapes nothing; `symCarveEsc` is the identical body with the value borrow
    escaping. The decomposition (`i`, `r`, `Hdec`) arrives as PARAMETERS here; §4
    re-asks with it minted across a call, which is the flagship's own shape.

    Note the extent is an opaque `N` with `Le (S Z) N` and the carve cites `Hdec`,
    per `hm-probe-mod`'s two forced shapes. -/

def symCarveUnit : Term := prog{
  fn G (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
        self : &mut (Σ0 (a : Array n (Σ (k : Nat). Nat)). AllK7 n a)) -> Unit {
    match self { Pair(a, H) => {
      let pre = &m (*a)[Z ; i ; S r | LeAdd i (S r) | hd];
      let cell = &m (*a)[i ; 1 ; r];
      let e = &m (*cell)[0];
      match e { Pair(kk, vv) => () } } } };
  () }

def symCarveEsc : Term := prog{
  fn G (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
        self : &mut (Σ0 (a : Array n (Σ (k : Nat). Nat)). AllK7 n a)) -> &mut Nat {
    match self { Pair(a, H) => {
      let pre = &m (*a)[Z ; i ; S r | LeAdd i (S r) | hd];
      let cell = &m (*a)[i ; 1 ; r];
      let e = &m (*cell)[0];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

/-! ## §3 SPELLING (i) — the FOLD-SPELLED update, at a symbolic index

    `AVSet i v` is `OpaqueFill` §7.6's update verbatim: index-first, cons-view,
    keeping the key and replacing the value. `PVSetN` lifts it to the pack at a
    SYMBOLIC extent (§7.6 only ever needed extents 2 and 3). This is the spelling
    a `SetHM` written the obvious way would have. -/

def AVSetT : Term := prog{
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

def PVSetNT : Term := prog{
  λ (N : Nat). λ (I : Nat). λ (V : Nat).
    λ (P : Σ0 (a : Array N (Σ (k : Nat). Nat)). AllK7 N a).
      elim P return (λ (Pz : Σ0 (a : Array N (Σ (k : Nat). Nat)). AllK7 N a).
                       Σ0 (a : Array N (Σ (k : Nat). Nat)). AllK7 N a) {
        Pair (A) (H) => Pair ((%AVSetT) I V N A) H } }

/-! ### §3.1 The concrete-index CONTROLS — my `PVSetN` reproduces §7.6

    Same two programs `OpaqueFill` §7.6 pinned (`gmPin2at1`, `gmPin2at1blind`),
    re-run through the extent-generic `PVSetN` rather than its `PVSet2T`. If these
    do not land green/red the port is wrong and nothing below means anything. -/

def gmConc2at1open : Term := prog{
  fn G (self : &mut (s : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a
                       ~> (%PVSetNT) 2 1 (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e0 = &m (*a)[0];
      match e0 { Pair(k0, v0) => {
        let e = &m (*a)[1];
        match e { Pair(kk, vv) => &m *vv } } } } } };
  () }

def gmConc2at1blind : Term := prog{
  fn G (self : &mut (s : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a
                       ~> (%PVSetNT) 2 1 (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e = &m (*a)[1];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

/-! ### §3.2 …and the flagship's own shape: SYMBOLIC extent, SYMBOLIC index -/

def gmSymPinFold : Term := prog{
  fn G (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
        self : &mut (s : Σ0 (a : Array n (Σ (k : Nat). Nat)). AllK7 n a
                       ~> (%PVSetNT) n i (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let pre = &m (*a)[Z ; i ; S r | LeAdd i (S r) | hd];
      let cell = &m (*a)[i ; 1 ; r];
      let e = &m (*cell)[0];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

/-! ### §3.3 Is it the symbolic INDEX or the symbolic EXTENT that stops the fold?

    §7.6's boundary was measured at concrete extents only, so `gmSymPinFold`'s
    refusal has two candidate causes and they have opposite consequences for the
    flagship. `gmSymAt0` keeps the extent symbolic (`S r`) and makes the index the
    literal `Z`; `gmSymAt1` keeps the extent symbolic and takes ONE step, opening
    element 0 the way a walk would. These two are the base case and the inductive
    step of a walking `GetMut`.

    (An extent written `S r` is REJECTED before any of this — `carve: premise (3)
    is stuck — the leaf's extent (S σ0) is a compound neutral, not a flexible σ`.
    That is `hm-probe-mod`'s capacity forcing, restated at the leaf: the extent is
    an opaque `m` plus a decomposition equation, everywhere, always.) -/

def gmSymAt0 : Term := prog{
  fn G (m : Nat, r : Nat, hd : Id Nat m (Add (S Z) r),
        self : &mut (s : Σ0 (a : Array m (Σ (k : Nat). Nat)). AllK7 m a
                       ~> (%PVSetNT) m Z (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let cell = &m (*a)[Z ; 1 ; r | LeAdd (S Z) r | hd];
      let e = &m (*cell)[0];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

def gmSymAt1 : Term := prog{
  fn G (m : Nat, r : Nat, hd : Id Nat m (Add (S Z) (S r)),
        self : &mut (s : Σ0 (a : Array m (Σ (k : Nat). Nat)). AllK7 m a
                       ~> (%PVSetNT) m (S Z) (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let pre = &m (*a)[Z ; 1 ; S r | LeAdd (S Z) (S r) | hd];
      let p0 = &m (*pre)[0];
      match p0 { Pair(k0, v0) => {
        let cell = &m (*a)[1 ; 1 ; r];
        let e = &m (*cell)[0];
        match e { Pair(kk, vv) => &m *vv } } } } } };
  () }

/-- The same step WITHOUT opening element 0 — the blind version of `gmSymAt1`,
    isolating the open from the extent. -/
def gmSymAt1blind : Term := prog{
  fn G (m : Nat, r : Nat, hd : Id Nat m (Add (S Z) (S r)),
        self : &mut (s : Σ0 (a : Array m (Σ (k : Nat). Nat)). AllK7 m a
                       ~> (%PVSetNT) m (S Z) (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let pre = &m (*a)[Z ; 1 ; S r | LeAdd (S Z) (S r) | hd];
      let cell = &m (*a)[1 ; 1 ; r];
      let e = &m (*cell)[0];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

/-! ## §4 SPELLING (ii) — the DECOMPOSITION-SPELLED update

    §3 says the fold cannot step past a σ-bodied prefix. So state the update in the
    form the fill already has: `arrCat i (S r) lo (acons r (Pair k (*res)) hi)`,
    aligned with `pinFill`'s spine BY CONSTRUCTION rather than by computation. The
    pieces `lo`/`k`/`hi` are not in scope at a signature, so the only way to write
    this at all is to take them as PARAMETERS — which is the measurement: it shows
    what the discharge does when the two sides have the same shape and differ only
    in which σ's stand at the leaves.

    `decompExtent` first checks the cheaper prerequisite: an extent spelled as the
    decomposition itself (`Array (Add i (S r))`), which would let the carve cite
    `Refl` and drop the transport. -/

def decompExtent : Term := prog{
  fn G (i : Nat, r : Nat,
        self : &mut (Σ0 (a : Array (Add i (S r)) (Σ (k : Nat). Nat)). AllK7 (Add i (S r)) a))
      -> Unit {
    match self { Pair(a, H) => {
      let pre = &m (*a)[Z ; i ; S r | LeAdd i (S r) | Refl];
      let cell = &m (*a)[i ; 1 ; r];
      let e = &m (*cell)[0];
      match e { Pair(kk, vv) => () } } } };
  () }

def gmSymPinDecomp : Term := prog{
  fn G (i : Nat, r : Nat, lo : Array i (Σ (k : Nat). Nat), k0 : Nat,
        hi : Array r (Σ (k : Nat). Nat),
        self : &mut (s : Σ0 (a : Array (Add i (S r)) (Σ (k : Nat). Nat)). AllK7 (Add i (S r)) a
                       ~> (elim s return (λ (Pz : Σ0 (a : Array (Add i (S r)) (Σ (k : Nat). Nat)).
                                                AllK7 (Add i (S r)) a).
                                            Σ0 (a : Array (Add i (S r)) (Σ (k : Nat). Nat)).
                                              AllK7 (Add i (S r)) a) {
                             Pair (A) (H) =>
                               Pair (arrCat i (S r) lo (acons r (Pair k0 (*res)) hi)) H })))
      -> &mut Nat {
    match self { Pair(a, H) => {
      let pre = &m (*a)[Z ; i ; S r | LeAdd i (S r) | Refl];
      let cell = &m (*a)[i ; 1 ; r];
      let e = &m (*cell)[0];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

/-! ## §5 THE NEGATIVE CONTROL — the KEY cell, at the spelling that works

    `gmSymAt1` with `&m *vv` replaced by `&m *kk`. The fill puts the shared exit in
    the key slot and the pin puts it in the value slot, so a discharge that
    accepted this would accept an escaping borrow onto a hashed cell. -/

def gmSymAt1Key : Term := prog{
  fn G (m : Nat, r : Nat, hd : Id Nat m (Add (S Z) (S r)),
        self : &mut (s : Σ0 (a : Array m (Σ (k : Nat). Nat)). AllK7 m a
                       ~> (%PVSetNT) m (S Z) (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let pre = &m (*a)[Z ; 1 ; S r | LeAdd (S Z) (S r) | hd];
      let p0 = &m (*pre)[0];
      match p0 { Pair(k0, v0) => {
        let cell = &m (*a)[1 ; 1 ; r];
        let e = &m (*cell)[0];
        match e { Pair(kk, vv) => &m *kk } } } } } };
  () }

/-! ## §6 THE WALK — the only shape left, and the one the flagship must adopt

    §3 says the index-first fold steps exactly when the body's flow opened the
    element in front of it, and §3.3 says a SYMBOLIC extent is no obstacle. Put
    those together and the shape that discharges at a symbolic index is the one
    `BorrowRefoundGoals`' `NthPin` already runs on lists: RECURSE on the index,
    opening one element per step, so that every `natRec` the pin has to take is
    taken in a branch where the index is a CONSTRUCTOR.

    `WalkA` is that program on an array. The extent is spelled as the
    decomposition (`Add i (S r)`, per `decompExtent`), so the carves cite `Refl`
    and no transport is needed. -/

def walkDecls : Term := prog{
  fn WalkA [i] (i : Nat, r : Nat,
      arr : &mut (t : Array (Add i (S r)) (Σ (k : Nat). Nat)
                    ~> (%AVSetT) i (*res) (Add i (S r)) t)) -> &mut Nat {
    match i {
      Z => {
        let cell = &m (*arr)[Z ; 1 ; r | LeAdd (S Z) r | Refl];
        let e = &m (*cell)[0];
        match e { Pair(kk, vv) => &m *vv } },
      S(i2) => {
        let hd1 = &m (*arr)[Z ; 1 ; Add i2 (S r) | LeAdd (S Z) (Add i2 (S r)) | Refl];
        let h0 = &m (*hd1)[0];
        match h0 { Pair(k0, v0) => {
          let tl = &m (*arr)[1 ; Add i2 (S r)];
          WalkA(i2, r, tl) } } }
    } };
  () }

/-! ### §6.1 …and under the PACKED container — the flagship's actual signature

    `WalkA` is on a bare array. The flagship's `self` is the intrinsically packed
    map, so the pack-level pin (`PVSetN`) has to discharge FROM the array-level pin
    the call returns. `packWalk` is that composition, and it is the shape
    `GetMut`'s body should have. -/

def packWalk : Term := prog{
  fn WalkA [i] (i : Nat, r : Nat,
      arr : &mut (t : Array (Add i (S r)) (Σ (k : Nat). Nat)
                    ~> (%AVSetT) i (*res) (Add i (S r)) t)) -> &mut Nat {
    match i {
      Z => {
        let cell = &m (*arr)[Z ; 1 ; r | LeAdd (S Z) r | Refl];
        let e = &m (*cell)[0];
        match e { Pair(kk, vv) => &m *vv } },
      S(i2) => {
        let hd1 = &m (*arr)[Z ; 1 ; Add i2 (S r) | LeAdd (S Z) (Add i2 (S r)) | Refl];
        let h0 = &m (*hd1)[0];
        match h0 { Pair(k0, v0) => {
          let tl = &m (*arr)[1 ; Add i2 (S r)];
          WalkA(i2, r, tl) } } }
    } };
  fn PackWalk (i : Nat, r : Nat,
      self : &mut (s : Σ0 (a : Array (Add i (S r)) (Σ (k : Nat). Nat)).
                          AllK7 (Add i (S r)) a
                    ~> (%PVSetNT) (Add i (S r)) i (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => WalkA(i, r, &m *a) } };
  () }

/-- The NEGATIVE control: the same walk returning the KEY borrow. Everything else
    identical, so a green verdict here would mean the pin accepted an escaping
    borrow onto a cell the packed invariant reads. -/
def packWalkKey : Term := prog{
  fn WalkAKey [i] (i : Nat, r : Nat,
      arr : &mut (t : Array (Add i (S r)) (Σ (k : Nat). Nat)
                    ~> (%AVSetT) i (*res) (Add i (S r)) t)) -> &mut Nat {
    match i {
      Z => {
        let cell = &m (*arr)[Z ; 1 ; r | LeAdd (S Z) r | Refl];
        let e = &m (*cell)[0];
        match e { Pair(kk, vv) => &m *kk } },
      S(i2) => {
        let hd1 = &m (*arr)[Z ; 1 ; Add i2 (S r) | LeAdd (S Z) (Add i2 (S r)) | Refl];
        let h0 = &m (*hd1)[0];
        match h0 { Pair(k0, v0) => {
          let tl = &m (*arr)[1 ; Add i2 (S r)];
          WalkAKey(i2, r, tl) } } }
    } };
  () }

/-! ### §6.2 …and it writes the right cell, executing

    The E2E half: instantiate at extent 3 / index 1, walk, write `9` through the
    returned cursor, end the group, read the pack back. -/

def runBinding (t : Term) (name : String) : Option String :=
  match runProgram t with
  | .ok env => (env.lookup name).map Val.pretty
  | .error _ => none

def packWalkCaller : Term := prog{
  fn WalkA [i] (i : Nat, r : Nat,
      arr : &mut (t : Array (Add i (S r)) (Σ (k : Nat). Nat)
                    ~> (%AVSetT) i (*res) (Add i (S r)) t)) -> &mut Nat {
    match i {
      Z => {
        let cell = &m (*arr)[Z ; 1 ; r | LeAdd (S Z) r | Refl];
        let e = &m (*cell)[0];
        match e { Pair(kk, vv) => &m *vv } },
      S(i2) => {
        let hd1 = &m (*arr)[Z ; 1 ; Add i2 (S r) | LeAdd (S Z) (Add i2 (S r)) | Refl];
        let h0 = &m (*hd1)[0];
        match h0 { Pair(k0, v0) => {
          let tl = &m (*arr)[1 ; Add i2 (S r)];
          WalkA(i2, r, tl) } } }
    } };
  fn PackWalk (i : Nat, r : Nat,
      self : &mut (s : Σ0 (a : Array (Add i (S r)) (Σ (k : Nat). Nat)).
                          AllK7 (Add i (S r)) a
                    ~> (%PVSetNT) (Add i (S r)) i (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => WalkA(i, r, &m *a) } };
  let p = Pair(Arr(Pair(7, 1), Pair(7, 2), Pair(7, 3)),
               Pair(Refl, Pair(Refl, Pair(Refl, unit))));
  let q = &m p;
  let c = PackWalk(1, 1, q);
  *c := 9;
  () }

/-! ## §7 THE VERDICTS

    Read top to bottom, these say: the symbolic carve is fine, the pin at a
    symbolic index is not, and a WALK is what converts the second into the first.

        symCarveUnit      symbolic carve, nothing escaping           GREEN
        symCarveEsc       …value borrow escaping, NO pin             red   (§7.5)
        gmConc2at1open    §7.6's port control, prefix opened         GREEN
        gmConc2at1blind   §7.6's port control, blind                 red
        gmSymPinFold      BLIND carve at a SYMBOLIC index, pinned    red   ← (i)
        gmSymAt0          symbolic EXTENT, index Z                   GREEN
        gmSymAt1          symbolic EXTENT, index 1, prefix opened    GREEN
        gmSymAt1blind     …the same, prefix NOT opened               red
        decompExtent      extent spelled `Add i (S r)`, carve `Refl` GREEN
        gmSymPinDecomp    decomposition-spelled pin                  red   ← (ii)
        gmSymAt1Key       the KEY twin of `gmSymAt1`                 red
        walkDecls         THE WALK, bare array                       GREEN ← the answer
        packWalk          THE WALK, packed container                 GREEN
        packWalkKey       the KEY twin of the walk                   red
-/

example : progOk symCarveUnit = true := by native_decide
example : progRejects symCarveEsc
  "audit: self's payload (Pair Arr⟨σ1 ▷ σ13, (S Z) ▷ [Pair σ19 σ21], σ2 ▷ σ17⟩ σ7) does not have its owed type"
  = true := by native_decide

example : progOk gmConc2at1open = true := by native_decide
example : progRejects gmConc2at1blind
  "exits (Pair (arrCat (S Z) (S Z) σ4 [Pair σ8 σ10]) σ3), does not convert with the declared pin (Pair (arrRec"
  = true := by native_decide

/-- **SPELLING (i) IS REFUTED, and the print says why in one line.** The entry σ
    WAS refined to the composition — the declared pin's argument is the very same
    `arrCat σ1 (S σ2) σ13 (acons σ2 (Pair σ19 σ20) σ17)` spine the fill carries,
    with the entry value `σ20` where the fill has the exit `σ21`. The two sides do
    not differ in shape at all. They differ because the pin is a `natRec` ON THE
    INDEX `σ1`, and `σ1` is a σ, so it cannot take its first step. -/
example : progRejects gmSymPinFold
  "exits (Pair (arrCat σ1 (S σ2) σ13 (acons σ2 (Pair σ19 σ21) σ17)) σ7), does not convert with the declared pin (Pair (natRec"
  = true := by native_decide

example : progOk gmSymAt0 = true := by native_decide
example : progOk gmSymAt1 = true := by native_decide
example : progRejects gmSymAt1blind
  "exits (Pair (arrCat (S Z) (S σ1) σ8 (acons σ1 (Pair σ14 σ16) σ12)) σ6), does not convert with the declared pin (Pair (arrRec"
  = true := by native_decide

example : progOk decompExtent = true := by native_decide

/-- **SPELLING (ii) IS REFUTED, and for a DIFFERENT reason — this is the print to
    take to a design discussion.** The two sides are the same term modulo which σ
    stands at three leaves: the fill's carve pieces `σ14`/`σ18` and carved key
    `σ20` against the parameters `σ2`/`σ4`/`σ3`. Index `σ0`, residue `σ1` and the
    exit `σ22` in the value slot all MATCH. The decomposition spelling is the right
    shape and is unwritable for one reason only: `pinFill`'s prefix and suffix are
    minted by the carve, and a signature has no way to name them. -/
example : progRejects gmSymPinDecomp
  "exits (Pair (arrCat σ0 (S σ1) σ14 (acons σ1 (Pair σ20 σ22) σ18)) σ8), does not convert with the declared pin (Pair (arrCat σ0 (S σ1) σ2 (acons σ1 (Pair σ3 σ22) σ4)) σ8)."
  = true := by native_decide

/-- The key twin of the spelling that works: exit `σ19` in the key slot on the
    fill, in the value slot on the pin. -/
example : progRejects gmSymAt1Key
  "exits (Pair (acons (S σ1) (Pair σ11 σ12) (acons σ1 (Pair σ19 σ18) σ15)) σ6), does not convert with the declared pin (Pair (acons (S σ1) (Pair σ11 σ12) (acons σ1 (Pair σ17 σ19) σ15)) σ6)."
  = true := by native_decide

/-- **THE ANSWER.** A `GetMut` that WALKS to its slot discharges the fold-spelled
    pin at a SYMBOLIC index, bare and packed. -/
example : progOk walkDecls = true := by native_decide
example : progOk packWalk = true := by native_decide

example : progRejects packWalkKey
  "audit: arr's pin is not met — the exit payload, hole-filled at the issued borrows' exits (acons σ0 (Pair σ9 σ8) σ5), does not convert with the declared pin (acons σ0 (Pair σ7 σ9) σ5)."
  = true := by native_decide

/-! …and the caller checks AND runs: cell 1's value becomes 9, the keys are
    untouched, and the `AllK7` proof the group end re-mints is inhabited by the
    three `Refl`s that were there before. -/
example : progOk packWalkCaller = true := by native_decide
example : runBinding packWalkCaller "p"
  = some ("Pair [Pair (S (S (S (S (S (S (S Z))))))) (S Z), "
       ++ "Pair (S (S (S (S (S (S (S Z))))))) (S (S (S (S (S (S (S (S (S Z))))))))), "
       ++ "Pair (S (S (S (S (S (S (S Z))))))) (S (S (S Z)))] "
       ++ "(Pair Refl (Pair Refl (Pair Refl unit)))")
  := by native_decide

end Dllbc.Tests.SetHmProbe

end
