import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas

/-!
# `SetHmProbe`

Tests whether a pinned borrow contract on a get-mut-style operation can be
discharged when both the carve index and the array's extent are symbolic
rather than concrete. Two direct spellings of the update — an index-first
fold, and an `arrCat` decomposition — are asserted rejected: the checker
cannot fold across elements the body's control flow never opened. A walk
(recursing on the index so every step sees it as a constructor) is asserted
accepted, both on a bare array and under a packed container.

Everything here is library-level; no kernel change is needed or proposed.
-/

section

open Dllbc

namespace Dllbc.Tests.SetHmProbe

open Dllbc.StdLemmas (LeAdd LeRefl IdCongr IdSym AddZero)

/-- The checker's error string verbatim, or `"OK"` if the program is accepted. -/
def errOf (t : Term) : String :=
  match checkProgram t prog defer_check { Unit } with | .ok _ => "OK" | .error e => e

/-! ## The container

    `AllK7 n a` folds over the array asserting every key is `7`, reading no
    value. An escaping value borrow cannot break this invariant; an escaping
    key borrow can. -/

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

/-! ## Baseline: the pin-free symbolic carve

    Before asking about a pin, check what the un-pinned program does.
    `symCarveUnit` carves at a symbolic `i` inside the pack and escapes
    nothing; `symCarveEsc` is the identical body with the value borrow
    escaping. Here the decomposition (`i`, `r`, `hd`) arrives as parameters;
    later sections re-ask the same question with it minted across a call.

    The extent is an opaque `n` with `Le (S Z) n`, and the carve cites `hd`. -/

def symCarveUnit : Term := prog{
  fn G (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
        self : &mut (Σ0 (a : Array n (Σ (k : Nat). Nat)). AllK7 n a)) -> Unit {
    match self { Pair(a, H) => {
      let pre = &m (*a)[Z ; i ; S r | LeAdd i (S r) | hd];
      let cell = &m (*a)[i ; 1 ; r];
      let e = &m (*cell)[0];
      match e { Pair(kk, vv) => () } } } };
  () }

def symCarveEsc : Term := prog defer_check {
  fn G (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
        self : &mut (Σ0 (a : Array n (Σ (k : Nat). Nat)). AllK7 n a)) -> &mut Nat {
    match self { Pair(a, H) => {
      let pre = &m (*a)[Z ; i ; S r | LeAdd i (S r) | hd];
      let cell = &m (*a)[i ; 1 ; r];
      let e = &m (*cell)[0];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

/-! ## Spelling (i): the fold-spelled update, at a symbolic index

    `AVSetT i v` is an index-first, cons-view update: keep the key, replace
    the value. `PVSetNT` lifts it to the pack at a symbolic extent. This is
    the spelling a `SetHM` written the obvious way would have. -/

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

def PVSetNT : Term := prog defer_check {
  λ (N : Nat). λ (I : Nat). λ (V : Nat).
    λ (P : Σ0 (a : Array N (Σ (k : Nat). Nat)). AllK7 N a).
      elim P return (λ (Pz : Σ0 (a : Array N (Σ (k : Nat). Nat)). AllK7 N a).
                       Σ0 (a : Array N (Σ (k : Nat). Nat)). AllK7 N a) {
        Pair (A) (H) => Pair ((%AVSetT) I V N A) H } }

/-! ### Concrete-index controls

    A pin at a concrete index discharges when the body's flow opened the
    prefix (`gmConc2at1open`), and is refused at a blind carve
    (`gmConc2at1blind`). These fix the known-good baseline before moving to a
    symbolic index below. -/

def gmConc2at1open : Term := prog{
  fn G (self : &mut (s : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a
                       ~> (%PVSetNT) 2 1 (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e0 = &m (*a)[0];
      match e0 { Pair(k0, v0) => {
        let e = &m (*a)[1];
        match e { Pair(kk, vv) => &m *vv } } } } } };
  () }

def gmConc2at1blind : Term := prog defer_check {
  fn G (self : &mut (s : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a
                       ~> (%PVSetNT) 2 1 (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e = &m (*a)[1];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

/-! ### Symbolic extent, symbolic index -/

def gmSymPinFold : Term := prog defer_check {
  fn G (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
        self : &mut (s : Σ0 (a : Array n (Σ (k : Nat). Nat)). AllK7 n a
                       ~> (%PVSetNT) n i (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let pre = &m (*a)[Z ; i ; S r | LeAdd i (S r) | hd];
      let cell = &m (*a)[i ; 1 ; r];
      let e = &m (*cell)[0];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

/-! ### Isolating the cause: symbolic index, or symbolic extent?

    `gmSymPinFold`'s refusal could come from the symbolic extent or the
    symbolic index; the two candidates have opposite consequences.
    `gmSymAt0` keeps the extent symbolic (`S r`) and makes the index the
    literal `Z`; `gmSymAt1` keeps the extent symbolic and takes one step,
    opening element 0 the way a walk would. These two are the base case and
    the inductive step of a walking get-mut.

    (An extent written as a bare `S r`, with no decomposition equation
    supplying it, is rejected by the carve before any of this — an extent
    must always be spelled as an opaque variable plus a decomposition
    equation.) -/

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

/-- The same step without opening element 0 — the blind version of
    `gmSymAt1`, isolating the open from the extent. -/
def gmSymAt1blind : Term := prog defer_check {
  fn G (m : Nat, r : Nat, hd : Id Nat m (Add (S Z) (S r)),
        self : &mut (s : Σ0 (a : Array m (Σ (k : Nat). Nat)). AllK7 m a
                       ~> (%PVSetNT) m (S Z) (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let pre = &m (*a)[Z ; 1 ; S r | LeAdd (S Z) (S r) | hd];
      let cell = &m (*a)[1 ; 1 ; r];
      let e = &m (*cell)[0];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

/-! ## Spelling (ii): the decomposition-spelled update

    The fold above cannot step past a symbolic prefix, so state the update
    instead in the form the fill already has: `arrCat i (S r) lo (acons r
    (Pair k (*res)) hi)`, matching the fill's spine by construction rather
    than by computation. The pieces `lo`/`k`/`hi` are not in scope at a
    signature, so the only way to write this at all is to take them as
    parameters — which is what this measures: whether the discharge succeeds
    when the two sides have the same shape and differ only in which
    variables stand at the leaves.

    `decompExtent` first checks the cheaper prerequisite: an extent spelled
    as the decomposition itself (`Array (Add i (S r))`), which lets the
    carve cite `Refl` and drop the transport. -/

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

def gmSymPinDecomp : Term := prog defer_check {
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

/-! ## Negative control: the key cell

    `gmSymAt1` with `&m *vv` replaced by `&m *kk`. The fill puts the shared
    exit in the key slot while the pin puts it in the value slot, so a
    discharge that accepted this would accept an escaping borrow onto a
    hashed cell. -/

def gmSymAt1Key : Term := prog defer_check {
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

/-! ## The walk

    The index-first fold steps exactly when the body's flow opened the
    element in front of it, and a symbolic extent alone is no obstacle. So
    the shape that discharges at a symbolic index recurses on the index,
    opening one element per step, so that every `natRec` the pin needs is
    taken in a branch where the index is a constructor.

    `walkDecls` is that program on a bare array. The extent is spelled as
    the decomposition (`Add i (S r)`, as in `decompExtent`), so the carves
    cite `Refl` and no transport is needed. -/

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

/-! ### Under the packed container

    A get-mut's `self` is typically the intrinsically packed map, so the
    pack-level pin (`PVSetNT`) has to discharge from the array-level pin the
    call returns. `packWalk` is that composition. -/

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

/-- Negative control: the same walk returning the key borrow. Everything
    else identical, so a green verdict here would mean the pin accepted an
    escaping borrow onto a cell the packed invariant reads. -/
def packWalkKey : Term := prog defer_check {
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

/-! ### It writes the right cell, executing

    Instantiate at extent 3 / index 1, walk, write `9` through the returned
    cursor, end the group, read the pack back. -/

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

/-! ## Verdicts

    Read top to bottom: the symbolic carve is fine, the pin at a symbolic
    index is not, and a walk is what converts the second case into the
    first.

        symCarveUnit      symbolic carve, nothing escaping           GREEN
        symCarveEsc       …value borrow escaping, no pin             red
        gmConc2at1open    concrete-index control, prefix opened      GREEN
        gmConc2at1blind   concrete-index control, blind              red
        gmSymPinFold      blind carve at a symbolic index, pinned    red   ← (i)
        gmSymAt0          symbolic extent, index Z                   GREEN
        gmSymAt1          symbolic extent, index 1, prefix opened    GREEN
        gmSymAt1blind     …the same, prefix not opened               red
        decompExtent      extent spelled `Add i (S r)`, carve `Refl` GREEN
        gmSymPinDecomp    decomposition-spelled pin                  red   ← (ii)
        gmSymAt1Key       the key twin of `gmSymAt1`                 red
        walkDecls         the walk, bare array                      GREEN ← the answer
        packWalk          the walk, packed container                GREEN
        packWalkKey       the key twin of the walk                  red
-/

example : progOk symCarveUnit = true := by native_decide
example : progRejects symCarveEsc
  "audit: self's payload (Pair Arr⟨σ1 ▷ σ13, (S Z) ▷ [Pair σ19 σ21], σ2 ▷ σ17⟩ σ7) does not have its owed type"
  = true := by native_decide

example : progOk gmConc2at1open = true := by native_decide
example : progRejects gmConc2at1blind
  "exits (Pair (arrCat (S Z) (S Z) σ4 [Pair σ8 σ10]) σ3), does not convert with the declared pin (Pair (arrRec"
  = true := by native_decide

/-- Spelling (i) is refused: the two sides are the same `arrCat` spine and
    differ only in the entry vs. exit value at one leaf. The refusal is
    because the pin is a `natRec` on the index `σ1`, which is symbolic, so
    it cannot take its first step. -/
example : progRejects gmSymPinFold
  "exits (Pair (arrCat σ1 (S σ2) σ13 (acons σ2 (Pair σ19 σ21) σ17)) σ7), does not convert with the declared pin (Pair (natRec"
  = true := by native_decide

example : progOk gmSymAt0 = true := by native_decide
example : progOk gmSymAt1 = true := by native_decide
example : progRejects gmSymAt1blind
  "exits (Pair (arrCat (S Z) (S σ1) σ8 (acons σ1 (Pair σ14 σ16) σ12)) σ6), does not convert with the declared pin (Pair (arrRec"
  = true := by native_decide

example : progOk decompExtent = true := by native_decide

/-- Spelling (ii) is refused for a different reason: the two sides are the
    same term modulo which variable stands at three leaves — the fill's
    carve pieces `σ14`/`σ18`/`σ20` against the parameters `σ2`/`σ4`/`σ3`
    standing in for them. The decomposition spelling is the right shape and
    is unwritable in general for one reason: the carve mints the prefix and
    suffix, and a signature has no way to name them. -/
example : progRejects gmSymPinDecomp
  "exits (Pair (arrCat σ0 (S σ1) σ14 (acons σ1 (Pair σ20 σ22) σ18)) σ8), does not convert with the declared pin (Pair (arrCat σ0 (S σ1) σ2 (acons σ1 (Pair σ3 σ22) σ4)) σ8)."
  = true := by native_decide

/-- The key twin of the spelling that works: the exit `σ19` sits in the key
    slot on the fill but in the value slot on the pin. -/
example : progRejects gmSymAt1Key
  "exits (Pair (acons (S σ1) (Pair σ11 σ12) (acons σ1 (Pair σ19 σ18) σ15)) σ6), does not convert with the declared pin (Pair (acons (S σ1) (Pair σ11 σ12) (acons σ1 (Pair σ17 σ19) σ15)) σ6)."
  = true := by native_decide

/-- A get-mut that walks to its slot discharges the fold-spelled pin at a
    symbolic index, both bare and packed. -/
example : progOk walkDecls = true := by native_decide
example : progOk packWalk = true := by native_decide

example : progRejects packWalkKey
  "audit: arr's pin is not met — the exit payload, hole-filled at the issued borrows' exits (acons σ0 (Pair σ9 σ8) σ5), does not convert with the declared pin (acons σ0 (Pair σ7 σ9) σ5)."
  = true := by native_decide

/-! The caller both checks and runs: cell 1's value becomes 9, the keys are
    untouched, and the `AllK7` proof the group end re-mints is inhabited by
    the three `Refl`s that were there before. -/
example : progOk packWalkCaller = true := by native_decide
example : runBinding packWalkCaller "p"
  = some ("Pair [Pair (S (S (S (S (S (S (S Z))))))) (S Z), "
       ++ "Pair (S (S (S (S (S (S (S Z))))))) (S (S (S (S (S (S (S (S (S Z))))))))), "
       ++ "Pair (S (S (S (S (S (S (S Z))))))) (S (S (S Z)))] "
       ++ "(Pair Refl (Pair Refl (Pair Refl unit)))")
  := by native_decide

end Dllbc.Tests.SetHmProbe

end
