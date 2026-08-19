import Dllbc.Tests.HashMap

/-!
# The hashmap flagship's PINNED ops — S4: GetMut with a functional contract

The 2026-08-17 run pinned GetMut/GetMutOrInsert as executing-only: a returned
borrow kept its group open and the audit could not re-type the packed invariant
with a loan inside slots. Main has since landed the borrow re-founding
(12-design, M35): `&mut (s : τ ~> E)` one-slot contracts, `*res` naming the
issued borrow's exit payload, discharge by hole-filling, D9 value components,
and `atake`/`adrop` — which `ArrCatIota` measured into "the blind carve at a
symbolic index CHECKS". This module is the hashmap instance: `SetHM` (the
pack→pack model update, decomposition-first), the pinned bucket walk, and
`GetMutHM`/`GetMutOrInsertHM` per 13-'s un-deferred spec, closing with the
two-call round-trip chain (`twoGetMutChain` at hashmap scale).

**The one spelling rule everything here hangs on:** every new spec function
compares keys as `Eqb QUERY entrykey` — `FindL`'s own argument order — so that
the walk's branch equations (`if e : Eqb key *kk`) name the very spine the
pin's normalization gets stuck on. The S1 walks bound the FLIPPED orientation
(`Eqb *kk key`) and repaired it with lemmas; a pin has no lemma slot, so the
orientation is load-bearing here.
-/

section

open Dllbc
open Dllbc.StdLemmas (LeRefl LeAdd LeAddL LeTrans LePredL
  AddSucc AddZero IdTrans IdCongr IdSym NatRw BoolFT BoolTF
  LeRwL LeRwR EqbRefl EqbTrueEq EqbSym IfDec Znots SInj
  Mod ModLtN Sub AddSubCancel Mul)

namespace Dllbc.Tests.HashMap

/-! ## (xxiv) The bucket-level update, in the pin's orientation

    `BSetK q v l` — the entry at key `q` gets value `v`, keys and structure
    untouched, no-op when `q` is absent. Mirrors `FindL` clause for clause so
    the two can never disagree about which entry is "the" hit. -/

def BSetK : Term := prog{
  λ (Q : Nat). λ (V : Nat). λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). List (Σ (k : Nat). Nat)) {
      Nil => Nil,
      Cons (E) (T) Rec =>
        elim E return (λ (Em : Σ (k : Nat). Nat). List (Σ (k : Nat). Nat)) {
          Pair (K2) (V2) =>
            elim (Eqb Q K2) return (λ (Bm : Bool). List (Σ (k : Nat). Nat)) {
              True => Cons(Pair(K2, V), T),
              False => Cons(Pair(K2, V2), Rec) } } } }

example : chkL prog{ Refl } prog{ Id (List (Σ (k : Nat). Nat))
  (BSetK 3 99 Cons(Pair(1, 10), Cons(Pair(3, 30), Nil)))
  Cons(Pair(1, 10), Cons(Pair(3, 99), Nil)) } = true := by native_decide
example : chkL prog{ Refl } prog{ Id (List (Σ (k : Nat). Nat))
  (BSetK 7 99 Cons(Pair(1, 10), Nil)) Cons(Pair(1, 10), Nil) } = true := by native_decide
example : chkL prog{ Refl } prog{ Id (List (Σ (k : Nat). Nat))
  (BSetK 3 99 Cons(Pair(3, 30), Cons(Pair(3, 31), Nil)))
  Cons(Pair(3, 99), Cons(Pair(3, 31), Nil)) } = true := by native_decide

/-- Presence survives a non-hit head: from `Eqb q k0 ≡ False` and presence in
    the whole bucket, presence in the tail — the walk's recursion premise. -/
def HitTailEv : Term := prog{
  λ (Q : Nat). λ (K0 : Nat). λ (V0 : Nat). λ (T : List (Σ (k : Nat). Nat)).
  λ (E : Id Bool (Eqb Q K0) False).
  λ (H : Id Bool (HitL Q Cons(Pair(K0, V0), T)) True).
    IdTrans Bool (HitL Q T) (HitL Q Cons(Pair(K0, V0), T)) True
      (IdSym Bool (HitL Q Cons(Pair(K0, V0), T)) (HitL Q T)
        (IdCongr Bool Bool
          (λ (W : Bool). IsSomeB (elim W return (λ (Bm : Bool). Σ (bb : Bool). OptP bb Nat) {
            True => SomeN V0, False => FindL Q T }))
          (Eqb Q K0) False E))
      H }
def HitTailEvTy : Term := prog{
  Π (Q : Nat) → Π (K0 : Nat) → Π (V0 : Nat) → Π (T : List (Σ (k : Nat). Nat)) →
    Id Bool (Eqb Q K0) False → Id Bool (HitL Q Cons(Pair(K0, V0), T)) True →
    Id Bool (HitL Q T) True }
example : chkL HitTailEv HitTailEvTy = true := by native_decide

/-- The hit leg's return conjunct: at `Eqb q k0 ≡ True`, the head's value IS
    the bucket's answer at `q`. Stated in the D9 orientation (`Some (*r)` on
    the left) so the constructed proof's type is verbatim the declared one. -/
def FindEvHit : Term := prog{
  λ (Q : Nat). λ (K0 : Nat). λ (V0 : Nat). λ (T : List (Σ (k : Nat). Nat)).
  λ (E : Id Bool (Eqb Q K0) True).
    IdSym OptN (FindL Q Cons(Pair(K0, V0), T)) (SomeN V0)
      (IdCongr Bool OptN
        (λ (W : Bool). elim W return (λ (Bm : Bool). Σ (bb : Bool). OptP bb Nat) {
          True => SomeN V0, False => FindL Q T })
        (Eqb Q K0) True E) }
def FindEvHitTy : Term := prog{
  Π (Q : Nat) → Π (K0 : Nat) → Π (V0 : Nat) → Π (T : List (Σ (k : Nat). Nat)) →
    Id Bool (Eqb Q K0) True →
    Id OptN (SomeN V0) (FindL Q Cons(Pair(K0, V0), T)) }
example : chkL FindEvHit FindEvHitTy = true := by native_decide

/-- The miss leg's transport: a non-hit head is skipped by the lookup, so tail
    evidence lifts to the whole bucket. -/
def FindTailEv : Term := prog{
  λ (Q : Nat). λ (K0 : Nat). λ (V0 : Nat). λ (T : List (Σ (k : Nat). Nat)).
  λ (E : Id Bool (Eqb Q K0) False).
    IdSym OptN (FindL Q Cons(Pair(K0, V0), T)) (FindL Q T)
      (IdCongr Bool OptN
        (λ (W : Bool). elim W return (λ (Bm : Bool). Σ (bb : Bool). OptP bb Nat) {
          True => SomeN V0, False => FindL Q T })
        (Eqb Q K0) False E) }
def FindTailEvTy : Term := prog{
  Π (Q : Nat) → Π (K0 : Nat) → Π (V0 : Nat) → Π (T : List (Σ (k : Nat). Nat)) →
    Id Bool (Eqb Q K0) False →
    Id OptN (FindL Q T) (FindL Q Cons(Pair(K0, V0), T)) }
example : chkL FindTailEv FindTailEvTy = true := by native_decide

/-! ## (xxv) THE GATE — does the key-driven walk discharge its pin?

    The unmeasured mechanism this whole module rests on: the walk branches on
    `Eqb key *kk` — a STUCK Bool — and the pin `BSetK key (*res) t`, normalized
    at the audit, is stuck at exactly that `elim (Eqb key σkk)`. The audit is
    branch-swept; the question is whether the branch's equation feeds its
    conversion. `NthPin` (BorrowRefoundGoals) never asks it — its recursion is
    on a Nat index and each branch refines a CONSTRUCTOR. The hit leg needs the
    True arm taken, the miss leg the False arm (whose result must then converge
    with the recursive call's projected pin at the shared exit σ). Pin-only
    (plain `&mut Nat` return) so a failure names the pin, not D9. -/

def bktGetPinOnly : Term := prog defer_check {
  fn BktGetP [fuel] (fuel : Nat, key : Nat,
      b : &mut (t : List (Σ (k : Nat). Nat) ~> BSetK key (*res) t),
      Hin : Id Bool (HitL key (*b)) True,
      Hf : Le (LenE (*b)) fuel) -> &mut Nat {
    match b {
      Nil => botElim Unit (BoolFT Hin),
      Cons(Pair(kk, vv), tl) => match fuel {
        Z => botElim Unit Hf,
        S(f2) => {
          let K0 = *kk;
          let V0 = *vv;
          let T0 = *tl;
          if e : Eqb key *kk {
            &m *vv
          } else {
            BktGetP(f2, key, &m *tl, HitTailEv key K0 V0 T0 e Hin, Hf)
          } } } } };
  () }

/-- **THE GATE'S VERDICT — red, and the print is the session's headline
    finding.** The fill is the hit leg's `Cons (Pair σ18 σ22) σ17`; the pin
    normalized to a `boolRec` STUCK on `Eqb σ11 σ18` whose True arm is
    LITERALLY that fill — one ι-step away, gated on the branch equation the
    body's `if e :` bound. The audit's conversion does not consult branch
    equations, and `Eqb` is a fold, stuck even at syntactically equal neutral
    arguments (`EqbRefl` is a LEMMA, and a pin has no lemma slot). So no
    KEY-comparing update can ever discharge a pin over symbolic keys — not by
    accident but on principle: **a pin's data must be pin-computable.** The
    key→position conversion cannot happen inside the pin, so it happens in the
    signature: the walk below recurses on a POSITION (constructor refinement,
    `NthPin`'s measured mechanism) and the position joins the parameters.
    Kernel-scope alternatives, named not attempted: branch-equation-aware
    audit conversion, or a neutral-reflexivity ι for `Eqb`. -/
example : progRejects bktGetPinOnly
  "does not convert with the declared pin (boolRec" = true := by native_decide

/-! ### The position vocabulary: where `key` sits, and the update that needs
    no comparison -/

/-- `FindPosL q l` — the hit's position; `LenE l` when absent (every miss adds
    one `S`), which is exactly the or_insert write site. -/
def FindPosL : Term := prog{
  λ (Q : Nat). λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Nat) {
      Nil => Z,
      Cons (E) (T) Rec =>
        elim E return (λ (Em : Σ (k : Nat). Nat). Nat) {
          Pair (K2) (V2) =>
            elim (Eqb Q K2) return (λ (Bm : Bool). Nat) {
              True => Z,
              False => S(Rec) } } } }

example : chkL prog{ Refl } prog{ Id Nat
  (FindPosL 3 Cons(Pair(1, 10), Cons(Pair(3, 30), Nil))) 1 } = true := by native_decide
example : chkL prog{ Refl } prog{ Id Nat
  (FindPosL 9 Cons(Pair(1, 10), Cons(Pair(3, 30), Nil))) 2 } = true := by native_decide

/-- `BSetP p v l` — value at position `p` becomes `v`, key and structure kept,
    no-op past the end. Index-first, so a constructor-refined `p` steps it with
    NO key comparison anywhere — this is what makes it pin-dischargeable where
    `BSetK` is not. -/
def BSetP : Term := prog{
  λ (P : Nat). λ (V : Nat).
    elim P return (λ (Pz : Nat). Π (L : List (Σ (k : Nat). Nat)) → List (Σ (k : Nat). Nat)) {
      Z => λ (L : List (Σ (k : Nat). Nat)).
        elim L return (λ (Lm : List (Σ (k : Nat). Nat)). List (Σ (k : Nat). Nat)) {
          Nil => Nil,
          Cons (E) (T) Rec =>
            Cons(elim E return (λ (Em : Σ (k : Nat). Nat). Σ (k : Nat). Nat) {
              Pair (K2) (V2) => Pair(K2, V) }, T) },
      S (P2) Rec => λ (L : List (Σ (k : Nat). Nat)).
        elim L return (λ (Lm : List (Σ (k : Nat). Nat)). List (Σ (k : Nat). Nat)) {
          Nil => Nil,
          Cons (E) (T) Rec2 => Cons(E, Rec T) } } }

example : chkL prog{ Refl } prog{ Id (List (Σ (k : Nat). Nat))
  (BSetP 1 99 Cons(Pair(1, 10), Cons(Pair(3, 30), Nil)))
  Cons(Pair(1, 10), Cons(Pair(3, 99), Nil)) } = true := by native_decide

/-- Position `Z` on a hit bucket means the HEAD is the hit. -/
def PosZHit : Term := prog{
  λ (Q : Nat). λ (K0 : Nat). λ (V0 : Nat). λ (T : List (Σ (k : Nat). Nat)).
  λ (Hp : Id Nat Z (FindPosL Q Cons(Pair(K0, V0), T))).
    IfDec (Eqb Q K0) (Id Bool (Eqb Q K0) True)
      (λ (Et : Id Bool (Eqb Q K0) True). Et)
      (λ (Ef : Id Bool (Eqb Q K0) False).
        botElim (Id Bool (Eqb Q K0) True)
          (Znots (FindPosL Q T)
            (IdTrans Nat Z (FindPosL Q Cons(Pair(K0, V0), T)) (S (FindPosL Q T)) Hp
              (IdCongr Bool Nat (λ (W : Bool). elim W return (λ (Bm : Bool). Nat) {
                True => Z, False => S (FindPosL Q T) }) (Eqb Q K0) False Ef)))) }
def PosZHitTy : Term := prog{
  Π (Q : Nat) → Π (K0 : Nat) → Π (V0 : Nat) → Π (T : List (Σ (k : Nat). Nat)) →
    Id Nat Z (FindPosL Q Cons(Pair(K0, V0), T)) → Id Bool (Eqb Q K0) True }
example : chkL PosZHit PosZHitTy = true := by native_decide

/-- Position `S p2` on a bucket means the head MISSED and `p2` locates the key
    in the tail — the walk's recursion evidence, in one package. -/
def PosSStep : Term := prog{
  λ (Q : Nat). λ (K0 : Nat). λ (V0 : Nat). λ (T : List (Σ (k : Nat). Nat)). λ (P2 : Nat).
  λ (Hp : Id Nat (S P2) (FindPosL Q Cons(Pair(K0, V0), T))).
    IfDec (Eqb Q K0) ((Id Bool (Eqb Q K0) False) × (Id Nat P2 (FindPosL Q T)))
      (λ (Et : Id Bool (Eqb Q K0) True).
        botElim ((Id Bool (Eqb Q K0) False) × (Id Nat P2 (FindPosL Q T)))
          (Znots P2 (IdSym Nat (S P2) Z
            (IdTrans Nat (S P2) (FindPosL Q Cons(Pair(K0, V0), T)) Z Hp
              (IdCongr Bool Nat (λ (W : Bool). elim W return (λ (Bm : Bool). Nat) {
                True => Z, False => S (FindPosL Q T) }) (Eqb Q K0) True Et)))))
      (λ (Ef : Id Bool (Eqb Q K0) False).
        Pair(Ef, SInj P2 (FindPosL Q T)
          (IdTrans Nat (S P2) (FindPosL Q Cons(Pair(K0, V0), T)) (S (FindPosL Q T)) Hp
            (IdCongr Bool Nat (λ (W : Bool). elim W return (λ (Bm : Bool). Nat) {
              True => Z, False => S (FindPosL Q T) }) (Eqb Q K0) False Ef)))) }
def PosSStepTy : Term := prog{
  Π (Q : Nat) → Π (K0 : Nat) → Π (V0 : Nat) → Π (T : List (Σ (k : Nat). Nat)) →
  Π (P2 : Nat) → Id Nat (S P2) (FindPosL Q Cons(Pair(K0, V0), T)) →
    (Id Bool (Eqb Q K0) False) × (Id Nat P2 (FindPosL Q T)) }
example : chkL PosSStep PosSStepTy = true := by native_decide

/-! ### THE WALK, position-driven — and it discharges

    `NthPin`'s mechanism at the bucket: recurse on `p`, so every `natRec` the
    pin owes steps in a branch where `p` is a CONSTRUCTOR. The key never needs
    comparing at pin level; the D9 evidence reconstructs the `FindL` claim
    from the position facts, value-level, where lemmas are allowed. -/

def bktGetAtDecl : Term := prog{
  fn BktGetAt [p] (p : Nat, key : Nat,
      b : &mut (t : List (Σ (k : Nat). Nat) ~> BSetP p (*res) t),
      Hhit : Id Bool (HitL key (*b)) True,
      Hpos : Id Nat p (FindPosL key (*b)))
      -> Σ (r : &mut Nat). Id OptN (SomeN (*r)) (FindL key (old *b)) {
    match b {
      Nil => botElim Unit (BoolFT Hhit),
      Cons(Pair(kk, vv), tl) => {
        let K0 = *kk;
        let V0 = *vv;
        let T0 = *tl;
        match p {
          Z => Pair(&m *vv, FindEvHit key K0 V0 T0 (PosZHit key K0 V0 T0 Hpos)),
          S(p2) => {
            let Ep = PosSStep key K0 V0 T0 p2 Hpos;
            let Emiss = FstT (Id Bool (Eqb key K0) False) (Id Nat p2 (FindPosL key T0)) Ep;
            let Epos2 = SndT (Id Bool (Eqb key K0) False) (Id Nat p2 (FindPosL key T0)) Ep;
            let Pair(r2, h2) = BktGetAt(p2, key, &m *tl,
              HitTailEv key K0 V0 T0 Emiss Hhit, Epos2);
            let W0 = *r2;
            Pair(r2, IdTrans OptN (SomeN W0) (FindL key T0)
              (FindL key Cons(Pair(K0, V0), T0)) h2
              (FindTailEv key K0 V0 T0 Emiss))
          } } } } };
  () }

example : progOk bktGetAtDecl = true := by native_decide

/-! ## (xxvii) The slot split, spelled so the pin can cite it

    The carve at slot `Mod key cap` must present its split point as terms the
    pin's own normalization produces — `SlotOfE`'s MINTED σ's cannot convert
    with `SetHM`'s internal `Mod`/`CoMod` spines, so the pinned op carves at
    the literal applications and cites `ModSplit` instead of a minted `hd`. -/

/-- The residue: everything after `key`'s slot. `cap = Mod key cap + S (CoMod
    key cap)` whenever `1 ≤ cap` — that is `ModSplit`. -/
def CoMod : Term := prog{ λ (Q : Nat). λ (C : Nat). Sub C (S (Mod Q C)) }

def ModSplit : Term := prog{
  λ (Q : Nat). λ (C : Nat). λ (H : Le (S Z) C).
    IdSym Nat (Add (Mod Q C) (S (CoMod Q C))) C
      (IdTrans Nat (Add (Mod Q C) (S (CoMod Q C))) (S (Add (Mod Q C) (CoMod Q C))) C
        (AddSucc (Mod Q C) (CoMod Q C))
        (AddSubCancel C (S (Mod Q C)) (ModLtN Q C H))) }
def ModSplitTy : Term := prog{
  Π (Q : Nat) → Π (C : Nat) → Le (S Z) C →
    Id Nat C (Add (Mod Q C) (S (CoMod Q C))) }
example : chkL ModSplit ModSplitTy = true := by native_decide

-- It computes: cap 5, key 7 → slot 2, residue 2; cap 32, key 1056 → slot 0.
example : chkL prog{ Refl } prog{ Id Nat 5 (Add (Mod 7 5) (S (CoMod 7 5))) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id Nat (CoMod 7 5) 2 } = true := by native_decide

/-! ## (xxviii) `SetHM` — the pack→pack model update, decomposition-first

    The pin's whole job is to CONVERT with the hole-filled exit, so `SetHM`
    names the carve's pieces with `atake`/`adrop` at the very split terms the
    pinned body carves at (`Mod q cap`, `CoMod q cap`) — `AVSetDecT`'s shape
    (ArrCatIota §3.1) lifted to the pack, with the element work done by
    `BSetK` on the `acons`-headed suffix. The invariant value rides through
    untouched, exactly as the toy's `PVSetDecT` carries `H`: a value write
    keeps every clause's inhabitant. -/

def BumpHead : Term := prog{
  λ (Q : Nat). λ (V : Nat). λ (R : Nat). λ (A : Array (S R) (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))).
        Array Mz (List (Σ (k : Nat). Nat)))
      Arr()
      (λ (M : Nat). λ (X : List (Σ (k : Nat). Nat)).
        λ (XS : Array M (List (Σ (k : Nat). Nat))).
        λ (Ih : Array M (List (Σ (k : Nat). Nat))).
          acons M (BSetK Q V X) XS)
      (S R) A }

def SetHM : Term := prog{
  λ (Q : Nat). λ (V : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
        Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
          Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
      Pair (Cap) (R1) =>
        elim R1 return (λ (H1 : Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))). HMInvT Cap load n slots).
            Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
              Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
          Pair (Load) (R2) =>
            elim R2 return (λ (H2 : Σ (n : Nat).
                Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                  HMInvT Cap Load n slots).
                Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                  Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
              Pair (N) (R3) =>
                elim R3 return (λ (H3 : Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                    HMInvT Cap Load N slots).
                    Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
                  Pair (Slots) (Inv) =>
                    Pair(Cap, Pair(Load, Pair(N, Pair(
                      arrCat (Mod Q Cap) (S (CoMod Q Cap))
                        (atake (Mod Q Cap) (S (CoMod Q Cap)) Slots)
                        (BumpHead Q V (CoMod Q Cap)
                          (adrop (Mod Q Cap) (S (CoMod Q Cap)) Slots)),
                      Inv)))) } } } } }

-- It computes through the spec lookup: the hit key's answer moves, the frame
-- (a DIFFERENT key hashing to the same slot, and the size) does not.
example : chkL prog{ Refl } prog{ Id OptN (FindHM 3 (SetHM 3 99 hmEx)) (SomeN 99) }
  = true := by native_decide
example : chkL prog{ Refl } prog{ Id OptN (FindHM 5 (SetHM 3 99 hmEx)) NoneN }
  = true := by native_decide
example : chkL prog{ Refl } prog{ Id OptN (FindHM 7 (SetHM 7 99 hmEx)) NoneN }
  = true := by native_decide
example : chkL prog{ Refl } prog{ Id Nat (SizeHM (SetHM 3 99 hmEx)) 1 } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id Nat (CapHM (SetHM 3 99 hmEx)) 2 } = true := by
  native_decide

/-- `SetHM` preserves the size — the second call's fuel bound. Nested Σ-elims
    to the leaf, where both sides compute to the same `N` and `Refl` closes. -/
def SetHMSize : Term := prog{
  λ (Q : Nat). λ (V : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
        Id Nat (SizeHM (SetHM Q V H0)) (SizeHM H0)) {
      Pair (Cap) (R1) =>
        elim R1 return (λ (H1 : Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))). HMInvT Cap load n slots).
            Id Nat (SizeHM (SetHM Q V Pair(Cap, H1))) (SizeHM Pair(Cap, H1))) {
          Pair (Load) (R2) =>
            elim R2 return (λ (H2 : Σ (n : Nat).
                Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                  HMInvT Cap Load n slots).
                Id Nat (SizeHM (SetHM Q V Pair(Cap, Pair(Load, H2))))
                  (SizeHM Pair(Cap, Pair(Load, H2)))) {
              Pair (N) (R3) =>
                elim R3 return (λ (H3 : Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                    HMInvT Cap Load N slots).
                    Id Nat (SizeHM (SetHM Q V Pair(Cap, Pair(Load, Pair(N, H3)))))
                      (SizeHM Pair(Cap, Pair(Load, Pair(N, H3))))) {
                  Pair (Slots) (Inv) => Refl } } } } }
def SetHMSizeTy : Term := prog{
  Π (Q : Nat) → Π (V : Nat) →
  Π (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) →
    Id Nat (SizeHM (SetHM Q V Hm)) (SizeHM Hm) }
example : chkL SetHMSize SetHMSizeTy = true := by native_decide

/-! ## (xxix) The map level — `SetHMAt`, and the pinned `GetMutHM`

    The occurs check closes the literal-spine route: a carve citing
    `ModSplit key cap` would refine `σcap := Add (Mod key σcap) …` — cyclic —
    so the slot index and residue enter as PARAMETERS with their equations as
    evidence (`hm-probe-mod`'s forced shape, re-derived at the pin), and the
    pin cites them: `SetHMAt i rr p (*res) s`, `gmDecSymPin`'s exact shape.
    The KEY leaves the pin entirely — slot `i` and cell `p` are the
    pin-computable data; `key` stays in the D9 return conjunct and the
    equations (`Him`/`Hhit`/`Hpos`) tying the data to it. The caller mints
    `i`/`rr` as `Mod`/`CoMod` and discharges `Hd` with `ModSplit` — which is
    what (xxvii) was for. -/

def BumpHeadP : Term := prog{
  λ (P : Nat). λ (V : Nat). λ (R : Nat). λ (A : Array (S R) (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))).
        Array Mz (List (Σ (k : Nat). Nat)))
      Arr()
      (λ (M : Nat). λ (X : List (Σ (k : Nat). Nat)).
        λ (XS : Array M (List (Σ (k : Nat). Nat))).
        λ (Ih : Array M (List (Σ (k : Nat). Nat))).
          acons M (BSetP P V X) XS)
      (S R) A }

def SetHMAt : Term := prog{
  λ (I : Nat). λ (R : Nat). λ (P : Nat). λ (V : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
        Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
          Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
      Pair (Cap) (R1) =>
        elim R1 return (λ (H1 : Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))). HMInvT Cap load n slots).
            Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
              Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
          Pair (Load) (R2) =>
            elim R2 return (λ (H2 : Σ (n : Nat).
                Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                  HMInvT Cap Load n slots).
                Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                  Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
              Pair (N) (R3) =>
                elim R3 return (λ (H3 : Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                    HMInvT Cap Load N slots).
                    Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
                  Pair (Slots) (Inv) =>
                    Pair(Cap, Pair(Load, Pair(N, Pair(
                      arrCat I (S R) (atake I (S R) Slots)
                        (BumpHeadP P V R (adrop I (S R) Slots)),
                      Inv)))) } } } } }

/-- The position of `q` in its hashed bucket, over the pack. -/
def PosHM : Term := prog{
  λ (Q : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots). Nat) {
      Pair (Cap) (R1) =>
        elim R1 return (λ (H1 : Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))). HMInvT Cap load n slots). Nat) {
          Pair (Load) (R2) =>
            elim R2 return (λ (H2 : Σ (n : Nat).
                Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                  HMInvT Cap Load n slots). Nat) {
              Pair (N) (R3) =>
                elim R3 return (λ (H3 : Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                    HMInvT Cap Load N slots). Nat) {
                  Pair (Slots) (Inv) => FindPosL Q (AgetB Cap Slots (Mod Q Cap)) } } } } }

example : chkL prog{ Refl } prog{ Id Nat (PosHM 3 hmEx) Z } = true := by native_decide

/-- The crossing fact at the carve, index moved to the hash by the equation:
    `AgetB` of the composition at `Mod q cap` IS the carved bucket. -/
def AgetAtMod : Term := prog{
  λ (I : Nat). λ (R : Nat). λ (M : Nat).
  λ (L : Array I (List (Σ (k : Nat). Nat))). λ (B : List (Σ (k : Nat). Nat)).
  λ (H : Array R (List (Σ (k : Nat). Nat))).
  λ (Him : Id Nat I M).
    NatRw (λ (W : Nat). Id (List (Σ (k : Nat). Nat))
        (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) W) B)
      I M Him
      (AgetBCatMid R B H I L) }
def AgetAtModTy : Term := prog{
  Π (I : Nat) → Π (R : Nat) → Π (M : Nat) →
  Π (L : Array I (List (Σ (k : Nat). Nat))) → Π (B : List (Σ (k : Nat). Nat)) →
  Π (H : Array R (List (Σ (k : Nat). Nat))) →
    Id Nat I M →
    Id (List (Σ (k : Nat). Nat))
      (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M) B }
example : chkL AgetAtMod AgetAtModTy = true := by native_decide

/-! ### The value-level lookup — the Refl-matchable conjunct

    13-'s return conjunct `Id (Opt Nat) (Some (*r)) (FindHM key (old *self))`
    wraps the payload in a RIGID constructor, and a `Refl`-match cannot refine
    a σ under a rigid head ("both endpoints are rigid — no solution by
    refinement"). The LIST law knew this: `NthPinEv`'s conjunct is the BARE
    payload (`Id Nat (*r) (NthL i (old *v))`). So the op returns BOTH: the
    Nat-level primary (`FindValHM`, the caller's `Refl`-match handle) and the
    doc's Opt-shaped conjunct beside it. -/

def FindVL : Term := prog{
  λ (Q : Nat). λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Nat) {
      Nil => Z,
      Cons (E) (T) Rec =>
        elim E return (λ (Em : Σ (k : Nat). Nat). Nat) {
          Pair (K2) (V2) =>
            elim (Eqb Q K2) return (λ (Bm : Bool). Nat) {
              True => V2,
              False => Rec } } } }

def FindValHM : Term := prog{
  λ (Q : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots). Nat) {
      Pair (Cap) (R1) =>
        elim R1 return (λ (H1 : Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))). HMInvT Cap load n slots). Nat) {
          Pair (Load) (R2) =>
            elim R2 return (λ (H2 : Σ (n : Nat).
                Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                  HMInvT Cap Load n slots). Nat) {
              Pair (N) (R3) =>
                elim R3 return (λ (H3 : Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                    HMInvT Cap Load N slots). Nat) {
                  Pair (Slots) (Inv) => FindVL Q (AgetB Cap Slots (Mod Q Cap)) } } } } }

example : chkL prog{ Refl } prog{ Id Nat (FindValHM 3 hmEx) 30 } = true := by native_decide

/-- The hit leg's Nat-level conjunct. -/
def FindVEvHit : Term := prog{
  λ (Q : Nat). λ (K0 : Nat). λ (V0 : Nat). λ (T : List (Σ (k : Nat). Nat)).
  λ (E : Id Bool (Eqb Q K0) True).
    IdSym Nat (FindVL Q Cons(Pair(K0, V0), T)) V0
      (IdCongr Bool Nat
        (λ (W : Bool). elim W return (λ (Bm : Bool). Nat) {
          True => V0, False => FindVL Q T })
        (Eqb Q K0) True E) }
def FindVEvHitTy : Term := prog{
  Π (Q : Nat) → Π (K0 : Nat) → Π (V0 : Nat) → Π (T : List (Σ (k : Nat). Nat)) →
    Id Bool (Eqb Q K0) True →
    Id Nat V0 (FindVL Q Cons(Pair(K0, V0), T)) }
example : chkL FindVEvHit FindVEvHitTy = true := by native_decide

/-- The miss leg's Nat-level transport. -/
def FindVTailEv : Term := prog{
  λ (Q : Nat). λ (K0 : Nat). λ (V0 : Nat). λ (T : List (Σ (k : Nat). Nat)).
  λ (E : Id Bool (Eqb Q K0) False).
    IdSym Nat (FindVL Q Cons(Pair(K0, V0), T)) (FindVL Q T)
      (IdCongr Bool Nat
        (λ (W : Bool). elim W return (λ (Bm : Bool). Nat) {
          True => V0, False => FindVL Q T })
        (Eqb Q K0) False E) }
def FindVTailEvTy : Term := prog{
  Π (Q : Nat) → Π (K0 : Nat) → Π (V0 : Nat) → Π (T : List (Σ (k : Nat). Nat)) →
    Id Bool (Eqb Q K0) False →
    Id Nat (FindVL Q T) (FindVL Q Cons(Pair(K0, V0), T)) }
example : chkL FindVTailEv FindVTailEvTy = true := by native_decide

/-! ### The op — 13-'s GetMut, in the pin-computable spelling -/

def hmPinUnder (tail : Term) : Term := prog{
  fn BktGetAt [p] (p : Nat, key : Nat,
      b : &mut (t : List (Σ (k : Nat). Nat) ~> BSetP p (*res) t),
      Hhit : Id Bool (HitL key (*b)) True,
      Hpos : Id Nat p (FindPosL key (*b)))
      -> Σ (r : &mut Nat). (Id Nat (*r) (FindVL key (old *b)))
           × (Id OptN (SomeN (*r)) (FindL key (old *b))) {
    match b {
      Nil => botElim Unit (BoolFT Hhit),
      Cons(Pair(kk, vv), tl) => {
        let K0 = *kk;
        let V0 = *vv;
        let T0 = *tl;
        match p {
          Z => {
            let Ehit = PosZHit key K0 V0 T0 Hpos;
            Pair(&m *vv, Pair(FindVEvHit key K0 V0 T0 Ehit,
              FindEvHit key K0 V0 T0 Ehit))
          },
          S(p2) => {
            let Ep = PosSStep key K0 V0 T0 p2 Hpos;
            let Emiss = FstT (Id Bool (Eqb key K0) False) (Id Nat p2 (FindPosL key T0)) Ep;
            let Epos2 = SndT (Id Bool (Eqb key K0) False) (Id Nat p2 (FindPosL key T0)) Ep;
            let Pair(r2, h2) = BktGetAt(p2, key, &m *tl,
              HitTailEv key K0 V0 T0 Emiss Hhit, Epos2);
            let W0 = *r2;
            let Hv2 = FstT (Id Nat W0 (FindVL key T0)) (Id OptN (SomeN W0) (FindL key T0)) h2;
            let Ho2 = SndT (Id Nat W0 (FindVL key T0)) (Id OptN (SomeN W0) (FindL key T0)) h2;
            Pair(r2, Pair(
              IdTrans Nat W0 (FindVL key T0) (FindVL key Cons(Pair(K0, V0), T0)) Hv2
                (FindVTailEv key K0 V0 T0 Emiss),
              IdTrans OptN (SomeN W0) (FindL key T0)
                (FindL key Cons(Pair(K0, V0), T0)) Ho2
                (FindTailEv key K0 V0 T0 Emiss)))
          } } } } };
  fn GetMutHM (i : Nat, rr : Nat, p : Nat, key : Nat,
      self : &mut (s : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
          Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots
        ~> SetHMAt i rr p (*res) s),
      Hd : Id Nat (CapHM (*self)) (Add i (S rr)),
      Him : Id Nat i (Mod key (CapHM (*self))),
      Hhit : Id Bool (HitHM key (*self)) True,
      Hpos : Id Nat p (PosHM key (*self)))
      -> Σ (r : &mut Nat). (Id Nat (*r) (FindValHM key (old *self)))
           × (Id OptN (SomeN (*r)) (FindHM key (old *self))) {
    match self { Pair(capb, r1) => match r1 { Pair(loadb, r2x) => match r2x { Pair(nb, r3) => match r3 { Pair(sb, Invb) => {
      let I0 = i;
      let R0 = rr;
      let Key0 = key;
      let C0 = *capb;
      let pre = &m (*sb)[Z ; i ; S rr | LeAdd i (S rr) | Hd];
      let cell = &m (*sb)[i ; 1 ; rr];
      let hic = &m (*sb)[S i ; rr];
      let bb = &m (*cell)[0];
      let L0 = *pre;
      let B0 = *bb;
      let H0 = *hic;
      let EB = AgetAtMod I0 R0 (Mod Key0 C0) L0 B0 H0 Him;
      let HhitB = IdTrans Bool (HitL Key0 B0)
                    (IsSomeB (FindL Key0 (AgetB (Add I0 (S R0))
                      (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Mod Key0 C0)))) True
                    (IdSym Bool
                      (IsSomeB (FindL Key0 (AgetB (Add I0 (S R0))
                        (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Mod Key0 C0))))
                      (HitL Key0 B0)
                      (IdCongr (List (Σ (k : Nat). Nat)) Bool
                        (λ (W : List (Σ (k : Nat). Nat)). IsSomeB (FindL Key0 W))
                        (AgetB (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0))
                          (Mod Key0 C0)) B0 EB))
                    Hhit;
      let HposB = IdTrans Nat p
                    (FindPosL Key0 (AgetB (Add I0 (S R0))
                      (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Mod Key0 C0)))
                    (FindPosL Key0 B0)
                    Hpos
                    (IdCongr (List (Σ (k : Nat). Nat)) Nat
                      (λ (W : List (Σ (k : Nat). Nat)). FindPosL Key0 W)
                      (AgetB (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0))
                        (Mod Key0 C0)) B0 EB);
      let Pair(rb, hb) = BktGetAt(p, key, &m *bb, HhitB, HposB);
      let W0 = *rb;
      let HvB = FstT (Id Nat W0 (FindVL Key0 B0)) (Id OptN (SomeN W0) (FindL Key0 B0)) hb;
      let HoB = SndT (Id Nat W0 (FindVL Key0 B0)) (Id OptN (SomeN W0) (FindL Key0 B0)) hb;
      Pair(rb, Pair(
        IdTrans Nat W0 (FindVL Key0 B0)
          (FindVL Key0 (AgetB (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0))
            (Mod Key0 C0)))
          HvB
          (IdSym Nat
            (FindVL Key0 (AgetB (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0))
              (Mod Key0 C0)))
            (FindVL Key0 B0)
            (IdCongr (List (Σ (k : Nat). Nat)) Nat
              (λ (W : List (Σ (k : Nat). Nat)). FindVL Key0 W)
              (AgetB (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Mod Key0 C0))
              B0 EB)),
        IdTrans OptN (SomeN W0) (FindL Key0 B0)
          (FindL Key0 (AgetB (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0))
            (Mod Key0 C0)))
          HoB
          (IdSym OptN
            (FindL Key0 (AgetB (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0))
              (Mod Key0 C0)))
            (FindL Key0 B0)
            (IdCongr (List (Σ (k : Nat). Nat)) OptN
              (λ (W : List (Σ (k : Nat). Nat)). FindL Key0 W)
              (AgetB (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Mod Key0 C0))
              B0 EB))))
    } } } } } };
  %tail }

/-- **13-'s GetMut CHECKS**: the map-level pin discharges through the carve
    (`atake`/`adrop` ι at the parameter split), the bucket callee's projected
    pin lands in the composition's cell, and the D9 conjunct is rebuilt from
    the callee's evidence by the `AgetAtMod` transport. -/
def errOf (t : Term) : String :=
  match checkProgram t prog{ Unit } with | .ok _ => "OK" | .error e => e

example : progOk (hmPinUnder prog{ () }) = true := by native_decide

/-! ## (xxx) THE E2E CHAIN — `twoGetMutChain` at hashmap scale

    Get the cursor, write 42 through it, get again at the same key: the second
    call's evidence plus one `Refl`-match and the CHECKER derives `T ≡ 42` and
    the exact final map — the fact the borrow-refounding milestone is named
    for, on the packed container. The premises at a concrete pack are all
    `Refl` (`Mod`/`CoMod`/`PosHM` compute), and — the part worth staring at —
    they are `Refl` again at the SECOND call, whose argument is the first
    call's PINNED RELEASE: `SetHMAt 1 0 0 42 m₀` computes because the pin made
    the release a value, not an existential. That is precisely what the S1 run
    could not have: an unpinned release is a fresh σ, and no premise about its
    capacity or its buckets survives the call. -/

def vN : Nat → Val | 0 => .ctor "Z" [] | n + 1 => .ctor "S" [vN n]
def vP (a b : Val) : Val := .ctor "Pair" [a, b]
def vU : Val := .ctor "unit" []
def vR : Val := .ctor "Refl" []
def vNil : Val := .ctor "Nil" []

/-- The expected final pack: cap 2, load 8, n 1, slot 1 = `[(3, 42)]`, and the
    entry pack's own invariant inhabitant riding through unchanged. -/
def vPackY : Val :=
  vP (vN 2) (vP (vN 8) (vP (vN 1) (vP
    (.ctor "Arr" [vNil, .ctor "Cons" [vP (vN 3) (vN 42), vNil]])
    (vP vU (vP vR (vP vU (vP vR
      (vP (vP vU vU) (vP (vP (vP vR vU) (vP vR vU)) vU)))))))))

def hmChainCaller : Term := hmPinUnder prog defer_check {
  let m = Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(3, 30), Nil)),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
        unit))))))))));
  let b = &m m;
  let pr = GetMutHM(1, 0, 0, 3, b, Refl, Refl, Refl, Refl);
  match pr { Pair(r, h) => {
    *r := 42;
    let b2 = &m m;
    let pr2 = GetMutHM(1, 0, 0, 3, b2, Refl, Refl, Refl, Refl);
    match pr2 { Pair(r2, h2) => {
      let Pair(hv, ho) = h2;
      match hv { Refl => {
        let T = *r2;
        let y = m;
        () } } } } } } }

example : progOk hmChainCaller = true := by native_decide

/-- THE LAW, in the checker's own environment: `T ≡ 42` (derived, not run) and
    `y` is the exact updated pack. -/
example : tailEnv hmChainCaller
  [("m", .bot), ("b", .bot), ("pr", .bot), ("r", .bot),
   ("h", .ctor "Pair" [.sym 0, .sym 1]),
   ("b2", .bot), ("pr2", .bot), ("r2", .bot), ("h2", .bot),
   ("hv", .bot), ("ho", .sym 2),
   ("T", vN 42), ("y", vPackY)] = true := by native_decide

-- …and the lying expectation is refused: the same env with `T ↦ 43`.
example : tailEnv hmChainCaller
  [("m", .bot), ("b", .bot), ("pr", .bot), ("r", .bot),
   ("h", .ctor "Pair" [.sym 0, .sym 1]),
   ("b2", .bot), ("pr2", .bot), ("r2", .bot), ("h2", .bot),
   ("hv", .bot), ("ho", .sym 2),
   ("T", vN 43), ("y", vPackY)] = false := by native_decide

-- The executing machine computes the same final map — the checker/machine
-- divergence the original run pinned for get_mut CLOSES for the pinned op.
def runV (t : Term) (name : String) : Option Val :=
  match runProgram t with
  | .ok env => env.lookup name
  | .error _ => none

example : (runV hmChainCaller "T" == some (vN 42)) = true := by native_decide
example : (runV hmChainCaller "y" == some vPackY) = true := by native_decide

/-! ## (xxxi) The counterfactual twins for the new greens -/

/-- The KEY twin at the bucket walk: identical body, the `Z` leg escapes the
    KEY borrow. The fill puts the exit in the key slot, the pin keeps it in
    the value slot. Pin-only (no D9), so the refusal names the pin. -/
def bktGetAtKey : Term := prog defer_check {
  fn BktGetK [p] (p : Nat, key : Nat,
      b : &mut (t : List (Σ (k : Nat). Nat) ~> BSetP p (*res) t),
      Hhit : Id Bool (HitL key (*b)) True,
      Hpos : Id Nat p (FindPosL key (*b))) -> &mut Nat {
    match b {
      Nil => botElim Unit (BoolFT Hhit),
      Cons(Pair(kk, vv), tl) => {
        let K0 = *kk;
        let V0 = *vv;
        let T0 = *tl;
        match p {
          Z => &m *kk,
          S(p2) => {
            let Ep = PosSStep key K0 V0 T0 p2 Hpos;
            BktGetK(p2, key, &m *tl,
              HitTailEv key K0 V0 T0
                (FstT (Id Bool (Eqb key K0) False) (Id Nat p2 (FindPosL key T0)) Ep)
                Hhit,
              SndT (Id Bool (Eqb key K0) False) (Id Nat p2 (FindPosL key T0)) Ep)
          } } } } };
  () }

example : progRejects bktGetAtKey "pin is not met" = true := by native_decide

/-- The WRONG-POSITION caller: everything as the green chain, but the first
    call claims position 1 where the key sits at 0 — the `Hpos` `Refl` has no
    type to check at, and the caller is refused before any op runs. -/
def hmChainWrongPos : Term := hmPinUnder prog defer_check {
  let m = Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(3, 30), Nil)),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
        unit))))))))));
  let b = &m m;
  let pr = GetMutHM(1, 0, 1, 3, b, Refl, Refl, Refl, Refl);
  match pr { Pair(r, h) => {
    *r := 42;
    () } } }

example : progOk hmChainWrongPos = false := by native_decide

/-- The WRONG-SLOT caller: slot 0 claimed for key 3 at cap 2 — `Him`'s `Refl`
    is refused. -/
def hmChainWrongSlot : Term := hmPinUnder prog defer_check {
  let m = Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(3, 30), Nil)),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
        unit))))))))));
  let b = &m m;
  let pr = GetMutHM(0, 1, 0, 3, b, Refl, Refl, Refl, Refl);
  match pr { Pair(r, h) => {
    *r := 42;
    () } } }

example : progOk hmChainWrongSlot = false := by native_decide

/-! ## (xxxii) `GetMutOrInsert` — the or_insert vocabulary

    Position-driven like GetMut, with two extra moving parts. (1) `FindPosL`
    of an ABSENT key is the bucket length — exactly the append site — so ONE
    update (`BPutP`: set at `p`, or append `(key, v)` past the end) covers hit
    and fresh alike, and the walk needs no hit/miss branching. (2) The count
    moves: the pin cannot compute `hit ? n : S n` (the hit is not
    pin-computable data at the outer level), so the NEW COUNT `n2` is a
    parameter, the BODY writes it into the pack (`*nb := n2`), and honesty is
    a premise (`Hn2` ties `n2` to the hit; `Hroom` keeps the ledger). -/

def BPutP : Term := prog{
  λ (P : Nat). λ (Key : Nat). λ (V : Nat).
    elim P return (λ (Pz : Nat). Π (L : List (Σ (k : Nat). Nat)) → List (Σ (k : Nat). Nat)) {
      Z => λ (L : List (Σ (k : Nat). Nat)).
        elim L return (λ (Lm : List (Σ (k : Nat). Nat)). List (Σ (k : Nat). Nat)) {
          Nil => Cons(Pair(Key, V), Nil),
          Cons (E) (T) Rec =>
            Cons(elim E return (λ (Em : Σ (k : Nat). Nat). Σ (k : Nat). Nat) {
              Pair (K2) (V2) => Pair(K2, V) }, T) },
      S (P2) Rec => λ (L : List (Σ (k : Nat). Nat)).
        elim L return (λ (Lm : List (Σ (k : Nat). Nat)). List (Σ (k : Nat). Nat)) {
          Nil => Cons(Pair(Key, V), Nil),
          Cons (E) (T) Rec2 => Cons(E, Rec T) } } }

example : chkL prog{ Refl } prog{ Id (List (Σ (k : Nat). Nat))
  (BPutP 1 5 77 Cons(Pair(1, 10), Nil))
  Cons(Pair(1, 10), Cons(Pair(5, 77), Nil)) } = true := by native_decide
example : chkL prog{ Refl } prog{ Id (List (Σ (k : Nat). Nat))
  (BPutP 0 5 77 Cons(Pair(1, 10), Nil))
  Cons(Pair(1, 77), Nil) } = true := by native_decide

/-- What the returned borrow holds at entry: the old value if the key was
    there, the default if not. -/
def OrDefL : Term := prog{
  λ (Q : Nat). λ (D : Nat). λ (L : List (Σ (k : Nat). Nat)).
    elim (HitL Q L) return (λ (Bm : Bool). Nat) {
      True => FindVL Q L,
      False => D } }

def OrDefHM : Term := prog{
  λ (Q : Nat). λ (D : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim (HitHM Q Hm) return (λ (Bm : Bool). Nat) {
      True => FindValHM Q Hm,
      False => D } }

example : chkL prog{ Refl } prog{ Id Nat (OrDefHM 3 77 hmEx) 30 } = true := by native_decide
example : chkL prog{ Refl } prog{ Id Nat (OrDefHM 5 77 hmEx) 77 } = true := by native_decide

/-- A hit at the head makes the whole bucket's `OrDefL` its head value. -/
def OrDHitEv : Term := prog{
  λ (Q : Nat). λ (D : Nat). λ (K0 : Nat). λ (V0 : Nat). λ (T : List (Σ (k : Nat). Nat)).
  λ (E : Id Bool (Eqb Q K0) True).
    IdSym Nat (OrDefL Q D Cons(Pair(K0, V0), T)) V0
      (IdTrans Nat (OrDefL Q D Cons(Pair(K0, V0), T))
        (FindVL Q Cons(Pair(K0, V0), T)) V0
        (IdCongr Bool Nat
          (λ (W : Bool). elim (IsSomeB (elim W return (λ (B2 : Bool). Σ (bb : Bool). OptP bb Nat) {
              True => SomeN V0, False => FindL Q T }))
            return (λ (B3 : Bool). Nat) {
              True => FindVL Q Cons(Pair(K0, V0), T), False => D })
          (Eqb Q K0) True E)
        (IdSym Nat V0 (FindVL Q Cons(Pair(K0, V0), T)) (FindVEvHit Q K0 V0 T E))) }
def OrDHitEvTy : Term := prog{
  Π (Q : Nat) → Π (D : Nat) → Π (K0 : Nat) → Π (V0 : Nat) →
  Π (T : List (Σ (k : Nat). Nat)) →
    Id Bool (Eqb Q K0) True →
    Id Nat V0 (OrDefL Q D Cons(Pair(K0, V0), T)) }
example : chkL OrDHitEv OrDHitEvTy = true := by native_decide

/-- A miss at the head passes `OrDefL` through to the tail. -/
def OrDMissEv : Term := prog{
  λ (Q : Nat). λ (D : Nat). λ (K0 : Nat). λ (V0 : Nat). λ (T : List (Σ (k : Nat). Nat)).
  λ (E : Id Bool (Eqb Q K0) False).
    IdSym Nat (OrDefL Q D Cons(Pair(K0, V0), T)) (OrDefL Q D T)
      (IdTrans Nat (OrDefL Q D Cons(Pair(K0, V0), T))
        (elim (HitL Q T) return (λ (B3 : Bool). Nat) {
          True => FindVL Q Cons(Pair(K0, V0), T), False => D })
        (OrDefL Q D T)
        (IdCongr Bool Nat
          (λ (W : Bool). elim (IsSomeB (elim W return (λ (B2 : Bool). Σ (bb : Bool). OptP bb Nat) {
              True => SomeN V0, False => FindL Q T }))
            return (λ (B3 : Bool). Nat) {
              True => FindVL Q Cons(Pair(K0, V0), T), False => D })
          (Eqb Q K0) False E)
        (IdCongr Nat Nat
          (λ (W : Nat). elim (HitL Q T) return (λ (B3 : Bool). Nat) {
            True => W, False => D })
          (FindVL Q Cons(Pair(K0, V0), T)) (FindVL Q T)
          (IdSym Nat (FindVL Q T) (FindVL Q Cons(Pair(K0, V0), T))
            (FindVTailEv Q K0 V0 T E)))) }
def OrDMissEvTy : Term := prog{
  Π (Q : Nat) → Π (D : Nat) → Π (K0 : Nat) → Π (V0 : Nat) →
  Π (T : List (Σ (k : Nat). Nat)) →
    Id Bool (Eqb Q K0) False →
    Id Nat (OrDefL Q D T) (OrDefL Q D Cons(Pair(K0, V0), T)) }
example : chkL OrDMissEv OrDMissEvTy = true := by native_decide

def BumpPutP : Term := prog{
  λ (P : Nat). λ (Key : Nat). λ (V : Nat). λ (R : Nat).
  λ (A : Array (S R) (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))).
        Array Mz (List (Σ (k : Nat). Nat)))
      Arr()
      (λ (M : Nat). λ (X : List (Σ (k : Nat). Nat)).
        λ (XS : Array M (List (Σ (k : Nat). Nat))).
        λ (Ih : Array M (List (Σ (k : Nat). Nat))).
          acons M (BPutP P Key V X) XS)
      (S R) A }

/-- The or_insert release: slot `i`'s bucket put-or-appended at `(p, key)`,
    and the count REPLACED by the parameter `n2` — the body stores it, the
    signature's `Hn2` premise keeps it honest. -/
def SetOrInsAt : Term := prog{
  λ (I : Nat). λ (R : Nat). λ (P : Nat). λ (N2 : Nat). λ (Key : Nat). λ (V : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
        Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
          Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
      Pair (Cap) (R1) =>
        elim R1 return (λ (H1 : Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))). HMInvT Cap load n slots).
            Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
              Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
          Pair (Load) (R2) =>
            elim R2 return (λ (H2 : Σ (n : Nat).
                Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                  HMInvT Cap Load n slots).
                Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                  Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
              Pair (N) (R3) =>
                elim R3 return (λ (H3 : Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                    HMInvT Cap Load N slots).
                    Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
                  Pair (Slots) (Inv) =>
                    Pair(Cap, Pair(Load, Pair(N2, Pair(
                      arrCat I (S R) (atake I (S R) Slots)
                        (BumpPutP P Key V R (adrop I (S R) Slots)),
                      Inv)))) } } } } }

/-- The map-to-bucket `OrDefL` glue at the carve — packaged so the op's body
    applies one lemma instead of inlining the two-place congruence. -/
def OrDAgetEv : Term := prog{
  λ (Q : Nat). λ (D : Nat). λ (I : Nat). λ (R : Nat). λ (M : Nat).
  λ (L : Array I (List (Σ (k : Nat). Nat))). λ (B : List (Σ (k : Nat). Nat)).
  λ (H : Array R (List (Σ (k : Nat). Nat))).
  λ (Him : Id Nat I M).
    IdSym Nat
      (elim (IsSomeB (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M)))
        return (λ (B3 : Bool). Nat) {
          True => FindVL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M),
          False => D })
      (OrDefL Q D B)
      (IdTrans Nat
        (elim (IsSomeB (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M)))
          return (λ (B3 : Bool). Nat) {
            True => FindVL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M),
            False => D })
        (elim (IsSomeB (FindL Q B)) return (λ (B3 : Bool). Nat) {
          True => FindVL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M),
          False => D })
        (OrDefL Q D B)
        (IdCongr (List (Σ (k : Nat). Nat)) Nat
          (λ (W : List (Σ (k : Nat). Nat)).
            elim (IsSomeB (FindL Q W)) return (λ (B3 : Bool). Nat) {
              True => FindVL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M),
              False => D })
          (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M) B
          (AgetAtMod I R M L B H Him))
        (IdCongr Nat Nat
          (λ (W : Nat). elim (IsSomeB (FindL Q B)) return (λ (B3 : Bool). Nat) {
            True => W, False => D })
          (FindVL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M))
          (FindVL Q B)
          (IdCongr (List (Σ (k : Nat). Nat)) Nat
            (λ (W : List (Σ (k : Nat). Nat)). FindVL Q W)
            (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M) B
            (AgetAtMod I R M L B H Him)))) }
def OrDAgetEvTy : Term := prog{
  Π (Q : Nat) → Π (D : Nat) → Π (I : Nat) → Π (R : Nat) → Π (M : Nat) →
  Π (L : Array I (List (Σ (k : Nat). Nat))) → Π (B : List (Σ (k : Nat). Nat)) →
  Π (H : Array R (List (Σ (k : Nat). Nat))) →
    Id Nat I M →
    Id Nat (OrDefL Q D B)
      (elim (IsSomeB (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M)))
        return (λ (B3 : Bool). Nat) {
          True => FindVL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M),
          False => D }) }
example : chkL OrDAgetEv OrDAgetEvTy = true := by native_decide

/-! ### The or_insert ops -/

def hmOrUnder (tail : Term) : Term := prog{
  fn BktPutAt [p] (p : Nat, key : Nat, d : Nat,
      b : &mut (t : List (Σ (k : Nat). Nat) ~> BPutP p key (*res) t),
      Hpos : Id Nat p (FindPosL key (*b)))
      -> Σ (r : &mut Nat). Id Nat (*r) (OrDefL key d (old *b)) {
    match b {
      Nil => match p {
        Z => {
          *b := Cons(Pair(key, d), Nil);
          match b { Cons(hd, tl) => match hd { Pair(kk, vv) =>
            Pair(&m *vv, Refl) } }
        },
        S(p2) => botElim Unit (Znots p2 (IdSym Nat (S p2) Z Hpos))
      },
      Cons(Pair(kk, vv), tl) => {
        let K0 = *kk;
        let V0 = *vv;
        let T0 = *tl;
        match p {
          Z => Pair(&m *vv, OrDHitEv key d K0 V0 T0 (PosZHit key K0 V0 T0 Hpos)),
          S(p2) => {
            let Ep = PosSStep key K0 V0 T0 p2 Hpos;
            let Emiss = FstT (Id Bool (Eqb key K0) False) (Id Nat p2 (FindPosL key T0)) Ep;
            let Epos2 = SndT (Id Bool (Eqb key K0) False) (Id Nat p2 (FindPosL key T0)) Ep;
            let Pair(r2, h2) = BktPutAt(p2, key, d, &m *tl, Epos2);
            let W0 = *r2;
            Pair(r2, IdTrans Nat W0 (OrDefL key d T0)
              (OrDefL key d Cons(Pair(K0, V0), T0)) h2
              (OrDMissEv key d K0 V0 T0 Emiss))
          } } } } };
  fn GetMutOrInsertHM (i : Nat, rr : Nat, p : Nat, n2 : Nat, key : Nat, d : Nat,
      self : &mut (s : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
          Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots
        ~> SetOrInsAt i rr p n2 key (*res) s),
      Hd : Id Nat (CapHM (*self)) (Add i (S rr)),
      Him : Id Nat i (Mod key (CapHM (*self))),
      Hpos : Id Nat p (PosHM key (*self)),
      Hn2 : Id Nat n2 (elim (HitHM key (*self)) return (λ (Bm : Bool). Nat) {
        True => SizeHM (*self), False => S (SizeHM (*self)) }),
      Hroom : Le (Mul 5 n2) (LoadHM (*self)))
      -> Σ (r : &mut Nat). Id Nat (*r) (OrDefHM key d (old *self)) {
    match self { Pair(capb, r1) => match r1 { Pair(loadb, r2x) => match r2x { Pair(nb, r3) => match r3 { Pair(sb, Invb) => {
      let I0 = i;
      let R0 = rr;
      let Key0 = key;
      let D0 = d;
      let C0 = *capb;
      let pre = &m (*sb)[Z ; i ; S rr | LeAdd i (S rr) | Hd];
      let cell = &m (*sb)[i ; 1 ; rr];
      let hic = &m (*sb)[S i ; rr];
      let bb = &m (*cell)[0];
      let L0 = *pre;
      let B0 = *bb;
      let H0 = *hic;
      let HposB = IdTrans Nat p
                    (FindPosL Key0 (AgetB (Add I0 (S R0))
                      (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Mod Key0 C0)))
                    (FindPosL Key0 B0)
                    Hpos
                    (IdCongr (List (Σ (k : Nat). Nat)) Nat
                      (λ (W : List (Σ (k : Nat). Nat)). FindPosL Key0 W)
                      (AgetB (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0))
                        (Mod Key0 C0)) B0
                      (AgetAtMod I0 R0 (Mod Key0 C0) L0 B0 H0 Him));
      *nb := n2;
      let Pair(rb, hb) = BktPutAt(p, key, d, &m *bb, HposB);
      let W0 = *rb;
      Pair(rb, IdTrans Nat W0 (OrDefL Key0 D0 B0)
        (elim (IsSomeB (FindL Key0 (AgetB (Add I0 (S R0))
            (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Mod Key0 C0))))
          return (λ (B3 : Bool). Nat) {
            True => FindVL Key0 (AgetB (Add I0 (S R0))
              (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Mod Key0 C0)),
            False => D0 })
        hb
        (OrDAgetEv Key0 D0 I0 R0 (Mod Key0 C0) L0 B0 H0 Him))
    } } } } } };
  %tail }

example : progOk (hmOrUnder prog{ () }) = true := by native_decide

/-! ### The or_insert round-trip — and the append path's honest seam

    Fresh key 5 into slot 1 (colliding with key 1) at cap 4 (cap 2's ledger
    has no room for a second entry — `Hroom` is a real premise), write 88
    through the returned cursor, then GET the key back and `Refl`-match: the
    checker derives `T ≡ 88` and the exact final map, count bumped once.

    THE SEAM, pinned honestly below (`orInsReuse`): the APPEND grows the
    bucket, so the packed invariant's INHABITANT gains conjuncts — the entry
    proof tree no longer typechecks at the released slots, and a second op on
    the raw release is refused at the call's `hasType` ("does not have its
    parameter type"). Value writes (GetMut) have no such seam — the proof tree
    is shape-invariant under them. So the caller RE-ESTABLISHES the invariant
    at the repack (at concrete data the new proofs are literal `Refl`/`unit`),
    and the named follow-up is the invariant TRANSFORMER — `SetOrInsAt`
    carrying a proof-rebuilding component (S2's `MkInv`/`SFCatGlue` machinery
    as a spec function) instead of `Inv`-passthrough. -/

def vPackOr : Val :=
  vP (vN 4) (vP (vN 16) (vP (vN 2) (vP
    (.ctor "Arr" [vNil,
      .ctor "Cons" [vP (vN 1) (vN 10), .ctor "Cons" [vP (vN 5) (vN 88), vNil]],
      vNil, vNil])
    (vP vU (vP vR (vP vU (vP vR
      (vP (vP vU vU)
        (vP (vP (vP vR (vP vR vU)) (vP vR (vP vR vU)))
          (vP (vP vU vU) (vP (vP vU vU) vU)))))))))))

/-- The stale entry invariant, still visible as knowledge after the repack. -/
def vInvStale : Val :=
  vP vU (vP vR (vP vU (vP vR
    (vP (vP vU vU) (vP (vP (vP vR vU) (vP vR vU))
      (vP (vP vU vU) (vP (vP vU vU) vU)))))))

def orInsChain : Term := hmPinUnder (hmOrUnder prog defer_check {
  let m = Pair(4, Pair(16, Pair(1, Pair(Arr(Nil, Cons(Pair(1, 10), Nil), Nil, Nil),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
        Pair(Pair(unit, unit), Pair(Pair(unit, unit), unit))))))))))));
  let b = &m m;
  let pr = GetMutOrInsertHM(1, 2, 1, 2, 5, 77, b, Refl, Refl, Refl, Refl, unit);
  match pr { Pair(r, h) => {
    match h { Refl => {
      *r := 88;
      let Pair(cc, rest1) = m;
      let Pair(ll, rest2) = rest1;
      let Pair(nn, rest3) = rest2;
      let Pair(ss, IV) = rest3;
      let m2 = Pair(cc, Pair(ll, Pair(nn, Pair(ss,
        Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
          Pair(Pair(unit, unit),
            Pair(Pair(Pair(Refl, Pair(Refl, unit)), Pair(Refl, Pair(Refl, unit))),
              Pair(Pair(unit, unit), Pair(Pair(unit, unit), unit))))))))))));
      let b2 = &m m2;
      let pr2 = GetMutHM(1, 2, 1, 5, b2, Refl, Refl, Refl, Refl);
      match pr2 { Pair(r2, h2) => {
        let Pair(hv, ho) = h2;
        match hv { Refl => {
          let T = *r2;
          let y = m2;
          () } } } } } } } } })

example : progOk orInsChain = true := by native_decide

/-- The or_insert law in the checker's environment: `T ≡ 88`, `y` the exact
    two-entry map — and the stale entry invariant (`IV`) sitting in plain view
    as the seam the repack crossed. -/
example : tailEnv orInsChain
  [("m", .bot), ("b", .bot), ("pr", .bot), ("r", .bot), ("h", .bot),
   ("cc", vN 4), ("rest1", .bot), ("ll", vN 16), ("rest2", .bot),
   ("nn", vN 2), ("rest3", .bot), ("ss", .bot), ("IV", vInvStale),
   ("m2", .bot), ("b2", .bot), ("pr2", .bot), ("r2", .bot), ("h2", .bot),
   ("hv", .bot), ("ho", .sym 0),
   ("T", vN 88), ("y", vPackOr)] = true := by native_decide

example : (runV orInsChain "T" == some (vN 88)) = true := by native_decide
example : (runV orInsChain "y" == some vPackOr) = true := by native_decide

/-- THE PINNED SEAM: the same chain re-calling on the RAW release (no repack).
    The append made the entry invariant inhabitant stale, and the second call
    refuses the payload. -/
def orInsReuse : Term := hmOrUnder prog defer_check {
  let m = Pair(4, Pair(16, Pair(1, Pair(Arr(Nil, Cons(Pair(1, 10), Nil), Nil, Nil),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
        Pair(Pair(unit, unit), Pair(Pair(unit, unit), unit))))))))))));
  let b = &m m;
  let pr = GetMutOrInsertHM(1, 2, 1, 2, 5, 77, b, Refl, Refl, Refl, Refl, unit);
  match pr { Pair(r, h) => {
    *r := 88;
    let b2 = &m m;
    let pr2 = GetMutOrInsertHM(1, 2, 1, 2, 5, 77, b2, Refl, Refl, Refl, Refl, unit);
    match pr2 { Pair(r2, h2) => {
      () } } } } }

example : progRejects orInsReuse "does not have its parameter type" = true := by
  native_decide

/-! ## (xxxiii) THE BRIDGE — the pin's spelling equals the doc's

    The pin carries `BSetP p (*res)` (position-driven, pin-computable); the
    doc's `SetHM` carries `BSetK key` (key-driven, the caller-facing law).
    Wherever the position evidence holds they are THE SAME UPDATE — proved by
    one induction, so a caller may rewrite its pinned release into the doc's
    vocabulary. (The map-level equality follows pointwise at the carve
    composition through `AgetAtMod`, the same way every crossing fact here
    does; the bucket level is where the content lives.) -/

def BSetPKEq : Term := prog{
  λ (Q : Nat). λ (V : Nat).
  λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)).
        Π (P : Nat) → Id Nat P (FindPosL Q Lm) →
          Id (List (Σ (k : Nat). Nat)) (BSetP P V Lm) (BSetK Q V Lm)) {
      Nil => λ (P : Nat). λ (Hp : Id Nat P (FindPosL Q Nil)).
        NatRw (λ (W : Nat). Id (List (Σ (k : Nat). Nat)) (BSetP W V Nil) Nil)
          Z P (IdSym Nat P Z Hp) Refl,
      Cons (E) (T) Rec =>
        elim E return (λ (Em : Σ (k : Nat). Nat).
            Π (P : Nat) → Id Nat P (FindPosL Q Cons(Em, T)) →
              Id (List (Σ (k : Nat). Nat)) (BSetP P V Cons(Em, T)) (BSetK Q V Cons(Em, T))) {
          Pair (K2) (V2) => λ (P : Nat). λ (Hp : Id Nat P (FindPosL Q Cons(Pair(K2, V2), T))).
            IfDec (Eqb Q K2)
              (Id (List (Σ (k : Nat). Nat))
                (BSetP P V Cons(Pair(K2, V2), T)) (BSetK Q V Cons(Pair(K2, V2), T)))
              (λ (Et : Id Bool (Eqb Q K2) True).
                IdTrans (List (Σ (k : Nat). Nat))
                  (BSetP P V Cons(Pair(K2, V2), T))
                  Cons(Pair(K2, V), T)
                  (BSetK Q V Cons(Pair(K2, V2), T))
                  (NatRw (λ (W : Nat). Id (List (Σ (k : Nat). Nat))
                      (BSetP W V Cons(Pair(K2, V2), T)) Cons(Pair(K2, V), T))
                    Z P
                    (IdSym Nat P Z
                      (IdTrans Nat P (FindPosL Q Cons(Pair(K2, V2), T)) Z Hp
                        (IdCongr Bool Nat
                          (λ (W : Bool). elim W return (λ (Bm : Bool). Nat) {
                            True => Z, False => S (FindPosL Q T) })
                          (Eqb Q K2) True Et)))
                    Refl)
                  (IdSym (List (Σ (k : Nat). Nat))
                    (BSetK Q V Cons(Pair(K2, V2), T)) Cons(Pair(K2, V), T)
                    (IdCongr Bool (List (Σ (k : Nat). Nat))
                      (λ (W : Bool). elim W return (λ (Bm : Bool). List (Σ (k : Nat). Nat)) {
                        True => Cons(Pair(K2, V), T),
                        False => Cons(Pair(K2, V2), BSetK Q V T) })
                      (Eqb Q K2) True Et)))
              (λ (Ef : Id Bool (Eqb Q K2) False).
                IdTrans (List (Σ (k : Nat). Nat))
                  (BSetP P V Cons(Pair(K2, V2), T))
                  Cons(Pair(K2, V2), BSetK Q V T)
                  (BSetK Q V Cons(Pair(K2, V2), T))
                  (IdTrans (List (Σ (k : Nat). Nat))
                    (BSetP P V Cons(Pair(K2, V2), T))
                    Cons(Pair(K2, V2), BSetP (FindPosL Q T) V T)
                    Cons(Pair(K2, V2), BSetK Q V T)
                    (NatRw (λ (W : Nat). Id (List (Σ (k : Nat). Nat))
                        (BSetP W V Cons(Pair(K2, V2), T))
                        Cons(Pair(K2, V2), BSetP (FindPosL Q T) V T))
                      (S (FindPosL Q T)) P
                      (IdSym Nat P (S (FindPosL Q T))
                        (IdTrans Nat P (FindPosL Q Cons(Pair(K2, V2), T))
                          (S (FindPosL Q T)) Hp
                          (IdCongr Bool Nat
                            (λ (W : Bool). elim W return (λ (Bm : Bool). Nat) {
                              True => Z, False => S (FindPosL Q T) })
                            (Eqb Q K2) False Ef)))
                      Refl)
                    (IdCongr (List (Σ (k : Nat). Nat)) (List (Σ (k : Nat). Nat))
                      (λ (W : List (Σ (k : Nat). Nat)). Cons(Pair(K2, V2), W))
                      (BSetP (FindPosL Q T) V T) (BSetK Q V T)
                      (Rec (FindPosL Q T) Refl)))
                  (IdSym (List (Σ (k : Nat). Nat))
                    (BSetK Q V Cons(Pair(K2, V2), T))
                    Cons(Pair(K2, V2), BSetK Q V T)
                    (IdCongr Bool (List (Σ (k : Nat). Nat))
                      (λ (W : Bool). elim W return (λ (Bm : Bool). List (Σ (k : Nat). Nat)) {
                        True => Cons(Pair(K2, V), T),
                        False => Cons(Pair(K2, V2), BSetK Q V T) })
                      (Eqb Q K2) False Ef))) } } }
def BSetPKEqTy : Term := prog{
  Π (Q : Nat) → Π (V : Nat) → Π (L : List (Σ (k : Nat). Nat)) → Π (P : Nat) →
    Id Nat P (FindPosL Q L) →
    Id (List (Σ (k : Nat). Nat)) (BSetP P V L) (BSetK Q V L) }
example : chkL BSetPKEq BSetPKEqTy = true := by native_decide

end Dllbc.Tests.HashMap

end
