import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas

/-!
# The hashmap with the proofs taken out

`Tests/HashMap.lean` writes a resizable hashmap whose invariant is packed into
the container's type and whose every operation carries its full specification.
This file writes THE SAME RUNTIME PROGRAM with all of that removed: no packed
invariant, no proof parameters, no evidence returns, no spec functions. Same
data layout, same control flow, same allocation shape, same answers.

It exists to measure the proof overhead, and to say by a concrete differential
rather than by assertion that the two programs compute the same thing: the
callers at the bottom are `HashMap.lean`'s executing differential ported over
verbatim, asserting the same expected values.

The measurement, and what is left after the erasure, are in the two sections
below.
-/

section
open Dllbc
open Dllbc.StdLemmas (Mod ModLtN ModDec LeAdd LebTrueLe Mul)

namespace Dllbc.Tests.HashMapErased

/-! ## The runtime vocabulary

    Everything here is data or a Bool test that the program branches on — it
    survives the erasure because the RUNTIME reads it, not because a proof
    does. There is deliberately no import of `Tests/HashMap.lean`: the erased
    program needs none of that file's ~3000 lines of pure lemmas, and an
    import would hide that. -/

/-- The option payload, and the Σ(Bool) option type standing in for a native
    `Option` the kernel does not have. -/
def OptP : Term := prog defer_check {
  λ (B : Bool). λ (T : Type). elim B return (λ (Bm : Bool). Type) {
    True => T,
    False => Unit } }

def Opt : Term := prog defer_check { λ (T : Type). Σ (b : Bool). OptP b T }
def OptN : Term := prog defer_check { Σ (bb : Bool). OptP bb Nat }
def SomeN : Term := prog defer_check { λ (V : Nat). Pair(True, V) }
def NoneN : Term := prog defer_check { Pair(False, unit) }

/-- Bucket emptiness as a Bool, so the drain loop can test `src` without
    matching it — matching a borrow reborrows its payload and the rotation
    below could then not move the node. -/
def IsNilB : Term := prog defer_check {
  λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Bool) {
      Nil => True,
      Cons (E) (T) Rec => False } }

/-- `n` empty buckets — the only allocation a resize performs. -/
def MkSlots : Term := prog defer_check {
  λ (N : Nat). elim N return (λ (Nm : Nat). Array Nm (List (Σ (k : Nat). Nat))) {
    Z => Arr(),
    S (M) Rec => acons M Nil Rec } }

/-- **The one piece of proof that does not erase.** DLLBC has no unchecked
    indexing: a carve of `Array n T` at a symbolic index has to hand premise
    (3) a decomposition `n = i + (1 + r)`, and at a symbolic `n` no such
    decomposition computes. This mints one from `i < n`: the residue `r`, the
    equation, and the identity tying `i` to the hash.

    Verbatim from `HashMap.lean`'s `SlotPack`, which is where it is explained.
    See the erasure notes below for why it is irreducible. -/
def SlotPackE : Term := prog defer_check {
  λ (H : Nat). λ (N : Nat). λ (Hne : Le (S Z) N).
    elim (ModDec (Mod H N) N (ModLtN H N Hne)) return
        (λ (Q : Σ (R : Nat). Id Nat N (Add (Mod H N) (S R))).
          Σ (i : Nat). Σ (r : Nat). Σ (hd : Id Nat N (Add i (S r))). Id Nat i (Mod H N)) {
      Pair (R0) (Hd0) => Pair(Mod H N, Pair(R0, Pair(Hd0, Refl))) } }

/-! ## The erased program

    One `fn` per verified `fn`, same name, same order, same body shape. What
    changed, systematically:

    * the container is `Σ cap. Σ load. Σ n. Array cap Bucket` — no `Σ0`
      invariant component;
    * every proof parameter and every evidence return is gone, so each fn
      returns the runtime value it actually computes (`Bool`, the `Opt`, or
      `Unit`);
    * a `Z => botElim Unit Hf` fuel arm becomes a harmless default, since
      nothing proves the fuel sufficient any more;
    * `cap ≥ 1` came from the packed invariant (`InvLe1`); here every fn that
      carves tests it itself with `Leb 1 cap` and turns the test into the
      `Le` that `SlotOfE` wants. The test is a `Leb`, deliberately, and NOT a
      `match cap`: matching refines the extent to `S c`, and a compound extent
      is rigid, which is exactly what the carve cannot have (¶8.4). -/

def hmErasedUnder (tail : Term) : Term := prog{
  fn InsertInList [fuel] (fuel : Nat, key : Nat, val : Nat,
                          b : &mut (List (Σ (k : Nat). Nat)))
      -> Bool
      { match b {
          Nil => { *b := Cons(Pair(key, val), Nil); False },
          Cons(Pair(kk, vv), tl) => match fuel {
            Z => False,
            S(f2) =>
              if Eqb *kk key { *vv := val; True }
              else { InsertInList(f2, key, val, &m *tl) }
          } } };
  fn RemoveL [fuel] (fuel : Nat, key : Nat, l : List (Σ (k : Nat). Nat))
      -> Σ (ret : OptN). List (Σ (k : Nat). Nat)
      { match l {
          Nil => Pair(NoneN, Nil),
          Cons(Pair(kk, vv), tl2) => match fuel {
            Z => Pair(NoneN, Cons(Pair(kk, vv), tl2)),
            S(f2) =>
              if Eqb kk key { Pair(Pair(True, vv), tl2) }
              else {
                let Pair(rr2, l3) = RemoveL(f2, key, tl2);
                Pair(rr2, Cons(Pair(kk, vv), l3))
              }
          } } };
  fn SlotOfE (h : Nat, n : Nat, Hne : Le (S Z) n)
      -> Σ (i : Nat). Σ (r : Nat). Σ (hd : Id Nat n (Add i (S r))). Id Nat i (Mod h n) {
    SlotPackE h n Hne };
  fn NewHM (cap : Nat)
      -> Σ (c : Nat). Σ (load : Nat). Σ (n : Nat). Array c (List (Σ (k : Nat). Nat)) {
    Pair(cap, Pair(Mul 4 cap, Pair(Z, MkSlots cap))) };
  fn SlotUpd (fuel : Nat, cap : Nat, key : Nat, val : Nat,
              b : &mut (Array cap (List (Σ (k : Nat). Nat))))
      -> Bool
      { if e : Leb 1 cap {
          let Pair(i, Pair(r, Pair(hd, him))) = SlotOfE(key, cap, LebTrueLe 1 cap e);
          let pre = &m (*b)[Z ; i ; S r | LeAdd i (S r) | hd];
          let cell = &m (*b)[i ; 1 ; r];
          let hic = &m (*b)[S i ; r];
          let bb = &m (*cell)[0];
          InsertInList(fuel, key, val, &m *bb)
        } else { False } };
  fn SlotRem (fuel : Nat, cap : Nat, key : Nat,
              b : &mut (Array cap (List (Σ (k : Nat). Nat))))
      -> OptN
      { if e : Leb 1 cap {
          let Pair(i, Pair(r, Pair(hd, him))) = SlotOfE(key, cap, LebTrueLe 1 cap e);
          let pre = &m (*b)[Z ; i ; S r | LeAdd i (S r) | hd];
          let cell = &m (*b)[i ; 1 ; r];
          let hic = &m (*b)[S i ; r];
          let bb = &m (*cell)[0];
          let bcur = *bb;
          let Pair(rr2, l3) = RemoveL(fuel, key, bcur);
          *bb := l3;
          rr2
        } else { NoneN } };
  fn SlotPush (cap2 : Nat,
               src : &mut (List (Σ (k : Nat). Nat)),
               dst : &mut (Array cap2 (List (Σ (k : Nat). Nat))))
      -> Unit
      { match src {
          Nil => (),
          Cons(Pair(kk, vv), tail) => {
            let k0 = *kk;
            *kk := k0;
            if e : Leb 1 cap2 {
              let Pair(i, Pair(r, Pair(hd, him))) = SlotOfE(k0, cap2, LebTrueLe 1 cap2 e);
              let pre = &m (*dst)[Z ; i ; S r | LeAdd i (S r) | hd];
              let cell = &m (*dst)[i ; 1 ; r];
              let hic = &m (*dst)[S i ; r];
              let bb = &m (*cell)[0];
              let tmp = *tail;
              *tail := *bb;
              *bb := *src;
              *src := tmp;
              ()
            } else { () }
          } } };
  fn MoveBktR [fuel] (fuel : Nat, cap2 : Nat,
                      src : &mut (List (Σ (k : Nat). Nat)),
                      dst : &mut (Array cap2 (List (Σ (k : Nat). Nat))))
      -> Unit
      { if IsNilB (*src) { () } else {
          match fuel {
            Z => (),
            S(f2) => {
              SlotPush(cap2, &m *src, &m *dst);
              MoveBktR(f2, cap2, &m *src, &m *dst)
            } }
        } };
  fn MoveOne (tfuel : Nat, capF : Nat, cap2 : Nat, j : Nat,
              src : &mut (Array capF (List (Σ (k : Nat). Nat))),
              dst : &mut (Array cap2 (List (Σ (k : Nat). Nat))))
      -> Unit
      { if e : Leb (S j) capF {
          let bbs = &m (*src)[j | LebTrueLe (S j) capF e];
          let bl = *bbs;
          *bbs := Nil;
          MoveBktR(tfuel, cap2, &m bl, &m *dst)
        } else { () } };
  fn MoveSlots [m] (m : Nat, j : Nat, tfuel : Nat, capF : Nat, cap2 : Nat,
                    src : &mut (Array capF (List (Σ (k : Nat). Nat))),
                    dst : &mut (Array cap2 (List (Σ (k : Nat). Nat))))
      -> Unit
      { match m {
          Z => (),
          S(m2) => {
            MoveOne(tfuel, capF, cap2, j, &m *src, &m *dst);
            MoveSlots(m2, S j, tfuel, capF, cap2, &m *src, &m *dst)
          } } };
  fn InsertHM (fuel : Nat, key : Nat, val : Nat,
               self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                 Array cap (List (Σ (k : Nat). Nat))))
      -> Unit
      {
        let Pair(cap, Pair(load, Pair(nn, slots))) = *self;
        let sb = &m slots;
        let hit2 = SlotUpd(fuel, cap, key, val, &m *sb);
        match hit2 {
          True => { *self := Pair(cap, Pair(load, Pair(nn, slots))); () },
          False =>
            if Leb (Mul 5 (S nn)) load {
              *self := Pair(cap, Pair(load, Pair(S(nn), slots)));
              ()
            } else {
              let nslots = MkSlots (Mul 2 cap);
              let db = &m nslots;
              MoveSlots(cap, Z, fuel, cap, Mul 2 cap, &m *sb, &m *db);
              *self := Pair(Mul 2 cap, Pair(Mul 4 (Mul 2 cap), Pair(S(nn), nslots)));
              ()
            }
        } };
  fn RemoveHM (fuel : Nat, key : Nat,
               self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                 Array cap (List (Σ (k : Nat). Nat))))
      -> OptN
      {
        let Pair(cap, Pair(load, Pair(nn, slots))) = *self;
        let sb = &m slots;
        let rr = SlotRem(fuel, cap, key, &m *sb);
        match rr {
          Pair(tg, pv) => match tg {
            True => match nn {
              Z => { *self := Pair(cap, Pair(load, Pair(Z, slots))); Pair(True, pv) },
              S(m2) => { *self := Pair(cap, Pair(load, Pair(m2, slots))); Pair(True, pv) }
            },
            False => { *self := Pair(cap, Pair(load, Pair(nn, slots))); Pair(False, pv) }
          } } };
  %tail }

/-- The erased chain, with nothing after it, type-checks. -/
example : progOk (hmErasedUnder prog defer_check { () }) = true := by native_decide

end Dllbc.Tests.HashMapErased
end
