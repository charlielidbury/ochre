import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.HashMap

/-!
# ProbeRotate — viability probes for the rotation-based single-allocation resize

Scratch module, never imported. Build directly: `lake build Dllbc.Tests.ProbeRotate`.
Probes, in risk order:
  P1  the rotation fn (mem::replace chain through a matched borrow), rebuilt here;
  P2  the SlotPush composite: through-borrow match on src + carve of dst INSIDE the
      arm + parent read (*src) after mutating through the child + old-relative
      Σ0/Id evidence in the return type — all in one body;
  P3  IsNilB (list-elim to Bool), its two Nil lemmas, the `if e :` dispatch, and
      passing the branch equation across a call boundary at `&m *b`;
  P4  `j` at the bucket type (BktRw), NatRw's shape at `List (Σ (k : Nat). Nat)`;
  P5  the concrete inline rotation with values, Refl-snapshot closed.
-/

section
open Dllbc
open Dllbc.StdLemmas (LeRefl LeAdd LeAddL LeAddSucc LeTrans LeUpR LePredL
  AddSucc AddZero IdTrans IdCongr IdSym NatRw BoolFT BoolTF EqbRefl
  LeRwL LeRwR LeAddMonoL Mod ModDec ModLtN EqbTrueEq EqbSym IfDec)
open Dllbc.Tests.HashMap

namespace Dllbc.Tests.ProbeRotate

/-- P1: the checker-verified rotation, symbolic mode. Each read is immediately
    followed by an overwrite of the slot it was read from (mem::replace). -/
def rot1 : Term := prog{
  fn MoveHead (og : &mut (List Nat), nw : &mut (List Nat)) -> Unit {
    match og {
      Nil => (),
      Cons(hd, tail) => {
        let tmp = *tail;
        *tail := *nw;
        *nw := *og;
        *og := tmp;
        ()
      }
    }
  };
  () }
example : progOk rot1 = true := by native_decide

/-- P3a: `IsNilB` — pure emptiness test over a bucket. -/
def IsNilBP : Term := prog defer_check {
  λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Bool) {
      Nil => True,
      Cons (E) (T) Rec => False } }
def IsNilBPTy : Term := prog defer_check { Π (L : List (Σ (k : Nat). Nat)) → Bool }
example : chkL IsNilBP IsNilBPTy = true := by native_decide

/-- P3b: an empty bucket answers nothing (per-key `HitL` is `False`). -/
def NilHitFalseP : Term := prog defer_check {
  λ (Q : Nat). λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)).
        Id Bool (IsNilBP Lm) True → Id Bool (HitL Q Lm) False) {
      Nil => λ (Hn : Id Bool True True). Refl,
      Cons (E) (T) Rec => λ (Hn : Id Bool False True).
        botElim (Id Bool (HitL Q (Cons(E, T))) False) (BoolFT Hn) } }
def NilHitFalsePTy : Term := prog defer_check {
  Π (Q : Nat) → Π (L : List (Σ (k : Nat). Nat)) →
    Id Bool (IsNilBP L) True → Id Bool (HitL Q L) False }
example : chkL NilHitFalseP NilHitFalsePTy = true := by native_decide

/-- P3c: an empty bucket has length zero. -/
def NilLenZP : Term := prog defer_check {
  λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)).
        Id Bool (IsNilBP Lm) True → Id Nat (LenE Lm) Z) {
      Nil => λ (Hn : Id Bool True True). Refl,
      Cons (E) (T) Rec => λ (Hn : Id Bool False True).
        botElim (Id Nat (LenE (Cons(E, T))) Z) (BoolFT Hn) } }
def NilLenZPTy : Term := prog defer_check {
  Π (L : List (Σ (k : Nat). Nat)) →
    Id Bool (IsNilBP L) True → Id Nat (LenE L) Z }
example : chkL NilLenZP NilLenZPTy = true := by native_decide

/-- P3d: a nonempty bucket has positive length (the fuel-Z contradiction). -/
def NotNilLenPosP : Term := prog defer_check {
  λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)).
        Id Bool (IsNilBP Lm) False → Le (S Z) (LenE Lm)) {
      Nil => λ (Hn : Id Bool True False).
        botElim (Le (S Z) (LenE Nil)) (BoolTF Hn),
      Cons (E) (T) Rec => λ (Hn : Id Bool False False). unit } }
def NotNilLenPosPTy : Term := prog defer_check {
  Π (L : List (Σ (k : Nat). Nat)) →
    Id Bool (IsNilBP L) False → Le (S Z) (LenE L) }
example : chkL NotNilLenPosP NotNilLenPosPTy = true := by native_decide

/-- P3e: the `if e :` dispatch on `IsNilBP (*b)`, the branch equation handed
    across a call boundary at `&m *b`, and the Nil-arm refinement turning the
    hypothesis into `Id Bool True False`. -/
def dispatchNil : Term := prog{
  fn TakeHd (src : &mut (List (Σ (k : Nat). Nat)),
           Hne : Id Bool (IsNilBP (*src)) False) -> Unit {
    match src {
      Nil => botElim Unit (BoolTF Hne),
      Cons(hd, tail) => ()
    }
  };
  fn Drive (b : &mut (List (Σ (k : Nat). Nat))) -> Unit {
    if e : IsNilBP (*b) { () } else { TakeHd(&m *b, e) }
  };
  () }
example : progOk dispatchNil = true := by native_decide

/-- Identity applications for the constructor-argument fence (`KeepLe`'s trick):
    a capital comptime snapshot cannot be cited BARE in a constructor argument,
    but an application in the same position is ⇝-computed. -/
def IdNatP : Term := prog defer_check { λ (X : Nat). X }
def IdBktP : Term := prog defer_check { λ (X : List (Σ (k : Nat). Nat)). X }

/-- P2: THE COMPOSITE. Through-borrow match on `src`; carve of the 2-slot `dst`
    INSIDE the Cons arm (slot 0, literal indices so `AgetB` computes); the
    rotation with a parent read of `*src` after mutating through `tail`; and the
    return rides Σ0 snapshots plus old-relative Id evidence — the head
    decomposition, the src tail equation, and the pushed slot's pointwise Find
    equation, all expected to close by Refl. The `Hfr` citation checks a
    two-borrowed-places hypothesis instantiating after refinement. Snapshots are
    CAPITAL (comptime, non-taking) lets; the rotation's lowercase reads are each
    immediately followed by the overwrite of their source slot. -/
def push2 : Term := prog{
  fn Push2 (src : &mut (List (Σ (k : Nat). Nat)),
            dst : &mut (Array 2 (List (Σ (k : Nat). Nat))),
            Hne : Id Bool (IsNilBP (*src)) False,
            Hfr : Π (K2 : Nat) → Π (Hk2 : Id Bool (HitL K2 (*src)) True) →
                  Id (Σ (bb : Bool). OptP bb Nat)
                    (FindL K2 (AgetB 2 (*dst) Z)) NoneN)
      -> Σ0 (K0 : Nat). Σ0 (V0 : Nat). Σ0 (T0 : List (Σ (k : Nat). Nat)).
         Σ0 (B0 : List (Σ (k : Nat). Nat)). Σ0 (B1 : List (Σ (k : Nat). Nat)).
         Σ (Hdec : Id (List (Σ (k : Nat). Nat)) (old *src) (Cons(Pair(K0, V0), T0))).
         Σ (Hsrc : Id (List (Σ (k : Nat). Nat)) (*src) T0).
         Σ (Hln : Id Nat (LenE (old *src)) (S (LenE (*src)))).
         Σ (Hnew : Id (List (Σ (k : Nat). Nat)) B1 (Cons(Pair(K0, V0), B0))).
         Π (Q : Nat) → Id (Σ (bb : Bool). OptP bb Nat)
           (FindL Q B1)
           (boolRec (λ (W2 : Bool). Σ (bb : Bool). OptP bb Nat) (SomeN V0)
             (FindL Q B0) (Eqb Q K0))
      { match src {
          Nil => botElim Unit (BoolTF Hne),
          Cons(Pair(kk, vv), tail) => {
            let K0 = *kk;
            let V0 = *vv;
            let T0 = *tail;
            let HfrK = Hfr K0 (IdSym Bool True (HitL K0 (Cons(Pair(K0, V0), T0)))
                         (HitEvHit K0 V0 K0 T0 (EqbRefl K0)));
            let pre = &m (*dst)[Z ; Z ; 2 | LeAdd Z 2 | Refl];
            let cell = &m (*dst)[Z ; 1 ; 1];
            let bb = &m (*cell)[0];
            let B0 = *bb;
            let tmp = *tail;
            *tail := *bb;
            *bb := *src;
            *src := tmp;
            let B1 = *bb;
            Pair(IdNatP K0, Pair(IdNatP V0, Pair(IdBktP T0, Pair(IdBktP B0,
              Pair(IdBktP B1, Pair(Refl, Pair(Refl, Pair(Refl, Pair(Refl,
                λ (Q : Nat). Refl)))))))))
          }
        } };
  () }
example : progOk push2 = true := by native_decide

/-- P4: `j` at the bucket type — `NatRw`/`ListRw`'s counterpart. -/
def BktRwP : Term := prog defer_check {
  λ (P : List (Σ (k : Nat). Nat) → Type).
  λ (X : List (Σ (k : Nat). Nat)). λ (Y : List (Σ (k : Nat). Nat)).
    λ (H : Id (List (Σ (k : Nat). Nat)) X Y). λ (Px : P X).
      j (List (Σ (k : Nat). Nat)) X
        (λ (Y2 : List (Σ (k : Nat). Nat)).
          λ (Hh : Id (List (Σ (k : Nat). Nat)) X Y2). P Y2) Px Y H }
def BktRwPTy : Term := prog defer_check {
  Π (P : List (Σ (k : Nat). Nat) → Type) →
  Π (X : List (Σ (k : Nat). Nat)) → Π (Y : List (Σ (k : Nat). Nat)) →
    Id (List (Σ (k : Nat). Nat)) X Y → P X → P Y }
example : chkL BktRwP BktRwPTy = true := by native_decide

/-- P5: the concrete inline rotation with values — after rotating the head of
    `a` onto `b`, `Refl` closes both final states. -/
def rotConcrete : Term := prog{
  let a = Cons(Pair(1, 10), Cons(Pair(2, 20), Nil));
  let b = Cons(Pair(9, 90), Nil);
  let og = &m a;
  let nw = &m b;
  match og {
    Nil => (),
    Cons(hd, tail) => {
      let tmp = *tail;
      *tail := *nw;
      *nw := *og;
      *og := tmp;
      ()
    }
  };
  let a2 = a;
  let b2 = b;
  let H1 = (Refl : Id (List (Σ (k : Nat). Nat)) a2 Cons(Pair(2, 20), Nil));
  let H2 = (Refl : Id (List (Σ (k : Nat). Nat)) b2
              Cons(Pair(1, 10), Cons(Pair(9, 90), Nil)));
  () }
example : progOk rotConcrete = true := by native_decide

end Dllbc.Tests.ProbeRotate
end
