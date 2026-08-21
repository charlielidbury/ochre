import Dllbc.Program
import Dllbc.FnMacro
import Dllbc.ElabCheck
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas

/-! # The standard lemma chain (docs/20 stage 4)

    Every StdLemmas lemma as an `fn`, in one module block: the signature is the
    stated type, the body is the proof, and this block elaborating IS the
    definition-site check. 41 are native match+recursion rewrites; the rest
    wrap the original proof term (renamed `XRaw` in StdLemmas.lean) applied to
    the parameters. Consumers seed from `std.env` and cite lemmas by name. -/

namespace Dllbc
open Dllbc.StdLemmas

set_option maxHeartbeats 0 in
def std : Checked := prog () {
  -- ── segment 0 ──

  fn LeRefl [n] (n : Nat) -> Le n n {
    match n { Z => unit, S(k) => LeRefl(k) } };

  fn LeTrans [a] (a : Nat, b : Nat, c : Nat, Hab : Le a b, Hbc : Le b c) -> Le a c {
    match a { Z => unit,
      S(a2) => match b { Z => botElim (Le (S a2) c) Hab,
        S(b2) => match c { Z => botElim (Le (S a2) Z) Hbc,
          S(c2) => LeTrans(a2, b2, c2, Hab, Hbc) } } } };

  fn LeUpR [a] (a : Nat, b : Nat, H : Le a b) -> Le a (S b) {
    match a { Z => unit,
      S(a2) => match b { Z => botElim (Le (S a2) (S Z)) H,
        S(b2) => LeUpR(a2, b2, H) } } };

  fn LeAdd [i] (i : Nat, g : Nat) -> Le i (Add i g) {
    match i { Z => unit, S(i2) => LeAdd(i2, g) } };

  fn LeAddL [a] (b : Nat, a : Nat) -> Le b (Add a b) {
    match a { Z => LeRefl(b),
      S(a2) => LeUpR(b, Add a2 b, LeAddL(b, a2)) } };

  fn LeAddSucc [i] (i : Nat, g : Nat) -> Le (S i) (Add i (S g)) {
    match i { Z => unit, S(i2) => LeAddSucc(i2, g) } };

  fn LeRwR (a : Nat, x : Nat, y : Nat, h : Id Nat x y, p : Le a x) -> Le a y {
    match h { Refl => p } };

  fn LeRwL (b : Nat, x : Nat, y : Nat, h : Id Nat x y, p : Le x b) -> Le y b {
    match h { Refl => p } };

  fn LeAddMonoL [lo] (lo : Nat, a : Nat, b : Nat, h : Le a b) -> Le (Add lo a) (Add lo b) {
    match lo { Z => h, S(lo2) => LeAddMonoL(lo2, a, b, h) } };

  fn IdTrans (A : Type, x : A, y : A, z : A, p : Id A x y, q : Id A y z) -> Id A x z {
    match p { Refl => q } };

  fn IdCongr (A : Type, B : Type, F : A → B, x : A, y : A, p : Id A x y) -> Id B (F x) (F y) {
    match p { Refl => Refl } };

  -- ── segment 1 ──


  -- P1: no composition through `j`/IdCongr/IdTrans is needed here — a single
  -- non-recursive `Refl`-match transports the proof directly.
  fn IdSym (A : Type, x : A, y : A, p : Id A x y) -> Id A y x {
    match p { Refl => Refl }
  };

  -- P2 (see report): AddZero/AddSucc/AddComm/AddAssoc/CountAppend/LenSet/
  -- LenSwapL/CountConsCongr/CountConsHit/SwapLSet all compose their recursive
  -- step through IdCongr/IdTrans/j, whose ι-rule needs a literal Refl-shaped
  -- witness — a `fn` self-call desugars to the opaque `Ih`, which `j` cannot
  -- reduce through. So these stay spliced citations of the original proof.

  fn AddZero (a : Nat) -> Id Nat (Dllbc.StdLemmas.Add a Z) a { Dllbc.StdLemmas.AddZeroRaw a };

  fn AddSucc (a : Nat, b : Nat) -> Id Nat (Dllbc.StdLemmas.Add a (S b)) (S (Dllbc.StdLemmas.Add a b)) {
    Dllbc.StdLemmas.AddSuccRaw a b
  };

  fn AddComm (a : Nat, b : Nat) -> Id Nat (Dllbc.StdLemmas.Add a b) (Dllbc.StdLemmas.Add b a) {
    Dllbc.StdLemmas.AddCommRaw a b
  };

  fn AddAssoc (a : Nat, b : Nat, c : Nat)
      -> Id Nat (Dllbc.StdLemmas.Add (Dllbc.StdLemmas.Add a b) c) (Dllbc.StdLemmas.Add a (Dllbc.StdLemmas.Add b c)) {
    Dllbc.StdLemmas.AddAssocRaw a b c
  };

  fn CountAppend (m : Nat, a : List Nat, b : List Nat)
      -> Id Nat (Dllbc.StdLemmas.Count m (Dllbc.StdLemmas.Append a b))
           (Dllbc.StdLemmas.Add (Dllbc.StdLemmas.Count m a) (Dllbc.StdLemmas.Count m b)) {
    Dllbc.StdLemmas.CountAppendRaw m a b
  };

  fn LenSet (k : Nat, v : Nat, l : List Nat) -> Id Nat (Dllbc.StdLemmas.Len (Dllbc.StdLemmas.Set k v l)) (Dllbc.StdLemmas.Len l) {
    Dllbc.StdLemmas.LenSetRaw k v l
  };

  fn LenSwapL (i : Nat, j : Nat, l : List Nat) -> Id Nat (Dllbc.StdLemmas.Len (Dllbc.StdLemmas.SwapL i j l)) (Dllbc.StdLemmas.Len l) {
    Dllbc.StdLemmas.LenSwapLRaw i j l
  };

  fn CountConsCongr (m : Nat, h : Nat, l1 : List Nat, l2 : List Nat,
      p : Id Nat (Dllbc.StdLemmas.Count m l1) (Dllbc.StdLemmas.Count m l2))
      -> Id Nat (Dllbc.StdLemmas.Count m (Cons h l1)) (Dllbc.StdLemmas.Count m (Cons h l2)) {
    Dllbc.StdLemmas.CountConsCongrRaw m h l1 l2 p
  };

  fn CountConsHit (m : Nat, a : Nat, l : List Nat, hq : Id Bool (Dllbc.StdLemmas.Eqb m a) True)
      -> Id Nat (Dllbc.StdLemmas.Count m (Cons a l)) (S (Dllbc.StdLemmas.Count m l)) {
    Dllbc.StdLemmas.CountConsHitRaw m a l hq
  };

  fn SwapLSet (i : Nat, j : Nat, l : List Nat,
      pij : Dllbc.StdLemmas.Le (S i) j, p2 : Dllbc.StdLemmas.Le (S j) (Dllbc.StdLemmas.Len l))
      -> Id (List Nat)
           (Dllbc.StdLemmas.Set i (Dllbc.StdLemmas.NthL j l) (Dllbc.StdLemmas.Set j (Dllbc.StdLemmas.NthL i l) l))
           (Dllbc.StdLemmas.SwapL i j l) {
    Dllbc.StdLemmas.SwapLSetRaw i j l pij p2
  };

  -- ── segment 2 ──

  fn BoolFT (h : Id Bool False True) -> Bot { Dllbc.StdLemmas.BoolFTRaw h };

  fn BoolTF (h : Id Bool True False) -> Bot { Dllbc.StdLemmas.BoolTFRaw h };

  fn LebTrueLe [a] (a : Nat, b : Nat, h : Id Bool (Leb a b) True) -> Le a b {
    match a {
      Z => unit,
      S(a') => match b {
        Z => { let bad = BoolFT(h); botElim (Le (S a') Z) bad },
        S(b') => LebTrueLe(a', b', h)
      }
    }
  };

  fn LebFalseGt [a] (a : Nat, b : Nat, h : Id Bool (Leb a b) False) -> Le (S b) a {
    match a {
      Z => { let bad = BoolTF(h); botElim (Le (S b) Z) bad },
      S(a') => match b {
        Z => unit,
        S(b') => LebFalseGt(a', b', h)
      }
    }
  };

  fn LeAntisym [a] (a : Nat, b : Nat, h1 : Le a b, h2 : Le b a) -> Id Nat a b {
    match a {
      Z => match b {
        Z => Refl,
        S(b') => botElim (Id Nat Z (S b')) h2
      },
      S(a') => match b {
        Z => botElim (Id Nat (S a') Z) h1,
        S(b') => { let ih = LeAntisym(a', b', h1, h2); IdCongr Nat Nat (λ (n : Nat). S n) a' b' ih }
      }
    }
  };

  fn Znots (x : Nat, h : Id Nat Z (S x)) -> Bot { Dllbc.StdLemmas.ZnotsRaw x h };

  fn SInj (m : Nat, n : Nat, h : Id Nat (S m) (S n)) -> Id Nat m n { Dllbc.StdLemmas.SInjRaw m n h };

  fn Sub [a] (a : Nat, b : Nat) -> Nat {
    match a {
      Z => Z,
      S(a') => match b {
        Z => S(a'),
        S(b') => Sub(a', b')
      }
    }
  };

  fn AddSubCancel (a : Nat, b : Nat, h : Le b a) -> Id Nat (Add b (Dllbc.StdLemmas.SubRaw a b)) a { Dllbc.StdLemmas.AddSubCancelRaw a b h };

  fn LePredL (a : Nat, b : Nat, h : Le (S a) b) -> Le a b { Dllbc.StdLemmas.LePredLRaw a b h };

  fn EqbGtFalse [h] (h : Nat, x : Nat, hlt : Le (S h) x) -> Id Bool (Eqb x h) False {
    match h {
      Z => match x {
        Z => botElim (Id Bool (Eqb Z Z) False) hlt,
        S(x') => Refl
      },
      S(h') => match x {
        Z => botElim (Id Bool (Eqb Z (S h')) False) hlt,
        S(x') => EqbGtFalse(h', x', hlt)
      }
    }
  };

  -- ── segment 3 ──

  fn EqbLtFalse [a] (a : Nat, b : Nat, hab : Le (S a) b) -> Id Bool (Eqb a b) False {
    match a {
      Z => match b {
        Z => botElim (Id Bool (Eqb Z Z) False) hab,
        S(b2) => Refl },
      S(a2) => match b {
        Z => botElim (Id Bool (Eqb (S a2) Z) False) hab,
        S(b2) => EqbLtFalse(a2, b2, hab) } } };

  fn CountConsMiss (m : Nat, h : Nat, t : List Nat, hq : Id Bool (Eqb m h) False) ->
      Id Nat (Count m (Cons h t)) (Count m t) {
    Dllbc.StdLemmas.CountConsMissRaw m h t hq };

  fn EqbRefl [n] (n : Nat) -> Id Bool (Eqb n n) True {
    match n { Z => Refl, S(n2) => EqbRefl(n2) } };

  fn ListRw (P : List Nat → Type, x : List Nat, y : List Nat,
      h : Id (List Nat) x y, px : P x) -> P y {
    Dllbc.StdLemmas.ListRwRaw P x y h px };

  fn SortedHead (h : Nat, t : List Nat, s0 : Sorted (Cons h t)) -> Bound h t {
    match s0 { Pair(x, y) => x } };

  fn SortedTail (h : Nat, t : List Nat, s0 : Sorted (Cons h t)) -> Sorted t {
    match s0 { Pair(x, y) => y } };

  -- P2: `Ub`/`Lb` are old-style hand terms whose Σ binds a COMPTIME first
  -- component (`Σ (Hh : Le H P). Ih`, capital `Hh`), and the fence refuses to
  -- ⇒-move a comptime match-arm binder out as a function's return value — P1
  -- (`match u { Pair(X, y) => X }`) hits "fence: 'X' is a COMPTIME binder ...
  -- cannot be ⇒-moved" no matter which case (X)/(x) is tried for the first
  -- component (lower-case there instead fails the earlier "arm binder is
  -- lowercase but the component is COMPTIME" check). Citing the old term
  -- sidesteps it.
  fn UbHead (p : Nat, h : Nat, t : List Nat, u : Ub p (Cons h t)) -> Le h p {
    Dllbc.StdLemmas.UbHeadRaw p h t u };

  fn UbTail (p : Nat, h : Nat, t : List Nat, u : Ub p (Cons h t)) -> Ub p t {
    Dllbc.StdLemmas.UbTailRaw p h t u };

  fn LbBound (p : Nat, l : List Nat, hl : Lb p l) -> Bound p l {
    Dllbc.StdLemmas.LbBoundRaw p l hl };

  fn BoundAppend (h : Nat, p : Nat, t : List Nat, b : List Nat, hb : Bound h t, hp : Le h p) ->
      Bound h (Append t (Cons p b)) {
    match t {
      Nil => hp,
      Cons(h2, t2) => hb } };

  -- P2: the original's recursion feeds `T`/`P`/`B`/`Sa`/`Ua` to SIX different
  -- helper calls in the Cons arm, each more than once; as `fn`+`match`
  -- lowercase (runtime) params those uses are affine moves and collide
  -- ("readR: t#8 holds ⊥ (use-after-move)"). Citing the old term sidesteps the
  -- sharing problem entirely — the original already checks (chkLib,
  -- StdLemmas.lean:2036).
  fn SortedAppendPivot (p : Nat, a : List Nat, b : List Nat,
      sa : Sorted a, ua : Ub p a, sb : Sorted b, lb0 : Lb p b) ->
      Sorted (Append a (Cons p b)) {
    Dllbc.StdLemmas.SortedAppendPivotRaw p a b sa ua sb lb0 };

  -- ── segment 4 ──

  fn CountConsL (n : Nat, x : Nat, a : List Nat, b : List Nat, c : List Nat,
      h : Id Nat (Add (Count n a) (Count n b)) (Count n c))
      -> Id Nat (Add (Count n (Cons x a)) (Count n b)) (Count n (Cons x c)) {
    Dllbc.StdLemmas.CountConsLRaw n x a b c h };

  fn CountConsR (n : Nat, x : Nat, a : List Nat, b : List Nat, c : List Nat,
      h : Id Nat (Add (Count n a) (Count n b)) (Count n c))
      -> Id Nat (Add (Count n a) (Count n (Cons x b))) (Count n (Cons x c)) {
    Dllbc.StdLemmas.CountConsRRaw n x a b c h };

  fn LbHead (p : Nat, h : Nat, t : List Nat, u : Dllbc.StdLemmas.Lb p (Cons h t)) -> Le p h {
    Dllbc.StdLemmas.LbHeadRaw p h t u };

  fn LbTail (p : Nat, h : Nat, t : List Nat, u : Dllbc.StdLemmas.Lb p (Cons h t)) -> Dllbc.StdLemmas.Lb p t {
    Dllbc.StdLemmas.LbTailRaw p h t u };

  fn NoAboveOfUb (p : Nat, l : List Nat, hu : Dllbc.StdLemmas.Ub p l, x : Nat, hx : Le (S p) x)
      -> Id Nat (Count x l) Z {
    Dllbc.StdLemmas.NoAboveOfUbRaw p l hu x hx };

  fn UbOfNoAbove (p : Nat, l : List Nat,
      HN : (Π (x : Nat) → Le (S p) x → Id Nat (Count x l) Z)) -> Dllbc.StdLemmas.Ub p l {
    Dllbc.StdLemmas.UbOfNoAboveRaw p l HN };

  fn UbPerm (p : Nat, a : List Nat, b : List Nat,
      HC : (Π (n : Nat) → Id Nat (Count n a) (Count n b)), hb : Dllbc.StdLemmas.Ub p b) -> Dllbc.StdLemmas.Ub p a {
    Dllbc.StdLemmas.UbPermRaw p a b HC hb };

  fn NoBelowOfLb (p : Nat, l : List Nat, hl : Dllbc.StdLemmas.Lb p l, x : Nat, hx : Le (S x) p)
      -> Id Nat (Count x l) Z {
    Dllbc.StdLemmas.NoBelowOfLbRaw p l hl x hx };

  fn LbOfNoBelow (p : Nat, l : List Nat,
      HN : (Π (x : Nat) → Le (S x) p → Id Nat (Count x l) Z)) -> Dllbc.StdLemmas.Lb p l {
    Dllbc.StdLemmas.LbOfNoBelowRaw p l HN };

  fn LbPerm (p : Nat, a : List Nat, b : List Nat,
      HC : (Π (n : Nat) → Id Nat (Count n a) (Count n b)), hb : Dllbc.StdLemmas.Lb p b) -> Dllbc.StdLemmas.Lb p a {
    Dllbc.StdLemmas.LbPermRaw p a b HC hb };

  fn SortedHeadA (k : Nat, h : Nat, t : Array k Nat,
      s0 : Dllbc.StdLemmas.SortedA (S k) (acons k h t)) -> Dllbc.StdLemmas.BoundA h k t {
    Dllbc.StdLemmas.SortedHeadARaw k h t s0 };

  -- ── segment 5 ──


  -- P1: non-recursive projection out of a Σ (`fn` with no `[k]` hint is a
  -- plain sealed λ, so `match` here is just the elim sugar, no recursor).
  fn SortedTailA (K : Nat, H : Nat, T : Array K Nat,
      s0 : Σ (hb : Dllbc.StdLemmas.BoundA H K T). Dllbc.StdLemmas.SortedA K T)
      -> Dllbc.StdLemmas.SortedA K T {
    match s0 { Pair(hb, y) => y }
  };

  fn UbHeadA (P : Nat, K : Nat, H : Nat, T : Array K Nat,
      u : Σ (hu : Le H P). Dllbc.StdLemmas.UbA P K T)
      -> Le H P {
    match u { Pair(hu, y) => hu }
  };

  fn UbTailA (P : Nat, K : Nat, H : Nat, T : Array K Nat,
      u : Σ (hu : Le H P). Dllbc.StdLemmas.UbA P K T)
      -> Dllbc.StdLemmas.UbA P K T {
    match u { Pair(hu, y) => y }
  };

  -- P2 from here: all touch `arrRec`/`Array` (or the `j`-eliminator), which the
  -- `fn`+`match` sugar has no recursor for (only `Nat`/`List` recursion). Body
  -- is a splice of the existing StdLemmas proof applied to the new telescope —
  -- bare qualified identifier with DSL space-application, no `%`.

  fn LbBoundA (P : Nat, N : Nat, A : Array N Nat, hl : Dllbc.StdLemmas.LbA P N A)
      -> Dllbc.StdLemmas.BoundA P N A {
    Dllbc.StdLemmas.LbBoundARaw P N A hl
  };

  fn BoundArrCat (H : Nat, P : Nat, K : Nat, T : Array K Nat, Q : Nat, B : Array Q Nat,
      hbt : Dllbc.StdLemmas.BoundA H K T, hhp : Le H P)
      -> Dllbc.StdLemmas.BoundA H (Add K (S Q))
           (arrCat K (S Q) T (arrCat 1 Q (Dllbc.StdLemmas.Asingle P) B)) {
    Dllbc.StdLemmas.BoundArrCatRaw H P K T Q B hbt hhp
  };

  fn SortedArrCat (P : Nat, M : Nat, A : Array M Nat, Q : Nat, B : Array Q Nat,
      sa : Dllbc.StdLemmas.SortedA M A, ua : Dllbc.StdLemmas.UbA P M A,
      sb : Dllbc.StdLemmas.SortedA Q B, lb0 : Dllbc.StdLemmas.LbA P Q B)
      -> Dllbc.StdLemmas.SortedA (Add M (S Q))
           (arrCat M (S Q) A (arrCat 1 Q (Dllbc.StdLemmas.Asingle P) B)) {
    Dllbc.StdLemmas.SortedArrCatRaw P M A Q B sa ua sb lb0
  };

  fn CountArrCat (X : Nat, M : Nat, A : Array M Nat, Q : Nat, B : Array Q Nat)
      -> Id Nat (Dllbc.StdLemmas.CountA X (Add M Q) (arrCat M Q A B))
           (Add (Dllbc.StdLemmas.CountA X M A) (Dllbc.StdLemmas.CountA X Q B)) {
    Dllbc.StdLemmas.CountArrCatRaw X M A Q B
  };

  fn CountAconsHit (M : Nat, A : Nat, K : Nat, L : Array K Nat, hq : Id Bool (Eqb M A) True)
      -> Id Nat (Dllbc.StdLemmas.CountA M (S K) (acons K A L))
           (S (Dllbc.StdLemmas.CountA M K L)) {
    Dllbc.StdLemmas.CountAconsHitRaw M A K L hq
  };

  fn CountAconsMiss (M : Nat, H : Nat, K : Nat, T : Array K Nat, hq : Id Bool (Eqb M H) False)
      -> Id Nat (Dllbc.StdLemmas.CountA M (S K) (acons K H T)) (Dllbc.StdLemmas.CountA M K T) {
    Dllbc.StdLemmas.CountAconsMissRaw M H K T hq
  };

  fn NoAboveOfUbA (P : Nat, N : Nat, A : Array N Nat, hu : Dllbc.StdLemmas.UbA P N A,
      X : Nat, hx : Le (S P) X)
      -> Id Nat (Dllbc.StdLemmas.CountA X N A) Z {
    Dllbc.StdLemmas.NoAboveOfUbARaw P N A hu X hx
  };

  fn UbOfNoAboveA (P : Nat, N : Nat, A : Array N Nat,
      Hn : Π (X : Nat) → Le (S P) X → Id Nat (Dllbc.StdLemmas.CountA X N A) Z)
      -> Dllbc.StdLemmas.UbA P N A {
    Dllbc.StdLemmas.UbOfNoAboveARaw P N A Hn
  };

  -- ── segment 6 ──

  fn UbPermA (P : Nat, M : Nat, A : Array M Nat, Q : Nat, B : Array Q Nat,
      Hc : Π (X : Nat) → Id Nat (Dllbc.StdLemmas.CountA X M A) (Dllbc.StdLemmas.CountA X Q B),
      Hb : Dllbc.StdLemmas.UbA P Q B) -> Dllbc.StdLemmas.UbA P M A {
    Dllbc.StdLemmas.UbPermARaw P M A Q B Hc Hb };

  fn NoBelowOfLbA (P : Nat, N : Nat, A : Array N Nat, Hlb : Dllbc.StdLemmas.LbA P N A,
      X : Nat, Hx : Le (S X) P) -> Id Nat (Dllbc.StdLemmas.CountA X N A) Z {
    Dllbc.StdLemmas.NoBelowOfLbARaw P N A Hlb X Hx };

  fn LbOfNoBelowA (P : Nat, N : Nat, A : Array N Nat,
      Hn : Π (X : Nat) → Le (S X) P → Id Nat (Dllbc.StdLemmas.CountA X N A) Z) ->
      Dllbc.StdLemmas.LbA P N A {
    Dllbc.StdLemmas.LbOfNoBelowARaw P N A Hn };

  fn LbPermA (P : Nat, M : Nat, A : Array M Nat, Q : Nat, B : Array Q Nat,
      Hc : Π (X : Nat) → Id Nat (Dllbc.StdLemmas.CountA X M A) (Dllbc.StdLemmas.CountA X Q B),
      Hb : Dllbc.StdLemmas.LbA P Q B) -> Dllbc.StdLemmas.LbA P M A {
    Dllbc.StdLemmas.LbPermARaw P M A Q B Hc Hb };

  fn CountSwap2 (M : Nat, A : Nat, B : Nat) ->
      Id Nat (Dllbc.StdLemmas.CountA M 2 Arr(B, A)) (Dllbc.StdLemmas.CountA M 2 Arr(A, B)) {
    Dllbc.StdLemmas.CountSwap2Raw M A B };

  fn NatRw (P : Nat → Type, X : Nat, Y : Nat, H : Id Nat X Y, Px : P X) -> P Y {
    Dllbc.StdLemmas.NatRwRaw P X Y H Px };

  fn LeZeroEq [n] (n : Nat, h : Le n Z) -> Id Nat n Z {
    match n { Z => Refl, S(n2) => botElim (Id Nat (S n2) Z) h } };

  fn SortedANil (N : Nat, A : Array N Nat, H : Id Nat N Z) -> Dllbc.StdLemmas.SortedA N A {
    Dllbc.StdLemmas.SortedANilRaw N A H };

  fn SplitANil (P : Nat, Kz : Nat, N : Nat, A : Array N Nat, Hz : Id Nat N Z) ->
      Dllbc.StdLemmas.SplitAL P Kz N A {
    Dllbc.StdLemmas.SplitANilRaw P Kz N A Hz };

  fn SplitA0Lb (P : Nat, N : Nat, A : Array N Nat, Hs : Dllbc.StdLemmas.SplitAL P Z N A) ->
      Dllbc.StdLemmas.LbA P N A {
    Dllbc.StdLemmas.SplitA0LbRaw P N A Hs };

  fn SplitACatE1 (P : Nat, K : Nat, Mm : Nat, L : Array K Nat, W : Array Mm Nat,
      Hs : Dllbc.StdLemmas.SplitAL P (S K) (Add K Mm) (arrCat K Mm L W)) ->
      Σ (Hu : Dllbc.StdLemmas.UbA P K L). Dllbc.StdLemmas.SplitAL P (S Z) Mm W {
    Dllbc.StdLemmas.SplitACatE1Raw P K Mm L W Hs };

  -- ── segment 7 ──

  fn SplitACatI0 (P : Nat, K : Nat, Mm : Nat, L : Array K Nat, W : Array Mm Nat,
      U : Dllbc.StdLemmas.UbA P K L, H : Dllbc.StdLemmas.SplitAL P Z Mm W)
      -> Dllbc.StdLemmas.SplitAL P K (Add K Mm) (arrCat K Mm L W) {
    Dllbc.StdLemmas.SplitACatI0Raw P K Mm L W U H };

  fn PartACatI0 (Pv : Nat, K : Nat, Mm : Nat, L : Array K Nat, W : Array Mm Nat,
      U : Dllbc.StdLemmas.UbA Pv K L, H : Dllbc.StdLemmas.PartA Pv Z Mm W)
      -> Dllbc.StdLemmas.PartA Pv K (Add K Mm) (arrCat K Mm L W) {
    Dllbc.StdLemmas.PartACatI0Raw Pv K Mm L W U H };

  fn PartACatE0 (Pv : Nat, K : Nat, Mm : Nat, L : Array K Nat, W : Array Mm Nat,
      S0 : Dllbc.StdLemmas.PartA Pv K (Add K Mm) (arrCat K Mm L W))
      -> Σ (Hu : Dllbc.StdLemmas.UbA Pv K L). Dllbc.StdLemmas.PartA Pv Z Mm W {
    Dllbc.StdLemmas.PartACatE0Raw Pv K Mm L W S0 };

  fn SplitACatUb (P : Nat, K : Nat, Mm : Nat, L : Array K Nat, W : Array Mm Nat,
      S0 : Dllbc.StdLemmas.SplitAL P (S K) (Add K Mm) (arrCat K Mm L W))
      -> Dllbc.StdLemmas.UbA P K L {
    elim (Dllbc.StdLemmas.SplitACatE1Raw P K Mm L W S0)
      return (λ (Qz : Σ (Hu : Dllbc.StdLemmas.UbA P K L). Dllbc.StdLemmas.SplitAL P (S Z) Mm W).
                Dllbc.StdLemmas.UbA P K L) {
        Pair (U) (V) => U } };

  fn SplitACatRest (P : Nat, K : Nat, Mm : Nat, L : Array K Nat, W : Array Mm Nat,
      S0 : Dllbc.StdLemmas.SplitAL P (S K) (Add K Mm) (arrCat K Mm L W))
      -> Dllbc.StdLemmas.SplitAL P (S Z) Mm W {
    elim (Dllbc.StdLemmas.SplitACatE1Raw P K Mm L W S0)
      return (λ (Qz : Σ (Hu : Dllbc.StdLemmas.UbA P K L). Dllbc.StdLemmas.SplitAL P (S Z) Mm W).
                Dllbc.StdLemmas.SplitAL P (S Z) Mm W) {
        Pair (U) (V) => V } };

  fn SplitA1Head (P : Nat, R : Nat, G : Array R Nat, Yv : Nat,
      S0 : Σ (Hh : Le Yv P). Dllbc.StdLemmas.SplitAL P Z R G)
      -> Le Yv P {
    elim S0 return (λ (Qz : Σ (Hh : Le Yv P). Dllbc.StdLemmas.SplitAL P Z R G). Le Yv P) {
      Pair (U) (V) => U } };

  fn SplitA1Tail (P : Nat, R : Nat, G : Array R Nat, Yv : Nat,
      S0 : Σ (Hh : Le Yv P). Dllbc.StdLemmas.SplitAL P Z R G)
      -> Dllbc.StdLemmas.SplitAL P Z R G {
    elim S0 return (λ (Qz : Σ (Hh : Le Yv P). Dllbc.StdLemmas.SplitAL P Z R G).
                      Dllbc.StdLemmas.SplitAL P Z R G) {
      Pair (U) (V) => V } };

  fn PartACatUb (Pv : Nat, K : Nat, Mm : Nat, L : Array K Nat, W : Array Mm Nat,
      S0 : Dllbc.StdLemmas.PartA Pv K (Add K Mm) (arrCat K Mm L W))
      -> Dllbc.StdLemmas.UbA Pv K L {
    elim (Dllbc.StdLemmas.PartACatE0Raw Pv K Mm L W S0)
      return (λ (Qz : Σ (Hu : Dllbc.StdLemmas.UbA Pv K L). Dllbc.StdLemmas.PartA Pv Z Mm W).
                Dllbc.StdLemmas.UbA Pv K L) {
        Pair (U) (V) => U } };

  fn PartACatRest (Pv : Nat, K : Nat, Mm : Nat, L : Array K Nat, W : Array Mm Nat,
      S0 : Dllbc.StdLemmas.PartA Pv K (Add K Mm) (arrCat K Mm L W))
      -> Dllbc.StdLemmas.PartA Pv Z Mm W {
    elim (Dllbc.StdLemmas.PartACatE0Raw Pv K Mm L W S0)
      return (λ (Qz : Σ (Hu : Dllbc.StdLemmas.UbA Pv K L). Dllbc.StdLemmas.PartA Pv Z Mm W).
                Dllbc.StdLemmas.PartA Pv Z Mm W) {
        Pair (U) (V) => V } };

  fn PartA0Eq (Pv : Nat, Jj : Nat, G : Array Jj Nat, Ev : Nat,
      S0 : Σ (He : Id Nat Ev Pv). Dllbc.StdLemmas.LbA Pv Jj G)
      -> Id Nat Ev Pv {
    elim S0 return (λ (Qz : Σ (He : Id Nat Ev Pv). Dllbc.StdLemmas.LbA Pv Jj G). Id Nat Ev Pv) {
      Pair (U) (V) => U } };

  fn PartA0Lb (Pv : Nat, Jj : Nat, G : Array Jj Nat, Ev : Nat,
      S0 : Σ (He : Id Nat Ev Pv). Dllbc.StdLemmas.LbA Pv Jj G)
      -> Dllbc.StdLemmas.LbA Pv Jj G {
    elim S0 return (λ (Qz : Σ (He : Id Nat Ev Pv). Dllbc.StdLemmas.LbA Pv Jj G).
                      Dllbc.StdLemmas.LbA Pv Jj G) {
      Pair (U) (V) => V } };

  -- ── segment 8 ──


  fn CountAconsCongr (Q : Nat, H : Nat, K : Nat, T1 : Array K Nat, T2 : Array K Nat,
      Hc : Id Nat (Dllbc.StdLemmas.CountA Q K T1) (Dllbc.StdLemmas.CountA Q K T2)) ->
      Id Nat (Dllbc.StdLemmas.CountA Q (S K) (acons K H T1))
             (Dllbc.StdLemmas.CountA Q (S K) (acons K H T2)) {
    Dllbc.StdLemmas.CountAconsCongrRaw Q H K T1 T2 Hc };

  fn BumpComm (b1 : Bool, b2 : Bool, cl : Nat, cg : Nat) ->
      Id Nat (Dllbc.StdLemmas.BumpN b2 (Add cl (Dllbc.StdLemmas.BumpN b1 cg)))
             (Dllbc.StdLemmas.BumpN b1 (Add cl (Dllbc.StdLemmas.BumpN b2 cg))) {
    match b1 {
      True => match b2 { True => Refl, False => Dllbc.StdLemmas.AddSuccRaw cl cg },
      False => match b2 {
        True => Dllbc.StdLemmas.IdSymRaw Nat (Add cl (S cg)) (S (Add cl cg))
                   (Dllbc.StdLemmas.AddSuccRaw cl cg),
        False => Refl } } };

  fn CountSwapA (Q : Nat, X : Nat, Y : Nat, K : Nat, L : Array K Nat, R : Nat, G : Array R Nat) ->
      Id Nat (Dllbc.StdLemmas.CountA Q (S (Add K (S R)))
                (acons (Add K (S R)) Y (arrCat K (S R) L (acons R X G))))
             (Dllbc.StdLemmas.CountA Q (S (Add K (S R)))
                (acons (Add K (S R)) X (arrCat K (S R) L (acons R Y G)))) {
    Dllbc.StdLemmas.CountSwapARaw Q X Y K L R G };

  fn StepInv (b : Nat, r : Nat, c : Nat, h : Le (Add r c) b) ->
      Le (Add (Dllbc.StdLemmas.NextR r c) (Dllbc.StdLemmas.NextC b c)) b {
    match c {
      Z => Dllbc.StdLemmas.LeReflRaw b,
      S(c2) => Dllbc.StdLemmas.LeRwLRaw b (Add r (S c2)) (S (Add r c2))
                  (Dllbc.StdLemmas.AddSuccRaw r c2) h } };

  fn ModCLt [a] (a : Nat, b : Nat, r : Nat, c : Nat, h : Le (Add r c) b) ->
      Le (S (Dllbc.StdLemmas.ModC a b r c)) (S b) {
    match a {
      Z => Dllbc.StdLemmas.LeTransRaw r (Add r c) b (Dllbc.StdLemmas.LeAddRaw r c) h,
      S(a2) => ModCLt(a2, b, (Dllbc.StdLemmas.NextR r c), (Dllbc.StdLemmas.NextC b c),
                  StepInv(b, r, c, h)) } };

  fn ModLtN (a : Nat, n : Nat, h : Le (S Z) n) -> Le (S (Dllbc.StdLemmas.Mod a n)) n {
    match n {
      Z => botElim (Le (S (Dllbc.StdLemmas.Mod a Z)) Z) h,
      S(b2) => ModCLt(a, b2, Z, b2, Dllbc.StdLemmas.LeReflRaw b2) } };

  fn ModDec (I : Nat, N : Nat, H : Le (S I) N) -> Σ (R : Nat). Id Nat N (Add I (S R)) {
    Dllbc.StdLemmas.ModDecRaw I N H };

  fn AddSwapL [a] (a : Nat, b : Nat, c : Nat) ->
      Id Nat (Add a (Add b c)) (Add b (Add a c)) {
    match a {
      Z => Refl,
      S(a2) =>
        Dllbc.StdLemmas.IdTransRaw Nat (S (Add a2 (Add b c))) (S (Add b (Add a2 c))) (Add b (S (Add a2 c)))
          (Dllbc.StdLemmas.IdCongrRaw Nat Nat (λ (X : Nat). S X) (Add a2 (Add b c)) (Add b (Add a2 c))
             AddSwapL(a2, b, c))
          (Dllbc.StdLemmas.IdSymRaw Nat (Add b (S (Add a2 c))) (S (Add b (Add a2 c)))
             (Dllbc.StdLemmas.AddSuccRaw b (Add a2 c))) } };

  fn AddInterchange (A : Nat, B : Nat, C : Nat, D : Nat) ->
      Id Nat (Add (Add A B) (Add C D)) (Add (Add A C) (Add B D)) {
    Dllbc.StdLemmas.AddInterchangeRaw A B C D };

  fn MulSucc [a] (a : Nat, b : Nat) ->
      Id Nat (Dllbc.StdLemmas.Mul a (S b)) (Add a (Dllbc.StdLemmas.Mul a b)) {
    match a {
      Z => Refl,
      S(a2) => {
        let hsw = AddSwapL(b, a2, (Dllbc.StdLemmas.Mul a2 b));
        Dllbc.StdLemmas.IdCongrRaw Nat Nat (λ (X : Nat). S X)
          (Add b (Dllbc.StdLemmas.Mul a2 (S b))) (Add a2 (Add b (Dllbc.StdLemmas.Mul a2 b)))
          (Dllbc.StdLemmas.IdTransRaw Nat (Add b (Dllbc.StdLemmas.Mul a2 (S b)))
            (Add b (Add a2 (Dllbc.StdLemmas.Mul a2 b)))
            (Add a2 (Add b (Dllbc.StdLemmas.Mul a2 b)))
            (Dllbc.StdLemmas.IdCongrRaw Nat Nat (λ (X : Nat). Add b X)
               (Dllbc.StdLemmas.Mul a2 (S b)) (Add a2 (Dllbc.StdLemmas.Mul a2 b)) MulSucc(a2, b))
            hsw) } } };

  fn MulAddR [a] (a : Nat, b : Nat, c : Nat) ->
      Id Nat (Dllbc.StdLemmas.Mul a (Add b c))
             (Add (Dllbc.StdLemmas.Mul a b) (Dllbc.StdLemmas.Mul a c)) {
    match a {
      Z => Refl,
      S(a2) => {
        let hi = AddInterchange(b, c, (Dllbc.StdLemmas.Mul a2 b), (Dllbc.StdLemmas.Mul a2 c));
        Dllbc.StdLemmas.IdTransRaw Nat
          (Add (Add b c) (Dllbc.StdLemmas.Mul a2 (Add b c)))
          (Add (Add b c) (Add (Dllbc.StdLemmas.Mul a2 b) (Dllbc.StdLemmas.Mul a2 c)))
          (Add (Add b (Dllbc.StdLemmas.Mul a2 b)) (Add c (Dllbc.StdLemmas.Mul a2 c)))
          (Dllbc.StdLemmas.IdCongrRaw Nat Nat (λ (X : Nat). Add (Add b c) X)
            (Dllbc.StdLemmas.Mul a2 (Add b c))
            (Add (Dllbc.StdLemmas.Mul a2 b) (Dllbc.StdLemmas.Mul a2 c)) MulAddR(a2, b, c))
          hi } } };

  -- ── segment 9 ──


  -- P2: straight-line (IdTrans/IdCongr/MulAddR), no recursion — splice the
  -- existing checked proof, renamed telescope.
  fn MulTwoDouble (a : Nat, c : Nat) ->
      Id Nat (StdLemmas.Mul a (StdLemmas.Mul 2 c)) (Add (StdLemmas.Mul a c) (StdLemmas.Mul a c)) {
    StdLemmas.MulTwoDoubleRaw a c };

  -- P2: straight-line (LeRwR/LeRwL/AddComm/LeAddMonoL), no recursion.
  fn LeAddMonoR (a : Nat, b : Nat, k : Nat, h : Le a b) -> Le (Add a k) (Add b k) {
    StdLemmas.LeAddMonoRRaw a b k h };

  -- P2: straight-line (LeTrans/LeAddMonoR-shaped composition), no recursion.
  fn LeAddMono (a : Nat, b : Nat, c : Nat, d : Nat, H1 : Le a b, H2 : Le c d) ->
      Le (Add a c) (Add b d) {
    StdLemmas.LeAddMonoRaw a b c d H1 H2 };

  -- P1: elim on A with Ih = LeAddMono at the predecessor — the LeTrans-shaped
  -- match+recursion. Self-call `LeMulR(a2, b, c, H)` becomes `ih` at the
  -- predecessor; the local fn `LeAddMono` above is called by name.
  --
  -- H is CAPITAL (comptime), not lowercase, even though the original proof
  -- never matches on it: the S(a2) arm uses H twice on one path (once as
  -- LeAddMono's own proof argument, once threaded into the recursive
  -- call), and a lowercase H is a linear runtime resource that can only be
  -- read once per path — confirmed empirically: lowercase h fails
  -- elaboration with "h#3 holds ⊥ (use-after-move)", capitalizing it fixes
  -- it clean. LeTrans's own worked example (docs/20) keeps its analogous
  -- premises (Hab, Hbc) capital for the same reason.
  fn LeMulR [a] (a : Nat, b : Nat, c : Nat, H : Le b c) ->
      Le (StdLemmas.Mul a b) (StdLemmas.Mul a c) {
    match a {
      Z => unit,
      S(a2) => LeAddMono(b, c, StdLemmas.Mul a2 b, StdLemmas.Mul a2 c, H, LeMulR(a2, b, c, H)) } };

  -- P2: straight-line (LeTrans applied at unit / LeMulR), no recursion.
  fn Le5M4 (c : Nat, h : Le 2 c) -> Le 5 (StdLemmas.Mul 4 c) {
    StdLemmas.Le5M4Raw c h };

  -- P1: elim on N, no self-call in either arm (the S arm discharges by
  -- botElim on the impossible `h`) — match ⇜-refines `h`'s type per arm
  -- exactly as the LeTrans model does for its premises.
  fn FiveN4Zero (n : Nat, h : Le (StdLemmas.Mul 5 n) 4) -> Id Nat n Z {
    match n {
      Z => Refl,
      S(n2) => botElim (Id Nat (S n2) Z)
        (StdLemmas.LeRwLRaw 4 (StdLemmas.Mul 5 (S n2)) (Add 5 (StdLemmas.Mul 5 n2)) (StdLemmas.MulSuccRaw 5 n2) h) } };

  -- P1: elim on A, inner elim on B per arm, self-call `Ih B2 H` — the
  -- LeTrans-shaped nested match, decreasing only on A.
  fn LeLebTrue [a] (a : Nat, b : Nat, h : Le a b) -> Id Bool (Leb a b) True {
    match a {
      Z => Refl,
      S(a2) => match b {
        Z => botElim (Id Bool (Leb (S a2) Z) True) h,
        S(b2) => LeLebTrue(a2, b2, h) } } };

  -- P1: elim on A, inner elim on B per arm, self-call `Ih B2 H` in the S/S
  -- case only.
  fn EqbTrueEq [a] (a : Nat, b : Nat, h : Id Bool (Eqb a b) True) -> Id Nat a b {
    match a {
      Z => match b {
        Z => Refl,
        S(b2) => botElim (Id Nat Z (S b2)) (StdLemmas.BoolFTRaw h) },
      S(a2) => match b {
        Z => botElim (Id Nat (S a2) Z) (StdLemmas.BoolFTRaw h),
        S(b2) => StdLemmas.IdCongrRaw Nat Nat (λ (x : Nat). S x) a2 b2 (EqbTrueEq(a2, b2, h)) } } };

  -- P1: elim on A, inner elim on B per arm, self-call `Ih B2` in the S/S
  -- case only (no premise to carry).
  fn EqbSym [a] (a : Nat, b : Nat) -> Id Bool (Eqb a b) (Eqb b a) {
    match a {
      Z => match b { Z => Refl, S(b2) => Refl },
      S(a2) => match b { Z => Refl, S(b2) => EqbSym(a2, b2) } } };

  -- P2 (per dispatch note): Type-family/Bool-motive shape — B/T/F/G stay
  -- capital (comptime), splice the existing boolRec-based proof.
  fn IfDec (B : Bool, T : Type, F : Id Bool B True → T, G : Id Bool B False → T) -> T {
    StdLemmas.IfDecRaw B T F G };

  -- P2: the resize-ledger combinator (IfDec/NatRw dispatch on non-decreasing
  -- premises) — splice the existing checked proof.
  fn LedgerGrow (c : Nat, n : Nat, h1 : Le (S Z) c, hle : Le (StdLemmas.Mul 5 n) (StdLemmas.Mul 4 c)) ->
      Le (StdLemmas.Mul 5 (S n)) (StdLemmas.Mul 4 (StdLemmas.Mul 2 c)) {
    StdLemmas.LedgerGrowRaw c n h1 hle };

  ()
}

end Dllbc
