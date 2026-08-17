import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff
import Dllbc.Tests.Direct

/-!
# The hashmap flagship — `docs/13-hashmap-flagship.md`

A verified, resizable, in-place hashmap mirroring the Aeneas ICFP'22 case study
(`competitors/aeneas-hashmap/`). See the problem statement for the fixed layout, ops,
specs, and acceptance battery; this file is staged S1 (fixed-capacity, full specs) →
S2 (resize) → S3 (twins + differential + writeup).

## §0 — the ported arithmetic (`hm-probe-mod`, verified here against current `main`)

`Mod`/`Div`/`Mul` and the two lemmas a slot access needs (`ModLtN`, `ModDec`) now
live in `StdLemmas.lean`, ported verbatim from the probe. This section re-runs the
probe's own `chkL` checks against THIS tree, so a divergence between the probe's base
commit and current `main` is caught here rather than three ops downstream.
-/

open Dllbc
open Dllbc.StdLemmas (LeRefl LeTrans LeAdd LeAddL LeAddSucc LeRwL LeRwR AddSucc AddZero
  IdTrans IdCongr IdSym Znots LebTrueLe LebFalseGt LePredL EqbRefl EqbGtFalse EqbLtFalse
  NatRw
  NextR NextC NextQ ModC Mod DivC Div Mul StepInv StepInvTy ModCLt ModCLtTy
  ModLtN ModLtNTy ModDec ModDecTy
  OptP Opt Some None OptElim Entry Bucket LenE FindL
  AllKeysEq AllHashedA TotalLenA TotalLenACat OptElimAssoc FindArrA FindArrACat
  HMInv HashMapT FindHM SizeHM FindIns FindRem
  MkFillFn MkFillAllHashed MkFillTotalLen MkFillFind
  FalseNotTrue FalseNotTrueTy EqbTrueEq EqbTrueEqTy EqbSymm EqbSymmTy
  FindInsL CondBump CondBumpSucc CondBumpSuccTy
  BoolRw BoolRwTy BoolRecTrue BoolRecTrueTy BoolRecFalse BoolRecFalseTy)

namespace Dllbc.Tests.HmFlagship

/-- Type-check a closed term against a closed type in the pure seed (ArraySort's `chkL`). -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

def pv (t : Term) : Term := Pure.nf 4000000 t
def modOf (a b : Nat) : Term := pv prog{ Mod %(Term.nat a) %(Term.nat b) }
def divOf (a b : Nat) : Term := pv prog{ Div %(Term.nat a) %(Term.nat b) }

example : (modOf 7 3).natOf? == some 1 := by native_decide
example : (modOf 0 3).natOf? == some 0 := by native_decide
example : (divOf 7 3).natOf? == some 2 := by native_decide

-- The Aeneas hashmap's own `test1` keys at its own capacity: `0, 128, 1024, 1056`
-- all land in slot 0 of 32, which is what makes that test exercise the collision list.
example : (modOf 0 32).natOf? == some 0 := by native_decide
example : (modOf 128 32).natOf? == some 0 := by native_decide
example : (modOf 1024 32).natOf? == some 0 := by native_decide
example : (modOf 1056 32).natOf? == some 0 := by native_decide

example : chkL StepInv StepInvTy = true := by native_decide
example : chkL ModCLt ModCLtTy = true := by native_decide
example : chkL ModLtN ModLtNTy = true := by native_decide
example : chkL ModDec ModDecTy = true := by native_decide

/-! ## §0.5 — the Option/Entry/Bucket vocabulary, smoke-tested -/

example : chkL prog{ Some 5 } prog{ Opt Nat } = true := by native_decide
example : chkL None prog{ Opt Nat } = true := by native_decide
example : chkL prog{ Cons(Pair(3, 30), Cons(Pair(1, 10), Nil)) } Bucket = true := by
  native_decide

def bucketLit : Term := prog{ Cons(Pair(1, 10), Cons(Pair(3, 30), Nil)) }

example : (pv prog{ LenE %bucketLit }).natOf? == some 2 := by native_decide
example : (pv prog{ FindL 3 %bucketLit }).natOf? = none := by native_decide -- an Opt, not a Nat
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindL 3 %bucketLit) (Some 30) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindL 9 %bucketLit) None } = true := by
  native_decide
-- The wrong value is refused, so the two checks above are not vacuous.
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindL 3 %bucketLit) (Some 10) } = false := by
  native_decide

-- `OptElim`, both branches, at both a Lean-level check and a program use.
example : chkL prog{ OptElim (Some 5) Nat Z (λ (V : Nat). V) } prog{ Nat } = true := by
  native_decide
example : (pv prog{ OptElim (Some 5) Nat Z (λ (V : Nat). V) }).natOf? == some 5 := by
  native_decide
example : (pv prog{ OptElim None Nat 9 (λ (V : Nat). V) }).natOf? == some 9 := by
  native_decide

/-! ## §0.6 — well-hashedness, entry counting, and the whole-map fold, smoke-tested -/

def okSlots : Term := prog{ Arr(Nil, Cons(Pair(5, 7), Nil), Cons(Pair(1, 2), Cons(Pair(3, 4), Nil))) }
-- 3 slots, cap 3: slot 0 empty, slot 1 = [(5,7)] (5 mod 3 = 2 — WRONG on purpose below);
-- rebuilt so every entry really does hash to its own slot: 1 mod 3 = 1, 4 mod 3 = 1, 3 mod 3 = 0.
def okSlots2 : Term := prog{ Arr(Cons(Pair(3, 90), Nil), Cons(Pair(1, 20), Cons(Pair(4, 40), Nil)), Nil) }

-- `AllHashedA`'s witness is the nested Sigma-chain `arrRec`/`AllKeysEq` actually build:
-- one `Pair(Refl, …)` per entry, one `Pair(…, …)` per slot, `unit` at every Nil.
-- `cap = 2`: slot 0 = `[(2,90)]` (`2 mod 2 = 0`, matches its own slot), slot 1 = `[]`.
def hashOkSlots : Term := prog{ Arr(Cons(Pair(2, 90), Nil), Nil) }
example : chkL prog{ Pair(Pair(Refl, unit), Pair(unit, unit)) }
               prog{ AllHashedA 2 2 %hashOkSlots Z } = true := by native_decide
-- Not vacuous: `okSlots` puts a key-5 entry in slot 1, and `5 mod 3 = 2 ≠ 1` — no witness
-- of the RIGHT SHAPE exists, so even the correctly-shaped witness above is refused here.
example : chkL prog{ Pair(Pair(Refl, unit), Pair(unit, unit)) }
               prog{ AllHashedA 3 3 %okSlots Z } = false := by native_decide

example : (pv prog{ TotalLenA 3 %okSlots2 }).natOf? == some 3 := by native_decide
example : chkL OptElimAssoc prog{
    Π (O1 : Opt Nat) → Π (O2 : Opt Nat) → Π (D : Opt Nat) →
      Id (Opt Nat) (OptElim O1 (Opt Nat) (OptElim O2 (Opt Nat) D Some) Some)
                   (OptElim (OptElim O1 (Opt Nat) O2 Some) (Opt Nat) D Some) } = true := by
  native_decide
example : chkL TotalLenACat prog{
    Π (M : Nat) → Π (A : Array M Bucket) → Π (Kk : Nat) → Π (B : Array Kk Bucket) →
      Id Nat (TotalLenA (Add M Kk) (arrCat M Kk A B)) (Add (TotalLenA M A) (TotalLenA Kk B)) }
    = true := by native_decide
example : chkL FindArrACat prog{
    Π (Q : Nat) → Π (M : Nat) → Π (A : Array M Bucket) → Π (Kk : Nat) → Π (B : Array Kk Bucket) →
      Id (Opt Nat) (FindArrA Q (Add M Kk) (arrCat M Kk A B))
                   (OptElim (FindArrA Q M A) (Opt Nat) (FindArrA Q Kk B) Some) } = true := by
  native_decide

-- `FindArrA` really does scan every slot and find the entry.
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindArrA 4 3 %okSlots2) (Some 40) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindArrA 9 3 %okSlots2) None } = true := by
  native_decide

/-! ## §0.7 — a hand-packed `HashMap`, smoke-tested against `HashMapT`/`FindHM`/`SizeHM`

    `cap = 2`, one entry (key 2, value 90) in slot 0, slot 1 empty — `hashOkSlots`
    from §0.6, whose `AllHashedA` witness is already worked out there. `load` and the
    entry-count clause are checked by `Refl`, so `Div (Mul 2 4) 5` and `TotalLenA 2
    hashOkSlots` both have to compute to the literals below for the pack to check —
    the ONE place this section is not just replaying §0.6's witness. -/

def hmInvWitness : Term :=
  prog{ Pair(unit, Pair(Pair(Pair(Refl, unit), Pair(unit, unit)), Pair(Refl, Refl))) }
def hmExample : Term := prog{ Pair(2, Pair(1, Pair(1, Pair(%hashOkSlots, %hmInvWitness)))) }

example : chkL hmExample HashMapT = true := by native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindHM 2 %hmExample) (Some 90) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindHM 9 %hmExample) None } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id Nat (SizeHM %hmExample) 1 } = true := by native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindIns 5 5 70 %hmExample) (Some 70) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindIns 2 5 70 %hmExample) (Some 90) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindRem 2 2 %hmExample) None } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindRem 9 2 %hmExample) None } = true := by
  native_decide

/-! ## §1 — the program chain

    `hmChain` is `ArraySort`'s `arrUnder`: one function taking the tail to splice, so
    every `fn` below is in scope for every one after it and the whole thing is ONE
    program with no table. Ops are added here one milestone at a time; `New` first,
    since it needs the least new machinery. -/

def NewRet : Term := prog{
  Σ0 (result : HashMapT).
    (Π (Q : Nat) → Id (Opt Nat) (FindHM Q result) None) × Id Nat (SizeHM result) Z }

/-! ## §1.6 — `InsertInList`'s four supporting lemmas

    Bare `λ`/`elim` (StdLemmas' own style), NOT `fn`+`if` — a hard-won finding, not a
    style preference. `if`/`match`'s named equation is real (confirmed: a borrow-free
    `fn` using `if` gets a genuinely citable hypothesis, unlike a bare `elim` arm) —
    but the CHECKER'S "audit" step, which comptime-evaluates an `fn`'s return value to
    verify it, cannot reduce THROUGH an `if`/`match` construct at all ("match not
    implemented in the comptime fragment this milestone"), and that failure surfaces
    the moment the returned value is built from `j`-based rewriting (`NatRw`,
    `BoolRecTrue`/`False`, …) keyed to the `if`'s own equation — REGARDLESS of whether
    that rewriting sits directly in the `if`'s branch or is factored into a separately
    named pure function the branch merely calls. Four independent constructions were
    tried and four independent ways failed the SAME audit; only dropping `if`
    entirely closed it.

    The needed replacement — a genuinely citable "we are in this arm" equation from a
    BARE `elim`, with no `if` anywhere — turns out to already be in this file:
    `OptElimAssoc`/`BoolRecTrue`/`BoolRecFalse`'s own trick. Thread the equation
    through the motive as a `Π`, and supply `Refl : Id A X X` (always valid, even at
    a symbolic `X`) as the elim's OWN tail argument; within each arm the motive has
    already specialised that `Π`'s domain to the concrete constructor, so the arm's
    own bound variable IS the citable equation. `InsRecurseEq`'s True arm needs this
    twice over (nested `elim`, each with its own `Refl`-fed `Π`-motive) to derive `Q =
    Key` from `Eqb Q Key = True` and use it against `Hne`. -/

def InsFoundEq : Term := prog{
  λ (Kk0 : Nat). λ (Key : Nat). λ (V : Nat). λ (Vv0 : Nat). λ (Tl0 : Bucket).
  λ (HeqKey : Id Nat Kk0 Key). λ (Q : Nat).
    NatRw (λ (X : Nat). Id (Opt Nat) (FindL Q Cons(Pair(X, V), Tl0)) (FindInsL Q Key V Cons(Pair(X, Vv0), Tl0)))
      Key Kk0 (IdSym Nat Kk0 Key HeqKey)
      (elim (Eqb Q Key) return (λ (Bz : Bool).
          Id (Opt Nat) (boolRec (λ (W : Bool). Σ (b : Bool). OptP b Nat) (Some V) (FindL Q Tl0) Bz)
                       (boolRec (λ (W : Bool). Σ (b : Bool). OptP b Nat) (Some V)
                          (boolRec (λ (W : Bool). Σ (b : Bool). OptP b Nat) (Some Vv0) (FindL Q Tl0) Bz) Bz)) {
        True => Refl,
        False => Refl
      }) }
def InsFoundEqTy : Term := prog{
  Π (Kk0 : Nat) → Π (Key : Nat) → Π (V : Nat) → Π (Vv0 : Nat) → Π (Tl0 : Bucket) →
    Π (HeqKey : Id Nat Kk0 Key) → Π (Q : Nat) →
      Id (Opt Nat) (FindL Q Cons(Pair(Kk0, V), Tl0)) (FindInsL Q Key V Cons(Pair(Kk0, Vv0), Tl0)) }

def InsFoundLen : Term := prog{
  λ (Kk0 : Nat). λ (Key : Nat). λ (V : Nat). λ (Vv0 : Nat). λ (Tl0 : Bucket).
  λ (HeqKey : Id Nat Kk0 Key).
    NatRw (λ (X : Nat). Id Nat (LenE Cons(Pair(X, V), Tl0))
             (CondBump (FindL Key Cons(Pair(X, Vv0), Tl0)) (LenE Cons(Pair(X, Vv0), Tl0))))
      Key Kk0 (IdSym Nat Kk0 Key HeqKey)
      (IdCongr (Opt Nat) Nat (λ (O : Opt Nat). CondBump O (LenE Cons(Pair(Key, Vv0), Tl0)))
        (Some Vv0) (FindL Key Cons(Pair(Key, Vv0), Tl0))
        (IdSym (Opt Nat) (FindL Key Cons(Pair(Key, Vv0), Tl0)) (Some Vv0)
          (BoolRecTrue (Some Vv0) (FindL Key Tl0) (Eqb Key Key) (EqbRefl Key)))) }
def InsFoundLenTy : Term := prog{
  Π (Kk0 : Nat) → Π (Key : Nat) → Π (V : Nat) → Π (Vv0 : Nat) → Π (Tl0 : Bucket) →
    Π (HeqKey : Id Nat Kk0 Key) →
      Id Nat (LenE Cons(Pair(Kk0, V), Tl0))
        (CondBump (FindL Key Cons(Pair(Kk0, Vv0), Tl0)) (LenE Cons(Pair(Kk0, Vv0), Tl0))) }

def InsRecurseEq : Term := prog{
  λ (Kk0 : Nat). λ (Vv0 : Nat). λ (Key : Nat). λ (V : Nat). λ (Old : Bucket). λ (New : Bucket).
  λ (Hne : Id Bool (Eqb Kk0 Key) False).
  λ (Hp : Π (Q : Nat) → Id (Opt Nat) (FindL Q New) (FindInsL Q Key V Old)).
  λ (Q : Nat).
    elim (Eqb Q Key) return (λ (Bz1 : Bool). Π (H1 : Id Bool (Eqb Q Key) Bz1) →
        Id (Opt Nat) (FindL Q Cons(Pair(Kk0, Vv0), New)) (FindInsL Q Key V Cons(Pair(Kk0, Vv0), Old))) {
      True => λ (H1 : Id Bool (Eqb Q Key) True).
        (λ (HQKey : Id Nat Q Key).
        (λ (HKeyKk0False : Id Bool (Eqb Key Kk0) False).
        (λ (HQKk0False : Id Bool (Eqb Q Kk0) False).
        IdTrans (Opt Nat) (FindL Q Cons(Pair(Kk0, Vv0), New)) (Some V) (FindInsL Q Key V Cons(Pair(Kk0, Vv0), Old))
          (IdTrans (Opt Nat) (FindL Q Cons(Pair(Kk0, Vv0), New)) (FindL Q New) (Some V)
            (BoolRecFalse (Some Vv0) (FindL Q New) (Eqb Q Kk0) HQKk0False)
            (IdTrans (Opt Nat) (FindL Q New) (FindInsL Q Key V Old) (Some V)
              (Hp Q) (BoolRecTrue (Some V) (FindL Q Old) (Eqb Q Key) H1)))
          (IdSym (Opt Nat) (FindInsL Q Key V Cons(Pair(Kk0, Vv0), Old)) (Some V)
            (BoolRecTrue (Some V) (FindL Q Cons(Pair(Kk0, Vv0), Old)) (Eqb Q Key) H1)))
        (NatRw (λ (X : Nat). Id Bool (Eqb X Kk0) False) Key Q (IdSym Nat Q Key HQKey) HKeyKk0False))
        (IdTrans Bool (Eqb Key Kk0) (Eqb Kk0 Key) False (EqbSymm Key Kk0) Hne))
        (EqbTrueEq Q Key H1),
      False => λ (H1 : Id Bool (Eqb Q Key) False).
        elim (Eqb Q Kk0) return (λ (Bz2 : Bool). Π (H2 : Id Bool (Eqb Q Kk0) Bz2) →
            Id (Opt Nat) (FindL Q Cons(Pair(Kk0, Vv0), New)) (FindInsL Q Key V Cons(Pair(Kk0, Vv0), Old))) {
          True => λ (H2 : Id Bool (Eqb Q Kk0) True).
            IdTrans (Opt Nat) (FindL Q Cons(Pair(Kk0, Vv0), New)) (Some Vv0) (FindInsL Q Key V Cons(Pair(Kk0, Vv0), Old))
              (BoolRecTrue (Some Vv0) (FindL Q New) (Eqb Q Kk0) H2)
              (IdSym (Opt Nat) (FindInsL Q Key V Cons(Pair(Kk0, Vv0), Old)) (Some Vv0)
                (IdTrans (Opt Nat) (FindInsL Q Key V Cons(Pair(Kk0, Vv0), Old)) (FindL Q Cons(Pair(Kk0, Vv0), Old)) (Some Vv0)
                  (BoolRecFalse (Some V) (FindL Q Cons(Pair(Kk0, Vv0), Old)) (Eqb Q Key) H1)
                  (BoolRecTrue (Some Vv0) (FindL Q Old) (Eqb Q Kk0) H2))),
          False => λ (H2 : Id Bool (Eqb Q Kk0) False).
            IdTrans (Opt Nat) (FindL Q Cons(Pair(Kk0, Vv0), New)) (FindL Q Old) (FindInsL Q Key V Cons(Pair(Kk0, Vv0), Old))
              (IdTrans (Opt Nat) (FindL Q Cons(Pair(Kk0, Vv0), New)) (FindL Q New) (FindL Q Old)
                (BoolRecFalse (Some Vv0) (FindL Q New) (Eqb Q Kk0) H2)
                (IdTrans (Opt Nat) (FindL Q New) (FindInsL Q Key V Old) (FindL Q Old)
                  (Hp Q) (BoolRecFalse (Some V) (FindL Q Old) (Eqb Q Key) H1)))
              (IdSym (Opt Nat) (FindInsL Q Key V Cons(Pair(Kk0, Vv0), Old)) (FindL Q Old)
                (IdTrans (Opt Nat) (FindInsL Q Key V Cons(Pair(Kk0, Vv0), Old)) (FindL Q Cons(Pair(Kk0, Vv0), Old)) (FindL Q Old)
                  (BoolRecFalse (Some V) (FindL Q Cons(Pair(Kk0, Vv0), Old)) (Eqb Q Key) H1)
                  (BoolRecFalse (Some Vv0) (FindL Q Old) (Eqb Q Kk0) H2)))
        } Refl
    } Refl }
def InsRecurseEqTy : Term := prog{
  Π (Kk0 : Nat) → Π (Vv0 : Nat) → Π (Key : Nat) → Π (V : Nat) → Π (Old : Bucket) → Π (New : Bucket) →
  Π (Hne : Id Bool (Eqb Kk0 Key) False) →
  Π (Hp : Π (Q : Nat) → Id (Opt Nat) (FindL Q New) (FindInsL Q Key V Old)) →
  Π (Q : Nat) →
    Id (Opt Nat) (FindL Q Cons(Pair(Kk0, Vv0), New)) (FindInsL Q Key V Cons(Pair(Kk0, Vv0), Old)) }

def InsRecurseLen : Term := prog{
  λ (Kk0 : Nat). λ (Vv0 : Nat). λ (Key : Nat). λ (Old : Bucket). λ (New : Bucket).
  λ (Hne : Id Bool (Eqb Kk0 Key) False).
  λ (Hlen2 : Id Nat (LenE New) (CondBump (FindL Key Old) (LenE Old))).
    (λ (HKeyKk0False : Id Bool (Eqb Key Kk0) False).
    IdTrans Nat (LenE Cons(Pair(Kk0, Vv0), New)) (S (LenE New))
      (CondBump (FindL Key Cons(Pair(Kk0, Vv0), Old)) (LenE Cons(Pair(Kk0, Vv0), Old)))
      Refl
      (IdTrans Nat (S (LenE New)) (S (CondBump (FindL Key Old) (LenE Old)))
        (CondBump (FindL Key Cons(Pair(Kk0, Vv0), Old)) (LenE Cons(Pair(Kk0, Vv0), Old)))
        (IdCongr Nat Nat (λ (N : Nat). S N) (LenE New) (CondBump (FindL Key Old) (LenE Old)) Hlen2)
        (IdTrans Nat (S (CondBump (FindL Key Old) (LenE Old))) (CondBump (FindL Key Old) (S (LenE Old)))
          (CondBump (FindL Key Cons(Pair(Kk0, Vv0), Old)) (LenE Cons(Pair(Kk0, Vv0), Old)))
          (CondBumpSucc (FindL Key Old) (LenE Old))
          (IdCongr (Opt Nat) Nat (λ (O : Opt Nat). CondBump O (S (LenE Old)))
            (FindL Key Old) (FindL Key Cons(Pair(Kk0, Vv0), Old))
            (IdSym (Opt Nat) (FindL Key Cons(Pair(Kk0, Vv0), Old)) (FindL Key Old)
              (BoolRecFalse (Some Vv0) (FindL Key Old) (Eqb Key Kk0) HKeyKk0False))))))
    (IdTrans Bool (Eqb Key Kk0) (Eqb Kk0 Key) False (EqbSymm Key Kk0) Hne) }
def InsRecurseLenTy : Term := prog{
  Π (Kk0 : Nat) → Π (Vv0 : Nat) → Π (Key : Nat) → Π (Old : Bucket) → Π (New : Bucket) →
  Π (Hne : Id Bool (Eqb Kk0 Key) False) →
  Π (Hlen2 : Id Nat (LenE New) (CondBump (FindL Key Old) (LenE Old))) →
    Id Nat (LenE Cons(Pair(Kk0, Vv0), New))
      (CondBump (FindL Key Cons(Pair(Kk0, Vv0), Old)) (LenE Cons(Pair(Kk0, Vv0), Old))) }

/-! ## §1.6.1 — a checker finding: `InsFoundEq`/`InsFoundLen` must be INLINED, not called

    `InsertInList`'s Found branch needs `HeqKey : Id Nat Kk0 key`, built from the `if`'s
    own `e : Id Bool (Eqb Kk0 key) True` via `EqbTrueEq`, then fed to `NatRw`. Measured:
    that construction, when it CROSSES A FUNCTION-CALL BOUNDARY (i.e. `HeqKey` is
    computed and then handed to a SEPARATELY-DEFINED `InsFoundEq`), fails the checker's
    audit at the `Opt Nat`/`Bucket` types — but the IDENTICAL construction, written
    INLINE in the `if`'s own branch (no call boundary), is accepted. Isolated by binary
    search across a dozen minimal probes: neither `if` alone, nor `NatRw` alone, nor
    complex types alone reproduce it — only `EqbTrueEq(if-derived e)` flowing into a
    CALLEE's own `NatRw` at the `Opt Nat` type does. `InsRecurseEq`/`InsRecurseLen` do
    NOT need this treatment: their own `Hne` parameter is the `if`'s `e` PASSED
    THROUGH UNCHANGED (`Id Bool (Eqb Kk0 key) False`, no `EqbTrueEq`/`NatRw` bridge at
    the call site), and a plain pass-through argument crosses the boundary fine —
    confirmed by a dedicated probe. So `InsertInList` below inlines `InsFoundEq`'s and
    `InsFoundLen`'s BODIES (their standalone forms above remain as the checked
    specification of what the inlined code must equal) and calls `InsRecurseEq`/
    `InsRecurseLen` normally. -/

def hmChain (rest : Term) : Term := prog{
  fn New (cap : Nat, Hcap : Le (S Z) cap) -> %NewRet {
    Pair(
      Pair(cap, Pair(Div (Mul cap 4) 5, Pair(Z,
        Pair(MkFillFn cap,
          Pair(Hcap, Pair(MkFillAllHashed cap cap Z, Pair(MkFillTotalLen cap, Refl))))))),
      Pair(λ (Q : Nat). MkFillFind cap Q, Refl))
  };

  fn InsertInList [fuel] (fuel : Nat, key : Nat, val : Nat, b : &mut Bucket,
                          Hf : Le (LenE (*b)) fuel)
      -> Σ0 (Hp : Π (Q : Nat) → Id (Opt Nat) (FindL Q (*b)) (FindInsL Q key val (old *b))).
           Id Nat (LenE (*b)) (CondBump (FindL key (old *b)) (LenE (old *b))) {
    match b {
      Nil => {
        *b := Cons(Pair(key, val), Nil);
        Pair(λ (Q : Nat). Refl, Refl)
      },
      Cons(hd, tl) => match fuel {
        Z => botElim Unit Hf,
        S(f2) => match hd {
          Pair(kk, vv) => {
            let Kk0 = *kk;
            if e : Eqb Kk0 key {
              let Vv0 = *vv;
              let Tl0 = *tl;
              *vv := val;
              Pair(
                λ (Q : Nat).
                  NatRw (λ (X : Nat). Id (Opt Nat) (FindL Q Cons(Pair(X, val), Tl0))
                           (FindInsL Q key val Cons(Pair(X, Vv0), Tl0)))
                    key Kk0 (IdSym Nat Kk0 key (EqbTrueEq Kk0 key e))
                    (elim (Eqb Q key) return (λ (Bz : Bool). Id (Opt Nat)
                        (boolRec (λ (W : Bool). Σ (b : Bool). OptP b Nat) (Some val) (FindL Q Tl0) Bz)
                        (boolRec (λ (W : Bool). Σ (b : Bool). OptP b Nat) (Some val)
                           (boolRec (λ (W : Bool). Σ (b : Bool). OptP b Nat) (Some Vv0) (FindL Q Tl0) Bz) Bz)) {
                      True => Refl,
                      False => Refl
                    }),
                NatRw (λ (X : Nat). Id Nat (LenE Cons(Pair(X, val), Tl0))
                         (CondBump (FindL key Cons(Pair(X, Vv0), Tl0)) (LenE Cons(Pair(X, Vv0), Tl0))))
                  key Kk0 (IdSym Nat Kk0 key (EqbTrueEq Kk0 key e))
                  (IdCongr (Opt Nat) Nat (λ (O : Opt Nat). CondBump O (LenE Cons(Pair(key, Vv0), Tl0)))
                    (Some Vv0) (FindL key Cons(Pair(key, Vv0), Tl0))
                    (IdSym (Opt Nat) (FindL key Cons(Pair(key, Vv0), Tl0)) (Some Vv0)
                      (BoolRecTrue (Some Vv0) (FindL key Tl0) (Eqb key key) (EqbRefl key)))))
            } else {
              let Tl0 = *tl;
              let Pair(Hp2, Hlen2) = InsertInList(f2, key, val, &m *tl, Hf);
              Pair(λ (Q : Nat). %InsRecurseEq Kk0 (*vv) key val Tl0 (*tl) e Hp2 Q,
                   %InsRecurseLen Kk0 (*vv) key Tl0 (*tl) e Hlen2)
            }
          }
        }
      }
    }
  };
  %rest }

def hmChainClosed : Term := hmChain prog{ () }
example : progOk hmChainClosed = true := by native_decide

/-! ## §1.8 — `InsertInList`, executing

    `Aeneas`'s own `insert_in_list` behaviour, on a concrete bucket: overwrite an
    existing key's value in place, or append a fresh entry at the end (`Nil` refill). -/

def natOfV2 : Nat → Val → Option Nat
  | f, v =>
    match Val.asCtor? v, f with
    | some ("Z", []), _ => some 0
    | some ("S", [w]), f' + 1 => (natOfV2 f' w).map (· + 1)
    | _, _ => none

def entriesOfV2 : Nat → Val → Option (List (Nat × Nat))
  | f, v =>
    match Val.asCtor? v, f with
    | some ("Nil", []), _ => some []
    | some ("Cons", [h, t]), f' + 1 =>
      match Val.asCtor? h, entriesOfV2 f' t with
      | some ("Pair", [a, b]), some xs =>
        match natOfV2 2000 a, natOfV2 2000 b with
        | some k, some v => some ((k, v) :: xs)
        | _, _ => none
      | _, _ => none
    | _, _ => none

def entryTermsOf : List (Nat × Nat) → Term
  | [] => prog{ Nil }
  | (k, v) :: t => prog{ Cons(Pair(%(Term.nat k), %(Term.nat v)), %(entryTermsOf t)) }

def insertInListCaller (entries : List (Nat × Nat)) (key val fuel : Nat) : Term :=
  hmChain prog{
    let z = %(entryTermsOf entries);
    let b = &m z;
    InsertInList(%(Term.nat fuel), %(Term.nat key), %(Term.nat val), b, unit);
    let y = z;
    () }

def runInsertInList (entries : List (Nat × Nat)) (key val fuel : Nat) : Option (List (Nat × Nat)) :=
  match Dllbc.Tests.S9Diff.runExec (insertInListCaller entries key val fuel) with
  | .ok env => (env.lookup "y").bind (entriesOfV2 2000)
  | .error _ => none

-- Overwrite an existing key (found at the head).
example : runInsertInList [(1, 10), (3, 30)] 1 99 2 == some [(1, 99), (3, 30)] := by
  native_decide
-- Overwrite an existing key found DEEPER in the walk (exercises the recurse branch).
example : runInsertInList [(1, 10), (3, 30)] 3 99 2 == some [(1, 10), (3, 99)] := by
  native_decide
-- A fresh key appends at the end (the Nil refill, reached via the recurse branch).
example : runInsertInList [(1, 10), (3, 30)] 5 50 2 == some [(1, 10), (3, 30), (5, 50)] := by
  native_decide
-- An empty bucket.
example : runInsertInList [] 5 50 0 == some [(5, 50)] := by native_decide

/-! ## §1.5 — `insert_in_list`'s arithmetic toolkit, smoke-tested -/

example : chkL EqbTrueEq EqbTrueEqTy = true := by native_decide
example : chkL EqbSymm EqbSymmTy = true := by native_decide
example : chkL CondBumpSucc CondBumpSuccTy = true := by native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindInsL 3 3 70 %bucketLit) (Some 70) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindInsL 9 3 70 %bucketLit) (FindL 9 %bucketLit) }
    = true := by native_decide
example : (pv prog{ CondBump None 5 }).natOf? == some 6 := by native_decide
example : (pv prog{ CondBump (Some 1) 5 }).natOf? == some 5 := by native_decide
example : chkL BoolRw BoolRwTy = true := by native_decide
example : chkL BoolRecTrue BoolRecTrueTy = true := by native_decide
example : chkL BoolRecFalse BoolRecFalseTy = true := by native_decide

/-! ## §1.7 — `InsertInList`'s four supporting lemmas, verified against their types

    Each is `if`-free (bare `elim`, the `OptElimAssoc` trick for the two that need a
    genuinely citable branch equation) — see the note above `InsFoundEq` for why. -/

example : chkL InsFoundEq InsFoundEqTy = true := by native_decide
example : chkL InsFoundLen InsFoundLenTy = true := by native_decide
example : chkL InsRecurseEq InsRecurseEqTy = true := by native_decide
example : chkL InsRecurseLen InsRecurseLenTy = true := by native_decide

end Dllbc.Tests.HmFlagship
