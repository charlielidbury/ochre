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

def hmChain (rest : Term) : Term := prog{
  fn New (cap : Nat, Hcap : Le (S Z) cap) -> %NewRet {
    Pair(
      Pair(cap, Pair(Div (Mul cap 4) 5, Pair(Z,
        Pair(MkFillFn cap,
          Pair(Hcap, Pair(MkFillAllHashed cap cap Z, Pair(MkFillTotalLen cap, Refl))))))),
      Pair(λ (Q : Nat). MkFillFind cap Q, Refl))
  };
  %rest }

def hmChainClosed : Term := hmChain prog{ () }
example : progOk hmChainClosed = true := by native_decide

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

end Dllbc.Tests.HmFlagship
