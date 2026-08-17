import Dllbc.Tests.HmProbeMod

/-!
# `HmProbeModCarve` — M4: an in-place write at the computed slot

`SlotWrite(h, n, v, Hne, slots)` writes `v` into slot `h % n` of an `n`-slot array,
in place, with the index bound and the carve decomposition both discharged.

The shape is forced, and the two forcings are the probe's real content.

**The capacity is an opaque `n` with `Hne : Le (S Z) n`, not the pattern `S c`.**
Premise (3) solves its equation by REFINING, and a refinement needs a σ on one
side; `S c` is a constructor applied to a σ, so the cited equation type-checks and
then has nowhere to go — verbatim, `Refl: both endpoints are rigid`.

**The index and the residue are minted across a CALL.** With `n` opaque the
equation is `n = add i (S r)`, and if `i` and `r` are computed comptime terms they
both mention `n` — verbatim, `Refl: occurs check — endpoint σ1 occurs in the other
endpoint`. `SlotOf` returns the pair as a `Σ`, the caller matches it, and §6.2's
opacity re-mints both as fresh binders. This is exactly the shape `partitionA`
already uses for `splitA`'s returned `k`/`r`, arrived at from the other direction.

After that the carve is free: the prefix carve cites `Hdec`, and the one-slot carve
at the newly-minted base needs no evidence at all, because its leaf-relative
obligation `Le 1 (S r)` computes to `⊤`.
-/

namespace Dllbc.Tests.HmProbeMod
open Dllbc
open Dllbc.StdLemmas (LeAdd)

def slotDecls : Term := prog{
  fn SlotOf (h : Nat, n : Nat, Hne : Le (S Z) n)
      -> Σ (i : Nat) → Σ (r : Nat) → Id Nat n (Add i (S r)) {
    Pair(Mod h n, ModDec (Mod h n) n (ModLtN h n Hne))
  };
  fn SlotWrite (h : Nat, n : Nat, v : Nat, Hne : Le (S Z) n,
                slots : &mut (Array n Nat)) -> Unit {
    let d = SlotOf(h, n, Hne);
    match d { Pair(i, d2) => match d2 { Pair(r, hd) => {
      let pre = &m (*slots)[Z ; i ; S r | LeAdd i (S r) | hd];
      let cell = &m (*slots)[i ; 1 ; r];
      (*cell)[0] := v;
      ()
    } } }
  };
  () }

example : progOk slotDecls = true := by native_decide

/-! ### …and it writes the RIGHT slot, executing -/

def natOfV : Nat → Val → Option Nat
  | f, v =>
    match Val.asCtor? v, f with
    | some ("Z", []), _ => some 0
    | some ("S", [w]), f' + 1 => (natOfV f' w).map (· + 1)
    | _, _ => none

def arrOfV : Val → Option (List Nat)
  | v => match Val.asCtor? v with
    | some ("Arr", vs) => vs.mapM (natOfV 4000)
    | _ => none

/-- Four zeroed slots; write `9` at `h % 4`; read the array back. `Hne : Le 1 4`
    computes to `⊤` at the literal, so the caller supplies `unit`. -/
def slotCaller (h : Nat) : Term := prog{
  fn SlotOf (h : Nat, n : Nat, Hne : Le (S Z) n)
      -> Σ (i : Nat) → Σ (r : Nat) → Id Nat n (Add i (S r)) {
    Pair(Mod h n, ModDec (Mod h n) n (ModLtN h n Hne))
  };
  fn SlotWrite (h : Nat, n : Nat, v : Nat, Hne : Le (S Z) n,
                slots : &mut (Array n Nat)) -> Unit {
    let d = SlotOf(h, n, Hne);
    match d { Pair(i, d2) => match d2 { Pair(r, hd) => {
      let pre = &m (*slots)[Z ; i ; S r | LeAdd i (S r) | hd];
      let cell = &m (*slots)[i ; 1 ; r];
      (*cell)[0] := v;
      ()
    } } }
  };
  let z = Arr(0, 0, 0, 0);
  let b = &m z;
  SlotWrite(%(Term.nat h), 4, 9, unit, b);
  let y = z;
  () }

def runSlot (h : Nat) : Option (List Nat) :=
  match runProgram (slotCaller h) with
  | .ok env => (env.lookup "y").bind arrOfV
  | .error _ => none

example : runSlot 0 == some [9, 0, 0, 0] := by native_decide
example : runSlot 1 == some [0, 9, 0, 0] := by native_decide
example : runSlot 6 == some [0, 0, 9, 0] := by native_decide
example : runSlot 7 == some [0, 0, 0, 9] := by native_decide

end Dllbc.Tests.HmProbeMod
