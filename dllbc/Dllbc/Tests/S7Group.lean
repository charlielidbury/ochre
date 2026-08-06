import Dllbc.Program
import Dllbc.ProgMacro

/-!
# §6.1 test suite — entangled calls and loan groups

Some functions break the wire correspondence: `choose` returns a borrow into
`x` OR `y` depending on a runtime bool, so no per-loan promise can say where a
written value lands. A call mints a **loan group** tying the loans it captured
to the borrows it issued, and the ending discipline is the group's whole
content — every issued borrow ends first, then the group ends atomically,
releasing each captured loan. The ordering *is* the soundness argument: a
captured owner cannot recover while an issued borrow lives.

The headline is the pair: the opaque group **forgets** (choose → distinct
fresh σ's; `z = 7` is not provable, and that is the cost, §6.2), while the
identity wire **remembers** (through → the owner recovers the written value).
M5/M6's wires are now the degenerate `issued = []` group.
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.S7Group

/-! ## `choose`: the entangled call -/

-- choose (c : Bool, x : &mut Nat, y : &mut Nat) → &mut Nat = match c { … }.
-- The callee checks under the borrow-returning audit: each branch consumes one
-- argument borrow into the result (exempt) and audits the other.
def choose : Term := prog{
  fn choose (c : Bool, x : &mut Nat, y : &mut Nat) -> &mut Nat
    { match c { True => x, False => y } };
  () }

example : progOk choose = true := by native_decide

-- The §6.1 trace verbatim. After `*r := 7`, demanding `a` (via `let z = a`)
-- forces the cascade: End ℓᵣ first (its 7 surrendered and DISCARDED — the
-- ordering as soundness, r ↦ ⊥ and 7 never reaches a or b), then the group
-- ends ATOMICALLY (b's fresh existential arrives too, though only a was
-- demanded). a and b hold DISTINCT fresh σ's; z holds a's. The imprecision is
-- the point: z = 7 is not provable (§6.2's cost).
def chooseCaller : Term := prog{
  fn choose (c : Bool, x : &mut Nat, y : &mut Nat) -> &mut Nat
    { match c { True => x, False => y } };
  let a = 0; let b = 0; let pa = &mut a; let pb = &mut b;
  let r = choose(True, pa, pb);
  *r := 7;
  let z = a;
  () }

-- `let z = a` ends the group (fresh existentials for a and b) and then COPIES
-- a's existential (§2.1), so a and z share it; canonicalization numbers a's σ
-- first (it now appears in a's own slot), b's second.
example : tailEnv chooseCaller
  [("a", .sym 0), ("b", .sym 1), ("pa", .bot), ("pb", .bot), ("r", .bot), ("z", .sym 0)]
  = true := by native_decide

/-! ## A single-borrow wire is opaque too (no signature-driven precision) -/

-- through (b : &mut List Nat) → &mut List Nat = b. It shares its SIGNATURE with
-- an `advance` that returns a field reborrow of the tail — signature-only
-- checking cannot tell them apart, so constraining the captured release to the
-- surrendered payload would be UNSOUND. Every opaque group therefore releases
-- a fresh existential: the caller below recovers a FRESH σ : List Nat, NOT the
-- written `Cons 9 Nil`. Precision is deliberately lost; §6.2's transparent/spec
-- group ends are the recovery route.
def through : Term := prog{ fn through (b : &mut List Nat) -> &mut List Nat { b }; () }

example : progOk through = true := by native_decide

def throughCaller : Term := prog{
  fn through (b : &mut List Nat) -> &mut List Nat { b };
  let x = Cons(1, Nil); let b = &mut x;
  let r = through(b);
  *r := Cons(9, Nil);
  let y = x;
  () }

-- y is a fresh σ (the write is forgotten — deliberate, per the soundness fix).
-- `x`'s recovered σ is typed `List Nat` (DATA), so reading it MOVES it (§2.1).
example : tailEnv throughCaller
  [("x", .bot), ("b", .bot), ("r", .bot), ("y", .sym 0)] = true := by native_decide

/-- …and the pair that keeps the loss honest: the EXECUTING machine still writes
    the value and still hands `Cons(9, Nil)` back to the owner. What opacity removes
    is the CHECKER's ability to know it — §5 point 4, a fact about what was ascribed
    and never about what happens.

    Moved here from `S17Spec` when that file retired (M28 D7). §17 was the
    declared-backward-spec suite, where a `through` carrying `back = λ r. r` let the
    caller recover the written value in CHECKING mode; M27 deleted the mechanism, and
    what was left of that section was this file's own opacity claim plus this
    executing counterpart, which this file did not have. -/
def vlist9 : Val := .ctor "Cons" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S"
  [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "Z" []]]]]]]]]], .ctor "Nil" []]
example : (match runProgram throughCaller with
  | .ok env => env.lookup "y" == some vlist9
  | .error _ => false) = true := by native_decide

/-! ## Rejections -/

-- The group cannot end because an issued borrow cannot surrender: `*r` was
-- taken, leaving its payload a hole (⊥), and then a captured owner is demanded.
example : progRejects (prog{
  fn choose (c : Bool, x : &mut Nat, y : &mut Nat) -> &mut Nat
    { match c { True => x, False => y } };
  let a = 0; let b = 0; let pa = &mut a; let pb = &mut b;
  let r = choose(True, pa, pb);
  let tk = *r;
  let z = a;
  () })
  "nothing surrendered" = true := by native_decide

-- A borrow-returning body whose returned payload fails its owed type:
-- `bad (b : &mut Nat) → &mut Bool = b` returns a Nat borrow as a Bool borrow.
example : progRejects (prog{ fn bad (b : &mut Nat) -> &mut Bool { b }; () })
  "owed type" = true := by native_decide

/-! ## The constrained branch, retired with its rule (M28 τ)

    A hand-built `constrained` group used to be handed to `endGroup` directly, to
    drive the one branch no call could reach: the identity wire, where a captured
    owner recovers the issued borrow's SURRENDERED payload instead of a fresh
    existential. It was kept so the branch was not dead-untested.

    The branch is gone, so there is nothing to test. Inferring that wire from a
    signature is unsound — `through` and `advance` share one and differ in exactly
    what it would claim, which is this file's own §6.1 headline — and the flag that
    forced it on existed only to validate the differential. That validation is now
    stated at the comparator (`S9Diff`), so the kernel no longer carries a case for
    a rule it does not have. -/

end Dllbc.Tests.S7Group
