import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff

/-!
# Target ledger for the borrow re-founding

This file is a target ledger for the borrow re-founding milestone, not an
ordinary test suite: every program below is a `def`. The live assertions pin
what is true today, and the assertions commented out and marked `TARGET` are
what the milestone must make true. When a `TARGET` lands, it goes live, and any
`TODAY` assertion it contradicts moves or is removed.

Three goal families:

  * **(a)** `split_at_mut` as an ordinary library function returning a pair of
    borrows.
  * **(b)** the get_mut round-trip law: whatever the caller writes through a
    returned cursor is still there the next time it gets. The executing
    machine already keeps this; the checker forgets it, and the assertions
    below pin the gap from both sides.
  * **(c)** the read-only borrow law: a returned borrow whose debt is the
    identity is read-only, and the container's own identity then follows.

Design: `docs/12-design-borrow-refounding.md`. The pin surface used in the
`TARGET` signatures below: `~> S = e` attaches a pin `e` to a container's owed
type `S`, and `*res` names the issued borrow's exit payload inside that pin.
-/

open Dllbc
-- `StdLemmas.Set` is the list update the get_mut pin is written against.
-- Opening it selectively keeps Lean's own `Set` unshadowed elsewhere.
open Dllbc.StdLemmas (Set NthL)

namespace Dllbc.Tests.BorrowRefoundGoals

/-! ## Reading helpers -/

def vnat : Nat → Val | 0 => .ctor "Z" [] | n + 1 => .ctor "S" [vnat n]
def vlist : List Nat → Val | [] => .ctor "Nil" [] | h :: t => .ctor "Cons" [vnat h, vlist t]

/-- What the executing machine leaves in `y`, as opposed to the checker's
answer, which is `tailEnv`'s. -/
def runY (t : Term) : Option Val :=
  match Dllbc.Tests.S9Diff.runExec t with
  | .ok env => env.lookup "y"
  | .error _ => none

/-! ## (b) The get_mut round-trip law

    Whatever the caller writes through a `get_mut` borrow should still be there
    the next time it gets. Stated over a list first, so the container's theory
    is one `NthL`/`Set` pair rather than a hashmap's.

    The cursor is `Nth`, a bounds-proof function returning a `&mut Nat` into a
    list. The target adds a claim on its parameter:

    ```
    TARGET signature (does not parse today — design doc D1, D3):

      fn Nth [i] (v : &mut (s : List Nat ~> List Nat = Set i (*res) s),
                  i : Nat, p : Le (S i) (Len *v)) -> &mut Nat
    ```

    Read: when `v`'s loan ends, its payload is the entry list with position `i`
    replaced by whatever came back through the returned borrow; `*res` names
    that borrow's exit payload.

    The callee must fill this hole on both branches:

      * `Z`:    the payload is `Cons (loan ℓ_hd) tl`; filling the hole gives
                `Cons σ_res tl`, and the pin `Set Z σ_res (Cons hd tl)` reduces
                to exactly that.
      * `S(k)`: the payload is `Cons hd (loan ℓ_tl)`, with `ℓ_tl` in the
                recursive call's own group, whose pin projects to
                `Set k σ_res tl_entry`; the outer pin
                `Set (S k) σ_res (Cons hd tl)` reduces to
                `Cons hd (Set k σ_res tl)`, matching it.

    Both legs are definitional on `StdLemmas.Set` as written: it recurses on
    the index first, so `Set (S k) v (Cons h t)` reduces to
    `Cons h (Set k v t)`, and `Set Z v (Cons h t)` reduces to `Cons v t`. -/

def withNth (rest : Term) : Term := prog{
  fn Nth [i] (v : &mut List Nat, i : Nat, p : Le (S i) (Len *v)) -> &mut Nat {
    match v {
      Nil => botElim Unit p,
      Cons(hd, tl) => match i {
        Z => &m *hd,
        S(k) => Nth(&m *tl, k, p)
      }
    } };
  %rest }

example : progOk (withNth prog defer_check { () }) = true := by native_decide

/-- The round trip: get position 1, write 9 through it, end the group, read the list. -/
def getMutRoundTrip : Term := withNth prog defer_check {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = Nth(b, 1, ());
  *r := 9;
  let y = x;
  () }

example : progOk getMutRoundTrip = true := by native_decide

-- TODAY: the checker hands `y` a fresh existential — the write through `r` is
-- forgotten. `x` is `⊥` (moved into `y`), and `y` is unconstrained at `List Nat`.
example : tailEnv getMutRoundTrip
  [("x", .bot), ("b", .bot), ("r", .bot), ("y", .sym 0)] = true := by native_decide

-- The executing machine does the right thing, which is what makes this a gap in
-- the checker rather than a real disagreement: opacity is a fact about what was
-- promised, not about what actually happens.
example : runY getMutRoundTrip == some (vlist [1, 9, 3]) := by native_decide

/-! TARGET. With the pin on `Nth`'s parameter, the checker knows the same thing:
    `y ≡ Set 1 9 (Cons 1 (Cons 2 (Cons 3 Nil))) ⇝ Cons 1 (Cons 9 (Cons 3 Nil))`.
    The release is no longer an existential, so the `tailEnv` above moves from a
    `.sym` to the concrete list.

    TARGET (uncomment when the milestone lands; the `TODAY` tailEnv above moves):

    example : tailEnv getMutRoundTrip
      [("x", .bot), ("b", .bot), ("r", .bot), ("y", vlist [1, 9, 3])] = true := by native_decide

    This assertion is live further below, on `getMutRoundTripPin` — the pin is
    per-signature, so the flip happens on the pinned twin, and the unpinned
    `tailEnv` above stays as the permanent statement that opacity is the default.
-/

/-- The same law one level deeper: `Nth` reaches position 1 through its own
    recursive call, so this exercises the recursive projection (`S(k)`) rather
    than the base case. Separated from `getMutRoundTrip` because if the pin
    composes at `i = 0` but not at `i = 1`, the mechanism is shallow rather than
    the general law. -/
def getMutRoundTripHead : Term := withNth prog defer_check {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = Nth(b, 0, ());
  *r := 7;
  let y = x;
  () }

example : progOk getMutRoundTripHead = true := by native_decide
example : runY getMutRoundTripHead == some (vlist [7, 2, 3]) := by native_decide

-- TARGET: y ≡ Cons(7, Cons(2, Cons(3, Nil))) in CHECKING mode too.

/-! ## (c) The read-only borrow law

    Give the issued borrow the identity pin and it becomes read-only; the
    container's own identity then follows, rather than being separately
    asserted.

    ```
    TARGET signature (does not parse today):

      fn Peek [i] (v : &mut (s : List Nat ~> List Nat = Set i (*res) s),
                   i : Nat, p : Le (S i) (Len *v)) -> &mut (t : Nat ~> Nat = t)
    ```

    The result's own debt says: what comes back through this borrow is what
    went out through it; `endIssued` enforces it, so a caller that writes
    through `r` is rejected. The container's pin then computes: `Set i (*res) s`
    with `*res = NthL i s` gives `Set i (NthL i s) s`, which is `s`. The caller
    derives that the container is unchanged; nothing separately claims it.

    This is why a shared reference can be understood as a contract on `&mut`
    rather than a new type former — and may remove the main reason to
    reinstate a separate shared-reference type `&τ`. The limit is honest,
    though: an identity-pinned `&mut` gives non-mutation, not aliasing. It is
    still exclusive, so two of them cannot coexist over one place. -/

/-- A caller that reads through the returned cursor and writes nothing.

    The read uses the comptime deref `let T = *r` (non-consuming: `*b` means
    the payload right now) rather than `let t = *r`, which would take the
    payload, leave a hole, and make the group unendable. A borrow-mode
    `match r` reads non-destructively too and would do the same job here, at
    the cost of splitting the run into two paths; the comptime deref keeps one
    path so the environment below is a single statement. -/
def readOnlyCaller : Term := withNth prog defer_check {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = Nth(b, 1, ());
  let T = *r;
  let y = x;
  () }

example : progOk readOnlyCaller = true := by native_decide

-- TODAY: opacity does not distinguish a caller that wrote from one that did not.
-- `y` is the same fresh σ as in `getMutRoundTrip` — the checker cannot tell the
-- two callers apart. This family is about that: not that a write is forgotten,
-- but that a non-write is forgotten too.
example : tailEnv readOnlyCaller
  [("x", .bot), ("b", .bot), ("r", .bot), ("T", .sym 0), ("y", .sym 1)] = true := by native_decide

example : runY readOnlyCaller == some (vlist [1, 2, 3]) := by native_decide

/-! TARGET: with the identity pin on the result, the checker knows `y ≡ [1,2,3]`:

    example : tailEnv readOnlyCaller
      [("x", .bot), ("b", .bot), ("r", .bot), ("T", .sym 0), ("y", vlist [1, 2, 3])] = true := by native_decide

    `T` — the element read out — stays an existential either way: the identity
    pin on the result says what comes back through the borrow equals what went
    out, not what that value is. Knowing the element would need the
    container's own `NthL i s` in the result's type, a separate capability
    (`retMixesBorrow`, see below).

    Live further below on `readOnlyCallerPin` (direct identity pins) — and `T`
    indeed stays a σ there, exactly as this note says.
-/

/-- The negative half: a caller that writes through a read-only borrow must be
    rejected, or the identity pin is only a comment.

    Today this program is accepted — it is `getMutRoundTrip` under a different
    name, since `Nth` carries no pin to violate. The target flips it only for a
    pinned cursor; the unpinned `Nth` above must keep accepting it. -/
def readOnlyViolated : Term := withNth prog defer_check {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = Nth(b, 1, ());
  *r := 9;
  let y = x;
  () }

example : progOk readOnlyViolated = true := by native_decide

-- TARGET (against a `Peek` carrying the identity pin, not against `Nth`):
--   example : progRejects readOnlyViolatedPinned "pin" = true := by native_decide
-- Live below as `readOnlyViolatedPin` (and the derived form's
-- `readOnlyDerivedViolated`); this unpinned acceptance stays, as it must.

/-! ## (a) `split_at_mut` as an ordinary library function

    Posed on an array, because that is where the calculus has a real split,
    and a cons-list's prefix and suffix are not two separate places.

    ```
    TARGET signature (does not parse today):

      fn SplitAtMut (a : &mut (s : Array 3 Nat ~> Array 3 Nat
                                 = arrCat 1 2 (*(fst res)) (*(snd res))))
        -> Σ (x : &mut (Array 1 Nat)). &mut (Array 2 Nat)
    ```

    The pin is over two issued exits — the general multi-issued case, where
    today's `Group` already carries `issued : List _` and only the release is
    opaque. -/

def varr (l : List Nat) : Val := .ctor "Arr" (l.map vnat)

def withSplit (rest : Term) : Term := prog{
  fn SplitAtMut (a : &mut (Array 3 Nat))
      -> Σ (x : &mut (Array 1 Nat)). &mut (Array 2 Nat) {
    let l = &m (*a)[Z ; 1];
    let r = &m (*a)[1 ; 2];
    Pair(l, r) };
  %rest }

/-- The shape already checks today: a function returning a pair of borrows
    carved out of one array type-checks now — the multi-issued group and the
    array carve compose without adjustment. What is missing is not the ability
    to write `split_at_mut`; it is the ability for its caller to learn
    anything from it. -/
example : progOk (withSplit prog defer_check { () }) = true := by native_decide

def splitCaller : Term := withSplit prog defer_check {
  let z = Arr(3, 1, 2);
  let b = &m z;
  let pr = SplitAtMut(b);
  match pr { Pair(lo, hi) => {
    *lo := Arr(9);
    *hi := Arr(8, 7);
    let y = z;
    () } } }

example : progOk splitCaller = true := by native_decide

-- TODAY: both halves are written and both writes are forgotten. `y` is one fresh σ at
-- `Array 3 Nat` — the group's opaque release — and nothing relates it to `Arr(9)` or
-- `Arr(8,7)`.
example : tailEnv splitCaller
  [("z", .bot), ("b", .bot), ("pr", .bot), ("lo", .bot), ("hi", .bot), ("y", .sym 0)]
  = true := by native_decide

example : runY splitCaller == some (varr [9, 8, 7]) := by native_decide

/-! TARGET: with the two-exit pin, the checker knows `y ≡ arrCat 1 2 (Arr 9) (Arr 8 7)`,
    i.e. `Arr(9, 8, 7)`:

    example : tailEnv splitCaller
      [("z", .bot), ("b", .bot), ("pr", .bot), ("lo", .bot), ("hi", .bot),
       ("y", varr [9, 8, 7])] = true := by native_decide
-/

/-! ### What blocks the target today, in two witnesses

    Both are named rejections rather than silent gaps, which makes them
    measurable now and flippable later. -/

/-- Witness 1: the containment refusal. A richer claim on a parameter consumed
    into the result is refused, because the callee is exempted from proving it
    and the caller's group end mints the release at it. `Programs.lean`'s
    `ThroughLie` pins the general form; this is the same refusal in
    `split_at_mut`'s own shape, where the parameter reaches both results. The
    milestone's hole-filling audit is what gives it a checker, and this
    `progRejects` becomes a `progOk`.

    Stated on the list cursor rather than the array one because the array's
    own owed types are longer than the point needs. -/
def containmentWitness : Term := prog defer_check {
  fn ThroughRich (v : &mut (s : List Nat ~> Σ (l : List Nat). Id Nat (Len l) (Len s)))
      -> &mut List Nat { v };
  () }

example : progRejects containmentWitness "is consumed into the result" = true := by native_decide

-- TARGET: this becomes `progOk` once the hole-filling audit checks the claim
-- instead of refusing the position. The rejection message above names the fix:
-- state a richer claim on a parameter the body keeps, where the audit runs.

/-- Witness 2: a pair of borrows cannot be a parameter. `split_at_mut`'s
    result can be returned but not passed on, because a borrow type is a
    telescope-position marker, and `Σ (x : &mut _). &mut _` is not one of the
    two shapes `processArgs` and `seedTelescopeV` hand-cut. (The one shape
    they do cut is the runtime-length slice `Σ (c : Nat). &mut (Array c T)`, a
    special case the general walk is meant to replace.)

    This is the shape half of the target, and it is what "an ordinary library
    function" means: a `split_at_mut` whose result cannot be handed to the
    next function is not one. -/
def pairParamWitness : Term := prog defer_check {
  fn UsePair (pr : Σ (x : &mut (Array 1 Nat)). &mut (Array 2 Nat)) -> Unit { () };
  () }

example : progRejects pairParamWitness "only valid at a telescope position" = true := by native_decide

-- TARGET: this becomes `progOk` once `readC` reflects `borrowT` (stage 2, the
-- shape half) instead of hand-cutting two shapes.

/-! ## What each family needs, and when it should go green

    Mapped against the design doc's stage plan, so the milestone can be
    checked off as `TARGET`s flip:

      * stage 2 (shape half)  → witness 2 flips: `pairParamWitness` becomes
                                `progOk`.
      * stage 4 (mint sites)  → nothing here flips on its own; it makes the
                                local-mint and stacking rules available to
                                stage 5.
      * stage 5 (the pin)     → family (b) flips entirely: both
                                `getMutRoundTrip` tailEnvs move from a `.sym`
                                to a concrete list, and witness 1
                                (`containmentWitness`) becomes `progOk`. Family
                                (c) flips with it — the read-only tailEnv, and
                                the write-through rejection against a pinned
                                `Peek`.
      * stage 6 (generality)  → family (a) flips: `splitCaller`'s tailEnv
                                moves.

    Two things must NOT move, and that is as much the acceptance criterion as
    the flips above:

      * `S7Group.chooseCaller` (`Boundaries.lean:341`) — distinct fresh σ's,
        `z = 7` unprovable. `choose` has no pin and must not acquire one;
        opacity stays the default.
      * `ArraySort`'s carve reset (`ArraySort.lean:195`, `:737`) — a call
        re-mints the caller's payload as a fresh σ at the declared type, which
        is the only way to reset the rigidity regime and is load-bearing for
        expressiveness, not hygiene. Writing no pin must change nothing.

    One program is expected to move from accepted to rejected: `g2SiblingHole`,
    where a range read leaves `⊥` in a sibling leaf of a parameter that is
    exempted wholesale because a borrow derived from it is returned. The
    hole-filling audit checks the payload whole and refuses it — a live
    soundness gap this milestone closes, not a precision feature. -/

/-! # The pin lands (stage 5) — families (b) and (c), on the pinned twins

    The design doc's ruling on pin syntax is one-slot: the right-hand side of
    `~>` is a single term, kind-classified — a type is the owed-type claim
    (every signature above, unchanged), and anything else is a pin, the value
    the release is, in which `*res` names the issued borrow's exit payload.
    The `TARGET` comments above were drafted in an earlier two-slot `~> τ' = e`
    spelling; what landed is the one-slot form below, so `List Nat = Set i
    (*res) s` is written `Set i (*res) s`, with the owed type inferred from
    the pin.

    A pin citing `i` needs `i` in scope, so `i` precedes `v` in the pinned
    telescopes (a parameter's type may cite only earlier parameters). The
    unpinned `Nth` and its callers above stay exactly as they are: they are
    the permanent controls that opacity remains the default. -/

/-! ## (b) The get_mut round-trip law, live -/

/-- `Nth` with the round-trip pin: when `v`'s loan ends, its payload is the
    entry list with position `i` replaced by whatever came back through the
    returned borrow. -/
def withNthPin (rest : Term) : Term := prog{
  fn NthPin [i] (i : Nat, v : &mut (s : List Nat ~> Set i (*res) s), p : Le (S i) (Len *v)) -> &mut Nat {
    match v {
      Nil => botElim Unit p,
      Cons(hd, tl) => match i {
        Z => &m *hd,
        S(k) => NthPin(k, &m *tl, p)
      }
    } };
  %rest }

/-- The callee-side discharge goes through on both branches: `Z` directly, and
    `S(k)` through the recursive call's own pin, projected at the shared exit σ
    (`Set (S k) r (Cons h t) ≡ Cons h (Set k r t)`, all atoms neutral) — now
    checked by the audit itself. -/
example : progOk (withNthPin prog defer_check { () }) = true := by native_decide

/-- The target, live: get position 1, write 9 through it, end the group — and
    the checker knows `y ≡ [1, 9, 3]`. The release is the pin with the
    surrendered payload substituted for `*res`, not an existential. Compare
    `getMutRoundTrip` above: same program, unpinned cursor, `y ↦ σ`. -/
def getMutRoundTripPin : Term := withNthPin prog defer_check {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = NthPin(1, b, ());
  *r := 9;
  let y = x;
  () }

example : progOk getMutRoundTripPin = true := by native_decide
example : tailEnv getMutRoundTripPin
  [("x", .bot), ("b", .bot), ("r", .bot), ("y", vlist [1, 9, 3])] = true := by native_decide

-- The executing machine computes the same list, so the gap the unpinned caller
-- pins above — checker forgets, machine remembers — closes for the pinned
-- cursor.
example : runY getMutRoundTripPin == some (vlist [1, 9, 3]) := by native_decide

/-- The head position — the `Z` leg of the same law, exercised through the
    recursion's base arm. -/
def getMutRoundTripHeadPin : Term := withNthPin prog defer_check {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = NthPin(0, b, ());
  *r := 7;
  let y = x;
  () }

example : progOk getMutRoundTripHeadPin = true := by native_decide
example : tailEnv getMutRoundTripHeadPin
  [("x", .bot), ("b", .bot), ("r", .bot), ("y", vlist [7, 2, 3])] = true := by native_decide
example : runY getMutRoundTripHeadPin == some (vlist [7, 2, 3]) := by native_decide

/-! ## (c) the read-only borrow law, live — way 1: direct identity pins

    The container pins to `s` (identity), the result to `t` (identity). The
    callee proves the container pin because the issued pin constrains the
    exit: an identity-pinned result's exit is its current payload, so the fill
    puts the entry element back in its place and the filled list converts with
    its own entry. No lemma, no `NthL` needed — the law as two identity pins. -/

def withGetRO (rest : Term) : Term := prog{
  fn GetRO [i] (i : Nat, v : &mut (s : List Nat ~> s), p : Le (S i) (Len *v)) -> &mut (t : Nat ~> t) {
    match v {
      Nil => botElim Unit p,
      Cons(hd, tl) => match i {
        Z => &m *hd,
        S(k) => GetRO(k, &m *tl, p)
      }
    } };
  %rest }

example : progOk (withGetRO prog defer_check { () }) = true := by native_decide

/-- Reads through `r` (the non-consuming comptime deref), writes nothing — and
    the checker knows `x` is unchanged: `y ≡ [1,2,3]`, where `readOnlyCaller`
    above gets a fresh σ. `T` stays an existential either way, exactly as the
    `TARGET` note above says it must: the identity pin says what comes back
    equals what went out, not what the element is (that needs
    `retMixesBorrow`, a separate capability covered below). -/
def readOnlyCallerPin : Term := withGetRO prog defer_check {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = GetRO(1, b, ());
  let T = *r;
  let y = x;
  () }

example : progOk readOnlyCallerPin = true := by native_decide
example : tailEnv readOnlyCallerPin
  [("x", .bot), ("b", .bot), ("r", .bot), ("T", .sym 0), ("y", vlist [1, 2, 3])]
  = true := by native_decide
example : runY readOnlyCallerPin == some (vlist [1, 2, 3]) := by native_decide

/-- The negative half: a write through the identity-pinned borrow is rejected
    at the group's end — the pin is a contract, not a comment. The same write
    against the unpinned `Nth` (`readOnlyViolated` above) stays accepted,
    exactly as it must. -/
def readOnlyViolatedPin : Term := withGetRO prog defer_check {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = GetRO(1, b, ());
  *r := 9;
  let y = x;
  () }

example : progRejects readOnlyViolatedPin "violates the borrow's pin" = true := by native_decide

/-! ## (c) way 2 — the derivation note, measured

    `GetRO` is derivable from `NthPin` — pin the container to `Set i (*res) s`
    and the result to identity — iff `Set i (NthL i s) s ⇝ s` is definitional.
    That reduction is definitional at concrete `i`/`s`, but stuck at symbolic
    ones (`Tests.PinProbe`). What that means operationally, measured here:

    * the derived form's declaration checks — the container discharge never
      needs the lemma, because the fill computes `Set i (exit) s` directly;
    * its caller learns the relational fact `y ≡ [1, T, 3]` — the entry with
      position `i` replaced by the very element it read out, the σ shared
      between `T` and `y` — strictly more than opacity, and strictly less
      than way 1's `y ≡ [1,2,3]`. Closing that gap needs `T = NthL i s`, i.e.
      where the cursor points, which is `retMixesBorrow`, not a pin.

    So "the caller derives that the container is unchanged" holds of way 1
    outright, and of way 2 only up to the element fact the calculus cannot yet
    state. The read-only rejection is identical either way. -/

def withNthPinRO (rest : Term) : Term := prog{
  fn NthPinRO [i] (i : Nat, v : &mut (s : List Nat ~> Set i (*res) s), p : Le (S i) (Len *v)) -> &mut (t : Nat ~> t) {
    match v {
      Nil => botElim Unit p,
      Cons(hd, tl) => match i {
        Z => &m *hd,
        S(k) => NthPinRO(k, &m *tl, p)
      }
    } };
  %rest }

example : progOk (withNthPinRO prog defer_check { () }) = true := by native_decide

def readOnlyDerivedCaller : Term := withNthPinRO prog defer_check {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = NthPinRO(1, b, ());
  let T = *r;
  let y = x;
  () }

example : progOk readOnlyDerivedCaller = true := by native_decide
example : tailEnv readOnlyDerivedCaller
  [("x", .bot), ("b", .bot), ("r", .bot), ("T", .sym 0),
   ("y", .ctor "Cons" [vnat 1, .ctor "Cons" [.sym 0, .ctor "Cons" [vnat 3, .ctor "Nil" []]]])]
  = true := by native_decide

def readOnlyDerivedViolated : Term := withNthPinRO prog defer_check {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = NthPinRO(1, b, ());
  *r := 9;
  let y = x;
  () }

example : progRejects readOnlyDerivedViolated "violates the borrow's pin" = true := by native_decide

/-! ## The cursor says where it points — way 2's residual closes

    `retMixesBorrow` is lifted: a borrow-returning signature may carry value
    components, judged per component at the callee's audit against the actual
    first component (no `∀` — the callee knows this one), checked against the
    return type pinned at entry and branch-swept (`St.retTyBorrow`; a type
    rebuilt at audit time would otherwise hold a stale entry σ). So the shape
    the containment refusal above made unwritable now exists:

        Σ (r : &mut Nat). Id Nat (*r) (NthL i (old *v))

    `*r` collapses to the binder and opens at the payload — the knowledge of a
    borrow component is its payload — on both ends: the callee's check and the
    caller's minted evidence. -/

/-- Evidence alone: `NthEv` proves per branch that the borrow it returns points
    at position `i` — `Refl` at the `Z` leg (`NthL Z (Cons h t) ⇝ h`), the
    recursive call's own evidence at `S(k)` (`NthL (S k) (Cons h t) ⇝ NthL k t`,
    index-first, so the chain composes definitionally). -/
def withNthEv (rest : Term) : Term := prog{
  fn NthEv [i] (i : Nat, v : &mut List Nat, p : Le (S i) (Len *v))
      -> Σ (r : &mut Nat). Id Nat (*r) (NthL i (old *v)) {
    match v {
      Nil => botElim Unit p,
      Cons(hd, tl) => match i {
        Z => Pair(&m *hd, Refl),
        S(k) => NthEv(k, &m *tl, p)
      }
    } };
  %rest }

example : progOk (withNthEv prog defer_check { () }) = true := by native_decide

/-- Pin and evidence — the full get_mut signature: the parameter says what the
    container becomes, the result says where the cursor points. -/
def withNthPinEv (rest : Term) : Term := prog{
  fn NthPinEv [i] (i : Nat, v : &mut (s : List Nat ~> Set i (*res) s), p : Le (S i) (Len *v))
      -> Σ (r : &mut Nat). Id Nat (*r) (NthL i (old *v)) {
    match v {
      Nil => botElim Unit p,
      Cons(hd, tl) => match i {
        Z => Pair(&m *hd, Refl),
        S(k) => NthPinEv(k, &m *tl, p)
      }
    } };
  %rest }

example : progOk (withNthPinEv prog defer_check { () }) = true := by native_decide

/-- Way 2, completed. `readOnlyDerivedCaller` above stops at `y ≡ [1, T, 3]`
    because nothing said what `T` is; the evidence says it. Matching the
    returned `Refl` refines the exit σ to `NthL 1 entry ⇝ 2`, so `T` is the
    concrete element and the release computes `Set 1 2 [1,2,3] ⇝ [1,2,3]`. The
    caller derives that the container is unchanged, with the derivation
    visible: pin + evidence + one `Refl`-match. -/
def readOnlyDerivedClosed : Term := withNthPinEv prog defer_check {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let pr = NthPinEv(1, b, ());
  match pr { Pair(r, h) => {
    match h { Refl => {
      let T = *r;
      let y = x;
      () } } } } }

example : progOk readOnlyDerivedClosed = true := by native_decide
example : tailEnv readOnlyDerivedClosed
  [("x", .bot), ("b", .bot), ("pr", .bot), ("r", .bot), ("h", .bot),
   ("T", vnat 2), ("y", vlist [1, 2, 3])] = true := by native_decide
example : runY readOnlyDerivedClosed == some (vlist [1, 2, 3]) := by native_decide

/-- The two-call round-trip chain — the full get_mut law across two calls on
    the list arena. Call, write 9 through the cursor, call again at the same
    index: the second call's evidence tells the caller the second borrow holds
    `NthL 1` of the released list, which the first call's pin made `[1,9,3]`,
    so `T ≡ 9`. The checker derives that what was written through the first
    borrow is what the second borrow holds, end to end in checking mode. -/
def twoGetMutChain : Term := withNthPinEv prog defer_check {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let pr = NthPinEv(1, b, ());
  match pr { Pair(r, h) => {
    *r := 9;
    let b2 = &m x;
    let pr2 = NthPinEv(1, b2, ());
    match pr2 { Pair(r2, h2) => {
      match h2 { Refl => {
        let T = *r2;
        let y = x;
        () } } } } } } }

example : progOk twoGetMutChain = true := by native_decide
example : tailEnv twoGetMutChain
  [("x", .bot), ("b", .bot), ("pr", .bot), ("r", .bot), ("h", .sym 0),
   ("b2", .bot), ("pr2", .bot), ("r2", .bot), ("h2", .bot),
   ("T", vnat 9), ("y", vlist [1, 9, 3])] = true := by native_decide
example : runY twoGetMutChain == some (vlist [1, 9, 3]) := by native_decide

/-- The negative control: evidence about the wrong position — the body returns
    the head while the type claims position 1. Refused at the audit's
    value-component check, with both sides printed. -/
def badEv : Term := prog defer_check {
  fn BadEv (i : Nat, v : &mut List Nat, p : Le (S i) (Len *v))
      -> Σ (r : &mut Nat). Id Nat (*r) (NthL 1 (old *v)) {
    match v {
      Nil => botElim Unit p,
      Cons(hd, tl) => Pair(&m *hd, Refl)
    } };
  () }

example : progRejects badEv "mixed return type — value component" = true := by native_decide

/-- Diagnostics speak the surface: the kernel form of `*res` is the marker
    spine `@res k`, and a message quoting a pin the discharge could not
    substitute must print it the way the programmer wrote it. The leak shape:
    a value-returning function whose parameter pins to `*res` — no borrow is
    issued, so nothing can ever pay the pin, the substitution has no exits,
    and the failure quotes the pin raw. The needle asserts the sugared
    spelling (`Term.resSugar`, a display-only pre-pass in `Term.pretty`; the
    fst/snd forms engage when a term cites index ≥ 1). No existing needle
    depends on the raw `@res` spelling, so this rewording moves nothing
    else. -/
def resLeakPin : Term := prog defer_check {
  fn KeepPin (v : &mut (s : List Nat ~> *res)) -> Unit { () };
  () }

example : progRejects resLeakPin "does not convert with the declared pin (*res)" = true := by
  native_decide

end Dllbc.Tests.BorrowRefoundGoals
