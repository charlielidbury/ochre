import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff

/-!
# GOALS — the borrow re-founding milestone's finish line

**This file is not a test suite. It is a target.** Every program below is a `def`;
what is asserted live is only what is TRUE TODAY, and every assertion the milestone
is supposed to make true is written out and commented off, marked `TARGET`. The file
builds green on `b8721644` and must keep building green until the milestone lands,
at which point the `TARGET` lines go live and the `TODAY` lines that contradict them
move.

The design is `docs/design-borrow-refounding.md`; read that first. The one-line
version: `&mut τ` becomes a value predicate rather than a telescope position, and
`~> S` becomes a **debt registered on the loan at mint** rather than an annotation
attached to a boundary — with an optional **pin**, a value claim that may mention
the exit snapshots of the loans issued alongside it. The pin is what makes the three
families below expressible.

Three families:

  * **(a)** `split_at_mut` as an ordinary library function returning a pair of
    borrows. The SUGGESTIONS entry's own acceptance test.
  * **(b)** the **get_mut round-trip law** — whatever the caller writes through a
    returned cursor is still there next time it gets. Today the checker forgets it;
    the executing machine does not, and the pair below pins the gap from both sides.
  * **(c)** the **read-only borrow law** — a returned borrow whose own debt is the
    identity is read-only, and the container's own identity then FOLLOWS. This is
    the observation that a shared reference may be a contract on `&mut` rather than
    a new type former.

The surface used in the `TARGET` signatures below (`~> S = e`, and `*res` for an
issued borrow's exit snapshot) **does not parse today** — decisions D1 and D3 of the
design doc — so those signatures appear in comments only. Nothing here should be
read as a commitment to that spelling.

**STAGE 5 LANDED (M35).** Families (b) and (c) are LIVE, at the end of the file,
under D1's ratified ONE-SLOT spelling (`~> Set i (*res) s`, no `= e` connective) —
on PINNED TWINS, because a pin is per-signature: every TODAY assertion above
STAYS, as the permanent control that opacity remains the default for signatures
that write no pin. Family (a) (`split_at_mut`) remains a target — it needs the
shape half (stage 2) and the general walk (stage 6).
-/

open Dllbc
-- `StdLemmas.Set` is the list update the get_mut pin is written against; the
-- SELECTIVE open keeps Lean's own `Set` unshadowed for everything else.
open Dllbc.StdLemmas (Set NthL)

namespace Dllbc.Tests.BorrowRefoundGoals

/-! ## Reading helpers -/

def vnat : Nat → Val | 0 => .ctor "Z" [] | n + 1 => .ctor "S" [vnat n]
def vlist : List Nat → Val | [] => .ctor "Nil" [] | h :: t => .ctor "Cons" [vnat h, vlist t]

/-- What the EXECUTING machine leaves in `y`. The checker's answer is `tailEnv`'s. -/
def runY (t : Term) : Option Val :=
  match Dllbc.Tests.S9Diff.runExec t with
  | .ok env => env.lookup "y"
  | .error _ => none

/-! ## (b) THE GET_MUT ROUND-TRIP LAW

    "Whatever the user writes through a `get_mut` borrow is still there next time
    they get." Stated over a list first, so the container's own theory is one
    `NthL`/`Set` pair rather than a hashmap's.

    The cursor is §14's `Nth`, verbatim — a bounds-proof cursor returning a `&mut Nat`
    into a list. What the milestone adds is a claim on its PARAMETER:

    ```
    TARGET signature (does not parse today — design doc D1, D3):

      fn Nth [i] (v : &mut (s : List Nat ~> List Nat = Set i (*res) s),
                  i : Nat, p : Le (S i) (Len *v)) -> &mut Nat
    ```

    Read: when `v`'s loan ends, its payload is the entry list with position `i`
    replaced by whatever came back through the borrow I returned. `*res` is the exit
    snapshot of the issued borrow.

    The callee-side obligation is the design doc's §2.3 hole-filling, and the two
    branches are the two cases:

      * `Z`:    payload `Cons (loanₘ ℓ_hd) tl`, hole-filled `Cons σ_res tl`;
                the pin opens to `Set Z σ_res (Cons hd tl) ⇝ Cons σ_res tl`.        ✓
      * `S(k)`: payload `Cons hd (loanₘ ℓ_tl)` with ℓ_tl captured by the recursive
                call's group, whose own pin PROJECTS to `Set k σ_res tl_entry`;
                the pin opens to `Set (S k) σ_res (Cons hd tl) ⇝ Cons hd (Set k σ_res tl)`. ✓

    Both legs are definitional on `StdLemmas.Set` as written (it recurses on the
    index first, so `Set (S k) v (Cons h t) ⇝ Cons h (Set k v t)` and
    `Set Z v (Cons h t) ⇝ Cons v t`). That is the design doc §10's viability probe,
    hand-checked; it should still be run against the machine before stage 1. -/

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

example : progOk (withNth prog{ () }) = true := by native_decide

/-- The round trip: get position 1, write 9 through it, end the group, read the list. -/
def getMutRoundTrip : Term := withNth prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = Nth(b, 1, ());
  *r := 9;
  let y = x;
  () }

example : progOk getMutRoundTrip = true := by native_decide

-- TODAY: the checker hands the owner a FRESH σ — the write through `r` is forgotten,
-- exactly as `S7Group.throughCaller` pins for the degenerate cursor. `x` is ⊥ (moved
-- into `y`), and `y` is an existential at `List Nat` about which nothing is known.
example : tailEnv getMutRoundTrip
  [("x", .bot), ("b", .bot), ("r", .bot), ("y", .sym 0)] = true := by native_decide

-- …and the executing machine does the right thing, which is what makes the gap a gap
-- and not a disagreement: opacity is a fact about what was promised, never about what
-- happens (`dllbc-arrows.md` §6.2, M27's fold).
example : runY getMutRoundTrip == some (vlist [1, 9, 3]) := by native_decide

/-! TARGET. With the pin on `Nth`'s parameter, the CHECKER knows the same thing:
    `y ≡ Set 1 9 (Cons 1 (Cons 2 (Cons 3 Nil))) ⇝ Cons 1 (Cons 9 (Cons 3 Nil))`.
    The release is no longer an existential, so the `tailEnv` above moves from a
    `.sym` to the concrete list — which is the shape of the assertion, whatever the
    canonical spelling of the recovered value turns out to be.

    TARGET (uncomment when the milestone lands; the `TODAY` tailEnv above moves):

    example : tailEnv getMutRoundTrip
      [("x", .bot), ("b", .bot), ("r", .bot), ("y", vlist [1, 9, 3])] = true := by native_decide

    STAGE 5 LANDED (M35): this assertion is LIVE below, on `getMutRoundTripPin` —
    the pin is per-signature, so the flip happens on the PINNED twin and the
    unpinned tailEnv above STAYS, as the permanent statement that opacity is the
    default. See "THE PIN LANDS" at the end of the file.
-/

/-- The same law one call deeper: the value written through a cursor obtained from a
    cursor. This is the case that exercises the recursive projection (`S(k)`), because
    `Nth`'s own body reaches position 1 through a recursive call. It is the same
    program as above; it is called out separately because if the pin composes for
    `i = 0` and not for `i = 1`, the mechanism is the shallow one and not the law. -/
def getMutRoundTripHead : Term := withNth prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = Nth(b, 0, ());
  *r := 7;
  let y = x;
  () }

example : progOk getMutRoundTripHead = true := by native_decide
example : runY getMutRoundTripHead == some (vlist [7, 2, 3]) := by native_decide

-- TARGET: y ≡ Cons(7, Cons(2, Cons(3, Nil))) in CHECKING mode too.

/-! ## (c) THE READ-ONLY BORROW LAW

    Give the ISSUED borrow the identity pin and it becomes read-only; the container's
    own identity then FOLLOWS rather than being separately asserted.

    ```
    TARGET signature (does not parse today):

      fn Peek [i] (v : &mut (s : List Nat ~> List Nat = Set i (*res) s),
                   i : Nat, p : Le (S i) (Len *v)) -> &mut (t : Nat ~> Nat = t)
    ```

    The result's own debt says: what comes back through this borrow is what went out
    through it. `endIssued` asserts it, so a caller that writes through `r` is
    REJECTED. And the container's pin then computes: `Set i (*res) s` with
    `*res = NthL i s` gives `Set i (NthL i s) s`, which is `s`. **The caller derives
    that the container is unchanged**; nothing separately claims it.

    That is the language-design observation the design doc §5 flags: a shared
    reference is a CONTRACT on `&mut`, not a new type former, and `&τ` — cut from the
    roadmap on 2026-08-13 — may be obviated for its principal motivation without
    being reinstated. The honest limit travels with it: an identity-pinned `&mut`
    gives non-mutation, not ALIASING. It is still exclusive, so two of them cannot
    coexist over one place, and the cut entry's aliasing motivations are untouched. -/

/-- A caller that READS through the returned cursor and writes nothing.

    The read is the **comptime deref** `let T = *r` (§5.2's "`*b` means the payload
    now", non-consuming) rather than `let t = *r`, which is §2.2's take: it leaves a
    hole and makes the group unendable ("nothing surrendered"). A borrow-mode `match r`
    reads non-destructively too, and does the same job here at the cost of splitting
    the run into two paths — either would serve; the comptime deref keeps one path so
    the environment below is a single statement. -/
def readOnlyCaller : Term := withNth prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = Nth(b, 1, ());
  let T = *r;
  let y = x;
  () }

example : progOk readOnlyCaller = true := by native_decide

-- TODAY: opacity does not distinguish a caller that wrote from one that did not.
-- `y` is the same fresh σ it is in `getMutRoundTrip`, and the checker cannot tell the
-- two callers apart. THAT is what this family is about — not that the write is
-- forgotten, but that the NON-write is forgotten too.
example : tailEnv readOnlyCaller
  [("x", .bot), ("b", .bot), ("r", .bot), ("T", .sym 0), ("y", .sym 1)] = true := by native_decide

example : runY readOnlyCaller == some (vlist [1, 2, 3]) := by native_decide

/-! TARGET: with the identity pin on the result, the checker knows `y ≡ [1,2,3]`:

    example : tailEnv readOnlyCaller
      [("x", .bot), ("b", .bot), ("r", .bot), ("T", .sym 0), ("y", vlist [1, 2, 3])] = true := by native_decide

    Note that `T` — the element read out — stays an existential either way. The
    identity pin on the RESULT says what comes back through the borrow equals what
    went out; it does not say what that value IS, and nothing here should. Knowing
    the element would need the container's own `NthL i s` in the result's type, which
    is design-doc D9's lifted `retMixesBorrow` and a separate capability.

    STAGE 5 LANDED (M35): live below on `readOnlyCallerPin` (way 1, direct
    identity pins) — and `T` indeed stays a σ there, exactly as this note says.
-/

/-- The negative half, and the more important one: a caller that WRITES through a
    read-only borrow must be REJECTED. Without this the identity pin is a comment.

    Today this program is ACCEPTED — it is `getMutRoundTrip` under a different name,
    and `Nth` carries no pin to violate. The milestone must flip it, and only for the
    pinned cursor: the unpinned `Nth` above must go on accepting it. -/
def readOnlyViolated : Term := withNth prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = Nth(b, 1, ());
  *r := 9;
  let y = x;
  () }

example : progOk readOnlyViolated = true := by native_decide

-- TARGET (against a `Peek` carrying the identity pin, not against `Nth`):
--   example : progRejects readOnlyViolatedPinned "pin" = true := by native_decide
-- STAGE 5 LANDED (M35): live below as `readOnlyViolatedPin` (and the derived
-- form's `readOnlyDerivedViolated`); this unpinned acceptance stays, as it must.

/-! ## (a) `split_at_mut` AS AN ORDINARY LIBRARY FUNCTION

    The SUGGESTIONS entry's own acceptance test. Posed on an array, because that is
    where the calculus has a real split — the M24 carve — and a cons-list's prefix and
    suffix are not two places.

    ```
    TARGET signature (does not parse today):

      fn SplitAtMut (a : &mut (s : Array 3 Nat ~> Array 3 Nat
                                 = arrCat 1 2 (*(fst res)) (*(snd res))))
        -> Σ (x : &mut (Array 1 Nat)). &mut (Array 2 Nat)
    ```

    The pin is over TWO issued exits — the general multi-issued case, where today's
    `Group` already carries `issued : List _` and only the release is opaque. -/

def varr (l : List Nat) : Val := .ctor "Arr" (l.map vnat)

def withSplit (rest : Term) : Term := prog{
  fn SplitAtMut (a : &mut (Array 3 Nat))
      -> Σ (x : &mut (Array 1 Nat)). &mut (Array 2 Nat) {
    let l = &m (*a)[Z ; 1];
    let r = &m (*a)[1 ; 2];
    Pair(l, r) };
  %rest }

/-- **The shape is already there, and that is the finding to lead with.** A function
    returning a pair of borrows carved out of one array checks TODAY — the multi-issued
    group (`Nth2`, §6.1) and the carve (M24) compose without adjustment. What is
    missing is not the ability to write `split_at_mut`; it is the ability for its
    caller to learn anything from it. -/
example : progOk (withSplit prog{ () }) = true := by native_decide

def splitCaller : Term := withSplit prog{
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

    Both are honest, named rejections rather than silent gaps — which is what makes
    them measurable now and flippable later. -/

/-- **Witness 1: the M27 containment.** A richer claim on a parameter consumed into the
    result is refused, because the callee is exempted from proving it and the caller's
    group end mints the release AT it. `Programs.lean` §E1 pins the general form
    (`ThroughLie`); this is the same refusal in `split_at_mut`'s own shape, where the
    parameter reaches BOTH results. The milestone's §3.3 hole-filling audit is what
    gives it a checker, and this `progRejects` becomes a `progOk`.

    Stated on the list cursor rather than the array one because the array's own
    non-trivial owed types are longer than the point. -/
def containmentWitness : Term := prog{
  fn ThroughRich (v : &mut (s : List Nat ~> Σ (l : List Nat). Id Nat (Len l) (Len s)))
      -> &mut List Nat { v };
  () }

example : progRejects containmentWitness "is consumed into the result" = true := by native_decide

-- TARGET: this becomes `progOk` — the hole-filling audit checks the claim instead of
-- refusing the position. The M27 containment's own message names the fix: "state a
-- richer claim on a parameter the body keeps, where the audit runs."

/-- **Witness 2: a pair of borrows cannot be a PARAMETER.** `split_at_mut`'s result can
    be returned but not passed on, because a borrow type is a telescope-position marker
    and `Σ (x : &mut _). &mut _` is not one of the two shapes `processArgs` and
    `seedTelescopeV` hand-cut. (The one shape they do cut is M24's runtime-length slice,
    `Σ (c : Nat). &mut (Array c T)` — the "special-cased crack in a general wall" the
    SUGGESTIONS entry names. Design-doc D10 deletes it in favour of the general walk.)

    This is the shape half, and it is what "an ordinary library function" means: a
    `split_at_mut` whose result cannot be handed to the next function is not one. -/
def pairParamWitness : Term := prog{
  fn UsePair (pr : Σ (x : &mut (Array 1 Nat)). &mut (Array 2 Nat)) -> Unit { () };
  () }

example : progRejects pairParamWitness "only valid at a telescope position" = true := by native_decide

-- TARGET: this becomes `progOk`. The refusal is `readC`'s, and it goes away when
-- `readC` reflects `borrowT` (design-doc §4.2, stage 2) — the shape half, which is
-- also what closes §7's "pass it as an argument" promise for borrow-moded signatures
-- (`suspensions.md` §421, still an open residual today).

/-! ## What each family needs, and when it should go green

    Against the design doc's seven-stage plan (§10). This is the map from this file's
    `TARGET`s to the work, so the milestone can be checked off against it.

      * stage 2 (shape half)   → witness 2 flips: `pairParamWitness` becomes `progOk`.
      * stage 4 (mint sites)   → nothing here flips on its own; it is what makes the
                                 local-mint and stacking rules available to stage 5.
      * stage 5 (the pin)      → family (b) flips entirely: both `getMutRoundTrip`
                                 tailEnvs move from a `.sym` to a concrete list, and
                                 witness 1 (`containmentWitness`) becomes `progOk`.
                                 Family (c) flips with it — the read-only tailEnv, and
                                 the write-through rejection against a pinned `Peek`.
      * stage 6 (generality)   → family (a) flips: `splitCaller`'s tailEnv moves.

    And the two things that must NOT move, which are as much the acceptance criteria as
    the flips are:

      * `S7Group.chooseCaller` (`Boundaries.lean:341`) — distinct fresh σ's, `z = 7`
        unprovable. `choose` has no pin and must not acquire one. Opacity stays the
        default, and this is where that is stated.
      * `ArraySort`'s carve reset (`ArraySort.lean:195`, `:737`) — a call re-mints the
        caller's payload as a fresh σ at the declared type, which is the only way to
        reset the rigidity regime and is load-bearing for EXPRESSIVENESS, not hygiene
        (`dllbc-arrows.md` §6.2). Writing no pin must change nothing.

    One program is expected to move from ACCEPTED to REJECTED, and only one: the
    `hm-probe-getmut` lane's `g2SiblingHole`, where a range read leaves ⊥ in a sibling
    leaf of a parameter that is exempted wholesale because a borrow derived from it is
    returned. The hole-filling audit checks the payload whole and refuses it. See the
    design doc §3.3.1 — that is a live soundness gap this milestone closes, not a
    precision feature. -/

/-! # THE PIN LANDS (stage 5) — families (b) and (c), on the PINNED twins

    12-design D1's ratified ONE-SLOT form: the RHS of `~>` is a single term,
    kind-classified — a type is the owed-type claim (every signature above,
    unchanged), anything else is a PIN, the value the release IS, in which
    `*res` names the issued borrow's exit payload. The TARGET comments above
    were drafted in the two-slot `~> τ' = e` spelling; what landed is the
    one-slot ruling, so `List Nat = Set i (*res) s` is written `Set i (*res) s`
    and the owed type is the pin's own.

    A pin citing `i` needs `i` IN SCOPE, so `i` precedes `v` in the pinned
    telescopes (a parameter's type may cite only earlier parameters — the §5.2
    convention the draft signatures elided). The UNPINNED `Nth` and its callers
    above stay exactly as they are: they are the permanent controls that
    opacity remains the default. -/

/-! ## (b) the get_mut round-trip law, live -/

/-- `Nth` with the round-trip pin: when `v`'s loan ends, its payload IS the
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

/-- The callee-side discharge goes through on BOTH branches — `Z` directly,
    `S(k)` through the recursive call's own pin PROJECTED at the shared exit σ:
    the stage-0 probe's conversion (`Set (S k) r (Cons h t) ≡ Cons h (Set k r t)`,
    all atoms neutral), now run by the audit itself. -/
example : progOk (withNthPin prog{ () }) = true := by native_decide

/-- THE TARGET, live: get position 1, write 9 through it, end the group — and
    the CHECKER knows `y ≡ [1, 9, 3]`. The release is the pin with the
    surrendered payload substituted for `*res`, not an existential. Compare
    `getMutRoundTrip` above: same program, unpinned cursor, `y ↦ σ`. -/
def getMutRoundTripPin : Term := withNthPin prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = NthPin(1, b, ());
  *r := 9;
  let y = x;
  () }

example : progOk getMutRoundTripPin = true := by native_decide
example : tailEnv getMutRoundTripPin
  [("x", .bot), ("b", .bot), ("r", .bot), ("y", vlist [1, 9, 3])] = true := by native_decide

-- …and the executing machine computes the same list, so the divergence pair the
-- unpinned caller pins above (checker forgets / machine remembers) CLOSES for
-- the pinned cursor.
example : runY getMutRoundTripPin == some (vlist [1, 9, 3]) := by native_decide

/-- The head position — the `Z` leg of the same law, exercised through the
    recursion's base arm. -/
def getMutRoundTripHeadPin : Term := withNthPin prog{
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

/-! ## (c) the read-only borrow law, live — WAY 1: direct identity pins

    The container pins to `s` (identity), the result to `t` (identity). The
    callee proves the container pin BECAUSE the issued pin CONSTRAINS the exit:
    an identity-pinned result's exit IS its current payload, so the fill puts
    the entry element back in its place and the filled list converts with its
    entry self. No lemma, no `NthL` — §5's law as two identity pins. -/

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

example : progOk (withGetRO prog{ () }) = true := by native_decide

/-- Reads through `r` (the non-consuming comptime deref), writes nothing — and
    the checker knows `x` is UNCHANGED: `y ≡ [1,2,3]`, where `readOnlyCaller`
    above gets a fresh σ. `T` stays an existential either way, exactly as the
    TARGET note above says it must: the identity pin says what comes back
    equals what went out, not what the element IS (that is D9's lifted
    `retMixesBorrow`, a separate capability). -/
def readOnlyCallerPin : Term := withGetRO prog{
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

/-- The negative half, and the more important one: a WRITE through the
    identity-pinned borrow is REJECTED at the group's end — the pin is a
    contract, not a comment. The same write against the unpinned `Nth`
    (`readOnlyViolated` above) stays accepted, exactly as it must. -/
def readOnlyViolatedPin : Term := withGetRO prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = GetRO(1, b, ());
  *r := 9;
  let y = x;
  () }

example : progRejects readOnlyViolatedPin "violates the borrow's pin" = true := by native_decide

/-! ## (c) WAY 2 — the derivation note, MEASURED

    §12(c)'s note reads: `GetRO` is DERIVABLE from `NthPin` — pin the container
    to `Set i (*res) s` and the result to identity — iff `Set i (NthL i s) s ⇝ s`
    is definitional. Stage 0 measured the reduction: definitional at CONCRETE
    `i`/`s`, stuck at symbolic ones (`Tests.PinProbe`). What that means
    operationally, measured here:

    * the derived form's DECLARATION checks — the container discharge never
      needs the lemma, because the fill computes `Set i (exit) s` directly;
    * its CALLER learns the RELATIONAL fact `y ≡ [1, T, 3]` — the entry with
      position `i` replaced by the very element it read out, the σ SHARED
      between `T` and `y` — which is strictly more than opacity and strictly
      less than way 1's `y ≡ [1,2,3]`. Closing the residual gap needs `T = NthL i s`,
      i.e. WHERE the cursor points — D9's lifted `retMixesBorrow`, not a pin.

    So the doc's "the caller derives that the container is unchanged" holds of
    way 1 outright, and of way 2 only up to the element fact the calculus
    cannot yet state. The read-only REJECTION is identical either way. -/

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

example : progOk (withNthPinRO prog{ () }) = true := by native_decide

def readOnlyDerivedCaller : Term := withNthPinRO prog{
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

def readOnlyDerivedViolated : Term := withNthPinRO prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = NthPinRO(1, b, ());
  *r := 9;
  let y = x;
  () }

example : progRejects readOnlyDerivedViolated "violates the borrow's pin" = true := by native_decide

/-! ## D9 LANDS (M35, residual (b)) — the cursor says WHERE it points, and
    way 2's residual CLOSES

    `retMixesBorrow` is lifted: a borrow-returning signature may carry VALUE
    components, judged per component at the callee's audit with the ACTUAL
    first component (no ∀ — the callee knows this one) against the return type
    pinned at entry and branch-swept (`St.retTyBorrow`; a type rebuilt at audit
    time holds a stale entry σ — measured, not guessed). So the shape M27's
    containment made unwritable exists:

        Σ (r : &mut Nat). Id Nat (*r) (NthL i (old *v))

    `*r` collapses to the binder and opens at the PAYLOAD — the knowledge of a
    borrow component IS its payload — on both ends: the callee's check and the
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

example : progOk (withNthEv prog{ () }) = true := by native_decide

/-- Pin AND evidence — the full get_mut signature: the parameter says what the
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

example : progOk (withNthPinEv prog{ () }) = true := by native_decide

/-- WAY 2, COMPLETED. `readOnlyDerivedCaller` above stops at `y ≡ [1, T, 3]`
    because nothing said what `T` is; the evidence says it. Match the returned
    `Refl` and the exit σ REFINES to `NthL 1 entry ⇝ 2` — so `T` is the
    concrete element and the release computes `Set 1 2 [1,2,3] ⇝ [1,2,3]`. The
    caller derives that the container is unchanged, exactly as 12-design §5
    wanted, with the derivation visible: pin + evidence + one Refl-match. -/
def readOnlyDerivedClosed : Term := withNthPinEv prog{
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

/-- THE TWO-CALL ROUND-TRIP CHAIN — the full two-get_mut law on the list arena.
    Call, write 9 through the cursor, call again at the same index: the second
    call's evidence tells the caller the second borrow holds NthL 1 of the
    RELEASED list — which the first call's pin made `[1,9,3]` — so `T ≡ 9`:
    the checker DERIVES that what was written through the first borrow is what
    the second borrow holds. This is the fact the whole milestone is named for,
    end to end in checking mode. -/
def twoGetMutChain : Term := withNthPinEv prog{
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

/-- The NEGATIVE control: evidence about the WRONG position — the body returns
    the head while the type claims position 1. Refused at the audit's new
    value-component check, with both sides printed. -/
def badEv : Term := prog{
  fn BadEv (i : Nat, v : &mut List Nat, p : Le (S i) (Len *v))
      -> Σ (r : &mut Nat). Id Nat (*r) (NthL 1 (old *v)) {
    match v {
      Nil => botElim Unit p,
      Cons(hd, tl) => Pair(&m *hd, Refl)
    } };
  () }

example : progRejects badEv "mixed return type — value component" = true := by native_decide

/-- **Diagnostics speak the surface** (M35 addendum): the kernel form of `*res`
    is the marker spine `@res k`, and a message quoting a pin the discharge
    could not substitute must print it the way the programmer wrote it. The
    leak shape: a VALUE-returning function whose parameter pins to `*res` — no
    borrow is issued, so nothing can ever pay the pin, the substitution has no
    exits, and the failure quotes the pin raw. The needle asserts the sugared
    spelling (`Term.resSugar`, a display-only pre-pass in `Term.pretty`; the
    fst/snd forms engage when a term cites index ≥ 1). No existing needle
    anywhere contains `@res` — grepped — so the rewording moves nothing. -/
def resLeakPin : Term := prog{
  fn KeepPin (v : &mut (s : List Nat ~> *res)) -> Unit { () };
  () }

example : progRejects resLeakPin "does not convert with the declared pin (*res)" = true := by
  native_decide

end Dllbc.Tests.BorrowRefoundGoals
