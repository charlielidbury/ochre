import Dllbc.Program
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.ProgMacro
import Dllbc.Tests.S6Call
import Dllbc.Tests.S16Spec

/-!
# §27 (M27) — the mixed-return-type containment

**The hole, found by `dllbc-b1`'s back-probe** (branch `backprobe`,
`Tests/S27BackProbe.lean` §A, whose six witnesses this file's controls are drawn
from and credited to). A borrow-carrying return type is audited STRUCTURALLY —
`collectResultBorrows` walks it and checks each issued borrow against its owed
type — and is deliberately never pinned or `readC`'d, since `readC` rejects
`borrowT`. Both audit sites gate the value check on the WHOLE type being
borrow-free, so a non-borrow component of a borrow-carrying return type was judged
by nothing at all.

**Not vacuous — unsound.** The caller's `buildResult` mints a σ at the stated leaf
type regardless, so a caller RECEIVES the unearned claim as a proof and can return
it at its own value return type, where the pin-and-check path does run and passes,
because the σ genuinely carries that `sctx` type. b1 closed it: `fn closedBot ()
-> Bot`, no hypotheses, checking.

**Why it never bit.** No corpus declaration is both borrow-returning AND
ensures-carrying: cursor content rode in `back`, and backs ARE checked at their own
callee audit. M27 deletes backs and points the whole language at ensures, which
walks straight into it — so the containment lands before the conversion, not after.

**The containment.** Refuse a return type that MIXES borrow and non-borrow
components, at both dispatch sites, rather than teach the audit to judge value
components in a borrow-carrying position. A cursor's sayable contract is its issued
borrows' owed types; a value claim belongs on a value-returning function, where
§5 point 4's "what you keep is what you ascribe" is enforced by a check that looks.

**BOTH sites, and the second is the one that matters after M27.** The declaration
path (`checkFn`) and the SEAL path (`checkRFnBody`) carry the same gate, so a
sealed λ had the same hole. Fixing only `checkFn` would have left it in the path
the endgame keeps.
-/

open Dllbc
open Dllbc.StdLemmas (len Le znots)

namespace Dllbc.Tests.S27Mixed

/-! The `ok`/`rejects` helpers retired with the `FnDef` subjects they took (M28
    ν). Every subject in this file is a program now, and `progOk`/`progRejects`
    take one directly — which is also why the two imported subjects below
    (`S6Call.toNatProg`, `S16Spec.swapS01`) read the same as the local ones. -/


/-! ## §A. The break, contained — b1's witnesses, now refused

    `a1lie` is b1's A1: a cursor returning the head borrow beside a FALSE claim
    (`Id Nat Z (S Z)`) discharged by a `Refl` that cannot inhabit it. It CHECKED
    before this commit. -/

def a1lie : Term := prog{
  fn head_lie (v : &mut List Nat, hi : Le (S Z) (len *v))
        -> Σ (x : &mut Nat) → Id Nat Z (S Z)
        { match v {
            Nil => botElim Unit hi,
            Cons(hd, tl) => Pair(&mut *hd, Refl)
        } };
  () }

example : progRejects a1lie "may not also carry VALUE components" = true := by native_decide

/-- b1's A5c, and **the control that makes the containment honest**: an HONEST
    claim in the same position is refused too.

    That is deliberate, not collateral. The position never judged anything, so
    acceptance there carried no information — a true claim was accepted for exactly
    the reason a false one was. Refusing both is what turns a silent lie into an
    explicit refusal; accepting the true one would mean the checker had started
    judging value components in a borrow-carrying position, which is the fix the
    containment declines to make. -/
def a5honest : Term := prog{
  fn head_true (v : &mut List Nat, hi : Le (S Z) (len *v))
        -> Σ (x : &mut Nat) → Id Nat Z Z
        { match v { Nil => botElim Unit hi, Cons(hd, tl) => Pair(&mut *hd, Refl) } };
  () }

example : progRejects a5honest "may not also carry VALUE components" = true := by native_decide

/-! ## §B. The two controls that isolate `hasBorrowT` as the whole cause

    b1's A2 and A5a. Neither changes here, and that is the point: the containment
    touches only the mixed position, so the rules that were already looking are
    left exactly as they were. -/

-- A2: the SAME false claim with no borrow in the return type. The pin-and-check
-- path runs, and always did.
def a2lie : Term := prog{
  fn val_lie (v : &mut List Nat, hi : Le (S Z) (len *v))
        -> Σ (x : Nat) → Id Nat Z (S Z)
        { Pair(Z, Refl) };
  () }
example : progRejects a2lie "does not have return type" = true := by native_decide

-- A5a: the direct route to the same absurdity, refused as it always was.
def a5direct : Term := prog{
  fn direct () -> Bot { znots Z Refl };
  () }
example : progRejects a5direct "does not have return type" = true := by native_decide

/-! ## §C. Not over-broad: the shapes the corpus actually uses still check

    A containment that refused real cursors would be a regression wearing a fix's
    clothes. The two live shapes are a bare borrow and a Σ of borrows — `nth`'s and
    `nth2`'s — and both are all-borrow, so neither mixes. -/

def bare : Term := prog{
  fn bare (v : &mut List Nat, hi : Le (S Z) (len *v)) -> &mut Nat
        { match v { Nil => botElim Unit hi, Cons(hd, tl) => &mut *hd } };
  () }
example : progOk bare = true := by native_decide

def twoBorrows : Term := prog{
  fn two (v : &mut List Nat, hi : Le (S Z) (len *v))
        -> Σ (x : &mut Nat) → &mut List Nat
        { match v {
            Nil => botElim Unit hi,
            Cons(hd, tl) => Pair(&mut *hd, &mut *tl)
        } };
  () }
example : progOk twoBorrows = true := by native_decide

-- …and the whole corpus is unmoved: the full suite is green with the refusal in,
-- which is the claim `retMixesBorrow` has to earn — it must catch the break
-- without catching a single thing the corpus says today.

/-! ## §D. THE SEAL PATH HAS THE SAME HOLE, and this is the half that survives M27

    `checkRFnBody` gates its value check on `hasBorrowT ret` exactly as `checkFn`
    does, so a sealed λ ascribed at a mixed Π was unjudged in the same way. After
    M27 the seal is the ONLY audit site, so a containment that fixed only the
    declaration path would have fixed only the half being deleted. -/

def mixedSeal : Term := pure{ Π (v : &mut List Nat) → Σ (x : &mut Nat) → Id Nat Z (S Z) }

def sealProg : Term := prog{
  let f = (λ(v : &mut List Nat) { match v { Nil => (), Cons(hd, tl) => Pair(&mut *hd, Refl) } } : %mixedSeal);
  () }

example : progRejects sealProg "may not also carry VALUE components" = true := by native_decide

-- Not vacuous: an all-borrow ascription in the same position is accepted, so the
-- refusal is about the MIXTURE and not about sealing a cursor at all.
def borrowSeal : Term := pure{ Π (v : &mut List Nat) → &mut List Nat }
def sealOk : Term := prog{ let f = (λ(v : &mut List Nat) { v } : %borrowSeal); () }
example : progOk sealOk = true := by native_decide

/-! ## §E. THE SECOND CONTAINMENT — a lie in a PARAMETER'S OWED TYPE

    b1 found a second closed `Bot`, and it is inside the first containment's
    blessing: the return type here is ALL borrow, so §A's refusal has nothing to
    say about it. The lie hides one level down, in what the parameter owes back.

    §6.1 exempts a borrow CONSUMED INTO THE RESULT from the payload audit — "being
    issued is its exemption" — and that is correct about the payload: a borrow that
    left in the result has no payload here to check. But the exemption takes the
    OWED TYPE with it, and the caller's group end then MINTS the captured loan's
    release AT that type. So the callee is excused from proving the claim and the
    caller receives it as fact. Neither end looks.

    **Refused rather than repaired**, on the same reasoning as §A: option (i) —
    "check the release against the owed type" — is vacuous as stated, since a
    freshly minted σ trivially has the type it was minted at. Making the unjudged
    position unwritable is the honest move. A parameter passed onward into the
    result owes back the type it was lent. -/

def e1lie : Term := prog{
  fn through_lie (v : &mut (s : List Nat ~> Id Nat Z (S Z))) -> &mut List Nat
        { v };
  () }
example : progRejects e1lie "would be checked by nobody" = true := by native_decide

/-- The isolating control: the SAME body and the SAME consumed-into-result shape
    with a TRIVIAL owed type is accepted. So the refusal is about the claim, not
    about handing a borrow onward — which is `through`'s whole job. -/
def e2trivial : Term := prog{
  fn through_ok (v : &mut List Nat) -> &mut List Nat { v };
  () }
example : progOk e2trivial = true := by native_decide

/-! ### E3. Measured before it shipped: the corpus's two non-trivial owed types

    The containment was run against the corpus before being committed, because a
    refusal that caught a load-bearing owed type would be a design conversation
    rather than a containment. Of **142 borrow parameters** in the corpus, exactly
    **two** carry a non-trivial owed type — and both are Unit-returning, so neither
    is ever consumed into a result and the exemption cannot fire on them. Their
    owed types are checked today and still are.

    That is the whole reason this ships as a containment: the position it closes is
    one the corpus never used, and the two places that DO state a rich owed type
    state it where the audit runs. -/

-- `to_nat (v : &mut (Bool ~> Nat))` — the type-changing ↝, S6Call's own subject.
example : progOk Tests.S6Call.toNatProg = true := by native_decide
-- `swapS01`, whose owed type is a Σ carrying a length-preservation proof.
example : progOk Tests.S16Spec.swapS01 = true := by native_decide

/-! ## §F. THE THIRD CONTAINMENT — reading a sealed borrow-taking function

    From c1's curry probe (branch `curryprobe`, `S27CurryProbe.lean` §G3, addendum
    `9b374c7f`), whose witnesses these controls are drawn from and credited to. It
    generalizes `S26Rec` §M in two ways that change the pricing:

    **1. No recursor is required.** §M found it on `ih` and read the trigger as
    something about induction hypotheses. It is not: the trigger is a σ whose Π is
    **borrow-moded**, which therefore has no `Val` (M26-C's founding fact) and lives
    in `fsig` alone, where `indexKindV`'s `.sym` case — which consults `sctx` — finds
    nothing and takes the move default. Any ordinary sealed borrow-taking function
    bound to a slot reproduces it.

    **2. It is not confined to the safe direction.** §M's case was reject-vs-run,
    which costs expressiveness and nothing else. c1 exhibits a program **both
    machines ACCEPT** whose final Ωs do not correspond — `f = ⊥` on the checking
    side, the λ-spine on the executing one. That is a simulation break on an
    accepted program: precisely what `S9Diff`'s whole-program assertions exist to
    catch, arriving where they cannot see it.

    So the position is made unwritable, checking-side only — the executing machine
    holds a real function value and copies it correctly, and refusing there would
    break running programs to protect a checker.

    **AND THE CONTAINMENT HAS SINCE GRADUATED INTO THE MODEL** (M27 α.2). The two
    paragraphs above are the record of what was believed and why, and both are
    still true of the mechanism — but the rule no longer keys on the mechanism.
    The ratified model is that **functions are reached by NAME**: the binding a
    declaration creates IS the name (§8), calling where bound and passing as an
    argument are name-uses, and the one move the model forbids is reading a
    function out of its slot into a SECOND binding, which is what turns it from a
    name into a value. So the key is now being a function at all, and the
    borrow-free case flips with it — c1 measured that one as SOUND on both
    machines (§G3a), and it is refused anyway, because soundness was never what
    made it wrong. What is left of "teach `indexKindV` about `fsig`" is §12 open
    8, which the model may simply not need. -/

def fSeal : Term := pure{ Π (v : &mut List Nat) → Unit }

-- F1. A sealed borrow-taking function, NO recursor anywhere, bound to a second
-- slot. This is the shape c1's §G3b has both machines accepting with different Ωs.
def f1read : Term := prog{
  let f = (λ(v : &mut List Nat) { () } : %fSeal);
  let g = f;
  () }
-- The needle moved with the rule: what is refused is no longer "a sealed
-- borrow-taking function" but a function, full stop.
example : progRejects f1read "reached by NAME" = true := by native_decide

-- F2. **THE ONE THAT FLIPPED, and it is the clearest statement of what changed.**
-- ~~The isolating control: a BORROW-FREE sealed function bound to a second slot is
-- ACCEPTED, because a borrow-free Π has a `Val`, its σ lands in `sctx` too, and
-- `indexKindV` can see it — so the refusal is about the missing value form, not
-- about functions.~~ **OVERTAKEN by α.2.** Every word of that is still true of the
-- MECHANISM, and c1 measured this program as copying correctly on both machines.
-- It is refused now anyway, and the reason is the model rather than a defect:
-- functions are names, and this reads one into a second slot. The refusal it gets
-- is the same one F1 gets, which is the point — there is no longer a class here to
-- be isolated from.
def gSeal : Term := pure{ Π (x : Nat) → Nat }
def f2read : Term := prog{
  let f = (λ(x : Nat) { x } : %gSeal);
  let g = f;
  () }
example : progRejects f2read "reached by NAME" = true := by native_decide

-- F2b. The ISOLATING CONTROL that survives, and it has to be a different one now:
-- an ordinary value in a second slot is still an ordinary read. So F1/F2 are about
-- functions and not about second bindings.
def f2data : Term := prog{
  let f = 3;
  let g = f;
  () }
example : progOk f2data = true := by native_decide

-- F3. And it does not touch CALLING, which under the model is the headline rather
-- than a caveat: calling where bound is a NAME-use. `.callV` locates its callee
-- rather than moving it (M26-E), so it never reaches the read rule at all.
def f3call : Term := prog{
  let f = (λ(v : &mut List Nat) { () } : %fSeal);
  let x = Cons(1, Nil);
  let b = &mut x;
  f(b);
  () }
example : progOk f3call = true := by native_decide

end Dllbc.Tests.S27Mixed
