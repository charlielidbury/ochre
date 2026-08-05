import Dllbc.Program
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.DeclMacro
import Dllbc.ProgMacro

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

def rejects (d : Decl) (needle : String) (table : List Decl := [d]) : Bool :=
  match checkFn table d with | .ok _ => false | .error e => strContains e needle

def ok (d : Decl) (table : List Decl := [d]) : Bool :=
  match checkFn table d with | .ok _ => true | .error _ => false

/-! ## §A. The break, contained — b1's witnesses, now refused

    `a1lie` is b1's A1: a cursor returning the head borrow beside a FALSE claim
    (`Id Nat Z (S Z)`) discharged by a `Refl` that cannot inhabit it. It CHECKED
    before this commit. -/

def a1lie : Decl :=
  decl{ fn head_lie (v : &mut List Nat, hi : Le (S Z) (len *v))
        -> Σ (x : &mut Nat) → Id Nat Z (S Z)
        { match v {
            Nil => botElim Unit hi,
            Cons(hd, tl) => Pair(&mut *hd, Refl)
        } } }

example : rejects a1lie "may not also carry VALUE components" = true := by native_decide

/-- b1's A5c, and **the control that makes the containment honest**: an HONEST
    claim in the same position is refused too.

    That is deliberate, not collateral. The position never judged anything, so
    acceptance there carried no information — a true claim was accepted for exactly
    the reason a false one was. Refusing both is what turns a silent lie into an
    explicit refusal; accepting the true one would mean the checker had started
    judging value components in a borrow-carrying position, which is the fix the
    containment declines to make. -/
def a5honest : Decl :=
  decl{ fn head_true (v : &mut List Nat, hi : Le (S Z) (len *v))
        -> Σ (x : &mut Nat) → Id Nat Z Z
        { match v { Nil => botElim Unit hi, Cons(hd, tl) => Pair(&mut *hd, Refl) } } }

example : rejects a5honest "may not also carry VALUE components" = true := by native_decide

/-! ## §B. The two controls that isolate `hasBorrowT` as the whole cause

    b1's A2 and A5a. Neither changes here, and that is the point: the containment
    touches only the mixed position, so the rules that were already looking are
    left exactly as they were. -/

-- A2: the SAME false claim with no borrow in the return type. The pin-and-check
-- path runs, and always did.
def a2lie : Decl :=
  decl{ fn val_lie (v : &mut List Nat, hi : Le (S Z) (len *v))
        -> Σ (x : Nat) → Id Nat Z (S Z)
        { Pair(Z, Refl) } }
example : rejects a2lie "does not have return type" = true := by native_decide

-- A5a: the direct route to the same absurdity, refused as it always was.
def a5direct : Decl := decl{ fn direct () -> Bot { znots Z Refl } }
example : rejects a5direct "does not have return type" = true := by native_decide

/-! ## §C. Not over-broad: the shapes the corpus actually uses still check

    A containment that refused real cursors would be a regression wearing a fix's
    clothes. The two live shapes are a bare borrow and a Σ of borrows — `nth`'s and
    `nth2`'s — and both are all-borrow, so neither mixes. -/

def bare : Decl :=
  decl{ fn bare (v : &mut List Nat, hi : Le (S Z) (len *v)) -> &mut Nat
        { match v { Nil => botElim Unit hi, Cons(hd, tl) => &mut *hd } } }
example : ok bare = true := by native_decide

def twoBorrows : Decl :=
  decl{ fn two (v : &mut List Nat, hi : Le (S Z) (len *v))
        -> Σ (x : &mut Nat) → &mut List Nat
        { match v {
            Nil => botElim Unit hi,
            Cons(hd, tl) => Pair(&mut *hd, &mut *tl)
        } } }
example : ok twoBorrows = true := by native_decide

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
  let f = seal(λ(v) { match v { Nil => (), Cons(hd, tl) => Pair(&mut *hd, Refl) } },
               %mixedSeal);
  () }

example : progRejects sealProg "may not also carry VALUE components" = true := by native_decide

-- Not vacuous: an all-borrow ascription in the same position is accepted, so the
-- refusal is about the MIXTURE and not about sealing a cursor at all.
def borrowSeal : Term := pure{ Π (v : &mut List Nat) → &mut List Nat }
def sealOk : Term := prog{ let f = seal(λ(v) { v }, %borrowSeal); () }
example : progOk sealOk = true := by native_decide

end Dllbc.Tests.S27Mixed
