import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.DeclMacro
import Dllbc.Tests.S9Diff
import Dllbc.Migrate

/-!
# §17 test suite — the cursor family, after the backward specs retired

**What this file used to be, and what happened to it (M27-P2).** §17 was the
declared-backward-spec suite: the sound reincarnation of M8's `constrained` wire,
where a borrow-returning function carried a `FnDef.back` — a pure function from the
issued borrows' surrendered values to the captured loan's release — checked
against its body at the callee and used at the caller to compute the release
instead of minting an existential. M23 retired the architecture (its quicksort
declares ZERO backs, deliberately) and M27 deleted the mechanism, so what this
file tests now is the cursor family itself: `nth`, `nth2` and the `swapS` built on
them, checked as ordinary ensures-free functions, plus the opacity that was always
the default.

**Where the deleted claims went**, so a reader does not mistake this for lost
coverage:

* The **caller-side precision** — that a caller of a back-carrying `swapS`
  recovered the exact swapped list in CHECKING mode — is gone BY DESIGN. §5 point
  4 of `combining-fns.md`: what you keep across a boundary is what you ascribe,
  and `-> &mut Nat` ascribes nothing about the payload. Opacity is now the only
  behaviour, which is what `throughOpaque` below always tested.
* The **claim itself survives, restated as an ensures**, and M23 wrote it before
  this deletion was contemplated: `S23Direct.setAt` is `nth`-plus-write with the
  relationship in the RETURN TYPE (`Id (List Nat) (*v) (set i x (old *v))`) and
  `swapAt` is `swapS` the same way (`Id (List Nat) (*v) (swapL i j (old *v))`) —
  the same two model functions, `set` and `swapL`, moved out of the `back` field
  and into the contract, with their own lie twins. A caller learns strictly more
  than the backward spec gave it: a propositional equation it can rewrite along,
  rather than a value the group-end happened to compute. `Tests/S27Dispose.lean`
  §C2 asserts that pair on both paths.
* The **lying-back control** (`throughLie`, which declared `back = λ r. Cons(1,Nil)`
  for a body returning its argument) tested the back mechanism itself and retired
  with it. A test of a deleted feature is not coverage.
-/

open Dllbc

namespace Dllbc.Tests.S17Spec

/-! ## `through` — the borrow that comes straight back out -/

-- `through (b) = b`. It once carried `back = λ (r). r` (the release IS the
-- surrendered value, M8's arc closed); with the mechanism gone this is simply a
-- borrow-returning function, and what a caller learns is its type.
def throughOk : FnDef :=
  decl{ fn through (b : &mut List Nat) -> &mut List Nat
        { b } }
example : Migrate.progOkOf throughOk = true := by native_decide

-- The caller writes through the returned borrow and then demands the owner. With
-- the backward spec this recovered the WRITTEN value (`y = Cons(9, Nil)`); without
-- it the group end mints a fresh existential, which is §6.2's precision loss and
-- is now the only behaviour. The assertion below is the OPACITY one — the same
-- shape S7Group's spec-less `through` always had.
def caller : FnDef :=
  decl{ fn caller () -> Unit {
    let x = Cons(1, Nil); let b = &mut x;
    let r = through(b);
    *r := Cons(9, Nil);
    let y = x;
    () } }
def vlist9 : Val := .ctor "Cons" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "Z" []]]]]]]]]], .ctor "Nil" []]
example : (match Migrate.progEnvsOfT [throughOk, caller] caller with
  | [.ok env] => match env.lookup "y" with | some (.sym _) => true | _ => false
  | _ => false) = true := by native_decide
-- Not vacuous, and this is the pair that keeps the deletion honest: the EXECUTING
-- machine still writes the value and still hands back `Cons(9, Nil)`. What the
-- deletion removed is the CHECKER's ability to know it, which is exactly §5 point
-- 4 — opacity is a fact about what was ascribed, never about what happens.
example : (match Dllbc.Tests.S9Diff.runExec [throughOk] caller.body with
  | .ok env => env.lookup "y" == some vlist9
  | .error _ => false) = true := by native_decide

/-! ## Spec-less stays opaque (no regression) -/

-- Same body, no `back`: the caller's recovery is a fresh existential (a `sym`),
-- exactly as in M9 — the spec-carrying end is opt-in.
def throughOpaque : FnDef :=
  decl{ fn through (b : &mut List Nat) -> &mut List Nat { b } }
example : (match Migrate.progEnvsOfT [throughOpaque, { caller with name := "c2" }] { caller with name := "c2" } with
  | [.ok env] => match env.lookup "y" with | some (.sym _) => true | _ => false
  | _ => false) = true := by native_decide

/-! ## The cursor family: `nth`, `nth2`, and the `swapS` built on them

    These three carried the composing backward specs — `set i r s`, then
    `set i r₁ (set j r₂ s)` composing it, then `swapL i j s` composing that with no
    surrendered arguments since `swapS` returns Unit — and the composition along a
    call chain was §17's headline. The functions are unchanged; only the specs are
    gone, so what they check now is that the cursor bodies themselves are
    well-typed: the `Le`-bounded descent, the field reborrows, the `botElim` on the
    impossible `Nil` path.

    The composing-spec claim is not re-expressed here. Its ensures-style successor
    is `S23Direct.swapAt`, which states the whole swap as one equation over the
    exit snapshot instead of as three specs that compose — and composing was the
    old architecture's answer to a question the ensures does not ask. -/

open Dllbc.StdLemmas (set swapL)

def nthS : FnDef :=
  decl{ fn nth [i] (v : &mut List Nat, i : Nat, p : Le (S i) (len *v)) -> &mut Nat
        { match v {
            Nil => botElim Unit p,
            Cons(hd, tl) => match i {
              Z => &mut *hd,
              S(k) => nth(&mut *tl, k, p)
            }
        } } }

def nth2S : FnDef :=
  decl{ fn nth2 [i] (v : &mut List Nat, i : Nat, j : Nat,
                 pij : Le (S i) j, p2 : Le (S j) (len *v)) -> Σ (x : &mut Nat) → &mut Nat
        { match v {
            Nil => botElim Unit p2,
            Cons(hd, tl) => match i {
              Z => match j {
                Z => botElim Unit pij,
                S(jjv) => Pair(&mut *hd, nth(&mut *tl, jjv, p2))
              },
              S(k) => match j {
                Z => botElim Unit pij,
                S(jj2) => nth2(&mut *tl, k, jj2, pij, p2)
              }
            }
        } } }

def swapSN : FnDef :=
  decl{ fn swapS (v : &mut List Nat, i : Nat, j : Nat,
                  pij : Le (S i) j, p2 : Le (S j) (len *v)) -> Unit
        { let pr = nth2(v, i, j, pij, p2);
          match pr { Pair(ei, ej) => {
            let t = *ei;
            *ei := *ej;
            *ej := t;
            () } } } }

example : Migrate.progOkOf nthS = true := by native_decide
example : Migrate.progOkOf nth2S ([nthS, nth2S]) = true := by native_decide
example : Migrate.progOkOf swapSN ([nthS, nth2S, swapSN]) = true := by native_decide

-- The caller's CHECKING-mode view is now opaque — `swapS` promises only `Unit`,
-- so `y` is a fresh existential. This is the deletion's whole visible cost, and
-- the executing differential below is what says the cost is in knowledge and not
-- in behaviour.
def spcBody : Term := prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &mut x;
  swapS(b, 0, 2, (), ());
  let y = x;
  () }
def spcCaller : FnDef := decl{ fn spc () -> Unit = %spcBody }
def vlist321 : Val := .ctor "Cons" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "Z" []]]],
  .ctor "Cons" [.ctor "S" [.ctor "S" [.ctor "Z" []]], .ctor "Cons" [.ctor "S" [.ctor "Z" []], .ctor "Nil" []]]]
example : (match Migrate.progEnvsOfT [nthS, nth2S, swapSN, spcCaller] spcCaller with
  | [.ok env] => match env.lookup "y" with | some (.sym _) => true | _ => false
  | _ => false) = true := by native_decide
-- …and the program really does swap: [1,2,3] ends [3,2,1] when RUN. The checker
-- stopped being able to say so; the machine never stopped doing it.
example : (match Dllbc.Tests.S9Diff.runExec [nthS, nth2S, swapSN] spcBody with
  | .ok env => env.lookup "y" == some vlist321
  | .error _ => false) = true := by native_decide

end Dllbc.Tests.S17Spec
