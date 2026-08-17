import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Boundaries

/-!
# Surface sugar — matched EXPRESSIONS, and the singleton-constructor `let`

Two additions to the surface (M34), both entirely in the macro layer: the kernel
has no idea either of them happened, and each is asserted here against the
spelling it replaces.

  * **(i) `match E { … }`** where `E` is not a plain local is
    `let §m = E ; match §m { … }`. The old grammar took an `ident` and refused
    every one that was not a bound runtime variable, so the result of a call had
    to be `let`-bound by hand before it could be matched.
  * **(ii) `let C(a, b) = E ; rest`** is `match E { C(a, b) => rest }` — the rest
    of the block moves inside the arm. Nothing at the surface asks whether `C` is
    the scrutinee type's ONLY constructor: the desugaring is unconditional and
    §9's exhaustiveness check refuses the ones that are not, with the error it
    already had.

**What this file must protect is the path the sugar does NOT take.** A match on a
plain variable is unchanged byte for byte, and that is a semantic requirement
rather than a tidiness one: matching a BORROW variable reborrows — the arm
binders are loans into the scrutinee's payload — so binding the scrutinee to a
fresh slot first would move it, and `vecPush`'s two-field update and the money
test that guards it would stop meaning what they mean. The goldens below assert
`Term` EQUALITY, not convertibility, because the claim is that the elaborator
produces the same term and not merely an equivalent one.
-/

open Dllbc
open Dllbc.Term (nat)

namespace Dllbc.Tests.Sugar

/-! ## (i) A plain variable takes the old path, and the golden says so

    The scrutinee of the match below is `b`, a borrow. The hand-written term has
    the `.matchE` header sitting DIRECTLY on `b`'s slot with nothing between them
    — no interposed `.letIn`, no fresh id — which is the whole content of "the
    sugar does not fire here". -/

def borrowMatch : Term := prog{
  let v = Pair(0, 1);
  let b = &m v;
  match b { Pair(l, r) => { *l := 1; () } } }

def borrowMatchHand : Term :=
  .letIn ⟨0, "v"⟩ (.ctorApp "Pair" [nat 0, nat 1])
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "v"⟩))
      (.matchE ⟨1, "b"⟩ none
        [.mk "Pair" [⟨2, "l"⟩, ⟨3, "r"⟩]
          (.assign (.deref (.var ⟨2, "l"⟩)) (nat 1) .unit)]))

example : borrowMatch = borrowMatchHand := by rfl

-- **Parenthesized, it is still the plain path.** Two characters is not a licence
-- to change a program's ownership, so `elabScrut` strips grouping before asking
-- whether it has an identifier — otherwise `match (b) { … }` would move what
-- `match b { … }` reborrows.
example : prog{
    let v = Pair(0, 1);
    let b = &m v;
    match (b) { Pair(l, r) => { *l := 1; () } } } = borrowMatchHand := by rfl

-- The same for the branch-equation form (M23), whose scrutinee became a `uterm`
-- with the plain one's. Its equation binder still lands at the id it always did,
-- because the plain-variable path does not touch the counter.
def eqnMatch : Term := prog{
  let n = 0;
  match h : n { Z => (), S(m) => () } }

def eqnMatchHand : Term :=
  .letIn ⟨0, "n"⟩ (nat 0)
    (.matchE ⟨0, "n"⟩ (some ⟨1, "h"⟩)
      [.mk "Z" [] .unit, .mk "S" [⟨2, "m"⟩] .unit])

example : eqnMatch = eqnMatchHand := by rfl

-- An identifier that is not a bound runtime local is still an ERROR and not a
-- fresh-slot binding — the sugar is for what the grammar could not spell, and an
-- identifier was always spellable. (Stated as a comment for the same reason
-- `S15Elab` states its unbound-name case that way: the assertion is that the
-- program does not COMPILE, which needs the exact macro message to write down.
-- `prog{ let x = 0; match Nat { Z => () } }` fails at macro time with
-- "match scrutinee 'Nat' is not a bound runtime variable".)

/-! ## (i) An expression scrutinee, which the old grammar could not spell -/

-- A constructor application, matched where it stands.
def ctorScrut : Term := prog{
  let out = match Pair(1, 2) { Pair(a, b) => a };
  () }

-- A CALL's result — the shape the corpus is full of, and the reason for the
-- sugar: `SplitA(f2, m2, hfuel, p, &m *tl)` returns a five-deep Σ nest and every
-- one of its use sites had to name an intermediate.
def callScrut : Term := prog{
  fn Mk (x : Nat) -> Σ (a : Nat). Nat { Pair(x, x) };
  let out = match Mk(2) { Pair(a, b) => b };
  () }

-- The near-miss capture test. `§m` is the sugar's binder and no program can
-- write one (`checkBinder` refuses the whole `§` namespace), so what is left to
-- check is that the binder the sugar mints does not disturb the ones a program
-- CAN write. `m` here is read from inside the arm, i.e. from under the sugar's
-- `let` — and since M32 R1 resolves Ω by NAME with newest-wins, a fresh binder
-- spelled `m` would shadow it and this would answer 1 instead of 7.
def noCapture : Term := prog{
  let m = 7;
  let out = match Pair(1, 2) { Pair(a, b) => m };
  () }

-- Two of them nested, so both `§m` slots are alive in one Ω at once.
def nestedScrut : Term := prog{
  let out = match Pair(1, 2) { Pair(a, b) => match Pair(3, b) { Pair(c, d) => d } };
  () }

-- The machinery is VISIBLE in Ω, as `if`'s `__if` slot has always been: the
-- sugar's `let` is an ordinary binding and leaves an ordinary entry, holding ⊥
-- because the pattern binders moved the payload out of it. Asserted rather than
-- hidden, so that a program whose final Ω is checked knows what to expect.
example : progOk ctorScrut = true := by native_decide
example : progRunsTo ctorScrut
    [("§m", .bot), ("a", Val.nat 1), ("b", Val.nat 2), ("out", Val.nat 1)] = true := by
  native_decide

example : progOk callScrut = true := by native_decide
example : progRuns callScrut = true := by native_decide

example : progOk noCapture = true := by native_decide
example : progRunsTo noCapture
    [("m", Val.nat 7), ("§m", .bot), ("a", Val.nat 1), ("b", Val.nat 2),
     ("out", Val.nat 7)] = true := by native_decide

example : progOk nestedScrut = true := by native_decide
example : progRunsTo nestedScrut
    [("§m", .bot), ("a", Val.nat 1), ("b", Val.nat 2), ("§m", .bot),
     ("c", Val.nat 3), ("d", Val.nat 2), ("out", Val.nat 2)] = true := by native_decide

-- Symbolically the call's result is a fresh σ, the match splits its pair, and
-- `out` is the second component — which is the whole point of matching a call
-- where it stands. (`tailEnv` drops the `fn`'s own Ω entry.)
example : tailEnv callScrut
    [("§m", .bot), ("a", Val.sym 0), ("b", Val.sym 1), ("out", Val.sym 1)] = true := by
  native_decide

-- **The escaped-identifier route is closed, and closed the way `§σ`'s is** (the
-- M32 R1 battery in `KernelFloor`, `S32Sigma`). An ordinary Lean `ident` cannot
-- contain `§`; an escaped one can, and `Name.toString` re-escapes it — so the
-- binder this program writes is literally named `«§m»`, guillemets and all,
-- which is a different name from `§m` and not in the reserved namespace at all.
-- The read from inside the arm therefore still finds 7. Measured rather than
-- argued, because `reservedBinder`'s guard never fires on this input.
def escapedScrut : Term := prog{
  let «§m» = 7;
  let out = match Pair(1, 2) { Pair(a, b) => «§m» };
  () }

example : progRunsTo escapedScrut
    [("«§m»", Val.nat 7), ("§m", .bot), ("a", Val.nat 1), ("b", Val.nat 2),
     ("out", Val.nat 7)] = true := by native_decide

/-! ## (ii) `let C(a, b) = E ;` — the pyramid, flattened

    The claim is EQUALITY with the nested match it replaces, not convertibility.
    The binder ids are minted from the same counter at the same point — the rest
    of the block is elaborated exactly where the arm body would have been — so a
    `let Pair(…) = … ;` chain is literally the pyramid, and a migration of the
    corpus cannot change a single checked term. -/

def flatLet : Term := prog{
  let p = Pair(1, 2);
  let Pair(a, b) = p;
  () }

def pyramidLet : Term := prog{
  let p = Pair(1, 2);
  match p { Pair(a, b) => () } }

example : flatLet = pyramidLet := by rfl

-- Three deep, which is where the difference starts to be worth something: the
-- flat spelling never indents and never accumulates a closing `}}}}`.
def flat3 : Term := prog{
  let p = Pair(1, Pair(2, Pair(3, 4)));
  let Pair(a, z1) = p;
  let Pair(b, z2) = z1;
  let Pair(c, d) = z2;
  let out = d;
  () }

def pyramid3 : Term := prog{
  let p = Pair(1, Pair(2, Pair(3, 4)));
  match p { Pair(a, z1) => match z1 { Pair(b, z2) => match z2 { Pair(c, d) => {
    let out = d;
    () } } } } }

example : flat3 = pyramid3 := by rfl
example : progOk flat3 = true := by native_decide
example : progRuns flat3 = true := by native_decide

-- Composing with (i): the scrutinee may be a call, and then the two sugars are
-- one line where the surface used to need three.
def letCall : Term := prog{
  fn Mk (x : Nat) -> Σ (a : Nat). Nat { Pair(x, x) };
  let Pair(a, b) = Mk(2);
  let out = b;
  () }

example : progOk letCall = true := by native_decide

example : progRunsTo flat3
    [("p", .bot), ("a", Val.nat 1), ("z1", .bot), ("b", Val.nat 2), ("z2", .bot),
     ("c", Val.nat 3), ("d", Val.nat 4), ("out", Val.nat 4)] = true := by native_decide
-- The pyramid twin runs to the same thing, and does so for the strongest reason
-- available: it is the same term (`flat3 = pyramid3` above).
example : runProgram flat3 = runProgram pyramid3 := by rfl

example : tailEnv letCall
    [("§m", .bot), ("a", Val.sym 0), ("b", Val.sym 1), ("out", Val.sym 1)] = true := by
  native_decide

/-! ## (ii) at the flagship: `vecPush` respelled

    §4.2's dependent flagship is a borrow-mode match over a Σ, and it is the test
    the sugar had to be built around: the arm binders `l` and `xs` are LOANS into
    the payload behind `v`, so a desugaring that bound the scrutinee to a fresh
    slot would move the pair and the two writes would land somewhere nobody can
    see. The respelling is asserted EQUAL to `vecPush` itself — same term, so the
    money test below is testing the same program it always was. -/

def vecPushLet : Term := prog{
  fn Push (e : Nat, v : &mut (Σ (l : Nat). %Tests.S5Bound.vecFT Nat l)) -> Unit {
    let Pair(l, xs) = v;
    *xs := Pair(e, *xs);
    *l := S(*l);
    () };
  () }

example : vecPushLet = Tests.S5Bound.vecPush := by rfl
example : progOk vecPushLet = true := by native_decide

-- THE MONEY TEST, in the new spelling: forget `*l := S(*l)` and the second field
-- is checked against the stuck `VecF Nat σₗ`, which the concrete `Pair` cannot
-- inhabit. Rejected, as it is in `Boundaries`.
example : progRejects (prog{
    fn Push (e : Nat, v : &mut (Σ (l : Nat). %Tests.S5Bound.vecFT Nat l)) -> Unit {
      let Pair(l, xs) = v;
      *xs := Pair(e, *xs);
      () };
    () })
  "owed type" = true := by native_decide

/-! ## The macro knows nothing about types, and §9 is what refuses the rest

    `let Cons(h, t) = l ;` desugars unconditionally to a one-branch match, and the
    exhaustiveness check the kernel has had since §9 refuses it — by name, and for
    the reason that is actually true of it. That is the whole argument for not
    asking the question at the surface: no constructor table in the macro layer,
    no second definition of which types have one constructor, and nothing to keep
    in step when the basis grows. -/

def headByLet : Term := prog{
  fn Head (l : List Nat) -> Nat { let Cons(h, t) = l; h };
  () }

-- The message in full, so that what a user of the sugar actually reads is pinned
-- and not merely assumed:
--
--   match: non-exhaustive — no branch for constructor 'Nil' of the scrutinee's type
--
-- It names the constructor that is missing, which is the actionable half. It also
-- says "match" for something written as a `let`, which is the one place the
-- desugaring shows through; the alternative is a surface-level constructor table,
-- and this is the cheaper leak.
example : progRejects headByLet
  "match: non-exhaustive — no branch for constructor 'Nil'" = true := by native_decide

-- The one-constructor case is accepted by the same route, with no special case
-- anywhere: `Pair` is Σ's only constructor, so the one-branch match IS exhaustive.
example : progOk (prog{
    fn Snd (p : Σ (a : Nat). Nat) -> Nat { let Pair(x, y) = p; y };
    () }) = true := by native_decide

end Dllbc.Tests.Sugar
