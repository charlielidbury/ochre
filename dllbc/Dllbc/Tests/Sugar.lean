import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas

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

end Dllbc.Tests.Sugar
