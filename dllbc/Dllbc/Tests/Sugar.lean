import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Boundaries

/-!
# Surface sugar — matched EXPRESSIONS, the singleton-constructor `let`, nested patterns

Three additions to the surface (M34), all entirely in the macro layer: the kernel
has no idea any of them happened, and each is asserted here against the
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
  * **(iii) `Cons(Pair(k, v), tl) => …`** — a constructor in ARGUMENT position, in
    match arms and in (ii)'s `let` alike, is the fresh binder and the immediate
    inner match it stands for. Each arm still compiles alone: there is no
    cross-arm grouping and no pattern matrix, so deeper discrimination is an
    ordinary inner match and §9 checks it like any other.

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
-- identifier was always spellable.
--
-- **A macro refusal is assertable, and this is the corpus's first one.** It was
-- written as a comment when the sugar landed, on the ground that pinning it needs
-- the exact message (`KernelFloor` says the same of its unbound-name case). That
-- ground was wrong: `#guard_msgs` takes the exact message and compares it, which
-- is precisely what a refusal test should do — the message IS the deliverable, so
-- a test that does not read it is testing the wrong half.
/-- error: decl: match scrutinee 'Nat' is not a bound runtime variable -/
#guard_msgs in
example : Term := prog{ let x = 0; match Nat { Z => () } }

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
example : progRejects (prog defer_check {
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

def headByLet : Term := prog defer_check {
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

/-! ## (iii) A constructor in ARGUMENT position

    `Cons(Pair(k, v), tl) => …` reads a field of a field where it is meant, and is
    **exactly** the hand-written `Cons(§p, tl) => match §p { Pair(k, v) => … }` —
    same ids, same names, same `Term`. The twins below are written as `Term`s
    rather than as `prog{ }` because that hand-spelling is not writable: the
    intermediate's name is reserved, which is what makes the sugar hygienic and
    also what stops the twin from being source.

    **There is no cross-arm anything.** Each arm compiles on its own, DLLBC's match
    stays one arm per head constructor, and a nested pattern is an inner match that
    §9 checks for exhaustiveness like every other — so `Cons(Z, tl)` is not a
    partial arm awaiting a sibling, it is a one-branch match on a `Nat` and it is
    REJECTED. Asserted below, with the message the kernel already had. -/

def nestedArm : Term := prog{
  let l = Cons(Pair(1, 2), Nil);
  match l { Nil => (), Cons(Pair(kk, vv), tl) => { let out = vv; () } } }

def nestedArmHand : Term :=
  .letIn ⟨0, "l"⟩ (.ctorApp "Cons" [.ctorApp "Pair" [nat 1, nat 2], .ctorApp "Nil" []])
    (.matchE ⟨0, "l"⟩ none
      [.mk "Nil" [] .unit,
       .mk "Cons" [⟨1, "§p1"⟩, ⟨2, "tl"⟩]
         (.matchE ⟨1, "§p1"⟩ none
           [.mk "Pair" [⟨3, "kk"⟩, ⟨4, "vv"⟩]
             (.letIn ⟨5, "out"⟩ (.var ⟨4, "vv"⟩) .unit)])])

example : nestedArm = nestedArmHand := by rfl

-- **The id order is the whole of the rewrite**, and it is what the golden above
-- is really pinning: EVERY argument of the head takes its slot first (`§p1`, then
-- `tl`), and only then does the nested one mint what is inside it (`kk`, `vv`) —
-- because that is what a match arm does, binders from the counter and then the
-- body. Get it the other way round and the terms are still convertible and no
-- longer equal, which is the difference between a migration that cannot change a
-- checked term and one that has to be re-verified site by site.

/-! ### Three deep, and what a migration actually changes

    `deep3` is `flat3` above with its two intermediates unnamed. Same ids, slot
    for slot, same values — and two binder NAMES differ, `§p2`/`§p4` where the
    chain wrote `z1`/`z2`, because the nested spelling does not name what it does
    not use. That is the one thing a corpus site gains by moving to a nested
    pattern and the one thing it changes; both Ωs are written out below so the
    difference is on the page rather than in an argument. -/

def deep3 : Term := prog{
  let p = Pair(1, Pair(2, Pair(3, 4)));
  let Pair(a, Pair(b, Pair(c, d))) = p;
  let out = d;
  () }

def deep3Hand : Term :=
  .letIn ⟨0, "p"⟩
      (.ctorApp "Pair" [nat 1, .ctorApp "Pair" [nat 2, .ctorApp "Pair" [nat 3, nat 4]]])
    (.matchE ⟨0, "p"⟩ none
      [.mk "Pair" [⟨1, "a"⟩, ⟨2, "§p2"⟩]
        (.matchE ⟨2, "§p2"⟩ none
          [.mk "Pair" [⟨3, "b"⟩, ⟨4, "§p4"⟩]
            (.matchE ⟨4, "§p4"⟩ none
              [.mk "Pair" [⟨5, "c"⟩, ⟨6, "d"⟩]
                (.letIn ⟨7, "out"⟩ (.var ⟨6, "d"⟩) .unit)])])])

example : deep3 = deep3Hand := by rfl
example : progOk deep3 = true := by native_decide
-- `flat3`'s Ω, verbatim, with `z1`/`z2` replaced by the minted names and nothing
-- else touched — not even the ids, which the goldens above pin exactly.
example : progRunsTo deep3
    [("p", .bot), ("a", Val.nat 1), ("§p2", .bot), ("b", Val.nat 2), ("§p4", .bot),
     ("c", Val.nat 3), ("d", Val.nat 4), ("out", Val.nat 4)] = true := by native_decide

/-! ### The corpus's own shape, five deep, in all three spellings

    `SplitA`, `PartitionA`, `Partition` and `Ih` all return a five-component Σ
    nest, and every call site of them was the pyramid below. The migration took it
    in two steps and this is both of them, checked:

      * `pyramid5` → `chain5` is sugar (ii) and changes NOTHING — same ids, same
        names, `rfl`. Every one of the corpus's 57 flattened arms is this step.
      * `chain5` → `nest5` is sugar (iii) and drops the three intermediates. The
        ids are still the same, slot for slot, and `z1`/`z2`/`z3` are now
        `§p2`/`§p4`/`§p6` — the two Ωs below are the whole of that difference. -/

def pyramid5 : Term := prog{
  let p = Pair(1, Pair(2, Pair(3, Pair(4, 5))));
  match p { Pair(a, z1) => match z1 { Pair(b, z2) => match z2 { Pair(c, z3) =>
  match z3 { Pair(d, e) => {
    let out = e;
    () } } } } } }

def chain5 : Term := prog{
  let p = Pair(1, Pair(2, Pair(3, Pair(4, 5))));
  let Pair(a, z1) = p;
  let Pair(b, z2) = z1;
  let Pair(c, z3) = z2;
  let Pair(d, e) = z3;
  let out = e;
  () }

def nest5 : Term := prog{
  let p = Pair(1, Pair(2, Pair(3, Pair(4, 5))));
  let Pair(a, Pair(b, Pair(c, Pair(d, e)))) = p;
  let out = e;
  () }

example : pyramid5 = chain5 := by rfl
example : progOk nest5 = true := by native_decide

example : progRunsTo chain5
    [("p", .bot), ("a", Val.nat 1), ("z1", .bot), ("b", Val.nat 2), ("z2", .bot),
     ("c", Val.nat 3), ("z3", .bot), ("d", Val.nat 4), ("e", Val.nat 5),
     ("out", Val.nat 5)] = true := by native_decide
example : progRunsTo nest5
    [("p", .bot), ("a", Val.nat 1), ("§p2", .bot), ("b", Val.nat 2), ("§p4", .bot),
     ("c", Val.nat 3), ("§p6", .bot), ("d", Val.nat 4), ("e", Val.nat 5),
     ("out", Val.nat 5)] = true := by native_decide

/-! ### Borrow mode goes all the way down

    This is the case the whole design is answerable to. `match v { … }` on a `&mut`
    REBORROWS — the arm binders are loans into the payload, not copies of it — and
    the minted intermediate has to keep that true one level further in. It does,
    and for a reason worth naming rather than testing blindly: the intermediate is
    a plain variable, so the inner match takes sugar (i)'s plain-variable path, the
    `.matchE` header sits directly on its slot, and the loan chains. Had the sugar
    bound it to a fresh slot instead, the payload would have MOVED and the writes
    below would land on a copy nobody can see. -/

def nestedWrite : Term := prog{
  let t = Pair(0, Pair(0, 0));
  let b = &m t;
  let Pair(x, Pair(y, z)) = b;
  *x := 1;
  *y := 2;
  *z := 3;
  () }

example : progOk nestedWrite = true := by native_decide
-- All three writes landed in `t`, which is the assertion: the loans reached the
-- innermost field THROUGH the minted intermediate. `§p3` is the intermediate's
-- slot, ⊥ because its match moved the payload into `y` and `z`.
example : progRunsTo nestedWrite
    [("t", Val.ctor "Pair" [Val.nat 1, Val.ctor "Pair" [Val.nat 2, Val.nat 3]]),
     ("b", .bot), ("x", .bot), ("§p3", .bot), ("y", .bot), ("z", .bot)] = true := by
  native_decide

-- The corpus's own shape (`Boundaries`' cursor walks, `ArraySort`'s buckets): a
-- borrowed LIST whose elements are pairs, cleared through the borrow. The head
-- constructor is matched in reborrow mode and the element's fields are loans
-- reached through the intermediate — two levels of `&mut` from one pattern.
def clearHead : Term := prog{
  let l = Cons(Pair(7, 9), Nil);
  let b = &m l;
  match b {
    Nil => (),
    Cons(Pair(kk, vv), tl) => { *vv := 0; () }
  };
  () }

example : progOk clearHead = true := by native_decide
-- The value field is 0 and the KEY IS UNTOUCHED — the half that "it runs" would
-- miss, since a nested pattern reaching the wrong loan would still run.
example : progRunsTo clearHead
    [("l", Val.ctor "Cons" [Val.ctor "Pair" [Val.nat 7, Val.nat 0], Val.nil]),
     ("b", .bot)] = true := by native_decide

/-! ### …and the money test survives the respelling

    `vecPush` with a second coupled field, destructured in ONE pattern. `n` is a
    running count, `l` the vector's length and `xs` its payload; all three are
    loans into the same `&mut`, and the second is what the dependent type is
    indexed by. Forget `*l := S(*l)` and the concrete `Pair` is checked against the
    stuck `VecF Nat σₗ`, exactly as in `Boundaries` — the rejection is unchanged by
    the pattern being nested, because the term is what it always was. -/

def vecPushNested : Term := prog{
  fn Push (e : Nat, v : &mut (Σ (n : Nat). Σ (l : Nat). %Tests.S5Bound.vecFT Nat l))
      -> Unit {
    let Pair(n, Pair(l, xs)) = v;
    *xs := Pair(e, *xs);
    *l := S(*l);
    *n := S(*n);
    () };
  () }

example : progOk vecPushNested = true := by native_decide

example : progRejects (prog defer_check {
    fn Push (e : Nat, v : &mut (Σ (n : Nat). Σ (l : Nat). %Tests.S5Bound.vecFT Nat l))
        -> Unit {
      let Pair(n, Pair(l, xs)) = v;
      *xs := Pair(e, *xs);
      *n := S(*n);
      () };
    () })
  "owed type" = true := by native_decide

/-! ### Exhaustiveness is not a new rule

    A nullary constructor in argument position is a nested pattern like any other —
    and the names it claims (`Z`, `Nil`, `True`, …) are exactly the names
    `checkBinder` already REFUSED there, so this reads programs that used to be
    macro errors and re-reads none that compiled. `Cons(Z, tl)` is therefore a
    one-branch match on a `Nat`, and §9 says what is missing from it. There is no
    cross-arm grouping to appeal to: no sibling arm can complete it, because DLLBC
    matches are one arm per head constructor and this is not the head. -/

def nestedNonExh : Term := prog defer_check {
  fn F (l : List Nat) -> Unit { match l { Nil => (), Cons(Z, tl) => () } };
  () }

example : progRejects nestedNonExh
  "match: non-exhaustive — no branch for constructor 'S'" = true := by native_decide

/-! ### The branch-equation form refuses them, and says why

    `match h : x { … }` binds one `h` whose TYPE varies per arm — the equation
    between the scrutinee and that arm's constructor. At a nested position nobody
    has said what that equation is (the payload's own? the outer one refined? both
    conjoined?), so v1 declines to answer rather than answering silently. The inner
    match is still writable by hand, with its own `match h2 : …` where an equation
    is wanted. Refusing is the reversible half of the choice. -/

/--
error: decl: the branch-equation form `match h : e { … }` does not take nested patterns. `h`'s type is the equation between the scrutinee and THIS arm's constructor, and no equation is defined at a nested position — write the inner match explicitly (with its own `match h2 : …` if it needs one).
-/
#guard_msgs in
example : Term := prog{
  let p = Pair(1, Pair(2, 3));
  match h : p { Pair(a, Pair(b, c)) => () } }

/-! ### Two of them alive at once — the reason the id is in the NAME

    `Pair(Pair(a, b), Pair(c, d))` mints two intermediates in ONE branch, and the
    match on the first runs while the second is still live. Ω is name-keyed with
    newest-wins (`findSlot?` never reads an id), so one shared name for both would
    send the first match's header to the SECOND payload — `out` would be 3, and
    nothing would report an error. It is 1, and that is what `patName`'s suffix
    buys. (`§m` gets away with one name for every site because an outer `§m` is
    dead the moment its match is entered. These two are not.) -/

def twoNested : Term := prog{
  let q = Pair(Pair(1, 2), Pair(3, 4));
  let Pair(Pair(a, b), Pair(c, d)) = q;
  let out = a;
  () }

example : progOk twoNested = true := by native_decide
-- `out` is 1. Under one shared name it would be 3, and the two ⊥ slots below
-- would be one.
example : progRunsTo twoNested
    [("q", .bot), ("§p1", .bot), ("§p2", .bot), ("a", Val.nat 1), ("b", Val.nat 2),
     ("c", Val.nat 3), ("d", Val.nat 4), ("out", Val.nat 1)] = true := by native_decide

end Dllbc.Tests.Sugar
