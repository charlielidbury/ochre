import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdChain
import Dllbc.Tests.Boundaries
import Dllbc.FnMacro

/-!
# Surface sugar

Tests for surface sugar that lives entirely in the macro layer: matching on an
expression (binds the scrutinee to a fresh slot first), the singleton-constructor
`let` (desugars to a one-arm match, with exhaustiveness still checked), and
nested constructor patterns (a fresh binder plus an immediate inner match). The
goldens assert `Term` equality with the spelled-out form, because the claim is
that the elaborator produces the same term, not merely an equivalent one. The
closing battery covers the call spelling itself: `f(a, b)` is the same term as
juxtaposition, and the argument-reordering the `[k]` hoist requires.

One rule stays fixed: a match on a plain variable is unchanged byte-for-byte.
Matching a borrow variable reborrows, so inserting a fresh binding would move
the scrutinee and change the semantics.
-/

open Dllbc
open Dllbc.Term (nat)

namespace Dllbc.Tests.Sugar

/-! ## A numeral is the `S (S … Z)` chain, built as one node

    `Surface.buildNat` emits `Term.nat k` rather than `k` nested `ctorApp`
    syntax nodes. The `Term` is the same — `Term.nat` IS the chain — which the
    first line says by `rfl` against the spelled-out form. The second is why it
    matters: a literal `1056` used to be a 1056-deep syntax tree that exhausted
    `maxRecDepth`, which is what made the corpus splice large numerals as
    `%(Term.nat k)`. -/

example : ty{ 3 } = .ctorApp "S" [.ctorApp "S" [.ctorApp "S" [.ctorApp "Z" []]]] := by rfl
example : (ty{ 138 } == nat 138) = true := by native_decide
example : (ty{ 1056 } == nat 1056) = true := by native_decide

/-! ## A plain variable is matched directly

    The scrutinee below is `b`, a borrow. The hand-written term has the
    `.matchE` header sitting directly on `b`'s slot with no interposed `.letIn`
    and no fresh id, confirming the sugar does not fire on a plain variable. -/

def borrowMatch : Term := prog{
  let v = Pair(0, 1);
  let b = &m v;
  match b { Pair(l, r) => { *l := 1; () } } }

def borrowMatchHand : Term :=
  .seq (.letIn (Var.slot "v") (.ctorApp "Pair" [nat 0, nat 1]))
    (.seq (.letIn (Var.slot "b") (.borrow (.var "v")))
      (.matchE "b" none
        [.mk "Pair" [Var.slot "l", Var.slot "r"]
          (.seq (.assign (.deref (.var "l")) (nat 1)) .unit)]))

example : borrowMatch = borrowMatchHand := by rfl

-- Parentheses around the scrutinee don't change the path: `elabScrut` strips
-- grouping before checking for an identifier, so `match (b) { … }` still
-- reborrows rather than moving the value.
example : prog{
    let v = Pair(0, 1);
    let b = &m v;
    match (b) { Pair(l, r) => { *l := 1; () } } } = borrowMatchHand := by rfl

-- The same holds for the branch-equation form: the equation binder still lands
-- at the same id, since the plain-variable path never touches the counter.
def eqnMatch : Term := prog{
  let n = 0;
  match h : n { Z => (), S(m) => () } }

def eqnMatchHand : Term :=
  .seq (.letIn (Var.slot "n") (nat 0))
    (.matchE "n" (some (Var.slot "h"))
      [.mk "Z" [] .unit, .mk "S" [Var.slot "m"] .unit])

example : eqnMatch = eqnMatchHand := by rfl

-- An identifier that is not a bound runtime local is an error, not a fresh-slot
-- binding: the sugar only covers what the grammar could not already spell.
-- `#guard_msgs` pins the exact message below, since the message is the point
-- of a refusal test.
/-- error: decl: match scrutinee 'Nat' is not a bound runtime variable -/
#guard_msgs in
example : Term := prog{ let x = 0; match Nat { Z => () } }

/-! ## An expression scrutinee, not a bare variable -/

-- A constructor application, matched where it stands.
def ctorScrut : Term := prog{
  let out = match Pair(1, 2) { Pair(a, b) => a };
  () }

-- A call's result, matched directly instead of naming an intermediate first.
def callScrut : Term := prog{
  fn Mk (x : Nat) -> Σ (a : Nat). Nat { Pair(x, x) };
  let out = match Mk(2) { Pair(a, b) => b };
  () }

-- Capture check: `§m` is the sugar's binder and no program can write one
-- directly (`checkBinder` refuses the `§` namespace), so this checks that the
-- minted binder doesn't shadow a program-written `m`. Environment lookup
-- resolves by name with newest-wins, so a fresh binder spelled `m` would
-- shadow the outer one and this would answer 1 instead of 7.
def noCapture : Term := prog{
  let m = 7;
  let out = match Pair(1, 2) { Pair(a, b) => m };
  () }

-- Two of them nested, so both `§m` slots are alive in one Ω at once.
def nestedScrut : Term := prog{
  let out = match Pair(1, 2) { Pair(a, b) => match Pair(3, b) { Pair(c, d) => d } };
  () }

-- The sugar's `let` is visible in Ω like any ordinary binding: its slot holds
-- ⊥ because the pattern binders moved the payload out of it.
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

-- Symbolically the call's result is a fresh symbol, the match splits the
-- pair, and `out` is the second component. (`tailEnv` drops the `fn`'s own Ω
-- entry.)
example : tailEnv callScrut
    [("§m", .bot), ("a", Val.sym 0), ("b", Val.sym 1), ("out", Val.sym 1)] = true := by
  native_decide

-- An ordinary Lean `ident` cannot contain `§`, but an escaped one can, and
-- `Name.toString` re-escapes it: the binder this program writes is named
-- `«§m»`, guillemets included, which is a different name from `§m` and not in
-- the reserved namespace. The read from inside the arm still finds 7.
def escapedScrut : Term := prog{
  let «§m» = 7;
  let out = match Pair(1, 2) { Pair(a, b) => «§m» };
  () }

example : progRunsTo escapedScrut
    [("«§m»", Val.nat 7), ("§m", .bot), ("a", Val.nat 1), ("b", Val.nat 2),
     ("out", Val.nat 7)] = true := by native_decide

/-! ## Singleton-constructor `let` desugars to a one-arm match

    The claim is equality with the nested match it replaces, not just
    convertibility: binder ids are minted from the same counter at the same
    point, and the rest of the block is elaborated exactly where the arm body
    would be. -/

def flatLet : Term := prog{
  let p = Pair(1, 2);
  let Pair(a, b) = p;
  () }

def pyramidLet : Term := prog{
  let p = Pair(1, 2);
  match p { Pair(a, b) => () } }

example : flatLet = pyramidLet := by rfl

-- Three levels deep: the flat spelling never indents or accumulates closing
-- braces.
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

-- Composing with the expression-scrutinee sugar: the right-hand side may be a
-- call result.
def letCall : Term := prog{
  fn Mk (x : Nat) -> Σ (a : Nat). Nat { Pair(x, x) };
  let Pair(a, b) = Mk(2);
  let out = b;
  () }

example : progOk letCall = true := by native_decide

example : progRunsTo flat3
    [("p", .bot), ("a", Val.nat 1), ("z1", .bot), ("b", Val.nat 2), ("z2", .bot),
     ("c", Val.nat 3), ("d", Val.nat 4), ("out", Val.nat 4)] = true := by native_decide
-- Runs to the same result because it is the same term (`flat3 = pyramid3`
-- above).
example : runProgram flat3 = runProgram pyramid3 := by rfl

example : tailEnv letCall
    [("§m", .bot), ("a", Val.sym 0), ("b", Val.sym 1), ("out", Val.sym 1)] = true := by
  native_decide

/-! ## `vecPush` respelled with the singleton-constructor `let`

    `vecPush` is a borrow-mode match over a Σ: the arm binders `l` and `xs` are
    loans into the payload behind `v`, so a desugaring that bound the scrutinee
    to a fresh slot would move the pair and the writes would land on a copy.
    The respelling is asserted equal to `vecPush` itself, so the test below is
    checking the same program. -/

def vecPushLet : Term := prog{
  fn Push (e : Nat, v : &mut (Σ (l : Nat). Tests.S5Bound.vecFT Nat l)) -> Unit {
    let Pair(l, xs) = v;
    *xs := Pair(e, *xs);
    *l := S(*l);
    () };
  () }

example : vecPushLet = Tests.S5Bound.vecPush := by rfl
example : progOk vecPushLet = true := by native_decide

-- Forget `*l := S(*l)` and the second field is checked against the stuck
-- `VecF Nat σₗ`, which the concrete `Pair` cannot inhabit — rejected, as in
-- `Boundaries`.
example : progRejects (prog_parse {
    fn Push (e : Nat, v : &mut (Σ (l : Nat). Tests.S5Bound.vecFT Nat l)) -> Unit {
      let Pair(l, xs) = v;
      *xs := Pair(e, *xs);
      () };
    () })
  "owed type" = true := by native_decide

/-! ## Exhaustiveness is checked, not assumed, at the surface

    `let Cons(h, t) = l ;` desugars unconditionally to a one-branch match; the
    kernel's exhaustiveness check refuses it when the type has more than one
    constructor. The macro layer keeps no constructor table of its own — it
    does not need to know which types have exactly one constructor. -/

def headByLet : Term := prog_parse {
  fn Head (l : List Nat) -> Nat { let Cons(h, t) = l; h };
  () }

-- The message names the missing constructor and says "match" for what was
-- written as a `let` — the one place the desugaring is visible from outside.
example : progRejects headByLet
  "match: non-exhaustive — no branch for constructor 'Nil'" = true := by native_decide

-- The one-constructor case is accepted through the same check: `Pair` is Σ's
-- only constructor, so the one-branch match is exhaustive.
example : progOk (prog{
    fn Snd (p : Σ (a : Nat). Nat) -> Nat { let Pair(x, y) = p; y };
    () }) = true := by native_decide

/-! ## A constructor pattern in argument position

    `Cons(Pair(k, v), tl) => …` is exactly the hand-written
    `Cons(§p, tl) => match §p { Pair(k, v) => … }` — same ids, same names, same
    `Term`. The twins below are written as `Term`s rather than `prog{ }`
    because the hand-spelling isn't writable: the intermediate's name is
    reserved.

    Each arm still compiles on its own: DLLBC's match is one arm per head
    constructor, and a nested pattern is just an inner match, checked for
    exhaustiveness like any other. So `Cons(Z, tl)` is a one-branch match on a
    `Nat` and is rejected, not a partial arm waiting for a sibling. -/

def nestedArm : Term := prog{
  let l = Cons(Pair(1, 2), Nil);
  match l { Nil => (), Cons(Pair(kk, vv), tl) => { let out = vv; () } } }

def nestedArmHand : Term :=
  .seq (.letIn (Var.slot "l") (.ctorApp "Cons" [.ctorApp "Pair" [nat 1, nat 2], .ctorApp "Nil" []]))
    (.matchE "l" none
      [.mk "Nil" [] .unit,
       .mk "Cons" [Var.slot "§p0", Var.slot "tl"]
         (.matchE "§p0" none
           [.mk "Pair" [Var.slot "kk", Var.slot "vv"]
             (.seq (.letIn (Var.slot "out") (.var "vv")) .unit)])])

example : nestedArm = nestedArmHand := by rfl

-- The golden pins the id order: every argument of the head takes its slot
-- first (`§p1`, then `tl`), and only then does the nested pattern mint what is
-- inside it (`kk`, `vv`) — matching how a match arm binds, counter first and
-- then body. Reversed, the terms would still be convertible but no longer
-- equal.

/-! ### Three levels deep, nested vs. chained

    `deep3` is `flat3` above with its two intermediates unnamed. Same ids, slot
    for slot, same values, but two binder names differ: `§p2`/`§p4` where the
    chain wrote `z1`/`z2`, since the nested spelling never names what it
    doesn't use. Both Ωs are written out below so the difference is visible
    directly. -/

def deep3 : Term := prog{
  let p = Pair(1, Pair(2, Pair(3, 4)));
  let Pair(a, Pair(b, Pair(c, d))) = p;
  let out = d;
  () }

def deep3Hand : Term :=
  .seq (.letIn (Var.slot "p")
      (.ctorApp "Pair" [nat 1, .ctorApp "Pair" [nat 2, .ctorApp "Pair" [nat 3, nat 4]]]))
    (.matchE "p" none
      [.mk "Pair" [Var.slot "a", Var.slot "§p0"]
        (.matchE "§p0" none
          [.mk "Pair" [Var.slot "b", Var.slot "§p1"]
            (.matchE "§p1" none
              [.mk "Pair" [Var.slot "c", Var.slot "d"]
                (.seq (.letIn (Var.slot "out") (.var "d")) .unit)])])])

example : deep3 = deep3Hand := by rfl
example : progOk deep3 = true := by native_decide
-- `flat3`'s Ω, with `z1`/`z2` replaced by the minted names and nothing else
-- changed — not even the ids, which the goldens above pin exactly.
example : progRunsTo deep3
    [("p", .bot), ("a", Val.nat 1), ("§p0", .bot), ("b", Val.nat 2), ("§p1", .bot),
     ("c", Val.nat 3), ("d", Val.nat 4), ("out", Val.nat 4)] = true := by native_decide

/-! ### A five-deep nest, in all three spellings

    `pyramid5`, `chain5` and `nest5` are the same five-component Σ
    destructuring at increasing levels of sugar:

      * `pyramid5` → `chain5` is the singleton-`let` sugar and changes
        nothing — same ids, same names, `rfl`.
      * `chain5` → `nest5` is the nested-pattern sugar and drops the three
        intermediates. The ids stay the same, slot for slot; only
        `z1`/`z2`/`z3` become `§p2`/`§p4`/`§p6`. -/

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
    [("p", .bot), ("a", Val.nat 1), ("§p0", .bot), ("b", Val.nat 2), ("§p1", .bot),
     ("c", Val.nat 3), ("§p2", .bot), ("d", Val.nat 4), ("e", Val.nat 5),
     ("out", Val.nat 5)] = true := by native_decide

/-! ### Reborrowing through a nested pattern

    `match v { … }` on a `&mut` reborrows: the arm binders are loans into the
    payload, not copies. The minted intermediate stays a plain variable, so the
    inner match takes the plain-variable path — its `.matchE` header sits
    directly on the intermediate's slot, and the loan chains through. If the
    sugar bound it to a fresh slot instead, the payload would move and the
    writes below would land on an unreachable copy. -/

def nestedWrite : Term := prog{
  let t = Pair(0, Pair(0, 0));
  let b = &m t;
  let Pair(x, Pair(y, z)) = b;
  *x := 1;
  *y := 2;
  *z := 3;
  () }

example : progOk nestedWrite = true := by native_decide
-- All three writes land in `t`: the loans reached the innermost field through
-- the minted intermediate. `§p3` is the intermediate's slot, ⊥ because its
-- match moved the payload into `y` and `z`.
example : progRunsTo nestedWrite
    [("t", Val.ctor "Pair" [Val.nat 1, Val.ctor "Pair" [Val.nat 2, Val.nat 3]]),
     ("b", .bot), ("x", .bot), ("§p0", .bot), ("y", .bot), ("z", .bot)] = true := by
  native_decide

-- A borrowed list whose elements are pairs, cleared through the borrow. The
-- head constructor is matched in reborrow mode and the element's fields are
-- loans reached through the intermediate — two levels of `&mut` from one
-- pattern.
def clearHead : Term := prog{
  let l = Cons(Pair(7, 9), Nil);
  let b = &m l;
  match b {
    Nil => (),
    Cons(Pair(kk, vv), tl) => { *vv := 0; () }
  };
  () }

example : progOk clearHead = true := by native_decide
-- The value field is 0 and the key is untouched — a nested pattern reaching
-- the wrong loan would still run, so this checks which one it reached.
example : progRunsTo clearHead
    [("l", Val.ctor "Cons" [Val.ctor "Pair" [Val.nat 7, Val.nat 0], Val.nil]),
     ("b", .bot)] = true := by native_decide

/-! ### A three-field nested pattern, with the same rejection

    `vecPush` with a second coupled field, destructured in one pattern: `n` is
    a running count, `l` the vector's length, `xs` its payload — all three are
    loans into the same `&mut`, and `l` is what the dependent type is indexed
    by. Forget `*l := S(*l)` and the concrete `Pair` is checked against the
    stuck `VecF Nat σₗ`, same as in `Boundaries`; nesting the pattern doesn't
    change the rejection. -/

def vecPushNested : Term := prog{
  fn Push (e : Nat, v : &mut (Σ (n : Nat). Σ (l : Nat). Tests.S5Bound.vecFT Nat l))
      -> Unit {
    let Pair(n, Pair(l, xs)) = v;
    *xs := Pair(e, *xs);
    *l := S(*l);
    *n := S(*n);
    () };
  () }

example : progOk vecPushNested = true := by native_decide

example : progRejects (prog_parse {
    fn Push (e : Nat, v : &mut (Σ (n : Nat). Σ (l : Nat). Tests.S5Bound.vecFT Nat l))
        -> Unit {
      let Pair(n, Pair(l, xs)) = v;
      *xs := Pair(e, *xs);
      *n := S(*n);
      () };
    () })
  "owed type" = true := by native_decide

/-! ### A nullary constructor nested is still checked for exhaustiveness

    A nullary constructor in argument position is a nested pattern like any
    other: names like `Z`, `Nil`, `True` are exactly the names `checkBinder`
    already refuses at that position, so this covers programs `checkBinder`
    would otherwise reject and none that compiled before. `Cons(Z, tl)` is a
    one-branch match on a `Nat`; no sibling arm can complete it, since DLLBC
    matches are one arm per head constructor and this is not the head. -/

def nestedNonExh : Term := prog_parse {
  fn F (l : List Nat) -> Unit { match l { Nil => (), Cons(Z, tl) => () } };
  () }

example : progRejects nestedNonExh
  "match: non-exhaustive — no branch for constructor 'S'" = true := by native_decide

/-! ### The branch-equation form refuses a nested pattern

    `match h : x { … }` binds `h` to the equation between the scrutinee and
    that arm's constructor, and its type varies per arm. At a nested position
    it's unclear what that equation should be (the payload's own? the outer
    one refined? both?), so this form declines to answer rather than guessing.
    The inner match can still be written by hand, with its own
    `match h2 : …` if an equation is needed there. -/

/--
error: decl: the branch-equation form `match h : e { … }` does not take nested patterns. `h`'s type is the equation between the scrutinee and THIS arm's constructor, and no equation is defined at a nested position — write the inner match explicitly (with its own `match h2 : …` if it needs one).
-/
#guard_msgs in
example : Term := prog{
  let p = Pair(1, Pair(2, 3));
  match h : p { Pair(a, Pair(b, c)) => () } }

/-! ### Two minted intermediates alive at once

    `Pair(Pair(a, b), Pair(c, d))` mints two intermediates in one branch, and
    the match on the first runs while the second is still live. Ω is
    name-keyed with newest-wins (`findSlot?` never reads an id), so a shared
    name for both would send the first match's header to the second payload —
    `out` would be 3, silently. It is 1, because `patName` gives each
    intermediate a distinct suffix. (`§m` can reuse one name across sites
    because an outer `§m` is dead by the time its match is entered; these two
    are not.) -/

def twoNested : Term := prog{
  let q = Pair(Pair(1, 2), Pair(3, 4));
  let Pair(Pair(a, b), Pair(c, d)) = q;
  let out = a;
  () }

example : progOk twoNested = true := by native_decide
-- `out` is 1. Under one shared name it would be 3, and the two ⊥ slots below
-- would be one.
example : progRunsTo twoNested
    [("q", .bot), ("§p0", .bot), ("§p1", .bot), ("a", Val.nat 1), ("b", Val.nat 2),
     ("c", Val.nat 3), ("d", Val.nat 4), ("out", Val.nat 1)] = true := by native_decide

end Dllbc.Tests.Sugar

section
namespace Dllbc.Tests.S32Spine

open Dllbc Dllbc.Tests
open Dllbc.StdChainRaw (LeReflRaw)

/-! ## The application spine, and what retiring a node must not take with it

    `Term.callV` is gone: `f(a, b)` is surface sugar for `.app (.app f a) b`, so
    the surface's n-ary shape and the document's binary grammar are one thing.

    The hazard is that `callV` looked like it carried the mint-vs-remember
    split, when that split is actually arrow-keyed: ⇒ mints a fresh existential
    at the instantiated codomain, ⇝ remembers the structured neutral. With two
    nodes you cannot tell which key is load-bearing; with one you can, and
    these are the assertions that say so. -/

/-! ## A. The two spellings are one term

    Not "behave the same" — the same `Term`, which is the strongest form the
    claim has and the one that makes every other assertion about calls apply to
    juxtaposition automatically. -/

def spelledCall : Term := prog_parse { let F = λ (x : Nat). x; let z = F(2); () }
def spelledJux  : Term := prog_parse { let F = λ (x : Nat). x; let z = F 2; () }
example : Term.beq spelledCall spelledJux = true := by native_decide

/-! ## B. ⇒ mints at the instantiated codomain

    An abstract `σ : Π` applied under ⇒ forgets the application and keeps what
    the type promised — a fresh σ per call, which is why the two calls below get
    distinct ones. This is `callV`'s old rule, and it now runs off the value. -/

def mintTwice : Term := prog{
  let F = (λ (x : Nat). x : Π (x : Nat) → Nat); let y = F(2); let z = F(2); () }
example : tailEnv mintTwice [("F", .sym 0), ("y", .sym 1), ("z", .sym 2)] = true := by
  native_decide

-- …and the juxtaposed spelling mints too, which is §A's consequence made
-- explicit: if this ever diverges from the line above, the split has gone
-- node-keyed again.
def mintTwiceJux : Term := prog{
  let F = (λ (x : Nat). x : Π (x : Nat) → Nat); let y = F 2; let z = F 2; () }
example : tailEnv mintTwiceJux [("F", .sym 0), ("y", .sym 1), ("z", .sym 2)] = true := by
  native_decide

/-! ## C. ⇝ remembers the structured neutral, and refuses to enter

    The other half, and it needs both directions. ⇝ has a reading of an
    application of an abstract function (the neutral `f a`), and no reading at
    all of an application that must be entered — a sealed function's result is a
    fresh existential minted at an event, and ⇝ has no events. `reflectC` used
    to key that on the `.callV` node; it keys it on the callee's value now. -/

-- Remembered: a Π-typed comptime parameter applied inside a spec position. The
-- program checks, which is the assertion — the neutral has a reading.
def rememberNeutral : Term := prog{
  fn Use (G : Π (x : Nat) → Nat, n : Nat) -> Id Nat (G n) (G n) { Refl };
  () }
example : progOk rememberNeutral = true := by native_decide

-- Refused: a sealed function's call, ⇝-read at a capital `let`. Entering is an
-- event; this is the refusal that retired with `.callV` and came back on the
-- value.
def enterRefused : Term := prog_parse {
  fn GiveLe (a : Nat) -> Le a a { LeReflRaw a };
  fn Caller (n : Nat) -> Unit { let P = GiveLe(n); () };
  () }
example : progRejects enterRefused "not in the comptime fragment" = true := by native_decide

/-! ## D. A `.var`-headed spine is imperative

    `Term.imperative` named `.callV` explicitly, and the classification is what
    `Term.lamImperative` reads to decide whether applying a λ is ⇒-entry. Read
    off the arguments alone, a nullary `fn` whose body is only a call would
    classify pure — its one binder is the Unit-desugar's comptime `U§`, so the
    binder half cannot save it, and `.app (.var g) .unit` has no imperative
    leaf. A `.const` head, or a head bound by a pure binder above it, stays
    comptime, which is the pure spine (docs/22: under one `var` the head's
    KIND is its scope, so the probe asks under the binder).

    The probes are `prog_parse { }` fragments with `g`/`l`/`a` free; the
    const-headed one reads `natRec` where it used to read a hand-written
    `.const "Len"`, because the surface resolves `Len` to its `…FnT` λ, which
    is a different head kind from the one this line is about. -/

example : Term.imperative prog_parse { g () } = true := by native_decide
example : Term.imperative prog_parse { natRec l } = false := by native_decide
example : Term.lamImperative prog_parse { λ (le : Type). le a } = false := by native_decide
-- A bare `.var` is a snapshot read, not a call, and both arrows have a rule.
example : Term.imperative prog_parse { g } = false := by native_decide

/-! ## E. The `[k]` permutation survives

    `retarget` reorders a call's arguments to match a `[k]`-hoisted callee's
    telescope — the hoist puts the scrutinee first, so a call written in
    declaration order has to be reordered the same way, and omitting it silently
    passes a borrow where a `Nat` is expected. Retiring `callV` changed what
    `retarget` builds and not what it decides, and these assert the decision
    against the new shape rather than against a program that could pass for
    other reasons. -/

-- `[k]` at parameter 1: the built spine puts argument 1 first.
example : Term.beq
    (FnMacro.retarget [("f", Var.decl "f", some 1)] (.call "f" [.unit, .type]))
    (Term.appSpine (.var "f") [.type, .unit]) = true := by native_decide

-- …and with no hint, declaration order is kept — without which the line above
-- would pass on a `retarget` that reordered unconditionally.
example : Term.beq
    (FnMacro.retarget [("f", Var.decl "f", none)] (.call "f" [.unit, .type]))
    (Term.appSpine (.var "f") [.unit, .type]) = true := by native_decide

-- The nullary desugar's `()` still arrives at the call site, which is what
-- makes a no-argument `fn` a spine at all rather than a bare variable.
example : Term.beq
    (FnMacro.retarget [("f", Var.decl "f", none)] (.call "f" []))
    (.app (.var "f") .unit) = true := by native_decide

-- And the spine reader inverts the builder, head and all.
example : (Term.appSpineVar? (Term.appSpine (.var "f") [.unit, .type]))
    == some ("f", [.unit, .type]) := by native_decide
example : (Term.appSpineVar? (Term.appSpine (.const "Len") [.unit])).isSome = false := by
  native_decide

end Dllbc.Tests.S32Spine
end

section
namespace Dllbc.Tests.FnTails

open Dllbc

/-! ## `fn`'s two optional tails

    `-> R` and `; rest` are both optional, and they are independent of each
    other.

    Omitting `; rest` is a change of SHAPE and nothing else: the `.seq` and the
    `bindFn` go, because there is no tail to sequence and none to retarget. That
    makes `fn` the one statement form that may end a block — `let x = e` still
    owes its `; rest`, and the grammar refuses a block that ends with one before
    any checking happens.

    Omitting `-> R` is a change of MEANING: no return type is no Π, no Π is no
    seal, and the seal is what makes a function opaque and what makes its body
    audited once at the declaration. §A–§C below pin the shapes; §D pins the
    meaning, as a differential against the sealed twin.

    The goldens are `Term.beq` under `native_decide` rather than `rfl`, unlike
    the rest of this file: `retarget` is `partial`, so a term the `fn` row built
    does not reduce in the kernel and `rfl` cannot see through it. `Term.beq` is
    the structural equality the rest of the corpus compares terms with. -/

/-! ### A. No `-> R` is a bare λ

    `fn F (…) { b }` is `let F = λ (…) { b }` — the same λ the `let` spelling
    writes, with no ascription wrapped around it. The hand-written term binds
    `Var.decl`, which is what a declaration's `let` binds and what `tailEnvs`
    filters on; that is untouched by this row and is the one thing the `fn`
    spelling and the `let` spelling still differ by. -/

def unsealedFn : Term := prog{ fn Idf (x : Nat) { x } ; () }

def unsealedHand : Term :=
  .seq (.letIn (Var.decl "Idf") (.lam (Var.slot "x") (.const "Nat") (.var "x"))) .unit

example : Term.beq unsealedFn unsealedHand = true := by native_decide

-- The control, and the reason the line above reads as a change rather than as a
-- restatement of what `fn` always did: WITH `-> Nat` the identical λ arrives
-- wrapped in a seal at the Π the header wrote. One `.seal` node is the entire
-- difference between the two.
def sealedFn : Term := prog{ fn Idf (x : Nat) -> Nat { x } ; () }

def sealedHand : Term :=
  .seq (.letIn (Var.decl "Idf")
         (.seal 0 (.lam (Var.slot "x") (.const "Nat") (.var "x"))
                  (.pi "x" (.const "Nat") (.const "Nat")))) .unit

example : Term.beq sealedFn sealedHand = true := by native_decide

-- …and the two are not the same term, which neither line above says on its own.
example : Term.beq unsealedFn sealedFn = false := by native_decide

/-! ### B. No `; rest` is the bare `.letIn`

    The tail-less form is not the `; ()` form — `.letIn` and `.seq (.letIn …) ()`
    are genuinely different terms and asserting equality between them would be
    false. What is true, and what dropping the tail amounts to, is that the `; ()`
    form is the tail-less form with a `.seq` and a tail put back around it. -/

def tailLess : Term := prog{ fn U () -> Unit { () } }
def withTail : Term := prog{ fn U () -> Unit { () } ; () }

example : Term.beq withTail (.seq tailLess .unit) = true := by native_decide

-- …said the other way round, because the line above would also hold of a
-- `tailLess` with some other head node entirely.
example : (match tailLess with | .letIn _ _ => true | _ => false) = true := by native_decide

-- Both check, and the tail-less one's value is `()`: a bare `.letIn` in tail
-- position is a unit-valued statement under ⇒ (`readR`, and `exploreD`'s
-- final-expression arm through `readResult`) and under ⇝ (`Pure.eval`). Its own
-- binding is a declaration's, so `tailEnv` filters it out and the Ω is empty.
example : progOk tailLess = true := by native_decide
example : progOk withTail = true := by native_decide
example : tailEnv tailLess ([] : Env) = true := by native_decide

-- It ends a BLOCK, not merely a whole program: an ordinary statement above it is
-- unaffected and what that statement left is still what the block leaves.
def afterAStatement : Term := prog{ let v = 0; fn U () -> Unit { () } }
example : progOk afterAStatement = true := by native_decide
example : tailEnv afterAStatement [("v", Val.nat 0)] = true := by native_decide

/-! ### C. Both tails off at once, and the nullary `()`-supply

    The two omissions compose: with neither, a `fn` is the bare `.letIn` of the
    bare λ. And the nullary-`Unit` desugar sits ABOVE `fnElab`'s choice of
    reading, so a no-argument unsealed `fn` still gets its `Unit` binder and
    `retarget` still supplies the `()` at the call site — without which `F()`
    would be a bare variable rather than a spine. -/

def bothOff : Term := prog{ fn Idf (x : Nat) { x } }

example : Term.beq bothOff
    (.letIn (Var.decl "Idf") (.lam (Var.slot "x") (.const "Nat") (.var "x"))) = true := by
  native_decide

-- Declared with no seal, and CALLED. The `()` arrives, the call reduces, and `y`
-- is the concrete 7 — §D's transparency seen from the run side: an unsealed
-- callee's body is what the call computes.
def nullaryCalled : Term := prog{ fn F () { 7 } ; let y = F(); y }
example : progOk nullaryCalled (retType := ty{ Nat }) = true := by native_decide
example : tailEnv nullaryCalled [("y", Val.nat 7)] = true := by native_decide

-- The sealed twin also checks and also receives its `()`, so the `()`-supply is
-- not what the seal changes. What it changes is the ANSWER: entering a seal mints
-- a fresh existential at the instantiated codomain, so `y` is `σ0`, not 7.
def nullarySealed : Term := prog{ fn F () -> Nat { 7 } ; let y = F(); y }
example : progOk nullarySealed (retType := ty{ Nat }) = true := by native_decide
example : tailEnv nullarySealed [("y", Val.nat 7)] = false := by native_decide
example : tailEnv nullarySealed [("y", .sym 0)] = true := by native_decide

-- A unary unsealed callee is called the same way — `retarget` rewrites a call
-- whether or not the binding it points at is sealed.
def unaryCalled : Term := prog{ fn Twice (x : Nat) { S(S(x)) } ; let y = Twice(3); y }
example : progOk unaryCalled (retType := ty{ Nat }) = true := by native_decide
example : tailEnv unaryCalled [("y", Val.nat 5)] = true := by native_decide

/-! ### D. THE AUDIT DIFFERENTIAL — what dropping the seal actually does

    The seal is what triggers the declaration-time body audit. Without one the λ
    is TRANSPARENT: it β-reduces at each call site, the checker meets the body
    there, and so the body is checked once per call site — and not at all when
    there is no call site. The three lines below are the whole claim, and it takes
    all three, since each alone would pass for a reason that is not the point.

    This is a feature, not a hole. Tests/Functions §C already pins the two callee
    rules it chooses between — "body known, so unfold: a literal λ callee
    β-reduces" against "body withheld, so only the type's promise" — and omitting
    `-> R` picks the first, deliberately. -/

-- `Bogus` is bound nowhere. UNSEALED and never called: accepted, because nothing
-- ever looks inside the λ.
def unsealedBogus : Term := prog_parse { fn G (x : Nat) { Bogus(x) } ; () }
example : progOk unsealedBogus = true := by native_decide

-- The same body, SEALED: rejected at the declaration, before any call, because
-- the seal audits it there.
def sealedBogus : Term := prog_parse { fn G (x : Nat) -> Nat { Bogus(x) } ; () }
example : progOk sealedBogus = false := by native_decide
example : progRejects sealedBogus "call: unknown function 'Bogus'" = true := by native_decide

-- …and the unsealed one is not exempt, only deferred: CALL it and the checker
-- meets the body at the call site and refuses it there, with the same message.
def unsealedBogusCalled : Term :=
  prog_parse { fn G (x : Nat) { Bogus(x) } ; let y = G(1); () }
example : progRejects unsealedBogusCalled "call: unknown function 'Bogus'" = true := by
  native_decide

/-! ### E. A `[k]` still needs a return type

    §7 builds the recursor's motive from the sealed Π with the scrutinee peeled
    off the front, so with nothing sealed there is no motive to derive. The
    pairing is decidable from the SYNTAX alone — no telescope type is consulted —
    so it is refused at the `fn` row, at Lean elaboration, where the fix can be
    named, rather than through `fnElabOrFail`'s sentinel, which carries the
    semantic refusals. `#guard_msgs` pins the message, since the message is the
    point of a refusal test. -/

/--
error: fn: 'Count' declares the decreasing argument 'n' but has no return type. §7 builds the recursor's motive from the sealed Π with the scrutinee peeled off the front, so a recursive `fn` must state what it returns — give 'Count' a `-> R`.
-/
#guard_msgs in
example : Term := prog{ fn Count [n] (n : Nat) { n } }

end Dllbc.Tests.FnTails
end
