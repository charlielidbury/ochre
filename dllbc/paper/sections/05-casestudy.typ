#import "../style.typ": *

= Case Study: A Verified In-Place Quicksort <sec-casestudy>

The preceding sections introduced the four arrows one region at a time; this one
assembles them into a real algorithm — three times. The target is an in-place
quicksort over a mutable borrow. The mechanization verifies it under _both_ of the
architectures @sec-architectures sets side by side, which is what turns that
comparison into a measurement; and then verifies the second architecture again over a
different _container_, which is what turns the differential harness into evidence
about the specification rather than only about the checker.

The first pass, through the end of §5.6, is architecture A. The program is the one a Rust
programmer would recognise — a swap-based Lomuto partition, recursion on
sub-ranges, no allocation and no rebuilding of sublists — and it is checked not as
a bespoke development but as an ordinary _implementation of a pure model_: each
imperative function carries a declared backward specification, and conformance is
conversion. We build it from the bottom: the slice representation, the
borrow-returning cursors, the bounds proofs that ride the telescope, the smallest
self-contained instance of the architecture, the partition, and the recursion.

*Architecture A is written in the past tense, and this is where that starts.* The
declared-back machinery it is built on has since been removed from the calculus
(@sec-boundaries), and A's cursors recurse through a borrow's payload, which has
no recursor form — so A's programs are in the corpus as source but are no longer
machine-checked. Every claim §5.2–§5.6 makes was green continuously up to commit
`113f1634`, the last commit at which a checker exists that admits them, and is a
historical claim after it. @sec-architectures states the fence once and in full;
this section keeps the walkthrough because what A _was_ measured to be is half of
the comparison the paper is making, and because several of its findings (the
disjointness problem, the gap-counter form, the stuck-spine split) are about the
calculus rather than about the architecture and survive it untouched.

The second pass (@sec-directroute) is architecture B, and it is the project's mission result:
the same problem with _no declared backward specification anywhere in the call
tree_, each function described only by a return type that is its postcondition,
and every proof step built inside the body from its callees' postconditions.
Reading the two in sequence is the point — the first shows what a pure model buys
and what it costs, the second what is left when you take it away.

The third pass (@sec-arrays) keeps architecture B and changes the _container_: an
`Array n T` whose sub-ranges are places, so that a recursive sort hands its callee a
sub-slice instead of the whole structure plus two indices. It is not a third
architecture. It is the second one again, over a representation that removes the
frame problem §5.1 describes — and because the two share a specification and no code,
running them against each other is a check on the specification that neither could
perform alone (@sec-empirics).

Every listing in this section is quoted from the mechanization, and every
acceptance and rejection claim it makes is a green `native_decide` proposition
unless a status tag says otherwise. Two pins are in play and the section keeps
them apart: §5.7 and §5.8's listings are quoted at the current pin, §5.2–§5.6's
at `113f1634`. Where a shared function's surface has moved between the two — the
cursors gained an explicit scrutinee hint, `partition` and `append_back` now
thread fuel — the listing shows the current form and the text says so.

== The slice, as a borrow and a bound

DLLBC has no heap — no addresses, no aliasing through pointers — which is exactly
what lets a type mention a value's _snapshot_ and never go stale (@calculus). A
"mutable slice", then, cannot be a pointer-and-length into a backing store;
it is represented as what a slice fundamentally _is_, a fat pointer written
honestly: a mutable borrow of the underlying list, paired with a comptime length
bound. The pair `(v : &mut List Nat, n : Nat)` is the calculus's slice, and a
sub-range is named not by a second borrow but by an offset `lo` and a count
`cnt` measured against the same `v`. Suffix sub-slices are tail reborrows
(`&mut *v` peeling one level, @fig-reorg); prefix recursion rides the bound
rather than a prefix borrow. This is a deliberate scoping of the claim: true
random-access arrays with $O(1)$ indexing are a compilation-story question,
outside the calculus, and the segment vocabulary here (`len`, `take`, `drop`,
all of which compute) is `List`-shaped. What the calculus _does_ claim, and
what the rest of this section checks, is the load-bearing half: $O(1)$-extra-space
_swap-based mutation through borrows_, with the segment's untouched remainder
pinned to its entry snapshot by the $arrow.r.curve$ obligation.

The scoping has a cost that the two `List` developments in this section pay, and
@sec-directroute returns to it: because a list segment is not a _place_, a sub-range
can never be handed to a callee as a borrow, so a contract must describe the whole
list including the part the callee must not touch.

That cost is what the third development removes. A flat `Array n T` former, an index
and a range step in the place grammar, and a lazy _carve_ reorganization that fires
only when handed a comptime proof of `Le (add lo cnt) n` make a range into a place —
so two range borrows of one array coexist not because the checker believes an
aliasing argument but because they are literally different subterms of one value tree,
and the suspension machinery of @identification already knows what to do with those.
The frame is then preserved by construction rather than described by a contract.
#status("green") It is built, and @sec-arrays is the third quicksort: the same
propositional architecture as §5.7, over a container where a sub-slice is a thing you
can point at.

== Cursors, and the disjointness problem

Element access is a borrow-returning recursion. The bounds-checked `nth` walks
the list behind a borrow and hands back a mutable borrow of the requested cell:

```rust
fn nth [i] (v : &mut List Nat, i : Nat, p : Le (S i) (len *v)) -> &mut Nat {
  match v {
    Nil => botElim Unit p,
    Cons(hd, tl) => match i {
      Z => &mut *hd,
      S(k) => nth(&mut *tl, k, p)
    }
  } }
```

There is a problem the moment a swap needs _two_ cells at once. Calling `nth`
consumes its borrow argument: after `nth(v, i, p)`, the borrow `v` is gone —
captured into the call's loan group (@fig-boundaries) — so a second
`nth(v, j, q)` has no `v` left to pass. Two sequential calls cannot yield two
simultaneously-live cursors; the first consumes the slice. This is the
calculus's version of the constraint that in Rust forces `split_at_mut`, and the
resolution is the same shape: a single call that issues _two_ borrows from _one_
captured loan.

```rust
fn nth2 [i] (v : &mut List Nat, i : Nat, j : Nat,
             pij : Le (S i) j, p2 : Le (S j) (len *v)) -> Σ (x : &mut Nat) → &mut Nat {
  match v {
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
  } }
```

`nth2` is this calculus's `split_at_mut`: one call captures the single argument
loan and issues the two borrows of the returned pair, tied together in a loan
group whose ending discipline keeps them exclusive of the owner until both die
(@fig-boundaries). The two cursors are disjoint _by construction_ — they point
into distinct fields of the same `Cons`-spine, held apart by the suspension tree
— and this disjointness is what makes the swap through them a genuine in-place
exchange rather than a copy. With the pair in hand, the swap is the take-and-fill
idiom applied twice: `let t = *ei; *ei := *ej; *ej := t`, three destructive
writes through the two reborrows, no list node copied.

== Bounds proofs that ride the telescope

The cursors above carry proofs, and it is worth seeing how little those proofs
cost. The precondition `p : Le (S i) (len *v)` is an ordinary telescope entry
whose type mentions the payload snapshot through the comptime deref `*v`
(@fig-comptime); it is refined per branch exactly as the scrutinee is. Three
facts make the discipline lightweight. First, the `Nil` branch is a
_$bot$-discharge_: there, `p` has type `Le (S i) 0`, which reduces to $bot$, so
the branch is dead and is closed by `botElim` — the ex-falso admission rule
(#smallcaps[B-ExFalso], @fig-boundaries), which lets a provably-dead branch
"return" a borrow it could never actually hold. Second, the recursive call
passes the _same_ proof unchanged: `Le (S (S k)) (S j') equiv Le (S k) j'`
holds _definitionally_, so descending the list needs no transport lemma — the
bound simply reduces along the recursion. Third, an out-of-bounds access is
rejected not inside `nth` but at the _call site_, because there is no inhabitant
of the false bound to supply:

```rust
let x = Cons(1, Cons(2, Cons(3, Nil)));
let bb = &mut x;
swap(bb, 0, 4, (), ());   // p2 : Le (S 4) (len [1,2,3]) = Le 5 3 = ⊥
let y = x;
```

This program is rejected with "does not have its parameter type": the actual
`()` supplied for `p2` would have to inhabit `Le 5 3`, which whnf-reduces to
$bot$, and $bot$ has no inhabitant. At concrete, in-bounds calls the same proofs
are the trivial `()` — `Le 1 2` and `Le 3 3` both reduce to $top$ — so the cost
of dependency is paid only where a bound is genuinely at stake. `Fin`-style
safety, with the error monad replaced by a type that cannot be constructed when
the access is illegal.

== The smallest complete instance

Before the partition, one function isolates the entire architecture in five
lines. `certSwapCount` borrows a symbolic list, swaps two positions in place, and
returns a _certificate_ that the swap preserved the element counts:

```rust
fn certSwapCount (s : List Nat, m : Nat, i : Nat, j : Nat,
      pij : Le (S i) j, p2 : Le (S j) (len s)) -> Id Nat (count m (swapL i j s)) (count m s)
      { let cert = count_swapL' m i j s pij p2;
        let b = &mut s;
        swapS(b, i, j, pij, p2);
        cert }
```

Everything the case study is about is present here at minimum size. The body
performs a genuine imperative mutation (`swapS` through the borrow `b`); the
boundary machinery recovers, precisely, that after the swap `s = swapL i j σ` —
the pure model of the swap applied to the entry snapshot; and the returned
`cert`, a `count_swapL'` proof computed over that entry snapshot, is accepted at
the return type because its subject `swapL i j s` is _definitionally_ the
recovered value. Imperative mutation, precise recovery of the mutated value as a
pure term, and a pure lemma certifying a property of it — end to end, checked by
conversion. The check is not vacuous: the negative control `certSwapCountLie`,
which claims the count _grew_ by one, is rejected ("does not have return type"),
because the certificate proves equality and the value-returning audit converts
the real return type against the declared one.

== Partition: a gap-counter Lomuto

The partition is Lomuto's, with one design choice forced by the calculus. It
maintains a boundary index `i` and a _gap counter_ `g` — the number of scanned
elements greater than the pivot — and decides at each step, from the comptime
read `leb (nth (add i g) *v) pivot`, whether to advance the boundary or grow the
gap, swapping the boundary and scan cells only on the `g = S g'` case. The
structural reason for the gap-counter form is `nth2`: a textbook Lomuto swaps
element `i` with element `j`, and its very first iteration can have `i = j`, a
_self-swap_. But `nth2` cannot issue two cursors to the same index — its two
borrows are disjoint by the suspension tree, and aliasing them is exactly what
it forbids — so the scan is organised so that the swapped positions are never
equal, and the base case is split on `i` to make the `i = 0` placement a literal
no-op (`*v`) rather than the stuck `swapL 0 0 *v`.

One machine feature earns its place here. The scan branches on `if leb x pivot`
with `x` symbolic, and the scrutinee does not reduce to a bare $sigma$ but to a
_stuck spine_ `leb σ σ_p`, which the substitution-based refinement
$arrow.l.squiggly$ cannot split — there is no variable to substitute. The
checker _generalizes_: on an owned stuck Bool spine it normalizes the spine and
abstracts it into a fresh $sigma_b : "Bool"$ across every $sigma$-bearing
component of the state (the #smallcaps[X-Gen] rule of @fig-comptime), after
which the ordinary owned-symbolic split refines $sigma_b$ to `True`/`False` per
branch. Both the spine _in the scrutinee_ and the same spine _in a pinned return
type_ refine together — which is precisely what generalizing across all
$sigma$-bearing state delivers, and a dedicated probe (`stuckProbe`, whose two
`boolRec` sides converge only per branch) confirms it, together with negative
controls for non-convergence and for non-exhaustiveness. #footnote[The
generalization is currently `Bool`-specific — `generalizeStuck` mints only a
fresh `Bool` symbol — sufficient for the `leb`/`if` splits the corpus needs but
narrower than a fully general rule; this is recorded as an extraction finding.]

The scan is declared `back = partScanL pivot k i g (*v)`, its pure model, and
the callee audit checks it _per path_ by conversion: the body's suspension
tree — the composition of the recursive call's declared back with `swapS`'s — is
definitionally that unfold. The recursion threads a length equation
(`hlen : len *v = S (add k (add i g))`) whose transports are definitional totals
plus a single `len_swapL` bridge in the swap case, and a lie in the declared back
(the boundary and gap indices swapped) is rejected because the composed tree no
longer converges. The subrange variant `partScanRange` carries the honest
invariant of a sub-slice — an _inequality_ `Le (add lo (S (add k (add i g)))) (len *v)`,
since a sub-range does not span to the end — ported through the same identity
toolkit; it too checks green.

== Quicksort

The crown assembles the pieces. `quicksort(v, fuel, lo, cnt, hbnd)` sorts the
`cnt` elements at offset `lo` in place, fuel-structural to mirror the pure model
`sortRangeL`. The bracketed `[fuel]` was, at A's pin, the declared _decreasing
position_ that guarded the self-call; under this architecture it is a formality,
since the declared `back`'s conversion is what carries the proof. The same
annotation is what makes the recursion of @sec-directroute admissible, and it has
outlived the guard: at the current pin `[k]` is a _scrutinee-selection hint_ read
by the elaboration rather than a side condition checked by the kernel
(@sec-boundaries).

```rust
// architecture A, quoted at `113f1634`; the `back = …` clause is no longer
// surface syntax, and this declaration no longer elaborates.
fn quicksort [fuel] (v : &mut List Nat, fuel : Nat, lo : Nat, cnt : Nat,
                     hbnd : Le (add lo cnt) (len *v)) -> Unit
      back = sortRangeL fuel lo cnt (*v)
      { match fuel {
          Z => (),
          S(f2) => match cnt {
            Z => (), S(cnt2) => match cnt2 {
              Z => (),
              S(cnt3) => {
                let pivot = nth lo (*v);
                let i = partIdxRangeL lo (S (S cnt3)) (*v);
                let g = partGapRangeL lo (S (S cnt3)) (*v);
                // hle, bl, br : the range bounds, from partScanSizeL and the
                // three length-preservation lemmas (see below)
                partScanRange(&mut *v, lo, S(cnt3), Z, Z, pivot, hle);
                quicksort(&mut *v, f2, lo, i, bl);
                quicksort(&mut *v, f2, S(add lo i), g, br)
              } } } } }
```

Three features of the calculus converge in the last three lines. The pivot's
relative index `i` and right-count `g` are read from the _entry_ list, before
any mutation, as the pure `partIdxRangeL`/`partGapRangeL` — so the body's
suspension tree (the partition's back, then the two recursive quicksort backs
composed) is _definitionally_ `sortRangeL`'s own unfold, and conformance is once
again conversion, not a bespoke argument. The two recursive calls are
_sequential reborrows of the one borrow_ `&mut *v`: this only checks because a
`&mut` on a place already holding a parked loan _demand-ends_ the previous call's
group first — releasing `*v` with its back applied — the concrete demand-driven
ending rather than an atomic-at-audit over-approximation that would suspend `*v`
for the whole body and block the second reborrow. A minimal witness (`twoRec`,
two sequential self-reborrows with `back = *v`) isolates exactly this. Finally,
the pivot index is returned, where a wrapper needs it, by a _singleton-$Sigma$
device_: `partitionRange` returns `Σ (q : Nat). Id q (partIdxRangeL lo cnt *v)`,
pinning the recovered index to its pure value. The range bounds `bl`/`br` are the
one place with real proof weight — a forest built from `partScanSizeL`
(`i + g + 1 = cnt`) and the three length-preservation lemmas (partition and each
recursive sort keep `len *v`, so bounds stated over the live `*v` transport back
to the entry length `hbnd`) — but it is ordinary dependent bookkeeping, and it
elaborates.

The headline held: `quicksort` checked — the imperative in-place
quicksort type-checks as an implementation of its pure model `sortRangeL`, with
conformance reduced to conversion (@fig-boundaries). The from-scratch
conformance `native_decide` runs in seconds rather than the pre-fix tens of
minutes, after the delayed-lift `substPure` optimization, and because converting
the declaration to the surface syntax preserved its underlying value byte for
byte, the check replays from `native_decide`'s cache across that surface change;
the performance story is told in full in @sec-lessons.

== The same problem with no model at all <sec-directroute>

Architecture B removes the `back`s. A callee's _only_ description becomes its
return type, a postcondition over the exit snapshot; a caller sees an opaque exit
plus whatever evidence the callee returned. Four things had to change, and each is
worth naming because each is a place where taking the model away exposed something
the model had been hiding.

*The data plan changes.* Range indices were an artefact of wanting a model
function: `sortRangeL fuel lo cnt` is a function of offsets, so the program was
too. Stated propositionally, the natural unit is the whole list, and what makes
whole-list recursion possible is take-and-refill (@calculus's idiom) applied to
_ownership_ rather than to elements. Two mutators establish the vocabulary — the
second of them is the one the final quicksort actually glues with:

```rust
fn split_off [i] (v : &mut List Nat, i : Nat, hi : Le i (len *v))
  -> Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (take i (old *v)))
       → Id (List Nat) ret (drop i (old *v))

fn append_back [fuel] (fuel : Nat, v : &mut List Nat, w : List Nat, Hf : Le (len *v) fuel)
  -> Id (List Nat) (*v) (append (old *v) w)
```

`split_off` leaves the first `i` elements behind the borrow and returns the rest
_by value_ — it cannot come back as a borrow, since its owner is local — with the
returned list $Sigma$-pinned to `drop i (old *v)`. It is the general
ownership-splitting primitive, and the reason this development has one at all;
the quicksort below reaches the same shape through its partition and needs only
`append_back` to reassemble.

*Both of these used to recurse through the borrow's payload, and no longer can.*
`append_back` walks to the end of `*v` and `partition` walks the list behind `v`,
so the natural decreasing position for each was the payload snapshot — a real
decrease, and the one thing that shrinks in a list cursor. The `[k]` guard
admitted it, because it compared snapshots structurally and a snapshot is just a
value. The elaboration cannot: a payload decrease has no recursor form, so there
is nothing for a self-call to become. Both functions therefore thread an explicit
`fuel : Nat` with a sufficiency hypothesis `Le (len *v) fuel`, exactly as the
quicksort below does, and the out-of-fuel branch is closed by ex-falso rather than
being unreachable by construction. This is the sharpest instance of the cost
@sec-boundaries records for moving recursion into the eliminators, and it is a
source change rather than an elaboration one — the signature moved, and so did
every caller. A borrow-mode eliminator would return the original form; it is
filed. #status("proposed")

Note what these ensures are stated _in_: `take`, `drop` and `append` are
_observation_ functions, which say what a list _is_ independently of any
implementation. That is the line this architecture holds, and it is a real line —
a declared `back` was a function mirroring the body's own algorithm, and none of
these is. The line is drawn at the development's own vocabulary rather than at
"purity": the same file defines `swapL`, which _is_ a model of a swap, and uses it
in the ensures of a swap leaf. What the quicksort's call tree contains is what the
claim is about, and it contains `count`, `len`, `append`, `Ub`, `Lb` and `Sorted`
— nothing that mirrors a partition or a sort.

*The leaf becomes provable, which contradicted a prior finding.* An earlier reading
held that an in-place leaf mutating through pointer writes has an opaque exit, so no
value-level postcondition about it is provable and delegation to a model-carrying
callee is forced. Half of that is wrong, and the half matters: opacity is a property
of borrows _issued by a call_, not of inline mutation. A leaf doing its own cursor
work through the body's _own_ match-field borrows (doc §3.3) writes into a suspension
that the audit itself collapses, so its exit is a constructor tree over known
snapshots. `set_at`'s base case is literally `{ *hd := x; Refl }` — a strong update
through a field reborrow, where the exit `Cons x` $sigma_"tl"$ _is_
`set Z x (Cons` $sigma_"hd") space sigma_"tl")$ definitionally. Three features had
been filed forward on the strength of the wrong half; two of them evaporated
(@sec-lessons logs the retraction).

*The partition returns two lists, and needs branch equations to do it.*

```rust
fn partition [fuel] (fuel : Nat, v : &mut List Nat, p : Nat, Hf : Le (len *v) fuel)
  -> Σ (hi : List Nat) → Σ (hub : Ub p (*v)) → Σ (hlb : Lb p hi)
       → Σ (hl1 : Le (len *v) (len (old *v))) → Σ (hl2 : Le (len hi) (len (old *v)))
       → Π (n : Nat) → Id Nat (add (count n (*v)) (count n hi)) (count n (old *v))
```

`*v` keeps the elements $lt.eq p$; the rest returns by value. There is no
`partitionL` in the mechanization — no pure model of this function exists — and
every one of the six conjuncts is proved _inductively in the body_ from the
recursive call's own ensures. The bounds are where @identification's branch
equations become load-bearing rather than convenient: the body branches on
`leb x p` and must _produce_ `Le x p` on one side and `Le p x` on the other, and
the same body with `Refl` in place of the equation binder is a rejected test
sitting one screen away in the same file. The two length conjuncts exist only to
feed the recursion below its sufficiency argument.

*Recursion carries its own decrease.* With the model gone, the return type _is_ the
postcondition, and a self-call admitted at it unconditionally proves anything
(@sec-lessons). The decrease is on the declared `[fuel]` — at the time a guarded
side condition on the self-call, and since M27 the position the elaboration
recurses on, `fuel` being the scrutinee of the `natRec` the definition lowers to:

```rust
fn quicksort [fuel] (fuel : Nat, v : &mut List Nat, hfuel : Le (len *v) fuel)
  -> Σ (hs : Sorted (*v)) → Π (n : Nat) → Id Nat (count n (*v)) (count n (old *v))
```

The head is the pivot; the tail is partitioned through `v`; the kept part is sorted
in place through `v` and the returned part through a borrow of the local holding it;
`append_back` glues. `Sorted` here is the _structural_ $Sigma$-chain down the spine,
not the positional `SortedR` above — which is why the $Sigma$-eliminator had to
land before any of this could be written, a caller's whole knowledge of a callee's
exit being a certificate it must be able to take apart. The sufficiency hypothesis
`hfuel` is what makes the out-of-fuel path dead: at `fuel = Z` with a non-empty list
it reduces to $bot$, so the branch is an ex-falso and the guarded recursion is
_total_. Weakening `hfuel` to `Unit` while keeping the parameter — so that the
rejection is about typing and not an unbound name — is a negative control, and the
body is rejected.

One step is more than gluing, and it is the same keystone the positional development
met. `sorted_append_pivot` needs `Ub p` of the left part _after_ it has been sorted,
while the partition bounded it _before_; `Ub`/`Lb` are $Sigma$-chains over the spine
and so are not natively permutation-invariant. The route is to cross to the
multiset, where the property is `Π x. x > p → count x l = Z` and
permutation-invariance is a one-line transitivity, with the two crossings as
ordinary inductions. That the same obstacle appears in both encodings, and yields to
the same move, is the case study's strongest evidence that it is a property of the
problem rather than of either formulation.

The headline holds: `progOk quicksort` is green with zero declared backs in its
call tree, against lying twins for each conjunct — each chosen to survive the `Nil`
path and fail on the recursive one — and against an executing differential that
runs the same declaration on concrete lists and compares with a reference sort.

*What the whole-list shape costs, stated plainly.* It is a workaround for a
structural fact, not a discovery: _a segment of a list is not a place_. A prefix of
a right-nested `Cons` tree is not a subterm of it and neither is a middle; only a
suffix is. So a recursion cannot hand a sub-segment to its callee, and the two
architectures are two ways of paying for that. The positional one hands over the
whole list plus two indices, and pays in a predicate library where every predicate
is range-scoped and every lemma carries a range-fits bound. The whole-list one buys
segment-shaped recursion by _moving ownership_ — relinking cells and gluing with a
traversal where the positional program swaps elements in place — and pays in the
program. Neither is the destination; the calculus is missing the thing that would
make a range a place, which is @sec-lessons's point about posing the problem, met
from the direction that hurts.

== Arrays: when a sub-range is a place <sec-arrays>

Everything above pays, twice over, for one structural fact: a segment of a list is
not a place. A prefix of a right-nested `Cons` tree is not a subterm of it and
neither is a middle; only a suffix is. So a recursion cannot hand a sub-segment to
its callee — it hands the whole structure plus two numbers, and the callee's contract
must then describe the part it must not touch. That is the frame problem, and the
positional development pays it in a predicate library indexed by ranges, in
subtraction-guarded reindexing arithmetic, and in length lemmas whose entire job is to
transport a bound across a mutation that obviously preserves length.

The third development removes it, with one new former and one new rule.

*The former.* `Array n T` — a length-indexed run of element slots, with an index step
`a[i]` and a range step `a[lo ; cnt]` added to the place grammar. A range being a
place is the whole point: a range borrow is then an ordinary `&mut`, and needs no new
kind of reference.

*The rule.* A *carve* is a lazy reorganization that splits an array node into
segments, and it is the calculus's first rule that _consumes evidence_
(@fig-carve). It fires only when handed a comptime proof of `Le (add lo cnt) n` —
whose content is exactly the existence of the residue the split introduces. After it
fires, the two sub-borrows are disjoint not because a checker believed an aliasing
argument but because they are _literally different subterms of one value tree_, and
the suspension machinery of §3.3 already handles those. There is no disjointness
judgment anywhere in the implementation. The slogan is worth stating as the design's
thesis in miniature: *proofs license reorganizations; reorganizations restore
structural disjointness; the borrow machinery is unchanged.*

The comparison that makes this concrete is Rust's. `get_disjoint_mut` ships exactly
this capability — take several disjoint mutable subslices at once — and checks the
disjointness _at run time_, returning a `Result` that can fail. DLLBC is not
inventing the capability; it is moving that check from run time to compile time and
deleting the failure mode. The reason Rust must check at run time is that it has no
comptime fragment to pay a proof from, and having one is this calculus's premise.

*What transferred, measured.* The design predicted that the quicksort library would
port by replacing `listRec` with `arrRec` and `Cons` with `acons`, with none of the
mathematics re-derived. That is verified verbatim across the whole library — the
predicates, the pivot glue, the count layer, and the permutation keystone that cost
the positional development its hardest result — some two dozen definitions and proofs,
each its list counterpart with the container swapped and nothing else changed. What the prediction
omitted is that the array constants must _compute_ the way the list constructors do,
or every step of a transferred proof wants a transport lemma its list original needs
none of; three ι-rules are what make the transfer mechanical rather than merely
possible. One of those is a small lesson in notation: the design note's own spelling
for a singleton, `arrCat (asingle p) r`, was stuck for symbolic `r` — *the chosen
notation could not reach the cons view it is notation for*.

*What did not transfer, and this is the sharper finding.* The partition is a new
program. The list partition is a relational take-and-rebuild returning two lists by
value; the array version needs an in-place scan returning a pivot _index_, because
the recursive calls carve at that index. There is no program to port. And the
algorithm is not a free choice either: two independent _symbolic_ indices into one
array turn out to be unreachable, because after the first carve a second request lands
in a leaf whose offset the machine minted while solving the containment equation — a
value with no surface name — so `swap(a[i], a[j])` at two runtime cursors is not
writable at all. Lomuto's inner loop is therefore not expressible, and what is
expressible is a scan in which every element access sits at index zero of a segment
the program itself carved. The design note offered "the right sub-slice is a segment
with its own zero; there is no reindexing" as a convenience. It is a hard constraint,
and it picks the algorithm.

*The result.*

```rust
fn quicksortA [fuel] (fuel : Nat, n : Nat, hfuel : Le n fuel, a : &mut (Array n Nat))
  -> Σ (hs : SortedA n (*a)) → Π x. Id Nat (countA x n (*a)) (countA x n (old *a))
```

§5.7's signature, re-posed on arrays: sorted and a permutation, over the exit
snapshot, in place, with zero declared backs anywhere in the call tree. It checks,
and — the part that took the most work — it _runs_.

#block(inset: 8pt, stroke: 0.5pt + luma(150), radius: 3pt, width: 100%)[
  _Conformance_ (architecture A) — that the imperative partition and quicksort
  implement their pure models `partScanL`/`sortRangeL`, checked by the
  declared-back audit — was green continuously up to `113f1634` and is a
  *historical* claim after it: the audit that checked it no longer exists, and A's
  cursors do not elaborate under the current checking path. Reproducible at that
  commit; not re-run at this pin. #status("open") _Model correctness_ for that
  route — that `sortRangeL` in fact sorts and permutes — remains open, and is the
  cost of routing verification through a model. It was never discharged, and the
  route's retirement means it now never will be.
  #status("green") _The direct route_ (architecture B, @sec-directroute) is green and does not
  incur that debt: `Sorted (*v)` together with count-preservation against
  `old *v` is proved in the bodies, with no model of the partition or the sort
  anywhere in the development. @sec-architectures compares the two;
  @sec-empirics states what a soundness proof of the machinery _itself_ would
  still have to establish, which neither architecture supplies.
]
