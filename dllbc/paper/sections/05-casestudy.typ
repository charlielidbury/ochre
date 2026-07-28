#import "../style.typ": *

= Case Study: A Verified In-Place Quicksort <sec-casestudy>

The preceding sections introduced the four arrows one region at a time; this one
assembles them into a real algorithm. The target is the program a Rust
programmer would recognise — a swap-based in-place Lomuto partition, quicksort
recursing on sub-ranges, no allocation and no take-and-rebuild of whole
sublists — checked not as a bespoke development but as an ordinary
_implementation of a pure model_: each imperative function carries a declared
backward specification (@fig-boundaries), and conformance is conversion. We
build it from the bottom: the slice representation, the borrow-returning
cursors, the bounds proofs that ride the telescope, the smallest self-contained
instance of the whole architecture, the partition, and finally the recursion.
Every listing in this section is quoted from the mechanization at the pin, and
every acceptance and rejection claim it makes is a green `native_decide`
proposition unless a status tag says otherwise.

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

== Cursors, and the disjointness problem

Element access is a borrow-returning recursion. The bounds-checked `nth` walks
the list behind a borrow and hands back a mutable borrow of the requested cell:

```rust
fn nth (v : &mut List Nat, i : Nat, p : Le (S i) (len *v)) -> &mut Nat {
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
fn nth2 (v : &mut List Nat, i : Nat, j : Nat,
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
        cert } }
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
`sortRangeL`:

```rust
fn quicksort (v : &mut List Nat, fuel : Nat, lo : Nat, cnt : Nat,
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

The headline holds: `checkFnOk quicksort` is green — the imperative in-place
quicksort type-checks as an implementation of its pure model `sortRangeL`, with
conformance reduced to conversion (@fig-boundaries). The from-scratch
conformance `native_decide` runs in seconds rather than the pre-fix tens of
minutes, after the delayed-lift `substPure` optimization, and because converting
the declaration to the surface syntax preserved its underlying value byte for
byte, the check replays from `native_decide`'s cache across that surface change;
the performance story is told in full in Section 8.

#block(inset: 8pt, stroke: 0.5pt + luma(150), radius: 3pt, width: 100%)[
  #status("green") _Conformance_ — that the imperative partition and quicksort
  implement their pure models `partScanL`/`sortRangeL`, checked by the
  declared-back audit — is green. #status("open") _Model correctness_ — that
  `sortRangeL` in fact sorts and permutes, and the direct propositional
  restatement `Sorted (*v)` $and$ `Perm (old *v) (*v)` over the exit snapshot —
  is open (the M22 line; @sec-architectures). Routing verification through a
  pure model is the comparison baseline, not the mission; @sec-architectures
  takes up why, and @sec-empirics states what a soundness proof of the machinery
  itself would have to establish.
]
