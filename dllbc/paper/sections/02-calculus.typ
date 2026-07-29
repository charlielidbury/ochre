#import "../style.typ": *

= The Language at a Glance <calculus>

DLLBC has a single syntactic category of terms. Types are terms of universe sort, and the borrow machinery --- mutable borrow, dereference, and the borrow type --- consists of ordinary term formers within it. The familiar stratification into a "pure" language of types and a "runtime" language of programs is not drawn syntactically; it is recovered _semantically_, as the fragment on which certain of the four arrows are defined.

== Values are trees; there is no heap

Programs execute against an _environment_ $Omega$ mapping variables to _values_, and a value is a tree: a constructor applied to values, plus a few ownership-tracking forms. There is no heap and no addresses. A mutable reference is modeled by _moving ownership of a subtree to the reference_ --- the value becomes #borrowm($ell$, $v$), carrying its payload $v$ under a fresh loan identifier $ell$ --- and leaving a marker #loanm($ell$) where the subtree used to sit. The symbol #vbot marks a vacant slot: not a value of any type but the _absence_ of one, excluded from every read-shaped rule.

This value semantics buys the calculus its central property. Types may mention program values, but only as _snapshots_: the (possibly symbolic) value a variable held at a fixed moment, written $sym("")$ for an unknown one. A snapshot is a copy, never a location, so no mutation can make a type stale --- the one guarantee the design exists to provide. Because a borrow _carries_ its payload, a deref `*b` appearing in a type is a pure projection of that payload, `*`#borrowm($ell$, $v$) $arrow.r.squiggly v$, never a store lookup that could read the wrong thing.

Two regimes coexist over these values. Inside a function body, borrowing is _contract-free_: the checker is a symbolic interpreter running the very rules the runtime runs, and it simply watches each payload change. Contracts appear only at _boundaries_ --- function signatures, and borrows stored under a type constructor --- the opaque places the interpreter cannot watch through. There is exactly one place a body's borrows are ever _judged_ against a type: the audit at return.

== The four arrows

All evaluation and checking is organized by four judgment forms over the one grammar. Two are runtime, two comptime; two read, two write.

#figure(
  table(
    columns: (auto, 1fr, 1fr),
    align: (left, left, left),
    inset: 7pt,
    table.header([], [*read*], [*write*]),
    [*runtime*],
    [$evR(Omega, t, v, Omega')$ --- consume-read: evaluate $t$ to a value with move semantics],
    [$wrR(Omega, t, v, Omega')$ --- destructive write: fill the location $t$ denotes with $v$],
    [*comptime*],
    [$evC(Omega, t, v)$ --- comptime read: evaluate in the borrow-free fragment],
    [$refi(S, x, t, S')$ --- comptime write: refine the snapshot layer by substitution],
  ),
  caption: [The four arrows. $Omega$ is the runtime environment; the comptime read leaves no $Omega'$, being effect-free; the comptime write ranges over the whole checker state $S$.],
)

The comptime pair is not a second semantics. It is the _same machine restricted to the borrow-free, assignment-free fragment_: comptime read threads $Omega$ over pure entries, but excludes the constructs that touch the loan state (minting a borrow, consuming through one) and excludes assignment outright, so its only footprint on $Omega$ is the fresh pure entries its `let`s introduce. "No side effects at the type level" is thus a _fragment property_, not a separate rule set --- and it is what an eventual erasure pass will rely on, since types must be deletable without disturbing the state the runtime sees. The comptime _write_ $arrow.l.squiggly$ is the checker's refinement judgment, fired on entry to a match branch; it has no surface syntax at all --- no program text elaborates to it.

Which arrows are defined on which constructs is the skeleton of the language. @arrow-map reproduces it. Two regularities organize everything that follows. _Down the columns:_ the $arrow.r.squiggly$ column is the $arrow.r.double$ column minus the borrowing rows, minus assignment, and minus consumption --- the comptime fragment made visible. _Across the rows:_ several constructs mean different things under different arrows --- `*t` reads destructively, locates non-destructively, or projects a snapshot; `match` destructures or reborrows by the scrutinee's mode; a variable is a move, a write target, a snapshot read, or a refinement site --- one grammar, with the arrows carrying all the behavioral variation. The rule figures (@fig-runtime, @fig-reorg, @fig-comptime, @fig-match, @fig-boundaries, @fig-typing) are the unpacking of this table, one region at a time; the prose below runs the machine on a handful of programs to fix intuitions first.

#figure(
  table(
    columns: (auto, auto, auto, auto, auto, 1fr),
    align: (left, center, center, center, center, left),
    inset: 5pt,
    table.header(
      [*construct*],
      [$arrow.r.double$], [$arrow.l.double$], [$arrow.r.squiggly$], [$arrow.l.squiggly$],
      [*note*],
    ),
    [`x`], [✓], [✓], [✓], [✓],
    [$arrow.r.double$ is the move; $arrow.l.double$ fills a vacant slot; $arrow.r.squiggly$ reads the snapshot; $arrow.l.squiggly$ _is_ refinement],
    [$"Type"_i$], [✗], [✗], [✓], [✗], [comptime value; no runtime representation],
    [$piT(x, tau, tau')$], [✗], [✗], [✓], [✗], [as above],
    [$lambda (x : tau). t$], [✓], [✗], [✓], [✗], [no capture, so formation is inert: $Omega' = Omega$ even under $arrow.r.double$],
    [$t space t'$], [✓], [✗], [✓], [✗], [$arrow.r.double$: the call rule; $arrow.r.squiggly$: $beta$/$iota$-reduction],
    [`T`], [✗], [✗], [✓], [✗], [a comptime value],
    [`T.c`], [✓], [✗], [✓], [✗], [constructor values exist in both worlds; $arrow.r.double$ consumes the fields],
    [`match t {…}`], [✓], [✗], [✓#footnote[The $arrow.r.squiggly$ cell for `match` is aspirational. Comptime $iota$-reduction of `match` on the pure fragment is not implemented in the v0 mechanization; type-level case analysis holds today only through the recursors that `match` would _elaborate_ to (the CIC eliminators of @fig-comptime), pending the substitution discipline for binders. It is the one cell where this table runs ahead of the mechanization.]], [✗],
    [$arrow.r.double$: two modes by scrutinee type, branch entry refines by $arrow.l.squiggly$; $arrow.r.squiggly$: $iota$-reduction, stuck on symbolic],
    [$"let" x = t ; t'$], [✓], [✗], [✓], [✗], [sequencing in both fragments],
    [$t := t' ; t''$], [✓], [✗], [✗], [✗], [$arrow.r.double$: RHS by $arrow.r.double$, target by $arrow.l.double$; excluded from the comptime fragment],
    [`&mut t`], [✓], [✗], [✗], [✗], [mints a loan; `&mut *x` is reborrow],
    [$borrowT(s, tau, S)$], [✗], [✗], [✓], [✗], [the borrow _type_ is comptime, though borrow _values_ are not],
    [`*t`], [✓], [✓], [✓], [✓],
    [the peel, arrow-generic: takes, locates, projects, or refines the payload],
  ),
  caption: [The construct/arrow table: the map of the language.],
) <arrow-map>

== First programs

We now run the machine, annotating $Omega$ after each step. One standing convention governs the traces: _reorganization is lazy_. The environment may be rewritten between two steps --- a loan ended, a displaced value dropped --- but the checker does so only when some rule's premise demands it, never eagerly. The demand does the work.

*Moves, and the vacant slot.* A bare use of a variable is a $arrow.r.double$-read: it consumes.

```rust
let x = 3;         // Ω = x ↦ 3
let y = x;         // Ω = x ↦ ⊥, y ↦ 3
```

The second line is $evR(Omega, x, 3, Omega[x |-> #vbot])$: the value moves out and #vbot is left behind. A second use of `x` is simply stuck --- no read rule fires on #vbot --- which is how use-after-move becomes the absence of a derivation rather than a special error. A vacant slot is refillable, and writing onto a slot that is _not_ vacant forces a drop first, inserted lazily. One refinement earns its place from the mechanization's brush with index arithmetic: a $arrow.r.double$-read of an _index-kind_ value --- a concrete `Nat`/`Bool`/`Unit` tree, any pure-former value, or a symbolic one of such a type --- is a _copy_, the owner keeping it (@fig-runtime, #smallcaps[R-Copy]). On such values the ownership machinery is doubly vacuous; on data proper --- `Cons`-trees, pairs, user constructors --- a move stays a move, keeping Rust's line that silently duplicating aggregates hides cost.

*Borrowing, writing through, and ending.* Minting a borrow moves the payload to the reference and parks a loan marker at the source; writing _through_ the borrow locates the payload without consuming the reference; and the loan ends only when a later demand forces it.

```rust
let x = 3;         // Ω = x ↦ 3
let b = &mut x;    // Ω = x ↦ loanₘ ℓ, b ↦ borrowₘ ℓ 3
*b := 7;           // Ω = x ↦ loanₘ ℓ, b ↦ borrowₘ ℓ 7
let y = x;         // demand for x forces End-Mut ℓ first:
                   // Ω = x ↦ 7, b ↦ ⊥;  then the move: x ↦ ⊥, y ↦ 7
```

The write `*b := 7` peels one indirection under $arrow.l.double$ and replaces the payload in place; no contract governs it, because inside the body borrowing is contract-free. The last line is where laziness pays out: the move needs to read `x`, but `x` holds a loan and no rule applies, so the environment reorganizes first. #smallcaps[G-EndMut] (@fig-reorg) plugs the borrow's current payload back where the marker sits and kills the borrow --- itself just a $arrow.l.double$-fill aimed at the environment's own bookkeeping --- after which the move proceeds. Nothing marked _when_ $ell$ had to end; the demand for `x` did.

*Take and refill.* Under $arrow.r.double$ the peel `*b` moves the payload out _through_ the borrow, leaving a hole; the only rule then applicable at `b` is the $arrow.l.double$-fill back through it. This is the in-place update idiom the calculus is built to make routine:

```rust
let x = Cons(3, Nil);
let b = &mut x;            // Ω = x ↦ loanₘ ℓ, b ↦ borrowₘ ℓ (Cons 3 Nil)
let tail = *b;            // Ω = …, b ↦ borrowₘ ℓ ⊥, tail ↦ Cons 3 Nil
*b := Cons(7, tail);      // Ω = …, b ↦ borrowₘ ℓ (Cons 7 (Cons 3 Nil)), tail ↦ ⊥
```

Between the take and the refill, `b` holds a hole --- a state both Rust (error E0507) and LLBC @ho-fromherz-protzenko-2024 forbid, because a panic in the gap would end the loan with the owner recovering garbage. DLLBC has no panic and the hole cannot escape: #vbot satisfies no read rule, and no function boundary can be crossed while an argument borrow holds one. No list node was copied, and under compilation the value's journey out and back is no journey at all.

*Where the rules of ownership are.* The reborrow `&mut *b` borrows a borrow's payload, suspending the parent until the child's loan ends; composed with drop it produces the calculus's classic stress test, the _self-reborrow_ `b := c` after `let c = &mut *b`, which DLLBC deliberately _rejects_ --- the chain to be dropped runs through the very value being written, so no ending rule fires and drop is stuck (@fig-reorg). Other calculi in this family accept it at the price of ghost variables; declining to pay keeps drop a total procedure and $Omega$ free of inaccessible entries. The section's lesson survives the rejection: the borrow machinery has _no rules of its own_ beyond bookkeeping. Every step above is $arrow.r.double$ for the moves, $arrow.l.double$-fill for every write, and two reorganizations --- #smallcaps[G-EndMut] and drop --- aimed at an environment that remembers who owes whom.
