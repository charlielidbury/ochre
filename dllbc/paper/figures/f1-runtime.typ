#import "../style.typ": *
== F1: Runtime reads and writes (⇒/⇐) <fig-runtime>

// Extracted from the implementation (`Dllbc/Machine.lean`, `readR`/`writeR`) as
// the source of truth. F1 is the two RUNTIME arrows only: ⇒ (consume-read /
// move) and ⇐ (fill). The ⇒ arrow also drives `match` (→ F4) and `call`
// (→ F5); those rules live in their own figures and are cited, not restated.

The runtime fragment has two arrows. #evR($Omega$, $t$, $v$, $Omega'$) is the
*consume-read* (a move): it evaluates $t$ to a value, threading the environment
$Omega$ to $Omega'$. #wrR($Omega$, $p$, $v$, $Omega'$) is the *destructive
write*, and it is *fill-only* — its one premise is that the target holds the
hole #vbot. One grammar carries all variation (doc §1.1): the ⇐, take, and `&mut`
rules are only *defined* on *places*, and the same construct means different
things under different arrows.

*Reorganization is presented nondeterministically.* The implementation ends
loans and drops values *lazily and deterministically* — a fuel-bounded
retry fired exactly when a rule's premise is blocked. F1 factors that out into a
single interleaving rule, #smallcaps[R-Reorg], and every other rule takes clean
premises. The reorganization judgment #reorg($Omega$, $Omega'$) is defined in F2
(rule prefix `G-`); F1 only cites it.

=== Places

The write, the `*`-take, and `&mut` act on a *place* (impl `placeToPos`):

#align(center, $ p ::= x #h(1em) | #h(1em) * p $)

A place resolves to a root variable under $n$ `*`-peels. Two conventions,
matching `navRead`/`navWrite`: $"loc"(Omega, p)$ is the value reached by peeling
$n$ #borrowm($$, $$)-layers into the root slot (each peeled layer must be a
borrow, else the step is stuck); and $Omega[p arrow.r.bar w]$ rethreads $w$ back
through those same borrow layers to the root. At $n = 0$ (a bare variable)
$"loc"(Omega, x) = Omega(x)$ and $Omega[x arrow.r.bar w]$ is the ordinary slot
update. This one convention gives reborrow (`&mut *b`), take-at-depth, and
write-through for free.

#let ruled(rule, gloss) = block(width: 100%, breakable: false, inset: (y: 0.4em))[
  #align(center, rule)
  #v(0.35em)
  #align(center, box(width: 92%, text(size: 9pt, style: "italic", fill: luma(90))[#gloss]))
]

=== The ⇒ arrow (consume-read)

#ruled(
  irule("R-Copy",
    evR($Omega$, $x$, $v$, $Omega$),
    $Omega(x) = v$,
    $v #h(0.4em) "index-kind"$),
  [A read of an #footnote[*Index-kind* (impl `indexKindV`): a concrete
    `Nat`/`Bool`/`Unit` tree, any pure-former value (a proof — `Refl` or a
    neutral proof spine — a type, a Π-type, or a λ), or a symbolic σ whose
    σ-context type is one of these. Decided by value *shape* (the σ-context type
    for a σ), never a declared trait; a σ with no σ-context entry is not
    index-kind and moves. Index-kind values are marker-free, so #smallcaps[R-Copy]
    never needs a reorganization.]#h(-0.15em) index-kind value copies it: the
    owner slot is left intact ($Omega$ unchanged), so the value stays
    re-readable. This is why a comptime index may be used more than once (doc §2.1).],
)

#ruled(
  irule("R-Move",
    evR($Omega$, $x$, $v$, $Omega[x arrow.r.bar bot]$),
    $Omega(x) = v$,
    $v #h(0.4em) "data"$,
    $v #h(0.4em) "move-ready"$),
  [A read of *data* (a `Cons`-tree, a pair, a user constructor — anything not
    index-kind) moves it out, leaving #vbot behind; a second read is then stuck
    (no rule). #footnote[*Move-ready*: no loan marker sits in $v$'s owned
    position (the constructor spine), and if $v$ is itself a borrow its payload
    hides no suspended reborrow. Both blockers are ended by #smallcaps[R-Reorg]
    first — an owned-position marker via #smallcaps[G-EndMut] (doc §2.2), a carried suspended
    reborrow via doc §19's flow-back. The implementation checks these inline
    (`firstLoanMarker`; the carried-borrow case at `readR` var, doc §19) and retries;
    F1 makes them #smallcaps[R-Reorg] preconditions.]#h(-0.15em) Data moves even
    when marker-free — silent aggregate duplication is the cost-opacity Rust's
    move discipline prevents, and this calculus keeps that line (doc §2.1).],
)

#ruled(
  irule("R-Ctor",
    evR($Omega_0$, ctorv($C$, $t_1 space dots.h space t_n$), ctorv($C$, $v_1 space dots.h space v_n$), $Omega_n$),
    evR($Omega_0$, $t_1$, $v_1$, $Omega_1$),
    $dots.h$,
    evR($Omega_(n-1)$, $t_n$, $v_n$, $Omega_n$)),
  [A constructor application ⇒-consumes each field left to right, threading
    $Omega$, and assembles the constructor value. A nullary `Nil`/`Z` is the
    $n = 0$ case with no field premises.],
)

#ruled(
  irule("R-Take",
    evR($Omega$, $* p$, $w$, $Omega[* p arrow.r.bar bot]$),
    $"loc"(Omega, * p) = w$,
    $w != bot$,
    $ownfree(w)$),
  [`*p` in read position is a *take*: it moves the located payload out *through*
    the borrow, leaving a hole #vbot at that place. The borrow layers above are
    untouched — `b` itself is not consumed — and the hole's only legal successor
    is a ⇐-fill through it (doc §2.4). This is the update-in-place idiom the calculus
    exists to make routine. The $ownfree(w)$ premise is a *demand*, discharged the
    way every demand is: a payload still holding a parked loan — a `&mut *v` handed
    to a call that has returned, or a field reborrow from a borrow-mode match — is a
    *suspension*, not a value, and #smallcaps[G-EndMut] (@fig-reorg) collapses it
    innermost-first before the take proceeds. Without the premise the *marker* is
    taken and travels on as though it were a value.],
)

#ruled(
  irule("R-Mint",
    evR($Omega$, $amp"mut" space p$, borrowm($ell$, $v$), $Omega[p arrow.r.bar #loanm($ell$)]$),
    $"loc"(Omega, p) = v$,
    $v in.not { bot, #loanm($dot.c$) }$,
    $ell #h(0.4em) "fresh"$),
  [`&mut` mints a fresh loan $ell$: ownership of the located value moves into the
    borrow #borrowm($ell$, $v$), and the marker #loanm($ell$) parks where it sat,
    rendering the source unusable (not vacant — *owed*). At a bare place $x$ this
    is a plain borrow (doc §2.2); at `*b` it is a *reborrow* — the parent `b` is
    suspended, holding #loanm($ell$) where its payload was, recovering when
    $ell$ ends (doc §2.5).],
)

#ruled(
  irule("R-Let",
    evR($Omega$, $"let" x = t \; t'$, $v'$, $Omega_2$),
    evR($Omega$, $t$, $v$, $Omega_1$),
    evR($Omega_1\, x arrow.r.bar v$, $t'$, $v'$, $Omega_2$)),
  [`let` reads its right-hand side by ⇒, binds it to a fresh slot, and reads the
    continuation — the sequencing form of the runtime fragment.],
)

#ruled(
  irule("R-Seq",
    evR($Omega$, $t \; t'$, $v$, $Omega_2$),
    evR($Omega$, $t$, $\_$, $Omega_1$),
    evR($Omega_1$, $t'$, $v$, $Omega_2$)),
  [A sequenced statement is read for its $Omega$-effect and its value discarded,
    then the continuation is read. // RULE-GAP: doc §1.1 calls `t ; t′` sugar for
    // `let _ = t ; t′`, but the implementation keeps a distinct `seq` former
    // (readR .seq) that discards the value WITHOUT running `drop` on it — an
    // ownership-carrying value sequenced away is not returned home. Reported.
    (Doc §1.1 calls this sugar for `let _ = t ; t'`; the implementation keeps a
    distinct `seq` former that discards the value without dropping it — see the
    gaps note.)],
)

#ruled(
  irule("R-Assign",
    evR($Omega$, $p := t \; t'$, $v'$, $Omega_3$),
    evR($Omega$, $t$, $v$, $Omega_1$),
    wrR($Omega_1$, $p$, $v$, $Omega_2$),
    evR($Omega_2$, $t'$, $v'$, $Omega_3$)),
  [Assignment evaluates the RHS by ⇒ *first*, then fills the target place by ⇐
    (a live target is vacated by a drop via #smallcaps[R-Reorg]), then reads the
    continuation. The RHS-first order is doc §2.5's, and it is exactly what makes the
    self-reborrow `b := c` stuck: the RHS consumes `c`, so the value drop needs
    is in flight.],
)

#ruled(
  irule("R-Unit",
    evR($Omega$, $()$, ctorv($"unit"$, $$), $Omega$)),
  [The unit literal reads to the nullary `unit` value with no effect on $Omega$;
    it is what a `let`/`:=`-terminated program ends in.],
)

#ruled(
  irule("R-Lift",
    evR($Omega$, $t$, $v$, $Omega$),
    evC($Omega$, $t$, $v$),
    $t #h(0.4em) "a comptime-only former"$),
  [On the borrow-free fragment ⇒ coincides with the comptime read ⇝ up to
    consumption (doc §1.3): a comptime-only former ($"Type"$, $Pi$, $lambda$, an
    application, $"Id" A space a space b$, a constant) is an *unrestricted* value,
    so ⇒ delegates to ⇝ (impl `readC`) and hands the result back as an ordinary
    runtime datum — storable in a field, passable to a call, returnable. The lift
    is non-destructive (these values are copyable/erasable), so $Omega$ is
    unchanged, modulo the sanctioned pure-`let` entries a ⇝ may introduce (doc §1.3).],
)

=== The ⇐ arrow (destructive write)

#ruled(
  irule("W-Fill",
    wrR($Omega$, $p$, $v$, $Omega[p arrow.r.bar v]$),
    $"loc"(Omega, p) = bot$),
  [⇐ is *fill-only*: its single premise is that the target place holds #vbot, and
    the value drops in. Writing onto a *live* place is not a separate rule — a
    *drop* reorganization (#smallcaps[R-Reorg], doc §2.3) vacates it to #vbot first.
    The place convention makes `x := v`, `*b := v` (write-through), and `**x := v`
    the same rule at $0$, $1$, $2$ peels. A non-place target (`Pair(1) := v`) has
    no `loc`, so it is stuck — this is how ⇐ rejects writes to arbitrary terms.],
)

=== Interleaving

#ruled(
  irule("R-Reorg",
    evR($Omega$, $t$, $v$, $Omega''$),
    reorgs($Omega$, $Omega'$),
    evR($Omega'$, $t$, $v$, $Omega''$)),
  [Before any ⇒ (or ⇐) step, the environment may reorganize — #reorg($Omega$,
    $Omega'$), whose rules live in F2 — to unblock the step: end a loan
    sitting in a value about to move (#smallcaps[G-EndMut], doc §2.2), collapse a match's field-loan chain
    when its owner is demanded (doc §3.3), end a carried suspended reborrow before its
    carrier moves (doc §19), or *drop* a live value at a fill target, vacating it to
    #vbot (doc §2.3). The implementation fires these lazily and deterministically (a
    fuel-bounded retry) exactly when a premise is blocked; F1 states the freedom
    nondeterministically. The identical rule with ⇐ in place of ⇒ supplies the
    drop-before-fill that #smallcaps[W-Fill] and #smallcaps[R-Assign] rely on.],
)

=== Rule ↔ implementation ↔ test

Implementations are in `Dllbc/Machine.lean` unless prefixed; tests are in
`Dllbc/Tests/`. F2's `endLoan`/`drop` implement #smallcaps[R-Reorg]'s premise.
Cells name the *function and case* rather than a line: an earlier version of this
table carried line numbers, and every one of them was wrong within a few
milestones. Test-side anchors are line numbers because those files are stable.

#xref(
  ([#smallcaps[R-Copy]],  [`readR` `.var` (index-kind arm); `indexKindV`], [S2.lean:35 doc §2.1 copy-on-read]),
  ([#smallcaps[R-Move]],  [`readR` `.var` (move arm, and its doc §19 carried-borrow retry)], [S2.lean:101 take-and-refill (`tail` is data → moved)]),
  ([#smallcaps[R-Ctor]],  [`readR` `.ctorApp`; `readArgs`], [S2.lean:88 `Cons(3, Nil)`]),
  ([#smallcaps[R-Take]],  [`readR` `.deref` (`firstLoanMarker` + `endLoan` + retry); `navRead`], [S2 doc §2.4 `let tail = *b`; `S23Direct`]),
  ([#smallcaps[R-Mint]],  [`readR` `.borrow`], [S2.lean:45 `&mut x`; :117 `&mut *b` reborrow]),
  ([#smallcaps[R-Let]],   [`readR` `.letIn`], [S2.lean:26 (every trace)]),
  ([#smallcaps[R-Seq]],   [`readR` `.seq`], [S8Diff.lean:65 `e ; ()`; S19Partition]),
  ([#smallcaps[R-Assign]],[`readR` `.assign`; `writeR`], [S2.lean:53 `*b := 7`; :76 `b := 9`]),
  ([#smallcaps[R-Unit]],  [`readR` `.unit`], [S2.lean:30 trailing `()`]),
  ([#smallcaps[R-Lift]],  [`readR` (pure formers) → `collapseCDerefs`, then `readC`], [S11Lib.lean:72 `botElim` ⇒-lifted; :61 proof into Σ]),
  ([#smallcaps[W-Fill]],  [`writeR` (fill arm); `setAtPos`; `navWrite`; `placeToPos`], [S2.lean:101 fill the hole; :150 non-place reject]),
  ([#smallcaps[R-Reorg]], [`readR` (the retry arms); `writeR` (drop-before-fill); F2's `endLoan`/`drop`], [S2.lean:63 End-Mut before read; :76 drop before fill; :129 chain collapse]),
)
