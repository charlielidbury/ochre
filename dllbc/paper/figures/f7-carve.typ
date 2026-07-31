#import "../style.typ": *

== F7: The carve <fig-carve>

// The array era's one new judgment form. It is a REORGANIZATION in F2's sense —
// lazy, demand-driven, rewriting Ω — but it is the only one that CONSUMES A PROOF,
// which is why it is not folded into F2: F2's own gloss is that the borrow
// machinery has no rules of its own beyond bookkeeping, and this rule has content.
// This figure owns the K- prefix.

A *carve* splits an array node into segments so that a sub-range becomes a
subterm. It is a reorganization in @fig-reorg's sense — lazy, fired by a demand,
rewriting $Omega$ and nothing else — with one difference that is the array era's
whole point: *it is the only rule in the calculus that consumes evidence.* @fig-reorg
can say that the borrow machinery has no rules of its own beyond bookkeeping because
every rule there is bookkeeping; this one is not, and that is why it is a separate
figure rather than a seventh reorganization.

What it buys is stated most precisely by comparison. Rust's `get_disjoint_mut` takes
several disjoint mutable subslices at once and checks their disjointness *at run
time*, returning a result that can fail. The carve moves that check to compile time
and deletes the failure mode — and afterwards there is no disjointness judgment in
the system at all, because the two sub-borrows are *different subterms of one value
tree* and @fig-match's suspension machinery already governs those.

=== The extent map

A carved array value is a *segment list*, written $"Arr" chevron.l c_1 ▷ b_1, …,
c_k ▷ b_k chevron.r$: $k$ bodies with their extents, in order. Its *extent map* is
the derived list of *leaves* — each a base, a count, and a body — obtained by summing
the extents left to right. An uncarved array carries no wrapper at all: a
single-segment value and a bare value are the same state, so the wrapper appears only
when $k gt.eq 2$. Two consequences the rules below rely on: a *merge* (adjacent runs
concatenated) is run first, so that @fig-carve's premise (1) sees maximal leaves; and
*rejoin is merge at the moment a payload plugs back into its marker*, which every
End-Mut path funnels through, so no trigger site can be forgotten because none is
listed.

#let leafj(b, c, body) = $(#b, #c, #body)$
#let carvej(p, lo, cnt) = $#p ⧗ [#lo ; #cnt]$

=== The rule

#irule("K-Carve",
  $Omega tack.r #carvej($p$, $"lo"$, $"cnt"$) tack.l Omega'$,
  $Omega(p) arrow.r.long.squiggly^* "merge" quad "leaves"(Omega(p)) in.rev #leafj($b$, $m$, $v$)$,
  $"lo" = "add" space b space "lo'" quad #ownfree($v$)$,
  $#hasT($e$, $"Le" space ("add" space "lo'" space "cnt") space m$)$,
  $m equiv "add" space "lo'" space ("add" space "cnt" space "rest")$,
  $Omega' = Omega[p |-> "Arr" chevron.l "lo'" ▷ v_1, "cnt" ▷ v_2, "rest" ▷ v_3 chevron.r]$,
)

Read the premises in order; each is doing one job.

*(1) Containment — a leaf, not an overlap test.* Some leaf must contain the request.
Because two segments cannot overlap, a range that crosses a segment boundary has no
leaf *at all*, whatever its ownership: the rejection is "no leaf contains it", and no
owned-versus-loaned comparison appears. A request *contained* in a loaned leaf is a
different case and is not rejected — it demand-ends that loan and retries, which is
@fig-reorg's rule reaching its sixth site.

*(2) The obligation, and whose term discharges it.* $e$ is a comptime proof the
*program supplies*; there is no inference and no decision procedure. Two spellings are
forced, and both matter more than they look. The bound is stated *leaf-relatively* —
`Le (add lo' cnt) m` and not `Le (add lo cnt) n` — because `Le` computes by double
recursion and is stuck on a symbolic base, so the global form never converts with
anything a program can supply. And a *concrete* count is unrolled into successors, so
that the obligation at `a[i]` reads `Le (S i) n`. That is not a convenience: it is
character for character the cursor bound the list development has been threading since
its two-cursor swap. The design note claimed those were "on the nose, the containment
obligation the carve demands"; written the obvious way the obligation would have been
`Le (add i (S Z)) n` and the claim would have been false in the one place it was meant
to be exact.

*(3) The residue transition, and the rule that constrains it.* The leaf's extent must
decompose as offset-plus-count-plus-remainder. Solved as an ordinary refl-match
solution transition (@fig-match, #smallcaps[M-Refl-Flex]) — no subtraction is
introduced anywhere, which is the decision that keeps the audit's later conversion
definitional. `rest` may be *minted* by the checker, or *supplied* by the program as
an optional surface slot. Supplying it is what makes a residue nameable downstream,
and it often deletes the obligation outright rather than merely making it writable: a
pivot carve's `Le 1 rest` is unwritable while `rest` is an unnamed σ, and computes to
$top$ the moment `rest := S j` is supplied.

#align(center)[
#irule("K-Cite",
  $"licensed"(m, "cnt", "rest")$,
  $m equiv "add" space "lo'" space ("add" space "cnt" space "rest")$,
)
#h(3em)
#irule("K-Cite-Eq",
  $"licensed"(m, "cnt", "rest")$,
  $#hasT($h_"eq"$, $"Id" space "Nat" space m space ("add" space "cnt" space "rest")$)$,
)
]

#smallcaps[K-Cite] asserts nothing: the decomposition already holds by conversion, and
no evidence is demanded. #smallcaps[K-Cite-Eq] is the other case, and the *only* other
case — there is no third rule that refines the extent directly.

*Premise (3) may not refine a telescope parameter's σ.* This is a soundness rule and
it was found, not designed. When the leaf's extent is a telescope parameter's σ —
which is the case in every program the supplied-residue form exists for — solving the
decomposition by refinement is a refinement of a *universally quantified* length
against terms that may be unrelated, and nothing records the induced constraint in the
signature. Callers are then never held to it: a body carving `[Z ; i ; S j]` out of
`Array n` checked, and so did a caller passing $n = 2$ with $i = j = 5$, which the
concrete machine then got stuck on. That is the differential property *failing* rather
than over-approximating.

The precedent settles it. A body imposing an unrecorded constraint on its callers is
exactly the signature-inferred backward flow of @sec-boundaries, whose lesson is that
cross-boundary constraints are *declared and checked, never inferred*. So the
decomposition must either hold by conversion — #smallcaps[K-Cite], the common case,
asserting nothing — or be *cited* as an ordinary `Id`, checked by @fig-typing before
the same solution transition runs (#smallcaps[K-Cite-Eq]). The measurement that says
this is not a tax: across the three shipped array declarations there are thirteen
carve sites, and *three* need a citation — one each, at the split that the program's
own returned equation is about. Every other carve converts and asserts nothing. A
decomposition a program cannot prove is one it had no business asserting, and the
programs were already returning the equations as honesty decoration before the rule
made them load-bearing.

=== Degenerate cases, and why they are separate

A *whole-leaf* request needs no split and no obligation — `Le m m` computes — and a
*zero-width* request must disturb nothing at all. Both skip the ownership test, because
between a take and its refill a segment holds a hole and the refill is its one legal
successor; testing ownership first rejects the refill. The zero-width case needs its
own segment inserted rather than selecting the leaf it abuts, since `Le (add lo Z) (add b m)` holds at a leaf's *far end* — a subtlety that is unreachable symbolically
(a residue σ is never *known* to be zero) and routine concretely, and which is one of
the four sites of the polarity finding @sec-empirics reports.

=== Two restrictions, stated

#block(inset: (left: 1em))[
  #text(size: 8.5pt)[
  *Rigid extents cannot be sub-carved.* The residue transition needs the leaf's extent
  to be a *flex* σ. A segment whose extent is a constructor tree (`S i`) or a compound
  neutral (`add p q`) equates two rigid terms and is stuck. This bites wider than a
  declared length: it applies to *every* segment's extent, and it is why a three-way
  split cannot be reached by re-associating a two-way one.
  #linebreak()
  *Recursion cannot decrease through a carved payload.* @fig-boundaries's guard counts
  constructor fields as subterms and refuses application spines; a carve refines the
  payload to a concatenation *spine*, so no sub-slice is a structural predecessor of
  its parent. "Recurse on the sub-slice, no fuel needed" is therefore closed, and the
  array sort recurses on fuel like its list counterpart. Teaching the guard that a
  concatenation's arguments are subterms of it would open it, and is filed rather than
  built. #status("proposed")
  ]
]

=== Correspondence

#xref(
  ([#smallcaps[K-Carve]], [`carveAt` (premises in order); `extentMap`], [`S24Arrays`]),
  ([premise (1), merge], [`Val.mergeArrays`, `segsNode`], [`S24Arrays`]),
  ([premise (2)], [`carveAt` obligation formation; `hasType`], [`S24Arrays`]),
  ([#smallcaps[K-Cite] / #smallcaps[K-Cite-Eq]], [`carveAt` (cited-equation arm)], [`S24Arrays` (`threeWayUncited`, `threeWayWrongEq`)]),
  ([rejoin], [`sendPayloadToLoan` → merge], [`S24Arrays`]),
  ([the array library], [`StdLemmas` (M24 section)], [`S24Arrays`, `S25ArrSort`]),
)
