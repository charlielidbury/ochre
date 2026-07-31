# DLLBC extraction findings — companion ledger to the mock-paper

This file is part of the paper artifact (the "Status of this document" box
declares it so). It records every doc-vs-implementation divergence surfaced
while extracting the six rule figures, plus the integration log for the
editorial pass that unified the nine authors' files. Findings are REPORTED
here; resolution belongs to the theory owner. Each finding keeps its original
number (1–20 — the figure-audit findings the paper's §8 counts) and names the
figure that recorded it.

**Three pins.** The figures were first extracted at `122bb424`; re-extracted at
`4e950ab7` (the second verification architecture); and re-extracted again at
`9d92a894`, the current pin, when arrays, range places and the carve landed. The
1–20 numbering is SEALED to the original extraction and is not renumbered — §8
counts it — so closures are recorded in place (marked CLOSED), and each re-pin has
its own separate section below with its own prefix (`P`/`R` for the second, `A` for
the array era). Nothing is renumbered across eras; a claim the paper made about an
audit stays checkable against the audit it was made about.

The array era carries its own upstream ledger, `dllbc/docs/DELTAS.md`, which is the
primary source for what that work was like while it happened — 33 entries, including
two conclusions it recorded and a later probe refuted. This file records only what
the *paper* had to change.

The paper's claim discipline leans on this file: §4.5 and §6.5 state findings
14, 15, and 18 as the audit-strategy holes a soundness statement must close;
§8.2/§8.3 tell findings 5, 18, and the comptime-match deferral (2) as the
lessons; the arrow-table footnote in §2 is finding 2 verbatim.

## Theory-line fix candidates (behavior to change, not prose)

5. **`seq` is NOT the doc's sugar** (F1; the significant one). Doc §1.1:
   `t ; t′` ≡ `let _ = t ; t′` (value parked in a dead slot, loans still
   locatable). The implementation keeps a distinct `.seq` (readR:~1062) that
   DISCARDS the value without running `drop` — an ownership-carrying value
   sequenced away is not returned home; a later end of its dangling loan is
   stuck. Conservative (rejection, not unsoundness), but a real semantics
   fork: either seq-discard must run drop / desugar to let, or the doc's
   sugar claim changes.

14. **Silent spec degradation on multi-captured backs** (F2; the serious
    one). A declared back on a call capturing ≥2 borrows is silently
    IGNORED — endGroup matches backSpec only against captured=[(ℓc,_)],
    degrading to opaque without rejection. A declared promise silently
    unused is a bug class; reject or support, never silent. Cross-confirmed
    by finding 18.

15. **Read/write asymmetry on group-captured owners** (F2): reading
    demand-ends the group; OVERWRITING is rejected ("in flight") because
    drop calls killBorrowInΩ, never endLoan. Doc §2.3's locatability
    phrasing doesn't predict the split.

16. **Strategy incompleteness vs the nondeterministic rules** (F2): a
    rules-admissible order (End-Mut a live reborrow before the group end) is
    rejected by the implemented endLoan→endGroup→endIssued order when an
    issued payload is suspended. Soundness unaffected; a
    strategy-completeness question the metatheory section states (§6.4).

18. **Vacuous back-audit paths** (F5; the most soundness-relevant finding of
    the extraction): both back checks (B-BackN/B-Back0) take the FIRST
    qualifying obligation and pass VACUOUSLY when none qualifies — and
    B-Back0 also when the argument borrow is consumed whole into a sub-call.
    A declared back can go entirely unaudited on such paths. THEORY-LINE FIX
    required before any soundness statement quantifies over declared specs.

## Mechanization limitations, recorded in-figure

1. **PARTLY CLOSED at the re-pin. C-Deref proviso is doc-intent only** (F3).
   reflectC still projects a borrow payload unconditionally, so the "v proper"
   side-condition is not tested at the peel. What changed is that the condition
   is now ESTABLISHED before the read: on the pure lift (a body reading live
   state) `collapseCDerefs` demand-ends a parked loan first, and treats a bare
   variable whose own loan a call still holds as a place too. `readC` proper
   stays the read-only projection. Residue is presentational: the figure states
   as a side-condition something a premise elsewhere establishes.

2. **Comptime `match` is unimplemented** (F3; reflectC errors on .matchE).
   The doc §1.3 arrow-table's ⇝-cell for `match` is aspirational: it holds
   today only through the recursor constants match would elaborate to (doc
   §9). The paper footnotes this at the arrow table — the one place the
   table overstates the mechanization. (F4 confirms independently.)

3. **X-Gen is Bool-specific** (F3/F4; generalizeStuck mints σ:Bool only);
   sufficient for the corpus (leb/if splits), narrower than the general rule.
   CONSEQUENCE at the re-pin: it bounds the branch-equation form too — at a
   stuck split the equation is always an `Id Bool`. X-Gen also gained a second
   OUTPUT (the normalized pre-abstraction spine), which is the only thing a
   stuck-split equation can be built from.

4. **nfV-letIn kernel gap** (F3): `let` reduces only along reflection, never
   inside pure normalization/conversion — one of the two bimodal surface
   forms; kernel-rule vs surface-split is an open user decision.

8. **Nested-borrow scrutinee payloads (`borrowM (borrowM …)`) are explicitly
   rejected** (F4) as unsupported — a real limitation of the mechanization
   that doc §3 does not record as such.

9. **The set-valued symbolic semantics lives in the `explore` driver ON TOP
   of the single-path monad** (F4) — readR.matchE rejects symbolic
   scrutinees; a symbolic match in EXPRESSION position is rejected outright
   (concrete is fine). The paper's set-valued judgment abstracts the driver;
   the elaboration note in F4 states the architecture fact.

12. **A fixed-fuel island** (F6): Refl endpoint conversion hardcodes fuel
    1000 (ctorSig) independent of the threaded fuel — a caveat for any
    "uniform fuel discipline" claim.

19. **CLOSED at the re-pin. Doc ahead of implementation on exit-snapshot return types** (F5): doc
    §5.4 at the pin records the DECIDED exception (borrow-payload derefs in
    return types read the EXIT snapshot; `old *v` = entry) — not implemented
    at 122bb424 (checkFn entry-pins wholesale). IMPLEMENTED at 4e950ab7:
    `checkFn` mints one σ_exit per borrow param and `markExit` rewrites the
    return type so a bare `*v` pins to it and `old *v` to the entry σ. B-Pin
    re-extracted; the rule-gap note is gone. The exit σ's live only in the pin
    and `exitSyms` until the audit defines them by substituting each borrow's
    collapsed final payload — a dedicated audit-local pass, NOT a ⇜, because it
    carries a mutation result and ⇜ is knowledge-only.

20. **Unexercised edges, precisely located** (F5): B-Res-Pair builds
    dependent-Σ results with the binder unsubstituted; the ↝ owed S of a
    borrow RETURN is read at return in the exit state (unlike value returns'
    entry-pin) — a dependent S over a consumed parameter would misread;
    auditAction re-reads an unpinned T on value paths. All flagged in-figure.

## The re-pin (`122bb424` → `4e950ab7`): what the figures gained

Recorded as a section rather than as new numbered findings, because these are
not divergences between doc and implementation — they are rules that did not
exist at the first extraction. Each was verified against the implementation
before being written into a figure.

R1. **F4 — the branch equation.** `matchE` gained an optional equation binder;
    `match h : x { … }` binds `h` in every branch to a proof that the
    scrutinee's pre-split value equals that branch's constructor. Presented as a
    shared premise `eqn(h, τ, p, C σ̄)` threaded through all four match rules,
    with three cases collapsing to one reading: `Refl` on a concrete scrutinee
    and on a plain symbolic one (⇜ has already equated the endpoints), a fresh
    σ only at a stuck split. Correspondence rows: `bindEqnRefl`,
    `mintStuckEqn`/`symOwnedSetup`, tested in `S23Direct`.

R2. **F5 — the recursion guard, and it closed a live unsoundness.** Before it,
    a self-call was admitted at the function's own declared return type with no
    side condition, so `fn bad () -> Id Nat Z (S Z) { bad() }` was ACCEPTED.
    Added as B-Call-Self (the actual at the declared `[k]` must be a strict
    structural subterm of that parameter's current snapshot, which ⇜ carries
    like every other σ-bearing component) and B-Call-Mutual (the absence of a
    rule; `reachesFn` rejects mutual recursion outright, since a
    per-declaration guard would admit `f → g → f` with nothing decreasing).
    Error strings: "declares no decreasing argument", "not a strict structural
    predecessor", "mutual recursion … is not supported".
    NOTE FOR §1/abstract: "no termination checking" was TRUE at the first pin
    and is FALSE at this one — corrected in both.

R3. **F3/F6 — `sigmaRec`.** A new recursor with an ι-rule
    (`sigmaRec A B P f (Pair a b) ⇝ f a b`, `Pure.whnfV`) and a `hasType` case.
    Non-recursive, one arm, no `ih` — so explicitly NOT the natRec/boolRec/listRec
    scheme the F3 gloss elides, and written out rather than folded into it. Both
    premises cross a binder because Σ's second parameter is a family.

R4. **F1 — the take's demand.** `readR`'s `.deref` now demand-ends a parked loan
    before taking (`firstLoanMarker` + `endLoan` + retry), so R-Take gained an
    own-free premise. Without it the marker itself was taken and travelled on as
    a value — the same silent-marker class as finding 1 and as §3.2's
    ⊥-into-a-pure-value bug. With finding 1's lift-side fix this is the same rule
    at a second site; the calculus document now states it once ("every demand
    collapses first") with the sites as instances.

R5. **F5 — `buildResult` threads dependent Σ results.** B-Res-Pair's RULE-GAP
    note said the second Σ component was built independently of the first. It now
    receives the already-built components substituted into its type, so a pinned
    result reaches a caller usable rather than with a dangling binder.

### Not re-extracted, and why

F2 (reorganization) was re-read and needed nothing: the M23 changes added
demand-SITES for G-EndMut, not new reorganizations, and G-EndMut's own statement
is unchanged. The three open theory-line findings (14, 15, 18) are untouched
behaviour and remain open at this pin.

## Doc-polish items (prose fixes to the calculus document)

6. **`*t` in ⇒-read position is place-restricted** (F1, placeToPos): only
   `*x`, `**x`, … — the doc's positional-restriction paragraph states this
   for `:=`/`&mut`/match but not for deref-reads; the implementation
   enforces it uniformly.

7. **Doc §2.1's opening trace shows a move of a Nat** that its own
   copy-on-read refinement paragraph supersedes one paragraph later —
   pedagogical ordering, not a conflict; the paper's R-Copy/R-Move present
   the refined semantics.

10. **Doc §3.5's join reads as implemented until its v0 note** (F4) — the
    doc's own note concedes duplication is the baseline, but the join's
    prominent treatment precedes it. Reorder or reframe §3.5.

## Presentational facts confirmed (no action)

11. **`convert` is FULL normal-form equality** (F6; `nfV a == nfV b`,
    Pure.lean:198), not whnf-and-compare — the coordinator's brief
    mis-described it; the figure's equivalence/congruence rules are the
    declarative content of that one equality. Relevant to §8's perf story:
    the unmerged incremental-convert experiment measured a wash against
    exactly this baseline.

13. T-Conv is fused into synthesis leaves in code (declarative separation is
    the paper's); the universe rule is checking-only under type-in-type;
    table-miss/arity-mismatch return false — which IS the money-test
    rejection mechanism (doc §4.2 framing accurate).

17. Minor (F2): endIssued's docstring claims a collapse that only
    Boundary.collapseArg performs (comment drift); the "innermost-first" of
    drop = one own-free premise on G-DropBorrow (load-bearing: without it
    the self-reborrow derives); owned-position is a property of F1's
    demanding move, not of the end — F2 glosses rather than rules it,
    deliberately.

## Performance numbers: TWO SETS, and the fence between them

There are now two performance results in the paper. They measure different
things, and combining them into one comparison would be wrong. Anyone editing
§5, §8, §7's table, or the abstract must keep them apart.

**Set 1 — the substitution fix (a CHECKER change).** From the dllbc-simplest
final report; same harness before and after, hence authoritative:

- CONFORMANCE quicksort checkFn (`back = sortRangeL`), compiled exe:
  **84,121 ms → 181 ms (465×)**.
- full suite from scratch: **38m49s wall / 2326s CPU → ~13 s wall**
  (12.95 s in the fixing worktree; 16–21 s in later independent verifies,
  load-dependent — "≈13–20 s" is the honest range).
- The "~76 s" figure was a different machine/load measurement of the same
  pre-fix exe; never mix it in. (Verified absent from the paper.)

**Set 2 — the encoding (a SPECIFICATION-AND-PROGRAM change, no checker work).**
Two DIRECT-PROVING quicksorts, both proving sortedness plus count-preservation,
same machine, same checker, same build configuration:

- positional (`SortedR cnt lo`, swap-based Lomuto over a range): **21.8 s**
- whole-list (`Sorted` as a Σ-chain, two-list partition): **21 ms**

**The fence.** Set 1's 84,121 ms and Set 2's 21.8 s are not comparable: the
first is a conformance audit against a pure model, the second a propositional
postcondition, and they are different programs. Nor is Set 1's 181 ms directly
comparable to Set 2's 21 ms, for the same reason. What Set 2 supports is a claim
about how the PROBLEM IS POSED, and even there the honest scope is narrower than
"encoding": the two differ in both specification encoding AND partition program,
the two differences are coupled (the positional spec exists because a swap-based
scan mutates a range; the whole-list spec is what makes a two-list partition
natural), and NO experiment here isolates one from the other. §8 states that
bound explicitly; do not let an edit quietly widen it to "the encoding alone".

## Integration log (editorial pass, branch `paper-integration`)

Resolved during figure-wave and prose-wave work:

- B-SpecEnd/G-EndGroupBack dedupe: DONE by F5 itself (commit 4987cd4e);
  the caller-side spec end lives solely in F2 as G-EndGroupBack, division
  stated in-figure.
- Model-name check RESOLVED: `sortRangeL` (the index-bounded model) IS the
  green headline model; PROGRESS's older `sortL` naming refers to the
  superseded take/drop spec-level model.

Resolved during the integration pass (this branch):

- style.typ chevron deprecations fixed; F2's and F5's figure-local judgment
  helpers promoted to style.typ; the spec-carrying group notation unified on
  one form (F5's superscript variant folded into F2's inline `back f` form).
- F3's ⇜-reach box and F5's refinement-reach conventions checked for
  consistency on the self-back spec: consistent (F3 itemizes it; F5's "the
  reflected backward specs" covers both).
- All bare `§N` references in figures normalized to `doc §N`, with the
  convention stated once in the Rules intro; prose rule-name references
  verified to exist in the figures (one stale name fixed: §4 cited
  B-SpecEnd, now G-EndGroupBack + B-Call); status tags unified on the
  `#status()` convention; section @-refs and the deferred bibliography
  cites wired (refs.bib entries only).

### Contradiction log (fixed toward this ledger)

- §8.3 claimed the extraction produced **21** recorded findings; this ledger
  numbers **20** (items 21–24 of the original file were integration TODOs
  and resolutions, not findings). §8.3 now says 20.

### Currency pass (this pin)

- Pin moved `122bb424` → `4e950ab7`; figures re-extracted where rules moved
  (see the re-pin section); the two-era scaffolding that had been added for the
  branch-equation write-up was REMOVED, since re-pinning subsumes it.
- §7's architecture-B status tags (`in flight`/`proposed`) and the abstract's
  "ongoing mission" clause were stale and are corrected; §5 now works BOTH
  quicksorts, architecture A through §5.6 and architecture B in §5.7.
- Abstract/§1's "no termination checking" corrected (see R2).
- §6.5 said "two" audit-strategy holes where §4.5 and the abstract said "three";
  reconciled by distinguishing the two that bear on audit SOUNDNESS from the
  third, which is a rejection (a completeness gap) — the counts now agree.
- §5.6 and §7.1's conformance-quicksort listings gained the `[fuel]` annotation
  the guard migration added to the real declaration (verified at
  `S19Partition.lean:670`).
- §8 gained a fourth lesson (how the problem is posed is a performance decision)
  and a fourth member of the lying-twin class (the recursion guard); its
  retraction list gained a third entry, the delegation discipline, withdrawn at
  this pin.
- Verified still true at this pin, not merely carried over: findings 2 (comptime
  match unimplemented), 4 (nfV-letIn), 8 (nested-borrow scrutinee rejected),
  14/15/18 (the three open theory-line holes); full `lake build` green.
- §6.1's differential counts RE-MEASURED at this pin rather than carried over,
  since M23 touched the match form the generator emits and the take rule the
  bodies exercise. Unchanged, and exact: 91/47/141 for `(v : &mut List Nat)`,
  32/15/45 for `(n : Nat)`, 13/13/52 for `(b : &mut Nat, c : Bool)` — 136
  generated, 75 accepted, 238 runs.
- …and then ASSERTED, which is the one mechanization change in this pass. Those
  counts lived in a doc-comment nothing checked — which is precisely why the pass
  had to re-measure them by hand. `S8Diff.lean` now carries six `native_decide`
  assertions at its foot: the three per-telescope pairs, and the three totals the
  header comment and §6.1 actually quote. Liveness confirmed by flipping one and
  watching the build go red. They are DESCRIPTIVE, not normative — a legitimate
  change to the generator or to what the checker accepts should update the
  numbers, the header comment and §6.1 together; what the assertions forbid is
  changing any one of them silently.

---

## The array era (`4e950ab7` → `9d92a894`): what the paper gained

Entries prefixed `A`, not continuing any earlier numbering. Each was verified against
the implementation or the suites before being written into the paper.

A1. **@fig-carve is new, and it is the first new judgment form since the original
    extraction.** Placed as a seventh figure rather than folded into F2 for a reason
    the figures themselves make: F2's gloss is that the borrow machinery has no rules
    of its own beyond bookkeeping, and the carve has content — it consumes a proof.
    Absorbing it would have contradicted the figure it was absorbed into. The figure
    states premises (1) containment, (2) the leaf-relative obligation, (3) the residue
    transition, plus the citation rule, the degenerate cases, and the two restrictions
    (rigid extents cannot be sub-carved; recursion cannot decrease through a carved
    payload).

A2. **The polarity finding, in §6 and in the abstract.** The first divergence in which
    the *concrete* machine was the wrong side — a call's re-mint repairing execution
    rather than abstracting it. Promoted deliberately from an empirics observation to
    part of the central claim, because it is the one thing a design argument
    structurally cannot reach: the machine is what such an argument reasons *from*.
    §6.5's simulation obligation was rewritten as a consequence — phrasing it as "the
    checker over-approximates" is now a known error, not a simplification.

A3. **The cross-differential, fenced as a THIRD measurement set.** Two implementations
    sharing a specification and no code, agreeing on eleven inputs with each other and
    with a reference sort. Verified in the suite rather than transcribed: the check is
    a *conjunction* (both agree AND both match the reference), so a two-way agreement
    on a wrong answer still goes red, and a failure on either side cannot masquerade
    as agreement. The eleven inputs were counted in the source.

A3b. **A ledger claim I could not reproduce, and did not transcribe.** DELTAS says
    "exactly TWO carves in the whole lane need a citation". Counted in the source, the
    three shipped declarations have thirteen carve sites with *three* citations — one
    each in `splitA`, `partitionA` and `quicksortA` (the suites hold twelve cited
    carves in total, the rest being probes and lying twins). The ledger may be counting
    distinct carve *shapes*, or may be one out. The paper states the measured numbers.
    Worth a note to the era's authors rather than a correction to their ledger, which
    is a historical record and should not be edited to match.

A3c. **A second count I could not reproduce.** The ledger and the merge message both
    say the transferred library is "twenty-one definitions and proofs". Enumerating the
    ledger's *own* list of what transferred (six predicates, nine glue lemmas, three
    count lemmas, six permutation-keystone items) gives twenty-four, and `StdLemmas`
    holds twenty-five array-suffixed items once M25's invented `SplitA`/`PartA` are
    included. The discrepancy does not touch the substantive claim — that the transfer
    is verbatim — so §5 states the strata and "some two dozen" rather than a precise
    number I cannot land on. Same recommendation as A3b: raise with the authors.

A4. **The constrained-wire principle gained a third act** (§4). The carve's premise (3)
    may not refine a telescope parameter's extent, for exactly the reason a backward
    flow may not be inferred from a signature: it constrains callers without recording
    it. Worth the paragraph because the precedent decided a rule nobody had imagined
    when it was set.

A5. **Two claim reversals recorded as reversals** (§8's retraction discipline). The
    design note's advice to carve inline and reach for a function only for abstraction
    is *withdrawn* — the boundary is what makes the program possible; and its "one
    stratum deleted, one inherited, none invented" is corrected to *one invented*, at
    the partition's interface. §7's cost model for architecture B updated accordingly.

A6. **A fifth lesson** (§8): run the differential at both extent regimes and default to
    neither. Every late-hiding defect in the era was invisible at one regime and
    routine at the other.

### Not carried into the paper, and why

* **Aeneas's `split_at_mut` backward function.** The design note's survey reports it as
  total by fiat — silently returning the original slice when the length guard fails,
  sound only because generated code satisfies the guard. It is a sharp comparison for
  the carve, which makes exactly that guard a checked proof. NOT USED: the `aeneas/`
  subtree in this repository is the mechanized-LLBC Rocq development, not the Lean
  backend, so the claim cannot be verified here, and it is a criticism of another
  system. §9 makes only the `get_disjoint_mut` comparison, which is a public API
  surface. If someone verifies the backward-function claim against the Aeneas sources,
  it strengthens §9 considerably and should go in.
* **The full 33-entry DELTAS ledger.** The paper takes the findings that change a claim
  it makes. The rest — spelling refinements, representation decisions, the transfer
  measurements — belong to the design note and its ledger, which the paper cites rather
  than absorbs.
