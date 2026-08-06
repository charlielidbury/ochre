# DLLBC extraction findings — companion ledger to the mock-paper

This file is part of the paper artifact (the "Status of this document" box
declares it so). It records every doc-vs-implementation divergence surfaced
while extracting the six rule figures, plus the integration log for the
editorial pass that unified the nine authors' files. Findings are REPORTED
here; resolution belongs to the theory owner. Each finding keeps its original
number (1–20 — the figure-audit findings the paper's §8 counts) and names the
figure that recorded it.

**Four pins.** The figures were first extracted at `122bb424`; re-extracted at
`4e950ab7` (the second verification architecture); re-extracted again at
`9d92a894` when arrays, range places and the carve landed; and re-extracted at
`dc90adce`, the current pin, after the function model was ratified and the surface
collapsed. The 1–20 numbering is SEALED to the original extraction and is not
renumbered — §8 counts it — so closures are recorded in place (marked CLOSED), and
each re-pin has its own separate section below with its own prefix (`P`/`R` for the
second, `A` for the array era, `N` for the function-model era). Nothing is
renumbered across eras; a claim the paper made about an audit stays checkable
against the audit it was made about.

**The fourth pass is partial by design.** F1, F3, F6 and §2/§3 were left untouched
because a concurrent pass owns the λ/let/mode machinery they describe, and
`main.typ` — which declares the pin — had uncommitted edits elsewhere. Each figure
this pass re-extracted therefore carries its own pin in a header comment, and the
document's declared pin lags them. The last section of this file lists what was
deferred and to whom.

The array era carries its own upstream ledger, `dllbc/docs/DELTAS.md`, which is the
primary source for what that work was like while it happened — 33 entries, including
two conclusions it recorded and a later probe refuted. This file records only what
the *paper* had to change.

The paper's claim discipline leans on this file: §4.5 and §6.5 stated findings
14, 15, and 18 as the audit-strategy holes a soundness statement must close — at
the fourth pin, 14 and 18 are closed BY DELETION and 15 alone survives, and both
sections say so in those terms;
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

14. **CLOSED BY DELETION at the `dc90adce` era. Silent spec degradation on
    multi-captured backs** (F2; the serious one). A declared back on a call
    capturing ≥2 borrows is silently IGNORED — endGroup matches backSpec only
    against captured=[(ℓc,_)], degrading to opaque without rejection. A declared
    promise silently unused is a bug class; reject or support, never silent.
    Cross-confirmed by finding 18. CLOSURE: `Group.backSpec`, `Decl.back` and
    endGroup's spec arm no longer exist (M27), so there is no promise to degrade.
    Recorded as closed-by-deletion and NOT as a fix — nothing was learned about
    how to end a multi-captured spec group correctly. See N2.

15. **STILL OPEN at `dc90adce`, RE-VERIFIED not carried. Read/write asymmetry on
    group-captured owners** (F2): reading demand-ends the group; OVERWRITING is
    rejected ("in flight") because drop calls killBorrowInΩ, never endLoan. Doc
    §2.3's locatability phrasing doesn't predict the split. RE-CHECK: `drop`
    (Machine.lean) still reaches `killBorrowInΩ` on a loan marker and `readR`'s
    `.var` case still reaches `endLoan`. This is now the SOLE survivor of the
    three audit-strategy holes §4.5/§6.5 listed — a completeness gap, not an
    unsoundness. See N2.

16. **Strategy incompleteness vs the nondeterministic rules** (F2): a
    rules-admissible order (End-Mut a live reborrow before the group end) is
    rejected by the implemented endLoan→endGroup→endIssued order when an
    issued payload is suspended. Soundness unaffected; a
    strategy-completeness question the metatheory section states (§6.4).

18. **CLOSED BY DELETION at the `dc90adce` era. Vacuous back-audit paths**
    (F5; the most soundness-relevant finding of the extraction): both back checks
    (B-BackN/B-Back0) take the FIRST qualifying obligation and pass VACUOUSLY when
    none qualifies — and B-Back0 also when the argument borrow is consumed whole
    into a sub-call. A declared back can go entirely unaudited on such paths.
    THEORY-LINE FIX required before any soundness statement quantifies over
    declared specs. CLOSURE: there are no declared specs. Both checks, the rules
    that stated them and `resolveTree` are deleted (M27), so the quantifier is
    empty. Same caveat as 14: closed-by-deletion, not fixed. See N2.

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

* **Aeneas's `split_at_mut` backward function — WAS held out, now VERIFIED and IN.**
  Initially excluded because the `aeneas/` subtree in this repository is the
  mechanized-LLBC Rocq development, not the Lean backend, so a claim about the Lean
  model could not be checked here — and it is a claim about another system, which
  raises the bar rather than lowering it. Since verified against upstream
  `AeneasVerif/aeneas` `main` on 2026-07-31
  (`backends/lean/Aeneas/Std/Slice.lean`): the backward function re-appends the halves
  under a length guard and returns the original slice unchanged otherwise, with a
  source comment recording that totality is deliberate and that correctness holds for
  generator-produced code. §9 now carries it, framed as a *placement* difference
  rather than a defect — the same condition, at the same point, trusted in a
  translate-and-prove architecture and discharged as an obligation here. The framing
  was chosen deliberately: an unfair reading ("Aeneas does not check this") would be
  both wrong and weaker, since the interesting content is the trade, not a scoreboard.
  Line numbers in the original survey had moved; the content is verbatim.
* **The full 33-entry DELTAS ledger.** The paper takes the findings that change a claim
  it makes. The rest — spelling refinements, representation decisions, the transfer
  measurements — belong to the design note and its ledger, which the paper cites rather
  than absorbs.

---

## The function-model era (`9d92a894` → `dc90adce`): what the paper had to change

Entries prefixed `N`, not continuing any earlier numbering. The letter is arbitrary
and deliberately not `M`, which would read as a milestone number in a section that
says "M27" and "M28" on every other line. Two campaigns are covered: **M27**, which
ratified the function model (a definition is a `let` of a sealed λ; `checkFn`,
`Decl.back` and the `[k]` guard deleted; three soundness containments landed), and
**M28**, which collapsed the surface (`decl{ }` and `FnDef` out of the kernel, 27
test files into 10 subject buckets, an end-to-end suite). Each entry was verified
against the implementation before being written into the paper.

This was the first re-extraction in which the dominant change was **deletion**, and
that shaped the whole pass. The house rule that emerged, applied in F2, F5, §4, §6
and §8 and worth stating once: *a finding that stops existing because its feature
stopped existing is recorded as CLOSED BY DELETION and never as a fix.* The
temptation to bank the closures is real — the paper's headline hole count drops from
three to one — and it would be reporting progress the project did not make.

N1. **F5 is a re-extraction, not a revision, and six rules left it.** B-CheckFn (no
    declaration form to quantify over), B-Call-Self and B-Call-Mutual (no `selfRec`,
    no `strictSubterm`, no `reachesFn`), and B-Back-None/B-Back0/B-BackN with the
    `res` suspension-tree resolution (no `back` at all). What arrived in their place
    is not a smaller figure: B-Seal-Fn/B-Body (the check is an EVENT at the `.seal`
    node, with frame isolation), B-Seed-Fn (a Π-typed parameter is a σ in `fsig` —
    this is `ih`, and it is why recursion costs the kernel nothing), B-Inst-Cmp (the
    comptime argument column, which the old figure omitted entirely), and
    B-Call-Unbound (not a rejected recursion — an unbound variable). The deleted
    subsection is replaced by a short historical note pointing at pin `9d92a894`,
    per the convention that history stays recoverable.

N2. **Two of the three audit-strategy holes closed by deletion; one survives and was
    re-verified.** Findings 14 and 18 are marked CLOSED BY DELETION in place. Finding
    15 — the read/write asymmetry on group-captured owners — is STILL OPEN, and this
    was checked in the source rather than carried forward: `drop` reaches
    `killBorrowInΩ`, `readR`'s `.var` case reaches `endLoan`, and the two have not
    converged. **The coordination brief for this pass said all three had closed.**
    They had not; the implementation is the source of truth and the brief was
    followed on the other two and overridden here.

N3. **The `back` tier's precision was replaced by something the old figures never
    showed.** `callDeclC` mints one σ′ per captured loan AT THE CALL, types it at
    that loan's owed type, `markExit`-reflects the return type against it, and PINS
    the captured loan's release to it (`Group.exitRelease`). So the owner a caller
    recovers and the evidence the call returned are the same symbolic value. This
    existed at the previous pin as prose in §4 and §7 ("a single symbolic value is
    shared…") and appeared in NO rule; it is now a premise of B-Call and a case of
    G-EndGroupOpaque. Worth flagging as a class: the previous extraction found the
    gaps by reading rules against code, and this one was found by reading the code
    for a mechanism the prose asserted and the rules did not state.

N4. **A rules-level agreement that is not a premise.** The pinned release and the
    callee's exit snapshot are the same σ′ only because `callDeclC` builds both from
    one list. Nothing in the rules records the identification — the callee's audit
    defines its own σ_exit, and the caller reflects against its own σ′. Recorded as a
    metatheory obligation in F2's rule-gap rather than forced into a premise, since
    the honest statement is about two derivations agreeing, not about one rule.

N5. **The corpus's list `partition` and `append_back` changed SIGNATURE, and §5's
    listings were stale in the way §8's anecdote predicts.** Both used to decrease
    through the borrow's payload (`[v]`); a payload decrease has no recursor form, so
    `fnElab` refuses it, and both now thread `fuel : Nat` with a sufficiency
    hypothesis `Le (len *v) fuel`. This is the second instance of §8's "a paper about
    a moving mechanization decays silently" — same section, same kind of staleness,
    two pins later. §8's anecdote gained it; the listings were corrected against
    `Direct.lean`.

N6. **The differential's harness validation was DOWNGRADED, and §6 leads with it.**
    The `forceConstrained` flag and `Group.constrained` are deleted (M28 τ), so the
    control no longer reintroduces the bug in a real kernel and watches the finder
    catch it; the same discrimination is asserted at the COMPARATOR, over a
    hand-written wrong-refinement environment. What is kept: the relation says NO to
    the wrong refinement and YES to the honest σ, so it is not a relation that
    refuses everything. What is given up: the demonstration that the finder, driven
    by a genuinely buggy kernel, reaches that comparison at all. The suite's own
    docstring records this as "a real reduction in strength"; the paper does too,
    because §6's whole argument is that an unvalidated counterexample finder is
    worthless as evidence.

N7. **The v1 differential's counts are UNCHANGED and remain asserted.** 136 generated
    / 75 accepted / 238 runs; per telescope 91/47/141, 32/15/45, 13/13/52. Re-checked
    at this pin rather than carried over, because the harness became program-shaped
    (`progOk` over a `prog{ }` let-chain, no wrapper and no table) and a change in
    plumbing that moved a count would have been a change in behaviour. It did not.
    §6 now quotes the per-telescope triples, and states "unchanged" as itself a claim.

N8. **Two STALE DOCSTRINGS in the implementation, reported not fixed.** (a)
    `St.fsig`'s docstring says the signature is stored "as a `FnDef`, which is
    precisely a telescope and a return type with no body"; M27-δ changed it to store
    the Π ITSELF, which the field's own inline comment two screens down explains. (b)
    The differential suite's header still states its property as "if `checkFn`
    accepts a declaration", and `checkFn` has not existed since M27-δ; the assertions
    below it use `progOk`. Neither affects a rule or a count. Reported here rather
    than edited, since this pass owns the paper and not the mechanization.

N9. **F4 and F7's rules survived both campaigns untouched, which is a result.** All
    seventeen implementation functions their correspondence tables cite still exist
    under the same names and none moved. What broke was the ANCHORS: the M28
    consolidation put 27 era-numbered files into 10 subject buckets, so every table
    in the paper cited files that no longer exist. The namespaces survived the move
    verbatim, so all four tables (F2, F4, F5, F7) now cite bucket file + namespace,
    which is the form that stays true under another consolidation.

N10. **One F7 prose claim cited deleted machinery while remaining true.** "Recursion
    cannot decrease through a carved payload" was justified by the `[k]` guard
    counting constructor fields as subterms and refusing application spines. The
    guard is gone; the restriction stands, for a better reason — the eliminators a
    definition may lower to are `Nat`'s and a list's, and a concatenation spine is
    the scrutinee of neither. Restated on that footing, which also makes its
    `#status("proposed")` opening move honest: what would open it is an array
    eliminator, not a relaxed side condition.

N11. **Architecture A is doubly unreachable, and §7's fence named only one reason.**
    §7 already fenced A at `113f1634` on the grounds that its cursors recurse through
    a borrow's payload. True, and not the first obstacle: the audit that checked a
    declared back does not exist either. The two are independent — reversing one
    would not restore A — and the fence now says both. §5's status box and its
    "quoted from the mechanization at the pin" preamble were NOT fenced and are now:
    the section runs at two pins and says which listings belong to which.

N12. **What the paper can no longer claim about model correctness.** §5's status box
    listed "model correctness for architecture A — that `sortRangeL` in fact sorts
    and permutes" as OPEN. It was never discharged, and with the route retired it now
    never will be. Recorded as a cost of the retirement rather than left as an open
    item that quietly stopped being worked on.

### Deferred to the pass that owns the files this one does not

* **`main.typ`'s pin declaration.** The "Status of this document" box still declares
  `9d92a894`. Every figure this pass re-extracted carries its own pin in a header
  comment (`dc90adce`); the declaration itself, and the abstract, are a later pass's,
  since `main.typ` had uncommitted local edits elsewhere during this one.
* **F1, F3, F6 and §2, §3.** A concurrent pass is changing the λ/let/mode machinery
  those describe. Two consequences visible from here: §2's arrow table has no row for
  the `.seal` node, which is a ⇒-form with real content (F5's B-Seal-Fn), and F6 owns
  no seal rule although the seal's VALUE case is exactly `readC`-then-`hasType`.
  Neither was touched.
* **`style.typ`.** Its rule-prefix pin table still lists `B-Back…`, `B-CheckFn` and
  `G-EndGroupBack`, and the helpers `backJ`, `resolve`, `hole`, `checkFn` and
  `groupb` are now unused. F5's one new judgment form (`bodyJ`) is defined LOCALLY in
  the figure rather than promoted, to keep this pass out of a file a concurrent one
  may be editing. Promotion and pruning belong together, in whichever pass owns
  `style.typ` next.
