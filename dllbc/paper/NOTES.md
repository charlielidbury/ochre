# DLLBC extraction findings — companion ledger to the mock-paper

This file is part of the paper artifact (the "Status of this document" box
declares it so). It records every doc-vs-implementation divergence surfaced
while extracting the six rule figures from the mechanization at the pin
commit (`122bb424`), plus the integration log for the editorial pass that
unified the nine authors' files. Findings are REPORTED here; resolution
belongs to the theory owner. Each finding keeps its original number (1–20 —
the figure-audit findings the paper's §8 counts) and names the figure that
recorded it.

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

1. **C-Deref proviso is doc-intent only** (F3). reflectC projects a borrow
   payload unconditionally; the doc's suspended-payload stuckness (§5.2)
   surfaces one layer downstream (nfV marker-leaf, later hasType rejection),
   not at the peel.

2. **Comptime `match` is unimplemented** (F3; reflectC errors on .matchE).
   The doc §1.3 arrow-table's ⇝-cell for `match` is aspirational: it holds
   today only through the recursor constants match would elaborate to (doc
   §9). The paper footnotes this at the arrow table — the one place the
   table overstates the mechanization. (F4 confirms independently.)

3. **X-Gen is Bool-specific** (F3/F4; generalizeStuck mints σ:Bool only);
   sufficient for the corpus (leb/if splits), narrower than the general rule.

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

19. **Doc ahead of implementation on exit-snapshot return types** (F5): doc
    §5.4 at the pin records the DECIDED exception (borrow-payload derefs in
    return types read the EXIT snapshot; `old *v` = entry) — not implemented
    at 122bb424 (checkFn entry-pins wholesale). The figure follows the
    implementation with a rule-gap at B-Pin (now flagged visibly in-figure);
    §7 presents the decision as the ongoing M22 line.

20. **Unexercised edges, precisely located** (F5): B-Res-Pair builds
    dependent-Σ results with the binder unsubstituted; the ↝ owed S of a
    borrow RETURN is read at return in the exit state (unlike value returns'
    entry-pin) — a dependent S over a consumed parameter would misread;
    auditAction re-reads an unpinned T on value paths. All flagged in-figure.

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

## Authoritative performance numbers (the canonical set)

From the dllbc-simplest final report — same harness before and after, hence
authoritative. §5, §8, and the abstract use these and only these:

- quicksort checkFn, compiled exe: **84,121 ms → 181 ms (465×)**.
- full suite from scratch: **38m49s wall / 2326s CPU → ~13 s wall**
  (12.95 s in the fixing worktree; 16–21 s in later independent verifies,
  load-dependent — "≈13–20 s" is the honest range).
- The "~76 s" figure was a different machine/load measurement of the same
  pre-fix exe; never mix the sets. (Verified absent from the paper.)

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
