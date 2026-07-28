# Extraction findings ledger (doc-vs-implementation, from the rule-figure audits)

Prose-wave agents MUST read this file. Each finding names the figure that
recorded it; findings are REPORTED here, resolution belongs to the theory owner.

## From F3 (comptime arrows)
1. **C-Deref proviso is doc-intent only.** reflectC projects a borrow payload
   unconditionally; the doc's suspended-payload stuckness (§5.2) surfaces one
   layer downstream (nfV marker-leaf, later hasType rejection), not at the peel.
2. **Comptime `match` is unimplemented** (reflectC errors on .matchE). The §1.3
   arrow-table's ⇝-cell for `match` is aspirational: it holds today only through
   the recursor constants match would elaborate to (doc §9). The prose section
   presenting the arrow table must footnote this — the one place the table
   overstates the mechanization.
3. **X-Gen is Bool-specific** (generalizeStuck mints σ:Bool only); sufficient
   for the corpus (leb/if splits), narrower than the general rule.
4. **nfV-letIn kernel gap** (restated by F3's C-Let footnote): `let` reduces
   only along reflection, never inside pure normalization/conversion — one of
   the two bimodal surface forms; kernel-rule vs surface-split is an open
   user decision.

## From F1 (runtime ⇒/⇐)
5. **seq is NOT the doc's sugar** (the significant one). Doc §1.1: `t ; t′` ≡
   `let _ = t ; t′` (value parked in a dead slot, loans still locatable). The
   implementation keeps a distinct `.seq` (readR:~1062) that DISCARDS the value
   without running `drop` — an ownership-carrying value sequenced away is not
   returned home; a later end of its dangling loan is stuck. Conservative
   (rejection, not unsoundness), but a real semantics fork: either seq-discard
   must run drop / desugar to let, or the doc's sugar claim changes. THEORY-LINE
   FIX CANDIDATE, not a paper problem.
6. **`*t` in ⇒-read position is place-restricted** (placeToPos): only `*x`,
   `**x`, … — the doc's positional-restriction paragraph states this for
   `:=`/`&mut`/match but not for deref-reads; the implementation enforces it
   uniformly. Doc-polish item.
7. **Doc §2.1's opening trace shows a move of a Nat** that its own copy-on-read
   refinement paragraph supersedes one paragraph later — pedagogical ordering,
   not a conflict; the paper's R-Copy/R-Move present the refined semantics.
   Doc-polish item.

## From F4 (match)
8. **Nested-borrow scrutinee payloads (`borrowM (borrowM …)`) are explicitly
   rejected** as unsupported — a real limitation of the mechanization that doc
   §3 does not record as such. Doc-note candidate.
9. **The set-valued symbolic semantics lives in the `explore` driver ON TOP of
   the single-path monad** — readR.matchE rejects symbolic scrutinees; a
   symbolic match in EXPRESSION position is rejected outright (concrete is
   fine). Architecture fact worth one prose sentence; the paper's set-valued
   judgment abstracts the driver.
10. **§3.5's join reads as implemented until its v0 note** — the doc's own
   note concedes duplication is the baseline, but the join's prominent
   treatment precedes it. Doc-polish: reorder or reframe §3.5. (Comptime-match
   defer and Bool-only generalization already ledgered from F3 — F4 confirms
   both independently.)

## From F6 (typing/conversion)
11. **`convert` is FULL normal-form equality** (`nfV a == nfV b`, Pure.lean:198),
    not whnf-and-compare — the coordinator's brief mis-described it; the figure's
    equivalence/congruence rules are the declarative content of that one
    equality. Relevant to the perf-story section: the unmerged incremental-
    convert experiment measured a wash against exactly this baseline.
12. **A fixed-fuel island**: Refl endpoint conversion hardcodes fuel 1000
    (ctorSig) independent of the threaded fuel — a caveat for any "uniform fuel
    discipline" claim in prose.
13. Presentational facts confirmed: T-Conv is fused into synthesis leaves in
    code (declarative separation is the paper's); the universe rule is
    checking-only under type-in-type; table-miss/arity-mismatch return false —
    which IS the money-test rejection mechanism (§4.2 framing accurate).

## From F2 (reorganization)
14. **Silent spec degradation on multi-captured backs** (the serious one): a
    declared back on a call capturing ≥2 borrows is silently IGNORED — endGroup
    matches backSpec only against captured=[(ℓc,_)], degrading to opaque without
    rejection. A declared promise silently unused is a bug class; THEORY-LINE
    FIX CANDIDATE (reject or support; never silent).
15. **Read/write asymmetry on group-captured owners**: reading demand-ends the
    group; OVERWRITING is rejected ("in flight") because drop calls
    killBorrowInΩ, never endLoan. Doc §2.3's locatability phrasing doesn't
    predict the split. Theory-line item.
16. **Strategy incompleteness vs the nondeterministic rules**: a rules-
    admissible order (End-Mut a live reborrow before the group end) is rejected
    by the implemented endLoan→endGroup→endIssued order when an issued payload
    is suspended. Soundness unaffected; a strategy-completeness question for
    the metatheory section to state.
17. Minor: endIssued's docstring claims a collapse that only Boundary.collapseArg
    performs (comment drift); the "innermost-first" of drop = one own-free
    premise on G-DropBorrow (load-bearing: without it the self-reborrow derives);
    owned-position is a property of F1's demanding move, not of the end — F2
    glosses rather than rules it, deliberately.
