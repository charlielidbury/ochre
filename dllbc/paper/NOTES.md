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
