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
