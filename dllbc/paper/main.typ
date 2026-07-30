#import "style.typ": *

#set document(title: "DLLBC: Dependent Types and Mutation in One Symbolic Interpreter")
#set text(font: "New Computer Modern", size: 10pt)
#set page(margin: 2.5cm, numbering: "1")
#set par(justify: true)
#set heading(numbering: "1.1")
#show link: underline

#align(center, text(size: 17pt, weight: "bold")[DLLBC: One Grammar, Four Arrows])
#align(center, text(size: 11pt)[A mock-paper on the Dependent Low-Level Borrow Calculus — draft])
#v(1em)

// ---------------- Abstract ----------------
#align(center, box(width: 85%, align(left)[
  *Abstract.* DLLBC, the Dependent Low-Level Borrow Calculus, puts full
  dependent types and Rust-style mutable borrowing in one language and checks
  both with one symbolic interpreter: a single term grammar, four evaluation
  arrows (runtime read and write, comptime read and write), and a checker that
  runs function bodies on symbolic arguments, so that borrow checking and
  dependent type checking are two readings of one execution. The design rests
  on an identification — LLBC's symbolic refinement of a matched scrutinee _is_
  Agda-style dependent pattern matching, one substitution mechanism serving
  both checkers — and on an inversion of the Aeneas pipeline: where Aeneas
  synthesizes a backward function per borrow, DLLBC lets the signature declare
  it (the $arrow.r.curve$ obligation is its type, a declared `back` the
  function itself) and audits the body against the declaration at return.
  Checked and green in the mechanization at the pin: the complete rule set of
  the six figures, each rule tied to its implementing function and exercising
  test; an in-place, swap-based quicksort that type-checks as an
  implementation of its pure model `sortRangeL`, conformance reduced to
  conversion; a differential harness relating the symbolic checker to concrete
  execution, validated by turning a removed unsound inference back on and
  watching it go red; a machine-verified invariant that refinement propagates
  knowledge and never state; and, after a profiler-guided substitution fix, a
  465× drop in the conformance check (84,121 ms to 181 ms; the full suite from
  38m49s to roughly 13–20 s). Open, and stated as such: the pure model's own
  correctness is in flight; the project's ongoing mission is the pivot from
  model-conformance to proving propositional postconditions directly over exit
  snapshots; the v0 kernel is type-in-type with no consistency claim and no
  termination checking; and three identified audit-strategy holes must be
  closed before any soundness statement can quantify over declared
  specifications. No soundness theorem is claimed.
]))
#v(0.8em)

// ---------------- Status of this document ----------------
#align(center, box(width: 85%, stroke: 0.5pt + luma(140), inset: 9pt, radius: 3pt, align(left)[
  #text(size: 9pt)[
  *Status of this document.* This is a _mock paper_: a paper-shaped audit of
  the DLLBC mechanization, written by extracting the rule figures from the
  implementation at pinned commit `122bb424` of the Ochre repository and
  holding every claim to what is checked there. It is not peer-reviewed and
  the calculus is work in progress. Claims carry a uniform status convention —
  #status("green") checked in the mechanization at the pin; #status("in flight")
  under construction; #status("proposed") decided but not mechanized;
  #status("open") a known gap — and untagged claims in the rule figures are
  green. The extraction's findings ledger (`NOTES.md`, alongside this
  document) is part of the artifact: it records every doc-vs-implementation
  divergence the figure extraction surfaced, including the ones this paper
  reports as open holes.
  ]
]))
#v(1em)

// ---------------- Contents ----------------
#{
  show outline.entry.where(level: 1): set text(weight: "semibold")
  outline(title: [Contents], depth: 2, indent: 1em)
}
#pagebreak()

// ---------------- Prose sections ----------------
#include "sections/01-intro.typ"
#include "sections/02-calculus.typ"
#include "sections/03-identification.typ"
#include "sections/04-boundaries.typ"
#include "sections/05-casestudy.typ"
#include "sections/06-empirics.typ"
#include "sections/07-architectures.typ"
#include "sections/08-lessons.typ"
#include "sections/09-related.typ"

// ---------------- Rule figures ----------------
= The Rules of DLLBC <rules>
The complete rule set, presented *nondeterministically*: reorganization
(@fig-reorg) may fire wherever its premises hold; the implementation's lazy,
fuel-bounded strategy (fire a reorganization only when a rule's premise demands
it) is one deterministic scheduling of these rules, discussed in @sec-empirics.
Each figure ends with a rule-to-implementation-to-test correspondence table.
References of the form "doc §N" point into the calculus's design document
(`docs/dllbc-arrows.md` at the pin commit), the specification the figures were
extracted against; `@`-references point within this paper.

#include "figures/f1-runtime.typ"
#include "figures/f2-reorg.typ"
#include "figures/f3-comptime.typ"
#include "figures/f4-match.typ"
#include "figures/f5-boundaries.typ"
#include "figures/f6-typing.typ"

#bibliography("refs.bib")
