#import "style.typ": *

#set document(title: "DLLBC: Dependent Types and Mutation in One Symbolic Interpreter")

#let dark-mode = true
#set text(font: "New Computer Modern", size: 10pt, fill: if dark-mode { white } else { black })
#set page(margin: 2.5cm, fill: if dark-mode { rgb("#1a1a2e") } else { white }, numbering: "1")
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
  both checkers — completed by a _branch equation_ rule that reifies the same
  fact where abstraction has replaced substitution; and, at the boundary, on an
  inversion of the Aeneas pipeline: where Aeneas synthesizes a backward function
  per borrow, DLLBC lets the signature declare it (the $arrow.r.curve$
  obligation is its type, a declared `back` the function itself) and audits the
  body against the declaration at return. Checked and green in the mechanization
  at the pin: the complete rule set of the seven figures, each rule tied to its
  implementing function and exercising test; _three_ in-place quicksorts, which
  between them make the paper's comparison of two verification architectures a
  measurement rather than a prediction — one type-checking as an implementation
  of its pure model `sortRangeL`, conformance reduced to conversion, and two
  carrying no declared backward specification anywhere in their call trees, whose
  return type _is_ their postcondition (sortedness of the exit snapshot, with
  count-preservation against the entry) and whose every proof step is built in
  the body from its callees' postconditions, with no pure model of the partition
  or the sort in either development at all; the *carve*, the calculus's first rule
  that consumes evidence — a lazy reorganization splitting an array into segments,
  licensed by a comptime `Le` proof, after which two range borrows coexist because
  they are literally different subterms of one value tree and no disjointness
  judgment exists anywhere in the system; a declared decreasing-argument guard
  that closed a live unsoundness — an unguarded recursive declaration proved any
  postcondition from itself. Its scope is exactly: a *single*, *declared*
  argument position, checked for strict structural decrease against that
  parameter's current snapshot, on *self*-calls only, with mutual recursion
  rejected outright rather than supported and no general well-founded measures;
  with a sufficiency hypothesis discharging the out-of-fuel path, recursion so
  guarded is total. Also checked at the pin: a
  differential harness relating the symbolic checker to concrete execution,
  validated by turning a removed unsound inference back on and watching it go
  red; and a machine-verified invariant that refinement propagates knowledge and
  never state. The differential is load-bearing rather than reassuring: it found
  the first divergence whose _polarity_ runs the other way, where the checker was
  right and the *machine* was broken — something no amount of checking could have
  revealed, and which a soundness statement phrased as "the checker
  over-approximates" cannot express. And because the two direct-proving quicksorts
  share a specification and no code, running them against each other is evidence
  about the specification rather than about either program: eleven shared inputs,
  agreeing with each other and with a reference sort. Three measurement sets
  appear, and no two are comparable: a profiler-guided substitution fix dropped the
  _conformance_ audit 465× (84,121 ms to 181 ms; the full suite from 38m49s to
  roughly 13–20 s); separately, the two `List` direct-proving quicksorts differ by
  about a thousandfold (21.8 s positional, 21 ms whole-list) with no performance
  work between them, how the problem is posed dominating what the checker costs;
  and the cross-differential's eleven inputs are a count of test cases, not a time.
  Open, and stated as such: the pure model's
  own correctness, which the conformance route rests on and the direct route no
  longer needs; a body cannot yet name the value a consumed binder held, which
  costs the direct route four staged proof-builders that do no mathematical
  work; the v0 kernel is type-in-type with no consistency claim; and three
  identified audit-strategy holes must be closed before any soundness statement
  can quantify over declared specifications. No soundness theorem is claimed.
]))
#v(0.8em)

// ---------------- Status of this document ----------------
#align(center, box(width: 85%, stroke: 0.5pt + luma(140), inset: 9pt, radius: 3pt, align(left)[
  #text(size: 9pt)[
    *Status of this document.* This is a _mock paper_: a paper-shaped audit of
    the DLLBC mechanization, written by extracting the rule figures from the
    implementation at pinned commit `4e950ab7` of the Ochre repository and
    holding every claim to what is checked there. It is not peer-reviewed and
    the calculus is work in progress. Claims carry a uniform status convention —
    #status("green") checked in the mechanization at the pin; #status("in flight")
    under construction; #status("proposed") decided but not mechanized;
    #status("open") a known gap — and untagged claims in the rule figures are
    green. The findings ledger (`NOTES.md`, alongside this document) is part of
    the artifact: it records every doc-vs-implementation divergence the figure
    extraction surfaced, including the ones this paper reports as open holes.

    #text(size: 8.5pt)[The figures were first extracted at `122bb424` and have been
      re-extracted twice since, each time because the artifact's subject changed rather
      than its detail: once when a second verification architecture landed, and once
      when arrays, range places and the carve arrived — the latter adding @fig-carve,
      the first new judgment form since the original extraction. Where a rule moved,
      the figure was re-read against the implementation rather than carried forward.
      The findings ledger keeps each extraction's numbering sealed and records, per
      era, what closed and what remains.]
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
Each figure ends with a rule-to-implementation-to-test correspondence table. Six of
the seven present rules that are, in one way or another, bookkeeping; @fig-carve is
the exception and says so — it is the only rule in the calculus that consumes a proof.
References of the form "doc §N" point into the calculus's design document
(`docs/dllbc-arrows.md` at the pin commit), the specification the figures were
extracted against; `@`-references point within this paper.

#include "figures/f1-runtime.typ"
#include "figures/f2-reorg.typ"
#include "figures/f3-comptime.typ"
#include "figures/f4-match.typ"
#include "figures/f5-boundaries.typ"
#include "figures/f6-typing.typ"
#include "figures/f7-carve.typ"

#bibliography("refs.bib")
