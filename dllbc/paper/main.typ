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

// ---------------- Abstract (stub) ----------------
#align(center, box(width: 85%, align(left)[
  *Abstract.* TODO — written last. Claims discipline: only what is checked and
  green in the mechanization today; everything else carries an explicit status.
]))
#v(1em)

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
