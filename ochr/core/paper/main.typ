#import "style.typ": *

#show: paper.with(
  title: [Proving the Program You Run],
  subtitle: [Mutable borrows inside a dependent type theory, by observation and closing off],
  abstract: [
    Verified systems code today is usually developed three times over: an efficient imperative program that runs, a pure model that the proofs are about, and a refinement proof or translation joining them. We present Ochr, a core calculus in which the in-place program itself appears in types and proofs, so that a development is one program and its properties. Ochr combines Rust-style mutable borrows with a Lean-style dependent type theory, and its definitional equality unfolds in-place code as Lean's unfolds pure code. Three mechanisms make this work. An _observational_ equality `Id A t u` compares two computations by what they return and what they leave in the places they may write; it is a derived proposition that computes to a conjunction of ordinary equations. A call whose body is stuck on an unknown value is _closed off_: its result, and the final content of every place it borrowed, become _sealed programs_, closed source programs that own their state and play the role of Aeneas's backward functions for that call, without a second language. And induction hypotheses are typed in the caller's environment, so that a lemma about a callee's borrowed place is, at the call site, a lemma about the caller's data. We give the calculus with a complete formal definition; worked examples on numbers and binary search trees, including a function that returns a borrow into its argument; an executable Lean checker whose test suite contains every program printed here and every false proof found while designing the calculus; two case studies, a resizing hash map whose development is a third shorter in lines than Aeneas's, although its proofs, without automation, are longer, and a verified in-place quicksort; and a Lean mechanisation of the frame property and of the equations that sealed programs satisfy, for a first-order fragment of an earlier version of the rules, without types or erasure. Consistency and the agreement of the checker's two evaluation paths are conjectures, for which we sketch a set-theoretic model. The checked semantics copies data where compiled code would move it, and the fragment has no shared borrows, loops or borrows stored in data.
  ],
)

= Introduction

#include "sections/intro.typ"

= Ochr by example <sec-overview>
#include "sections/overview.typ"

= The calculus <sec-calculus>
#include "sections/calculus.typ"

= Evaluation and closing off <sec-eval>
#include "sections/eval.typ"

= Observational equality <sec-obs>
#include "sections/obs.typ"

= Typing <sec-typing>
#include "sections/typing.typ"

= Metatheory <sec-meta>
#include "sections/meta.typ"

= Implementation and evaluation <sec-impl>
#include "sections/impl.typ"

= Related work <sec-related>
#include "sections/related.typ"

= Discussion <sec-discussion>
#include "sections/discussion.typ"

= Conclusion
#include "sections/conclusion.typ"
#bibliography("refs.bib", style: "association-for-computing-machinery")

#pagebreak()
#counter(heading).update(0)
#set heading(numbering: "A.1")
= Formal definition <sec-appendix>
#include "sections/appendix.typ"
