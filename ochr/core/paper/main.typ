#import "style.typ": *

#show: paper.with(
  title: [Proving the Program You Run],
  subtitle: [Mutable borrows inside a dependent type theory, by observation and closing off],
  abstract: [
    Verified systems code is usually written three times: an efficient imperative program, a pure model that the proofs are about, and a refinement proof joining them. We present Ochr, a core calculus that puts Rust-style mutable borrows inside a Lean-style dependent type theory, so that the in-place program itself appears in types and proofs. Definitional equality runs programs on symbolic inputs. A call stuck on an unknown value is _closed off_ into _sealed programs_, source programs that compute its result and the final contents of the places it borrowed, in the role of Aeneas's backward functions. An observational equality `Id` compares two computations by what they return and what they write, and computes to ordinary equations, so theorems about in-place code are proved by structural recursion. We give the calculus in full, a Lean checker that checks every program in the paper, and two case studies: Aeneas's hash map, verified with no model and no agreement proof in 11% fewer tokens although its proofs are longer, and an in-place quicksort. Ochr covers mutable borrows only, without shared borrows, loops or borrows in data. Its operational core is mechanised for a first-order fragment; consistency is a conjecture, tested by a differential fuzzer.
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
