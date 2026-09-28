#import "style.typ": *

#show: paper.with(
  title: [Proving the Program You Run],
  subtitle: [Mutable borrows inside a dependent type theory, by observation and closing off],
  abstract: [
    Verified systems code today is written twice: once as the efficient imperative program that runs, and once as a pure model that the proofs are about, joined by a refinement proof or a translation. We present Ochr, a core calculus in which the two are the same text. Ochr combines Rust-style mutable borrows with a Lean-style dependent type theory, and its definitional equality unfolds in-place code exactly as Lean unfolds pure code. Three ideas make this work. First, an _observational_ equality `Id A t u` compares two computations by what they return and what they leave behind in the places they may write; it is not a new primitive but computes to ordinary equality between observations. Second, a call whose body is stuck on an unknown value is _closed off_: its result, and the final content of every place it borrowed, become _sealed programs_, closed source programs that own their state. Sealed programs are the backward functions of Aeneas, but written in the source language, so the programmer never sees a second language. Third, induction hypotheses are typed in the caller's environment, where the borrow structure around the recursive argument performs the congruence step that a pure proof would write by hand. Proofs about in-place functions become plain structural recursion, frequently shorter than the corresponding proofs about pure functions. We give the calculus, its worked examples (including a function that returns a borrow into its argument), a translation into the calculus of inductive constructions that establishes consistency, and an executable Lean implementation of the checker.
  ],
)

= Introduction

#include "sections/intro.typ"

= Ochr by example <sec-overview>
#include "sections/overview.typ"

= The calculus <sec-calculus>
_Draft pending rule set v1._

= Evaluation and closing off <sec-eval>
_Draft pending rule set v1._

= Observational equality <sec-obs>
_Draft pending rule set v1._

= Typing
_Draft pending rule set v1._

= Metatheory <sec-meta>
_Draft pending the model._

= Implementation <sec-impl>
_Draft pending the Lean checker._

= Related work <sec-related>
#include "sections/related.typ"

= Conclusion
_Draft._
#bibliography("refs.bib", style: "association-for-computing-machinery")
