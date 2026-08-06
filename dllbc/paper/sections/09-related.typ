#import "../style.typ": *

= Related Work <sec-related>

DLLBC sits at the intersection of two lines that rarely meet: the verification
of Rust-style mutable borrowing, and full dependent type theory. We position it
against the closest work in each, and against the handful of systems that, like
DLLBC, try to hold both at once.

== Aeneas and LLBC

The closest kin is Aeneas @aeneas-2022 and its underlying Low-Level Borrow
Calculus @ho-fromherz-protzenko-2024. DLLBC borrows LLBC's loan/borrow *value*
semantics — mutable references modelled as loans and borrows in the operational
state rather than as pointers into a heap — and its symbolic execution
wholesale. The founding identification of this calculus, that matching a
symbolic scrutinee *is* dependent pattern matching, is the observation that
LLBC's symbolic interpreter already does, verbatim, what Agda-style dependent
elimination does by unification and substitution; DLLBC's comptime write (⇜) is
that mechanism named and reused for types.

The inversion is where DLLBC departs. Aeneas *synthesizes* a backward function
for each mutable borrow from the loan structure, as one stage of a translation
pipeline (Rust → LLBC → a pure functional model → a proof assistant), and the
program's correctness is then proved about the extracted model in Lean, Coq, or
F\*. DLLBC turns the synthesized artifact into a *declared and checked* signature
component. It did this at two strengths, and the history is the interesting part
of the comparison rather than a caveat on it. At full strength a function wrote
`back = f` in its type and the checker verified it by converting the borrow's
suspension tree against the declaration at the return audit — and because the
declaration was checked rather than derived, backward specifications *composed*
along call chains, a caller resolving a sub-call's group-end through the callee's
declared spec, which reconstructed LLBC's backward-function composition as a
checking discipline internal to one language. That tier has since been removed
from the calculus (@sec-boundaries), leaving the weaker and more basic form: the
$arrow.r.curve$ obligation, which declares the backward function's *type* rather
than the function, and a postcondition over the exit snapshot. So the current
system inverts Aeneas's pipeline without reconstructing its composition: what a
caller learns is what the callee's signature says, and the reasoning that Aeneas
does about a synthesized model is done here in the body, against the value the
borrow holds at exit. Which of the two is the better answer to Aeneas is a
question this paper poses rather than settles; @sec-architectures has the
measurements that were taken while both existed. The single-language stance is
unaffected, and is the second difference: the imperative
program, its dependent types, and its pure model are all terms of the same
calculus under one conversion relation, with no translation boundary between the
code and the logic it is verified against.

== Prophecy-based specification

RustHorn @matsushita-2020, RustHornBelt @rusthornbelt-2022, Creusot
@denis-2022, and Verus @lattuada-2023 specify mutable borrows through *prophecy*
variables: a mutable reference's final value is a logical variable, constrained
at the point the borrow ends, so a postcondition may speak about a value the
program has not yet produced. DLLBC's snapshot discipline deliberately *refuses*
prophecy. Its ↝ obligation and exit-snapshot postconditions are the
prophecy-free alternative — a borrow's contract is discharged against the value
actually present when its loan ends, never against a promised future. The
calculus doc makes the case for the refusal directly (doc §4.2): per-loan contracts
on coupled data would have to state conditions like "a vector whose length
matches whatever the *sibling* loan ends with" — a promise about another loan's
future, which is exactly what prophecy formalizes. DLLBC dissolves the coupling
instead of naming it: the sibling writes are unchecked strong updates, and the
*joint* condition is checked once, at the boundary, when both final values are
in hand and forming the result is a matter of conversion.

== Refinement types for Rust

Flux @flux-2023 equips Rust with refinement types that support *strong updates*
— a value's refinement may change as it is mutated in place — which makes it the
nearest neighbour in spirit for in-place verification, and the direct
descendant of Liquid-type refinement @liquidhaskell-2014. DLLBC differs in the
strength and decidability of its type discipline. Flux's refinements are drawn
from an SMT-decidable logic and discharged by an SMT solver; DLLBC carries full
CIC-style dependency — indexed families via large elimination, arbitrary
type-level computation — and its only decision procedure is conversion. The
boundary money test — a forgotten length update leaving a stuck type that no
constructor inhabits — is a conversion failure, not a solver query.

== Disjoint mutable subslices

The carve (@fig-carve) lands in a crowded area, and the honest positioning is that the
crowd already has every component. Three concerns are separable, and every system here
separates them: an *interval-arithmetic disjointness predicate*, present in Low\*
@protzenko-2017, in VST, and derivable in Iris; an *exclusivity discipline* that makes
coexistence a question worth asking, which is Rust's borrow checker, separation logic's
separating conjunction, or Verus's @lattuada-2023 tracked ghost tokens; and a
*recombination story*, which is Iris's magic wand, Aeneas's @aeneas-2022 backward
function, Creusot's @denis-2022 prophecies, or RustBelt's @rustbelt-2018
inheritance-at-lifetime-death.

What is claimed as new is the *conjunction*, not any component: ownership-transferring,
exclusivity-enforcing range borrows whose coexistence is licensed by comptime evidence
_the checker consumes_, over a heapless value-tree semantics. No system in the list
routes the disjointness predicate through the program's own dependent proofs in order
to license exclusivity inside the operational semantics. Rust hardwires it, and only
for constant indices. Separation logic discharges it in the meta-logic, by a proof
written in a proof mode rather than one the checker consumes. Low\* has the predicate
and the recombination but no exclusivity at all — its buffers may overlap freely, so
disjointness is never a permission question, only a framing one.

The concession belongs in the same breath, because a reader will reach for it: *Rust
already ships this API surface.* `get_disjoint_mut` takes range indices and returns
several disjoint mutable subslices, checking disjointness at run time and returning a
result that can fail. DLLBC is therefore not inventing a capability. It is moving an
existing capability's check from run time to compile time and deleting the failure
mode — a smaller claim than new expressive power, and the honest one. It is not a
small claim either, because _why_ Rust must check at run time is that it has no
comptime fragment to pay a proof from, and having one is this calculus's premise.

The sharpest comparison is with Aeneas @aeneas-2022, because it makes the *same*
condition appear at the *same* point with a different status. Aeneas models
`split_at_mut` in Lean with a backward function that re-appends the two halves when
their lengths are unchanged, and returns the original slice untouched when they are
not#footnote[`backends/lean/Aeneas/Std/Slice.lean` in `AeneasVerif/aeneas`, verified
against `main` on 2026-07-31. The guard is `if h1 : s0'.length = s0.length ∧
s1'.length = s1.length then ⟨s0'.val ++ s1'.val, …⟩ else s`, with a source comment
recording the reasoning: totality is wanted, the underlying update handles any length
gracefully, and the model is correct when the condition holds, "which is always the
case for code generated by Aeneas."]. This is a deliberate and defensible choice
rather than an oversight: the backward function is made *total by fiat* so that it
composes unconditionally, and its correctness is then conditional on the generator
only ever producing calls that satisfy the guard.

What it illustrates is the axis this section runs on. In a translate-and-prove
architecture the pure model is a *trusted* artifact — the translation is where the
guarantee is grounded, and a modelling step may buy totality with an assumption about
its own producer. In DLLBC the same length condition is the carve's premise (2), and
it is neither assumed nor discharged by construction: it is an obligation a program
term must inhabit, checked by the same conversion that checks everything else, at the
moment the split happens. Neither placement is obviously right, and the trade is
legible — Aeneas gets a total, composable model and pays with a proof obligation that
lives outside the artifact, while DLLBC gets the obligation inside the program and
pays by requiring every caller to carry a proof term. Stating where the condition
*lives* is more useful than claiming either system checks more.

== Dependent and linear type theories

ATS @xi-2017 combines dependent and linear types with explicit *views*:
stateful, separated resources threaded through the program to license mutation.
DLLBC's value semantics needs no view threading — the loan and borrow machinery
lives in the operational state, and the surface program reads like ordinary
code, its mutation-through-aliases tracked by the checker rather than spelled
out by the programmer. Quantitative Type Theory @atkey-2018, as realized in
Idris 2 @brady-2021, places linearity *in* the types by tracking usage
multiplicities, but governs erasure and resource counting rather than borrowing:
it has no reborrows and no strong updates through an alias, which are exactly the
constructs DLLBC is built to type.

== Deductive verification and the `old`/`ensures` correspondence

Dafny @leino-2010 pairs each method with an `ensures` clause in which `old(e)`
names the value of `e` on entry — the design ancestor of DLLBC's exit-snapshot
postconditions, where a return type's `old *v` reads the entry snapshot and its
borrow-payload derefs read the exit. The difference is where the correspondence
comes from. Dafny *decrees* the `old`/`ensures` semantics as a specification
construct; DLLBC *derives* it from loan structure — the entry-pin and
exit-snapshot readings fall out of *where* the ↝ obligation is consulted, not
from a separate assertion language layered over the code. Low\* @protzenko-2017
targets the same domain of verified low-level software, but verifies against an
explicit heap model discharged by SMT, where DLLBC verifies against a heap-free
loan/borrow value semantics discharged by conversion. The broader deductive
landscape for Rust — Prusti @astrauskas-2022, the semantic-soundness foundation
of RustBelt @rustbelt-2018, and the hybrid symbolic approach of Gillian-Rust
@gillian-rust-2025 — shares DLLBC's target but not its ambition to make the
specification language and the type theory one and the same.

== Lineage

DLLBC subsumes the earlier Och staging — the core calculus that isolated the
unification of terms and types, subtyping in the pure-subtype-systems line
@hutchins-2010, and dependent elimination before any mutation was in scope —
for the mutation question, and is the Ochre programme's
@lidburyOchreDependentlyTyped2024 working answer to how full dependent types
and in-place mutation inhabit a single system.
