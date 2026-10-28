# 13. Fording vs indices: how Ochr should express indexed families

Started by team-lead on 2026-10-28 from a discussion with the user. Status: **decided, option B** (user, 2026-10-28; lane `fording`). Induction on proofs, the related decision below, is still open. This is a language design decision, not a question about the Lean formalisation or the consistency proof, though it should be settled before that proof starts, because it changes the cases for inductive declarations, `Eq` and [Split].

## The question

Some types and propositions are naturally *families* whose recursive occurrences vary in an argument: `Vec(A, n)` (a list of exactly `n` elements), `Le(n, m)`, a permutation relation, reachability in a graph, a typing judgement. How should Ochr let a programmer define them?

## Terms

- **Index.** A native inductive family, as in Lean, Coq and Agda: `inductive Vec (A) : Nat → Type | nil : Vec A 0 | cons : A → Vec A n → Vec A (n+1)`. The kernel knows indices; matching unifies them.
- **Fording.** The index becomes an ordinary parameter, and each constructor stores a proof of what the index equals: `Vec(A, n) := Nil(h : Eq(Nat, n, Z)) | Cons(m : Nat, x : A, xs : Vec(A, m), h : Eq(Nat, n, S(m)))`. Needs value parameters, equation-typed fields, and recursive occurrences at a different parameter (`Vec(A, m)` inside `Vec(A, n)`).
- **Recursive family.** A type computed by recursion on the index: `Cells(E, n)` in `Examples/Array.lean`. Works when the index determines the shape.
- **Dependent fields.** The length is stored at runtime beside the data: `Vec(E) := MkVec(len, items : Array(E, len))` (docs/06).

These are not replacements for each other. A compile-time length (an index, a Forded parameter or a recursive family) and a runtime length (a dependent field) put the data on different sides of the compile-time/runtime divide and generate different code; the programmer chooses, and one is often defined in terms of the other. A compile-time length cannot change in place; that is what being a compile-time constant means, not a cost of any option.

## Where Ochr is today

- Inductive parameters are uniform; there are no indices (D45: "No indices, so `Eq` stays primitive").
- `Eq` is primitive and observational: it computes by the structure of the values it compares. This is what `Id` is built on.
- Equation-typed fields are rejected (`Check.lean`, `firstOrderTerm` and the K4 check). There was never a reason: equations fell outside D36's "first-order data" wording of positivity, and K4 grouped `Eq` with Π, sorts and `&` though its only recorded attack is for Π (fording-probe).
- Inductives have no usable value parameters: every argument of `D(ā)` is a type position, so `n : Word` can be declared but never applied (`Tag(Succ(Zero))` is "written where a type is expected"). No inductive in the suite has one. This is a gap independent of this decision.
- Non-uniform recursive occurrences: the paper forbids them; the checker accepts closed ones (`Nest(A) := … Deeper(n : Nest(Unit))`), a mismatch.
- Recursion is never on a proof: the decreasing argument must be a `Type₀` inductive, since a proof's value is ⋆ (RULES note 21). So there is no induction on a derivation of a `Prop` inductive.
- Relations are written as recursive functions into `Prop` (`Le`, `Lt`, `Sorted`, `OnlyIn`, `Count`), and compile-time-sized data as recursive families (`Cells`, `Array`).

## Why the examples have not hit this

The case studies verify in-place programs over data, and every specification they need is a property computed by recursion on that data. The awkward cases were written around: quicksort's permutation is "equal counts" rather than "related by swaps", and quicksort recurses on fuel because there is no well-founded recursion. The gap shows in specifications that are relations with intermediate steps: transitive closure, permutation by swaps, small-step semantics, typing judgements with non-syntax-directed rules, and anything proved by induction on a derivation. Those can be written today only with an explicit step count and a purpose-built existential, and proved only by induction on the step count.

## The options

**A. Status quo.** Recursive families for data, recursive functions into `Prop` for relations, step counts for relations with intermediate steps.
- For: no rule change; the smallest consistency proof.
- Against: relations with intermediate steps lose their natural definition and their natural induction principle; the corpus so far was chosen around the gap.

**B. Fording, as an emergent property.** Three relaxations of [Ind-decl] and nothing else: value parameters (an argument at a non-sort parameter is an erased position, not a type position), equation-typed fields, and non-uniform recursive occurrences. Probed on branch `fording-probe` (about 30 checker lines; all 1,558 existing verdicts unchanged).
- For: no new construct. [Split], `Id` and closing off are unchanged: an impossible arm receives a hypothesis such as `h : Eq(Nat, S(m), Z)` that computes to `False` once the index is split, so the absurdity is a value the arm uses, not a decision the checker makes. The set model needs indexed least fixed points, which is standard (Dybjer; Carneiro §5 reduces Lean's families to parameters plus `=` the same way). Probed: Forded `Vec` with a total `Head` and a three-line length lemma; `Le`, reachability, permutation by swaps and a small typing judgement with a non-syntax-directed rule, all built and inverted. Every attack was rejected for the intended reason (equation over the declared type; length lies directly, while lent, or through a non-uniform field; eliminating an arm at an unknown index; transport under a false equation); no closed proof of `False`. Value parameters are worth having on their own.
- Against: ergonomics, confirmed: constructors take their parameters explicitly with a `refl` per equation, lemmas rewrite along each arm's equation, data transport needs `J`, and an impossible arm is eliminated only after its index is split (at an unknown index `match h {}` is refused, failing safe). No induction on `Prop` derivations, confirmed (see below). The attacks were hand-written; the fuzzer has not been pointed at Forded declarations. A relation *parameter* still cannot be called in a field (K4), so reachability is written per relation, not once for all.

**C. Native indices in the kernel.**
- For: the idiom of Lean, Coq and Agda; matching computes without casts; impossible arms are eliminated by unification.
- Against: needs the same value parameters as B, and a bigger kernel besides: [Split] needs index unification, and conversion and the model need indexed families. Unification is a new decision surface for the two evaluation paths. It is stable under refinement if done right (a clash between constructor heads stays a clash; two stuck values are never treated as distinct), but it is new surface to get right. Its interaction with an observational `Eq` is less well trodden than Fording's.

**D. Indices in the surface syntax, translated to Fording.** B's kernel, with C's syntax: the checker's surface layer turns an indexed declaration and its matches into the Forded core, as Lean's elaborator turns `match` into eliminators. Ochr's surface already has sugar of this kind (`split`, `rewrite`, destructuring `let`).
- For: C's ergonomics with B's kernel and proof cost. The translation target now exists and is checked: every declaration and match in the probe's `Fording.lean` is what a surface indexed declaration would translate to.
- Against: needs a translation layer for declarations and matches; automatic arm elimination at the surface still needs the stability discipline of C.

## Arguments raised and withdrawn

Recorded so they are not raised again:
- "Indices violate the two-paths principle." Not inherently: eliminating an arm on a clash of constructor heads is stable under refinement, and keeping an undecidable arm is safe. It is a matter of implementing unification carefully (option C above).
- "Indices cost in-place mutation." No: a compile-time length cannot change by definition, whichever option provides it; runtime lengths use dependent fields, which all options keep.
- "Indices put the primitive `Eq` at risk." No: supporting indices never forces replacing the primitive observational `Eq` with an inductive one; they can coexist.

## Orthogonal, but decided alongside

- **Induction on proofs.** Any of B, C or D gives construction and case analysis of inductive predicates, but rule induction needs recursion on a `Prop` inductive, which Ochr forbids today (`LeZ … by d` is rejected). Lean allows it. This may matter more than the choice between B, C and D. Two routes, from the probe:
  - *Derivations as `Type₀` data* (works today under B): declare `LeD` beside `LeF` and recurse on `LeD` (`DToF`, `DTrans` check). Costs: two definitions per relation with the data one primary (a several-constructor proposition cannot eliminate into data, so there is no way back); `J` for data transport; derivations become proof-relevant.
  - *A syntactic guard for recursion on proofs* (sketched, not built): when the decreasing parameter is a proof, a recursive call must pass a field place of it in that position (pattern variables resolve to field places), and the parameter is never assigned. This is CIC's guard condition in its simplest form, read from syntax so both evaluation paths agree; in the model it is induction on the predicate's least fixed point. It touches [Def] and [Rec].
- **Well-founded recursion.** `Acc` needs a field of function type as well as an index; recursion on a measure would be the cheaper route. Independent of this decision.

## Evidence

- `fording-probe` (2026-10-28; branch `fording-probe`, unmerged; write-up `ochr/core/notes/fording-probe.md`, probe `Ochr/Examples/Fording.lean`, 49 declarations). Recommends B with value parameters, the restriction that no part of an equation field mentions the declared type, and equations only over first-order data. Its checker lines predate the total checker and the branch also touches `Machine.lean`, so adopting B means redoing them on current main rather than merging the branch.
- `fording` (2026-10-28; branch `fording`, unmerged; D71): option B implemented on the total checker with the probe's restrictions plus one the attack pass forced (no borrow-typed parameters); `Examples/Fording.lean`, 68 declarations, all earlier verdicts unchanged; the paper's [Ind-decl], A.1.1, §3.1, A.6 and Figure 16 updated. The attack pass also found a pre-existing [Repack] gap for stuck-block arms (D71).
- Still to do before landing B: point the fuzzer at Forded declarations, matches and repacks; update the paper ([Ind-decl], A.1.1's type positions, §3.1's remark on `Eq`, the model's indexed fixed points).

## Where the discussion stands

The user's view: supporting Fording is worthwhile because it is an emergent property of a reasonable system rather than a feature. The team-lead's current leaning: B now (the probe found no blocker), D later if the ergonomics demand it, C only if B and D prove unworkable; and decide the induction-on-proofs question at the same time, since without it B, C and D all stop short of rule induction. The syntactic guard is the cheaper of the two induction routes if it survives an attack pass.
