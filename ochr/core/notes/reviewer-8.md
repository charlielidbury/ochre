# Reviewer 8: generalist PC member (POPL/ICFP), cold read

Paper: "Proving the Program You Run: Mutable borrows inside a dependent type theory, by observation and closing off". Read from `ochr/core/paper/main.pdf` at c49e4f36 (48 pages: body pp. 1–25, references pp. 25–27, appendix pp. 28–48). I read the body in full. From the appendix I read A.1 and A.2 quickly, and read A.3, A.4.4–A.4.7 and A.7 notes 1–11 closely where the body sent me. I read nothing else in the repository.

## 1. The contribution in my words

Ochr is a small Lean-style dependent type theory (inductives, impredicative proof-irrelevant Prop) with Rust-style mutable borrows. Its definitional equality is a symbolic run of Aeneas's borrow/loan machine. When that run gets stuck on a call, the call is "closed off": its result, and the final contents of whatever it borrowed, become *sealed programs*, closed pieces of source code that play the role of Aeneas's backward functions. They are generated lazily and stay in the source language. An observational equality `Id` compares two computations by their results and their writes.

The payoff is that theorems about in-place code are stated about that code and proved by plain structural recursion, with no model, no refinement proof and no translation.

Soundness and consistency are conjectures. They are backed by four things: an executable checker, a counterfactual ledger that shows what each rule is needed for, a fuzzer, and a mechanisation of the untyped, first-order machine of an earlier rule set.

**Does the one-sentence contribution stay the same?**
- **After the abstract.** "A type theory in which in-place code appears in types; three mechanisms; a lot of evidence." That much is clear. But about a third of the abstract is caveats I could not yet interpret ("the agreement of the checker's two evaluation paths", "an earlier version of the rules").
- **After §1.** The bold sentence in §1.1 is the best statement of the contribution in the paper, and I could repeat it back: "this translation can be performed inside the type checker, lazily, as definitional equality, and in the source language itself". The last paragraph of §1.1 adds a second, *empirical* claim of a different kind: one system "gives shorter developments than the three pieces". The evaluation does not really support that claim (W4).
- **After §2.** Same as §1.1, and now I believe it. AddMZero, AddZero-by-lending and above all AddSub (§2.6) show the idea working.
- **After §6–§7.** The weight moves. Most of §6 and all of §7 are about keeping "the two paths" in agreement. I came away with a second contribution that the paper never announces: "these are the side conditions a type theory needs when its conversion is an effectful evaluator, and each one was paid for with a proof of False." That is real and useful. It should be named in §1, not discovered in Figure 8.

## 2. Strengths

**S1. The idea is new and easy to state.** It performs Aeneas's functional translation lazily, inside conversion, in source syntax, and only as far as an equation needs. That is a fresh point between "write it pure and hope the compiler updates in place" and "write it twice and prove refinement". I had not seen it before.

**S2. The opening example works, and the running example is well chosen.** Page 1 shows a four-line in-place addition and a two-line theorem about it, proved by bare recursion. A reader outside the niche sees the payoff before any machinery.

AddM carries §2.1–§2.5 well: the same function is reused for the pure wrapper, the generic call, the induction hypothesis and the returned borrow. AddSub in §2.6 is the most convincing example in the paper. There, a lemma about the *pure* `Add` is accepted where a proof about the *mutated* state is required, with no bridging lemma.

Two small caveats on the example:
- "In-place addition on unary numbers" sounds artificial to readers who think in machine integers. It is in-place append on a list of units; say so.
- Every statement it motivates is an equation between two recursions of the same shape, so the common case of a non-equational postcondition first appears on p22 (W6).

**S3. Unusual candour.** Most papers would bury these statements:
- Figure 1: what of Rust is covered.
- Figure 9: proved vs partly proved vs conjectured, with lemma names.
- §7.2: "each earlier version of it missed one".
- §7.3: "Nothing about types, conversion, stability or the model is mechanised".
- §8.2: property proofs 1.25 times as long as Aeneas's.
- §8.3: Verus a thirteenth of the tokens.

I trust the paper's other claims more because of them.

**S4. The counterfactual ledger (§8.1, Figure 10) is a method worth copying.** Every rule that is not the evident typing of a form has a switch. The build asserts exactly which verdicts flip when that rule is off. With the rule switched off, the fuzzer rediscovers 17 of the 20 soundness rows (§7.2). That is a better-than-usual demonstration that each rule is needed. Other language-design papers should copy it.

**S5. A clear, reusable design principle.** "No decision that changes a result is read from a normal form" (§6.3). Anyone who builds a dependent type theory whose conversion runs effectful code will run into exactly this. The paper's counterexamples map where.

**S6. The artefact matches the paper.**
- Every printed program is a regression test.
- The checker is small (about 5.3k lines) and fast (about 50 ms for the examples).
- It states fidelity, not speed, as its purpose ("a hand derivation can be charitable where the rules are silent, and a program cannot").

**S7. Related work is broad** and places Ochr precisely against Aeneas, prophecies, the fire triangle, OTT and Zombie.

## 3. Weaknesses, ranked by severity

### W1 (major). The new part is unproved, the proved part is the least new part, and the history of found proofs of False makes the conjectures hard to take on trust

**Where:**
- Abstract, last two sentences.
- §1.4, bullet 4.
- §6.4, first paragraph ("Two independent reviews of an earlier version of Ochr found closed proofs of False").
- §7 intro; Figure 9, rows 8–10.
- §7.2: "The argument is still an enumeration of the decisions we know of, and each earlier version of it missed one"; also "a reviewer found a closed proof of False through a refinement that leaked from one match arm into another".
- §7.3.

**The problem.** What is mechanised is the effectful machine of an earlier rule set ("version 1.3"). It is first-order and has no types, no closures, no inductive propositions and no stuck blocks. That is broadly the ground already covered by the soundness work on Aeneas's symbolic semantics [18].

Everything that makes Ochr a *type theory* is conjecture. That covers conversion, erasure, [Call-type], [Split], generalisation, stability (Conjecture 3), consistency (Conjecture 2) and adequacy (property 9). By the paper's own account, the stability argument has been wrong several times, once after the fuzzer existed. A POPL/ICFP paper that presents a new dependent type theory needs at least one theorem about the typed system.

**Fix, in order of preference:**
- **(a) Prove consistency and stability for a small typed fragment.** The fragment: Nat, Unit, True/False/And, Eq and Id, first-order top-level functions with borrow parameters (at least one of them returning a borrow), [Close], and [Split] with refinement. Leave out closures, stuck blocks, universes above Type₀ and large elimination. A paper proof in the appendix is enough; a mechanised one is better. State it as Theorem 1 in §7.
- **(b) If (a) is out of reach:** bring the existing mechanisation up to the current rules for its fragment, so that "version 1.3" disappears from the paper. Then prove Conjecture 3 for the fragment plus erasure, since erasure is where most of Figure 8's counterexamples live.
- **(c) Either way, reframe Conjecture 3 for generalists.** It is the substitution lemma (stability under instantiation) for a type theory whose conversion is an effectful evaluator. Saying so tells the reader what kind of proof to expect. It also shows why an enumerated list of "decisions" is the wrong shape for that proof: a proof goes by induction on the machine's rules, and the list of decisions should fall out of the rules rather than be kept by hand.
- **(d) Cheap and local: property 7.** Figure 9 row 7 says two endings commute (`end_comm`), and full order-independence is "partly mechanised". [End] removes exactly one borrow per step, so it terminates, and every maximal sequence of endings has the same length. If `end_comm` is the general diamond for two [End] steps, order-independence follows by a routine induction (or by Newman's lemma). Either say why that argument fails (§5.1 last sentence, A.7 note 13), or upgrade property 7 to "mechanised".

### W2 (major). §6.3–§6.7 and Figure 8 read as a catalogue of patches, and most of Figure 8 cannot be read from the body

**Where:** §6.3 bullets; §6.4; Figure 8 (p16); A.7 notes 1–11.

**The problem.** The principle in §6.3 is good. It is followed by about twenty side conditions, each with its counterexample squeezed into one table cell. Row 1 is typical: "A local function into U(n), where U(Z) computes to Prop, runs at the generic n but would be erased at n = Z, proving False". I could decode roughly a third of the rows without going to A.7.

From Figure 8 alone, a generalist cannot tell whether the side conditions follow from the principle or were added in response to attacks. §6.4 pushes the second reading: two of its rules ("A Π-type records its class", "Sorts are syntactic") were added after external reviews found False.

Confinement is described as "redundant for a correctly classified term, and is kept as a fail-safe" (§6.3 end; A.7 note 9). A belt-and-braces rule in a *calculus* signals that the authors do not fully trust Conjecture 3 either.

**Fix:**
- **Work three or four counterexamples in full in the body.** Give each 5–8 lines, with the program and its two evaluations side by side. One per category:
  - erasure decided from a value (A.7 notes 1/3);
  - a stuck block capturing by copy (Figure 8, row 3);
  - a codomain that computes to a borrow type (A.7 note 11, second half);
  - borrows of a universe (note 11, System U⁻).
- **Move the full Figure 8 to the appendix**, next to A.7, whose notes already explain each row.
- **Argue that the list of decisions is complete.** One paragraph: walk the machine rules of A.2, name every premise that branches, and show that each one is on the list.
- **Decide whether confinement is a rule or a defensive check.** If it is a rule, drop "fail-safe". If it is a check, move it to the implementation section.

### W3 (major for significance). Non-modularity and fragility under refactoring decide whether this scales, and the paper mentions them only in passing

**Where:**
- §1.5: "Its borrow checking is also not modular ... extracting a helper function can change which equations hold by refl".
- §6.2, end: "F(x) is not convertible with F's body inlined, nor are two functions with the same body and different names".
- §10.1 "Opaque definitions": "there is not yet a way to check a body once and then hide it from conversion, which is what modular verification needs".
- §8.2 "What is still costly": "a single lemma about lifting through the index would need quantification over programs".

**The problem.** For "would this change how people verify imperative code?", the key question is what happens at 10k lines. Conversion unfolds callees, and whether a caller passes the borrow check depends on whether a callee got stuck. So a change inside a callee can break both callers' borrow checks and callers' `refl` proofs.

The paper does say this, but in three places, one sentence each, with no example. The hash map study is presumably where this was felt, and I would like to know whether it was.

**Fix:** a short subsection (in §10.1 or §8.2) that does four things:
- **(i)** gives a concrete example of a change inside a callee that breaks a caller's borrow check, and one that breaks a caller's proof;
- **(ii)** says which proof style is robust (citing a callee lemma at the call site, as in `AddZero(x) := AddMZero(&x)`) and which is fragile (`refl` by unfolding);
- **(iii)** reports, for the hash map, how many proofs rely on unfolding a callee and how many cite a callee lemma;
- **(iv)** explains why "quantification over programs" is unavailable, given that Ochr has Π over function types with borrow parameters (§4.3). I could not work this out.

### W4 (major for the decision). The evaluation's headline number is the flattering one; the more modest result underneath is still interesting and should be the headline

**Where:** abstract ("a third shorter in lines than Aeneas's, although its proofs, without automation, are longer"); §1.1, last paragraph; §8.2 "What is written" and "Where the programs differ"; Figure 11; §8.3 "Quicksort".

**What I read from Figure 11 and §8.2:**
- **Lines vs tokens.** Line counts depend on formatting; tokens are the fairer measure. In tokens Ochr is 11% smaller (17.4k vs 19.7k), not a third.
- **Where the saving comes from.** Ochr drops Aeneas's model and agreement layers: (3.0k − 1.1k) + 2.7k ≈ 4.6k tokens, about 23% of Aeneas's total. Its longer property proofs pay back about 2.2k of that (14.7k vs 12.5k).
- **The Ochr hash map is a simpler program:**
  - unbounded Peano numbers, so no overflow and no failing operations (by §8.2's own figures, about 3% + 6% of Aeneas's proof lines);
  - a list of buckets instead of an array;
  - Nat values instead of a type parameter;
  - GetMut needs a proof that the key is present;
  - a fixed load factor.

  Correcting only for overflow and failure cuts the token gap from 11% to roughly 6%. The other simplifications would cut it further.
- **The case study shaped the language it measured.** The first complete version was 19% *larger*. Three language features (`rewrite`, destructuring `let`, `split f in t`) were added during the study and closed most of the gap. That is normal language design, but a second study that played no part in the design would be far more convincing.
- **Which Aeneas backend is the baseline?** The Figure 11 caption mentions F\*, and §8.2 says "every case analysis that Aeneas leaves to Z3". But §1.1 and §7.1 present Aeneas as producing Lean. Name the baseline's backend in the first paragraph of §8.2. It matters: F\* with Z3 is a strong automation baseline, which makes Ochr's result *better* than it currently reads.
- **Quicksort** is 8× the lines and 13× the tokens of Verus's, and recurses on fuel. §8.3 honestly says this measures automation, not the thesis. So quicksort supports only a capability claim ("Ochr can express and check this").

**Is it convincing to a non-specialist?** Partly. It convinces me the approach *works* on a non-trivial program with no model and no refinement proof. It does not convince me the development is *shorter* in any way that matters.

The honest headline would be: "Ochr drops the model and agreement layers entirely, and with no automation at all ends up about the same size as Aeneas with SMT automation." That is a good result. Say it that way.

**Fix:**
- Headline tokens rather than lines in the abstract and §8.2.
- Add the decomposition above as two lines under Figure 11.
- Soften the §1.1 thesis to "developments of comparable size, with no model and no agreement proof".
- Add a case study written after the language was frozen, or state plainly that there is none.

### W5 (moderate). The core typing rules are not in the body

**Where:** §6, Figure 7 (p13), which gives [Call-type], [Def], [Split] and [Rec] as prose and says "The rules for the basic forms are the evident ones". The actual inference rules are only in A.4.4–A.4.7 (pp. 40–43).

**The problem.** The typing judgement `Ω ⊢ t ⇓ v : A ⊣ Ω'` is the heart of the paper, and the body never shows a single rule of it. The prose for [Call-type] ("At the point where the arguments of f(ā) have been evaluated, with f : Π(x̄ : Ā). B: push a frame binding each xᵢ to aᵢ's value, evaluate B there on a private copy of the environment, and pop") made sense to me only after I read [Call-type] on p41.

**Fix:**
- Replace Figure 7's prose with the inference rules [Call-type]/[T-Call], [Split] and [Def] from A.4 (about half a page), with a one-line gloss under each.
- Early in §6, say explicitly that the algorithm *is* the definition: there is no separate declarative type system. Also say what that means for the metatheory: subject reduction and substitution become stability and naturality. Otherwise a generalist goes looking for the declarative system.

### W6 (moderate). §2 does not teach the two things a user most needs: how to write a postcondition, and what "two paths" means

**Where:** §6.2 ("λ(x : &Nat). (\*x := 5; refl) does not have type Π(x : &Nat). Id Nat (\*x) 5"); §8.3 QSCorrect; §1.3 and §6.3 (two paths); §2.8.

**The problem.**
- **Postconditions.** Every statement in §2 is an Id between two computations. The first non-equational postcondition ("after QS, c is sorted") appears on p22, along with the idiom for writing one: run the call on a copy inside the statement, `let c = *s; QS(n, n, &c); Sorted(n, c)`. Meanwhile §6.2 reveals that the Hoare-style statement a newcomer would write first is ill-typed.
- **Two paths.** They organise §6–§7 but get no example in §2. The smallest example in the paper is A.7 note 1, and it is involved.
- **§2.8 (branching)** is a single four-line paragraph that I could not follow.

**Does §2 prepare the reader for §3–§6?** For §4 and §5, yes: closing off, returned borrows and Id are all rehearsed. For §6, no: the two paths, erasure, stuck blocks and matching on proofs are not, and §2.8 is where stuck blocks should have been set up.

**Fix:** add to §2:
- **(i)** a five-line example of a non-equational postcondition written with the copy idiom, plus one sentence saying that types are formed once, on a copy;
- **(ii)** a subsection "When the two paths could disagree", with the simplest counterexample you have, showing the generic-call evaluation and the instance evaluation side by side;
- **(iii)** either an expanded §2.8 with an actual example and its normal form, or no §2.8 (§5 below).

### W7 (moderate). The gap between "the program you prove" and "the program you run" is wider than the title suggests

**Where:**
- The title.
- §4.1 "Reading": "A compiled program should move where the machine copies, which we have not justified".
- §10.2 "The checked machine is not yet the compiled program": "that the compiled program behaves as the checked one is, for now, an assumption".
- §7.1 Definition 1 and §10.1 "No 'static borrows": Ochr proves that every `Π(n : Nat). &Nat` has an injective backward function, which a safe Rust function returning `Box::leak(...)` violates.

**The problem.** The paper proves things (conjecturally) about a machine that copies data on every read and runs types and proofs on discarded private copies. The program one would compile moves data, erases types and proofs, and never copies. That is the same *kind* of gap §1.1 criticises in the pure route: the proof is about something other than the program that runs. §10.2 argues it is narrower, and I agree, but it is still a gap.

Separately, Ochr's logic refutes a type that safe Rust inhabits. So an opaque or foreign function that returns a borrow is an unchecked assumption.

**Fix:**
- Either prove a copy/move adequacy lemma for the mechanised first-order fragment, or list the gap among the abstract's caveats and soften the title (e.g. "Proving the Program You Wrote"). The lemma looks within reach: the fragment already has erased proofs, and the artefact already has a move semantics behind a switch (§10.2).
- Add the 'static consequence to §1.5 Scope as one sentence.

### W8 (moderate). The prose is dense, many terms are used before they are defined, and the abstract is too long

**Where:** see the reading log (§4 of this review). The main offenders:

| Term | First used | Defined |
|---|---|---|
| "generic call" | §1.3, §2.3 | §6 [Def] |
| frame separator `\|` | §2.4 | Figure 3 |
| `by x` | p1 | §3.1 |
| `split f in t` | Figure 2 | §8.2 |
| "the set model" | §6.4 | §7.1 |
| "version 1.3" | §1.4 | never (internal numbering) |
| "stuck block" | §4.2, §4.3 | §4.5 |
| "resolution" | Figure 9 | §7.1 |
| `x'` | §2.4 | never |

The abstract runs to about 330 words and includes internal details a first-time reader cannot interpret.

**Fix:**
- Add a notation box in §2 covering ⌈t⌉, σ, `borrow_ℓ v`, `loan_ℓ`, ⊥, ⋆, Ω with its frames, and "generic call".
- Cut the abstract to about 180 words: the idea; the three mechanisms, one sentence each; the evaluation, one sentence; the status, one sentence (e.g. "consistency is conjectured; the operational core is mechanised for a first-order fragment").
- Split sentences over about 40 words in §1.2, §2.4, §2.5 and §4.5.

### W9 (minor). Related work a generalist will look for

- **Liquid Haskell's reflection and proof by logical evaluation (PLE).** The program is its own specification, and proofs go by unfolding the program. It is the closest pure-language relative of AddMZero.
- **Dafny and Why3.** Imperative methods, pure functions usable in specifications, ghost code, two-state lemmas, and Why3's regions. "Specifications may call imperative code" is Ochr's point, so these are its natural foils.
- **Symbolic execution as a verification technique.** VeriFast, already cited, is itself a symbolic executor, and Ochr's typing is symbolic execution with case splits and generalisation. One paragraph would help readers from that community place the work.
- **Lean 4's `do` notation with local mutation** (Ullrich and de Moura, "do unchained", ICFP 2022): imperative surface syntax elaborated to a pure core. It is a direct contrast to Ochr's approach.

### W10 (minor). Smaller points

- **§8.2 "Coverage"** says "Aeneas's statement about remove asserts the invariant of the map it was given rather than of the map it returns". That is a claim about a competitor's development: cite the exact lemma and file, or drop it.
- **§8.2, garbled sentence:** "The invariant is stated the same way: that every key lies only in the bucket the index returns for it is `Π(k : Nat). OnlyIn(...)`". Rephrase.
- **§5.2 / Figure 6** define Eq only on constructor values. Say what Eq does at function types and at universes (stuck? function extensionality?). The comparison of functions by their generic observation (§4.3; A.3 [Conv-fun]) is conversion, not Eq.
- **§4.5 and A.1.4 item 7:** generalisation records are global and survive private copies. That is unusual state inside a typing judgement and will complicate any substitution lemma. Flag it in §7.2 as a known proof obligation.
- **Code blocks wrap badly** in §2.6 (LeAdd), §2.7 (SizeInsert) and A.7 notes 1–2.
- **"Version 1.3"** in §1.4 and §7.3 is internal numbering. Say "an earlier rule set that predates the erasure and inductive-proposition rules".
- **§2.2:** "runs again, now makes progress" is ungrammatical.
- **Figure 10's "Among the rules" column** uses internal vocabulary. Gloss it or drop it.
- **§7.1:** "Whether normalisation, and so type checking, terminates is open". Fine, but add that Lean is in the same position (Abel–Coquand applies to Lean too), so readers do not take it as specific to Ochr.

## 4. Reading log (where I got stuck, in order)

1. **Abstract.** "The agreement of the checker's two evaluation paths" means nothing until §6.3. In "closed source programs that own their state", "own their state" is unclear.
2. **p1.** `by x` in `AddM(...) : Unit by x :=`. I guessed "structural recursion on x"; it is defined in §3.1 (p7).
3. **§1.2 "Closing off".** First ⌈…⌉. "A returned borrow leaves a hole in them awaiting its final value" cannot be parsed before §2.5.
4. **§1.2 "Induction hypotheses at the call site".** "Observed through the caller's owner, successor included, so the induction hypothesis is literally the goal": re-read twice, clear only after §2.4.
5. **§1.3.** "A statement is evaluated along two paths ... and any decision on which the two paths disagree is a proof of false": "generic call" is undefined, and the claim is alarming and unexplained until §6.3.
6. **§1.4.** "Version 1.3" is internal versioning.
7. **§1.5.** "A callee that gets stuck leaves every borrowed argument borrowed until its returned borrow ends, while one that runs to completion releases them" needs an example; clear only after §4.4.
8. **§2.3.** "The checker works at the definition's generic call AddMZero(&c) from { c ↦ σ }" defines the generic call in passing. In ⟦AddM(x, 0)⟧ = ([…], N(σ)), is […] an elided ⌈…⌉? It is a different bracket.
9. **§2.4.** In `{ c ↦ loan₀ | x ↦ borrow₀ (S loan₁) }`, the `|` (frame separator) is defined only in Figure 3.
10. **§2.4.** ⟦AddM(x', 0)⟧: `x'` is never introduced. I assumed it is the callee's parameter, bound to `borrow₁ σ'`.
11. **§2.4.** "The owner of the argument's loan is found by following it outwards: loan₁ sits inside x's borrow, whose loan sits in c": re-read three times. A small picture of the nested borrows would fix it.
12. **§2.5.** "Re-running AddM''s sealed program on S σ' unfolds TailM once, closes off its inner call with a fresh hole, and the pending write \*r := y fills that hole": I could not check this in my head. Show the two normal forms.
13. **§2.7.** "Generalises the sealed program to a fresh abstract value, everywhere it occurs and wherever it is derived again": "derived again" means nothing until §4.5 / A.1.4 item 7.
14. **§2.8.** The whole paragraph. I could not reconstruct the closed-off match's normal form.
15. **Figure 2.** `split f in t` is in the grammar but explained only in §8.2 (p21).
16. **§3.2.** "A loan is a variable bound by its borrow": "bound" in the binder sense took a re-read.
17. **§4.2.** Why are erased terms evaluated at all? (To compute types.) It took a moment; one clause would help.
18. **§4.3.** "Two function values are convertible when ... their generic calls have the same observation": so conversion runs functions? Is that decidable? I went to A.3 [Conv-fun]; its remark about the coinductive reading helped and could be in the body.
19. **§4.5.** "Its head call C may not itself be closed off (calls made inside C's body may)": re-read; the analogy with the fixpoint guard in the calculus of inductive constructions helped.
20. **§4.5.** "Every later derivation of the same closed program normalises to that value": global state inside normalisation. Why is this sound? Not addressed.
21. **§5.1.** "A later refinement can shrink an owner set, removing a component both sides agree on": unclear.
22. **§5.1, last sentence.** "That the order in which they are ended does not matter is a conjecture, proved for two endings": why doesn't the two-step result give the whole thing (W1(d))?
23. **Figure 6.** What is Eq at Π-types and at universes?
24. **Figure 7.** Prose rules. I had to read A.4 (pp. 40–43) to understand [Call-type] and [Split].
25. **§6.2.** `λ(x : &Nat). (*x := 5; refl)` does not have the Hoare-style type, so how does one write a postcondition? Answered only by QSCorrect in §8.3.
26. **§6.3, bullet 2** ("What a stuck block captures, and how"): needs A.2.8.
27. **§6.4.** "The set model" is used before §7.1. "T(Z), with T(n) : P(n) and P(n) computing to Prop, was a proposition by computation but not by declaration" needed A.7 note 3.
28. **Figure 8.** Most rows need A.7 to decode, especially row 1, rows 5–6, and "Exclusive access; matches end loans in neutral heads".
29. **Figure 9, row 6.** "And so is the caller's context around it when every owner of the hole is observed; with fewer owners it can be constant": unclear until the Pick example in §7.2.
30. **§7.1, Definition 1 and "R is forced".** I needed §10.1 to see the 'static consequence.
31. **Figure 10.** The "Among the rules" column uses internal vocabulary.
32. **§8.2.** "The invariant is stated the same way: that every key lies only in the bucket the index returns for it is Π(k : Nat)...": garbled.
33. **§8.2.** "Would need quantification over programs": why is that not available?
34. **§8.2.** Which Aeneas backend is the baseline: Lean, as §1.1 suggests, or F\*, as the Figure 11 caption suggests?
35. **§8.3.** Why is `WithSplit` a continuation? (Because a pair of borrows cannot be returned; Figure 1.) Say so there.

## 5. What to cut or compress

The body is already about 24.5 pages (pp. 1–25, up to the end of §11), so it meets the 25-page target today. But the additions I ask for cost about 2 pages, so about 3.5 pages must go.

**Cut or compress:**

| Change | Saves |
|---|---|
| Abstract from about 330 to about 180 words | 0.2 p |
| §1.2 "Three ideas": the closing-off and IH-at-the-call-site paragraphs retell §2.2 and §2.4 more densely; keep one sentence each, with forward references | 0.4 p |
| §1.4 bullet 4 duplicates Figure 9; replace with one sentence | 0.15 p |
| §2.8 Branching: cut, or fold into §2.5 as one sentence ("a stuck match closes off like a call") | 0.15 p |
| Figure 8 to the appendix, keeping three or four worked counterexamples in the text (net) | 0.6 p |
| §6.4–§6.6: subsingleton elimination is Lean's; two sentences and a pointer to A.7 note 10 are enough | 0.5 p |
| §7.1: keep "what consistency is relative to" and the conjecture; move the Π interpretation and Definition 1 to A.6 beside the translation | 0.5 p |
| §7.2 "Testing it": keep the switch-off counts; move the three-finding history to the appendix | 0.3 p |
| §8.1: merge "Structure" and "What running the rules found" into the ledger paragraph; drop Figure 10's third column | 0.3 p |
| §8.3 "Arrays are a library" and "The untouched rest": one paragraph | 0.3 p |
| §10.2 and §11 overlap §1; make §11 a four-sentence close | 0.2 p |
| **Total** | **about 3.6 p** |

**Add (about 2 pages):**

| Addition | Costs |
|---|---|
| Figure 7 as inference rules | 0.5 p |
| A postcondition example in §2 | 0.25 p |
| A two-paths example in §2 | 0.4 p |
| A fragment theorem plus proof sketch in §7 | 0.4 p |
| A modularity paragraph | 0.3 p |
| A notation box | 0.15 p |

The net body comes to about 23 pages.

**Missing and needed by a reader:**
- a notation box;
- a statement that the algorithmic typing *is* the definition;
- the postcondition idiom;
- one worked disagreement between the two paths;
- which Aeneas backend the baseline uses.

## 6. Score and confidence

**Score: weak reject.**

**Confidence: medium.** I am a PL generalist. I followed the operational machine and the examples, but I did not check the side conditions of §6 against the appendix rules in detail, and I cannot judge how close Conjecture 3 is to provable.

**Rationale.**
- **For:** the idea is new and, on the evidence of §2, pleasant to use. The paper is honest to a degree I rarely see, and the ledger method is valuable.
- **Against, metatheory:** for a paper that presents a new dependent type theory, the typed system has no theorem at all, and the mechanised part covers an earlier, untyped, first-order rule set. The paper's own history of found proofs of False (two external reviews, plus one review after the fuzzer existed) means I cannot take consistency on trust.
- **Against, evaluation:** it shows the approach works. It does not show that developments are shorter in any robust sense, and the headline number is the flattering one.

**What would move my score up one notch (to weak accept):** a proved theorem, consistency plus stability (Conjecture 3), for a small typed fragment that includes [Close], [Split], Id and at least one function returning a borrow. A paper proof in the appendix is enough. Alongside it I would want:
- **(i)** the rules of Figure 7 in the body;
- **(ii)** the evaluation reframed around tokens and the decomposition "model and agreement layers removed, proofs longer without automation".

Neither (i) nor (ii) alone would move me; the theorem would. To reach accept I would also want the mechanisation brought up to the current rules for its fragment, and a second case study written after the language was frozen.
