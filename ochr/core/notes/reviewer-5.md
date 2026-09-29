# Review 5: "Proving the Program You Run" (Ochr)

Reviewer background: verification of Rust and imperative programs (Aeneas, RustHorn/RustHornBelt, Creusot, Prusti, Verus, Flux, VeriFast, separation logic, Low*/F*, borrow checking: LLBC, Polonius, Stacked/Tree Borrows).

What I read: the whole paper (sections 1–11 and appendix A) as of `0127f58b`, and the artifact as a reviewer with artifact access would use it: the README, the example tour (`00Std` … `15BorrowTypes`), the ledger, `lake exe tests`, and the statements (not the proofs) of the main theorems in `meta-lean`. I did not read DECISIONS, notes, ROADMAP or git history. During the review, the checker on the branch moved to `96d788a1` (a commit titled "D52": pairs become a library type, `Eq` becomes injective on constructors). I re-ran my main attack there, and it still goes through.

## 1. Summary

The paper proposes Ochr, a dependent type theory with Rust-style mutable borrows. Definitional equality is a deterministic symbolic machine taken from Aeneas's LLBC. Imperative code therefore unfolds during type checking, and an in-place function can be proved equal to another computation by plain structural recursion.

There are three mechanisms:
- **Closing off.** A call that gets stuck on a symbolic value is replaced by "sealed programs" that recompute its result and the final contents of the places it borrowed.
- **Observational `Id`.** Two computations are compared by their results and their writes, and `Id` reduces to `Eq` between those tuples.
- **Induction hypotheses at the call site.** They are typed in the caller's environment, so the borrow structure supplies the congruence steps.

The evidence is:
- worked examples on Peano numbers, lists and binary search trees;
- a Lean reference checker with 432 verdicts and a "counterfactual ledger" (which tests flip when each rule is switched off);
- a mechanised frame property and [Close] equations for a first-order fragment of an older rule version.

Consistency, stability (the two evaluation paths agree), adequacy and termination are conjectures. I found a closed proof of `False` that the artifact accepts. It is a counterexample to the stability conjecture as stated.

## 2. Strengths

- **The central idea is new and attractive.** Aeneas's state-passing reading of `&mut` is performed lazily, inside conversion, in the source language. For in-place/pure pairs that recurse the same way, the proofs really are one-line recursions, and seeing the environment supply `cong S` (§2.4) is instructive. `AddMEq` (§2.5) and `InsertMEq` (§2.7) check in the artifact exactly as printed.
- **Neutral forms for borrow-returning calls.** A hole `loan_k` inside the fills of every borrowed argument (§4.4, Fig. 4) is a clean way to give a stuck borrow-returning call a normal form. So is the observation that loans-as-variables make the hole fillable by the ordinary [End] rule. Because owners are sets (§5.1) and all of them are observed, a borrow chosen by a branch is handled soundly. The `Pick`/`AddToOne` examples are convincing.
- **"The borrow checker is the machine" (§4.1).** [Access] ends borrows lazily, which gives a flow-sensitive, NLL-like discipline without a separate lifetime analysis. The matching rule, where pattern variables are sub-places, is close to Rust's `ref mut` binding mode.
- **The artifact is unusually honest and executable.** Every paper program is a test. The count guards against silently empty test files. The ledger records which rule each regression depends on, and Fig. 7 and appendix notes 1–27 document the design space openly. I reproduced `432/432 as expected, 18.2 ms` at `0127f58b` with `.lake/build/bin/tests`.
- **The paper is candid about its limits.** It says what is conjectured (§7, Fig. 8), mentions the injectivity assumption for opaque borrow-returning functions (§10.2), and admits that the checked machine is not the compiled program (§10.3).
- **The writing is clear sentence by sentence**, and the running example is well chosen.

## 3. Weaknesses, ranked by severity

### W1 (critical). The artifact accepts a closed proof of `False`. It refutes the stability conjecture (§7.2, Conjecture "stability", item 1).

At `96d788a1`, and also at `0127f58b` with `Std`'s `U(Z)` in place of `P0`, the following block checks, including `Boom : False`:

```
ochr R5min {
  def P0 : Type := Prop                             -- a type abbreviation for the sort Prop
  def H (x : &Nat) : P0 := (*x := S Z; ⊤)           -- codomain term `P0` is not syntactically a sort: H "returns data" and runs
  def RunG (f : Π(x : &Nat). Prop) : Nat := (let c = Z; let g = f; g(&c); c)
  def RunGGen (f : Π(x : &Nat). Prop) : Id Nat (RunG(f)) Z := refl   -- at the generic call, g(&c) "returns types": erased, c stays Z
  def Boom : False := RunGGen(H)                    -- at f = H, g(&c) runs, c = 1; the statement is Eq Nat 1 0 ≡ False
  def RunGH : Id Nat (RunG(H)) 1 := refl            -- the checker itself computes RunG(H) = 1
}
```

**Diagnosis.** Appendix A.4.1 classifies a call by "the codomain term of [the function value's] Π-type": clause 3 and the definition of "returns types/proofs". There are two paths:
- At the generic call, `g` holds the abstract `σ_f`, whose Π-type `Π(x:&Nat). Prop` has a syntactic sort as its codomain, so the call is erased.
- At the instance, `g` holds `H`, whose codomain term is `P0`, so the call runs.

[Conv-pi] (A.3) compares Π-types by evaluating their codomains. So `H` is a legitimate argument at type `Π(x:&Nat). Prop`, and the instantiation α in Conjecture "stability" (§7.2 lists "definable closures for abstract functions") changes the codomain term that item (1) relies on. The argument in §7.2 ("each decision is read from syntax … α changes only normal forms") is therefore false for function-typed variables.

Calling `f` directly as a parameter (`f(&c)`) is safe in the checker, which reads the class from the parameter's declared type. But the class is lost as soon as the function goes through:
- a `let` (`let g = f`);
- a call (`IdF(f)(&c)` with `IdF(f : Π(x:&Nat). Prop) : (Π(x:&Nat). Prop) := f`). This variant is also accepted.

The same problem exists for the proof class. `f : Π(x:&Nat). ⊤`, instantiated with `λ(x:&Nat) : V(Z) => (*x := S Z; W(()))` where `W(u : Unit) : V(Z) := refl`, also yields an accepted `False`: a "proof" whose run mutates.

The row of [Close] (stability item 4) has the same defect, harmlessly because the type is `Unit`. `RunU(f : Π(x:&Nat). Unit, n) : Id Unit (let c = n; f(&c)) () := refl` checks, and its instance `RunU(H2, n)` has type `⊤`. The same statement written directly with `H2 : Π(x:&Nat). UU(Z)` computes to `Eq Unit ⌈let c = σ; H2(&c)⌉ ()`, so the two paths give different types for the same statement.

**Why this is the top weakness.** Fig. 7 and §7.2 say that each side condition was added after a counterexample, and that "the last round of review found one we had missed". This is one more. The enumeration strategy for stability is not converging, and the paper offers no invariant that would make it converge.

**Concrete fix.** Make the erasure class, and the [Close] row, part of the *type*, not of the term that happens to flow into a variable:
- Annotate Π-types with a relevance or quantity: runtime, types or proofs, as QTT or Agda's irrelevance annotations do.
- Make [Conv-pi] and argument checking require equal classes.
- Classify a call by the static type of its head, not by the value it evaluates to.

Then prove item (1) of stability as a lemma, at least for the first-order-plus-function-parameters fragment, instead of arguing it by enumeration.

### W2 (major). The metatheory is conjectural, and the mechanised part is not where the risk is (§7, Fig. 8, §7.3).

Unproved:
- consistency (Conjecture "consistency");
- stability (now refuted as stated);
- naturality and adequacy;
- independence of the order in which borrows end (proved for two endings);
- termination (`sorry` in `GuardTerm.lean`, `termination`).

The mechanisation covers "version 1.3 of the rules", a first-order fragment with no types, `Id`, conversion, erasure, closures or stuck blocks. Every soundness counterexample in Fig. 7, and mine, lives in the parts it does not cover.

Some "mechanised" claims are weaker than the labels suggest:
- Property 6 ("a backward function is injective … mechanised (machine form)"): `back_inj` and `ctx_inj` (`Inj.lean`) prove that *syntactic substitution* of a loan into an unnormalised value is injective. They do not prove that the backward function computed by [Seal], which re-normalises after substitution, is injective. The model needs the latter.
- The `close_*` theorems hold under loan-freedom hypotheses that are "not yet derived" from well-formedness.

For POPL, a new dependent type theory whose main risk is inconsistency needs either a proof or a much smaller claim.

**Fix.** Either:
- prove stability and adequacy for a fragment that includes `Id`, types and function parameters, and re-label Fig. 8 accurately (e.g. "6: substitution of a hole is injective (syntactic)"); or
- restrict the calculus to what you can prove, for example no function-typed parameters and no type-returning functions in runtime positions, and present the rest as future work.

### W3 (major). The pitch ("verified code is no longer written twice") is not supported by an evaluation (§1.1, §2, §8).

All the evidence consists of pairs of programs that recurse the same way: `AddM`/`AddM'`, `AppendM`/`AppendM'`, `InsertM`/`Insert`. In the BST example the specification *is* a hand-written pure `Insert` (§2.7, `InsertMEq`), which is exactly the second copy the introduction says is gone. What Ochr removes is reading a translation, not writing a specification.

A reader from my area will ask what Aeneas+Lean needs for the same program. Aeneas translates `InsertM` into a forward/backward pair whose backward function recurses exactly like `Insert`, and the equality is an induction closed by `simp`. The paper neither shows nor measures this.

The one non-twin theorem, `SizeInsert` (`10Inductives.lean`), is revealing. It needs two nested `J`s with hand-written motives and an auxiliary arithmetic lemma. There is no tactic language, no rewriting and no automation, so functional correctness beyond twin recursions will be expensive, and the paper gives no evidence either way.

Composition also needs helpers. To reuse `AddMEq` inside `AddM(&*x, y); AddM(x, z)`, I had to define a pure wrapper `AddP` (the function version of `AddM'`), snapshot `*x` (a motive may not capture a borrow), and transport with `J`. It checks, but "no pure model" does not survive the first attempt at modular reasoning.

**Fix.** Add an evaluation section:
- Take 5–10 programs from the Aeneas, Creusot, Verus or Prusti suites, for instance: the Aeneas hashmap, a linked-list cursor or `get_mut`, list rotation or reversal, AVL or red-black insertion, and an in-place partition checked against a pure spec that recurses differently.
- Report, for Ochr and for Aeneas+Lean at least: lines of code, lines of spec, lines of proof and check time.
- Show at least one case where specification and implementation do not recurse in the same way, and show the goals the user actually sees.

### W4 (major). The machine models a narrow, non-modular fragment of `&mut` (§3, §10.2).

Missing features, several of them load-bearing for real Rust:
- shared borrows (claimed simple in §10.1, but they interact with `&mut` through reborrowing, two-phase borrows and borrows in data);
- loops;
- borrows in data, so no `iter_mut`, `split_at_mut`, `Option<&mut T>`, `entry` or returning a pair of borrows (my `Split(x : &(Nat × Nat)) : &Nat × &Nat` is rejected);
- lifetime parameters;
- generic `&A` (no generic `swap`, and no `Vec<T>` method over a type parameter; §10.2 admits this);
- machine integers and arrays;
- two-phase borrows (`PushM(&*xs, Len(*xs))` is rejected; a temporary is needed);
- move semantics (see W5).

Two consequences go beyond "missing feature":

- **One region per call.** A stuck borrow-returning call puts its hole in the fill of *every* borrow argument (Fig. 4). This is Aeneas with all lifetimes unified, and it contradicts Rust's elision rule, which is an *error* for `fn(&mut A, &mut B) -> &mut C` without annotations.

  With `TailM2(x : &Nat, y : &Nat) : &Nat by x` (recursing on `x`), the program `let r = TailM2(&a, &b); let z = b; *r := 5; a` is rejected. Rust accepts it with `'a` on `x` only.

- **Borrow checking is not modular in signatures.** The same caller with `FirstM2(x : &Nat, y : &Nat) : &Nat := x`, which has the same type, is accepted. So whether a caller borrow-checks depends on the callee's *body* (whether it gets stuck), and on whether an input happens to be concrete: the variant with `let a = 2` is accepted. §7.2 shows the `Pick` case, but it does not say that this makes borrow checking non-compositional, a property Rust users rely on.

In addition, `Π(x : &Nat). &Nat` is not Rust's `fn(&mut u64) -> &mut u64`: every inhabitant must have an injective backward function (§7.1, §10.2). Prophecy-based models (RustHorn, Creusot) have no such restriction.

**Fix.**
- Put a one-table summary of the Rust fragment (feature, supported yes/no, what breaks) in §1.
- Add explicit region annotations to borrow-returning Π-types, so that a hole goes only into the fills of arguments of the returned region. This is Aeneas's per-region backward functions. It would fix both the imprecision and the non-modularity.
- State the modularity property you do have: borrow checking against an opaque function parameter uses only its type.

### W5 (major). "The program you run" overclaims (title, abstract, §4.1, §10.3).

The checked machine copies all borrow-free data on every read, and the compiled program is not defined. For Rust-like code this is not a benign detail:
- `let n = *x` on a `Tree` behind `&mut` is a deep clone in Ochr and illegal in Rust;
- passing `x` by value to `Add` is a copy in Ochr and a move in Rust.

The affine discipline that would license "last use is a move", and the simulation between compiled and checked programs, are both future work. Until then, the theorems are about a copy-semantics interpreter, not about the in-place program whose efficiency motivates the paper.

**Fix.** Either:
- define the affine discipline for the first-order fragment and prove that implementing a last-use copy as a move is unobservable; or
- change the title and abstract to "proving the program you check" and add the caveat to §1.

### W6 (moderate). The correspondences with Aeneas and with prophecies are stated more strongly than shown (abstract, §1.2, §4.4, §9).

**"Sealed programs are exactly Aeneas's backward functions"** is repeated five times. They coincide on:
- single-region calls,
- borrows at the top level,
- loop-free, first-order code.

Aeneas's backward functions differ in four ways:
- they exist per region and per function;
- they are derived from the signature, so they are modular and a callee is never unfolded;
- they cover loops (as fixed points);
- they cover nested borrows (region abstractions with projectors).

The mechanised statement (`close_back`) is for the v1.3 first-order fragment, with hypotheses.

**Prophecies (§9).** Three things are imprecise:
- A RustHorn prophecy `^x` is a value available *before* it is resolved, and specifications can mention it. This is what makes RustHorn and Creusot specs modular and lets them handle borrows in data and loops.
- Ochr's hole is inert, specifications cannot name it, and it is created only for borrows *returned* by stuck calls.
- Borrow *parameters* in Ochr are modelled by an owned generic place plus ending the borrow, which is Aeneas's reading, not RustHorn's. Unlike RustHorn, Ochr needs injectivity.

**Fix.** State the correspondence as a theorem with its fragment. Add an Aeneas ↔ Ochr table (forward function ↔ `⌈L; C⌉`, backward function ↔ fill of `c_i`, region abstraction ↔ hole, loop fixed point ↔ none). Rewrite the prophecy paragraph around the modularity point and the injectivity point.

### W7 (moderate). Readers from my area lose the thread at a few points.

- **The Rust fragment comes too late.** The key restrictions are scattered over §3 ("There are no shared borrows, no loops…"), §10 and appendix notes 11–27. A Rust reader needs them on page 2.
- **The hardest rules are thin in the body.** Stuck blocks and captures (end of §4.5), [Split] joins (§6.3) and erasure (§6.4) are where every soundness bug lives, yet the body gives them a paragraph each. Meanwhile §2 spends a page on `SubM`/`AddSub`.
- **"Id is not a new primitive"** (abstract, §1.2, §5) is hard to square with Id's own typing rule, footprint, owner sets and [Obs-borrow]. Say "Id is a derived *proposition* whose computation rule is observation".
- **The vocabulary is heavy.** Roughly twenty bespoke terms (generic call, sealed program, hole, inert loan, owner, footprint, observation, refinement, generalisation, stuck block, declared proof, confined, head call, entry value, …). A glossary would help.
- **Fig. 7 reads as a bug log.** Combined with §7.2's "the argument is an enumeration of the decisions we know of", it erodes confidence rather than building it. Present the *invariant* first, then the table as evidence for it.

### W8 (minor).

- **Pairs.** At `0127f58b` an abstract pair cannot be projected (`SwapPair` is a `reject def`), and `&(*x).1` for `x : &(Nat × Nat)` fails with "no such place". Only single-constructor inductives, accessed through `match`, give struct-like field borrows. `96d788a1` changes pairs, so please say which behaviour the paper describes.
- **Opaque definitions.** "Opaque definitions" (§10.1) are function-typed parameters or bodiless declarations, i.e. axioms. There is no opaque-but-checked definition, which is what modular Rust verification needs.
- **Decidability.** Type checking is not known to be decidable (§7.1: large elimination plus impredicative proof-irrelevant `Prop`). Mention this in the contributions, not only in §7.
- **Fig. 8, item 3** says "partly mechanised" for termination; the general statement is a `sorry`. Say so in the table.

### W9 (minor). Related-work gaps from my area (§9).

- **RustBelt** (Jung et al., POPL'18), **Stacked Borrows** (POPL'20) and **Tree Borrows** (PLDI'25): the reference points for "is [Access] a faithful model of `&mut` exclusivity".
- **Oxide** (Weiss et al.), **Polonius**, and Pearce's lifetime formalism (TOPLAS'21) for the borrow-checking side.
- **RefinedRust** (PLDI'24) and **Gillian-Rust** (PLDI'24): recent Rust verifiers with a foundational story.
- **Electrolysis** (Ullrich 2016): the first Rust-to-Lean functional translation, and the direct ancestor of the "second language" in §1.1.
- **Low\*/KaRaMeL** (ICFP'17) and **Cogent** (ICFP'16, "Refinement through restraint"). Both are "one language" answers to the two-language problem: Low* writes effectful code in F* and extracts it; Cogent's linear types give an automatically generated pure semantics for in-place code with a certifying compiler. §1.1's dichotomy ignores both, and Cogent is the closest prior art to "the second copy is generated".
- **F\*'s `reify` with its normaliser** already computes stateful code inside the type checker (§9 mentions `reify` but not that it computes in conversion). Say precisely what Ochr adds: borrow-aware locality and symbolic neutral forms.
- **SPARK's ownership and borrowing** (Dross et al., CAV'20 / NFM): an industrial "prove the program you run" with an ownership discipline.
- **Mutable value semantics** (Racordon et al., Hylo/Val, JOT'22) and **Lean 4's local mutation in `do`** ("do unchained", ICFP'22). Both treat an `inout` parameter as a pure function returning the new value, the same insight as §1.1.
- **Krishnaswami, Pradic and Benton, "Integrating linear and dependent types"** (POPL'15): an earlier combination of imperative linear state with dependent types.
- **WhyML's regions and ghost code** (Filliâtre, Gondelman, Paskevich), which Creusot builds on.

## 4. Attempted attacks and their outcomes

Each attack went through `lake env lean` on a scratch file under `Ochr/Examples/`, which I then deleted. Everything was run at `0127f58b` and the main attack was re-run at `96d788a1`.

| # | Attack | Outcome |
|---|---|---|
| 1 | **Erasure class through a let-bound function parameter** (W1): `RunGGen(H) : False` | **Accepted: closed proof of `False`**, at `0127f58b` (with `U(Z)`) and `96d788a1` (with `P0`). Not blocked by the `confineBodies` extension either. |
| 2 | Same, through an identity call `IdF(f)(&c)` | **Accepted: closed proof of `False`.** |
| 3 | Same for the proof class (`f : Π(x:&Nat). ⊤`, instance with codomain `V(Z)` whose body writes) | **Accepted: closed proof of `False`**; a "proof" whose run mutates. |
| 4 | Same, calling the parameter directly (`f(&c)`, no let) | Rejected: the checker uses the parameter's declared type. The rules as written in A.4.1 do not say this. |
| 5 | [Close] row flip: `f : Π(x:&Nat). Unit` vs `H2 : Π(x:&Nat). UU(Z)` | The two paths disagree (`RunU(H2, n) : ⊤`, but the same statement computes to `Eq Unit ⌈…⌉ ()`). No `False`, because `Unit` has one element. Counterexample to stability item (4). |
| 6 | Two live borrows from `TailM(&*x)` twice, writing through the first | Rejected (the second reborrow ends the first). Correct. |
| 7 | Stuck block choosing between a borrow parameter and `&local`, returned | Rejected ([Drop]: local still borrowed). Correct. |
| 8 | Read `*x` while a returned borrow into it is live, then write through the borrow | Rejected. Correct (Rust also rejects). |
| 9 | Two-phase borrow `PushM(&*xs, Len(*xs))` | Rejected: incomplete relative to Rust. |
| 10 | `split_at_mut`-like function returning `&Nat × &Nat` | Rejected by design (D48). |
| 11 | Lifetime precision: `let r = TailM2(&a, &b); let z = b; *r := 5` | Rejected at abstract `a`, accepted at `a = 2`, and accepted when the same-typed callee is `FirstM2 := x`. Incomplete and non-modular (W4). |
| 12 | Disjoint borrows of two fields (pair fields; `h` and `t` under `Cons`) held at the same time | Accepted. Good. |
| 13 | Reusing `AddMEq` inside a two-call context via `J` | Accepted once a pure wrapper and a snapshot are added. With `*x` in the motive it is rejected (a closure cannot capture a borrow). |
| 14 | Empty match on `Nat` as ex falso (`match n {}` at type `False`) | Rejected. Correct. |
| 15 | Artifact claims: `lake exe tests` | `432/432 as expected; total check time 18.2 ms` at `0127f58b`. Ledger printed with 46 rows as described. |

I found no use-after-free or UB-style acceptance in the borrow machinery itself (rows 6–8, plus the suite's own regressions). The borrow side appears robust. The soundness hole is where borrows meet the erasure and classification machinery of the dependent types.

## 5. Questions for the authors

1. Is the erasure class meant to be a property of the *term* bound in a variable or of its *type*? If of the term, how can any stability argument survive [Conv-pi], which identifies `Π(x:&Nat). Prop` with `Π(x:&Nat). P0`? If of the type, where is it in the Π-type and in conversion?
2. Can the stability conjecture be stated as a lemma about a *typing* judgement (for example, that the class is preserved by substitution of well-typed values), rather than as an enumeration of decisions?
3. How would you add lifetime/region annotations so that `TailM2`-style calls release non-returned arguments? Does this give signature-modular borrow checking, and does it change [Close]'s correspondence with Aeneas to per-region backward functions?
4. What is the proof effort for a pair whose recursion structures differ, for example an in-place partition or rotation against a pure specification? Can you show the goals?
5. For opaque, bodiless definitions: is there a way to check a body once and then hide it from conversion (like Lean's `irreducible`), and is that sound with respect to [Call-type]'s reliance on unfolding?
6. What exactly does Fig. 8's property 6 ("mechanised, machine form") prove? Is injectivity after [Seal] normalisation claimed anywhere?
7. With copy-on-read, what does a user do to *prevent* an accidental deep copy of a large structure? Is there any static signal?
8. Does the IH-at-call-site rule remain sound when an argument's owner is a temporary (appendix note 24)? Is there a test where the owner is a temporary *and* the context would be non-injective without it?

## 6. What to cut or compress

- **Repetition.** The claim that sealed programs are Aeneas's backward functions appears in the abstract, §1.2, §2.2, §4.4 and §9. Keep it once, in §4.4, stated as a theorem with its fragment.
- **§1.3 (fire triangle).** Two dense paragraphs, and the comparison with Pédrot–Tabareau is qualified until it says little ("we claim only the resemblance"). Compress to three sentences, or move to §9.
- **§2.6 (`SubM`/`AddSub`).** Nice, but secondary to the pitch. Keep `LeAdd` feeding `SubM` in five lines and cut `AddSubId`.
- **§2.7 (size theorem).** Either show the `J` proof, since it is the honest cost, or cut the paragraph. Describing it in prose hides the cost.
- **§6.5 (subsingleton elimination).** This is standard Lean. A sentence and a citation suffice; the `Or` discussion belongs in the appendix notes.
- **§8 (the ledger).** Condense the class breakdown into one table row per class, and use the space for the evaluation of W3.
- **Space to add.** The rules for stuck blocks and erasure should get their own figure in the body. They are the heart of the soundness story.

A self-contained version would be: §1 with the fragment table; §2 with `AddMZero`, `TailM`/`AddMEq` and `AddToOne` only; the machine and [Close]; `Id`; typing, with one figure containing erasure, [Split] and stuck blocks; a proved fragment; an evaluation against Aeneas; related work.

## 7. Score and confidence

**Score: Reject.** (Scale: strong reject / reject / weak reject / weak accept / accept / strong accept.)

The idea is original and could become a strong paper. But:
- the submission's own artifact accepts a closed proof of `False` through a conjectured-but-false property (W1);
- the metatheory is otherwise unproved where it matters (W2);
- the claim that code need not be written twice is supported only by toy, structurally twinned examples, with no comparison against Aeneas or the other tools it positions itself against (W3);
- the modelled fragment of `&mut` is narrow and non-modular in ways a Rust audience will notice immediately (W4, W5).

**Confidence: high** for the Rust-verification and borrow-model assessment. **Medium** for the type-theoretic model sketch, which I checked only through the artifact.

**What would move my score up one notch (to weak reject or borderline):**
1. Fix W1 with a principled invariant: the erasure class and [Close] row become part of the Π-type and are respected by conversion. Include a proof, for at least the first-order fragment extended with function parameters, that the two paths take the same decisions.
2. Add a small evaluation against Aeneas+Lean on five or more programs, including one whose spec and implementation recurse differently.
3. State the Rust fragment up front in §1 as a table.

Adding region annotations to fix the lifetime imprecision would move it further.
