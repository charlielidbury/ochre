# Review: "Proving the Program You Run: Mutable borrows inside a dependent type theory, by observation and closing off"

Reviewer expertise: dependent type theory (Lean/Coq/Agda kernels, OTT, effects in type theory, NbE) and Rust verification (Aeneas, RustHorn/Creusot, Verus, RustBelt). I read the whole paper (body and the 17-page formal appendix), checked the claims about the fire triangle against the cited paper, built and ran the artifact, and wrote ten small probe files against the checker (§7 lists them with their results).

**Score: Reject. Confidence: high (expert).**

**Is this, in its current form, a publishable document that makes mutability and dependent types deeply compatible? No.** Consistency, which is what "deeply compatible" means for a type theory, is asserted but not established. The paper gives only one-paragraph sketches. The mechanisation it cites is absent from the artifact and covers a first-order fragment of an earlier version of the rules. The set-theoretic model described cannot exist for the calculus as defined, because the sort rule `&T : Type₀` makes `Type₀` impredicative (confirmed in the checker). On top of that, the dependent-type side is much weaker than the "Lean-style" framing suggests. Π-types are compared by unevaluated code plus captured values, a closure that captures a variable cannot inhabit a closed Π-type, and there is no ∧-elimination. The demonstrated compatibility covers Peano numbers, lists and one BST insertion, in a fragment with no loops, no shared borrows and no borrows in data.

---

## 1. Summary

The paper presents Ochr, a core calculus that puts Rust-style mutable borrows (Aeneas's LLBC values with loans and borrows) inside a Lean-like dependent type theory with an impredicative, proof-irrelevant `Prop`. Definitional equality is normalisation by a deterministic, call-by-value symbolic machine, and typing is that machine run on abstract inputs, with case splits where the checked program inspects an abstract value. Three ideas carry the paper:

1. **Closing off.** When a call's body is stuck on an abstract value, the call is replaced by *sealed programs*: closed source programs such as `⌈let c = σ; AddM(&c, 0); c⌉`, one for the result and one for the final content of each borrowed place. These are neutral values that re-run when a later split refines `σ`. For borrow-returning calls, the sealed programs contain a *hole* `loan_k` that is filled when the returned borrow ends. The paper identifies these with Aeneas's backward functions, region abstractions and RustHorn prophecies.
2. **`Id A t u`.** This computes to `Eq` between *observations*: the result paired with the final contents of a footprint of places (the owners of every place either side may write). OTT-style rules for pairs and reflexive equations strip the unchanged components.
3. **[Call-type].** A call's type is its callee's codomain evaluated at the call site. For a recursive call on a reborrowed field, the observation therefore sees the caller's owner "through" the surrounding constructor, and the induction hypothesis arrives already wrapped in the congruence context (`S □`). `AddMZero` and a BST `InsertMEq` are proved by bare structural recursion.

The paper also includes a model sketch (computations into CIC_L, types into sets à la Carneiro, with an "injectivity relation" `R` on borrow-returning functions), a stability lemma and a naturality theorem for the "two evaluation paths", a Lean 4 reference checker (~3.3 kloc) with 247 verdict assertions and a "counterfactual ledger" of rule switches, and a mechanisation claim for part of the effectful layer.

## 2. Novelty and significance

The central technical idea is new and pleasing. It uses closing off as the neutral form of a stuck *effectful* call, and it types an induction hypothesis in the caller's environment so that the frame property supplies the congruence step. The `AddMZero` trace, which I reproduced with the checker, shows a genuinely different proof experience: the IH `Eq Nat (S ⌈…σ₁…⌉) (S σ₁)` is literally the goal. If the approach scaled and were proved consistent, it would be a significant contribution. As submitted, its significance is limited by how little it covers and by the unresolved correctness issues in §3.

Positioning relative to prior work:

- **Aeneas** already provides the symbolic LLBC semantics, the forward/backward decomposition, and region abstractions for returned borrows; the machine here is explicitly Aeneas's. The new contribution is *where* the translation happens: lazily, inside conversion, in source syntax. That is a genuine design point, but the paper gives no evidence that it is better for users than Aeneas + Lean. There is no shared example, no proof-size comparison, and nothing near Aeneas's scale; the Aeneas case studies (hashmap, B-epsilon tree, AVL) rely on some mix of loops, machine integers, vectors, `Option<&mut T>` and borrows in data, none of which Ochr supports. Aeneas is also *modular*: it never unfolds callees. Ochr must unfold callees to decide conversion, so type checking is whole-program symbolic execution unless a definition is made opaque. The paper states this but does not evaluate its cost.
- **RustHorn / Creusot prophecies.** The analogy "hole = unresolved prophecy" is apt. Creusot's `^x` specifications are, however, a mature and usable answer to the same problem, and the paper gives no comparison of what is easier or harder to express.
- **HTT / Ynot / F\* (Dijkstra monads, `reify`, Steel/Pulse).** These handle general heaps. Ochr's advantage is that equality between computations is a type decided by conversion. That advantage holds only while conversion can decide it; everything else requires `J` with hand-written motives (see `SizeInsert` in the artifact). Relational F\* work, e.g. Grimm et al. CPP'18 on a monadic framework for relational verification, deserves discussion.
- **∂CBPV / eMLTT / the fire triangle.** I checked the cited claims against the paper. "Observable effect" is indeed defined for closed terms (Def. 3). "Desynchronisation between effects performed in the term and in the type" is P&T's phrase for the *call-by-name* corner (§2.3), and Prop. 18 (thunkable ⟺ natural) is a property of the *forcing* model. Ochr is in the call-by-value corner: substitution is restricted to values ("a type contains only values") and dependent `let` works because the checker *evaluates* the bound term. That is a semantic value restriction in the style of Lepigre's PML (ESOP'16) and of Zombie (Casinghino–Sjöberg–Weirich, POPL'14), neither of which is cited. The claimed correspondence with naturality is, in the paper's own words, "a correspondence of invariants, not an embedding". I found it suggestive rather than informative.
- **OTT.** Only the pair rule and the reflexivity rule are adopted. `Id` is observational in name and in spirit, but none of OTT's substantive rules (function extensionality, computation by type structure beyond pairs) appear.
- **QTT.** The comparison is superficial. Ochr's runtime/erased split is Lean's sort-based erasure, not usage quantities, and the affine discipline that the paper's "allocates nothing" claim needs is "outside the core".
- **Missing related work:** Krishnaswami–Pradic–Benton, *Integrating linear and dependent types* (POPL'15), which has linear state, dependent types and in-place update; Low\* (ICFP'17); Dafny/Why3 ghost code and two-state lemmas as the "one language" alternative; RefinedRust (PLDI'24); Electrolysis (Ullrich 2016), an earlier Rust→Lean functional translation; Gillian-Rust; PML; Zombie. ATS deserves more than a passing mention, since it is the oldest "proofs about the in-place program in one language" system.

## 3. Correctness concerns

I list these in decreasing order of severity. Items marked **[checked]** were reproduced with the authors' checker; §7 gives the probe programs.

### C1. The sort of `&T` makes `Type₀` impredicative, which invalidates the model and moves the system into System U⁻ territory [checked]

Appendix A.4 ("Sorts") gives `&T` the sort `Type₀` for *every* `T`, and [T-Ref] imposes only that `T` contains no `&`. Types are values and places can hold them, so `x : &Type₀` is legal and `*x` is a type. A Π-closure's sort is "the largest sort of its parameter types and codomain", so

```
reject def Pred : Type := Π(X : Type) (a : X). X          -- Type₁: correctly rejected
def Impred : Type := Π(x : &Type) (a : *x). *x            -- accepted: lives in Type₀
def PolyId (x : &Type) (a : *x) : *x := a
def SelfApp (u : Unit) : Impred := let T = Impred; PolyId(&T, PolyId)     -- accepted
def SelfAppEq (n : Nat) : Id Nat (let T = Impred; let f = PolyId(&T, PolyId); let N = Nat; f(&N, n)) n := refl   -- accepted
```

Quantifying over `Type₀` through a borrow therefore lands in `Type₀`, and the polymorphic identity can be instantiated at its own type. Consequences:

1. **Theorem 10 (soundness of the model) is false as stated.** Its first clause, "types of sort s denote elements of s's universe", fails for `Impred`. Its denotation is a subset of Π_{A∈U₀}(A → A), which contains the polymorphic identity and so has rank ≥ κ, hence it is not in U₀ = V_κ. More generally, by Reynolds' theorem, System F, which now embeds in `Type₀`, has no set-theoretic model with full function spaces. The ZFC-plus-inaccessibles consistency argument cannot go through for the calculus as defined.
2. **The rules now contain Girard's System U⁻.** Map * ↦ `Prop`, □ ↦ `Type₀`, △ ↦ `Type₁`. The axioms * : □ and □ : △ hold (`Prop : Type₀ : Type₁`). The rules (\*,\*) and (□,\*) come from impredicative `Prop`, (□,□) is standard, and (△,□) is exactly `Π(x : &Type₀). B : Type₀`. Two nested impredicative universes are the known inconsistent configuration: Hurkens' paradox is a closed term of λU⁻. Coq's `-impredicative-set` avoids exactly this configuration: there `Prop` is not an element of the impredicative `Set`. Borrows cannot be captured by closures, but a type is borrow-free and can be copied out of `*x` at the start of each λ, so the restriction is no obstacle.
3. **I did not obtain a closed proof of `Eq Nat 0 1`.** My transcription of Hurkens' term was blocked only by C3: `τ(t)` must be a closure capturing `t`, and a capturing closure is never convertible to the closed Π-type `U`. As far as I can tell, the checker's consistency on this front currently rests on an incompleteness of conversion that the authors would presumably want to remove (see C3). **Fix:** `&T` should live in the sort of `T` (or `&` should be restricted to data types), and the soundness proof must cover borrow parameters of type-valued types.

This is the most important finding of the review. It is not in Fig. 7, not in the ledger and not in the appendix notes, which suggests that the design process (find a counterexample, add a side condition) has not converged.

### C2. Consistency and soundness are asserted, not proved

§7 states Theorem 3 (simulation), Theorem 4 (frame), Lemmas 5–6 (owners/injectivity; backward functions are injective), Lemma 7 (stability), Theorem 8 (naturality), Corollary 9 (adequacy), Theorem 10 (soundness) and Corollary 11 (consistency). Each comes with a paragraph describing "the hardest case". None has a proof in the paper, and there is no proof appendix: the appendix is a *definition*. The set-theoretic interpretation "exists on paper only", but that paper is not part of the submission. The mechanisation (§7.6):

- follows "an earlier version of the rules";
- covers a first-order fragment "with no closures, types or stuck blocks". Most of the counterexamples in Fig. 7 (erasure, closures, stuck blocks, generalisation, positivity) and every finding in C1/C3/C6 live in exactly those excluded parts;
- has its invariance lemma still a `sorry`;
- does not cover Lemmas 5–7 or Theorem 8 (2);
- **is not included in the artifact** (§6).

The design history makes the absence of a proof decisive rather than cosmetic. Fig. 7 and appendix notes 1–9 record at least ten distinct closed proofs of `False` found in earlier versions. The ledger has 33 switches. The argument for Lemma 7 is "each decision is read from syntax", which enumerates the decisions the authors have thought of rather than proving that there are no others. C1 and C6 show that the enumeration is incomplete: C1 is a rule the argument never considers, and C6 is a restriction the argument silently relies on. A POPL-level type-theory paper needs at least a complete paper proof of Theorem 10 for the core, with Lemma 7 and Theorem 8 proved by induction over the machine. Given the history, a mechanised proof would be the convincing standard.

Two smaller points on §7:

- The proof sketch of Lemma 2 (invariance; termination) says "concrete runs never evaluate types or proofs". The machine rule [Erase-type] does evaluate types, on a private copy, including calls to type-returning recursive functions. The termination claim may still hold via [Rec], but the stated reason is wrong.
- The model interprets terms "per run, on that run's shapes", and relates runs "through their resolutions". This is unusual enough that its well-definedness (coherence across the different shapes a symbolic and a concrete run pass through) needs an explicit argument, not a sentence.

### C3. Conversion on Π-types is capture-sensitive and does not evaluate under binders [checked]

[Conv-cong] compares closures and Π-closures "by their captured values and their code", and a closure's type is "the Π-closure ⟨κ ⊢ Π(x̄ : Ā). B⟩" with the *closure's* captures κ. The checker implements exactly this. Consequences:

```
def Apply (f : Π(n : Nat). Nat) (n : Nat) : Nat := f(n)
def Cap (m : Nat) : Nat := Apply(λ(n : Nat) : Nat => Add(n, m), 0)
  -- rejected: "argument 1 (f) has type Π(n : Nat). Nat where κ1 = σ0, expected Π(n : Nat). Nat"
def Pow (X : Type) : Type := Π(a : X). Prop
def P1 : Pow(Nat) := λ(a : Nat) : Prop => ⊤
  -- rejected: "has type Π(a : Nat). Prop, but the goal is Π(a : κ1). Prop where κ1 = Nat"
def ZeroAdd (n : Nat) : Id Nat (Add(0, n)) n := refl
def UseRefl (h : Π(n : Nat). Id Nat n n) : Unit := ()
def PassZeroAdd (u : Unit) : Unit := UseRefl(ZeroAdd)
  -- rejected, although both codomains compute to ⊤ at the generic argument
```

The consequences go beyond minor incompleteness:

- **Higher-order programming is broken.** No closure that captures anything can be passed to a function whose parameter type is a closed Π-type, even when the captured variable does not occur in the type.
- **Type abbreviations do not unfold under binders.**
- **Π-typed lemma statements are compared as unevaluated code**, so a lemma cannot be passed where an equivalent, simplified statement is expected.
- **Church encodings are unusable**, and Ochr needs them, because `Prop` has only `Eq`, `⊤`, `∧` and Π.
- **It is inconsistent with [Conv-fun]**, which *does* evaluate function values at their generic call. The paper never justifies why Π-types are treated differently.

The abstract's "definitional equality unfolds in-place code as Lean's unfolds pure code" holds only at the top level of a type. Combined with C1, the obvious repair to this rule should be re-examined for consistency before it is made.

### C4. There is no ∧-elimination [checked]

The grammar has `⟨h, k⟩` but no projection; `h.1` on `P ∧ Q` is rejected ("no sub-place at type σ0 ∧ σ1"). `Id` with a k-place footprint computes to a k-fold conjunction, so any `Id` hypothesis that constrains more than one place can only be passed on whole, never decomposed. For a paper whose headline type former produces conjunctions, this is a real gap in the logic.

### C5. The `R` restriction makes Ochr refute types that safe Rust inhabits [checked]

Lemma 6 and Definition 1 restrict borrow-returning function spaces to those with injective backward functions. The paper argues that `R` is "forced" and admits that an opaque borrow-returning definition "is an injectivity assumption". Concretely, Ochr proves the following, and the checker accepts it:

```
def L (x : &Nat) (e : Id Unit (*x := 0) (*x := 1)) : Empty := J(Nat, 0, 1, M, e, ())
def Inj (g : Π(x : &Nat). &Nat) (x : &Nat)
        (e : Id Unit (let r = g(x); *r := 0) (let r = g(x); *r := 1)) : Empty := let r = g(x); L(r, e)
```

That is: for every `g : &Nat → &Nat`, writing 0 or 1 through `g(x)` leaves distinguishable states. This is false for the safe Rust function `fn g(_: &mut u64) -> &mut u64 { Box::leak(Box::new(0)) }` (a `'static` borrow coerces to the elided lifetime), whose backward function is constant. Aeneas handles `g` without difficulty. So Ochr's function types do *not* model Rust's, and the "sealed programs are Aeneas's backward functions" correspondence holds only for the injective subset.

Note 7 / [T-Pi] forbid `Π(n : Nat). &Nat` "although safe Rust inhabits it with a leaked `'static` borrow". The same objection applies verbatim to `Π(x : &Nat). &Nat`, so the added side condition removes one symptom and leaves the cause. This undermines the Discussion's modularity story, which rests on opaque definitions: every external or opaque borrow-returning function is an unchecked axiom, and nothing in Rust's type discipline discharges it.

### C6. The "two paths agree" argument depends on restrictions the checker does not enforce [checked]

Lemma 7 (4) says [Close]'s row is "read from the declared codomain". The appendix's syntactic restriction that "`&A` occurs only as the whole declared type" is what makes that decision stable, but the checker does not enforce it:

```
def F (n : Nat) (x : &Nat) : (match n { Z => &Nat | S _ => Nat }) := match n { Z => x | S _ => 0 }    -- accepted
def G (n : Nat) (a : Nat) : Nat := let r = F(n, &a); let r2 = r; let r3 = r; a                         -- accepted
def UseG : Nat := G(0, 5)    -- rejected: "[Read] r was moved out or its borrow ended (reading ⊥)"
```

At `G`'s generic call, `F(σ, &a)` closes off with the *data* row, so `r` is a copyable neutral and `a`'s loan is already filled. At the instance `n = 0`, `F` returns a live borrow, which the first read moves. `G` is thus an accepted definition that goes wrong on every instance with `n = 0`, contradicting Corollary 9 (adequacy) *for the checker*. Similarly, the side condition of note 7 / [T-Pi] / [Def] (a borrow-returning Π-type needs a borrow parameter) is not implemented: `Q (g : Π(n : Nat). &Nat) : Empty := P(g(5), refl)` is accepted.

Neither is a flaw of the calculus as written. They do show that (a) the claim that the implementation "follows the rules closely" and checks "every example in this paper" is inaccurate (note 7's example is accepted, where the paper says it is rejected), and (b) syntactic restrictions the stability argument depends on appear neither in Fig. 7 nor in the ledger, so the ledger cannot catch their absence.

### C7. Smaller technical points

- **"The program you run" rests on an informal optimisation.** The core machine *copies* borrow-free data on every read, so `Add(x, y) := AddM(&x, y); x` copies a whole Peano number at the end. "An addition that allocates nothing" relies on an affine usage discipline, "outside the core", that turns last-use copies into moves. §1.1 criticises the pure route because its gap "is bridged by an optimisation the programmer cannot state or rely on", and the same criticism applies here. Either formalise the move semantics and relate it to the machine, or soften the claim.
- **Decidability and termination of type checking are open.** Every refinement re-runs every sealed program mentioning the refined value, so the checking cost on anything larger than the examples is unknown. The only measurement is 11.6 ms for 247 tiny declarations.

## 4. Clarity

Strengths: §2 is excellent. The running example is well chosen, the environment diagrams make closing off concrete, and the checker's trace of `AddMZero` really does reproduce §2 "symbol for symbol" (I ran it). The appendix is careful and names the implementing functions, which made the artifact easy to audit. The authors are commendably explicit about what is and is not mechanised (§7.6).

Weaknesses:

- **The body is mostly prose where a POPL paper needs rules.** The typing rules for the basic forms are omitted as "the evident ones". [Call-type], [Def], [Split] and [Rec] are paragraphs inside a "figure". The real definition lives in a 17-page appendix, and §7 introduces shapes, views, resolutions and `Ctx_O` in one sentence each before stating theorems about them.
- **Some claims are stronger than the evidence.** "Proofs about in-place functions become plain structural recursion" holds for the `Id`-equivalence lemmas. The one measure theorem (`SizeInsert`) needs two explicit `J` transports per arm with hand-written motives plus an auxiliary lemma. "No spec/implementation divide" sits uneasily with `InsertMEq`, whose specification *is* the pure `Insert`; it is written in the same language, but it is still a second program. "Every side condition is load-bearing" (§8) is contradicted by the ledger itself: two rows are labelled "redundant under D41" and flip nothing.
- **Numbers disagree with the artifact and with each other** (§6): 239 vs 247 verdicts, "thirty" vs 33 ledger rows, 11 ms (§8) vs 9 ms (§10).
- **The ledger cannot be traced to the paper.** The artifact labels its ledger rows with internal decision numbers (D17, D41, P1, …) that the paper never defines, so a reader cannot map the prose of §8 and the rows of Fig. 7 to the ledger rows that are supposed to justify them.
- **Format.** The paper does not use the acmart/PACMPL format; body plus references run to about 23 pages at 10pt US-letter, which would exceed the page limit once reformatted.

## 5. Strength of the evaluation

- **Examples.** Peano `AddM`/`TailM`/`SubM`, list append and `LastM`, and BST insertion with a size lemma. All are first-order and total, with at most two borrow parameters. The fragment excludes loops, shared borrows, borrows stored in data (so no `Option<&mut T>`: even BST `get_mut` is out), closures capturing borrows, arrays/vectors, machine integers and indexed families. None of Aeneas's or Creusot's published case studies can be expressed. For a paper whose thesis is "deep compatibility", the evidence is a handful of Peano-arithmetic lemmas.
- **No comparison.** There is no side-by-side with Aeneas + Lean or Creusot on the same function: no proof-size, annotation-burden or checking-time comparison.
- **Performance.** There is one number (the whole suite in ~11 ms). Conversion unfolds callees and re-runs sealed programs after every refinement, so the paper should at least measure scaling: deeper recursion, more constructors, longer call chains.
- **Implementation.** It is a useful executable definition. The verdict assertions and the counterfactual ledger are good practice, and I would like to see the ledger adopted more widely. But the checker is unverified (`partial def` throughout, ~80 in `Machine.lean`), shares the C1 universe bug, and diverges from the appendix in at least the two places of C6. The ledger shows that each switch is *necessary* for some test, not that the rules are *sufficient*.
- **Mechanisation.** It is claimed in the abstract and §7.6, but absent from the artifact, so I could not evaluate it (§6).

## 6. Artifact evaluation

What I did: `lake build` in `ochr/core/lean` (toolchain v4.33.0) completed in 25.7 s wall, all green. `lake exe tests` exited 0 in a further ~33 s (compiling the runner plus 21 timing runs). The shipped `main.pdf` is identical in text to a fresh `typst compile` of the sources.

| Paper claim | Artifact | Verdict |
|---|---|---|
| "about 3,300 lines … plus about 1,100 lines of examples and tests" | 3,334 lines in `Ochr/*.lean`; 1,228 lines of examples + runner | OK |
| "All 239 verdicts are as expected" | `verdicts as expected: 247/247 (expected total 247)` | **number wrong** |
| "decides the whole suite in about 11 ms" (§8); "about 9 ms in total" (§10) | total check time 11.6 ms | OK / internally inconsistent |
| "a clean build takes under half a minute" | 25.7 s (README says 42 s) | OK |
| "the thirty rows of the counterfactual ledger" | 33 rows, each asserted by `#guard` in `Registry.lean` | **number wrong** |
| "every row of the counterfactual ledger flips at least one of them [the closed false proofs]" | rows P1 and P3 ("redundant under D41") flip **nothing**. Rows P2 (private copy), C8, G1, D27 and D39 flip only *accepted* programs to rejected (completeness), not false proofs | **false** |
| abstract: the suite "records, for every side condition, the false proof it rules out" | no row for non-cumulativity, the [T-Pi]/[Def] borrow-parameter condition, or the `&`-position restriction; private-copy row admits no false proof | **overstated** |
| "Every example in this paper is checked by it" | note 7's `Q(g : Π(n : Nat). &Nat) : Empty` is **accepted** (the paper says [T-Pi]/[Def] reject its type); the checker contains no implementation of that condition | **false** |
| the trace of `AddMZero` reproduces §2 | reproduced exactly (`[Call-type] AddMZero(borrow_4 σ1) : Eq Nat (S ⌈…⌉) (S σ1)`) | OK |
| §7.6: a Lean mechanisation, no `sorry` except invariance | **no such development in the artifact** (no `meta-lean/`; the only `.lean` files are the checker, which has no theorems) | **cannot evaluate** |

Things I found broken or divergent (details in C1, C3–C6 and §7):

1. **Universe bug, shared by the appendix and the checker.** `&T : Type₀` for all `T`, so `Π(x : &Type)(a : *x). *x : Type` is accepted while `Π(X : Type)(a : X). X` is (correctly) `Type₁`, and impredicative self-application type-checks.
2. **Not implemented:** the borrow-returning Π-type side condition of [T-Pi]/[Def] (note 7).
3. **Not enforced:** the "`&` only as the whole declared type" restriction. A codomain that computes to `&Nat` is accepted, and an accepted definition then fails with a use-after-move on every instance with `n = 0`.
4. **Stale README.** It still says the checker and appendix differ on "declared vs computed sort Prop" (they now agree) and quotes a 42 s build and 247 declarations. The paper says 239.

Overall, the artifact is functional and pleasant to use. It supports the *examples* of the paper but not its *metatheoretical* claims, and it disagrees with the formal appendix in two places that matter for soundness arguments.

## 7. Probe programs

All were run with `lake env lean <file>` against the built checker, each wrapped in `ochr S { … }` and `#eval IO.println (run "S" S).show`. "rejected"/"accepted" are the checker's verdicts.

| # | Program (abridged) | Result | Shows |
|---|---|---|---|
| S1 | `M(n) : Type := match n {Z => Unit \| S _ => Empty}`; `P(x : &Nat, e : Id Unit (*x := 0) (*x := 1)) : Empty := J(Nat, 0, 1, M, e, ())`; `Q(g : Π(n : Nat). &Nat) : Empty := P(g(5), refl)` | all accepted | [T-Pi]/[Def] condition missing (C6) |
| S2/S8 | `Impred : Type := Π(x : &Type)(a : *x). *x`; `PolyId`; `SelfApp := let T = Impred; PolyId(&T, PolyId)`; `SelfAppEq … := refl`; `reject Pred : Type := Π(X : Type)(a : X). X` | as annotated | impredicative `Type₀` (C1) |
| S3 | `Apply(λ(n : Nat) : Nat => Add(n, m), 0)`; `P1 : Pow(Nat) := λ(a : Nat) : Prop => ⊤` | both rejected | capture-sensitive Π conversion (C3) |
| S4 | `Inj(g : Π(x : &Nat). &Nat, x : &Nat, e : Id Unit (let r = g(x); *r := 0) (let r = g(x); *r := 1)) : Empty := let r = g(x); L(r, e)` | accepted | Ochr refutes `Box::leak`-style functions (C5) |
| S5 | `Id Nat (Add(2, 3)) 5 := refl`; the `Pick … z := b …` program of Thm 8; `AddMZero` trace | accepted / rejected / trace matches §2 | paper examples reproduce |
| S6 | `AndL(P Q : Prop, h : P ∧ Q) : P := h.1` | rejected | no ∧-elimination (C4) |
| S7 | `F(n, x : &Nat) : (match n {Z => &Nat \| S _ => Nat}) := match n {Z => x \| S _ => 0}`; `G(n, a) := let r = F(n, &a); let r2 = r; let r3 = r; a`; `UseG := G(0, 5)` | F, G accepted; `UseG` rejected ("reading ⊥") | accepted definition goes wrong at instances (C6) |
| S9 | `UseRefl(h : Π(n : Nat). Id Nat n n)`; `UseRefl(ZeroAdd)` with `ZeroAdd(n) : Id Nat (Add(0, n)) n` | rejected | no evaluation under Π binders (C3) |
| S10 | `PIref(x : &Prop, h1 h2 : *x) : Id (*x) h1 h2 := refl` | accepted | (sanity check: proof irrelevance survives `&Prop`) |

## 8. Questions for the authors

1. **(C1)** What sort should `&T` have when `T` is a sort or a Π-type of sort ≥ `Type₀`? Is `Π(x : &Type₀). B : Type₀` intended? If not, what is the corrected rule, and does Theorem 10's proof then cover borrow parameters of type-valued types? If it is intended, how can a set-theoretic model exist, given Reynolds' theorem and λU⁻?
2. **(C2)** Is there a complete written proof of Theorem 10 / Corollary 11, and of Lemma 7 and Theorem 8 (2)? Can it be included? Which rule version does the mechanisation of §7.6 follow, and why is it not in the artifact?
3. **(C3)** Why are Π-types compared by captured values and unevaluated code, while function values are compared by their generic observation? Is `λ(n : Nat) : Nat => Add(n, m)` intended *not* to have type `Π(n : Nat). Nat`? If conversion were made to evaluate Π-types at generic arguments, what breaks, and does Hurkens' paradox then go through (C1)?
4. **(C4)** How is a hypothesis of type `P ∧ Q` (in particular a multi-place `Id`) used?
5. **(C5)** How do you reconcile `R` with safe Rust functions that return leaked `'static` borrows? Could the model drop injectivity, e.g. by observing the returned borrow's *identity* rather than relying on `back` being injective? What exactly must a user prove before binding an opaque borrow-returning definition to external code?
6. **(C6)** Which syntactic restrictions does Lemma 7 rely on beyond the four listed, and are they all enforced by the checker? Can the ledger be extended so that every restriction the stability argument relies on has a switch?
7. How would loops, shared borrows and `Option<&mut T>` (the next three features any Rust client needs) enter the closing-off rule? In particular, what is the neutral form of a stuck call returning `Option<&mut T>`, where the number of holes depends on an unknown tag?
8. What is the checking cost on something larger than the examples, e.g. a 10-function module with nested calls? Is there a worst-case blow-up from re-running sealed programs after each refinement?
9. Can the compiled (erased, move-semantics) program be related formally to the machine, so that "the program you run" is a theorem rather than a slogan (C7)?

## 9. Score and what would change it

**Score: Reject.** **Confidence: high.**

The core ideas (closing off as the neutral form of a stuck effectful call, observation-valued `Id`, and induction hypotheses typed in the caller's environment) are original and worth publishing *once they rest on a consistent, adequately expressive system*. At present: consistency is unproved and, for the calculus as written, the stated model cannot exist (C1–C2); conversion is too weak for ordinary dependent programming (C3–C4); the function spaces diverge from Rust (C5); and the evaluation consists of toy examples (§5).

**What would move my score up one step (to weak reject):**

- Fix the sort of `&T` and re-examine consistency, including against a Hurkens-style attack once conversion is made capture-insensitive.
- Include a complete paper proof of Theorem 10 and Corollary 11, with Lemma 7 and Theorem 8 proved rather than argued by enumeration.
- Ship the mechanisation and state precisely which rule version and fragment it covers.
- Align the checker with the appendix (the [T-Pi]/[Def] condition and the `&`-position restriction) and correct the numbers.

**To reach accept, additionally:**

- Make Π-type conversion evaluation-based, or justify why not, and add ∧-elimination.
- Add at least one non-trivial case study beyond Peano and BST insertion (ideally with loops or `Option<&mut T>`), with a side-by-side comparison of proof effort against Aeneas + Lean or Creusot.
- Either model Rust's full borrow-returning function space or state the restriction prominently as a limitation of the approach.

**Is this, in its current form, a publishable document that makes mutability and dependent types deeply compatible? No.** It is a promising design with an executable prototype. The system as defined is not shown to be consistent, and its model provably fails because of the `&Type₀ : Type₀` rule. Its dependent type theory is too weak for routine higher-order reasoning, and it has been demonstrated only on small first-order examples.
