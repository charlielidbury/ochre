# Review: "Proving the Program You Run: Mutable borrows inside a dependent type theory, by observation and closing off"

Reviewer 2. Expertise: dependent type theory (Lean/Coq kernels, OTT, effects in type theory, NbE) and Rust verification (Aeneas, RustHorn/Creusot, Verus, RustBelt).

I read the whole paper (body, 24 pp.) and the whole formal appendix (A.1–A.6, 17 pp.). To check the paper's claims about them I also read, in full, four cited papers: Aeneas (Ho & Protzenko, ICFP'22), the Fire Triangle (Pédrot & Tabareau, POPL'20), Carneiro's *The Type Theory of Lean*, and Atkey's QTT (LICS'18).

## 1. Summary

The paper presents Ochr, a core calculus that combines Lean-style dependent type theory (impredicative, definitionally proof-irrelevant `Prop`, non-cumulative universes, structural recursion) with Rust-style mutable borrows. The borrows are modelled with Aeneas's LLBC value representation: a borrow carries its content and a loan is left behind. Definitional equality is normalisation by one deterministic big-step machine, which runs imperative code, including inside types. The paper makes three technical moves.

1. **Closing off.** When a call's body gets stuck on an abstract value, the call is replaced by *sealed programs* ⌈L; C; cᵢ⌉. These are closed source programs that recompute the call's result, and the final contents of its borrowed arguments, from owned copies. They act as neutral terms, and they re-run when a later case split refines their inputs. For borrow-returning calls, each sealed program contains a *hole* `loan_k` that is filled when the returned borrow ends. The paper identifies these sealed programs with Aeneas's backward functions and with unresolved RustHorn prophecies.
2. **`Id A t u`.** This compares two computations, each run from the current environment on a private copy. It is defined to compute to `Eq` between *observations*: the result plus the final contents of the *owners* of every place either side may write. The footprint is read off the syntax, and owners are found by following loans outwards. Three extra conversion rules (Eq on pairs is ∧; a reflexive Eq is ⊤; ⊤ is a unit for ∧) strip the components that did not change.
3. **[Call-type].** The type of every call, the recursive calls that act as induction hypotheses included, is computed by re-evaluating the callee's codomain *at the call site*. Its observations therefore see the caller's owners. The claimed pay-off is that an induction hypothesis about `&p`, where `p` is a field of the caller's borrowed data, "arrives already wrapped in `S`", so the congruence step disappears.

The paper then gives:

- worked examples: in-place Peano addition, a borrow-returning `TailM`, an equivalence proof `AddMEq`, `SubM` with a precondition about the current contents of a borrow, and BST insertion;
- a table of side conditions, each justified by a counterexample (a closed proof of false) found against an earlier version of the rules;
- a metatheory section, with a set-theoretic model after Carneiro, a simulation theorem identifying sealed programs with backward functions, a frame theorem, a "naturality" theorem, adequacy and consistency;
- a 3 kLoC Lean 4 reference checker that decides 185 test verdicts;
- a 17-page formal appendix.

The metatheory is almost entirely sketched. The paper states that the set model "exists on paper only". The Lean mechanisation covers parts of the frame theorem and a few machine lemmas for a first-order fragment of an *earlier* rule set, with no closures, types, stuck blocks, `Id` or [Call-type].

## 2. Novelty and significance

The central idea is genuinely new and, in my view, interesting: perform Aeneas's functional translation *lazily, inside conversion, and in source syntax*, and let the neutral form of a stuck effectful call be a closed program that owns its state. I know of no prior dependent type theory with this neutral form. The [Call-type] rule, which types a call site by re-running the callee's statement in the caller's environment, is also new. So is the observation that soundness then *forces* backward functions to be injective (the relation R of Def. 1 / Lemma 6). That observation is a real contribution to understanding the Aeneas translation. Preconditions stated about the *current* contents of a borrow (`SubM(x : &Nat, y : Nat, h : Le(y, *x))`), discharged by a lemma about the pure wrapper, are the most compelling single demonstration in the paper. Nothing in Aeneas, Creusot or Verus looks like it.

Against that, the significance claims are larger than the evidence.

**Relative to Aeneas.** The model *is* Aeneas's translation (§7.1 says so), and Aeneas's output is executable: Aeneas §2 evaluates translated tests on F*'s normaliser. So "definitional equality unfolds in-place code" is equally true of Aeneas + Lean. There, `add_m_back` unfolds by δι exactly as ⌈let c = σ; AddM(&c,0); c⌉ does here. The difference is the *notation* of the neutral term, plus the absence of a trusted translation step. The first is a usability claim the paper never evaluates. The second is only as good as the metatheory, which is unproven (§4 below).

The saving advertised in the introduction ("the environment does the congruence") is, for `AddMZero`, a single `congrArg S ih` in Lean. The paper concedes (`AddSubId`) that sometimes the programmer must *withhold* the congruence by copying. That is a new choice, borrow versus copy to shape the induction hypothesis, which the user did not have to make before. The claim that in-place proofs are "frequently shorter than the corresponding proofs about pure functions" (abstract) is not supported by any comparison.

Two small inaccuracies:

- §9 calls Aeneas "whole-program". Aeneas describes its translation as modular, with no "cross-function inlining or whole-program analysis" (Aeneas §2).
- Electrolysis (Ullrich 2016, Rust → Lean with lenses) is the closest prior Rust-to-Lean translation and is not cited.

**Relative to RustHorn/Creusot.** The reading "a filled loan is a resolved prophecy, a hole is an unresolved one" is apt and nicely put. Prophecy-based tools are specification-based and automated, so the two approaches are complementary rather than competing. That is fine.

**Relative to HTT/F\*.** §9 states that in HTT, Ynot and F\* "the effectful program is specified, not compared: two programs with the same specification are not thereby equal". This is inaccurate for F\*. `reify` (Dijkstra Monads for Free, POPL'17) turns a stateful computation into a state-passing function, and relational program-equivalence proofs by reification and normalisation are established practice (e.g. Grimm et al., *A Monadic Framework for Relational Verification*, CPP'18). `Id` is closest to "equality of reified computations restricted to a footprint". The paper should position against that line precisely. The differences are real: ownership instead of a global heap, a footprint derived from syntax, and [Call-type]. But the conceptual novelty of "equality of computations as a type" is smaller than claimed.

**Relative to ∂CBPV/eMLTT.** I checked the Fire Triangle paper.

- Def. 3 does quantify over *closed* terms, so the paper is right that local ownership removes the theorem's hypothesis.
- Prop. 18 is specific to the forcing translation: thunkable iff natural w.r.t. forcing conditions.
- §6.2 of that paper does say the CBV corner loses dependent `let` and large elimination.

So the citations are accurate. But the connection drawn in §1.3 and §7.4 is an analogy: refinements as forcing-condition morphisms, naturality. The authors hedge ("a correspondence of invariants, not an embedding"). The claim in §9 that "ownership gives a syntactic criterion for thunkability" amounts to *evaluating every type eagerly to a value on a private copy*. That is closer to ∂CBPV's `dlet` synchronisation than to a new criterion.

**Relative to OTT.** Only three computation rules are adopted: products, reflexive equations, ⊤-unit. There is no computation of `Eq` at Π or at inductives, so propositional funext is not obviously available. Calling `Id` "observational" in the OTT sense oversells this. It is observational in the testing-equivalence sense (observe results and final state).

**Relative to QTT.** The QTT citation is accurate: types are formed in the 0-fragment, and a use in a type consumes nothing. The analogous Ochr mechanism ("types are formed on a private copy", "copying is essential inside types") is informal. The affine discipline that would license "AddM allocates nothing" (§1, §4.1) is "outside the core" and never defined. As written, every read of `y` in `AddM` copies a unary numeral.

**Relative to Lean FBIP / Koka FP².** The characterisation in the paper is fair.

Overall, the idea is novel and potentially significant for dependently typed verification of Rust-like code. What is actually delivered is a design plus an implementation, with an unproven consistency claim and toy-scale evidence.

## 3. Correctness

I first checked the worked examples against the appendix rules by hand:

- `AddMZero`, both at the generic call and at the recursive call, including the owner computation owners(ℓ₁) = owners(ℓ₀) = {c};
- `AddZero`, and `AddZero(x) := AddMZero(&x)`;
- `AddMEq`, including the claimed normal form B(Sσ′, τ) = S B(σ′, τ), which needs [Access] to end the inner hole `loan_k2` when `c` is read;
- `LeAdd`/`SubM`/`AddSub`: `Add(σ, τ)` normalises to N(σ, τ) because the inner `AddM` closes off and the body continues;
- `AddToOne`: both borrow variables are captured in mode `mv`, so the hole lands in both fills.

All of them go through as described. This is to the authors' credit: the appendix is precise enough to calculate with.

I then tried to break the calculus. I did not find a closed proof of false in the opaque-free core. I found one concrete inconsistency that arises from a feature the paper advertises, one place where the body states a rule that the appendix says is unsound, and several gaps in the soundness argument.

### C1. Opaque borrow-returning declarations can be inconsistent, and Ochr refutes innocuous-looking types (serious)

Take the following definitions. `Empty` is as in Note 3 of the appendix.

```
M(n : Nat) : Type₀ := match n { Z => Unit | S _ => Empty }
P(x : &Nat, e : Id Unit (*x := 0) (*x := 1)) : Empty := J(Nat, 0, 1, M, e, ())
Q(g : Π(n : Nat). &Nat) : Empty := P(g(5), refl)
```

`P` is accepted. At its generic call W = owners(ℓ₁) = {c₁}, so `e : eq(Unit×Nat, ((),0), ((),1)) = Eq Nat 0 1`, and `J` transports `() : M(0)` to `M(1) = Empty`.

In `Q`, `g(5)` closes off by [App-neutral] with the `&T` row. The row gives `borrow_k ⌈let r = σ_g(5)ʰ; *r⌉`, and since I = ∅, **no loan_k is placed anywhere**. At the call to `P`, [Call-type] evaluates the type of `e` with `x ↦ borrow_k …`:

- own(x) = owners(k) = ∅, so W = ∅;
- both observations are `()`;
- so the parameter type is `eq(Unit, (), ()) = ⊤`, and `refl` inhabits it.

Hence `Q` is accepted. Ochr proves ¬(Π(n : Nat). &Nat).

This is *consistent* with the model, because R at that type is empty: back : Nat → 1 is not injective. But it has two consequences the paper does not state.

1. An opaque declaration `leak : Π(n : Nat). &Nat` gives a closed proof `P(leak(5), refl) : Empty`, and via `J` a closed proof of `Eq Nat Z (S Z)`. Types such as `Π(x : &Bool). &Nat` are also empty in the model (there is no injection Nat → Bool). I expect them to be refutable too, by a pigeonhole case analysis on back(0), back(1) and back(2). Safe Rust inhabits `fn(u32) -> &'static mut u32` (`Box::leak`). Yet §10.1 presents opaque definitions as the way Ochr "recovers the modularity of Aeneas", with no side condition.
2. Cor. 11 (consistency) is stated with no hypothesis on opaque definitions. Lemma 6 and §7.1 do say that an opaque borrow-returning definition is "an injectivity assumption". But membership in R is semantic, the paper gives no syntactic check, and the corollary does not carry the assumption.

There is also a presentational inconsistency. Opaque declarations are not in the appendix grammar of programs, yet they appear in the Discussion, in Lemma 6 and Cor. 9, and in the mechanisation.

I would like the authors to:

- confirm this derivation with their checker;
- add the hypothesis to Cor. 11;
- either give a checkable well-formedness condition for opaque types, or drop the modularity claim;
- state explicitly that R makes some Rust-inhabited function types empty.

### C2. The body states the stuck-block erasure rule that the appendix says is unsound

§4.4: "a stuck block is erased exactly when its match would be". Proof of Lemma 7(1): "a stuck block is erased exactly when its match is".

Appendix §A.4.1 (Erasure, D40) says instead: "A stuck block is erased exactly when *each* of its arms … is a declared proof". Note 2 then states: "v1.7 first erased a block when its match would be erased; but … [this admits] `BoomG`. Hence D40."

So the body, including the proof sketch of the key stability lemma, describes the rule the appendix identifies as admitting a closed proof of false. Even if the body's phrase is meant loosely, a reader who implements the body's rule gets an unsound system. Given the paper's own history, this is exactly the class of mismatch that matters. Every such phrase in the body needs to be brought in line with the appendix, and Lemma 7's argument for (1) needs to be redone under D40. Under D40 the block and the directly-run match are *not* erased "exactly" together; they agree only because the block's sealed programs re-run the arms. That is a different, and more delicate, argument.

### C3. The soundness argument's hardest case rests on a theorem whose hypotheses do not cover it

Thm. 10 quantifies over "every valuation of the abstract values". For an abstract *function* `σ_g : Π(…). B`, a valuation is an arbitrary set-theoretic function in R, and the model needs this, since R is defined over set functions. The proof sketch says the hardest case, [Call-type], "combines Thm. 4(3), Lemma 5, Lemma 6 and Thm. 8". But the refinements α of Thm. 8 and Cor. 9 instantiate abstract functions only with "definable closures". So the naturality argument, which is how the paper relates the symbolic run at the generic call to the direct run at an instance, is not available for the valuations Thm. 10 actually quantifies over.

Either the [Call-type] case must be proved purely semantically, in the model, with no appeal to the machine, or the model must restrict function spaces to definable elements. That would be an unusual and non-standard model, and it would interact with impredicative `Prop`. Please say which.

### C4. Theorem 3 (simulation) as stated is false for `J`, and the translation is not compositional

The machine rule [J] returns `t` *unconditionally*. In CIC_L, `Eq.rec` reduces to its minor premise only when the endpoints are convertible: K-like reduction, Carneiro §2.6.4 and the κ/K⁺ rule of §4.1. A run that evaluates `J(Nat, Add(n,0), n, P, AddZero(n), t)` in data position, with P large, therefore takes a machine step that is *not* a CIC_L conversion. Thm. 3's claim "t†(Ω†) ≡ (v†, Ω′†) in CIC_L" fails, unless J translates to something ill-typed.

This is harmless in an extensional set model. But the paper's framing is "every machine step becomes a conversion there [in CIC_L]" (§7.1), so the framing is wrong. Relatedly, "the translation is defined per run" and "a symbolic run and a concrete run of one term can pass through different shapes". A translation indexed by runs is not a compositional interpretation of terms. The paper needs to say precisely what object Thm. 10 interprets a *definition* as, and why that object is independent of the run the checker happened to perform.

### C5. Persistent generalisation is equality reflection for neutrals; its model interpretation is unstated

[Split-gen] records n := σ, globally and surviving private copies (D34, D37). *Every later derivation* of the sealed program n then normalises to ρ*(σ), including derivations after the split, in the continuation, and in later-formed types.

This is not Lean's `generalize`. There the new variable is universally quantified and later occurrences of `n` are unrelated to it. Here σ is definitionally equal to Run(n) from then on, and simultaneously treated as a variable that splits may refine. In the model σ must therefore denote Run(n), not a free variable. Otherwise the conversion "n ≡ σ", used for later derivations, fails under valuations where σ ≠ Run(n). Thm. 10 says "every valuation of the abstract values". That must be restricted to *coherent* valuations, and the [Split] case must be argued for splits on such dependent σ. Conversely, once an abstract value embedded in n is itself refined, the refined program no longer matches the recorded key. σ then loses its link to n: sound, but a further source of incompleteness.

I believe this can be made to work. But it is a genuinely new definitional principle, and the paper mentions it only as an implementation detail ("Lean's `generalize`", §A.4.5).

### C6. Conversion is weaker than claimed, and Π-type conversion is syntactic

The abstract says definitional equality "unfolds in-place code exactly as Lean unfolds pure code". But:

- Conv-cong compares Π-closures by "captured values and code", *syntactically* (Note 18). So `Π(n:Nat). P((λy.y)(n))` and `Π(n:Nat). P(n)` are not convertible. Neither are the Π-types of two definitions whose statements differ only by a β-step.
- Conv-fun requires the two functions' Π-types to be convertible (hence syntactically equal up to captured values), and their captured values pairwise convertible.
- There is no η for functions or for `Unit`.
- Sealed programs are compared by Conv-cong, i.e. syntactically up to their embedded values. So two functions whose bodies are stuck at their generic call are convertible only if they are identical (least-fixpoint reading of Conv-fun, §A.3).

For a Lean-style theory these are substantial incompletenesses. They will bite in higher-order code, where [Call-type] checks A′ᵢ ≡ Tᵢ at function types. Please either justify them or normalise Π-codomains at the generic arguments, as Conv-fun already does for function values.

### C7. Other gaps and imprecisions

- *Termination* (Lemma 2): "concrete runs never evaluate types or proofs, so termination reduces to the recursion [Rec] enforces". Pairs may contain functions (T-Pair only excludes `&`), closures may be passed and returned, and large elimination computes types. Termination of a higher-order language with structural recursion needs a reducibility argument, not a remark. Lemma 2's invariance part is a `sorry` in the mechanisation, and the one mechanised simulation equation *assumes* loan-freeness "which should follow from Lemma 2".
- *"Owned locals are observed … if `Id` ignored owned locals … transport along that equation would prove `Eq Nat 6 5`"* (§5). `Id A t u` computes to `Eq` between observation *values*, and `J` transports along that. I see no rule that lets one transport an `Id` into a program context `(□; x)`. Please give the derivation. As it stands the argument is about the *meaning* of `Id`, not about consistency.
- *Proofs and mutation.* §4.2 says "a proof may use mutation freely on its copy". §6.4 says erased terms are checked not to write, borrow or move any place that outlives them (confinement, D41). The reference checker does not implement confinement (Note 6, "in progress"), so the implementation and the rules differ on this point.
- *Closures cannot capture neutral data or proofs* (Note 21). After `AddM(&*x, 1)`, the program `let n = *x; λ(y : Nat) : Nat => n` is *rejected*. For a dependent type theory this is a severe restriction: any local lemma or Π-type mentioning a closed-off value is affected. It contradicts "any program may appear in a statement". It belongs in the body, not in the last appendix note.
- *Discussion, "Nothing in a goal mentions loans"*. Sealed programs for returned borrows contain `loan_k`. I believe observations always resolve these holes before a goal is formed, but this is exactly the kind of invariant that should be stated and proved, not asserted as a design aspiration.
- *Carneiro and unique typing.* §7.1 argues that reflection is unavailable because "Carneiro's set model relies on unique typing, which reflection breaks". Carneiro §1.2 points out that Barras's Aczel-encoding trick removes the dependency on unique typing for soundness ("if our only goal was proving soundness we could skip section 4 entirely"). A translation of Ochr into an extensional type theory with impredicative proof-irrelevant `Prop`, followed by the standard Aczel-encoded set model, therefore looks viable. It would be more modular and more checkable than a bespoke interpretation "by recursion on derivations". The authors should address this route.

## 4. Status of the metatheory versus the claims

| Result | Status according to the paper | What the abstract and introduction say |
|---|---|---|
| Model / consistency (Thm. 10, Cor. 11) | set-theoretic interpretation "exists on paper only"; one paragraph of proof sketch naming "the hardest case" | abstract: "a model in Lean's type theory … which establishes consistency" |
| Simulation (Thm. 3) | one equation at machine level, assuming loan-freeness; others "in progress"; CIC_L translation "not started" | abstract: "a model in Lean's type theory in which Aeneas's backward functions reappear" |
| Frame (Thm. 4) | parts (1), (2) mechanised for a first-order fragment of an *earlier* rule set; part (3), the one [Call-type] needs, not mechanised | contributions: "the first-order fragment of the metatheory is mechanised" |
| Stability (Lemma 7), injectivity (Lemmas 5, 6), naturality (Thm. 8 beyond one commuting lemma) | "not started" | intro: "an adequacy theorem relating the symbolic machine to concrete evaluation" |
| Invariance (Lemma 2) | stated, proof is `sorry` | — |

The claims in the abstract and introduction do not match this.

1. The model is *not* "in Lean's type theory". §7.1 explicitly says no translation into intensional CIC preserves conversion, and that types are interpreted in ZFC sets.
2. Consistency is not "established". It is argued by a sketch.
3. "The first-order fragment of the metatheory is mechanised" overstates what is done. What is mechanised is a few operational lemmas of an earlier rule set. None of them concerns `Id`, [Call-type], erasure, stuck blocks or generalisation. Yet *every* row of the paper's own Fig. 7 (the side conditions and the proofs of false that forced them) concerns exactly those features.

The mechanisation therefore gives almost no assurance about the part of the design that has historically been unsound.

For a calculus whose own paper reports some ten distinct counterexamples against earlier versions, most of them closed proofs of false and the rest accepted programs that go wrong (Fig. 7, Notes 1–5, "two attacks from a separate review"), and whose rule set is at "v1.9" with open items (D41), I cannot accept "consistent" on the strength of a proof sketch. The authors are admirably candid about the status in §7.6. The abstract and introduction must be equally candid.

## 5. Clarity and organisation

The overview (§2) is excellent: concrete, well-paced, and the running examples are well chosen. The trace of `AddMZero`'s induction hypothesis is the clearest explanation I have seen of why a backward-function translation needs a congruence step, and of how an environment can supply it.

The rest of the body is less successful.

- §§3–6 describe the calculus mostly in prose. The typing section gives four prose "rules" and says "the rules for the basic forms are the evident ones … we omit them". Footprints, owners, [Access], erasure and closing off of stuck blocks are all prose. A reader cannot check the metatheory claims against the body and must use the 17-page appendix. Given the page budget (the body ends at p. 23 of 25), I would move a compact figure of the core typing judgement and of `W`/owners into the body, and shorten §9–§10.
- §7 states its theorems at a level of informality ("on that run's shapes", "up to ≈", "ends some borrows early") that makes them hard to evaluate or falsify. The per-run translation, in particular, needs a definition.
- The appendix is precise but is written as internal design documentation. It refers to decision numbers (D4 … D42, P1 … P6), checker issue labels (C12, C15, C19), rule-set versions (v1.5 … v1.9), internal attack names (`breaker-fresh-v16 X3`, `lean-checker P2`, `BoomG`, `BoomH`, `BoomL`, `BoomB`) and Lean function names. None of these can be resolved by a reader. They also communicate, not unfairly, that the calculus is still moving. The notes that record earlier unsound readings are valuable, but they should be rewritten as self-contained counterexamples with derivations.
- Fig. 7 ("Why each condition is there") is a good idea and I would keep it. But presenting design as "each side condition was added in response to a concrete closed proof of false" is, for a type-theory paper, a signal of fragility rather than of robustness. What is missing is the *invariant* that the conditions jointly establish, stated once and proved. Lemma 7 is meant to be this, but it is only sketched, and (see C2) its sketch uses the superseded rule.
- Terminology. "Observational" collides with OTT. The "Id" name suggests an identity type, but `Id` has no introduction or elimination of its own. "Sealed program", "closing off", "footprint", "owner", "hole", "inert" and "generalisation record" are all introduced informally, some only in the appendix.
- The title promises "the program you run". But there is no compiler. The run-time story (erasure plus an affine discipline that turns copies into moves) is informal and outside the core, so "allocates nothing" (§1) is not a property of the calculus.

## 6. Evaluation

- **Examples.** All examples are on unary naturals, plus small user-declared lists and binary trees: addition, subtraction, a tail borrow, BST insertion, list append. There are no machine integers, arrays or vectors, loops, shared borrows, borrows stored in data, or closures capturing borrows. All of these are acknowledged as future work. There is no example drawn from real Rust code. Aeneas's evaluation already verifies a resizable hash table, and Creusot and Verus handle far larger code. I do not expect scale from a core-calculus paper. But claims about proof *effort* ("frequently shorter", "no bridging lemma", "no congruence step") require at least a side-by-side comparison with Aeneas + Lean on the paper's own examples. None is given.
- **Implementation.** A 3 kLoC Lean checker with 185 expected verdicts, a build-time "counterfactual ledger" (switching off each rule flips exactly its tests), and a 9 ms suite. The ledger is a genuinely good engineering practice and I would like to see it adopted more widely. However: (i) the checker does not implement confinement (D41); (ii) it inherits the known incompleteness of Note 21; (iii) "every row of the counterfactual ledger flips at least one test" shows that each rule is *necessary* against known attacks, not that the rules are *sufficient*. The suite is regression evidence, not a soundness argument. No artifact is described (acceptable for double-blind, but it should be promised).
- **Mechanisation.** As discussed in §4, it covers little of what matters for the headline claims.
- **Completeness.** The paper honestly reports several ways the checker is incomplete, and I found two more:
  - the `Pick` program that runs on every concrete input but is rejected (Thm. 8 discussion);
  - no η for `Unit`, and the [Close] row keyed on the declared codomain (Note 10);
  - closures unable to capture neutrals (Note 21);
  - syntactic Π-conversion (C6, mine);
  - generalisations that lose their link to later-refined inputs (C5, mine).

  The combined effect on usability is not assessed.

## 7. Questions for the authors

1. Does your checker accept `Q(g : Π(n : Nat). &Nat) : Empty := P(g(5), refl)` from C1, and hence a closed proof of `Empty` from an opaque `leak : Π(n : Nat). &Nat`? What syntactic condition on opaque declarations guarantees membership in R? Does Cor. 11 assume there are no opaque declarations?
2. Which stuck-block erasure rule do Lemma 7 and its proof use: the body's ("exactly when its match is") or D40 ("when each arm is a declared proof")? Please redo the argument for Lemma 7(1) under D40.
3. In Thm. 10, abstract function values range over R, i.e. arbitrary set functions. Thm. 8 and Cor. 9 cover only definable instantiations. How is the [Call-type] case discharged for a definition with a function-typed parameter?
4. How does the model interpret an abstract value introduced by [Split-gen], given that later derivations of the generalised sealed program are *definitionally* replaced by it (C5)? Is the valuation in Thm. 10 restricted to coherent valuations?
5. What CIC_L term does `J` translate to, such that the [J] machine step is a CIC_L conversion when the endpoints are not convertible? More generally, what exactly is the denotation of a definition, given that the translation is "per run"?
6. What is the termination argument for concrete runs in the presence of first-class closures, closures inside pairs, and large elimination?
7. §5 says that ignoring owned locals in the footprint would let "transport along that equation prove `Eq Nat 6 5`". Which rule transports an `Id` into a program context? Please give the derivation.
8. Why is Π-type conversion syntactic (Note 18), when function values are compared by generic observation? Do you have examples where higher-order code fails to check because of it?
9. How often does Note 21 (closures cannot capture neutral data or proofs) block natural programs? Is it a gap in the checker or in the rules?
10. Can you give Aeneas + Lean proofs of `AddMZero`, `AddMEq`, `InsertMEq` and a `SubM` client, for comparison? The claim that in-place proofs are "frequently shorter" rests on this.
11. How does `Id` compare with relational verification by `reify` in F\* (Grimm et al., CPP'18)?
12. Which version of the rules does the Lean mechanisation follow? What is the plan for `Id`, [Call-type] and erasure, which is where Fig. 7's counterexamples live?
13. Is the affine discipline that justifies "AddM allocates nothing" defined anywhere, and is the copy-to-move optimisation proved to preserve the machine's semantics?
14. Is it intended that R makes function types such as `Π(n : Nat). &Nat` provably empty, and `Π(x : &Bool). &Nat` empty in the model? (This is arguably right for safe Rust without `'static`, but it should be stated, together with its consequences for modelling library functions.)

## 8. Score

**Weak reject.** Confidence: **high** (4/5). I work in both areas, read the whole submission including the appendix, and checked the cited papers.

The core ideas are original and would interest the POPL audience. Closing off into sealed source programs is one. The [Call-type] rule, with the induction hypothesis arriving in the caller's context, is another. The discovery that consistency forces injective backward functions is a third. The examples are clear, and the appendix is precise enough to calculate with.

But the paper's headline claim is a consistent dependent type theory, and that claim is not established. The model is a sketch on paper, it contains the gaps listed in C3–C5, and its mechanisation does not touch the features that the paper itself shows have been repeatedly unsound. The body contradicts the appendix on a rule (C2) that the appendix identifies as the source of a proof of false. And a feature advertised for modularity, opaque declarations, is inconsistent at innocuous types (C1). The evaluation does not substantiate the usability claims.

## 9. What would move my score up one step (to weak accept)

A *complete, checkable* soundness proof for a clearly delimited fragment that includes `Id`, [Call-type], closing off with returned borrows, erasure and [Split-gen]. It may exclude universes beyond `Type₀`, stuck blocks, and opaque declarations if necessary. It should be either:

- a full paper proof in the supplementary material, with every case of Thm. 10, the frame and naturality lemmas, and the treatment of function-typed valuations and generalised abstract values; or
- a mechanisation of the model for that fragment.

It must be accompanied by:

- abstract, introduction and contributions rewritten to match exactly what is proved and mechanised;
- the C1 hypothesis added to the consistency corollary, with a checkable condition on opaque declarations;
- the body/appendix erasure mismatch (C2) fixed.

A side-by-side comparison with Aeneas + Lean on the running examples would strengthen the significance case, but it is secondary.

**The single change that would most improve the paper:** replace the sketched §7 with a complete proof of consistency for an explicitly delimited core, and align every claim in the abstract and introduction with it. As submitted, the paper's own evidence (a counterexample-driven rule history, and a mechanisation that excludes the type-level features) argues *against* taking consistency on trust.
