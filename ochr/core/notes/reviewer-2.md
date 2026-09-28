# Review: "Proving the Program You Run: Mutable borrows inside a dependent type theory, by observation and closing off"

Reviewer 2. Expertise: dependent type theory (Lean/Coq kernels, OTT, effects in type theory, NbE) and Rust verification (Aeneas, RustHorn/Creusot, Verus, RustBelt).

I read the whole paper (body, 24 pp.) and the whole formal appendix (A.1–A.7, 17 pp.). To check the paper's claims about them I also read, in full, four cited papers: Aeneas (Ho & Protzenko, ICFP'22), the Fire Triangle (Pédrot & Tabareau, POPL'20), Carneiro's *The Type Theory of Lean*, and Atkey's QTT (LICS'18).

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

1. An opaque declaration `leak : Π(n : Nat). &Nat` gives a closed proof `P(leak(5), refl) : Empty`, and via `J` a closed proof of `Eq Nat Z (S Z)`. The same holds for `Π(x : &Bool). &Nat` and many similar types. Safe Rust inhabits `fn(u32) -> &'static mut u32` (`Box::leak`). Yet §10.1 presents opaque definitions as the way Ochr "recovers the modularity of Aeneas", with no side condition.
2. Cor. 11 (consistency) is stated with no hypothesis on opaque definitions. Lemma 6 and §7.1 do say that an opaque borrow-returning definition is "an injectivity assumption". But membership in R is semantic, the paper gives no syntactic check, and the corollary does not carry the assumption.

There is also a presentational inconsistency. Opaque declarations are not in the appendix grammar of programs, yet they appear in the Discussion, in Lemma 6 and Cor. 9, and in the mechanisation.

I would like the authors to:

- confirm this derivation with their checker;
- add the hypothesis to Cor. 11;
- either give a checkable well-formedness condition for opaque types, or drop the modularity claim;
- state explicitly that R makes some Rust-inhabited function types empty.

### C2. The body states the stuck-block erasure rule that the appendix says is unsound

§4.4: "a stuck block is erased exactly when its match would be". Proof of Lemma 7(1): "a stuck block is erased exactly when its match is".

Appendix §A.5 (erasure, D40) says instead: "A stuck block is erased exactly when *each* of its arms … is a declared proof". Note 2 then states: "v1.7 first erased a block when its match would be erased; but … [this admits] `BoomG`. Hence D40."

So the body, including the proof sketch of the key stability lemma, describes the rule the appendix identifies as admitting a closed proof of false. Even if the body's phrase is meant loosely, a reader who implements the body's rule gets an unsound system. Given the paper's own history, this is exactly the class of mismatch that matters. Every such phrase in the body needs to be brought in line with the appendix, and Lemma 7's argument for (1) needs to be redone under D40. Under D40 the block and the directly-run match are *not* erased "exactly" together; they agree only because the block's sealed programs re-run the arms. That is a different, and more delicate, argument.

### C3. The soundness argument's hardest case rests on a theorem whose hypotheses do not cover it

Thm. 10 quantifies over "every valuation of the abstract values". For an abstract *function* `σ_g : Π(…). B`, a valuation is an arbitrary set-theoretic function in R, and the model needs this, since R is defined over set functions. The proof sketch says the hardest case, [Call-type], "combines Thm. 4(3), Lemma 5, Lemma 6 and Thm. 8". But the refinements α of Thm. 8 and Cor. 9 instantiate abstract functions only with "definable closures". So the naturality argument, which is how the paper relates the symbolic run at the generic call to the direct run at an instance, is not available for the valuations Thm. 10 actually quantifies over.

Either the [Call-type] case must be proved purely semantically, in the model, with no appeal to the machine, or the model must restrict function spaces to definable elements. That would be an unusual and non-standard model, and it would interact with impredicative `Prop`. Please say which.

### C4. Theorem 3 (simulation) as stated is false for `J`, and the translation is not compositional

The machine rule [J] returns `t` *unconditionally*. In CIC_L, `Eq.rec` reduces to its minor premise only when the endpoints are convertible: K-like reduction, Carneiro §2.6.4 and the κ/K⁺ rule of §4.1. A run that evaluates `J(Nat, Add(n,0), n, P, AddZero(n), t)` in data position, with P large, therefore takes a machine step that is *not* a CIC_L conversion. Thm. 3's claim "t†(Ω†) ≡ (v†, Ω′†) in CIC_L" fails, unless J translates to something ill-typed.

This is harmless in an extensional set model. But the paper's framing is "every machine step becomes a conversion there [in CIC_L]" (§7.1), so the framing is wrong. Relatedly, "the translation is defined per run" and "a symbolic run and a concrete run of one term can pass through different shapes". A translation indexed by runs is not a compositional interpretation of terms. The paper needs to say precisely what object Thm. 10 interprets a *definition* as, and why that object is independent of the run the checker happened to perform.

### C5. Persistent generalisation is equality reflection for neutrals; its model interpretation is unstated

[Split-gen] records n := σ, globally and surviving private copies (D34, D37). *Every later derivation* of the sealed program n then normalises to ρ*(σ), including derivations after the split, in the continuation, and in later-formed types.

This is not Lean's `generalize`. There the new variable is universally quantified and later occurrences of `n` are unrelated to it. Here σ is definitionally equal to Run(n) from then on, and simultaneously treated as a variable that splits may refine. In the model σ must therefore denote Run(n), not a free variable. Otherwise the conversion "n ≡ σ", used for later derivations, fails under valuations where σ ≠ Run(n). Thm. 10 says "every valuation of the abstract values". That must be restricted to *coherent* valuations, and the [Split] case must be argued for splits on such dependent σ.

I believe this can be made to work. But it is a genuinely new definitional principle, and the paper mentions it only as an implementation detail ("Lean's `generalize`", §A.5).

### C6. Conversion is weaker than claimed, and Π-type conversion is syntactic

The abstract says definitional equality "unfolds in-place code exactly as Lean unfolds pure code". But:

- Conv-cong compares Π-closures by "captured values and code", *syntactically* (Note 19). So `Π(n:Nat). P((λy.y)(n))` and `Π(n:Nat). P(n)` are not convertible. Neither are the Π-types of two definitions whose statements differ only by a β-step.
- Conv-fun requires the two functions' Π-types to be convertible (hence syntactically equal), and their captured values pairwise convertible.
- There is no η for functions or for `Unit`.
- A sealed program whose head call is stuck is convertible only to a syntactically identical one (Conv-fun under the least-fixpoint reading, §A.6).

For a Lean-style theory these are substantial incompletenesses. They will bite in higher-order code, where [Call-type] checks A′ᵢ ≡ Tᵢ at function types. Please either justify them or normalise Π-codomains at the generic arguments, as Conv-fun already does for function values.

### C7. Other gaps and imprecisions

- *Termination* (Lemma 2): "concrete runs never evaluate types or proofs, so termination reduces to the recursion [Rec] enforces". Pairs may contain functions (T-Pair only excludes `&`), closures may be passed and returned, and large elimination computes types. Termination of a higher-order language with structural recursion needs a reducibility argument, not a remark. Lemma 2's invariance part is a `sorry` in the mechanisation, and the one mechanised simulation equation *assumes* loan-freeness "which should follow from Lemma 2".
- *"Owned locals are observed … if `Id` ignored owned locals … transport along that equation would prove `Eq Nat 6 5`"* (§5). `Id A t u` computes to `Eq` between observation *values*, and `J` transports along that. I see no rule that lets one transport an `Id` into a program context `(□; x)`. Please give the derivation. As it stands the argument is about the *meaning* of `Id`, not about consistency.
- *Proofs and mutation.* §4.2 says "a proof may use mutation freely on its copy". §6.4 says erased terms are checked not to write, borrow or move any place that outlives them (confinement, D41). The reference checker does not implement confinement (Note 6, "in progress"), so the implementation and the rules differ on this point.
- *Closures cannot capture neutral data or proofs* (Note 21). After `AddM(&*x, 1)`, the program `let n = *x; λ(y : Nat) : Nat => n` is *rejected*. For a dependent type theory this is a severe restriction: any local lemma or Π-type mentioning a closed-off value is affected. It contradicts "any program may appear in a statement". It belongs in the body, not in the last appendix note.
- *Discussion, "Nothing in a goal mentions loans"*. Sealed programs for returned borrows contain `loan_k`. I believe observations always resolve these holes before a goal is formed, but this is exactly the kind of invariant that should be stated and proved, not asserted as a design aspiration.
- *Carneiro and unique typing.* §7.1 argues that reflection is unavailable because "Carneiro's set model relies on unique typing, which reflection breaks". Carneiro §1.2 points out that Barras's Aczel-encoding trick removes the dependency on unique typing for soundness ("if our only goal was proving soundness we could skip section 4 entirely"). A translation of Ochr into an extensional type theory with impredicative proof-irrelevant `Prop`, followed by the standard Aczel-encoded set model, therefore looks viable. It would be more modular and more checkable than a bespoke interpretation "by recursion on derivations". The authors should address this route.
