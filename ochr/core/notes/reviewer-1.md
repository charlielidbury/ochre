# Review #1: "Proving the Program You Run: Mutable borrows inside a dependent type theory, by observation and closing off"

Reviewed version: the typst sources as of 2026-09-28 ~14:55. `meta.typ` changed while I was reviewing; I reviewed the later version, where Theorem 7 is split into operational and observational parts and the `Pick` remark was added. I also read the cited Pédrot–Tabareau (fire triangle), Ho–Protzenko (Aeneas, ICFP'22) and Carneiro (The Type Theory of Lean) in full, to check the claims made about them.

## 1. Summary

The paper presents Ochr, a core calculus that puts Rust-style mutable borrows inside a Lean-style dependent type theory. The type theory has an impredicative, definitionally proof-irrelevant `Prop`, universes, and `Eq` with `J`. The core is deliberately small. The data types are `Nat`, `Unit` and pairs. Places are `x | *p | p.1`, where `p.1` is the predecessor field of a number. There are no shared borrows, no borrows inside data, no closures that capture borrows, and no loops. Recursion is structural.

Definitional equality is normalisation by a deterministic big-step machine. The machine is Aeneas's LLBC symbolic semantics with one simplification: a loan is a variable bound by its borrow, so ending a borrow is a substitution and a loan may occur several times inside sealed programs. On abstract inputs the machine gets stuck, and the paper offers three ideas for what happens then.

1. **Closing off.** When a call's body is stuck on an abstract value, the call returns anyway. Each borrowed place is filled with a *sealed program* `⌈L; C; cᵢ⌉`: the same call re-run on fresh owned copies of the borrowed contents, then reading `cᵢ`. If the function returns a borrow, the fill contains a *hole* `loan_k`, filled when the returned borrow ends. Sealed programs re-run when a later case split refines an abstract value. A guard on the head call stops a sealed program from closing itself off again. A stuck `match` that is not a call body is closed off as a call to an anonymous function of its free places. This also gives joins after a match.
2. **Observational `Id`.** `Id A t u` runs `t` and `u` on independent copies of the current environment. It then compares their results together with the final contents of a *footprint*. The footprint is read off the syntax and traced back through loans to the owning places, the *owners*. `Id` computes to `Eq` on the observation tuples. Three extra conversion rules then strip what neither side changed: `Eq` on pairs is `∧`, a reflexive `Eq` is `⊤`, and `⊤` is a unit for `∧`.
3. **[Call-type] in the caller's environment.** A callee's statement is evaluated at the call site. For a recursive call on a reborrowed sub-place, the observation therefore sees the constructor around that sub-place, and the induction hypothesis arrives already wrapped in `S`.

The metatheory is a translation into Lean's type theory. It follows Aeneas: forward functions, and backward functions that take the final value of a returned borrow. Those backward functions are required to be injective, which turns the model into a logical relation. The paper states simulation, frame, borrow-ending-order and naturality/adequacy theorems, plus preservation and consistency. All of them come with proof sketches only. The mechanisation paragraph (§7.8) is a placeholder. By the paper's own account, the dependent layer, consistency, termination of higher-order programs and naturality for non-ground refinements are proved on paper only. A Lean reference checker of about 2,200 lines checks the paper's examples (about 105 verdicts). It also runs a "counterfactual ledger": switch off one side condition, and exactly the tests that condition is responsible for should flip.

## 2. Overall assessment (short version)

There is a genuinely new and attractive idea here. A stuck effectful call gets a neutral form that is a *source program*, and the backward function of Aeneas is recovered lazily inside conversion. The `LeAdd`/`SubM` example is persuasive: a lemma about the pure `Add` is accepted where a proof about in-place mutated state is required, with no bridging lemma. That is exactly the payoff one would want. The overview (§2) is one of the clearest introductions to a new calculus I have read this cycle.

As a POPL paper, though, it is premature, for four reasons.

- **The calculus is not formally defined.** The typing judgement is never given; §6 says "the evident rules" are omitted, and the particular rules are paragraphs of prose. Several rules that soundness depends on are unspecified: the motives of closed-off blocks, whether arms of stuck matches inside types are checked, `J`'s computation rule, and conversion under binders.
- **The metatheory is sketch-level where it is novel.** The consistency argument rests on components that are not established: a set model for the extensional target, and an injectivity logical relation that is never defined.
- **I believe I have found a core program that contradicts the implementation's claim that owner sets are never needed in the core** (C1 below). Either the test suite has a gap or a rule is missing from the paper.
- **The evaluation is on Peano numerals only.** On that data type the frame, owner and injectivity arguments are nearly trivial.

The novelty over Aeneas is real but narrower than the framing suggests. The advertised proof-effort gain is a single `cong S`, which a standard OTT conversion rule (one the paper says it adopts but does not) would give for free. The positioning against the fire triangle is also off.

## 3. Strengths

- **S1.** Sealed programs as neutral forms are a clean and original idea. Because loans are variables, [End] is plain substitution, the returned-borrow case is uniform (one [End] fills a hole in every owner at once), and borrow-ending order becomes a corollary of naturality. This is a real simplification over Aeneas's region abstractions and projectors (Aeneas Figs. 7–8).
- **S2.** Closing off a stuck `match` as an anonymous call is a neat answer to the "join" problem. Aeneas 2022 required every disjunction to be in terminal position and duplicated the continuation (Aeneas §4.3). Here precision is kept without a join of environments. This idea deserves more space than it gets (§6.3 is one paragraph).
- **S3.** Pure and in-place code are convertible (`Add(σ, y)` and the mutated `*x` normalise to the same sealed program). This is the best argument for putting the translation inside conversion, and the paper should lead with it more than with the congruence story.
- **S4.** The "why each condition is there" list (§6.5) and the counterfactual ledger (§8) are good methodology. The `Pick` remark (§7.5) honestly records an incompleteness and compares it correctly with Rust's non-lexical-lifetimes (NLL) behaviour.
- **S5.** I re-derived `AddMZero`, `AddZero`, `AddZero := AddMZero(&x)`, `LeAdd`, `AddMEq` (including the `TailM` hole being filled by the pending write) and the successor case of `AddSubId` on paper, under my reading of [Close] and [Seal]. They check out.

## 4. Novelty and significance

**Aeneas.** The paper says so openly: the machine is Aeneas's symbolic LLBC semantics, the model is Aeneas's functional translation, a sealed program is an application of a backward function, and a hole is a region abstraction. The contribution is therefore *where and when* the translation happens: inside conversion, lazily, with neutrals printed in source syntax. On top of that come three genuinely new pieces: loans as variables (S1), the stuck-block join (S2), and pure/in-place convertibility (S3).

What is not new is the insight that ownership makes mutation state-passing. That goes back to Wadler's "Linear types can change the world", Clean, Charguéraud–Pottier 2008, Electrolysis and Aeneas itself. Symbolic values refined by matches, with every occurrence substituted, are also Aeneas's (its §4.1).

The significance claim is that Aeneas users "work in two languages at once". But with Aeneas and Lean, the analogue of `AddMZero` is `induction x <;> simp [add_m_back, *]`, which is about the same size, and the paper gives no side-by-side comparison. The paper should also discuss the trusted computing base. Aeneas moves complexity into an untrusted-but-inspectable translation and keeps Lean's kernel. Ochr puts a symbolic borrow machine, with closing off, re-normalisation and owner resolution, *into the kernel*. That is a real cost for a verification tool, and it goes unmentioned.

Finally, §9 says "Aeneas translates eagerly, whole-program", while §9 and §10 also say "Aeneas is modular in that it never unfolds a callee". These contradict each other. Aeneas translates function by function, using callee signatures.

**RustHorn / Creusot / RustHornBelt (prophecies).** The analogy between the hole and a prophecy is accurate at the level stated. However, the core excludes exactly the programs for which prophecies were invented: borrows stored in data, iterators over `&mut`, and loops that advance a `&mut` cursor through a list. The paper itself calls these "the frontier" (§10.2). The comparison is therefore with the easy part of the prophecy story, and the claim that a hole is "the neutral form of … a RustHorn prophecy" is not yet tested where it matters.

**HTT / F\*.** §9 says "in all of these the effectful program is specified, not compared". This is not accurate for F\*. With DM4Free, `reify` turns a stateful computation into a state-passing function, and F\*'s normaliser can then prove equalities between reified computations by unfolding. That is the closest prior art for "equality of stateful computations decided by unfolding in the checker". The honest difference is that Ochr's state has the shape of its borrows, not a monolithic heap, so frame reasoning comes for free. That difference should be the stated point.

**Fire triangle / ∂CBPV / eMLTT.** The positioning in §1.3 and §9 is misframed.

- Pédrot–Tabareau's no-go theorem (their Thm 1) is about *observably effectful* theories. Their Def. 3 calls a theory observably effectful if it has a closed boolean term that some context can tell apart from both `true` and `false`. The paper itself says "every closed program behaves like a value" (§1.3). By Def. 3, Ochr is therefore not observably effectful, the triangle's hypotheses are not met, and a value restriction is not what makes Ochr consistent.
- Ochr also does not sit "in the call-by-value corner" in the sense Pédrot–Tabareau mean. Their §6.2 shows that the call-by-value theory whose types are restricted to values is "a very weak one": no dependent `let` and no large elimination. Ochr has both: `Le` is a recursive function returning `Prop`, and `let z = …; Id Nat z 2` uses the value of `z`. It also syntactically allows arbitrary computations inside types (`Id A t u`, `Le(y, *x)`). All of this is fine *precisely because* Ochr's effects are unobservable.
- The accurate framing is that Ochr is a pure type theory in which ownership makes state-passing implicit. That is still an interesting contribution, but it is a different pitch from "effects in dependent type theory".
- "Thunkability is naturality" cites Prop. 18 of the fire-triangle paper correctly. But Prop. 18 lives in the forcing model into an *extensional* target (their §10), where the forcing conditions are states of an effect. What Ochr's Theorem 7 states is that normal forms are stable under substituting refinements. Any normalisation-by-evaluation (NbE) algorithm, or any dependent pattern matching done by refinement, needs that property. The analogy is suggestive but carries no weight, and the "design test" it motivates is the standard stability requirement.
- eMLTT is parametric in an algebraic effect theory, not specific to global state. It was introduced in Ahman–Ghani–Plotkin (FoSSaCS'16); the paper cites Ahman's handlers paper (POPL'18) instead.

**Observational type theory (OTT).** Ochr adopts three conversion rules: pairs, reflexive equations, and `⊤` as a unit. That is a small fragment of OTT, and in particular it omits OTT's rules for constructors (`Eq Nat (S a) (S b) ≡ Eq Nat a b`, `Eq Nat Z (S b) ≡ ⊥`). Yet §9 says "we adopt the observational computation rules for the data types of the core".

This inconsistency matters for the paper's third headline idea. The constructor rule is sound in the same set model by `propext` and injectivity of `S`. With it, the induction hypothesis about a *copy*, `AddZero(p) : Eq Nat N(σ') σ'`, would be convertible to the goal `Eq Nat (S N(σ')) (S σ')`. "The environment does the congruence" would then buy nothing. Put differently, the idea solves a problem that a one-line conversion rule the paper says it already has would solve.

The actual role of evaluating statements in the caller's environment is to *apply lemmas* in an environment-relative logic. That is necessary, but its real costs are owner sets, injectivity of backward functions, and induction-hypothesis shapes that depend on whether the programmer borrowed or copied (`AddSubId`). The paper presents the mechanism as a benefit without weighing those costs.

The pun on "observational" (OTT's observational equality versus observations of programs) also confuses. Ochr's `Id` is a type former that runs programs, not an OTT-style equality computed by the structure of the type.

**Quantitative type theory (QTT).** The connection (usage inside types is erased) is loose but correctly stated.

**Missing related work.**
- Ullrich & de Moura, "'do' unchained" (ICFP'22): local imperative mutation inside Lean's pure code, proved by unfolding the same text. This is the obvious baseline for "one language".
- Mutable value semantics (Racordon et al., JOT'22; Hylo; Swift `inout`), which is essentially Ochr's discipline.
- Electrolysis.
- RefinedRust (PLDI'24), Gillian-Rust, and Verus's newer prophecy-based `&mut`.
- Zombie/Trellys (Casinghino et al. POPL'14; Sjöberg & Weirich POPL'15): call-by-value dependent types with a value restriction on dependency.
- Gilbert–Cockx–Sozeau–Tabareau (POPL'19) on definitional proof irrelevance and an `Eq` in `SProp`.
- Abel–Coquand (LMCS'20), for decidability (C2d).
- Dénès (2013) on `propext` versus Coq's guard condition (Q16).
- VeriFast, Prusti and Ynot are named without citations.

**Significance, overall.** The combination is original, and sealed programs as neutral forms are a contribution I would like to see published. The paper overstates four things: generality ("nothing in the rules is specific to [Nat]"), proof-effort gains ("frequently shorter"), its place in the landscape of effects in dependent type theory, and the maturity of its metatheory.

## 5. Correctness concerns

### C1. Owner sets appear to be needed inside the core, which contradicts §8

§5.1 and §6.5 say that observing only one owner of a returned borrow's hole lets [Call-type] prove `Id Nat (S Z) Z`. §8 says the opposite: switching owner sets off "changes no verdict, because every program that would need them requires a closure capturing a borrow, which the core excludes". I believe §6.5 is right and §8 is wrong. The following program uses no closures:

```
Pick(b : Nat, x₁ : &Nat, x₂ : &Nat) : &Nat := match b { Z => x₁ | S _ => x₂ }

Neq(y : &Nat, h : Id Unit (*y := Z) (*y := S Z)) : Eq Nat Z (S Z) := h

G(a₁ : Nat, a₂ : Nat, b : Nat,
  h : Eq Nat (let c₁ = a₁; let c₂ = a₂; let r = Pick(b, &c₁, &c₂); *r := Z;   c₁)
             (let c₁ = a₁; let c₂ = a₂; let r = Pick(b, &c₁, &c₂); *r := S Z; c₁))
  : Eq Nat Z (S Z) :=
  let r = Pick(b, &a₁, &a₂); Neq(r, h)

Bad : Eq Nat Z (S Z) := G(0, 0, 1, refl)
```

My derivation, under the rules as written:

- **`Neq` is valid.** At its generic call, `y = &c` with `c ↦ σ`. The type of `h` has footprint `{c}`, so it computes to `Eq Nat Z (S Z)`, which is exactly the goal.
- **`h`'s type in `G`.** At `G`'s generic call, `Pick` is stuck on `σ_b` and is closed off. Its hole `loan_k` goes into both `c₁` and `c₂`. Writing `Z` and then reading `c₁` ends `borrow_k`, so the left side normalises to `X_Z := ⌈let c₁ = σ₁; let c₂ = σ₂; let r = Pick(σ_b, &c₁, &c₂); *r := Z; c₁⌉`. The right side likewise normalises to `X_SZ`. So `h : Eq Nat X_Z X_SZ`.
- **`G`'s body.** `Pick(b, &a₁, &a₂)` closes off to the same canonical `L; C`, because [Close] uses fixed names, and it leaves the hole in both `a₁` and `a₂`. [Call-type] for `Neq(r, h)` evaluates `Id Unit (*y := Z) (*y := S Z)` with `y` bound to `r`.
  - With owner sets **off** and the single owner `a₁`, this is `Eq (Unit × Nat) ((), X_Z) ((), X_SZ) ≡ Eq Nat X_Z X_SZ`, which is exactly `h`'s type. `G` is then accepted.
  - With owner sets **on**, the footprint is `{a₁, a₂}` and the parameter type is `Eq Nat X_Z X_SZ ∧ Eq Nat Y_Z Y_SZ`, which `h` does not provide.
- **`Bad`.** At `b = 1`, `Pick` runs concretely and returns `&c₂`, so `c₁` stays `0` on both sides. `h`'s type becomes `Eq Nat 0 0 ≡ ⊤`, and `refl` proves it. `Bad` is then a closed proof of `Eq Nat Z (S Z)`.
- **If the single owner were `a₂` instead,** instantiating with `b = 0` gives the symmetric attack. This is the paper's own "whichever it picked".

The only ingredient beyond the paper's examples is a parameter type that writes through an earlier borrow parameter. `SubM`'s `h : Le(y, *x)` already has a parameter type that reads through one, and nothing in the paper forbids writing.

So, please either:

- add this test to the suite, so the ledger row is no longer empty and §8's explanation is corrected; or
- name the rule that rejects it.

If the rule is that `Id`-atoms may not occur in negative position within the core, then Lemmas 4 and 5, the injective restriction and the logical-relation model are all unnecessary for the core, and §7 is over-built. Either way, the paper currently contradicts itself about a side condition it calls load-bearing.

This matters beyond the single case. The paper's evidence that its side conditions are complete is the counterfactual ledger, and the ledger is only as good as the test suite.

### C2. The consistency argument rests on components that are not established

**(a) The extensional target.** Preservation (Thm 9(2)) lands in "ECIC_L, which adds equality reflection". The paper then says "Both have Carneiro's set model". Carneiro's thesis does not treat equality reflection, and his construction does not transfer as it stands:

- The interpretation (his §6) is defined through `lvl`/`sort` functions (his Lemma 6.1). These are what decide whether a `λ` or `∀` is read as a proof `•` or as a set-theoretic function or product.
- Those functions are well-defined *because of* unique typing (his Thm 4.1). Unique typing in turn rests on definitional inversion (his Thm 4.12), which is proved via Church–Rosser for his κ-reduction.
- Equality reflection breaks definitional inversion in inconsistent contexts. For example, from `h : Type₀ = (Prop → Type₀)` one derives `U ≡ Π`.

A set model of ETT exists (as a partial interpretation of derivations, with coherence), but it is a different construction, and here it must also account for Ochr's non-left-linear rule `Eq A a b ≡ ⊤ if a ≡ b` and for proof-irrelevant erasure. The alternative route, "CIC_L up to transports along propext equalities, as in the elimination of reflection", is not spelled out either. Winterhalter–Sozeau–Tabareau's translation needs uniqueness of identity proofs (UIP) and function extensionality in the target, and its source is a standard ETT, not one with impredicative, definitionally proof-irrelevant `Prop` and Ochr's extra conversions. As written, "Both have Carneiro's set model" is a new claim, not a citation.

**(b) Injectivity (Lemmas 4 and 5).** Π-types over borrow-returning functions translate into a *subset* ("with dg(T) → Fin injective"). Lemma 5 is described as "the fundamental lemma of the relation, by induction on typing", but the relation is never defined.

The translation of every such term must therefore carry an injectivity witness, which makes Theorem 9(4) and Lemma 5 mutually dependent. The paper gives no statement of that joint induction, and no treatment of higher-order code, abstract function parameters or opaque definitions. It also gives no proof of "and in general only then" in Lemma 4.

Injectivity is an unusual global semantic invariant. Every extension the paper lists as future work (closures capturing borrows, borrows in data, interior mutability) has to preserve it, and it is exactly the kind of property that fails silently. Note also that it is an *internal* principle: Ochr proves that every `h : Π(x : &Nat). &Nat` has an injective backward function (§7.1). So declaring an opaque definition of that type is an injectivity *assumption*. Importing a Lean function as such an opaque would be unsound in general. This deserves a sentence.

**(c) "The dependent layer is standard given Carneiro's model."** It is not standard:

- types are evaluated in environments;
- Π-codomains are closures over environment values;
- `Id` is interpreted by running programs and resolving owners;
- conversion contains a non-linear rule;
- [Split] generalises sealed programs.

This is the layer §7.8 leaves to paper, and on paper it is one paragraph (the proof of Thm 9).

**(d) Termination and decidability.** Lemma 1's termination argument is one sentence ("a reducibility argument over the simple structure of runtime values"). The language has universes, large elimination (`Le` returns a `Prop`; `J` has type-valued motives), impredicative `Prop`, higher-order functions, and re-normalisation cascades triggered by refinement. None of that is "simple structure".

Relatedly, Carneiro shows Lean's definitional equality is undecidable. Abel–Coquand show that normalisation fails for impredicative, proof-irrelevant `Prop` with transport that reduces on convertible endpoints. Ochr adopts both ingredients: `J` presumably reduces whenever `a ≡ b`, since `h` is erased. Ochr may escape because proofs are never run. The paper should still say which terms the checker ever normalises, why that set is closed under the rules (including `J` with `Prop`-valued motives and propositions computed by recursion), and whether type checking is decidable.

### C3. Rules that soundness depends on are not specified

- **(a) Stuck blocks inside types.** Program-level [Split] checks every arm. For a stuck `match` inside a *type*, the paper only says it is closed off (§4.4). Are its arms type-checked and borrow-checked? If not, a type such as `Id Unit (match n { Z => (let a = &x; let b = &x; *a := 1) | S _ => () }) ()` is formed symbolically, and the refinement `n := Z` then makes its sealed program fail. That breaks Theorem 7, which assumes the refined run exists, and with it preservation under [Split].
- **(b) Motives of closed-off blocks.** For a non-tail match whose arms have arm-dependent types (for example `let h = match n { Z => refl | S m => LeAdd(m, 0) }; …`), what is the result type of the anonymous function? It is the motive of dependent elimination and is never given. Relatedly, [Close] chooses its row by "result type", so the block's result type must be known before the arms are known.
- **(c) `J`.** Its typing and computation rules are not given; §5 only says it "takes its endpoints explicitly".
- **(d) Conversion under binders.** How are two Π-types, or two closures, compared? Is there η? The paper appeals to NbE (§4), and NbE evaluates under binders, but the machine as described does not.
- **(e) Π-codomain closures that mention an outer borrow.** "A closure over the values of the variables it mentions": what is captured when a codomain reads `*x`, or writes through `x`, for an outer `x : &Nat`? If this counts as a closure capturing a borrow, then no statement can quantify over data after a borrow parameter except through n-ary functions. Please say so.
- **(f) The typing judgement.** `Ω ⊢ t ⇓ v : A ⊣ Ω'` is never defined. The omitted "evident" rules are exactly where the unusual questions live: how terms inside types are checked, how a closed-off call gets its type, and how the types of erased terms are computed without running them.

### C4. The "shape" assumption of the model contradicts the `Pick` remark

§7.1 says: "A run fixes the *shape* of its environments … independently of the abstract values; that is what the borrow checker guarantees". It then defines the translation as a state-passing function "on fixed shapes". The `Pick` remark in §7.5 shows the opposite. There, the symbolic run and the concrete run end with different shapes: `r ↦ ⊥` symbolically, but `r` still live concretely. Yet Theorem 2 claims the same simulation "for the concrete machine". Please say precisely what the translation is defined on, and how concrete runs whose shape differs from the symbolic run are interpreted. Theorem 7(1) handles this operationally, "up to resolution", but the model section has not caught up.

### C5. [Split] generalisation of sealed programs

Replacing every occurrence of a sealed-program head by a fresh `σ` is sound as generalisation, provided the result is still well typed. Two things need an argument, though.

- **Well-typedness.** Is it preserved when only the *syntactic* occurrences in stored normal forms are replaced? A stored proof's type might depend on the sealed program in a way that is not syntactically visible.
- **Lost information.** Generalisation forgets that `σ''` equals `N(σ)`. After `match Add(x, 0) { … }`, can the user still apply `AddZero` to what the branch learned? Users will hit this immediately. It is the analogue of Coq's `destruct` without `eqn:`. It should at least be discussed as a completeness limitation, together with a workaround.

### C6. Footprints are not purely syntactic

§5.1 says the footprint "is syntactic, so it does not change when a later case split refines an abstract value". The places *written* are syntactic, but the *owners* are not: they depend on where loans sit, and refinement can remove a hole from a sealed program. In the `Pick` example, after `b := S _`, `a₁`'s fill normalises to `σ₁` and no longer contains `loan_k`. This happens to be harmless, because the component that loses its hole becomes reflexive and the `⊤` rules strip it. But the claim as stated is false, and the argument for why it is harmless belongs in the paper, since it is exactly what naturality for `Id` depends on.

### C7. What `Id` licenses is never stated

§5 says owned locals must be observed because "a context such as `(□; x)` … transport along that equation would prove `Eq Nat 6 5`". But the calculus has no program-level transport for `Id`. `J` transports along `Eq` between *values*, not along equivalences of programs. The real reason owned locals must be observed seems to be that the owners at a generic call *are* owned locals of the generic caller.

Relatedly, `Id A t u` does not imply contextual equivalence. By "unobserved moves are harmless", `t` may consume a borrow variable that the context uses later, so `C[t]` fails where `C[u]` succeeds. Please state what `Id` licenses:

- Is there a congruence lemma for sequencing (`Id t u → Id (t; k) (u; k)`), and under which side conditions?
- How does a user rewrite `AddM` into `AddM'` inside a proof about a *caller* of `AddM`?

Every example in the paper is proved by structural recursion over the very function it mentions. None shows a client proof that uses a lemma about a callee.

### C8. Smaller correctness points

- **Sealed programs contain `⋆` for proof arguments.** For example, the successor goal of `AddSubId` is `Eq Nat ⌈let c = N(σ', y); SubM(&c, σ', ⋆); c⌉ y`. So "a sealed program … is source code" and "nothing in a goal mentions loans, borrows, environments or backward functions" are not quite true: `⋆` is not source syntax. Also, the shape of the induction hypothesis depends on the borrow structure around the call. The programmer has to know that `&p` observes the owner through the `S` while `let c = p; …&c` does not (§2.6). That is a new concept, however it is printed.
- **"`Id` is not a new primitive" / "derived rather than primitive".** `Id` is a new type former. It computes by running programs in the ambient environment, with a syntactic footprint and owner resolution, and every soundness subtlety of the paper (owner sets, injectivity) lives there. Calling it derived undersells both what it is and where the risk is.
- **Opaque definitions under ground refinement.** Adequacy (Cor. 8) says a ground refinement "closes nothing off". A call to an opaque definition, declared with a type and no body (§10.1), is closed off even on ground inputs, because a refinement does not instantiate constants. Corollary 8 should exclude opaque definitions or say how they are handled.
- **`refl : ⊤`.** `refl` is overloaded as the proof of `⊤`, first used in §2 before the rule appears (Fig. 5). Please say this in §3.

## 6. Clarity of presentation

**What works.** §2 is excellent: concrete, well paced and honest about what the checker does. Fig. 4 ([Close]) is clear. §6.5 is valuable.

**What does not.**

- **The formal content is mostly prose.**
  - Fig. 6 ("typing rules") is four paragraphs.
  - The "evident" rules are omitted.
  - [Access], `drop`, frames, calls, [Seal], stuck blocks and captures are described only in prose.
  - The value grammar contains "closures | types" with no definition.
  - The model (Fig. 7) is "key clauses" using undefined notation: `holder(ℓ)`, `s without ā`, `Run`, `Out_B`, the "injective part".
  - The theorems mix `≡` (definitional equality in CIC_L), `=` and `≈` without defining which is which.

  A POPL paper about a new kernel needs the full rules, if necessary in an appendix.
- **Vocabulary load.** Observation, footprint, owner, closing off, sealed program, hole, inert loan, stuck block, generic call, head call, refinement, resolution, view, `Ctx`: a one-table glossary would help a great deal.
- **§7.8 is a placeholder** ("[to be filled in: …]"). The contributions list nevertheless says "The first-order fragment of the metatheory is mechanised", which a reader cannot check.
- **Overloaded notation.** `p.1` means both the predecessor place and the pair projection `t.1`. `N(σ)` and `N(σ, y)` are two different sealed programs under one name. The trace in §2.1 uses `x'` for `AddM`'s parameter without introducing it.
- **Precision.** The abstract says "Sealed programs are the backward functions of Aeneas", while §9 correctly says "an *application* of a backward function". "Aeneas translates eagerly, whole-program" contradicts §10's "modular" (see §4 above).
- **Typesetting.** In Fig. 6, the last line of each rule paragraph is centred. In Fig. 1, the `fix` line wraps. Page 11 is mostly blank.
- **Balance.** The overview takes 4.5 pages and the metatheory 6, yet the metatheory has almost no proofs. I would trade half of §2.6–2.7 and all of "Thunkability is naturality" for the typing rules and a real proof of one hard case (the [Call-type] case of Theorem 9).

## 7. Strength of the evaluation

**Examples.** Every example is on Peano naturals, a data type in which every value has exactly one sub-place. So every owner's content holds at most one chain of loans. The context `Ctx` of [Call-type] is always a stack of `S` constructors around at most one hole, possibly behind backward functions. On `Nat` the frame property, owner resolution and injectivity are therefore close to trivial. The hard cases are exactly the ones the core excludes:

- sibling sub-borrows (a pair or tree whose two fields are borrowed at once);
- a function taking `&Tree` that returns a borrow into either child;
- shared borrows;
- loops;
- borrows in data.

§10.1 claims that several fields "generalise directly" and that list append is "`AddM` with `Cons` in place of `S`", but neither is checked, even though an implementation exists. For scale: Aeneas 2022 verified a resizing hash table (201 lines of code, 4 person-days), and RustHorn/Creusot benchmarks include list traversal with `&mut` cursors.

**Implementation.** A 2,200-line reference checker with about 105 verdicts and a ten-second build is a good start for a design artifact. However:

- there are no timings of checking itself;
- there are no data on how large sealed programs get or how much re-normalisation happens under repeated refinement. Nested sealed programs such as `N(N(σ))`, or the `AddSubId` goal, suggest the growth could be significant;
- there is no caching;
- nothing connects the implementation to the formal rules beyond "follows the rules closely".

**Counterfactual ledger.** A good idea, but its evidential value is bounded by how complete the test suite is. By C1, the "empty row" is more plausibly a gap in the suite than evidence that a rule is harmless.

**Proof-effort claims.** The abstract says "frequently shorter than the corresponding proofs about pure functions". This is not measured. The only evidence is one saved `cong S` in one example. That saving is also available from OTT's constructor rule (§4 above) and from `simp` in Lean. A side-by-side table (Ochr versus Aeneas+Lean versus Lean `do`-notation, on the same functions, counting lines and interactive steps) would be the minimal evaluation of the central usability claim.

**Mechanisation.** It is a placeholder. By the paper's own account the dependent layer, consistency, termination for higher-order programs and naturality for non-ground refinements are on paper only. On paper they are sketches of three to ten sentences.

**The title's promise.** The core copies borrow-free data on every read. The claim that `AddM` "allocates nothing" (§1) depends on an affine usage discipline "outside the core", which licenses implementing a last-use copy as a move. No theorem connects the program that was checked to a program that runs with move semantics.

## 8. Questions for the authors

1. Is the `Pick`/`Neq`/`G`/`Bad` program in C1 accepted when owner sets are switched off? If it is rejected, by which rule? If it is accepted, please correct §8 and add the test.
2. If `Id`-atoms cannot occur in negative position in the core, what are Lemmas 4 and 5 needed for? If they can, why does §8 say no core program needs owner sets?
3. Which set model do you use for ECIC_L together with Ochr's extra conversions, given that Carneiro's construction depends on unique typing and definitional inversion? Alternatively, which translation to CIC_L, and with which axioms?
4. Please define the logical relation behind "the injective part".
   - How is the fundamental lemma proved for higher-order code and for abstract function parameters?
   - Is an opaque definition of type `Π(x : &Nat). &Nat` an injectivity assumption?
   - Is it sound to bind such an opaque to an arbitrary Lean function?
5. Are the arms of stuck blocks inside types type-checked and borrow-checked? What is the result type (the motive) of a closed-off block whose arms have arm-dependent types?
6. What are `J`'s typing and computation rules? How is conversion checked under binders, and is there η for functions?
7. Why not adopt OTT's rule for constructors (`Eq Nat (S a) (S b) ≡ Eq Nat a b`)? It is sound in your model, and it would make the copied induction hypothesis as good as the borrowed one. What would then remain of the third idea?
8. By Pédrot–Tabareau's Definition 3, is Ochr observably effectful? If not, please reframe §1.3 and the related-work paragraph.
9. How is a postcondition stated that constrains, but does not determine, the final state ("after `f(x)`, `*x` is even")? Is a type `P((f(x); *x))` the intended idiom? Please show one client proof that uses `AddMEq` or `AddMZero` *non-recursively* to reason about a caller of `AddM`.
10. What does `Id` license at the program level? Is there a congruence lemma for sequencing, and what are its side conditions (borrow consumption; places read outside the footprint)?
11. Which terms does the checker ever normalise? Is type checking decidable? How does Lemma 1 account for re-normalisation cascades and for `J`? What is the worst-case growth of sealed programs?
12. What does a Π-codomain capture when it mentions an outer borrow variable, for reading and for writing?
13. For binary trees, what do owners, `Ctx` and injectivity look like when two sibling sub-borrows are live at once? For example: a function on `&Tree` that recurses into both children, or one that returns a borrow into either child.
14. Can the head-call guard make two sealed programs that users would consider "the same" differ syntactically? For example, a stuck `match` inlined, versus the same `match` in a named helper. §6.3 says "a match and a call to a function containing it are treated alike". Does that mean they produce the *same* normal form?
15. What theorem connects the checked program (copy on read, proofs skipped) to the compiled program (moves, proofs erased)?
16. [Rec] is checked on values, and conversion contains `propext`-style rules. Coq's guard condition was found inconsistent with `propext` (Dénès 2013) through subterm checks that passed through casts along equalities. Please argue briefly why [Rec] is immune. I believe it is, since recursion is only on data entry values, but the paper should say so.
17. How does proof effort compare with Aeneas+Lean on your own examples?

## 9. Minor comments

- **§1.2:** "Sealed programs are exactly Aeneas's backward functions" should say applications of backward functions.
- **§2.6:** in `SubM`'s branch where `*x` is `Z` and `y` is `S q`, `h : Le(S q, Z) ≡ Eq Nat Z (S Z)` is absurd. The code returns `()` rather than eliminating `h`. A sentence explaining this would save the reader a double take.
- **§4.1:** "Inside types copying is essential: `Id Nat (Add(x, x)) x` must at least be a well-formed statement". This example is odd, since the statement is false. `x + x = 2 · x` alone makes the point.
- **§4.3:** "The precondition that each `uᵢ` is loan-free is guaranteed by [Access]". Please also say why non-borrow arguments `wᵢ` cannot contain holes. It follows from "borrow-free" meaning "no live loan", but the reader has to reconstruct that.
- **§5, Fig. 5 caption:** "for empty `W` the pair is just `A`" should say the *observation* is just the result.
- **§7.5, `Pick` remark:** "The checker is as conservative as Rust here". Make precise that Rust with NLL accepts reading `b` when `r` is dead afterwards, exactly as Ochr does. As written, it reads as if Rust rejects the read outright.
- **§9:** eMLTT citation (see §4 above). Ynot, VeriFast and Prusti need references.
- **Bibliography:** the `nbe` entry is a habilitation thesis formatted as `@inproceedings`. The title "FP²" has a literal `\textsuperscript`.

## 10. Score

**Weak reject.** Confidence: **high** (expert in dependent type theory kernels and in Rust verification).

The central idea of sealed programs as source-level neutral forms for stuck effectful calls, with the Aeneas translation performed lazily inside conversion, is new and worth publishing. §2 makes a compelling case for it. But the paper as submitted:

1. does not define its calculus formally;
2. supports its consistency claim with sketches that rest on an unestablished model (ECIC_L together with an undefined injectivity relation);
3. appears to contradict itself on a load-bearing side condition (C1);
4. evaluates only on Peano numerals, where the novel metatheory is nearly trivial;
5. overstates its advantages over Aeneas and its position relative to the fire triangle.

**What would move my score up one step (to weak accept):**

- **(a)** An appendix with the complete rules: machine, [Access]/`drop`, [Close]/[Seal]/stuck blocks with their motives and arm-checking, the typing judgement, and `J`.
- **(b)** Resolution of C1: either the missing rule, or the test plus a corrected §8.
- **(c)** Either a real proof of Theorem 9 in the [Call-type] and [Split] cases, against an explicitly constructed model with the injectivity relation defined, or the mechanisation that §7.8 promises, covering the effectful layer including Lemma 5.
- **(d)** At least one example with sibling sub-places (a binary tree), checked by the implementation, with timings.

Reframing §1.3 and §9 (fire triangle, OTT, Aeneas) would also be needed, but that is easy.

**The single change that would most improve the paper:** replace the prose rules and proof sketches with a complete formal definition and a real, preferably mechanised, soundness proof of the effectful layer, including an explicit model for the conversion rules and the injectivity relation. The paper's own narrative, that "every side condition in it is there because a smaller one admitted a proof of false", is exactly why sketches are not enough here.
