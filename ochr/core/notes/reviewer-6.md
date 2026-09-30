# Review 6: "Proving the Program You Run" (Ochr)

Reviewer background: dependent type theory and proof-assistant kernels (Lean, Rocq, Agda), OTT, NbE, set models, SProp and definitional proof irrelevance, effects in type theory.

I read the whole paper (body and appendix) at `c49e4f36`, then re-read the diff to `d964b73a`: moves are now the checked semantics, property 7 is mechanised, and the hash map is re-measured. I read the checker's source where the rules left me unsure. I did not read DECISIONS/RULES/notes/ROADMAP or the git history.

All attacks below were run on a private copy of `ochr/core/lean` at both commits, with the default `Config`. §4 gives each program verbatim, and all of them reproduce at `d964b73a`. I also ran `lake exe fuzz --seed 4242 --count 200000 --jobs 6`. It took 226 s and reported: checked 187,220, invalid 3,230, rejected 9,550. There were no nat/false/verdict/exec findings, 10 `escape` findings and 5,614 vacuous adequacy findings.

## 1. Summary

1. Ochr is a core calculus that puts Rust-style mutable borrows inside a Lean-style dependent type theory. Its definitional equality is normalisation by a symbolic machine that runs in-place code.
2. Three ideas carry the paper. A call stuck on an abstract value is *closed off* into closed "sealed programs" that play the role of Aeneas's backward functions. `Id A t u` compares two computations by their results and the final contents of the places they may write, and computes to a conjunction of `Eq`s. Induction hypotheses are typed at the call site, so evaluation performs the frame argument.
3. The evidence is informal and empirical:
   - an appendix that specifies the rules completely;
   - a Lean reference checker with 1,013 asserted verdicts and a counterfactual ledger;
   - a differential fuzzer;
   - a Lean mechanisation of the operational layer of an older version (1.3: no types, no erasure, no closures);
   - two case studies (Aeneas's hash map, and an in-place quicksort).
4. Consistency, the "two paths agree" stability property and naturality are conjectures. The paper says openly that its argument for stability "is still an enumeration of the decisions we know of, and each earlier version of it missed one."
5. **I found a new closed proof of `False` that the default checker accepts at both commits (§4, A1).** It combines three rules the ledger classifies as completeness or bookkeeping: global generalisation records, re-derived neutrals mapping to their records, and η for `Unit`. It exploits a decision the stability enumeration does not list: the type at which an observation compares a place.

## 2. Strengths

- **A new and interesting idea.** Closing off a stuck effectful call into *source-level* sealed programs is a genuinely new answer to "what is the neutral form of a stuck effectful computation?". Using the program itself as the specification (`Find(m,k) := Get(&m,k)`, and `Add` as `AddM` on a copy) is elegant. The `AddMZero` and `AddMEq` examples, where the induction hypothesis arrives already wrapped in `S` because the callee's statement is observed through the caller's owner, are memorable and well explained.
- **`Id` as a derived, computing proposition.** In the OTT spirit, `Id` needs no introduction or elimination rules of its own, and it reduces to ordinary equations that ordinary tactics-free proofs discharge.
- **Honesty.** The paper states clearly what is mechanised, what is conjectured and what is fuzzed (@fig-claims). It reports its own naturality counterexample (`Pick`) and says the first version of the hash map was *larger* than Aeneas's. It admits that the quicksort comparison measures automation, not the thesis. Its scope table (@fig-scope) is candid.
- **Engineering discipline in the artifact.**
  - Every verdict is asserted at build time, with per-file counts guarding against truncated files.
  - The counterfactual ledger ties every non-evident rule to a witness.
  - The fuzzer compares the generic path with instances.
  - The checker is small (about 5.3 kLOC), readable and well commented. Every checker function is tied to a rule name in the appendix.
- **Hardening against the obvious attacks.** Positivity, subsingleton elimination, zero-arm matches, large elimination in type positions, universe checks for parameters, recursion in types and the borrow-parameter rule for borrow-returning Π-types all held up in my attempts (A3–A10).
- **A real case study.** The hash map covers every theorem of Aeneas's interface, and the statement style (`InsertFindOther`) is a real selling point.

## 3. Weaknesses, most severe first

### W1 (fatal as submitted): a closed proof of `False` in the default checker, with a rule-level cause

The program is A1 in §4. `Boom : False` is accepted at `c49e4f36` and at `d964b73a`, where D53 moves are on by default. The mechanism has three steps. Each is licensed by the appendix as written, so this is a bug in the rules, not only in the implementation.

1. **Generalisation (appendix item 7).** Generalising a neutral `n` "at a place of type `T` takes σ fresh with Δ(σ) = T … and records n := σ", and the record is global.
   - In A1's `n := Z` arm, `n` is `⌈σg(())⌉`, where `g : Π(u : Unit). T(n)` is an abstract parameter.
   - The place type is `T(Z) = Box(Unit)`, so Δ(σ3) = Box(Unit).
   - `restoreKeep` keeps both the record and Δ(σ3), since σ3 was created in the arm.
2. **Re-derivation.** The record is keyed by the program text. `⌈σg(())⌉` does not mention `n`: its type depends on `n` only through Δ(σg). So in the `n := S σ5` arm the call `g(())` has type `Box(Bool)`, yet it re-derives the same text and is replaced by σ3, whose Δ is still `Box(Unit)`.
   - The trace shows `[Call-type] σ2(()) : Box(Bool)` and then `Cmp2(σ3)`.
   - A1's companion L1, which is accepted, shows the same leak with `Nat`/`Bool`: σ3 is split as `0`/`S σ4` in one arm and as `false`/`true` in the other.
3. **Observation in the untyped machine.**
   - `Cmp2(b) : Prop := (let c = b; Id Unit (c := MkBox(true)) (c := MkBox(false)))` returns types, so [Call-type] evaluates `Cmp2(σ3)` by running its body in the untyped machine.
   - There `c` has no stored type. [Obs] and [Id] take `T_i = type_Ω(π_i)`, which falls back to `typeof(Ω(c)) = Δ(σ3) = Box(Unit)`.
   - `eq` takes `MkBox(true)` and `MkBox(false)` apart at field type `Unit`. D59's `eq(Unit, _, _) = ⊤` then makes the whole `Id` equal to `⊤`.
   - Checked at its own generic call, `Cmp2(b)` is `False`.

`L2(y, refl)` therefore returns `False`. Switching off any one of `unitEta`, `globalRecords` or `genConsistent` rejects `F`.

Two rows the ledger calls *completeness* (G1 "a generalised neutral stays generalised", and D59 η for `Unit`) are needed for this proof of `False`. This is the methodological point of W3.

Fix: both (a) and (b) are needed at the level of the rules, and (c) is recommended.
- (a) Give a generalised value the type of the *neutral* as a term relative to the state before the arm's refinements, for example `⌈T(σ0)⌉` here and not `Box(Unit)`. Alternatively, key records by (program, type) and refuse to reuse one whose Δ is not convertible with the current place type.
- (b) Never type an observed place from its content. [Obs] should use stored or declared types. An untyped owner should be an error, or be typed by re-typing the sealed program (`sealedType`).
- (c) Let η for `Unit` fire only at a *declared* `Unit`.

Then add "the type at which each observed place is compared" as item (5) of @lem-stable, and add A1 and L1 as regression tests.

### W2 (major): the soundness story is conjectural, and the mechanisation covers none of the places where soundness has failed

- **What is proved.** Consistency (@cor-consistent), stability (@lem-stable) and naturality (property 9) are all conjectures. The mechanisation (@sec-meta-mech) covers v1.3's first-order fragment, with "no closures, types, inductive propositions or stuck blocks". That is exactly where every closed `False` in @fig-why lived, and where A1 lives.
- **Weight of the mechanised rows.** Several "mechanised" rows of @fig-claims are close to trivial:
  - Determinism of a definitional interpreter is `eval_det`, which is `exec_mono` plus a function.
  - `back_inj` and `ctx_inj` are injectivity of substituting for a loan that occurs, a few lines each.
  - These sit next to the substantial results (`frame_local`, `call_effect`, `close_*`, `exec_wf`) with no visual distinction.
- **The paper's own diagnosis.** It says the stability argument "is still an enumeration of the decisions we know of, and each earlier version of it missed one." A1 shows the current enumeration is still incomplete.
- **Consequence.** For POPL, a dependent type theory with a new equality and new neutral forms needs at least one proof of consistency or canonicity for a nontrivial core.
- **Fix, either of:**
  - Prove consistency (via the set model of §7) for a fragment containing closing off, `Id` and `Prop` erasure: first-order data, `&`, `Id`, `Prop` with `True`/`False`/`And`, no universes above `Type₀`, no type families.
  - Reframe the paper as a design with empirical validation, and move the consistency claim out of the contributions list.
- Also split @fig-claims into "substantive mechanised", "routine mechanised" and "conjectured".

### W3 (major): "principled or patched?" The principle is a rationalisation of a list, and the ledger cannot detect the failure mode that matters

- **The principle does not generate the rules.** "No decision that changes a result is read from a normal form" is a meta-principle, not a rule generator. @sec-typing-two applies it to a hand-written list of decisions. Several rules are not instances of it and are best read as patches motivated by specific counterexamples:
  - the head guard of [Seal];
  - global records with never-reused names (D37);
  - restoring the Δ of older values after an arm;
  - the canonical footprint order, needed because `∧` is not commutative by conversion;
  - confinement, described as "redundant … a fail-safe";
  - [Access] ending loans anywhere inside a neutral head;
  - non-cumulativity plus syntactic sorts, which restrict the language so that declared and computed sorts coincide;
  - the least-relation reading of [Conv-fun];
  - the injectivity relation R, a model-side patch for `'static`.
- **The ledger's blind spot.** The ledger switches each rule *off* and records which verdicts flip. That shows necessity. For a "completeness" rule, switching it off can only reject programs, so the ledger cannot reveal that the rule is *unsound when on*. A1 is exactly this case: G1 and D59 are completeness rows.
- **Moves.** The D53 move semantics now makes a new decision from the computed type: whether a read moves or copies ([Copy] versus [Read], "type_Ω(p) a copy type"). At a generic call, `x : T(n)` is not a copy type, while at an instance with `T(0) = Word` it is. The generic side is the conservative one, so this looks safe, but it is again a decision read from a normal form that the principle's list does not mention.
- **Fixes:**
  - Give each completeness extension the invariant it relies on. For example, η for `Unit` relies on "the type passed to `eq` is the type of both values".
  - Check those invariants as assertions in the checker.
  - Add a fuzzer or ledger mode that runs the attack corpus with each completeness rule on and each soundness rule's invariant monitored.

### W4 (major): it is unclear in what sense this is a type theory, and the usual metatheory properties fail or are not stated

- **Typing is symbolic execution.** The typing judgement `Ω ⊢ t ⇓ v : A ⊣ Ω'` is the machine run on abstract inputs. Types are values formed at a state. There is no declarative system of which the checker is an algorithm, and no substitution lemma, subject reduction or canonicity is stated.
- **`Id` depends on more than values.** Through owners, `Id` depends on the structure of the environment, not only on the values of its free variables.
- **Conversion is not stable under instantiation.** A2 shows that `Π(x : &Nat). False` and `Π(x : &Nat). Id Unit (*x := 0) (*x := 1)` are convertible: [Conv-pi] compares them at the generic state, where both codomains are `False`. Yet applying the two to the same argument `r = Pick(n, &a, &b)` gives `False` for one and, for the other, a conjunction of two `Eq Nat ⌈…⌉ ⌈…⌉` over `a` and `b`. The model rescues this through injectivity of contexts (property 6). Still, "convertible function types have convertible instances" is the property every kernel relies on, and here it is false.
- **Congruence is unstated.** Conversion also ignores constructor parameters (`Value.beq`), which the paper's [Conv-cong] does not say. And it is a congruence only relative to naturality, which is a conjecture.
- **Fixes:**
  - Give a declarative judgement, with the machine as its algorithm.
  - State which standard properties hold and which do not: substitution of values for abstract values, and stability of conversion under instantiation.
  - Otherwise, position Ochr as a dependently typed program logic by symbolic execution. Relate it to symbolic execution with separation logic (Berdine, Calcagno and O'Hearn), VeriFast and Gillian, and to relational Hoare type theory (see W9).

### W5 (major): the paper and the artifact disagree on rules that the model depends on

1. **Borrowing non-data.** [T-Borrow]'s premise "`type_Ω(p)` a data type" is not enforced for borrow *terms*; the check is made only when the type former `&A` is formed (A12). The checker accepts:
   - `&x` for `x : Prop` (`WP4`);
   - `&x` for `x : A` with `A : Type` (`WP7`);
   - `&A` for a type variable, then writing through it: `*r := Nat`, and `let b : *r = 5` (`BT`, `BT2`);
   - `Id Unit (let r = &A; *r := Nat) () ≡ Eq Type Nat A` (`BT6`);
   - `&f` for a function, with writes through it (`BF`);
   - `&h` for a proof (`P5`).

   A stuck block that captures such a place by `ref` then gets an anonymous function whose parameter type is `&Type₀` or `&⌈TP(σ)⌉` (`WP2`). This is exactly the "borrows only of data" model condition of @fig-why and §7. I found no `False` through it, because the user cannot name that Π-type. But the model's interpretation of the Fin component, and its claim that `&T` lives in `Type₀`, do not cover these programs.
2. **Closures in data.** §4.4 says a closure "cannot be an inductive field or be borrowed". But `Box(Π(n : Nat). Nat)`, `&Box(Π(n : Nat). Nat)` and `&Box(Π(y : &Nat). &Nat)` are accepted, because type parameters admit Π-types. Ochr then proves injectivity for *boxed* borrow-returning functions (A11, `QF7`). Definition 1 sets R_A = ⟦A⟧ for "base types", which includes `Box(…)`, so the model sketch as written validates boxes of non-injective functions and falsifies `QF7`. R must be defined semantically, through parameters and type variables.
3. **Universes.** The paper's grammar has `Type_i` for all `i`, but the checker's surface syntax has only `Prop` and `Type` (`Type₀`); `Type₁` appears only as the type of `Type`. Nothing above `Type₀` has been exercised.
4. **Built-in names.** The paper presents `Nat` and `Unit` as library declarations. In the checker they are built in, and a user may declare another `Nat` or `Unit` (A14). The result is diagnostics like "the body of k has type Nat, but the goal is Nat". η for `Unit` keys on the built-in, so this is not unsound, but it contradicts the claim that the checker is a faithful reference.
5. **Printed programs versus tested programs.** `SizeInsert` and `InsertFindOther` are printed with `Nat` keys; the tested versions use `Word`. At `d964b73a` the two case studies are also checked under *different* semantics: the hash map with moves, and the array library and quicksort with copies (@fig-sizes caption).

Fix: enforce [T-Borrow]'s data premise, or state the relaxed rule and extend the model. Forbid Π-types as inductive parameters, or extend R. Reject redeclaration of built-in names. Make the paper say "every printed program, modulo `Nat`→`Word` keys, is tested".

### W6 (moderate): the model sketch leaves out the hard parts

The following are not addressed:
- the interpretation of `Id`, whose footprint and owners depend on the environment;
- type-returning functions with effects, which are discarded when erased;
- sealed programs, whose denotation needs termination of [Seal] runs; that termination is property 3 and is itself partial;
- the gap between the view/resolution semantics and [Access]'s eager ending of loans inside neutral heads.

"Convertible types denote the same set" rests on [Conv-fun], which rests on naturality, and naturality is only a conjecture. So even the sketch is conditional on the hardest conjecture.

Fix: write out the model clauses for `Id`, for [Close] with holes, and for [Conv-fun]. Say exactly which conjecture each case uses.

### W7 (moderate): non-modularity limits scalability, and the evaluation does not measure it

- **Unfolding.** Conversion unfolds callees. "Extracting a helper can change which equations hold by `refl`" (§5), and opaque definitions are axioms (§9).
- **Borrow checking.** Whether a caller checks depends on the callee's body and on how concrete its inputs are (§1.5).
- **Consequence.** Proof stability under refactoring, proof re-checking cost and the growth of normal forms are therefore first-order concerns, but the evaluation reports only total check times (about 0.2 s).
- **Fix:** report the size of goals, meaning the number of sealed programs and their depth, for the hash map's largest lemmas. Show one refactoring, such as extracting a helper, and what it breaks. Say what a "check once, then seal" mechanism would require.

### W8 (moderate): the evaluation's headline numbers flatter the approach

- **Lines versus tokens.** The abstract leads with "a third shorter in lines". In tokens the development is only 11% smaller, and the property proofs are 1.26× Aeneas's. Lines depend on formatting.
- **A simpler program.** The Ochr hash map differs from Aeneas's in five ways, and each removes proof obligations:
  - numbers are unbounded;
  - the table is a list, not an array, with indexing that saturates instead of needing a bounds proof;
  - the load factor is fixed at one;
  - values are `Nat`, not generic;
  - `GetMut` takes a proof that the key is present.

  The paper estimates about 9% of Aeneas's lines for overflow and failure cases. It does not estimate what the other simplifications save.
- **Quicksort.** It is 8× the lines and 13× the tokens of Verus's version.
- **Fixes:**
  - Lead with tokens.
  - Add a row for Aeneas's development with overflow and failure removed, or an Ochr version with bounded words and array-backed slots.
  - Move "1.26× longer proofs" into the abstract next to "a third shorter".
  - Check both case studies under the same semantics.

### W9 (moderate): related work is missing close neighbours

- **Relational reasoning about effectful programs inside dependent type theory.** Relational Hoare Type Theory (Nanevski, Banerjee and Garg). This is the closest prior work to "`Id` compares two computations".
- **The program as its own specification, by unfolding.**
  - Liquid Haskell's refinement reflection (Vazou et al., POPL 2018).
  - Dafny's function-by-method and two-state lemmas, where specifications call functions and mention `old` state.
  - Why3's region-based alias control for deductive verification of mutable data (Filliâtre, Gondelman and Paskevich).
- **Local mutation in a pure prover.** Lean 4's `do` notation with mutable variables, compiled to pure code (Ullrich and de Moura, "do unchained", 2022).
- **CBPV-style dependent types with effects.** Vákár's dependently typed CBPV, alongside eMLTT and ∂CBPV.
- **Backward functions as lenses.** The bidirectional-transformation literature (Foster et al.).
- **Symbolic execution as proof checking.** Symbolic execution with separation logic (Berdine, Calcagno and O'Hearn).
- **Characteristic formulae.** CFML (Charguéraud): imperative code reasoned about in Coq without a separate model.
- **Relational compilation from functional to imperative code.** Rupicola (Pit-Claudel et al., PLDI 2022).
- **Ownership and uniqueness in a functional language.** Granule's fractional uniqueness (Marshall and Orchard, 2024).

### W10 (moderate): the fuzzer's evidence covers little of the paper's central mechanism

The generator (`Ochr/Fuzz/Gen*.lean`, `Case.lean`) checks generated `Id` statements at the generic call against instances. From my reading of the generator, it does not produce:
- recursive *proofs* whose induction hypothesis is typed at the call site, which is the paper's central idea;
- `rewrite` or `split` forms;
- user inductives with type parameters instantiated at Π-types, `Prop` or types;
- abstract function parameters whose Π-type depends on an earlier parameter and is refined in several arms, which is A1's shape.

The `escape` findings dismissed as "harmless imprecisions of scope" show values local to one arm flowing into the continuation through the arm's type (in my run: a block's Π-typed codomain that captured `(σ3, σ4)` from the `Mk` arm). That is the same family of leak as A1.

Fix: extend the generator along these axes, and re-triage `escape` findings against A1.

### W11 (minor): the title overclaims

- **Compiled code.** The relation between the checked machine and compiled code is an assumption (§9). Erased terms read through ghosts, and the move semantics was "unsound before it was turned on" (§7.2).
- **Coverage.** Loops, shared borrows, borrows in data and generic `&A` are all absent.
- **Fix:** "Proving the program you run" should be tempered, for example with "for a core of safe Rust with mutable borrows".

### W12 (minor): decidability and fuel

Termination of type checking is open. The checker bounds depth and fuel ("out of fuel", "normalisation depth exceeded"), so some rejections may be timeouts. Report whether any verdict in the suite or the case studies depends on the bounds.

## 4. Attempted attacks and outcomes

All programs are `ochr` blocks, checked with `run "<Block>" <Block>` under the default `Config` at `c49e4f36` and `d964b73a`. `uses Std` supplies `Box(A) := MkBox(x : A)`, `Bool := false | true`, `AddM` and `TailM`; `uses Fixtures` supplies `Pick`. Every probe was written as a `def`, meaning "expect accept", so a rejection means the attack failed.

### A1: closed proof of `False` (ACCEPTED, a soundness bug; see W1)

```
ochr Leak1 uses Std {
  def T (n : Nat) : Type := match n { Z => Box(Unit), S _ => Box(Bool) }
  def Cmp2 (b : Box(Bool)) : Prop := (let c = b; Id Unit (c := MkBox(true)) (c := MkBox(false)))
  def L2 (b : Box(Bool)) (h : Cmp2(b)) : False := h
  def G (n : Nat) : Prop := match n { Z => ⊤, S _ => False }
  def F (n : Nat) (g : Π(u : Unit). T(n)) : G(n) := (
    match n {
      Z => (let x = g(()); match x { MkBox(v) => refl }),
      S _ => (let y = g(()); L2(y, refl)),
    }
  )
  def Boom : False := F(1, λ(u : Unit) : T(1) => MkBox(true))
}
```
All six declarations are accepted.

Trace of `F`:
```
[Split] σ0 := 0
[Call-type] σ2(()) : Box(Unit)
[Split] generalise ⌈σ2(())⌉ to σ3 : Box(Unit)
[Split] σ0 := S σ5
[Call-type] σ2(()) : Box(Bool)
[Call-type] Cmp2(σ3) : Prop
[Def] F: path ends with type False against goal False
```
With `{ unitEta := false }`, `{ globalRecords := false }` or `{ genConsistent := false }`, `F` is rejected with "argument 2 (h) has type ⊤, expected False".

### L1: the Δ leak on its own (accepted; it demonstrates step 2 of A1)

```
ochr L1 uses Std {
  def T (n : Nat) : Type := match n { Z => Nat, S _ => Bool }
  def F (n : Nat) (g : Π(u : Unit). T(n)) : Nat := (
    match n {
      Z => (let x = g(()); match x { Z => 0, S _ => 1 }),
      S _ => (let y = g(()); match y { false => 2, true => 3 }),
    })
}
```
In the trace, one abstract value σ3 with Δ(σ3) = Nat is split as `σ3 := 0` / `σ3 := S σ4` in the `Z` arm and as `σ3 := false` / `σ3 := true` in the `S` arm.

### A2: conversion is not stable under instantiation (both accepted; no `False`)

```
ochr CP uses Std, Fixtures {
  def CP (h : Π(x : &Nat). False) : (Π(x : &Nat). Id Unit (*x := 0) (*x := 1)) := h
  def CPuse (h : Π(x : &Nat). Id Unit (*x := 0) (*x := 1)) (n : Nat) (a : Nat) (b : Nat) : False := (
    let r = Pick(n, &a, &b); h(r))
  def CPuse2 (h : Π(x : &Nat). False) (n : Nat) (a : Nat) (b : Nat) : False := (
    let r = Pick(n, &a, &b); h(r))
}
```
`CP` and `CPuse2` are accepted. `CPuse` is rejected: `h(r)` has type `(Eq Nat ⌈…*r := 0; c1⌉ ⌈…*r := 1; c1⌉) ∧ (Eq Nat ⌈…; c2⌉ ⌈…; c2⌉)`. So two convertible Π-types give different types when applied to the same argument (W4).

### A3: η for `Unit` through a user-declared `Unit` (rejected; safe)

```
ochr A3 { inductive Unit := A | B
          def H2 (x : Unit) (y : Unit) : Eq Unit x y := refl }
```
`Unit` is accepted. `H2` is rejected: "the body has type ⊤, but the goal is Eq Unit σ0 σ1". The accepted redeclaration is the papercut of W5.4.

### A4: getting data out of a non-subsingleton proof (all rejected)

```
ochr A4 {
  inductive Ex : Prop := Wit(n : Nat)
  def Get (h : Ex) : Nat := h.1                                           -- "no sub-place at type Ex"
  def Get2 (h : Ex) : Nat := match h { Wit(n) => n }                      -- D45
  def Q1 (h : Ex) : (match h { Wit(n) => Eq Nat n 0 }) := refl            -- D45
  def Q2 (h : Ex) (k : match h { Wit(n) => Eq Nat n 0 }) : False := k     -- D45
  def Q3 (h : Ex) : Nat := (let k : (match h { Wit(n) => Eq Nat n n }) = refl; 0)   -- D45
  def Q4 (h : Ex) : Id Nat (match h { Wit(n) => n }) 0 := refl            -- D45
  def Q5 (h : Ex) : Eq Nat (match h { Wit(n) => n }) 0 := refl            -- D45
  def Q6 (h : Ex) : Id Prop (match h { Wit(n) => Eq Nat n 0 }) False := refl        -- D45
}
```
`UseEx (h : Ex) : ⊤ := match h { Wit(n) => match n { Z => refl, S _ => refl } }` is accepted, correctly.

### A6: universes, positivity, recursion in types, and borrow-returning Π inside a parameter (all rejected except the benign ones)

```
ochr A6 uses Std {
  def BoxT : Type := Box(Type)            -- rejected: parameter has type Type_1
  def BoxTrue : Type := Box(⊤)            -- rejected: parameter has type Prop
  def BoxP : Type := Box(Prop)            -- accepted (fine: Prop : Type₀)
  inductive Void : Type
  def Neg (X : Type) : Type := (Π(x : X). Void)
  inductive Bad := MkBad(f : Neg(Bad))                   -- rejected, D36
  inductive Bad2 := MkBad2(f : Box(Neg(Bad2)))           -- rejected, D36
  inductive Bad3 := MkBad3(f : Box(Π(x : Bad3). Void))   -- rejected, D36
  def F (n : Nat) : Nat by n := (let e : Eq Nat (F(n)) (F(n)) = refl; 0)   -- rejected, [Rec]
  def BadBox : Type := Box(Π(u : Unit). &Nat)            -- rejected, D44
}
```
Also `def G (n : Nat) : Nat := (let e : Eq Nat (G(n)) (G(n)) = refl; 0)` is rejected (D31), and `Type 1` does not parse in the checker (W5.3).

### A9: zero-arm matches (all rejected except the empty data type)

```
ochr A9 uses Std {
  inductive Void : Type
  inductive Or (P : Prop) (Q : Prop) : Prop := Inl(p : P) | Inr(q : Q)
  def FromVoid (v : Void) : Nat := match v {}                          -- accepted (fine)
  def ZeroTrue (h : ⊤) : False := match h {}                           -- rejected
  def ZeroOr (h : Or(⊤, ⊤)) : False := match h {}                      -- rejected
  def ZeroAnd (h : ⊤ ∧ ⊤) : False := match h {}                        -- rejected
  def ZeroEq (x : Nat) (h : Eq Nat x x) : False := match h {}          -- rejected
  def ZeroEqAbs (x : Nat) (y : Nat) (h : Eq Nat x y) : False := match h {}   -- rejected
  def ZeroNat (n : Nat) : False := match n {}                          -- rejected
  def ZeroUnit (u : Unit) : False := match u {}                        -- rejected
  def ZeroAndF (h : ⊤ ∧ False) : False := match h {}                   -- rejected (incomplete, safe)
  def ZeroId (x : &Nat) (h : Id Unit (*x := 0) (*x := 0)) : False := match h {}   -- rejected
}
```

### A10 and A11: injectivity of borrow-returning functions, including boxed ones (accepted; a model gap, W5.2)

```
ochr B1 uses Std {
  def PF (x : &Nat) (e : Id Unit (*x := 0) (*x := 1)) : False := e
  def QF5 (g : Π(y : &Nat). &Nat) (x : &Nat) (e : Id Unit (let r = g(x); *r := 0) (let r = g(x); *r := 1)) : False := e
      -- rejected: at the generic call the Id is Eq Nat ⌈…0…⌉ ⌈…1…⌉, not False
  def QF6 (g : Π(y : &Nat). &Nat) (a : Nat)
      (e : Eq Nat (let c = a; let r = g(&c); *r := 0; c) (let c = a; let r = g(&c); *r := 1; c)) : False := (
    let r = g(&a); PF(r, e))                                     -- accepted: "R is forced"
  def QF7 (b : Box(Π(y : &Nat). &Nat)) (a : Nat)
      (e : Eq Nat (match b { MkBox(g) => (let c = a; let r = g(&c); *r := 0; c) })
                  (match b { MkBox(g) => (let c = a; let r = g(&c); *r := 1; c) })) : False := (
    match b { MkBox(g) => (let r = g(&a); PF(r, e)) })           -- accepted: R must reach inside Box
}
```
Writing `PF(g(&a), e)` directly is rejected by D41 ("an erased term borrows a"). The let-bound form above is accepted.

### A12: borrows of non-data at the term level (accepted; a rule/implementation mismatch; no `False` found; W5.1)

```
ochr A12 uses Std {
  def TP (n : Nat) : Type := match n { Z => Prop, S _ => Nat }
  def WP2 (n : Nat) (x : TP(n)) : Nat := (match n { Z => (let r = &x; ()), S _ => () }; 0)   -- accepted
  def WP4 (x : Prop) : Unit := (let r = &x; ())                                    -- accepted
  def WP7 (A : Type) (x : A) : Unit := (let r = &x; ())                            -- accepted
  def BT (A : Type) : Unit := (let r = &A; *r := Nat)                              -- accepted
  def BT2 (A : Type) (a : A) : Nat := (let r = &A; *r := Nat; let b : *r = 5; b)   -- accepted
  def BT6 (A : Type) (e : Id Unit (let r = &A; *r := Nat) ()) : Eq Type Nat A := e -- accepted
  def BF (f : Π(n : Nat). Nat) : Nat := (let r = &f; *r := (λ(n : Nat) : Nat => 0); f(3))   -- accepted
  def P5 (P : Prop) (h : P) : Unit := (let r = &h; ())                             -- accepted
  def RefP (x : &Prop) : Unit := ()                                                -- rejected (D48): only the type former is checked
  def BorrowBoxF (x : &Box(Π(n : Nat). Nat)) : Unit := ()                          -- accepted
}
```
In the same family, `W (n : Nat) (x : T(n)) : Nat := (match n { Z => (x := 5), S _ => () }; 0)` with `T(Z) = Nat` is accepted. Its stuck block's parameter is typed `&⌈T(σ)⌉`.

### A13: borrows stored in data (all rejected)

```
ochr S3 uses Std {
  def P1 (x : &Nat) (y : &Nat) : Unit := (let p = (x, y); ())       -- rejected
  def P2 (x : Nat) : Unit := (let b = MkBox(&x); ())                -- rejected
  def P3 (x : &Nat) : Unit := (let b = MkBox(x); ())                -- rejected
  def P6 (x : Nat) : Unit := (let b : Box(Nat) = MkBox(&x); ())     -- rejected
}
```

### A14: shadowing built-ins (declarations accepted; confusing diagnostics; not unsound)

```
ochr N1 { inductive Nat := Zero | One
          def k : Nat := 5 }       -- "the body of k has type Nat, but the goal is Nat"
```

### Attacks considered and not pursued, because I believe they are sound

These were reasoned through, not run:
- `rewrite` with an `h` whose endpoints are equal in the model but not syntactically. The rewritten goal is Leibniz-equivalent, and `h : Eq Unit σ ()` computes to `⊤`, so there is nothing to rewrite.
- `J` over endpoints that are convertible by [Conv-fun] but have different code. Soundness then reduces to naturality.
- A `split` target with a borrow-returning, proof-returning or type-returning head. The target's type is read from a closed codomain, and the checker rejects a borrow-row fill.
- Stuck blocks whose arms end or move borrows. [Access] at block formation is the more conservative path.
- Aliasing at call sites of lemmas with two borrow parameters. It is prevented by exclusivity; only the order of conjuncts can differ, which causes rejections.

### Fuzzer

With seed 4242, 200,000 cases took 226 s. There were no `nat`, `false`, `verdict` or `exec` findings. The 10 `escape` findings (first: case 44) are a stuck block whose anonymous function's codomain captured `(σ3, σ4)` from its `Mk` arm; see W10. The 5,614 adequacy findings are all "vacuous: stuck (escaped to the top)".

## 5. Questions for the authors

1. What should Δ(σ) be for a generalisation made in one arm and re-derived in another, where the neutral's text is the same but its type differs (A1, L1)? Should records be keyed by text alone?
2. Is there a declarative typing judgement of which `checkFix`/`eval true` is an algorithm? If not, what exactly is the consistency conjecture a statement about: accepted programs, or derivations?
3. Is conversion transitive, and is it a congruence? [Conv-fun] requires captured values to be pairwise convertible; `Value.beq` ignores constructor parameters. Given A2, what property of conversion does the stability argument actually use?
4. In the model, is `⟦Id A t u⟧` a function of the values of `Id`'s free variables, or of the whole view including owners? If it is of the view, how is `Π(x : &Nat). Id …` interpreted uniformly across call sites?
5. How is R (Definition 1) defined at inductive types whose parameters are Π-types (A11), and at type variables?
6. Is [T-Borrow]'s data premise meant to hold for terms (A12)? If it is relaxed, how does the model interpret the Fin component of a stuck block that captures a place of type `Type₀` by `ref`?
7. For the fire triangle: which of Pédrot and Tabareau's hypotheses exactly fails for Ochr? Do closed data terms enjoy canonicity? A closed stuck `⌈IsL(⋆)⌉` is ruled out by subsingleton elimination, but zero-arm matches and `J` can be stuck in open runs; can any closed data term be stuck?
8. Why η for `Unit` only, and not for other single-constructor types or for records? Which invariant does the η rule assume about the type passed to `eq`, and where is that invariant enforced?
9. Do any verdicts in the suite or the case studies depend on the fuel or depth bounds?
10. Why are the two case studies checked under different read semantics at `d964b73a`? What breaks in the array library under moves?

## 6. What to cut or compress, towards a self-contained "diamond"

- **Move the core idea forward.** Put the two-paths principle (@sec-typing-two) in the introduction, as the paper's central technical difficulty. At present the reader meets it only in §6.
- **Define terms before use.** Define *owners* and *footprint* before §2's `AddMZero` derivation uses them. Bring *declared type*, *class* and *copy type* out of the appendix and into §3.
- **Cut from the body:**
  - "What the programmer sees" in §9;
  - the `Pick` naturality example (keep one sentence);
  - "Stuck, never ill-typed" (move it to the appendix);
  - half of the related-work paragraph on Rust foundations;
  - the long prose on hash-map coverage (a table suffices).
- **Compress @fig-why.** Reduce it to one line per principle, with the counterexample programs referenced in the appendix notes, which already hold most of them.
- **Tidy @fig-claims.** Separate trivial mechanised facts from substantive ones.
- **Cut terminology.** At least a third of these would go in a diamond version: sealed program, hole, inert loan, private copy, confined, class, row, generic call, head call, footprint, owners, observation, resolution, view, refinement versus generalisation, ghost, copy type.
- **Use one semantics.** Give the case studies under one semantics, and drop the "first version" rows of @fig-sizes; they belong in an artifact appendix.

## 7. Score and confidence

- **Score:** Reject.
- **Confidence:** High (4/5) on the type theory and metatheory, medium on the Rust side.

The idea is original and worth publishing eventually. The writing is candid, and the artifact is unusually disciplined. But:
- the central claims (consistency, stability, naturality) are conjectures;
- the mechanisation covers none of the places where soundness has failed;
- the final artifact still accepts a closed proof of `False` (A1), through a decision that the paper's own enumeration of decisions misses.

**What would move my score up one notch (to weak reject or borderline):**
- A1 fixed at the level of the rules, as in W1 (a)–(c).
- The stability conjecture restated with the missing decision, together with an argument, not an enumeration, for why the list of decisions is now complete. The best such argument is a proof for a core fragment: first-order data, `&`, closing off, `Id`, and `Prop` with `True`/`False`/`And`. The paper's own set model would serve.
- The paper/artifact mismatches of W5 resolved.

A mechanised consistency proof for that fragment would move me to accept.
