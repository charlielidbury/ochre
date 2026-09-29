# Review 4: "Proving the Program You Run" (Ochr)

Reviewer background: dependent type theory and proof-assistant kernels (Lean, Coq/Rocq, Agda), observational type theory, NbE, models of type theory, effects in type theory. I read the whole paper (body and appendix) cold, from the typst sources and `main.pdf`. I used the artifact as a reviewer with artifact access would: I built the checker and ran attack programs through it (in a scratch copy, nothing committed to the artifact), and I built the mechanisation and checked its axioms. I did not read the authors' internal logs.

Versions tested: the checker as it stood with the submitted paper (commit `0127f58b`) and the current branch head (`b323d5ef`). Every result below reproduces on both. To check whether the artifact had moved during the review, I looked at one-line commit subjects on the branch; I did not read the commits, the notes or the logs.

## 1. Summary

The paper presents Ochr, a Lean-style dependent type theory with Rust-style mutable borrows, in which definitional equality is running a deterministic borrow machine (after Aeneas's symbolic semantics) on symbolic inputs. A call that gets stuck on an unknown value is "closed off": its result and the final contents of the places it borrowed become *sealed programs*. These are closed source programs that compute what Aeneas's backward functions would, and they re-run when a later case split refines their inputs. An observational `Id A t u` compares two computations by their result and the final contents of the places they may write, and reduces to `Eq` between tuples. Because an induction hypothesis's type is computed in the caller's environment, the borrow structure supplies congruence steps, so in-place lemmas such as `AddMZero` are bare structural recursion. Evidence: a Lean checker with a counterfactual ledger, a mechanisation of a first-order fragment of an earlier rule set, and conjectures (with sketches) for stability, adequacy and consistency.

## 2. Strengths

- **A genuinely new idea.** Computing Aeneas's backward functions lazily, inside conversion and in source syntax, is new. Sealed programs are a clean neutral form for stuck effectful calls. Holes for returned borrows (loans bound by a borrow, substituted at [End]) are a nice internal account of prophecies and region abstractions, and the `TailM`/`AddM'` example shows the idea covers more than the trivial case.
- **The induction-hypothesis-at-the-call-site observation is elegant.** The `AddMZero` derivation in §2 is the best part of the paper: the goal and the induction hypothesis are two instances of one rule, [Call-type], and the successor comes from the environment. The "borrowing supplies congruence, copying withholds it" remark (`AddSubId`) is a real insight about reasoning with borrows.
- **`Id` reduced to `Eq` over observations**, with owner sets and all-owners observation, is a simple and mostly principled design. The `Pick` example shows why all owners must be observed.
- **An honest status table** (Fig. "What Ochr is meant to satisfy"): it separates what is mechanised, partly mechanised and conjectured. The mechanisation builds, has one `sorry` (`termination`), and the named theorems use only `propext`, `Classical.choice` and `Quot.sound` (I checked with `#print axioms`).
- **The executable checker and the counterfactual ledger** are good methodology. Tying every side condition to a regression and recording what switching it off lets in is more than most submissions of this kind provide, and the rule-to-function mapping in the appendix made the artifact easy to audit.
- The sentence-level writing is clear, and the running examples are well chosen.

## 3. Weaknesses, ranked by severity

### W1 (critical). The checker accepts a closed proof of `False`, and the cause is in the rules, not only in the code

The following block is accepted by the checker (`run` with the default `Config`), at both commits:

```
ochr Attack {
  def P (n : Nat) : Type := match n { Z => Prop, S _ => Prop }
  def T (n : Nat) : P(n) := match n { Z => ⊤, S _ => ⊤ }
  def W (u : Unit) : T(Z) := refl
  def f (x : &Nat) : T(Z) := (*x := S Z; W(()))
  def RunK (k : Π(x : &Nat). ⊤) (x : &Nat) : Unit := (k(x); ())
  def Stmt (k : Π(x : &Nat). ⊤) (x : &Nat) : Id Unit (RunK(k, x)) () := refl
  def Boom : False := (let c = 0; Stmt(f, &c))
}
```

How it works (confirmed with the checker's trace):

1. `T(Z)` computes to `⊤`, but its *declared sort* (§6, app. "Erasure") is not `Prop`, because `T`'s codomain term `P(n)` is not syntactically a sort. So `f` is classed as returning data: its calls are not erased, and it really writes `S Z`.
2. [Conv-pi] compares codomains *after evaluation*, so `Π(x : &Nat). T(Z) ≡ Π(x : &Nat). ⊤` (the checker accepts `Eq Prop (Π(x : &Nat). T(Z)) (Π(x : &Nat). ⊤)` by `refl`). So `f` may be passed where a function *into a declared proposition* is expected.
3. At `Stmt`'s generic call, `k` is a proof parameter, so it is bound to `⋆`. `RunK(⋆, x)` does nothing, and the goal is `⊤`.
4. At the instance `Stmt(f, &c)`, [Call-type] binds `k ↦ f`. The call `RunK(k, x)` runs `RunK`'s body in the machine, which calls `f` by *`f`'s own* class (data) and writes `c := 1`. The statement becomes `Eq Nat 1 0`, which is `False`.

Two more closed proofs of `False` exploit the same seam through different doors:

```
  def RunGen (k : Π(x : &Nat). ⊤) : Id Nat (let c = 0; RunK(k, &c); c) 0 := refl
  def Boom2 : False := RunGen(f)                      -- accepted
  def RunIs : Id Nat (let c = 0; RunK(f, &c); c) 1 := refl   -- also accepted: the same term, two values

  def Lie4 (n : Nat) : Id Nat (let c = Z; match n {
      Z => (let q : (Π(x : &Nat). ⊤) = f; q(&c); ()),
      S _ => (let q : (Π(x : &Nat). ⊤) = f; q(&c); ()) }; c) 1 := match n { Z => refl, S _ => refl }
  def Boom4 : False := Lie4(0)                        -- accepted
```

`Boom4` uses only core syntax (an annotated `let`). The typing judgement erases the bound term of `let q : A = f` because `A` is a declared proposition (appendix erasure clause 4, last item). The machine does not, so the sealed program re-run under `n := Z` writes `c`, while the direct evaluation at the instance does not.

**Why this is a paper-level problem, not just a bug.** The paper's central safety argument is "every decision the two paths must agree on is made from syntax" (§1.3, §6 "Why each condition is there", Conjecture *stability*). But Ochr has two notions of "is a proposition": the *declared* sort (used for erasure, proof flags and [Close]'s row) and the *computed* sort (used by [Conv-pi], by the sort of a Π-type, and, per appendix item 10, by the generic call: "if `T_i` has sort Prop, let `a_i = ⋆`"). Conversion moves values between types whose declared classes differ, so a binding declared to hold a proof can hold a live, effectful function. Stability is stated only under *refinement* α. It must also hold under *conversion*, and it does not. The appendix is also underspecified at exactly the point that matters: the [App] frame `φ = κ̄, [f ↦ F], x̄ ↦ w̄` carries no proof flags, [Call-type]'s frame does not say whether flags are set, and no rule says what calling `⋆` means. The checker's reading of these gaps is unsound. Under the other reading, the attack might be blocked, but the invariant "every proof value is ⋆" still fails (see W2).

**Fix.** Make relevance a property of the type, not an after-the-fact syntactic classification of terms: put an erasure/relevance mark on Π binders and codomains (as Agda's irrelevance annotations, Coq's binder relevance marks for `SProp` [Gilbert et al. 2019], or QTT's 0/ω), and make [Conv-pi] compare the marks. Then prove, as a lemma rather than a conjecture, that the declared class of a type term equals the class of its value, or make the sort *be* the declared class (so `Π(x : &Nat). T(Z)` lives in `Type₀`). Erase arguments at proof-parameter positions to `⋆` in both judgements, and give [App] frames flags. Add `Boom`, `Boom2` and `Boom4` to the suite.

### W2 (major). The model sketch's key simplification is false as the rules stand

§7 says: "Carneiro needs unique typing to decide whether a λ or Π denotes a proof or a set-theoretic function; in Ochr that decision is syntactic, so the interpretation can be defined by recursion on derivations". The checker accepts all of:

```
  def TT : Prop := Π(x : &Nat). T(Z)
  def g2 (x : &Nat) : T(Z) := W(())
  def k (h : Π(x : &Nat). T(Z)) : Nat := (let c = Z; h(&c); c)
  def K1 : Eq Nat (k(f)) 1 := refl
  def K2 : Eq Nat (k(g2)) 0 := refl
```

So `TT` has sort `Prop` but two inhabitants that a data-valued function tells apart. In the sketched model, a type in `Prop` "denotes a subsingleton", and "a proposition has no Fin component, because proofs run on a private copy". Neither holds for `TT`: `f` is a member of a proposition whose calls have effects, so `K1` and `K2` cannot both be true in the model. The model sketch is the paper's only consistency story. It needs the same repair as W1 (a single notion of proposition). As written, the conjecture of consistency is not supported by the sketch.

### W3 (major). What is proved does not reach the typed calculus, and the abstract under-signals this

- The mechanisation covers "version 1.3 of the rules, which predates the erasure and inductive-proposition rules of §6", first-order, with no types, closures or stuck blocks (§7.3). The abstract and contributions say "a mechanised proof, for a first-order fragment, that a call affects only what it is passed and that sealed programs compute Aeneas's backward functions" without "of an earlier version of the rules". Every counterexample in Fig. `fig-why`, and the attack above, lives in the part that is *not* mechanised (erasure, classification, conversion).
- Property 6 ("a backward function is injective, and so is the caller's context") is mechanised as injectivity of *syntactic loan substitution* (`Val.substLoan_inj`, `back_inj`, `ctx_inj`). That is immediate. What [Call-type] needs for hypotheses in negative position is injectivity of the *denotation* of contexts that include sealed programs with holes (for example `⌈L; let r = C; *r := loan_k; c⌉`). That is not addressed.
- Stability, naturality/adequacy and consistency are conjectures. Termination is `sorry` in general.

**Fix.** State the version gap in the abstract and contributions. Mechanise the one lemma that the paper says most soundness hinges on: stability of every syntactic decision, under both refinement *and conversion*. It is a syntactic lemma and very mechanisable, and it would have found W1. Restate property 6 as what is actually proved.

### W4 (major). Decidability is not open: `J` reduces without looking at its proof, which is equality reflection for open terms

The appendix says `J(A, a, b, P, h, t)` "returns the value of `t` unchanged", with no condition on `h` or on `a ≡ b`. That is strictly stronger than Lean's K-like rule, which fires only when the endpoints are convertible. Under an absurd hypothesis it yields untyped λ-calculus inside the type checker:

```
  def C1 (h : Eq Type (Nat → Nat) ((Nat → Nat) → Nat)) (x : Nat → Nat) : ((Nat → Nat) → Nat) :=
    J(Type, Nat → Nat, (Nat → Nat) → Nat, (λ(X : Type) : Type => X), h, x)
  def C2 (h : Eq Type ((Nat → Nat) → Nat) (Nat → Nat)) (f : (Nat → Nat) → Nat) : (Nat → Nat) :=
    J(Type, (Nat → Nat) → Nat, Nat → Nat, (λ(X : Type) : Type => X), h, f)
  def Om (h1 : …) (h2 : …) : Nat := (let f = (λ(x : Nat → Nat) : Nat => (C1(h1, x))(x)); f(C2(h2, f)))
```

The checker reports "call depth exceeded (a non-terminating recursion)" on `Om`. Lean would accept `Om`, because its cast is stuck. Under the rules as written (no fuel), checking diverges. A related symptom: `CastMatch (h : Eq Type Nat Bool) : Nat := (let b = J(…, h, 5); match b { false => 0, true => 1 })` is rejected with "[Match] on 5, which is not a value of Bool". Well-formedness condition 6 ("values have their types") is not preserved in open terms, which property 2 does not cover (it mechanises conditions 1–5 only).

The paper says (§7) "whether type checking is decidable is also open ... Abel and Coquand". It is not open for the rules as stated, and the reason is much more elementary than Abel–Coquand.

**Fix.** Make `J` reduce only when `a ≡ b` (and otherwise close it off as a neutral that still runs `t` for its effects), or state plainly that conversion is undecidable. Cite Gilbert, Cockx, Sozeau and Tabareau, "Definitional proof-irrelevance without K" (POPL 2019), and Pujet and Tabareau, "Impredicative observational equality" (POPL 2023), which analyse exactly this design space (definitional proof irrelevance, observational `Eq`, reducing casts, impredicative `Prop`).

### W5 (major). The calculus reads as a pile of patches around two evaluators

The typing judgement and the machine are presented as one ("each rule below performs the step of the machine rule of the same name"), but they are two evaluators that must agree, and most of the design is machinery to keep them in agreement:

- 14 side conditions (Fig. `fig-why`), each added after a counterexample;
- a ten-part definition of "declared proof" (app. erasure clause 4);
- a "confinement" rule that the paper itself calls redundant for correctly classified terms ("a partial fail-safe");
- non-cumulative universes adopted for erasure stability;
- three [Close] rows keyed on the declared codomain, with `Unit` special-cased because there is no η for `Unit` (note 15);
- unit laws that hold in conversion but not in stored types;
- stuck-block capture modes modelled on Rust closure inference;
- a head guard with a separate case for neutral heads;
- and, most worrying for a type theorist, *global mutable state in the typing judgement*: generalisation records that survive private copies, plus a "fresh names are never reused" discipline. That makes typing non-compositional. It sits badly with "the interpretation can be defined by recursion on derivations", since a derivation's meaning depends on what earlier private copies recorded.

The paper's own summary, "every side condition in it is there because a smaller one admitted a proof of false", argues each condition is necessary. It does not argue the set is sufficient or principled. The ledger shows "each rule is needed for some verdict, not that the rules suffice" (§8), and W1 is a case the ledger did not anticipate.

**Fix.** Identify the one invariant that the conditions protect: relevance is part of the type (W1), and the machine and the typing judgement agree on relevance. Derive the conditions from it, and replace confinement by a theorem. Add η for `Unit` (and unit-like records), which deletes the `Unit` row and note 15. Say how generalisation records would appear in a derivation-indexed model.

### W6 (moderate). Claims that the evidence does not support

- "Ochr keeps its two paths synchronised by making every decision they must agree on ... from syntax rather than from normal forms" (§1.3). Conversion is not syntax (W1).
- "The typing judgement ... is the machine with types" (app. "Typing"). In the artifact, the typing judgement erases the bound term of a `let` with a declared-proposition annotation and treats calls through proof-flagged parameters as erased. The machine does neither (`RunIs`, and the `Lie4` pair). Either the artifact deviates from the rules or the rules are underspecified; the paper should say which.
- "Equations between an in-place function and another computation are then proved by plain structural recursion" (abstract). The BST size theorem needs `J` with hand-written motives and an arithmetic lemma (§2, "Trees"). The abstract should say "in-place equations of the shown kind".
- "Nothing in a goal mentions loans, borrows, environments or backward functions" (§10). The §2 goals print `loan_k` holes inside sealed programs.
- "A match and a call to a function containing it are treated alike" (§6 "Case splitting and joins"). This holds operationally, but not up to conversion. `F(x)` and `F`'s body inlined are not convertible at the generic call (the two sealed programs differ). Two top-level functions with identical bodies but different names are not convertible either. Conversion has no δ for stuck calls, so extracting a helper changes which equations hold by `refl`. That is a usability cliff for a proof assistant and should be stated.
- Appendix item 10 binds a parameter to `⋆` when its type "has sort Prop" (computed). The checker instead uses the declared class (`isPropV`/`fnClass`). With a parameter `g : Π(x : &Nat). T(Z)` the two readings differ. Under the appendix's reading, the generic call would see `⋆` where instances see an effectful function. The paper and the artifact disagree here.

### W7 (moderate). Presentation: the body does not define the calculus

- The body never shows the typing judgement formally. §6's figure gives four rules in prose, and everything else is in a 20-page appendix. A reader of the body cannot check a single derivation.
- Terms are used before they are defined: "generic call", "footprint", "owners" (§2, defined in §5–6); "stuck block", "head call" (§4); "declared proof", "declared sort", "confinement" (§6, defined only in the appendix); "[Seal]" (§8); "inert" loans; "generalisation" (Fig. `fig-why`, defined in the appendix).
- The same material is explained three times. Erasure appears in §4, §6 and the appendix. Subsingleton elimination appears in §6, note 10 and related work. "Injectivity deliberately not added" appears in §5, note 26 and related work.
- §1.3 ("Why this is not impossible") is dense and imprecise before the reader has the calculus. It says "a type contains only values", but types contain sealed programs that re-run under refinement.
- The paper presents `Nat` as a declared inductive, but the checker builds it in (note 25).

### W8 (minor). Completeness and usability

These are acknowledged, but they add up: naturality holds only up to resolution (the `Pick` program runs for every `n` but is rejected), there is no η at all, there is no δ on neutrals (W6), there is no injectivity of constructors, there is no generic `&A`, and there are no borrows in data. Loops are not designed. It would help to measure how often the examples need a workaround for each of these.

### W9 (minor). Related-work gaps, from my area

- Gilbert, Cockx, Sozeau and Tabareau, POPL 2019 (`SProp`, and why a reducing eliminator for a definitionally irrelevant equality is dangerous), and Pujet and Tabareau, POPL 2023 (impredicative OTT, normalisation). Both are directly on the `Eq`/`J`/`Prop` design (W4).
- Krishnaswami, Pradic and Benton, "Integrating linear and dependent types" (POPL 2015), and Vákár's dependent call-by-push-value. These are the standard references for state and linearity inside dependent types.
- Werner, "Sets in types, types in sets", and the Lee–Werner proof-irrelevant set model: the models the consistency sketch is actually closest to. Reynolds, "Polymorphism is not set-theoretic", is relevant as soon as a proof-relevant type sits in impredicative `Prop` (W2).
- Refinement reflection and proof by logical evaluation (Vazou et al., POPL 2018): "types run programs; equations proved by evaluating both sides", in a verification setting.
- Low* (F*) for verified low-level code in a dependently typed host. Electrolysis (Ullrich 2016), which translated safe Rust to Lean before Aeneas.
- `refs.bib` contains entries (`cbpv`, `syntactic-models`, `reflection-elim`, `bowman-cps`) that the paper does not cite. Either cite and discuss them, or remove them.

## 4. Attempted attacks and outcomes

All attacks were run in a scratch copy of the checker (`run` with the default `Config` unless stated).

| # | Attack | Outcome |
|---|---|---|
| 1 | Effectful `f : Π(x : &Nat). T(Z)` (`T(Z)` computes to `⊤` but is not a declared proposition) passed to a proof parameter `k : Π(x : &Nat). ⊤`; generic call sees `⋆`, instance runs `f` inside a callee (`Boom`) | **Accepted: closed proof of `False`.** Works at `0127f58b` and `b323d5ef`. |
| 2 | Same seam via a generic statement about `RunK(k, &c)` (`Boom2`), plus `RunIs` proving the opposite value of the same closed term | **Both accepted.** |
| 3 | Same seam via an annotated `let q : Π(x : &Nat). ⊤ = f` inside a stuck match (`Lie4`/`Boom4`): the typing judgement erases the bound term, the machine does not | **Accepted: closed proof of `False`.** |
| 4 | Prop-sorted type with distinguishable inhabitants (`TT`, `K1`, `K2`) | **Accepted.** No `False` by itself, but it refutes the model sketch (W2). |
| 5 | Direct instance, calling `k(x)` inline in the statement rather than through a callee | Rejected: the typing path reads a proof-flagged call head as `⋆`. The leak needs a callee body run by the machine. |
| 6 | Appendix item 10 read literally (a parameter whose type *has sort* `Prop` is `⋆` at the generic call), with `g : Π(x : &Nat). T(Z)` | Checker rejects, because it uses the declared class rather than the computed sort. This is a paper/artifact mismatch; under the appendix's wording the generic and instance paths would disagree. |
| 7 | `J`-cast Ω under hypotheses `(Nat→Nat) = ((Nat→Nat)→Nat)` and back | Checker: "call depth exceeded". Checking diverges without fuel (W4). |
| 8 | `J`-cast `5 : Bool` then match | Rejected with "[Match] on 5, which is not a value of Bool". WF condition 6 fails in open terms. |
| 9 | Projecting a data field out of a one-constructor, non-subsingleton `Prop` inductive (`inductive Sig : Prop := MkSig(n : Nat)`) | The surface has no named field projection, and the match form is correctly rejected by subsingleton elimination. But the appendix's core admits it: `content(p.g) = ⋆` when `content(p) = ⋆`, and `type(p.g)` is defined for a proof's only constructor, with no subsingleton condition on [T-Read] of a field place. Add the condition. |
| 10 | The paper's coinductive-conversion example (two functions stuck at the generic call) | Not convertible, as claimed. Also not convertible: two identically-bodied top-level functions, and `F(x)` against its own body (no δ on neutrals, W6). |
| 11 | Recursion via entry-value tricks, self-passing, nested closures | Rejected; the suite already covers these. |
| 12 | Mechanisation | `lake build` succeeds with one `sorry` (`termination`). The theorems in Fig. `fig-claims` depend only on standard axioms. Property 6 is syntactic injectivity (W3). |

## 5. Questions for the authors

1. In [App] and [Call-type], do parameter bindings carry proof flags? What does the machine do when a proof-flagged variable is a call head, or is passed as an argument, when its stored value is a live function? What does calling `⋆` mean?
2. Is "declared sort = computed sort" meant to be an invariant for well-formed type terms? If not, how does the model interpret `TT` (W2)?
3. Does the stability conjecture cover conversion as well as refinement? If yes, attack 1 is a counterexample. If no, what replaces it?
4. Why does `J` reduce without comparing endpoints? Would a K-like rule (reduce only when `a ≡ b`) break any example in the paper?
5. Given `h : Id A t u`, how does a user derive `Id B C[t] C[u]` for a program context `C`, or transitivity `Id A t v` from `Id A t u` and `Id A u v`, whose footprints differ? Is `Id` a congruence *inside* the logic, or only in the meta-theory? The name "computation equality" suggests the former. Note also that `Id Unit (x := 6) ()` is the proposition `x = 6`, so `Id` is relative to the current state rather than a contextual equivalence of programs.
6. How are generalisation records (global, surviving private copies) reflected in a derivation-indexed model?
7. What is the cost of re-normalising every sealed program in the state on each refinement, and on each growth of `ρ`, as programs grow?
8. Can the fire-triangle positioning be made precise, for example via a translation into ∂CBPV that identifies which of the three properties Ochr gives up for open terms?

## 6. What to cut or compress

- §1.3: cut to one paragraph, and move the fire-triangle comparison to related work once the calculus has been defined.
- §2: keep `AddM`/`AddMZero`, `TailM`/`AddMEq` and one of "Proofs about the current state" or "Trees". Cut "Branching" to two sentences.
- §4 "Functions and closures" and §6 "Proofs are matched by their type": halve them. Most of the content is repeated in the appendix.
- Fig. `fig-why`: move to the appendix and keep three representative rows in the body.
- §8 ledger classes and §10 "Costs" / "What the programmer sees": compress to a paragraph each.
- Appendix notes 12–27 are design choices. Move them to the artifact documentation.
- Remove the three-fold repetitions listed in W7.
- Spend the space saved on a one-page figure with the formal typing rules in the body, and a short glossary.

## 7. Score

**Reject.** Confidence: high (4/5).

The core idea (sealed programs as lazily computed backward functions, and induction hypotheses typed in the caller's environment) is original and worth publishing. But the submission's soundness story rests on a claimed invariant ("every decision is made from syntax") that the artifact refutes with a closed proof of `False`. The rules have a matching gap (two notions of proposition, joined by conversion). Nothing about the typed calculus is proved, the consistency sketch fails on an accepted program, and decidability is settled negatively rather than open.

**What would move my score up one notch (to weak reject):**

1. Put relevance into the types and make conversion respect it (W1), so that declared class equals sort by construction.
2. Add `Boom`, `Boom2`, `Boom4` and `TT` as regressions.
3. Make `J` K-like, or state undecidability (W4).
4. Mechanise stability under refinement *and* conversion for the current rule set, even without the model.

With those four, plus the formal typing rules in the body, I would be at weak accept for a venue that values new design ideas with an executable artifact.
