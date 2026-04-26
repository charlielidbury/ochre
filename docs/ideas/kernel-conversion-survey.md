# Kernel Conversion / Subtype Check around WHNF: A Literature Survey

This is a citation-heavy survey of how mainstream dependent type theory implementations
structure their conversion (definitional equality) and subtype (cumulativity) check
around weak head normal form (WHNF). The motivating question is the design decision in
Och of putting beta-reduction *inside* the subtype relation, vs the more common
practice of separating WHNF computation from the structural comparison.

The core focus questions, applied to each system below:

1. **Is reduction inside the subtype/conversion check, or outside?**
2. **What is the "value" representation?** (Closed term in WHNF? A separate `Value`
   inductive? Just any term with an `is_whnf` predicate?)
3. **How is equirecursion / recursive types handled?**
4. **How is non-termination handled?**
5. **Specific lines / sections where the conversion algorithm is implemented or
   specified.**

**TL;DR for the impatient.** Across Coq, Lean 4, Agda, MetaCoq, and Abel-style typed
NbE, the universal architecture is:

- **Reduction is _called from_ the conversion check, not _embedded in_ its rules.**
  The conversion algorithm is a structural comparison of WHNFs that may *re-invoke*
  reduction (typically via lazy delta or unfolding heuristics) when heads do not
  match; but the rules that compare the WHNFs themselves are pattern-matching on a
  finite set of head shapes, not closed under beta.
- **The "value" is almost always just a term**, distinguished by being the *output*
  of `whnf` or by sitting in a stack/zipper. Exceptions: **typed NbE** (Abel), where
  there is an explicit `D` / `Nf` / `Ne` algebra of semantic values; and (informally)
  the `tFix`/`tCoFix`-with-stack form in MetaCoq.
- **Cumulativity / subtyping is layered on top** as an extra leaf rule for sorts;
  it does *not* appear in the beta/iota rules. PCUIC is explicit: `cumul` is defined
  on terms by closing `leq_term` (a syntactic order on heads) under reductions on
  either side.
- **Equirecursion is essentially absent** from these systems; the closest thing is
  Agda's coinductive records (sized types / copatterns), which sidestep equirecursion
  by isorecursive-style copatterns rather than admitting `mu X. F X = F (mu X. F X)`
  inside conversion.
- **Non-termination is forbidden** by the termination/positivity checker upstream of
  the kernel in Coq, Agda, and MetaCoq; **Lean 4 admits non-terminating reduction in
  principle** (impredicativity + proof irrelevance + subsingleton elimination give
  Andreas-Abel-style omega, [Lean4Lean §3.2.1, p.7]) and the kernel guards against
  it with **fuel + depth limits**, not termination proofs.

Och's choice (β-redexes inside subtype) is the *unusual* one — none of these systems
do this. Section 6 below summarises what Och buys and pays for.

---

## 1. Coq's kernel (CCIC / PCUIC)

### Primary sources

- Thierry Coquand and Gérard Huet. **"The Calculus of Constructions"**. *Information
  and Computation* 76(2-3), 1988 (also INRIA RR 530, 1986).
  [INRIA HAL hal-00076024](https://hal.inria.fr/inria-00076024).
- Christine Paulin-Mohring. **"Inductive Definitions in the System Coq — Rules and
  Properties"**. TLCA 1993, LNCS 664. (Foundation for inductive types; iota-rules
  appear in conversion.)
- Hugo Herbelin and Bruno Barras. Various Coq RR notes on the kernel through the
  2000s; see also Herbelin's HDR thesis (2005) for the meta-theory of CIC's
  conversion.
- Amin Timany and Matthieu Sozeau. **"Cumulative Inductive Types in Coq"**. FSCD
  2018. [PDF on Inria](https://hal.inria.fr/hal-01580006). Specifies the form of
  cumulativity used in the modern PCUIC kernel.
- Bruno Barras. **"Coq en Coq"** (1996, INRIA RR-3026). Early
  Coq-checker-in-Coq attempt; precursor to MetaCoq. Established the pattern of
  WHNF-based comparison.

### Where the algorithm lives in the source

The Rocq (Coq) kernel's conversion check is in `kernel/reduction.ml` and its
interface in `kernel/reduction.mli`. See:

- [`coq/kernel/reduction.ml`](https://github.com/coq/coq/blob/master/kernel/reduction.ml)
- [`coq/kernel/reduction.mli`](https://github.com/coq/coq/blob/master/kernel/reduction.mli)
- [`coq/kernel/conversion.ml`](https://github.com/coq/coq/blob/master/kernel/conversion.ml)
  (the lazy delta / cumulativity dispatcher; spun out of `reduction.ml` in the 8.x
  refactor).

Key entry points (their names have been stable since Coq 8.0):

- `whd_all`, `whd_allnolet` — weak-head normalisation drivers (closure-based; flag
  controls which delta unfoldings are allowed).
- `ccnv` (conversion driver) and `eqappr_x` (compare two reduced applicative
  forms head-symbol by head-symbol).
- `compare_stack` — once two heads agree, walk down their argument stacks and
  recurse.

The driver structure is: feed both terms to `whd_all` to get WHNFs, dispatch on the
head pair, on equal heads recurse on subterms, on unequal heads attempt `lazy delta`
(unfold one definition, retry) before declaring failure.

### Strategy

- **WHNF, lazy, closure-based**: Coq's reduction machine (`Cclosure` /
  `RedFlags`-controlled) computes WHNFs incrementally; bodies are not normalised
  unless conversion forces it. There is also a separate **VM**
  (`kernel/cbytegen.ml`, `cbytecodes.ml`, the `vm_compute` machine) and a **native
  compiler** (`kernel/nativecode.ml`, `vo_native_compute.ml`), both of which produce
  full normal forms when invoked, but the *default* conversion path is WHNF +
  structural comparison + on-demand re-reduction.
- This style — "iterated comparison of weak-head normal forms to test cumulativity
  and conversion" — is the standard description in the Rocq reference manual
  ([§ 4 Conversion rules](https://coq.github.io/doc/v8.18/refman/)).

### Subtyping (cumulativity)

Cumulativity in CCIC / PCUIC is universe subtyping with reduction allowed on either
side, lifted compatibly through the term structure. The PCUIC declarative rule
(formalised in MetaCoq) is:

```
cumul_refl : leq_term Σ t u → Σ ; Γ ⊢ t ≤ u                      (universe ≤ at heads)
cumul_red_l : Σ ; Γ ⊢ t ⇝ v → Σ ; Γ ⊢ v ≤ u → Σ ; Γ ⊢ t ≤ u      (reduce LHS)
cumul_red_r : Σ ; Γ ⊢ t ≤ v → Σ ; Γ ⊢ u ⇝ v → Σ ; Γ ⊢ t ≤ u      (reduce RHS)
```

(Sozeau, Boulier, Forster, Tabareau, Winterhalter, *Coq Coq Correct!* POPL 2020,
§ 2, [PDF](https://theowinterhalter.github.io/res/POPL20-coq-coq-correct.pdf), see
the `cumul` definition reproduced verbatim around lines 307–311 of their paper:

> ```
> Inductive cumul (Σ : global_env_ext) (Γ : context) : term → term → Type :=
>   | cumul_refl t u : leq_term (global_ext_constraints Σ) t u → Σ ; Γ ⊢ t ≤ u
>   | cumul_red_l t u v : fst Σ ; Γ ⊢ t ⇝ v → Σ ; Γ ⊢ v ≤ u → Σ ; Γ ⊢ t ≤ u
>   | cumul_red_r t u v : Σ ; Γ ⊢ t ≤ v → fst Σ ; Γ ⊢ u ⇝ v → Σ ; Γ ⊢ t ≤ u
> ```)

Notice that *beta is not a cumulativity rule*; beta is a reduction (`⇝`), and
`cumul` is *closed under reduction at the boundary*, not "compatible with beta in
the middle". This is structurally identical to Coq's kernel and to every system
below.

### Recursive types and non-termination

CIC has **inductive** types (positivity-checked) and **co-inductive** types (guard-
checked). Both checks are performed by the kernel before a definition is added to
the environment; the conversion algorithm assumes well-foundedness. Non-termination
is *prevented* by termination/positivity, not handled by the kernel. The PCUIC
formalisation explicitly **postulates strong normalisation** as an axiom — see
*Coq Coq Correct!* § 2.3.4 / line 686:

> "we can state it as an axiom. […] Conjecture normalisation : ∀ Γ t,
>  welltyped Σ Γ t → Acc (cored (fst Σ) Γ) t."

There is **no equirecursion** in CIC. Recursive types are isorecursive (you write a
fixpoint, you must explicitly fold/unfold via `match`/recursors).

### Answers to focus questions

| Q | Coq |
|---|-----|
| Reduction inside subtype rules? | **No.** `cumul_red_l/r` is "close under reduction on the boundary"; the structural rules compare WHNFs only. |
| Value representation? | A `term` produced by `whd_all`. No separate type; you "know" it's a value because it came out of WHNF. |
| Equirecursion? | None. Inductive/coinductive only. |
| Non-termination? | Forbidden upstream by positivity + guard. SN is axiomatised. |
| File / line | `kernel/reduction.ml` (`ccnv`, `eqappr_x`, `compare_stack`). |

---

## 2. Lean 4's kernel

### Primary sources

- Mario Carneiro. **"The Type Theory of Lean"**. M.S. thesis, Carnegie Mellon
  University, April 2019. Source + PDF at
  [github.com/digama0/lean-type-theory](https://github.com/digama0/lean-type-theory/releases),
  release `v1.0` (the "MS Thesis version", 17 April 2019). The full formal spec of
  Lean's logical rules is in this PDF; not published anywhere else.
- Leonardo de Moura and Sebastian Ullrich. **"The Lean 4 Theorem Prover and
  Programming Language"**. CADE 2021, LNCS 12699, pp. 625–635. [PDF](https://pp.ipd.kit.edu/uploads/publikationen/demoura21lean4.pdf).
- Mario Carneiro. **"Lean4Lean: Towards a Formalised Metatheory for the Lean
  Theorem Prover"**, [arXiv:2403.14064](https://arxiv.org/abs/2403.14064), 2024.
  This is the most explicit walkthrough of the kernel's conversion algorithm in
  the literature.
- Sebastian Ullrich. **"An Extensible Theorem Proving Frontend"**. Ph.D. thesis,
  KIT 2023, has additional discussion of the elaborator (above the kernel).
- Andrés Goens, Sebastian Graf, Joachim Breitner et al. **"Lean4Less"**, ITP 2025.
  [Springer link](https://link.springer.com/chapter/10.1007/978-3-032-11176-0_13).

### Where the algorithm lives in the source

The C++ kernel:

- [`lean4/src/kernel/type_checker.cpp`](https://github.com/leanprover/lean4/blob/master/src/kernel/type_checker.cpp)
  contains `is_def_eq`, `whnf`, `whnf_core`, `lazy_delta_reduction`,
  `is_def_eq_app`, `is_def_eq_binding`, `is_def_eq_proof_irrel`. WHNF starts
  around line ~695 (`whnf_core`) and ~930 (`whnf`); `is_def_eq` around line ~900;
  `lazy_delta_reduction` around line ~1050.

A reference re-implementation (also a teaching artefact):

- [`ammkrn/type_checking_in_lean4`](https://ammkrn.github.io/type_checking_in_lean4/)
  — the "Type Checking in Lean 4" book, especially the
  [Definitional Equality](https://ammkrn.github.io/type_checking_in_lean4/type_checking/definitional_equality.html)
  chapter.

A formally-verified port:

- [`digama0/lean4lean`](https://github.com/digama0/lean4lean) — Lean 4 kernel
  re-implemented in Lean and (partially) verified.

### Algorithm structure

From Carneiro's *Lean4Lean* paper, § 3.2.4, p. 8 (line 939 of the arXiv text):

> "When writing a DTT type checker, this is the least 'canonical' part. There are
> many different heuristics one can employ here, and because the worst-case time
> complexity is galactically large, the heuristics are critical […]"

The algorithm for `s ≡ t`:

> § 3.2.4 / lines 957–1042:
> 1. If `s` and `t` are both lambdas / sorts / foralls / literals: compare subterms.
> 2. Validate `true ≡ t` if `t ↝ true`. *(reflection optimisation)*
> 3. Reduce `s ↝ s'` and `t ↝ t'` with `cheapProj := true`; continue with `s' ≡ t'`.
> 4. If `s : α` and `t : β` and `α ≡ β : U₀` then return true (`t-proof-irrel`).
> 5. If `f a ≡ g b` where both `f, g` are definitions, unfold the lower-`height`
>    one first (lazy delta); else unfold both and continue.
> 6. Compare subterms for applications, projections, variables.
> 7. Reduce again if it makes progress.
> 8. If `f a ≡ f b` where `f` is a definition: try `a ≡ b` *backtracking* if it
>    fails, otherwise unfold `s` and `t`.
> 9. Try η-expansion (`s ≡ λx.t` becomes `s x ≡ t`).
> 10. Try structure η: `s ≡ ⟨t_i⟩` becomes `s.i ≡ t_i`.
> 11. Unfold string literals, try unit η.
> 12. Otherwise fail. *("Because of various incompletenesses in this algorithm,
>    this doesn't actually imply `s ≢ t`."*)

The four entry points form the kernel's API and have a feedback-vertex-set structure
(*Lean4Lean* § 3.2.1, lines 770ff):

```text
isDefEqCore  : Expr → Expr → M Bool
whnfCore     : Expr → (cheapRec=false) (cheapProj=false) → M Expr
whnf         : Expr → M Expr
inferType    : Expr → (inferOnly : Bool) → M Expr
```

`whnfCore` "has the same specification as `whnf`, but it lacks some of the early
exit paths" (Lean4Lean § 3.2.1, line ~795). Both produce an `Expr`, not a separate
"value" type.

### Subtyping / cumulativity

Lean has cumulativity at the level of universes only (sort cumulativity). This is
checked in `is_def_eq_sort` / `is_def_eq(level const &, level const &)` which
delegates to `level::is_equivalent`. The structural rules compare WHNFs and treat
sorts as a leaf — there is no `cumul`-style closure under reduction on the boundary
because beta-reduction below sorts is handled by `whnf` before the structural
compare ever fires.

### Recursive types and non-termination

Lean has inductive types (with positivity check) plus quotient types and proposition
extensionality. **Famously, Lean's reduction is not provably terminating** — the
combination of impredicative `Prop`, proof irrelevance, and subsingleton elimination
admits Andreas Abel's omega construction. Carneiro reproduces this in *Lean4Lean*
§ 3.2.1, lines 778–810:

```lean
def True' := ∀ p : Prop, p → p
def om : True' := fun A a =>
  @cast (True' → True') A
    (propext ⟨fun _ => a, fun _ => id⟩)
    (fun z => z (True' → True') id z)
def Om : True' := om (True' → True') id om
#reduce Om -- whnf nontermination
```

The kernel handles this with a **`fuel` parameter** and a **`deepRecursion`
exception** (currently set to 1000). Quoting Lean4Lean § 3.2.1 lines 826–836:

> "use a fuel parameter, a natural number which counts the number of nested
> recursive calls to one of the Methods, and throw a `deepRecursion` error if we
> run out of fuel. Currently, this limit is a fixed constant (1000), which turns
> out to be sufficient for checking all of Mathlib […]"

This is the most permissive of the four major kernels surveyed and the most
relevant comparison for Och: Lean **does** allow non-terminating WHNF in proofs,
guarding only by fuel — and Lean still keeps reduction *outside* the structural
conversion rules.

### Answers

| Q | Lean 4 |
|---|--------|
| Reduction inside subtype rules? | No. `whnf` is called *between* structural compares; sorts are compared as leaves. |
| Value representation? | Plain `Expr` produced by `whnf` / `whnfCore`. No separate `Value` type. |
| Equirecursion? | None. Inductive / quotient types only. |
| Non-termination? | Allowed in principle (impredicativity + proof irrel + subsingleton). Guarded by **fuel = 1000** + depth limits. |
| File | `lean4/src/kernel/type_checker.cpp`. |

---

## 3. Agda's kernel

### Primary sources

- Ulf Norell. **"Towards a Practical Programming Language Based on Dependent Type
  Theory"**. Ph.D. thesis, Chalmers, September 2007.
  [PDF](https://www.cse.chalmers.se/~ulfn/papers/thesis.pdf). The conversion
  algorithm is given in Chapter 1 (§ 1.4, pp. 19–23, Figs 1.4–1.8).
- Andreas Abel and Thierry Coquand. **"Untyped Algorithmic Equality for
  Martin-Löf's Logical Framework with Surjective Pairs"**. TLCA 2005, LNCS 3461.
- Andreas Abel, Thierry Coquand, Miguel Pagano. **"A Modular Type-Checking
  Algorithm for Type Theory with Singleton Types and Proof Irrelevance"**. LMCS
  2011 (also TLCA 2009). [LMCS](https://lmcs.episciences.org/1069),
  [arXiv:1102.2405](https://arxiv.org/abs/1102.2405).
- Andreas Abel, Joakim Öhman, Andrea Vezzosi. **"Decidability of Conversion for
  Type Theory in Type Theory"**. POPL 2018,
  [DOI 10.1145/3158111](https://dl.acm.org/doi/10.1145/3158111).
- Andreas Abel. **"MiniAgda: Integrating Sized and Dependent Types"**. PAR 2010,
  [PDF](https://www.cse.chalmers.se/~abela/miniagda-par10.pdf).
- Andreas Abel and Brigitte Pientka. **"Wellfounded Recursion with Copatterns and
  Sized Types"**. JFP 26, 2016. (How Agda handles "coinduction" — copatterns +
  sized types, *not* equirecursion.)

### Source code

- Conversion: [`agda/src/full/Agda/TypeChecking/Conversion.hs`](https://github.com/agda/agda/blob/master/src/full/Agda/TypeChecking/Conversion.hs)
  — `compareTerm`, `compareAs`, `compareType`, `compareAtom`.
- Reduction: [`agda/src/full/Agda/TypeChecking/Reduce.hs`](https://github.com/agda/agda/blob/master/src/full/Agda/TypeChecking/Reduce.hs)
  — `reduce`, `reduceB`, `instantiate`, `instantiateFull`.
- The fast reduction machine (Agda Abstract Machine, AAM, "compile-time
  call-by-need"):
  [`agda/src/full/Agda/TypeChecking/Reduce/Fast.hs`](https://github.com/agda/agda/blob/master/src/full/Agda/TypeChecking/Reduce/Fast.hs).

### Algorithm structure (Norell § 1.4, pp. 19–23)

Norell's thesis presents the conversion algorithm as **type-directed** βη-equality
checking, with three judgements:

> Norell § 1.4, lines 951–953:
> "Γ ⊢ s ≃ t ↑ A   checking conversion of arbitrary terms
>  Γ ⊢ s ≃₀ t ↑ A  checking conversion of normal terms
>  Γ ⊢ s ≡ t ↓ A   checking conversion of neutral terms"

The first rule of `≃` (Fig. 1.7) explicitly invokes WHNF reduction:

> ```
> s →whnf s'    t →whnf t'    A →whnf A'    Γ ⊢ s' ≃₀ t' ↑ A'
> ─────────────────────────────────────────────────────────
> Γ ⊢ s ≃ t ↑ A
> ```

Then `≃₀` *only operates on weak head normal forms*; it is structural and does not
re-invoke beta. Subtyping (Fig. 1.6) has the analogous shape:

> ```
> A →whnf A'    B →whnf B'    Γ ⊢ A' ⩽₀ B'
> ─────────────────────────────────────
> Γ ⊢ A ⩽ B
> ```

So Agda's structure is the *cleanest* example of the standard architecture:
"reduce, *then* compare structurally, with structural rules pattern-matching on
WHNF heads only".

In the Haskell kernel, this becomes:

```haskell
compareTerm :: Comparison -> Type -> Term -> Term -> TCM ()
compareTerm !cmp !a !u !v = compareAs cmp (AsTermsOf a) u v

compareAs :: Comparison -> CompareAs -> Term -> Term -> TCM ()
-- delegates to compareAs' which uses reduceWithBlocker / reduceB
```

`compareAtom` does:

```haskell
mb' <- etaExpandBlocked =<< reduceB m
nb' <- etaExpandBlocked =<< reduceB n
```

i.e. *first reduce both sides to WHNF (returning a `Blocked Term`), then η-expand
records, then compare structurally*.

### Value representation

Agda has **no separate `Value` type**; everything is `Term`. The "is in WHNF"
predicate is *implicit*: a term is in WHNF iff it is the output of `reduceB`. The
`Blocked` wrapper records *why* reduction got stuck (e.g. waiting on a metavariable),
allowing the conversion check to defer:

```haskell
(catchConstraint (ValueCmp cmp t m n) :: TCM () -> TCM ()) $ do
```

The constraint is literally named `ValueCmp` — but the "value" here is just the
`Term` after `reduceB`.

### Recursive types and (co)induction

Agda has **inductive** types (positivity-checked) and **records with copatterns**
(for coinduction). It does *not* have equirecursive types in the conversion check.
"Coinductive equality" is handled by sized types or by copattern recursion at the
term level, never by silently identifying `μX. F X` with `F (μX. F X)` inside
conversion.

References:

- Abel, "MiniAgda" PAR 2010.
- Abel & Pientka, "Wellfounded Recursion with Copatterns and Sized Types", JFP 2016.

### Non-termination

Agda forbids non-termination via its **termination checker** (Abel's `foetus`-style
size-change termination, descendant of the work in his Habil § 4 / § 5). If a
definition fails the termination check Agda still admits it as `TERMINATING`-pragmaed
or with `--no-termination-check`, but then **the kernel does not guarantee
conversion termination** — it relies on the definition author having lied carefully.

The reduction machine itself has no fuel: termination is a global *meta-theoretic*
guarantee, not a runtime check.

### Answers

| Q | Agda |
|---|------|
| Reduction inside subtype rules? | No. WHNF is invoked once, structural comparison then proceeds on heads. (Norell § 1.4 Figs 1.6–1.8.) |
| Value representation? | `Term`, output of `reduceB`. No separate `Value`. |
| Equirecursion? | None. Inductive + copatterns + sized types. |
| Non-termination? | Forbidden by termination checker upstream of kernel. |
| File / line | `Agda/TypeChecking/Conversion.hs` (`compareTerm`, `compareAtom`). |

---

## 4. MetaCoq — Coq formalised in Coq

This is the most useful primary source for our purposes because the conversion
check is **formally specified and mechanically proved correct in Coq**.

### Primary sources

- Matthieu Sozeau, Abhishek Anand, Simon Boulier, Cyril Cohen, Yannick Forster,
  Fabian Kunze, Gregory Malecha, Nicolas Tabareau, Théo Winterhalter. **"The
  MetaCoq Project"**. Journal of Automated Reasoning 64, Feb 2020.
  [Springer DOI](https://link.springer.com/article/10.1007/s10817-019-09540-0).
  Extended ITP 2018 paper. Defines PCUIC.
- Matthieu Sozeau, Simon Boulier, Yannick Forster, Nicolas Tabareau, Théo
  Winterhalter. **"Coq Coq Correct! Verification of Type Checking and Erasure for
  Coq, in Coq"**. POPL 2020 (PACMPL Vol. 4).
  [PDF](https://theowinterhalter.github.io/res/POPL20-coq-coq-correct.pdf).
- Matthieu Sozeau, Yannick Forster, Meven Lennon-Bertrand, Jakob Nielsen, Nicolas
  Tabareau, Théo Winterhalter. **"Correct and Complete Type Checking and
  Certified Erasure for Coq, in Coq"**. Journal of the ACM, 2025.
  [DOI 10.1145/3706056](https://dl.acm.org/doi/10.1145/3706056).
- The MetaCoq codebase: [github.com/MetaCoq/metacoq](https://github.com/MetaCoq/metacoq)
  (now also [MetaRocq](https://github.com/MetaRocq/metarocq)).

### Where the algorithm is implemented

In MetaCoq's `safechecker/`:

- [`PCUICSafeReduce.v`](https://metacoq.github.io/v1.2-8.16/MetaCoq.SafeChecker.PCUICSafeReduce.html)
  — fuel-free verified reduction machine (`reduce_stack`).
- `PCUICSafeConversion.v` — the verified conversion checker (`isconv_red`,
  `isconv_prog`, `isconv_args`, `isconv_fallback`).
- `PCUICSafeChecker.v` — the surrounding `infer` / `infer_cumul` /
  `convert_leq` driver.

### Algorithm structure

From *Coq Coq Correct!* § 3 (lines 704–905). The algorithm has three layers:

1. **Reduction without fuel** (§ 3.1, p. 8:14, lines 709ff): uses a measure
   `R := dlexprod (cored Σ Γ) (@posR)` lexicographically combining "co-reduction
   step" (well-founded by the strong-normalisation axiom) and "position in the
   stack" (well-founded by structural depth).
   ```coq
   Definition reduce_stack Γ (t : term) (p : stack)
     (h : wellformed Σ Γ (zip (t,p)))
     : { t' : term ∗ stack | Req Σ Γ t' (t, p) } :=
     Fix_F (R := R Σ Γ) ... (* by accessibility *)
   ```
   See § 3.2 (`Weak-Head Normalisation Using a Stack Machine`, p. 8:16, line 791).

2. **Cumulativity / conversion** (§ 3.4, line 876, p. 8:18). Quoting verbatim
   (lines 892–902):

   > "Then, conversion up to cumulativity can be implemented again by induction on
   > accessibility of R […] Coarsely, it mimics the conversion algorithm
   > implemented in Coq which consists in
   >   (1) first weak-head reducing the two terms without δ-reductions (i.e.,
   >       without unfolding definitions);
   >   (2) then comparing their heads, and if they match comparing the subterms;
   >   (3) if they do not match, checking if some computation (pattern-matching
   >       or fixpoint) — or just the whole term — is blocked by a definition
   >       that could unfold to a value, unfolding this definition and comparing
   >       again."

   The `_isconv_red` Equations definition is a state machine over four states:
   `Reduction`, `Term`, `Args`, `Fallback`. Each state has its own correctness
   spec (`ConversionResult` / `Ret`).

3. **Type inference** (§ 3.5, lines 911–950): bidirectional, calls
   `infer_cumul` which calls `convert_leq` which is the verified conversion.

### Stack representation

This is the closest thing to a "value type" in the verified kernel. PCUIC's stack
(*Coq Coq Correct!* p. 8:15, lines 723–734) is:

```coq
Inductive stack : Type :=
| Empty
| App   (t : term) (p : stack)
| Fix   (f : mfixpoint term) (n : N) (args : list term) (p : stack)
| CoFix (f : mfixpoint term) (n : N) (args : list term) (p : stack)
| Case  (indn : inductive ∗ N) (p : term) (brs : list (N ∗ term)) (p : stack)
| Proj  (p : projection) (p : stack)
| Prod_l (na : name) (B : term) (p : stack)
| Prod_r (na : name) (A : term) (p : stack)
| Lambda_ty (na : name) (b : term) (p : stack)
| Lambda_tm (na : name) (A : term) (p : stack)
| coApp (t : term) (p : stack).
```

A "value-in-context" is the pair `(term, stack)`. `zip` reassembles it; `zipp`
projects out the focused subterm. Reduction is on this pair.

### Cumulativity in PCUIC

From *Coq Coq Correct!* § 2 (lines 240–311, see the `cumul` block above). Critical
invariant: cumulativity is closed under reduction *at the boundary*, not inside
beta — the `cumul_refl` rule uses `leq_term` which is *syntactic* up to universe
ordering. Beta is `⇝`, called from `cumul_red_l/r`. This is the same architecture
we've now seen three times and it is **never** the Och architecture.

### Key theorems

From *Coq Coq Correct!* § 3 and the JACM 2025 follow-up:

- **§ 3.1, line ~704**: `Conjecture normalisation : ∀ Γ t, welltyped Σ Γ t →
  Acc (cored (fst Σ) Γ) t.` — the SN axiom on which everything else stands.
- **`reduce_stack_sound`** (PCUIC: SafeReduce) — `reduce_stack` outputs a
  reduction-equivalent WHNF.
- **`R_Acc`** — the well-founded measure for the verified reduction machine.
- **`convert_leq`** correctness — verifies that the algorithm decides PCUIC's
  declarative `cumul` (modulo the SN axiom).
- The 2025 JACM paper additionally proves **completeness** (the algorithm rejects
  iff the declarative judgement does not hold) — this was conjectured in POPL
  2020 and is the main contribution of the JACM extension.

### Answers

| Q | MetaCoq / PCUIC |
|---|-----------------|
| Reduction inside subtype rules? | No. `cumul` is closed under reduction on either side; the leaf rule is `leq_term` (syntactic). |
| Value representation? | `(term, stack)` zipper. The "value" is whatever `reduce_stack` returns. |
| Equirecursion? | None. Inductive/coinductive only. |
| Non-termination? | SN is **axiomatised**; the algorithm uses well-founded recursion on the SN proof. |
| File | `metacoq/safechecker/theories/PCUICSafeReduce.v`, `PCUICSafeConversion.v`. |

---

## 5. Andreas Abel's NbE work

Abel's body of work is the most carefully-thought-out case for **typed
normalisation by evaluation** as the basis for the conversion check. It differs from
the previous four systems in one important way: there is an *explicit* algebra of
semantic values.

### Primary sources

- Andreas Abel. **"Normalization by Evaluation: Dependent Types and
  Impredicativity"**. Habilitationsschrift, LMU München, May 2013.
  [PDF](https://www.cse.chalmers.se/~abela/habil.pdf). The single most
  comprehensive document on typed NbE for dependent types.
- Andreas Abel, Klaus Aehlig, Peter Dybjer. **"Normalization by Evaluation for
  Martin-Löf Type Theory with Typed Equality Judgements"**. LICS 2007.
- Andreas Abel, Thierry Coquand, Peter Dybjer. **"Normalization by Evaluation
  for Martin-Löf Type Theory with One Universe"**. MFPS 2007.
- Andreas Abel, Thierry Coquand, Miguel Pagano. **"A Modular Type-Checking
  Algorithm for Type Theory with Singleton Types and Proof Irrelevance"**.
  LMCS 2011 / TLCA 2009. [LMCS](https://lmcs.episciences.org/1069),
  [arXiv:1102.2405](https://arxiv.org/abs/1102.2405).
- Andreas Abel, Joakim Öhman, Andrea Vezzosi. **"Decidability of Conversion for
  Type Theory in Type Theory"**. POPL 2018.
- Thorsten Altenkirch, Ambrus Kaposi. **"Normalisation by Evaluation for
  Dependent Types"**. FSCD 2016.
  [PDF](https://drops.dagstuhl.de/opus/volltexte/2016/5972/pdf/LIPIcs-FSCD-2016-6.pdf).
  Companion / alternative formulation using QIITs.
- Andreas Abel, Andrea Vezzosi, Theo Winterhalter. **"Normalization by
  Evaluation for Sized Dependent Types"**. ICFP 2017.
  [DOI](https://dl.acm.org/doi/10.1145/3110277).

### Algorithm structure

Abel's NbE has three syntactic categories — see Habil § 4, Fig. 4.1, p. 41
(line 2737):

```
D    ∋ a, b, f, A, F   ::= (λt)ρ | ↑^A e | c | suc a | recA | recA aₐ |
                            recA aₐ aₛ | Fun A | Fun A F     -- semantic values
Dⁿᵉ  ∋ e, E            ::= xₖ | e d | rec_D dz ds e          -- neutral values
Dⁿᶠ  ∋ d, D            ::= ↓^A a                              -- normal values
```

There is a **proper distinction between syntax (`Exp`) and semantics (`D`)**, and
between *neutrals*, *normals*, and *general semantic values*. Conversion is decided
by:

1. **Evaluate** both terms into `D`.
2. **Read back** (`Rⁿᶠ`) into normal form `Dⁿᶠ`.
3. **Compare syntactically** — at this point η-conversion is already absorbed into
   the read-back, and there's no beta to worry about because evaluation has
   resolved all of it.

Concretely (Habil § 4.2, "Type Values, Reflection and Reification", line 2849):

> "A significant change w.r.t. simple types is that reflection and reification are
> now directed by type values A. This has a profound impact on the application and
> read-back operations. Application of a reflected neutral (↑^{Fun A F} e) at
> dependent function type leads to instantiation of the function codomain.
> η-expansion happens here necessarily piece-wise."

```text
(↑^{Fun A F} e) · a   = ↑^{F·a} (e d)    where d = ↓^A a
Fun · A               = Fun A
Fun A · F             = Fun A F

R^{nf}_n ↓^{Fun A F} f  = λ. R^{nf}_{n+1} ↓^{F·a} (f · a)   where a = ↑^A x_k
R^{nf}_n ↓^{B} ↑^{B'} e = R^{ne}_n e                       (B ≠ B' allowed at base type)
```

The last rule is interesting: when reading back a reified neutral at a base type,
Abel allows `B ≠ B'`. As he says (Habil § 4.2, line 2977):

> "When reading back reified neutrals ↓^B ↑^{B'} e at base type, we allow B ≠ B'.
> For one, this saves us a pointless equality check during read-back; for two,
> since we have cumulative universes, the neutral ↓^{Set_j} ↑^{Set_i} e is legal,
> at least for j ≥ i."

So **cumulativity is reflected directly in the read-back**, not in a separate
subtyping judgement on terms. This is one of the few places in the literature
where cumulativity sits *inside* the conversion machinery (specifically, inside
read-back) — but note it's still not "inside beta": it's inside the *value*
algebra.

### Subtyping in Abel

Subtyping in Habil is restricted to **universe subsumption** (`Set_k ≤ Set_l` for
`k ≤ l`) plus type equality, see § 4.1, line 2762:

> "we have a subsumption rule expressing that any term which can be assigned type
> T can also be assigned type T' as long as Γ ⊢ T ≤ T' meaning that T is a
> subtype of T' in context Γ. Subtyping is restricted to universe subsumption
> Set_k ≤ Set_l and type equality Γ ⊢ T = T' which means that T and T' are
> βη-equal expressions inhabiting some universe."

This is the same architecture as PCUIC — βη is *equality*, and `≤` adds *only*
universe ordering. Beta is not "inside subtype".

### Modular Type-Checking (Abel/Coquand/Pagano)

The "Modular" paper is explicit about the value/normal form structure: it defines
a **PER model** for constructing the NbE algorithm, proves *completeness and
soundness of the algorithm*, *injectivity of type constructors*, and gives a
*correct and complete type-checking algorithm for terms in normal form*. The point
of the paper is exactly to show that you can layer features (singleton types,
proof irrelevance) on top of a typed-NbE conversion check without re-doing the
metatheory each time. Beta/eta live in the evaluator; conversion is read-back +
syntactic compare.

### Answers

| Q | Abel-style typed NbE |
|---|---------------------|
| Reduction inside subtype rules? | No. Beta is in the *evaluator*; subtyping is at the leaves of read-back. |
| Value representation? | **Explicit `D` / `Dⁿᵉ` / `Dⁿᶠ` algebra**. Distinct from syntax `Exp`. |
| Equirecursion? | Not addressed. Sized types (Habil § 6 / Abel-Vezzosi-Winterhalter ICFP 2017) replace recursion in a typed way. |
| Non-termination? | Forbidden upstream; NbE relies on strong normalisation. |
| Sections | Abel Habil Ch. 4 (dependent), Ch. 5 (impredicative). Modular paper § 3-§ 4 for the type-checker. |

---

## 6. Pure type systems / declarative ⊑ formulations with β inside

This is the section the user specifically asked about: are there examples where
β-redexes are **inside** the subtype relation (as in Och), rather than being a
separate reduction relation closed at the boundary?

### What I found: short answer

**Mostly no.** Across the dependent-type-theory literature I surveyed, every
mainstream system separates β (a *reduction*) from `≤` (a *subtype/conversion
relation*), and `≤` is closed under reduction *only at the top* (`cumul_red_l/r`
in PCUIC, the `→whnf` premise in Norell). The Abel-style typed NbE pushes the
distinction even further apart: β lives in evaluation, `≤` in read-back.

### Cases that are partial exceptions

#### 6.1 Pure Type Systems with Subtyping (Zwanenburg)

- Jan Zwanenburg. **"Pure Type Systems with Subtyping"**. TLCA 1999, LNCS 1581,
  pp. 381–396. [Springer link](https://link.springer.com/chapter/10.1007/3-540-48959-2_27).
- Jan Zwanenburg. **"Object-Oriented Concepts and Proof Rules: Formalization in
  Type Theory and Implementation in Yarrow"**. Ph.D. thesis, TU Eindhoven, 1999.

Zwanenburg generalises F^ω_≤ to a Pure Type System framework. In this style:

- The conversion relation `≡` is the βη-equivalence, i.e. β is in the *equality*.
- Subtyping `≤` is then layered on top: `≤` is the smallest preorder containing
  `≡` and the universe / arrow-variance rules.

So β-equivalence is part of subtyping in the (trivial) sense that `t ≡ u → t ≤ u`,
but β is *not a subtyping rule*; it is an *equality rule* that subtyping happens
to subsume. This is the same as PCUIC's `cumul_refl` over `leq_term`.

> "A central problem [Zwanenburg] addressed was how to formulate the rules of the
> framework in such a way that circularities between theory about typing and
> theory about subtyping are avoided, which he solved by ensuring that subtyping
> rules do not depend on the typing rules." (TLCA 1999 abstract.)

The fact that he had to *solve* this circularity is itself a warning: putting
typing-relevant computation inside subtyping is hard.

#### 6.2 λI≤ (Yang & Oliveira, OOPSLA 2017)

- Yanpeng Yang, Bruno C. d. S. Oliveira. **"Unifying Typing and Subtyping"**.
  OOPSLA 2017, PACMPL 1.
  [DOI 10.1145/3133871](https://dl.acm.org/doi/10.1145/3133871),
  [PDF](https://i.cs.hku.hk/~bruno/papers/oopsla17.pdf).
- See also: Yanpeng Yang, **"Simple Dependent Type Theories for Programming"**,
  PhD thesis, HKU, 2024. [PDF](https://i.cs.hku.hk/~bruno/thesis/YanpengYang.pdf).

This is *the* paper that genuinely fuses typing and subtyping into one
relation. From the abstract:

> "λI≤ employs a novel technique that unifies typing and subtyping. In λI≤ there
> is only a judgment akin to a typed version of subtyping, where both the typing
> relation and type well-formedness are just special cases of the subtyping
> relation."

In λI≤, the unified judgement `Γ ⊢ e₁ ≤ e₂ : A` covers (a) typing (when `e₁ = e₂`),
(b) well-formedness (when `e₂ = e₁ = e₂`'s erasure …), and (c) genuine subtyping.
β-conversion is part of this unified relation — it is one of the rules generating
the preorder.

This is the closest published prior art to Och's design. **Differences:**
λI≤ is intended to be a "follower" of System F≤ generalised with dependent
types; it has subject reduction, transitivity of subtyping, narrowing, all
mechanically proved in Coq. It does *not*, however, formalise an *algorithm* for
deciding the unified judgement; the paper focuses on the declarative system. Whether
the algorithm would put β-reduction inside the structural rules or just punt it to
WHNF (as everyone else does) is not directly addressed by the paper; the
algorithmic version in subsequent work (Yanpeng Yang's PhD thesis 2024, and
follow-up papers) does the standard thing of WHNF-then-compare.

#### 6.3 λP≤ (Aspinall & Compagnoni)

- David Aspinall. **"Subtyping Dependent Types"**. LFCS-97-370, 1997.
  [LFCS PDF](http://www.lfcs.inf.ed.ac.uk/reports/97/ECS-LFCS-97-370/ECS-LFCS-97-370.pdf).
- David Aspinall, Adriana Compagnoni. **"Subtyping Dependent Types"**. TCS 266,
  2001.

λP≤ extends LF (`λΠ`) with subtyping. Subject reduction holds. The conversion
in λP≤ is the standard βη-equivalence and subtyping uses `cumul`-style closure:

> "the substitution lemmas for typing and subtyping depend on each other and
> require a more complicated proof by induction on four different judgments
> (i.e. subtyping, typing, kinding and formation) simultaneously. The transitivity
> of algorithmic subtyping requires types to be well-formed through
> beta-conversion." (Aspinall-Compagnoni TCS 2001 abstract.)

So: still the standard architecture. β is *required* in the metatheory of `≤`, but
it is not a structural rule of `≤`.

#### 6.4 Pierce TAPL Ch. 26–28 (System F<:)

The non-dependent prior art is **System F<:** in Pierce, *Types and Programming
Languages*, MIT Press 2002, Chapters 26–28 (especially Ch. 28 "Metatheory of
Bounded Quantification"). In F<: there is no β in subtyping at the term level
because terms don't appear in types. F<:_ω (Cardelli-Wegner; see Cardelli's
*"An Extension of System F with Subtyping"*, [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0890540184710133),
Information & Computation 1994, vol 109) has β at the **type level** because
types contain type-level β-redexes; the algorithmic subtyping there reduces type
operators to WHNF first and compares structurally — *exactly* the pattern we
already saw in dependent settings.

Pierce TAPL § 31.4 ("Algorithmic Subtyping") makes this very explicit: the
algorithm pushes both sides to a WHNF (call it "weak head reduction of types"),
then dispatches on the head pair. β is in the reduction, not in the subtyping
rule.

#### 6.5 Coercive subtyping (Luo)

- Zhaohui Luo. **"Coercive Subtyping in Type Theory"**. CSL 1996, LNCS 1258.
  [Springer PDF](https://link.springer.com/content/pdf/10.1007/3-540-63172-0_45.pdf).
- Yong Luo et al. **"On Subtyping in Type Theories with Canonical Objects"**.
  TYPES 2016. [DROPS](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.TYPES.2016.13).

Luo's *coercive subtyping* takes the opposite design: subtyping is not a relation
on terms at all; it's a *coercion-insertion* mechanism that runs at the elaborator
level. The kernel sees only conversion. This is even further from Och than the
mainstream architecture is.

### Equirecursion / recursive types in subtyping

This is essentially a **non-dependent** topic. Brandt & Henglein, *"Coinductive
Axiomatization of Recursive Type Equality and Subtyping"*, Fundamenta Informaticae
33(4), 1998, [DOI 10.3233/FI-1998-33401](https://journals.sagepub.com/doi/10.3233/FI-1998-33401),
gave the canonical sound-and-complete coinductive axiomatisation. Decision procedures
based on simulation/bisimulation date back further (Amadio-Cardelli, Kozen-Palsberg-
Schwartzbach). None of these are in dependent type theories; they are at the
type-level for languages like F<: with `μ`.

For F-omega with equirecursion: Cai, Giarrusso, Ostermann, *"System F-omega with
Equirecursive Types for Datatype-Generic Programming"*, POPL 2016,
[PDF](https://ps.informatik.uni-tuebingen.de/research/functors/equirecursion-fomega-popl16.pdf).
This is not dependent, and even at this level the conversion needs careful
handling: equirecursive `μ` interacts with β at the type level, and the algorithm
is non-trivial.

The key technical observation: in equirecursive systems, conversion is decided
by **bisimulation up to unfolding**, not by reduction-to-WHNF. This *is* a case
where reduction-style rules are inside the conversion relation — but the relation
is coinductive, not inductive, and decidability requires a contractivity side
condition.

If Och wants equirecursion *and* β inside subtyping, the closest precedent is
this body of work, but the dependent-type setting is essentially uncharted.

---

## 7. Cross-system summary

| System | Reduction in subtype rules? | Value rep | Equirec | Non-term | Conv file |
|--------|------------------------------|-----------|---------|----------|-----------|
| **Coq kernel** | No (cumul closes at boundary) | `term` from `whd_all` | None | Forbidden upstream (axiom SN) | `kernel/reduction.ml` |
| **Lean 4** | No | `Expr` from `whnf` | None | **Allowed**, fuel = 1000 | `src/kernel/type_checker.cpp` |
| **Agda** | No | `Term` from `reduceB` (with `Blocked` wrapper) | Copatterns/sized; not equirec | Forbidden upstream | `Agda/TypeChecking/Conversion.hs` |
| **MetaCoq / PCUIC** | No (formal `cumul_red_l/r` only) | `(term, stack)` zipper | None | Axiom of SN | `safechecker/.../PCUICSafeConversion.v` |
| **Abel typed NbE** | No (β in evaluator, ≤ in read-back) | Explicit `D / Dⁿᵉ / Dⁿᶠ` algebra | Sized types | Forbidden upstream | Habil Ch. 4 |
| **Zwanenburg PTS+≤** | No | `term` | None | SN required | TLCA 1999 |
| **Yang/Oliveira λI≤** | **Yes in the declarative judgement**, no in the algorithm | `term` | None | SN | OOPSLA 2017 |
| **Pierce F<:_ω** | No (algorithmic; β at type-level reduces to WHNF) | type-WHNF | None | SN at type level | TAPL § 31.4 |
| **Brandt-Henglein equirec** | Yes (coinductive, bisim) | (no separate value) | **Yes** (the point) | Decidable via contractivity | Fund. Inf. 33(4) 1998 |
| **Och (current)** | **Yes** (β rules inside `⊑`) | `term` | (planned) | (allowed) | `src/Och/Sub.lean` |

---

## 8. What this means for Och

Och is, at the moment, the only dependent calculus I found that puts β-redexes
*structurally* inside its subtyping relation rather than at the boundary. The
closest published precedents are:

1. **Brandt & Henglein** — but coinductive, non-dependent, and with explicit
   contractivity guards.
2. **Yang & Oliveira λI≤** — declaratively unifies typing + subtyping with β
   inside, but the algorithmic story (PhD thesis 2024) reduces to the standard
   "WHNF-then-compare" pattern.
3. The coercive subtyping tradition (Luo) is the *opposite* design and is the
   other natural option for a future Och.

### What Och's choice (β-inside-⊑) buys

- **A single relation to reason about.** No separation between "is convertible"
  and "is a subtype". This is genuinely simpler in metatheoretical statements:
  you don't have to prove "subtyping respects conversion" as a separate lemma.
  This is precisely Yang & Oliveira's selling point.
- **No commitment to a specific reduction strategy.** β rules inside `⊑` mean
  the relation is closed under arbitrary β; the algorithmic question of *when*
  to fire β is a separate matter. (Other systems also have this property at the
  declarative level; the algorithmic level is where they pin the strategy.)
- **Cleanly accommodates non-termination.** If the relation is declarative and
  inductively/coinductively defined, β-inside-⊑ doesn't care whether reduction
  terminates; the algorithm has to. PCUIC sidesteps this by axiomatising SN. Lean
  sidesteps with fuel. Och has a third option open.

### What Och's choice costs

- **The structural rules of `⊑` are no longer pattern-matching on a finite set
  of head shapes.** Every introduction rule of `⊑` has to consider whether
  *either side* has a β-redex, which means the rule set is much larger and
  trickier to invert. Lambda inversion in `⊑` becomes the central technical
  challenge — exactly what your `eval-preservation` blocker is about.
- **Confluence becomes load-bearing.** If β is in `⊑`, then the meta-theorems
  about `⊑` (transitivity especially) lean on confluence-style arguments. PCUIC
  proves confluence as a *separate* theorem before even defining algorithmic
  conversion (Coq Coq Correct § 2.3, lines 446–627); this allows the conversion
  algorithm to be straightforward. With β-in-⊑ you typically have to interleave
  the proofs.
- **Algorithm derivation is harder.** Every other system can specify "the
  algorithm" as "compute WHNF, dispatch on head, recurse" because the
  structural rules of `≡` already pattern-match on heads. With β-in-⊑, the
  declarative rules don't tell you when to stop reducing; you have to add an
  external strategy (i.e., go full Norell § 1.4 anyway).
- **Zwanenburg's circularity warning applies.** Subtyping that depends on β
  depends on substitution, which (in dependent types) depends on typing, which
  depends on subtyping. PCUIC mostly avoids this because `cumul_refl` is
  syntactic. Och has to navigate it carefully (compare the soundness blocker
  notes in `docs/research/eval-preservation.md`).

### Concrete recommendations from the survey

Based on the prior art, the two architectures with the strongest published
metatheory are:

- **PCUIC's "cumul closes at the boundary"** (β as `⇝`, separately from `≤`), with
  the algorithm being WHNF + structural compare + lazy delta. Mechanically
  verified to be sound and complete in MetaCoq.
- **Abel's typed NbE** with an explicit `D / Dⁿᵉ / Dⁿᶠ` algebra and read-back. The
  conversion check is *decidable by construction* once you build the right
  PER model.

A third option, **Lean's "fuel-bounded reduction"**, is the closest match for
Och's "non-termination is allowed" stance. Lean keeps β outside `≡` but allows
non-terminating WHNF; the kernel guards with a fuel parameter and a
`deepRecursion` exception (Lean4Lean § 3.2.1, lines 826–836). This is by far
the best precedent for "non-termination tolerated by the kernel itself" and
suggests that **Och can keep its non-termination tolerance even if it moves β
out of `⊑`**.

If Och wants to keep β-in-⊑ (e.g. because of the Yang-Oliveira-style unification
benefits), the Brandt-Henglein coinductive style is a useful template, especially
combined with a contractivity / productivity side condition. Whether this is
worth the complexity vs going to a Lean-style fuel-bounded WHNF + structural
compare is the design call.

---

## Sources

### Coq / CCIC

- Coquand, Huet. "The Calculus of Constructions". *Information and Computation* 76(2-3), 1988. [INRIA RR-0530](https://hal.inria.fr/inria-00076024).
- Paulin-Mohring. "Inductive Definitions in the System Coq". TLCA 1993, LNCS 664.
- Barras. "Coq en Coq". INRIA RR-3026, 1996.
- Timany, Sozeau. "Cumulative Inductive Types in Coq". FSCD 2018.
- Rocq reference manual, [§ 4 Conversion rules](https://coq.github.io/doc/v8.18/refman/).
- [`coq/kernel/reduction.ml`](https://github.com/coq/coq/blob/master/kernel/reduction.ml).
- [`coq/kernel/reduction.mli`](https://github.com/coq/coq/blob/master/kernel/reduction.mli).
- [`coq/kernel/conversion.ml`](https://github.com/coq/coq/blob/master/kernel/conversion.ml).
- [`coq/kernel/constr.ml`](https://github.com/coq/coq/blob/master/kernel/constr.ml).
- Bonichon, Delahaye, Doligez. "Reduction and Conversion Strategies for the Calculus of (Co)Inductive Constructions". ENTCS, 2007. [PDF](https://www.sciencedirect.com/science/article/pii/S157106610700401X).

### Lean 4

- Carneiro. *The Type Theory of Lean*. M.S. thesis, CMU 2019. [github.com/digama0/lean-type-theory](https://github.com/digama0/lean-type-theory/releases).
- de Moura, Ullrich. "The Lean 4 Theorem Prover and Programming Language". CADE 2021, LNCS 12699. [PDF](https://pp.ipd.kit.edu/uploads/publikationen/demoura21lean4.pdf).
- Carneiro. "Lean4Lean: Verifying a Typechecker for Lean, in Lean". [arXiv:2403.14064](https://arxiv.org/abs/2403.14064), 2024.
- Goens, Graf, Breitner et al. "Lean4Less". ITP 2025. [DOI](https://link.springer.com/chapter/10.1007/978-3-032-11176-0_13).
- Kindelsberger et al. "Lean-Auto: An Interface Between Lean 4 and Automated Theorem Provers". CADE 2025. [arXiv:2505.14929](https://arxiv.org/abs/2505.14929).
- [`lean4/src/kernel/type_checker.cpp`](https://github.com/leanprover/lean4/blob/master/src/kernel/type_checker.cpp).
- [`digama0/lean4lean`](https://github.com/digama0/lean4lean).
- Ammkrn. "Type Checking in Lean 4: [Definitional Equality](https://ammkrn.github.io/type_checking_in_lean4/type_checking/definitional_equality.html)".

### Agda

- Norell. *Towards a Practical Programming Language Based on Dependent Type Theory*. PhD thesis, Chalmers, 2007. [PDF](https://www.cse.chalmers.se/~ulfn/papers/thesis.pdf).
- Abel, Coquand. "Untyped Algorithmic Equality for Martin-Löf's Logical Framework with Surjective Pairs". TLCA 2005.
- Abel, Coquand, Pagano. "A Modular Type-Checking Algorithm for Type Theory with Singleton Types and Proof Irrelevance". LMCS 2011 / TLCA 2009. [LMCS](https://lmcs.episciences.org/1069).
- Abel, Öhman, Vezzosi. "Decidability of Conversion for Type Theory in Type Theory". POPL 2018.
- Abel. "MiniAgda: Integrating Sized and Dependent Types". PAR 2010.
- Abel, Pientka. "Wellfounded Recursion with Copatterns and Sized Types". JFP 26, 2016.
- [`Agda/TypeChecking/Conversion.hs`](https://github.com/agda/agda/blob/master/src/full/Agda/TypeChecking/Conversion.hs).
- [`Agda/TypeChecking/Reduce.hs`](https://github.com/agda/agda/blob/master/src/full/Agda/TypeChecking/Reduce.hs).
- [`Agda/TypeChecking/Reduce/Fast.hs`](https://github.com/agda/agda/blob/master/src/full/Agda/TypeChecking/Reduce/Fast.hs).
- [`Agda/TypeChecking/Conversion/Pure.hs`](https://github.com/agda/agda/blob/master/src/full/Agda/TypeChecking/Conversion/Pure.hs).

### MetaCoq / PCUIC

- Sozeau, Anand, Boulier, Cohen, Forster, Kunze, Malecha, Tabareau, Winterhalter. "The MetaCoq Project". *JAR* 64, 2020. [Springer](https://link.springer.com/article/10.1007/s10817-019-09540-0).
- Sozeau, Boulier, Forster, Tabareau, Winterhalter. "Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq". POPL 2020. [PDF](https://theowinterhalter.github.io/res/POPL20-coq-coq-correct.pdf).
- Sozeau, Forster, Lennon-Bertrand, Nielsen, Tabareau, Winterhalter. "Correct and Complete Type Checking and Certified Erasure for Coq, in Coq". *JACM* 2025. [DOI 10.1145/3706056](https://dl.acm.org/doi/10.1145/3706056).
- [github.com/MetaCoq/metacoq](https://github.com/MetaCoq/metacoq) ; new home [github.com/MetaRocq/metarocq](https://github.com/MetaRocq/metarocq).
- [`PCUICSafeReduce.v`](https://metacoq.github.io/v1.2-8.16/MetaCoq.SafeChecker.PCUICSafeReduce.html).
- [`safechecker/theories/`](https://github.com/MetaCoq/metacoq/tree/coq-8.16/safechecker/theories).

### Abel NbE work

- Abel. *Normalization by Evaluation: Dependent Types and Impredicativity*. Habilitation, LMU München, 2013. [PDF](https://www.cse.chalmers.se/~abela/habil.pdf).
- Abel, Aehlig, Dybjer. "Normalization by Evaluation for Martin-Löf Type Theory with Typed Equality Judgements". LICS 2007.
- Abel, Coquand, Dybjer. "Normalization by Evaluation for Martin-Löf Type Theory with One Universe". MFPS 2007.
- Altenkirch, Kaposi. "Normalisation by Evaluation for Dependent Types". FSCD 2016. [DROPS](https://drops.dagstuhl.de/opus/volltexte/2016/5972/pdf/LIPIcs-FSCD-2016-6.pdf).
- Abel, Vezzosi, Winterhalter. "Normalization by Evaluation for Sized Dependent Types". ICFP 2017. [DOI](https://dl.acm.org/doi/10.1145/3110277).
- Schwichtenberg, Berger. Original NbE references; see Abel Habil Ch. 1 for history.

### PTS / declarative subtyping with β

- Zwanenburg. "Pure Type Systems with Subtyping". TLCA 1999, LNCS 1581. [Springer](https://link.springer.com/chapter/10.1007/3-540-48959-2_27).
- Zwanenburg. *Object-Oriented Concepts and Proof Rules*. PhD, TU Eindhoven, 1999.
- Aspinall. *Subtyping Dependent Types*. LFCS-97-370, Edinburgh, 1997. [PDF](http://www.lfcs.inf.ed.ac.uk/reports/97/ECS-LFCS-97-370/ECS-LFCS-97-370.pdf).
- Aspinall, Compagnoni. "Subtyping Dependent Types". *TCS* 266, 2001.
- Yang, Oliveira. "Unifying Typing and Subtyping". OOPSLA 2017. [PDF](https://i.cs.hku.hk/~bruno/papers/oopsla17.pdf).
- Yang. *Simple Dependent Type Theories for Programming*. PhD thesis, HKU 2024. [PDF](https://i.cs.hku.hk/~bruno/thesis/YanpengYang.pdf).
- Luo. "Coercive Subtyping in Type Theory". CSL 1996. [PDF](https://link.springer.com/content/pdf/10.1007/3-540-63172-0_45.pdf).
- Luo et al. "On Subtyping in Type Theories with Canonical Objects". TYPES 2016. [DROPS](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.TYPES.2016.13).
- Pierce. *Types and Programming Languages*. MIT Press 2002, Chapters 26–28, § 31.4.
- Cardelli, Wegner. "On Understanding Types, Data Abstraction, and Polymorphism". *Computing Surveys* 17(4), 1985.
- Cardelli. "An Extension of System F with Subtyping". *Information and Computation* 109, 1994. [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0890540184710133).
- Compagnoni, Goguen. "Anti-Symmetry of Higher-Order Subtyping". CSL 1999.

### Equirecursion / recursive types

- Brandt, Henglein. "Coinductive Axiomatization of Recursive Type Equality and Subtyping". *Fundamenta Informaticae* 33(4), 1998. [DOI](https://journals.sagepub.com/doi/10.3233/FI-1998-33401).
- Amadio, Cardelli. "Subtyping Recursive Types". *TOPLAS* 15(4), 1993.
- Cai, Giarrusso, Ostermann. "System F-omega with Equirecursive Types for Datatype-Generic Programming". POPL 2016. [PDF](https://ps.informatik.uni-tuebingen.de/research/functors/equirecursion-fomega-popl16.pdf).
- Ligatti, Blackburn, Nachiappan. "On Subtyping-Relation Completeness, with an Application to Iso-Recursive Types". *TOPLAS* 39(1), 2017.
- Yang, Lyu, Oliveira. "Full Iso-recursive Types". OOPSLA 2024. [arXiv:2407.00941](https://arxiv.org/html/2407.00941v2).
