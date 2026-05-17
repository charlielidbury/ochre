# Literature Review: Liskov-Style Substitutability in Dependently-Typed Subtyping

## Executive Summary

There is **no unified Liskov substitutability theorem** in the dependently-typed
subtyping literature; instead, every working system pays for the negative-position
problem with a specific design concession. The dominant strategies are: (1) restrict
the subtyping relation to **types only**, never values, so dependence on a value never
forces "subtype substitution under a binder" (Coq's cumulativity, Aspinall-Compagnoni
λP≤); (2) make the function-domain rule **invariant** rather than contravariant, so the
domain type cannot vary under the binder (Coq, Compagnoni's λP≤); (3) split the system
into a **declarative subsumption rule plus a separate algorithmic procedure**, and
prove that the two coincide modulo a narrowing/transitivity lemma (DOT,
Aspinall-Compagnoni); (4) replace subsumption with **coercive subtyping**, where every
"a : A ⊑ B implies a : B" is mediated by an explicit coercion that you transport along
identity paths (Luo's coercive subtyping, MetaCoq, the recent "Definitional
Functoriality" work, HoTT's transport); (5) reduce subtyping to **logical implication
between refinements over a common base type** so that there is no negative-position
problem about the base type (Liquid Haskell, F\*). The systems that get closest to
"pure structural Liskov on dependent types" — DOT, λP≤, Aspinall's singleton calculus —
all pay for it with a substantial narrowing-and-transitivity proof obligation, and DOT
in particular has subtyping that is **undecidable** as the price.

## The Negative-Position Problem, Precisely

Fix a dependent type theory with a binary subtyping relation `A ⊑ B`. The "naive"
Liskov rule is the **subsumption rule**:

    Γ ⊢ a : A    Γ ⊢ A ⊑ B
    -----------------------                 (Sub)
    Γ ⊢ a : B

This is the form the Liskov substitution principle takes in a typed lambda-calculus:
"if `A ⊑ B`, then any program `Γ ⊢ a : A` is also a program at `B`." The user's example
exhibits the failure mode of any *direct* generalisation of (Sub) to the *type
constructors* of a dependent calculus. Concretely, suppose

- `BoolFalse ⊑ Bool` (refinement: only `false` inhabits `BoolFalse`).
- `k : (Bool → Type)` and `k true : Type` is well-formed.

The "obvious" Liskov claim that `Bool → Type` is below `BoolFalse → Type` (covariant in
codomain, contravariant in domain) is wrong: a function that needs an arbitrary `Bool`
cannot be replaced by one that only handles `false`. So the contravariance direction is
fine. The *opposite* direction — `BoolFalse → Type ⊑ Bool → Type` — is also generally
not what a structural rule would give, even though it would let us claim
`(λ b ⇒ T) : Bool → Type` from a definition that only worked on `false`. The deeper
problem is that under a binder `x : A`, occurrences of `x` may appear at types whose
*shape* depends on the value of `x`. Substituting a subtype `A' ⊑ A` for `A` in such a
type changes which *terms* are allowed at that position. This is what Aspinall &
Compagnoni call the "intimate tangling" of typing and subtyping in dependent settings
[Aspinall & Compagnoni 1996/2001].

Three concrete consequences:

1. **The substitution lemma is no longer trivial.** In a non-dependent system, "if
   `Γ, x:A ⊢ b : B` and `Γ ⊢ a : A` then `Γ ⊢ b[a/x] : B`" is one line. In a dependent
   system with subsumption, you need it for *narrowing*: "if `Γ, x:A ⊢ J` and
   `Γ ⊢ A' ⊑ A`, then `Γ, x:A' ⊢ J`." But narrowing under a Pi type forces you to
   reason about what subsumption does to the codomain *under* the new variable, where
   the codomain may mention `x` at non-trivial dependent shapes.

2. **Transitivity and narrowing become mutually recursive.** This is the famous
   pathology of System F<: that, when generalised to the dependent setting, makes
   subtyping outright undecidable in DOT [Amin–Rompf–Odersky 2016] and motivates the
   use of *algorithmic* subtyping followed by a soundness/completeness theorem for
   declarative subtyping (Aspinall–Compagnoni's "transitivity elimination").

3. **Subject reduction modulo subtyping** is no longer an automatic corollary of
   progress and preservation; it requires a separate proof that reductions inside a
   term do not change the term's *minimal* type, which in a system with subsumption
   means the *least supertype admissible by every derivation*. Several systems
   (e.g. λP≤, λI≤) prove this by first stripping subsumption to an algorithmic system,
   then proving that the algorithmic system is sound and complete for the declarative
   one.

Notice that "use a coercion" is *also* a way of handling the problem — the substitution
`b[a/x]` is replaced by `b[coerce A' A a / x]`, and the transport semantics carries the
burden of preservation. We list this as one of the design strategies below.

## System-by-System Summary

### Coq / CIC (Cumulativity, Sozeau et al, MetaCoq)

Coq's subtyping is **cumulativity** — a relation `T ≤_{βδιζη} U` that is essentially
*definitional equality plus universe-level extension*. The defining clauses, quoting
the Coq 8.18 reference manual on the Calculus of Inductive Constructions:

- `t =_{βδιζη} u  ⇒  t ≤_{βδιζη} u`
- `Type(i) ≤_{βδιζη} Type(j)` if `i ≤ j`
- `Set ≤_{βδιζη} Type(i)`, `Prop ≤_{βδιζη} Set`
- For dependent products: **`∀x:T, T' ≤_{βδιζη} ∀x:U, U'` requires `T =_{βδιζη} U`
  (definitional equality on the domain) and `T' ≤_{βδιζη} U'` in the extended context.**

Coq deliberately makes the domain of a Pi type **invariant**, not contravariant. This
is the cleanest way to dodge the negative-position problem: subtyping never propagates
into a binder *where it could change which inhabitants are allowed*. Subsumption is
then taken as a primitive rule (the "Conv" rule of CIC):

> If `Γ ⊢ U : s`, `Γ ⊢ t : T`, and `Γ ⊢ T ≤_{βδιζη} U` then `Γ ⊢ t : U`.

Cumulative inductive types (Timany–Sozeau, "Cumulative Inductive Types in Coq", 2017)
extend this with annotated variance per universe parameter — *but only over universes,
never over data*. The MetaCoq project (Sozeau et al, 2020) has a fully mechanized proof
that this system enjoys subject reduction; the proof routes through PCUIC (Polymorphic
Cumulative Calculus of Inductive Constructions) and crucially exploits that
cumulativity is a relation on *types* and that it commutes with conversion. There is no
direct "Liskov" theorem at all — Liskov substitutability is the **Conv rule itself**,
admissible because subtyping is a refinement of definitional equality.

### Agda

Agda's subtyping is a strict subset of Coq's. Universes are cumulative *only when the
`--cumulativity` flag is on* — otherwise universe levels are explicitly polymorphic
[Agda manual, "Universe Levels"]. The other forms of subtyping are **for irrelevance and
modalities**: with `--subtyping`, the rule `.(x:A) → B <: (x:A) → B` lets a relevant
function be used where an irrelevant one is expected (Abel–Vezzosi, "Decidability of
Conversion for Type Theory in Type Theory", 2018; Atkey, "Syntax and Semantics of
Quantitative Type Theory", 2018). Agda has **no** value-level subtyping, no refinement
types, and no contravariant Pi rule. The substitutability theorem is once again
trivially admissible because the relation is on types and is absorbed into definitional
equality. Notably, Agda's irrelevance subtyping crosses positive/negative boundaries —
`.(x:A) → B <: (x:A) → B` *does* push subtyping under a binder — but the ordering is
about computational availability of the argument, not about the set of inhabitants, so
no negative-position pathology arises.

### Lean 4

Lean 4 does **not** have a built-in subtyping judgment. What looks like subtyping is
either (a) **universe cumulativity**, similar to Coq's; (b) **definitional eta**
(structures with eta laws are interconvertible with their projections); or (c)
**coercions**, mediated by the `CoeFun` / `Coe` type class hierarchy [Lean documentation,
"Coercions"]. The latter is purely *coercive* in Luo's sense: there is no subsumption
rule, only synthesised coercion terms. Liskov-style substitutability is therefore
**replaced by definitional equality on the synthesised term**. The Lean ecosystem has
encountered the standard Luo problem — that one term may admit two different coercion
paths to the same type, and these must agree definitionally for the elaboration to be
coherent. Issue tracking on the Lean repo for `Coe`/`CoeFun` reflects exactly this
problem (e.g. lean4#403 on coercion coherence, lean4#777 on definitional eta for
structures).

### F\*

F\* combines Hoare-logic style refinement types `x:t{φ}` with a complex effects system
[Swamy et al, "Dependent Types and Multi-Monadic Effects in F\*", POPL 2016]. The core
subtyping decisions are:

- **Refinement subsumption is reduced to logical implication:** `x:t{φ} ⊑ x:t{ψ}` if
  `φ ⇒ ψ` is valid in the SMT theory of the base type `t`.
- **Function subtyping is contravariant in the domain (refined) and covariant in the
  codomain.** The binder of the domain is *available* in the codomain comparison: if
  `(x : A₂) → B₁ ⊑ (x : A₁) → B₂` requires `A₁ ⊑ A₂` plus `B₁ ⊑ B₂` *in the context
  `x : A₁`*.
- **The negative-position monotonicity problem is solved by SMT validity checking**:
  the subtyping judgment `Γ ⊢ A ⊑ B` is reduced to a verification condition, and
  validity of an implication is monotone under strengthening assumptions. The original
  refinement-types-for-Haskell paper (Vazou et al 2014) and its F\* analogues both note
  that a *typing* judgment cannot appear in negative position of subtyping without
  breaking monotonicity, so the SMT-encoding restricts to first-order implication
  between *uninterpreted refinements* over a common base.

The recent "Mechanizing Refinement Types" paper [Lehmann, Geuvers, et al., POPL 2024,
DOI 10.1145/3632912] mechanizes the metatheory of a core refinement calculus and
explicitly notes that "earlier refinement type systems exhibited non-monotonicity when
typing appeared in the left-hand side of subtyping, making the proof impossible due to
the typing judgment occurring in a negative position in the implication judgment". The
solution there is to *separate* subtyping from typing carefully, so that the relation
remains monotone in the context.

The F\* "substitutability" theorem is therefore **subsumption-by-implication** plus a
preservation theorem proved separately for the operational semantics. The Liskov
property holds *only* on logical predicates over a fixed base, never on type
constructors that change shape.

### Cedille / CDLE

Cedille is built on the Calculus of Dependent Lambda Eliminations (CDLE), which has
**three main type formers beyond CC**: dependent intersection `ι x:A. B`, equality
types `{a ≃ b}`, and implicit (erased) products `∀x:A. B` [Stump, "From Realizability to
Induction via Dependent Intersection"; Marmaduke–Jenkins–Stump, "Zero-Cost Constructor
Subtyping", 2021]. There is no traditional subtyping relation. Instead:

- The implicit product `∀x:A. B` is the *erasure* of `(x:A) → B`, and behaves as a kind
  of subset.
- Intersection types `ι x:A. B` let a single term simultaneously inhabit two views,
  which gives many of the practical benefits of subtyping (e.g. zero-cost casts between
  representations).
- Subsumption is replaced by **definitional equality on erasures**: two terms that
  erase to the same untyped term may be used at any types they each inhabit.

The "Zero-Cost Constructor Subtyping" paper specifically shows how the subtyping
between two inductive families can be implemented by *constructing a coercion that
erases to the identity*, so the runtime cost is zero — but the *coercion itself* is the
mechanism, not a subsumption rule. The Liskov property is replaced by **provable
extensional equality**, which is propositional rather than typing-judgment-based. This
sidesteps the negative-position problem entirely: there is nothing to "substitute"
because the relation isn't a typing relation.

### Aspinall's Singleton Calculus

Aspinall's "Subtyping with Singleton Types" (CSL'94) presents a typed lambda calculus
with subtyping and **singleton types** `{M}`, where `{M}` is the unique type inhabited
only by terms convertible with `M`. Subsumption becomes available between any
`{M}` and the type of `M`, and singletons embed *abbreviational definitions* into the
type system. This is the **prototypical "minimal calculus of subtyping with a simple
form of dependent types"**.

The technical machinery: Aspinall proves that the system is consistent via a PER
(partial equivalence relation) model, and that adding singletons is a *non-conservative*
extension — strictly more terms become typable, and existing terms gain *additional*
non-dependent types. The substitutability story is:

- For type subtyping, rules are standard (covariant/contravariant on functions).
- For singleton-into-type subtyping, the rule `{M} ⊑ A` whenever `M : A`. This is
  "Liskov substitution restricted to a singleton on the left."

Aspinall's later "Subtyping Dependent Types" (LFCS-97-370, with Compagnoni) extends
this to full λP. The crucial design decisions there are:

1. The rule for Pi subtyping uses **subtyping on the domain** (i.e., true contravariant
   structural subtyping, not Coq-style invariance), but
2. The system requires both a **transitivity-elimination theorem** and a **narrowing
   lemma**, proved by a non-trivial mutual induction with subject reduction.
3. The substitution lemma is proved by induction on subtyping derivations and uses
   narrowing as a hypothesis.

This is the *deepest* engagement in the literature with the negative-position problem
in a "pure" structural setting. The proof technique (transitivity elimination via an
algorithmic system, then narrowing) is the template followed by DOT and λI≤.

### Refinement Types in General (Liquid Haskell)

Vazou et al's "Refinement Types for Haskell" (ICFP 2014) gives the prototypical
refinement-subtyping rule:

- **Sub-Base**: `Γ ⊢ ∀v:b. φ₁ ⇒ φ₂  ⊢  {v:b | φ₁} ⊑ {v:b | φ₂}`. Subtyping on a common
  base type reduces to logical implication of the refinements.
- **Sub-Fun**: `Γ ⊢ τ_{x₂} ⊑ τ_{x₁}` and `Γ; x₂:τ_{x₂} ⊢ τ₁[x₁/x₂] ⊑ τ₂  ⊢
  (x₁:τ_{x₁}) → τ₁ ⊑ (x₂:τ_{x₂}) → τ₂`. Domain is contravariant; codomain is checked
  *under the stronger argument*.

The negative-position problem is solved by the discipline that **the refinement
language is first-order**: the predicates `φ` are SMT-decidable formulas, not arbitrary
type-theoretic propositions. Substitutability is "validity of a logical implication",
which is monotone in assumptions. The substitution lemma reduces to: "validity of a
formula in a stronger logical context". The "How to Safely Use Extensionality in Liquid
Haskell" paper (Vazou et al 2021, arXiv:2103.02177) details how introducing
proposition-level extensionality breaks the simple monotonicity argument, because
typing then leaks into the implication.

### DOT / pDOT (Path-Dependent Types in Scala)

DOT (Amin–Grütter–Odersky–Rompf–Stark, "The Essence of Dependent Object Types") is the
calculus underlying Scala 3. It has *path-dependent types* `x.A`, dependent function
types, and intersection types. The subtyping relation is:

- Reflexive, transitive (as a primitive rule).
- **Function rule**: `(x:S₁) → T₁ ⊑ (x:S₂) → T₂` if `S₂ ⊑ S₁` *and* `T₁ ⊑ T₂` in the
  extended context. (Standard contravariant.)
- **Path-selection rules** that exploit object members at a path.

DOT is the system that exhibits the **most dramatic negative-position pathology**:
subtyping is *undecidable* (it can encode F<:), and the soundness proof must
simultaneously handle subtype transitivity and environment narrowing. Amin–Rompf 2017
shows that decidable type *checking* is recoverable in fragments, and pDOT
[Rapoport–Lhoták, OOPSLA 2019, arXiv:1904.07298] generalizes to fully path-dependent
types but at the cost of significant proof complexity.

The substitutability theorem in DOT is **subject reduction proved via tight typing** —
a tightening of the typing judgment that enjoys narrowing and transitivity by
construction, then connected to the declarative system. This is essentially the same
strategy as Aspinall–Compagnoni: separate algorithmic from declarative, prove they
agree.

### Coercive Subtyping (Luo) and Definitional Functoriality

Luo's coercive subtyping ("Coercive Subtyping in Type Theory", 1997; "Coercive
Subtyping: Theory and Implementation", I&C 2012) takes a different tack: there is *no*
subsumption rule. Instead, every claim "`A ⊑ B`" is justified by giving an explicit
coercion `c : A → B`. The substitutability is then: `b[a/x]` becomes `b[c(a)/x]` when
`x : A` is replaced by `x : B` via `A ⊑ B`. The system is conservative over the base
type theory: every term in `T[C]` can be elaborated to a term in `T`.

The price: **coherence**. Different derivations of `A ⊑ B` may give different
coercions. Luo's framework requires that all such coercions be *definitionally equal*.

The recent "Definitional Functoriality for Dependent (Sub)Types"
[Lennon-Bertrand–Tabareau–Tanter, ESOP 2024, arXiv:2310.14929] resolves the standard
pathology where coercive subtyping fails to compose definitionally through type
formers like `List` or `Vec`. Their key contribution: extend MLTT with **definitional
functor laws** for container types (i.e., `map id = id`, `map f ∘ map g = map (f ∘ g)`
become definitional equations). With these, **structural coercive subtyping is proved
equivalent to subsumptive subtyping**. This is, to date, the cleanest treatment of
"Liskov for dependent types": Liskov substitutability holds definitionally, *but only
because the type theory has been strengthened to make container functoriality
definitional*. The earlier Coraglia–Emmenegger work on generalized categories with
families gives the categorical-semantics analogue.

This is the strategy that HoTT also takes, with `transport`: given `p : A = B`, the
function `transport p : A → B` is the coercion, and substitutability is mediated by
path induction. There is no direct subtyping; everything is propositional equality.

## Pattern Catalog

Five distinct strategies emerge across the literature for handling Liskov in
dependently-typed subtyping. They are essentially orthogonal axes of the design space.

### Pattern 1: Restrict subtyping to types only; make Pi-domain invariant

**Examples:** Coq/CIC, Agda (with cumulativity flag).

**Mechanism:** The subtyping relation is defined to coincide with definitional equality
on every position except universes. The Pi rule requires `T =_{βδιζη} U` on the domain
(no subtyping under the binder), and the codomain may grow only by raising universe
levels. The "negative-position" problem is dodged because subtyping never changes the
*set of inhabitants* of the domain — only the *level* of an unused universe annotation.

**Liskov form:** Subsumption (Conv rule) is primitive. The substitution lemma holds
trivially because subtyping is a refinement of conversion, which already commutes with
substitution.

**Pros:** Decidable, clean, mechanizable. Coq's PCUIC is fully formalized in MetaCoq.
**Cons:** Severely limits expressiveness. No refinement subtyping, no value-level
subtyping, no structural Pi contravariance.

### Pattern 2: Algorithmic-declarative split with narrowing + transitivity-elimination

**Examples:** Aspinall–Compagnoni's λP≤, λI≤, DOT/pDOT.

**Mechanism:** The declarative system has subsumption and structural rules including
contravariant Pi, but subtyping is *not* directly verified by the declarative rules.
Instead, an *algorithmic* system without (or with restricted) transitivity is given,
and proven equivalent. The narrowing lemma — that typing is preserved when a context
binding is replaced by a subtype — is proved by mutual induction with transitivity
elimination.

**Liskov form:** Subsumption is admissible in the algorithmic system. Subject reduction
is proved separately, often via a "minimal type" argument: every well-typed term has a
minimal type, and reduction either preserves it or moves to a smaller one.

**Pros:** Most expressive structural dependent subtyping. Handles full contravariant
Pi.
**Cons:** Subtyping is undecidable in the worst case (DOT). Proofs are deep —
narrowing-and-transitivity are mutually recursive and each step must respect the
algorithmic-declarative gap.

### Pattern 3: Coercive subtyping (replace subsumption with explicit coercion)

**Examples:** Luo's coercive subtyping framework, Lean 4 `Coe` machinery, parts of HoTT
(`transport`), the recent "Definitional Functoriality" work.

**Mechanism:** Every `A ⊑ B` is justified by a term `c : A → B`. Substitution
`b[a/x]` becomes `b[c(a)/x]`. The system is conservative over the base theory.
Substitutability is proved by giving the coercion; coherence by requiring that
different derivations of `A ⊑ B` yield definitionally equal coercions.

**Liskov form:** Subsumption is *not* a typing rule; it is a *meta-theorem* that says
any term can be transported to a supertype. The negative-position problem disappears
because nothing is being substituted — coercions are inserted at the call-site.

**Pros:** Very modular. Lifts cleanly to HoTT-style transport; integrates with
identity/path equality. The recent definitional-functoriality work shows that this can
be made to enjoy *definitional* subsumption equivalence.
**Cons:** Coherence is technically demanding. In the absence of definitional functor
laws, coercive subtyping does not compose under type formers definitionally
[Lennon-Bertrand et al, ESOP 2024]. Requires the type theory to have UIP or
definitional equality structure rich enough to discharge coherence.

### Pattern 4: Refinement-only subtyping reduced to logical implication

**Examples:** Liquid Haskell, F\*, refinement Haskell more generally.

**Mechanism:** Subtyping is allowed *only* between refinements over a common base type.
The base-type subtyping rule is "implication of refinements is valid in SMT". The
function rule is structurally contravariant/covariant, but the comparison happens at a
fixed base; nothing changes the *kind* of inhabitants, only the *predicate* over them.

**Liskov form:** Subsumption is admissible because logical implication is monotone in
the assumption context. The substitution lemma reduces to the soundness of strengthening
SMT contexts. The negative-position problem is **excluded by syntactic restriction**:
the refinement language is first-order, so "typing in negative position" cannot happen.

**Pros:** Decidable (modulo SMT). Proven sound for industrial-scale uses. The
"Mechanizing Refinement Types" paper (POPL 2024) provides full mechanization.
**Cons:** Cannot express subtyping between *type constructors* — only between
refinements thereof. No type-level polymorphism via subtyping. Cannot handle the user's
`BoolFalse ⊑ Bool` example unless `BoolFalse = {b:Bool | b = false}` is treated as a
refinement of `Bool`, in which case it falls under this pattern but inherits its
limits.

### Pattern 5: Replace subtyping with intersection/union/singleton machinery

**Examples:** Cedille (intersection), Aspinall's singleton calculus, DOT-style abstract
type members.

**Mechanism:** Instead of a primitive subtyping relation, give *type formers* whose
inhabitants are simultaneously at multiple types: dependent intersection
`ι x:A. B` (Stump), singleton `{M}` (Aspinall), or interval `T..U` (DOT lower-and-upper
type members). Substitutability becomes "this term inhabits this type, full stop" —
not "this term moves between types".

**Liskov form:** Subsumption is *replaced* by membership inference. The user does not
write `a : A ⊑ B`; they write `a : ι x:A. B` and use both projections.

**Pros:** Often gives more expressive systems than subsumption-based subtyping. Cedille
encodes induction, large eliminations, and zero-cost casts via this mechanism.
**Cons:** The user-level burden is higher: every "Liskov use" requires constructing or
projecting from an intersection/singleton. The negative-position problem is sidestepped
by having no substitution — but nothing prevents the analogue from showing up under
intersection-elimination.

## Implications for Och

The user's description of Och places it most squarely in **Pattern 2**
(algorithmic-declarative split, structural subtyping including contravariant Pi).
Och's stuck-application equivalence — i.e., that two stuck applications are equivalent
when their corresponding pieces are — is the dependent-subtyping analogue of
λP≤'s structural rule for neutral types. The closest literature analogues are
Aspinall–Compagnoni's λP≤ (with its narrowing + transitivity-elimination machinery)
and DOT (with its tight-typing approach), with the caveat that DOT is undecidable as
the price of full structural dependent subtyping.

If Och accepts contravariant Pi domains, the literature suggests three concrete things
to expect: (i) **narrowing and transitivity will be mutually recursive**, and the proof
will need to handle both via simultaneous induction or via a transitivity-elimination
step; (ii) **subject reduction modulo subtyping** will need a minimal-type argument or
equivalent, since direct preservation does not hold under naive subsumption; (iii) the
substitution lemma will have a guard — typically that the substituted value is at a
subtype of the binder. The user's example with `BoolFalse ⊑ Bool` and
`λk : Bool → *. k true` illustrates exactly the case where naive contravariant Pi
fails: under the binder, `Bool` is *not* freely substitutable for `BoolFalse` even
though one is below the other. The two literature responses are (a) accept this and add
narrowing as a primitive lemma (Aspinall–Compagnoni route), or (b) move to a coercive
formulation (Pattern 3) where the user-supplied subtyping witness becomes an actual
function that gets inserted at the right places. The "Definitional Functoriality" work
suggests Pattern 3 may give a cleaner story if Och can afford to bake the relevant
functor laws into definitional equality.

## References

1. **Aspinall, D.** "Subtyping with Singleton Types." *CSL'94*, LNCS 933, 1995.
   <https://homepages.inf.ed.ac.uk/da/papers/lss/>. Singletons + subtyping; the
   prototypical minimal dependent subtyping calculus.

2. **Aspinall, D., and Compagnoni, A.** "Subtyping Dependent Types." *LICS 1996*; ECS
   Tech Report LFCS-97-370, 1997.
   <http://www.lfcs.inf.ed.ac.uk/reports/97/ECS-LFCS-97-370/>. Adds subtyping to λP;
   the prototypical "deep" dependent subtyping with narrowing + transitivity-elimination.

3. **Compagnoni, A., and Goguen, H.** "Anti-Symmetry of Higher-Order Subtyping." *CSL
   1999*, LNCS 1683.
   <https://link.springer.com/chapter/10.1007/3-540-48168-0_30>. Higher-order F<:ω
   subtyping, foundational for understanding when subtyping coincides with conversion.

4. **Coq Development Team.** *The Coq Proof Assistant Reference Manual*. CIC subtyping
   rules in section "Calculus of Inductive Constructions / Typing Rules".
   <https://rocq-prover.org/doc/V8.18.0/refman/language/cic.html>. Source for
   cumulativity and Conv rule.

5. **Sozeau, M., et al.** "The MetaCoq Project." *J. Automated Reasoning* 64, 2020.
   <https://link.springer.com/article/10.1007/s10817-019-09540-0>. Full mechanization
   of CIC's typing including cumulativity and subject reduction.

6. **Timany, A., and Sozeau, M.** "Cumulative Inductive Types in Coq." *FSCD 2018*.
   <https://www.semanticscholar.org/paper/Cumulative-Inductive-Types-In-Coq-Timany-Sozeau/aa12300902c11462834de20ae6d1e1daa55dd0bd>.
   Variance annotations on universe parameters of inductive types.

7. **Swamy, N., et al.** "Dependent Types and Multi-Monadic Effects in F\*."
   *POPL 2016*. F\*'s core refinement/effect calculus.

8. **Lehmann, T., Geuvers, H., et al.** "Mechanizing Refinement Types."
   *POPL 2024 / PACMPL*, DOI 10.1145/3632912.
   <https://dl.acm.org/doi/10.1145/3632912>. Mechanizes a core refinement calculus,
   discusses the typing-in-negative-position monotonicity issue explicitly.

9. **Vazou, N., Seidel, E., Jhala, R., Vytiniotis, D., and Peyton Jones, S.** "Refinement
   Types for Haskell." *ICFP 2014*. <https://goto.ucsd.edu/~nvazou/refinement_types_for_haskell.pdf>.
   The Liquid-Haskell prototype; gives Sub-Base and Sub-Fun rules.

10. **Vazou, N., Tondwalkar, A., Choudhury, V., et al.** "How to Safely Use
    Extensionality in Liquid Haskell." 2021. <https://arxiv.org/abs/2103.02177>.
    Discusses negative-position issues that arise when typing meets implication.

11. **Stump, A.** "From Realizability to Induction via Dependent Intersection."
    *APAL 2018*. <https://dblp.org/pid/46/656.html>. Cedille's foundational use of
    dependent intersection.

12. **Marmaduke, A., Jenkins, C., and Stump, A.** "Zero-Cost Constructor Subtyping."
    *PEPM 2021*. <https://dl.acm.org/doi/pdf/10.1145/3462172.3462194>. Subtyping
    expressed as erasure-preserving coercions in Cedille.

13. **Miquel, A.** "The Implicit Calculus of Constructions." *TLCA 2001*.
    <https://link.springer.com/chapter/10.1007/3-540-45413-6_27>. Implicit (erased)
    products and intersection-style subtyping in CC.

14. **Luo, Z.** "Coercive Subtyping in Type Theory." *CSL 1996*, LNCS 1258.
    <https://link.springer.com/chapter/10.1007/3-540-63172-0_45>. The foundational
    coercive-subtyping paper.

15. **Luo, Z., Soloviev, S., and Xue, T.** "Coercive Subtyping: Theory and
    Implementation." *Information and Computation* 223, 2013.
    <https://www.sciencedirect.com/science/article/pii/S0890540112001757>. Long
    journal version with implementation experience.

16. **Lennon-Bertrand, M., Tabareau, N., and Tanter, É.** "Definitional Functoriality
    for Dependent (Sub)Types." *ESOP 2024*; extended version arXiv:2310.14929.
    <https://arxiv.org/pdf/2310.14929>. Resolves the structural composition problem
    for coercive subtyping by adding definitional functor laws.

17. **Amin, N., Grütter, S., Odersky, M., Rompf, T., and Stark, S.** "The Essence of
    Dependent Object Types." *Wadlerfest 2016 / OOPSLA 2016*.
    <https://www.cs.purdue.edu/homes/rompf/papers/amin-popl17a.pdf>. The DOT calculus,
    formal subtyping rules, soundness via tight typing.

18. **Rapoport, M., and Lhoták, O.** "A Path to DOT: Formalizing Fully Path-Dependent
    Types." *OOPSLA 2019*; arXiv:1904.07298. <https://arxiv.org/abs/1904.07298>.
    pDOT; soundness of full path-dependent types with singleton path equality.

19. **Pierce, B., and Turner, D.** "Local Type Inference." *POPL 1998 / TOPLAS 22(1)
    2000*. <https://www.cis.upenn.edu/~bcpierce/papers/lti-toplas.pdf>. Bidirectional
    typing with subtyping; foundation of the algorithmic-declarative split.

20. **Coraglia, G., and Emmenegger, J.** "From Semantics to Syntax: A Type Theory for
    Comprehension Categories." 2025; arXiv:2503.10868.
    <https://arxiv.org/pdf/2503.10868>. Categorical semantics of coercive subtyping in
    dependent type theory; gives a clean account of when coercive and subsumptive
    subtyping coincide.

21. **Univalent Foundations Program.** *Homotopy Type Theory: Univalent Foundations of
    Mathematics*, 2013. The `transport` operation as a coercion-like substitutability
    mechanism mediated by identity types.

22. **Agda Development Team.** *Agda Reference Manual*, "Universe Levels" and
    "Irrelevance" sections. <https://agda.readthedocs.io/>. Cumulativity flag and
    irrelevance subtyping.
