# PSS Type Safety: Alternative Approaches Analysis

## The Problem Recap

PSS type safety requires proving that well-typed closed terms don't get stuck.
The blocking lemma is **canonical forms**: `Sub Gamma Top (lam s t) -> False`,
and more generally, **lambda inversion**: `Sub Gamma (lam a b) (lam s t) -> Sub Gamma a s`.

Three approaches have been tried:
1. **Syntactic (CanonicalForms.lean)**: Height induction. The beta_L compose case
   (`trans h1 beta_L hw` where h1 has .app middle) doesn't decrease any measure.
   2 sorrys remain (both the same obstacle).
2. **MPSS (MPSS.lean)**: Continuation-stack reformulation. De Bruijn encoding creates
   scope mismatches. 4 of the sorry'd statements are provably FALSE. The remaining
   sorrys (substitution, weakening, diamond ME-PRO+ME-PRO) are plausibly true but
   require substantial infrastructure.
3. **Logical relation (LogRel.lean + SafeLogRel.lean)**: Step-indexed semantic model.
   `concEval_safe` is proved with zero sorry, BUT it depends on `lam_sub_lam_inversion`
   as an axiom. `fundamental_subSem` has 4 sorrys (lam, app_cong, beta_L, beta_R).

The recurring pattern: **Sub derivations involving beta-redexes resist inductive analysis**.
The trans rule composes two derivations through a middle term, and when that middle
term is an application, the composed derivation has no smaller measure.


## Approach 1: Locally Nameless Encoding for MPSS

### Idea
Replace de Bruijn indices with locally nameless representation (bound variables as
de Bruijn indices, free variables as atoms). This is closer to the named-variable
presentation in the MPSS paper.

### Would it avoid current obstacles?
**Partially.** The 4 FALSE lemma statements in MPSS are all caused by de Bruijn
index arithmetic:
- `equivRed_change_ann`: FALSE because ME-PRO at index 0 breaks (fixed by noPromoAt)
- `weakening_equivRed`: FALSE because CtxRed reduces annotations, changing the shift target
- `substitution_subRed/equivRed`: FALSE because the generalized statement conflates
  stack scope and term scope

Locally nameless would eliminate the stack scope mismatch (finding 3 in MPSSSubstAudit)
because stack elements wouldn't need shifting under binders. Context extension wouldn't
change existing variable names, so weakening becomes trivial. The `ctxRed_unstk` blocker
(needing equivRed_weaken_one with shifted stack elements) would vanish.

### New obstacles
- **Infrastructure cost**: Need `open`/`close` operations, `lc` (locally closed)
  predicates, cofinite quantification for binding lemmas. This is 500-1000 lines of
  boilerplate in Lean.
- **Non-promotion tracking** still needed (the noPromoAt predicate is a mathematical
  necessity, not a de Bruijn artifact).
- **Substitution lemmas** still need proving. They'd be cleaner but not trivial.
- **Diamond ME-PRO+ME-PRO** still needs a mutual diamond for Sub+Equiv (independent
  of representation).

### Work estimate
- Locally nameless infrastructure: 3-5 days
- Re-encode MPSS syntax + reductions: 2-3 days
- Re-prove existing lemmas (equivRed_refl, ctxRed helpers): 2-3 days
- Prove the currently-sorry'd lemmas: 5-8 days
- Total: **12-19 days**

### Assessment
Moderate improvement. Removes de Bruijn friction but the hard mathematical content
(substitution, diamond, commutativity) remains. The paper was written with named
variables, so locally nameless is a natural fit, but the effort is substantial for
what amounts to eliminating encoding artifacts, not mathematical obstacles.


## Approach 2: Normalization by Evaluation (NbE)

### Idea
Define a semantic domain (values as Lean functions/closures), an evaluation function
`eval : Expr -> Val`, and a readback function `reify : Val -> Expr`. Prove that
the NbE round-trip normalizes terms, then define subtyping on normal forms where
transitivity is easier.

### Would it avoid current obstacles?
**Unlikely.** PSS terms are not strongly normalizing in general (consider
`(lam Top. x(x))(lam Top. x(x))`). NbE requires a terminating normalization
procedure, but PSS allows non-terminating terms. The Och mechanization works with
NbE because Och has a restricted syntax (no general recursion). PSS is Turing-
complete.

Even for well-typed terms, there's no known termination argument. The evaluator
`concEval` uses fuel precisely because termination is not guaranteed.

### New obstacles
- **Non-termination**: NbE fundamentally requires termination. Would need to
  restrict to a normalizable fragment, losing generality.
- **Untyped evaluation**: PSS terms serve as both types and programs. Evaluating
  a "type" like `(lam Top. x)(Top)` during NbE is problematic -- it might diverge.
- **Readback**: The readback function needs to commute with subtyping, which
  re-introduces the same problems.

### Work estimate
Unclear, but likely intractable due to the termination problem.

### Assessment
**Not viable for full PSS.** Would require restricting to a normalizable fragment,
which defeats the purpose. The Och NbE approach works because Och has structural
recursion guarantees that PSS lacks.


## Approach 3: Reducibility Candidates / Girard's Method

### Idea
Define a "reducibility" predicate R(tau) for each type tau, indexed by the type
structure. Prove the main lemma: if e is well-typed at tau, then e is in R(tau).
Prove that R(tau) implies safety. The key: define R(tau) so that transitivity
is built into the definition.

### Would it avoid current obstacles?
**This is essentially what LogRel.lean already does.** SemVal is a step-indexed
version of reducibility candidates. The step index replaces Girard's induction on
types (which doesn't work in PSS because types ARE terms and can be non-terminating).

The existing LogRel achieves:
- Transitivity is free (SubSem is set inclusion)
- Canonical forms is definitional (SemVal at lam requires the value to be a lambda)
- Type safety is proved (concEval_safe, zero sorry)

But the fundamental theorem (fundamental_subSem) still has 4 sorrys: lam, app_cong,
beta_L, beta_R. These are the "compatibility lemmas" in the logical relations
literature.

### What's missing
The sorrys in fundamental_subSem correspond to:
- **lam**: Need `Sub [] av dom` from `Sub [] av dom'` and `Sub [] dom' dom`, which
  requires `Wf [] dom'`. This is a "Sub preserves Wf" lemma.
- **beta_L/R**: Need to relate evaluation of `app (lam d b) arg` to evaluation of
  `b.subst 0 arg`. This is a "concEval beta-reduction" fact.
- **app_cong**: Need congruence of evaluation under equivalent subexpressions.

None of these are the trans/canonical-forms obstacle. They're standard compatibility
lemma obligations.

### New obstacles from a fresh reducibility approach
A Girard-style approach without step indices would need to define R by induction on
types. But types in PSS are terms, and the "type" of a term can be any expression,
including `app f a` which might not normalize. So the induction measure is unclear.

The step-indexed approach (which is what LogRel already is) resolves this by indexing
on fuel rather than type structure.

### Work estimate
The existing LogRel is already 95% of this approach. Closing the 4 sorrys requires:
- `Sub preserves Wf` (or reformulating SemVal to not need it): 3-5 days
- concEval beta-reduction facts: 2-3 days
- concEval congruence: 2-3 days
- Total: **7-11 days** (incremental on existing code)

### Assessment
This IS the existing approach. The remaining work is well-understood and doesn't
hit the trans/canonical-forms wall. Recommended as incremental progress on LogRel.


## Approach 4: Biorthogonality

### Idea
Define types as pairs (terms, evaluation contexts) that interact safely. A term e
is in type T if for all evaluation contexts E in T's dual, E[e] is safe. An
evaluation context E is in the dual if for all safe terms e, E[e] is safe.

### Would it avoid current obstacles?
**Partially.** Biorthogonality automatically gives closure under reduction (if e
reduces to e' and e' is safe in all contexts, then e is too). This sidesteps the
beta_L/beta_R compatibility lemma issues.

However, PSS doesn't have standard evaluation contexts in the usual sense. The
"evaluation context" in PSS includes positions inside lambdas (both domain and body),
which is unusual. The subtyping relation itself involves evaluation (beta-reduction
IS subtyping).

### New obstacles
- **Defining evaluation contexts**: PSS's congruence rules allow reduction everywhere
  (domain, body, function position, argument position). The evaluation context
  grammar is non-standard.
- **The same fundamental issue**: The biorthogonal model still needs to validate
  the subtyping rules, particularly trans. While biorthogonality gives transitivity
  for free at the semantic level, proving that the SYNTACTIC Sub rules are sound
  w.r.t. the model still requires the compatibility lemmas.
- **Complexity**: Biorthogonality in a pure subtype system where terms = types
  hasn't been done before. The interaction between the "term" and "type" roles
  of expressions would need careful handling.

### Work estimate
- Define the biorthogonal model: 3-5 days
- Prove basic properties: 3-5 days
- Prove compatibility lemmas: 5-10 days (unclear if easier than LogRel)
- Total: **11-20 days**

### Assessment
Higher risk, unclear payoff vs. LogRel. The compatibility lemmas may or may not
be easier. Not recommended unless LogRel compatibility lemmas prove intractable.


## Approach 5: Direct Proof for Closed Terms Only

### Idea
PSS type safety is about CLOSED terms in the empty context. In the empty context:
- There are no free variables, so `bvar` cases are vacuous
- Variable promotion (Sub.bvar) is vacuous
- The only inhabitants are Top, lambdas, and applications

Exploit this to simplify the canonical forms proof.

### Would it avoid current obstacles?
**No.** The obstacle is not variable-related cases. The stuck case in
CanonicalForms.lean is:

```
h1 : Sub Gamma Top (app f c)   -- Top <= some application
h2 : Sub Gamma (app f c) b     -- that application <= some head form
-- h2 has trans with .app middle: compose with h1
-- The composed derivation has the same total height
```

Even in the empty context, this case arises because Sub.app_cong and Sub.beta_L/R
create application terms as intermediaries. The empty context doesn't eliminate
applications from the middle of a transitivity chain.

Moreover, the induction in CanonicalForms is over Sub derivation height, not over
the context. Restricting to empty context doesn't change the derivation structure.

### New obstacles
None new, but doesn't solve the existing one either.

### Work estimate
Minimal, but no payoff.

### Assessment
**Not viable.** The obstacle is in the structure of Sub derivations, not in the
context. The empty context restriction doesn't help.


## Approach 6: Proof-Relevant Restricted Sub

### Idea
Define a restricted subtyping relation `RSub` that only admits "good" derivations
(ones where trans never chains through an application middle term, or where the
chain is bounded in some way). Prove that RSub is equivalent to Sub for well-formed
terms, then prove canonical forms for RSub.

### Would it avoid current obstacles?
**In principle, yes.** If RSub excludes the problematic derivation patterns, canonical
forms becomes straightforward. The hard part moves to proving RSub is complete
(every Sub derivation can be transformed into an RSub derivation for well-formed terms).

This is essentially what Hutchins' transitivity elimination conjecture says: every
Sub derivation can be transformed into one without trans, for well-formed terms. If
we could prove this, we wouldn't need RSub.

### The key question
Can we define an intermediate restriction that's:
1. Restrictive enough that canonical forms is provable
2. Liberal enough that completeness w.r.t. Sub is provable

For example: "no trans with .app middle term" is restrictive enough for canonical
forms (that's the only stuck case). Is it complete? This is exactly Hutchins'
conjecture.

Alternatively: "trans only with well-formed middle terms where the middle term is
structurally smaller than the conclusion." This is restrictive enough AND might be
complete, because well-formed applications always have a function that's "simpler"
in some sense.

### New obstacles
- **Defining the right restriction**: Too restrictive = can't prove completeness.
  Too liberal = can't prove canonical forms.
- **Proving completeness**: This IS the transitivity elimination problem in disguise.
  Any restriction that makes canonical forms trivial will be hard to prove complete.

### Work estimate
If the right restriction can be identified: 5-10 days.
Risk of the restriction not existing: high.

### Assessment
**High risk, potentially high reward.** If someone can find the right intermediate
restriction, this solves the problem. But the search for this restriction is
essentially the same as the search for a transitivity elimination proof. Not
recommended as a primary approach, but worth thinking about as a conceptual tool.


## Approach 7: Algorithmic Subtype Checker

### Idea
The algorithmic system (already mechanized in `Algorithmic.lean`) doesn't have a
trans rule. Instead, transitivity is replaced by iterated reduction steps. Define
an algorithmic subtype checker and prove:
1. **Soundness**: Algorithmic Sub implies declarative Sub
2. **Completeness**: Declarative Sub implies algorithmic Sub (for well-formed terms)
3. **Canonical forms for the algorithmic system**: Trivial because no trans rule

Then derive declarative canonical forms from (2) + (3).

### Would it avoid current obstacles?
**Yes, IF completeness can be proved.** The algorithmic system is syntax-directed
and transitivity-free, so canonical forms is easy. The hard part is completeness:
showing that every declarative Sub derivation has an algorithmic counterpart.

Completeness is exactly what the MPSS paper is trying to prove (via a different
route). The algorithmic system has premature promotion issues that make the
completeness proof non-trivial.

### What the MPSS paper achieves
The MPSS paper reformulates the algorithmic system with a continuation stack to
fix the premature promotion issue. They prove:
- Commutativity of equivalence and subtyping reduction (Lemma 1)
- Diamond property for equivalence reduction (Lemma 2)
- Transitivity admissibility (Theorem 3)

But full type safety depends on Conjecture 8 (context independence of well-subtyping),
which remains open.

### Connecting algorithmic and declarative
Soundness (algorithmic -> declarative) should be straightforward: each algorithmic
rule corresponds to a composition of declarative rules.

Completeness (declarative -> algorithmic) is the hard direction. The declarative
trans rule must be simulated by a sequence of algorithmic reduction steps. This
requires showing that the algorithmic reduction steps can "find" the same middle
terms that trans uses. This is essentially transitivity elimination.

### New obstacles
- **Completeness IS transitivity elimination**: The completeness proof for the
  algorithmic system is exactly the problem we're trying to solve.
- **Premature promotion**: The algorithmic system allows promoting variables before
  they receive their arguments, which breaks the commutativity needed for
  completeness. MPSS fixes this with continuation stacks, but introduces its own
  complications.

### Work estimate
- Soundness: 3-5 days (straightforward)
- Completeness: **Unknown** (this IS the open problem)
- Canonical forms for algorithmic: 1-2 days (easy)
- Total: **4-7 days + the open problem**

### Assessment
**Circular.** Completeness of the algorithmic system IS the transitivity elimination
problem. Soundness is easy but doesn't help with canonical forms. Not recommended
as a standalone approach, but the algorithmic system could be useful as a bridge.


## Approach 8: Hereditary Substitution

### Idea
Define a type-directed substitution that simultaneously substitutes and normalizes.
Instead of `subst 0 v` producing a raw beta-redex, hereditary substitution would
immediately reduce the redex if the substituted variable appears in function position.
The subtyping relation is then defined in terms of hereditary substitution.

### Would it avoid current obstacles?
**Unlikely.** Hereditary substitution works well for systems where types control the
recursion (e.g., LF, where types are always normalizable). In PSS, types are terms
and can be non-normalizing. The "type" directing the substitution might itself need
to be evaluated, creating a circularity.

Furthermore, the subtyping relation in PSS is not defined via substitution. Sub.trans
composes two derivations without any substitution. Hereditary substitution would
change the system's definition, not just its proof technique.

### New obstacles
- **Non-termination of type-directed operations**: Types in PSS can diverge.
- **Fundamental redesign**: Would need to redefine the subtyping relation, not just
  the proof strategy.
- **Unclear benefit**: Even with hereditary substitution, the trans rule still
  composes derivations through arbitrary middle terms.

### Work estimate
Unclear, likely intractable.

### Assessment
**Not viable.** PSS's lack of a type/term distinction makes type-directed
operations problematic.


## Ranking and Recommendations

### Tier 1: Most Promising

**Recommendation 1: Complete the LogRel compatibility lemmas (Approach 3)**

The step-indexed logical relation in LogRel.lean is the most developed approach.
`concEval_safe` already has zero sorry. The remaining work is 4 compatibility
lemmas in `fundamental_subSem`, which are standard obligations in the logical
relations literature and do NOT hit the trans/canonical-forms wall:

1. **lam**: Needs `Sub preserves Wf` or a reformulated SemVal. The cleanest path
   is to prove `Sub Gamma a b -> Wf Gamma a -> Wf Gamma b` by mutual induction
   with SubstWf. Alternatively, remove the `Sub [] av s` condition from SemVal
   and generalize to closing substitutions.

2. **beta_L/R**: Needs `concEval (app (lam d b) a) = concEval (b.subst 0 a)` when
   the argument evaluates. This is a straightforward property of the evaluator.

3. **app_cong**: Needs concEval congruence under equivalent subexpressions. Can be
   proved by induction on fuel using step_sub.

Estimated work: **7-11 days** (incremental, well-understood obstacles).

**Recommendation 2: Fix MPSS with locally nameless encoding (Approach 1)**

If the LogRel path stalls, locally nameless MPSS is the next best option. The
mathematical content of the MPSS paper is believed correct -- the problems are
all encoding artifacts. Locally nameless would:
- Eliminate the 4 FALSE lemma statements (de Bruijn scope mismatches)
- Make substitution lemmas match the paper's named-variable proofs
- Simplify ctxRed_unstk (no shifting of stack elements)

The non-promotion tracking (noPromoAt predicate) would still be needed, but it's
already well-understood and partially proved (equivRed_no_promo_change_ann_at is
complete).

Estimated work: **12-19 days** (fresh encoding, but following a detailed paper).

### Tier 2: Worth Considering

**Approach 6 (Restricted Sub)**: If someone can identify a restriction on Sub
derivations that's tight enough for canonical forms but loose enough for completeness,
this would be elegant. But the search for this restriction IS the open problem.

**Approach 4 (Biorthogonality)**: Could potentially simplify the beta_L/R
compatibility lemmas. Worth investigating if those specific cases resist the
LogRel approach.

### Tier 3: Not Recommended

**Approach 2 (NbE)**: Non-termination kills it.
**Approach 5 (Closed terms only)**: Doesn't address the obstacle.
**Approach 7 (Algorithmic completeness)**: Circular -- completeness IS the problem.
**Approach 8 (Hereditary substitution)**: Requires redesigning the system.


## Concrete Next Steps

### For Recommendation 1 (LogRel compatibility):

1. Prove `Sub Gamma a b -> Wf Gamma a -> Wf Gamma b` (or show it's unnecessary
   by reformulating SemVal without the Sub condition).

2. Prove `concEval_beta`: for closed well-formed `app (lam d b) a`, if
   `concEval n (app (lam d b) a) = ok v`, then `concEval n (b.subst 0 av) = ok v`
   where `concEval n a = ok av`.

3. Close the lam case of fundamental_subSem using (1).
4. Close beta_L/R using (2).
5. Close app_cong using fuel monotonicity + step_sub.

### For Recommendation 2 (Locally nameless MPSS):

1. Define locally nameless Expr (atoms for free vars, de Bruijn for bound).
2. Define open/close, local closure predicate.
3. Re-encode MEquivRed/MSubRed/CtxRed with locally nameless.
4. Re-prove equivRed_refl, ctxRed_refl.
5. Prove substitution lemma (should be cleaner without scope mismatches).
6. Prove weakening lemma (should be trivial with named free vars).
7. Complete diamond and commutativity.
