# Typed NbE fundamental lemma (Option 1.75)

**Status:** research/planning sketch, 2026-04-23.
**Scope:** the architectural path that would close Phase 1's
residual sorries (particularly `eval_vapp_preserves_fullyQuotable`)
by introducing reducibility-candidates-style typed invariants to
the NbE proof chain.
**Related:** `docs/ideas/quote-witness-feasibility.md` (the
impossibility that motivates this), `docs/ideas/bottom.md`,
`docs/ideas/soundness-strengthen.md` (Phase 2; orthogonal).

## Motivation

Phase 1's `eval_vapp_preserves_fullyQuotable` is formally impossible
without invariants stronger than `Val.fullyQuotable`'s structural
closedness — the implication
`Val.fullyQuotable d v → ∃ q, quote fuelω d v = some q` reduces to
the Halting Problem. See the companion research note for the Ω-closure
counterexample.

Phase 2's `progress_mod_fuel` refactor of `concEval` does NOT
subsume Task 1 — they live in different layers (substitution-based
vs NbE closures).

The remaining path is what the research note calls **Option 1.75**:
import the reducibility-candidates technique from normalisation proofs
into NbE, carrying typed semantic-value invariants through the proof.
Andreas Abel's 2013 paper "NbE: Dependent Types and Impredicativity"
is the canonical reference; we'd adapt for OCH's type-in-type + fix
setting.

**Key observation.** Classical reducibility candidates prove
termination for a *total* calculus — the canonical form is `RC τ v
iff v terminates at τ`, and the fundamental lemma gives RC on all
well-typed outputs, hence strong normalization.

**This doesn't port to OCH.** OCH is non-total: `fix x:A. x`
typechecks at any A, and the Ω-combinator typechecks via recursive
types (`x : fix X. X → X`). So OCH has well-typed closed terms that
diverge under eval. A fundamental lemma "typeCheck ⟹ RC" combined
with "RC ⟹ terminates" would imply "typeCheck ⟹ terminates,"
which is **false** for OCH. The classical vision cannot be
faithfully ported.

**What can be ported.** Three weaker variants, in descending honesty:

1. **Step-indexed RC_n τ v** meaning "v's quote succeeds within
   some fuel tied to n." Fundamental lemma: "typeCheck n e τ ⟹
   result is in RC_n τ." Not a termination result in the large,
   but sufficient for the specific sorry (which is parametric in
   fuel anyway). This is probably the right target.

2. **RC restricted to a terminating fragment.** Define RC so that
   recursive-type-inhabiting `fix` values are excluded. Fundamental
   lemma covers only expressions that avoid those features. Closes
   the sorry for the fragment, not in general. Essentially
   importing Coq's total fragment into OCH's framework.

3. **"RC = quote-terminates"** trivially restates the sorry.
   Research note already showed this predicate is not preserved
   by eval/vapp without further structure. Dead end.

The rest of this document sketches (1), step-indexed RC, as the
most workable target.

## The sketch

A **typed reducibility predicate** `RC τ : Val → Prop` such that:

```
RC τ v → ∃ q, quote fuelω d v = some q    -- terminates
RC τ v → Val.fullyQuotable d v              -- implies the weak invariant
RC τ v → ∀ τ'. Subtype' τ τ' → RC τ' v     -- closure under subtyping
```

Base case (types without quantifiers): `RC τ v` is defined
structurally on `τ`'s shape after reduction to normal form.

Recursive case (function types `A → B`): `RC (A → B) v` iff for
every `a : RC A a`, `vapp v a` terminates and the result is in `RC B`.

For `fix` / `iota`: the self-referential type is tricky. In Abel's
setting, these are handled by Howard's or Girard's reducibility
candidate construction with carefully-stratified types. In OCH with
`Type : Type`, we can't use universe hierarchies to stratify; we
need a different trick. Candidates:

1. **Step-indexed reducibility.** `RC_k τ v` indexed by fuel `k`.
   `vapp v a` must terminate within `k-1` steps. The `fix` case
   unfolds at `k-1`. This gives a well-founded definition via
   induction on `k`.

2. **Coinductive reducibility.** Define `RC` as the greatest
   fixed point satisfying the closure conditions. `fix` unfolds
   one step and we re-apply `RC` coinductively. The quote-termination
   witness is extracted from the coinductive structure.

3. **Size-indexed.** `RC^n τ v` indexed by syntactic size of `τ`.
   Only useful for non-recursive types; needs a separate treatment
   for `fix`.

**Recommendation**: step-indexed (option 1). Matches Iris-style
reasoning, has good precedent (Dreyer et al.'s step-indexed logical
relations), and the index aligns naturally with NbE's fuel argument.

## The fundamental lemma

```lean
theorem typed_NbE_fundamental
    {e τ : Expr}
    (hwf : typeCheck n e τ = .ok true) :
    ∃ v, eval n unfBound [] e = some v
       ∧ RC (eval τ) v
```

Reads: well-typed closed expressions evaluate to RC-values of their
declared type. From this, `fullyQuotable_has_quote` becomes trivial
for RC values.

Proof technique: structural induction on the typing derivation (once
we have a declarative typing relation or induct on `typeCheck`'s
operational steps), using RC-preservation lemmas for each typing rule.

## Cost and risk

**LOC estimate**: 1000–2000 new lines across:
- `RC τ v` definition and well-foundedness proof (~200 LOC).
- RC closure lemmas (one per `Subtype'` rule, ~20 lines each × 24
  rules = ~500 LOC).
- RC preservation for `eval`/`vapp` (each typing rule, ~400 LOC).
- The fundamental lemma itself (~100 LOC).
- Bridge to existing `typeCheck_sound` / `soundness` (~100 LOC).
- Tests and smoke-checks (~50 LOC).

**Time estimate**: 2–4 focused weeks of research-engineering. Not a
subagent-session-scale task.

**Risks**:

1. **Step-indexing interaction with coinductive `Subtype'`.** OCH's
   subtyping is equirecursive via seen-sets. RC definitions over
   recursive types need careful layering against this coinduction.
   Unclear whether the standard step-indexed machinery extends
   cleanly.

2. **`Type : Type`.** Abel's work uses stratified universes. OCH's
   type-in-type rules out universe-based stratification. We need a
   reducibility construction that tolerates impredicativity. Girard
   showed this is possible for System F-ω; extending to Och's
   features (fix, iota) is plausible but not free.

3. **iota self-types.** OCH's `ι` binder is unusual; no direct
   precedent in Abel. The RC for an iota type would need to handle
   the self-reference, probably by a fixed-point construction.

4. **Interaction with Phase 2.** If Phase 2 (refactor `concEval` to
   distinguish stuck vs fuel) lands first, typed NbE could be built
   on top of the richer substrate. If Phase 2 lands AFTER, there
   may be some retrofitting. Favour doing Phase 2 first if both are
   planned.

## Integration with existing infrastructure

- `Val.fullyQuotable` stays — it's a useful structural predicate.
  We'd prove `RC τ v → Val.fullyQuotable d v` as a consequence, not
  a dependency.
- `R` and `RList` stay — they're about NbE-Expr correspondence, not
  reducibility. Typed NbE adds a third relation alongside them.
- `Subtype'` stays. RC closure under subtyping uses `Subtype'`
  directly.
- `typeCheck_sound` gains a new clause: "typeCheck accepts ⟹
  fundamental lemma ⟹ RC-valued output ⟹ quote terminates ⟹ old
  preservation holds." The result is that the transitive axiom set
  of `typeCheck_sound` becomes clean.

## Success criteria

If this landed:

1. `eval_vapp_preserves_fullyQuotable` and `quoteClosure_realises`
   both close (via the stronger RC invariant).
2. `vapp_realises` and `tyInfer_sound_open` sub-sorries close
   (the `hnfq` witness threading becomes trivial from RC).
3. `#print axioms Och.Soundness.typeCheck_sound` goes axiom-clean.
4. Phase 1's goal is reached — but through Option 1.75, not
   Option 1.

A9 Category C would remain intentionally sorried — it's a proof-
statement bug orthogonal to this.

## Should we do it?

**Not unilaterally.** This is 2–4 weeks of committed effort with
several novel research questions (step-indexing × equirecursive
subtyping; impredicative RC; iota self-types). It should happen if:

- Och's soundness story needs to be completed for publication /
  downstream use.
- The non-totality boundary documentation from `paper.md §7.2` is
  insufficient for the project's aims.
- Someone is willing to invest in the research-engineering.

If none of those hold, **option (a) from the sorry-closure plan
post-mortem — accept the boundary — remains the most honest
answer**. The soundness theorems today have documented residual
sorries that map precisely to OCH's stated non-total design. That's
defensible.

## Pointers if we do proceed

- Andreas Abel, "Normalization by Evaluation: Dependent Types and
  Impredicativity", 2013 Habilitationsschrift. Chapter 3 on the
  reducibility candidate construction.
- Coquand & Kinoshita, "A type-theoretical alternative to ISWIM,
  CUCH, OWHY", 2001 — early NbE for dependent types.
- Dreyer, Ahmed, Birkedal, "Logical step-indexed logical
  relations" — for the step-indexing pattern.
- Iris project papers for Lean-compatible step-indexed reasoning.
- Chapman et al. "The gentle art of levitation" — intrinsically
  typed universe constructions (for the `Type : Type` / impredicativity
  discussion, if option b intrinsic typing enters the picture).
