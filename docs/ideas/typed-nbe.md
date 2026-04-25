# Typed NbE — the architectural foundation

**Status:** **endorsed direction**, 2026-04-25. To be implemented.
Original sketch 2026-04-23, expanded after 2026-04-24/25 perf + wishlist
investigations made the broader case.
**Scope:** rebuild Och's NbE so semantic values carry their types, and
the subtype/conversion check is type-directed. Not just a sorry-closure
plan — this is the architectural substrate the rest of Och's open
problems all reduce to.
**Related:** `docs/ideas/quote-witness-feasibility.md` (an impossibility
that motivates the typed approach), `docs/ideas/bottom.md`,
`docs/ideas/soundness-strengthen.md` (Phase 2; orthogonal),
`docs/ideas/subcheck-perf.md` and `docs/ideas/a6-closure-env-filtering.md`
(perf negative results that point here), `WISHLIST.md` items #2 and #3
(stuck-elim subsumption, unblocked by this).

## Why this is the right move

Three of Och's biggest open problems share a root cause: the algorithmic
checker has too little information at the point it's running.

1. **Soundness.** The four declaration-level sorries in
   `SoundnessProof.lean` need a typed reducibility predicate to close.
   `eval_vapp_preserves_fullyQuotable` is provably impossible at its
   current strength (Halting reduction, see `quote-witness-feasibility.md`)
   — it needs RC, which needs typed NbE.

2. **Performance.** `three_ ⊑ Nat_` costs ~50k fuel today. Two
   independent investigations (memoization 2026-04-24, env-filtering
   2026-04-25) confirmed there is no redundant work to cache or filter
   away — the cost is **genuine algorithmic work** done by an untyped
   checker that has to re-derive the singleton-Nat structure on every
   call. Typed NbE turns this into pay-once construction-time work:
   the obligation `n_ ⊑ Nat_` is discharged when the constant is built,
   and recorded on the value itself. Subsequent checks become O(1)
   lookups. The singleton encoding's intrinsic O(n) cost stops being
   a runtime cost.

3. **Wishlist #2 / #3.** Parametric width-monotonicity
   (`λn:Nat_. Fin n ⊑ λn:Nat_. Fin (succ_ n)`) and stuck-eliminator
   subsumption need the checker to know the *type* of a neutral, not
   just its untyped form. Today `Fin n` for neutral `n:Nat_` is opaque
   to the algorithm. With typed NbE the checker knows `n` inhabits
   `Nat_`'s shape and can reason about `Fin n` parametrically through
   its type rather than its stuck reduction.

These are not three separate problems — they are three symptoms of the
same architectural gap. Typed NbE is the foundation every credible
solution to all three starts from.

It also aligns Och with mainstream dependent type theory implementations.
Coq, Lean, and Agda all run conversion against a typed semantic
representation; none rely on untyped term equality alone. We can borrow
proof technique (Abel's habilitation, Iris-style step-indexing, Coq's
conversion machinery) instead of inventing from scratch.

## What it does NOT do

Typed NbE is the substrate, not the destination. It does not
automatically give:

- **Wishlist #1 (`Fin n ⊑ Nat_`)** — that's an Option F encoding
  trade-off; needs separate encoding work.
- **Wishlist #4 (inhabitation-as-subsumption)** — undecidable in full;
  requires layers on top of typed NbE.

But every credible path to those *starts from* typed NbE. Treat it as
the foundation that unlocks the rest.

## Original motivation (preserved for context)

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

**Yes — endorsed 2026-04-25.** The 2026-04-24/25 perf investigations
(memoization, env-filtering) closed the door on incremental fixes to
the untyped checker; both produced negative results pointing at the
same conclusion: the architecture itself is the limiting factor.
Combined with the soundness story and Wishlist items #2/#3, the case
for typed NbE is now overdetermined.

This is 2–4 weeks of committed research-engineering with genuine open
questions (step-indexing × equirecursive subtyping; impredicative RC;
iota self-types). Implementation will invalidate existing proofs in
`SoundnessProof.lean` during the rebuild — affected proofs should be
sorried with TODO markers and re-derived after the typed substrate
stabilises. This is acceptable: we're moving to a stronger foundation,
not abandoning soundness.

## Implementation addendum (2026-04-24, agent-a05d76a4)

This section records architectural choices made during the first
implementation pass. The goal of this pass is to land the typed-NbE
*substrate* (datatype + RC predicate + fundamental-lemma statement)
and use it to close the four declaration-level sorries in
`SoundnessProof.lean`. The substrate may or may not have provable
fundamental-lemma bodies — but the statement being right and the
pipework wiring through is the load-bearing thing.

### Choice 1 — parallel `TypedVal` over modifying `Val`

`Val` stays untyped. A new structure `TypedVal` carries a `Val` plus
its declared semantic type (also a `Val`). Rationale:

- Minimises blast radius. `Val.beq`, `subCheckVal`, `quote`, every
  proof in `SoundnessProof.lean` keeps working untouched.
- The classical NbE proofs (Abel, Coquand-Kinoshita) all separate
  semantic values from their *types* — types are values too in OCH,
  and separating the two layers ergonomically is the intent.
- Allows incremental migration: eval still produces `Val`s; we add
  `tyEval e τ : Outcome TypedVal` as a *checked* wrapper that bundles
  the evaluation with its declared type.
- If we later decide intrinsic-typing the `Val` is the right move, we
  can transition by making `TypedVal` the canonical form and dropping
  `Val`'s standalone existence. This is a strictly looser commitment.

A `TypedVal` is conceptually a witness `(v, τ) : Σ τ. RC τ v`, but
in practice we carry `(v, τ)` as data and `RC τ v` as a separate
proposition (Lean's record-with-Prop-field would force structural
equality through it; we don't need that yet).

### Choice 2 — RC as step-indexed `Prop`

Per the spec's recommendation. Defined `RC : Nat → Val → Val → Prop`
with `n` the step-budget. Inductive cases follow the type-shape of
its second argument *after one quote-and-unfold*:

```
RC 0 τ v             := True  -- step-zero is trivially-OK; refines under ihstep
RC (n+1) .type v     := True
RC (n+1) .bot v      := False  -- Bot is empty
RC (n+1) (.lam dV cl) v :=
  ∀ a, RC n dV a → ∃ r, vapp fuelω unfBound v a = .ok r ∧ RC n (cl.openω a) r
RC (n+1) (.iota aV cl) v :=
  RC n aV v ∧ RC n (cl.openω v) v
RC (n+1) (.fix _aV cl) v :=
  RC n (cl.openω (.fix _aV cl)) v
RC (n+1) (.neutral _) v := True  -- a neutral type is opaque; nothing to check
```

This doesn't yet account for `Subtype'` closure on the type side; that
will be a separate `RC_subtype_closed` lemma.

### Choice 3 — fundamental lemma as a *statement*, not a closed proof

Per the user prompt's step 4 directive. We commit the FL signature; the
proof body can be `sorry` initially. The downstream sorry-closure (step
5) gets to assume the FL.

### Choice 4 — file layout

New file `lean/Och/TypedNbE.lean`, importing `NbE`/`SubCheckVal`. Defines
`TypedVal`, `RC`, `tyEval` (a typed eval wrapper), and the FL statement
`typed_nbe_fundamental`. SoundnessProof.lean adds an import and uses the
FL to discharge the 4 sorries.

### Realistic scope of this pass

It is unlikely a single pass closes the FL proof body. The realistic
landing target for *this* attempt:

1. Datatype + RC + FL signature compile. ✓ goal
2. Old 4 sorries are reduced to *one* sorry — the FL body itself.
3. At least one regressed perf test (`three_ ⊑ Nat_` lower fuel) gets
   a typed-subsumption path that closes it more cheaply, *or* the
   path is wired and a follow-up agent adds the leaf-cases.

If this attempt only lands (1), that is still progress: it makes the
typed substrate a thing that exists, and the remaining work for follow-
up agents is concrete. The danger to avoid is leaving a half-wired
substrate that's neither used nor easy to use.

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
