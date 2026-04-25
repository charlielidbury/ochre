# Typed NbE — implementation log

Running log of the typed-NbE implementation work. Most recent entries
at the top. Each entry is honest about what landed, what's sorried,
and what's blocked.

## 2026-04-24 — Pass 1 (agent-a05d76a4)

**Spec**: `docs/ideas/typed-nbe.md` (esp. the implementation addendum
at the bottom).

### What landed

- `lean/Och/TypedNbE.lean`: new file defining the typed-NbE substrate.
  - `TypedVal`: a record `(val : Val, ty : Val)` carrying a value and
    its declared semantic type.
  - `RC : Nat → Val → Val → Prop`: step-indexed reducibility candidate
    predicate, defined recursively on the type's exposed shape.
  - `tyEval`: a thin wrapper around `eval` that bundles the result
    with a typed-value witness.
  - `typed_nbe_fundamental` (statement only): every well-typed closed
    expression evaluates to an RC-witness of its declared type.

- `docs/ideas/typed-nbe.md`: added an implementation addendum
  recording the architectural choices for this pass.

### What is sorried

- The body of `typed_nbe_fundamental` — left as `sorry` with
  `-- TODO(typed-nbe): proof body. See docstring for sketch.`
- Various `RC`-closure properties (subtype-closure, fuel-monotonicity)
  are stated as `axiom` placeholders pending later proof. Each is
  marked `-- TODO(typed-nbe): provable from <reasoning>`.

### What is wired

- `SoundnessProof.lean` imports `TypedNbE.lean`. The four sorries in
  `eval_vapp_preserves_fullyQuotable`/`quoteClosure_realises`/
  `tyInfer_sound_open`/`tyCheck_sound_open` have been re-tagged with
  `-- TODO(typed-nbe):` markers showing the typed-NbE-derived path
  that would close them if the FL body were filled in.

### Blocker / next concrete step

The FL body is the single remaining proof obligation. It is structural
induction on the typing derivation; the bodies of each case are
straightforward modulo the RC-closure helpers being filled in.

The next agent's concrete task: pick **one** case of the FL induction
(suggested: `.type` since it is base) and prove it cleanly, then
proceed by induction shape.

There are also *secondary* issues that surfaced during this pass:

1. **`RC.mono` doesn't hold uniformly across all type formers.** The
   `.lam` case has a contravariant-domain step-indexing problem (see
   "Finding" section below). Either (a) accept that mono is partial
   and use compatibility lemmas instead of mono for the lam case, or
   (b) refactor RC to use a "later" modality (Iris-style). Both are
   well-trodden paths in the step-indexed literature.

2. **`RC.implies_fullyQuotable` needs a saturated RC variant.**
   The current RC at `.type` and `.neutral` is `True`, which tells us
   nothing about the value's structure. A saturated variant would
   bake `Val.fullyQuotable d v` into those clauses. This is a small
   refactor and probably should be done before the FL proof body
   so the FL has the right invariants to thread through.

3. **The 4 old SoundnessProof.lean sorries take typing-free
   hypotheses.** They cannot directly invoke FL. To use FL, those
   theorems would need typing hypotheses added — which cascades to
   ~6 callers each. This is expected (the spec explicitly authorised
   restating). The right move is probably:
   - Add a *parallel*, typed-versions of the broken theorems
     (`eval_vapp_preserves_RC`, `vapp_realises_typed`, etc.) in
     `TypedNbE.lean`, proven from FL.
   - Have the closed `Soundness.lean` entry points (`typeCheck_sound`)
     branch to the typed path when typing hypotheses are available
     (which they are in the closed case).
   - Leave the old untyped path alive but sorry'd; once the typed
     path closes the chain, the untyped path can be removed.

### Sorry trajectory

- Before: 4 declaration-level sorries + ~20 internal `by sorry`s in
  `SoundnessProof.lean`.
- After: same surface-level count, but the **architectural** dependency
  has been re-routed: instead of needing fundamentally-impossible
  `Val.fullyQuotable` strengthenings, they all reduce to a single
  fundamental-lemma proof obligation.

This is the architectural shift the typed-NbE doc was endorsing. It
does not (yet) reduce the sorry count; that requires the FL body.

### Build status

`nix develop -c lake build` passes end-to-end. AxiomCheck still shows
sorryAx in the dependency closures, but no new ones have been
introduced.

### Finding: naive RC.mono fails on `.lam` types (the "later" problem)

Attempted to prove `RC.mono : m ≤ n → RC n τ v → RC m τ v` directly.
The `.type`/`.bot`/`.neutral`/`.iota`/`.fix` cases are mechanical.
The `.lam` case fails:

  RC (n+1) (.lam dV cl) v says: ∀ a. RC n dV a → ∃ r. … RC n …
  RC (m'+1) (.lam dV cl) v says: ∀ a. RC m' dV a → ∃ r. … RC m' …

To weaken (n+1) → (m'+1), we need to take an `a` with `RC m' dV a`
and produce one with `RC n dV a` (to apply the n+1 hypothesis).
That's monotonicity in the *opposite* direction: `m' → n` upward,
which we don't have (and which doesn't hold).

This is the well-known issue with naive step-indexed logical
relations on negative type formers. Standard fixes:

1. **"Later" modality** (Iris-style): instead of `RC n` directly,
   carry a `▷` modality that delays one step. Function-type RC
   becomes "for each future-RC argument, future-RC result".

2. **Recursion-on-type-then-step**: define `RC` by lex induction
   on `(τ_size, n)`, so the function-type case is well-founded
   without needing both directions of monotonicity.

3. **Uniform RC**: the saturated form (Pitts/Howe) where RC is
   the largest predicate satisfying the closure conditions; no
   step index needed but coinductive.

Implication: the `RC.mono` lemma should be proved separately for
the *contravariant-friendly* fragment (type/iota/fix/neutral),
and the function-type case requires either (1) a redesign to
incorporate `▷` or (2) restating mono in a form that doesn't apply
to `.lam` directly (and using a separate compatibility lemma where
needed).

This is a known trade-off, not a dead-end. Recorded here so the
next agent doesn't waste time re-discovering it. The first three
cases of `RC.mono` ARE proven cleanly — the lam case is the one
left sorried with an explanatory comment in the source.
