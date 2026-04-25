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
