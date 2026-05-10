# FALSE ALARM — Pasquale & García-Pérez 2024 Lemma 32 is correct

**Status:** Resolved. The previous claim of a paper bug at Lemma 32
was incorrect. The asymmetric form is **provable as a single `MEqRed`
step** in our de Bruijn encoding, and has been mechanized; the paper
is correct as stated.

**File:** `pss/Pss/Paper/Investigation/Lemma_32_Asymmetric.lean` ships
the constructive proof (`Lemma_32_Asymmetric_proved` and the
closed-prefix specialization `Lemma_32_Asymmetric_proved_closed`).
Axiom dependency: kernel three only (`propext`, `Classical.choice`,
`Quot.sound`). No `sorry`, no new axioms.

**Surface:** `pss/Pss/Paper/Aux/Substitution.lean` exposes the
asymmetric form as
`Lemma_32_ReductionUnderSubstitution_AuxForCommutation_Asymmetric`
alongside the previously shipped symmetric form
`Lemma_32_ReductionUnderSubstitution_AuxForCommutation`.

## The argument the previous dispatch missed

The previous dispatch (commit `e5d2096`) reduced the asymmetric
Lemma 32 to an obligation `MEqRedStackExtensionWall`:

> Given `MEqRed Γ [] arg arg'` (paper's `v →ᵉᵠᵘ v'`), iterated
> weakening across `instantiateBetaPrefix` heads, and a prevalid
> post-substitution stack `s'`, derive
> `MEqRed Γ' s' (shifted arg) (shifted arg')`.

It then claimed the wall was unprovable, citing the case
`arg = .abs t body`: the empty-stack `MEqRed Γ [] arg arg'` derivation
must be `Me-Fun` (body in `.sub t`-headed context, empty stack); the
non-empty-stack target requires `Me-FOp` (body in `.equ β`-headed
context, non-empty stack). The two body sub-derivation contexts
appeared structurally incompatible.

**What the previous dispatch missed:** the existing lemma
`MEqRed.sub_to_equ_head_replace`
(`Pss/Mpss/DeBruijnReductions.lean:1945`) precisely handles the kind
switch from `.sub`-bound head to `.equ`-bound head, preserving the
body sub-derivation. This lemma exists because `Me-Pro` (the only
`MEqRed` rule whose conclusion distinguishes `.sub` from `.equ`)
cannot fire on `bvar 0` under a `.sub` head. The body sub-derivation
of `Me-Fun` is therefore Me-Pro-free at index 0, hence valid as-is
under any new head kind at index 0.

Combined with stack-append extension by induction on the source
derivation (handling the `Me-Fun → Me-FOp` re-derivation), the wall
discharges cleanly. The proof is in
`Pss/Paper/Aux/StackExtension.lean`:

* `MEqRed.append_stack` — stack-append extension, the core induction.
* `MEqRed.lift_empty_to_stack` — the empty-source specialization.
* `MEqRed.appendCtx` — Type-valued iterated head-extension weakening.

The wall's discharge in `Pss/Paper/Investigation/Lemma_32_Asymmetric.lean`
(`MEqRedStackExtensionWall_proved`) composes these.

## Lessons for future investigations

1. **Search the codebase before declaring something unprovable.** The
   `sub_to_equ_head_replace` lemma was already in the tree (commit
   `8e72b12` referenced in the older `:1909–1944` commentary in
   `DeBruijnTypeSafety.lean`). The previous dispatch did not search
   for kind-narrowing helpers when investigating the abstraction case.

2. **De Bruijn obscures kind-narrowing arguments that are invisible in
   named binders.** The paper's `Me-Fun → Me-FOp` re-derivation is
   trivial in a named encoding — the fresh variable is renamed and
   the body's typing context entry's kind (`≤` vs `≡`) is implicit.
   In de Bruijn, the kind switch is syntactically explicit and
   requires a dedicated lemma. Future "this can't be done in de Bruijn"
   claims should specifically check for kind-switch helpers.

3. **A proof sketch via "this case lifts because Me-Pro can't fire on
   bvar 0 under .sub" is sufficient evidence to attempt the lift.**
   The previous dispatch correctly identified this argument in the
   abstract but did not act on it; instead it concluded structural
   incompatibility based on a surface inspection of constructor
   shapes.

## Updated commentary at related sites

The misleading "structurally impossible" commentary at
`Pss/Mpss/DeBruijnTypeSafety.lean:1909–1944` has been updated to
reference the asymmetric proof. The "fused kind-narrowing" symmetric
form remains as an optimization for call sites where the chain-shaped
composition is already in place.
