# STOP: Lemma 2 paper-faithful — structural barrier

## Context

Dispatch goal (commit objective): ship `Pss/Paper/Lemma_2_Diamond.lean`
containing the paper-faithful **`Lemma_2_DiamondMEqRed`** unconditionally
(no axioms, no `sorry`).

## Reachable from this dispatch

- `Pss/Paper/Lemma_2_Diamond.lean` ships **the paper-faithful statement**
  `Lemma_2_DiamondMEqRed_Conclusion` and the case-grid structure.
- The trivial `Me-Top × Me-Top` and `Me-Var × Me-Var` cases close
  conditionally on the transport auxiliary
  `MEqRedTransportAcrossEvolution`.
- The headline theorem `Lemma_2_DiamondMEqRed` is exposed conditional
  on a single `Lemma_2_CaseGrid` premise.

## Why the unconditional discharge stalled

The paper's proof of Lemma 2 (p. 9:21–25) is ~5 dense pages of case
analysis. Mechanizing it requires three structural auxiliaries beyond
what was already shipped:

### (1) `MEqRedTransportAcrossEvolution`

Statement: `MEqRed Γ s u v` together with `Γ; s ↣ Γ'; s'` yields
`MEqRedJ Γ' s' u v`.

This is the de Bruijn analogue of paper's Lemma 19 invocation pattern
("by weakening (Lemma 19) we have …"). The codebase has the per-rule
parts:

- `MEqRed.replaceAt_sub` (DeBruijnReductions.lean:1795) — replace a
  `.sub` bound at any depth.
- `MEqRed.replaceAt_sub_to_equ` (~line 1843) — kind narrowing.
- `MEqRed.stack_head_replace_from_handlers` (~line 503) — replace stack
  head, with per-rule handlers.

These do not directly close `MEqRedTransportAcrossEvolution`. The
transport requires:

- For `ctRefl`: identity (trivial).
- For `ctAnn`: replace head bound at index 0 across an entire `MEqRed`
  derivation. The `replaceAt_sub` call closes this when the kind is
  `.sub`; the `.equ` case needs the parallel `replaceAt_equ` family,
  which the codebase has only for some constructors (search for
  `MEqRed.*_equ_head_replace`).
- For `ctStk`: replace stack head across an entire `MEqRed` derivation.
  This requires lifting `stack_head_replace_from_handlers` from per-rule
  to a generic transport, which is a structural induction on `MEqRed`
  with each constructor's case calling the handler shape.

This auxiliary is ~150–250 lines of Lean (one per-`MEqRed`-constructor
case in each of the four `ContextEvolution` constructors).

### (2) ContextEvolution-extended IH

The paper's induction is on the source derivation of
`Γ₀; s₀ ⊢ t₀ →ᵉᵠᵘ t₁`. Each binder-introducing rule (`Me-Bet`,
`Me-Fun`, `Me-FOp`) recurses on a body sub-derivation in an extended
context. The IH thus needs to apply at the extended context, which
means the `ContextEvolution` premise must be lifted across the same
extension.

For example, for `Me-Bet`:
- Source body lives in `({t,.sub} :: Γ₀, Stack.shift 0 s₀)`.
- IH on body needs `ContextEvolution ({t,.sub} :: Γ₀) (Stack.shift 0 s₀)
  ({t,.sub} :: Γ_i) (Stack.shift 0 s_i)`.
- Such a lift exists by `ctAnn` (with `MEqRed.refl` on the bound) plus
  a stack-shift respect lemma for `ContextEvolution`.

The codebase does NOT yet have a `ContextEvolution.shiftedStack` or
`ContextEvolution.cons` helper that produces these lifted derivations.
Both are derivable from the existing `ContextEvolution` constructors
plus the `MEqRed.refl` family, but they need to be written.

This is ~50–100 lines.

### (3) Per-case proofs

Even with (1) and (2), the per-case proofs are non-trivial. Worst cases:

- **`Me-Bet × Me-Bet`** (paper p. 9:25): Needs IH on body in the
  extended `.sub` head context, IH on operand at `[]`, then **both**
  Lemma 19 (kind narrowing `.sub` → `.equ`, head update from `t` to
  `v_i`) AND asymmetric Lemma 32. The `(arg, arg')` substitution shape
  must match the paper's `(v_i, v_3)`.

- **`Me-App × Me-Bet`** (paper p. 9:22–23): Similar to above, with the
  "no Me-Pro promotion of x" side condition exploited.

- **`Me-FOp × Me-FOp`** (paper p. 9:24): IH on body in the extended
  `.equ` head context with shifted stack. The `Stack.shift` and
  `ContextEvolution` interaction is the trickiest piece.

Each case is 50–150 lines. Total ≈ 400–700 lines for all 9 cases.

## Total scope estimate

| Component | Lines |
|---|---|
| `MEqRedTransportAcrossEvolution` (auxiliary 1) | 150–250 |
| `ContextEvolution.cons_*` helpers (auxiliary 2) | 50–100 |
| Per-case proofs (cases 1–9) | 400–700 |
| **Total** | **600–1050** |

This is a multi-dispatch effort, comparable to the original
`DeBruijnTransitivityElim.lean` (29k lines for the full Lemma 1 + 2
fixed-context grid + Theorem 3 lifting).

## Recommended dispatch sequence

1. **Dispatch A**: Discharge `MEqRedTransportAcrossEvolution`
   unconditionally. Single file `Pss/Paper/Aux/EvolutionTransport.lean`,
   ~200 lines, induction on `ContextEvolution` with per-rule transport
   for each `MEqRed` constructor.

2. **Dispatch B**: Add `ContextEvolution.cons_sub`,
   `ContextEvolution.cons_equ`, `ContextEvolution.shiftedStack`
   helpers to `Pss/Paper/ContextEvolution.lean`. ~80 lines.

3. **Dispatch C**: Discharge cases 1–4 (Top × Top, Var × Var,
   Pro × Var, Pro × Pro). ~150 lines.

4. **Dispatch D**: Discharge cases 5–7 (App × App, App × TAp,
   TAp × TAp). ~150 lines.

5. **Dispatch E**: Discharge cases 8–9 (Fun × Fun, FOp × FOp). ~200
   lines.

6. **Dispatch F**: Discharge cases 10–11 (App × Bet, Bet × Bet — the
   Lemma 32 cases). ~250 lines.

7. **Dispatch G** (this file): Wire up the headline theorem
   `Lemma_2_DiamondMEqRed`, retire `Lemma_2_CaseGrid` premise.

## What this dispatch ships

This dispatch ships:

- `Pss/Paper/Lemma_2_Diamond.lean` — paper-faithful statement of
  `Lemma_2_DiamondMEqRed_Conclusion` and the conditional headline
  theorem `Lemma_2_DiamondMEqRed` (depending on the case-grid
  residual).
- The three structural cases (Top × Top, Var × Var) closed
  conditionally on the transport auxiliary
  `MEqRedTransportAcrossEvolution`.
- This STOP document describing the dispatch sequence to fully
  mechanize Lemma 2.

No axioms; no `sorry`; build green.

## Conclusion

The paper-faithful Lemma 2 is provable but the proof is a substantial
multi-dispatch effort (~1000 lines). This dispatch ships the
**foundation** (statement, structural skeleton, trivial cases). The
campaign should follow the recommended dispatch sequence A–F to fully
discharge Lemma 2 unconditionally.

The dispatch's progress is real: the paper-faithful statement now
exists, the case structure is laid out, and each future dispatch has
a precise scope and entry point.
