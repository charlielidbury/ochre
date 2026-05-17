# PSS — Pure Subtype Systems (Lean 4)

Lean 4 formalization of **Pasquale & García-Pérez (arXiv 2407.13882, v2 Dec 2025)**,
the "Machine-based PSS" (MPSS) Krivine-style reformulation that closes the
transitivity-elimination gap left open by Hutchins (POPL 2010).

This formalization targets the MPSS system specifically. The original Hutchins
algorithmic system (Fig. 2 of the POPL paper) is fully superseded by MPSS and is
NOT mechanized here — see "Scope" below.

See `PLAN.md` for the module map and `AXIOMS.md` for axiom commitments.

## Build

```sh
cd pss
nix develop --command lake build
```

The repo's Nix flake (one level up at `../flake.nix`) pins Lean and Lake to
the versions used by this formalization. The first build will fetch Mathlib
v4.16.0 and download its `.olean` cache; subsequent builds are incremental.

If you do not have Nix available, ensure `lean` and `lake` are on `PATH` at
the version specified in `lean-toolchain` (`leanprover/lean4:v4.16.0`) and
run `lake build` directly.

## Scope (KAM-only)

MPSS supersedes Hutchins' algorithmic machinery and metatheory entirely:

- Hutchins' algorithmic reductions `⟶^≡` / `⟶^≤` (POPL Fig. 2) → replaced by
  MPSS's 14 Me-*/Ms-* rules with extended contexts `Γ; s` (paper 2 Fig. 2).
- Hutchins' Theorem 6.1 (confluence of `⟶^≡`) → superseded by MPSS Lemma 2
  (Diamond of MPSS `⟶^≡`).
- Hutchins' Lemma 6.4 (local commutativity only) → superseded by MPSS Lemma 1
  (full strong commutativity).
- Hutchins' Conjectures 5.1 + 6.2 → resolved as MPSS Theorem 3.
- Hutchins' Theorems 5.5/5.6 (progress + preservation conditional on
  Conjecture 5.1) → restated and reproved as MPSS Theorems 4 & 5 conditional
  on Conjecture 8.

What MPSS keeps from Hutchins (and what we therefore mechanize):

- Term syntax `t ::= x | Top | λx ≤ t. u | t(u)`.
- The plain operational reduction `t ↦ t'` (Os-Bet + Os-Con).

The declarative subtyping `Γ ⊢ t ≤ u` is referenced in paper 2 §1 as
background only; paper 2's actual type-safety theorem is stated against MPSS
well-formedness `WfM` / `WSubM` / `WSubMStar` (Fig. 4). We do not mechanize
the Hutchins declarative judgments — they are not on the path to the headline
theorem.

## Status

All seven mechanization waves are complete; the project is in a
post-Wave-7 **discharge campaign** that has converted the previous
monolithic `Lemma_1_StrongCommutativity` and `Lemma_2_DiamondMEqRed`
axioms into theorems with narrow per-cell residuals.

Current state (run `nix develop --command lake build Pss.Sanity` to
re-verify):

- **Total axiom count: 12** (1 permanent paper conjecture + 9 active
  outstanding + 2 inactive outstanding).
- All five headline results — Theorems 3, 4, 5; Lemma 1; Lemma 2 —
  are theorems, not axioms.
- `Conjecture_8_WellSubtypingContextIndependent` (paper-permanent) is
  retained for paper faithfulness but is **not** in any headline
  theorem's dependency closure (Wave-7 reworked Lemma 7 to route
  around it).
- Theorem 5's residual axioms reduce to four: `Lemma_10_Inversion`,
  `Lemma_24_NarrowingMSubRed`, `Lemma_30_msPro_x_axiom`,
  `Proposition_17_beta_axiom`.
- Theorem 3, 4 and Lemma 1 share six residual axioms: the four for
  Theorem 5 minus `Lemma_10_Inversion`/`Proposition_17_beta_axiom`,
  plus the per-cell Lemma-1/Lemma-2 ctx-axiom + β-residual family.
- Lemma 2's residuals are three: `Lemma_2_DiamondMEqRed_ctx_axiom` and
  the two `Lemma_2_inline_*_residual_axiom` β-cells.

See `AXIOMS.md` for per-axiom paper references, blocker analyses, and
discharge plans, and `PLAN.md` (DISCHARGE CAMPAIGN STATUS section) for
the recommended next-step strategy. The campaign has converged on a
choice between continued grinding ("Option A") and a structural
"Type-LC" refactor ("Option B") that would unblock several β-residuals
at once by lifting `Term.LC` from `Prop` to `Type`.

## Papers

Under `papers/`:

- `papers/pasquale-garcia-perez-2024-mpss.pdf` — Pasquale & García-Pérez,
  "Towards the type safety of Pure Subtype Systems (Full version)"
  (arXiv 2407.13882, v2 13 Dec 2025). **Primary reference.**
- `papers/hutchins-2010-pss.pdf` — Hutchins, "Pure Subtype Systems"
  (POPL 2010). Read for the term syntax and the operational reduction;
  the metatheory it states is fully superseded by MPSS.
- `papers/hutchins-2009-thesis.pdf` — **MISSING**. Hutchins' 2009 Edinburgh
  PhD thesis. Not needed under the KAM-only scope; if you want it for
  background, fetch from <https://era.ed.ac.uk/handle/1842/3937>.

- `papers/pasquale-garcia-perez-2025-checker.pdf` — Pasquale & García-Pérez,
  "An interactive type checker for dependent types with general recursion
  (System Description)" (PPDP 2025, doi:10.1145/3756907.3756925). Describes
  an Emacs/Lisp-based interactive checker for PSS. Implementation-focused;
  no new metatheory, so not on this formalization's critical path. Note
  that this paper extends PSS with a primitive fixed-point combinator
  `Y u` and a variant type `Or(u, v)`, both of which are absent from the
  MPSS metatheory we mechanize — useful background but not part of the
  formalization scope.

  **The artifact is vendored as a git subtree under `checker-artifact/`** —
  see `checker-artifact/README.md` and `checker-artifact/src/` for the
  Emacs Lisp implementation. Sub-agents looking for concrete examples of
  PSS terms (Scott-encoded ints, the integer type, factorial, Syracuse) or
  the type-checker's command surface can read directly without leaving the
  worktree. Upstream:
  <https://github.com/valentin-ppp/interactive-dependenttypes-typechecker>.
