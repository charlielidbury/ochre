# Pure Subtype Systems, mechanized

A Lean 4 formalization of DeLesley S. Hutchins, **“Pure Subtype Systems”**, POPL 2010
(`docs/papers/pss.pdf` in this repo) — System **λ⊲**, its declarative and algorithmic
subtype systems, and the paper's metatheory.

This formalizes the *original* POPL 2010 paper, not any later machine-based
reformulation. The encodings are intended to be honest: every judgment, rule and
numbered statement of the paper has a direct Lean counterpart, with deviations
limited to standard formalization tweaks (de Bruijn indices), each documented
where it occurs.

## Building

```
cd pss && lake build
```

Lean 4.16, no dependencies (no mathlib). The lakefile's glob builds every file
under `Pss/`, imported or not.

## Conventions (formalization tweaks)

* **De Bruijn indices.** Binders are nameless; `lam t u` is `λx ≤ t. u` where the
  bound `t` scopes *outside* the binder and the body `u` binds index 0.
  Substitution is σ-calculus style (`Term.rename` / `Term.subst` with the
  composition-lemma library in `Pss/Syntax.lean`); `Term.subst1` is the paper's
  `[x ↦ s]u`.
* **The metavariable `⊲`.** The paper's `⊲` ranges over `≤` and `≡`; here it is a
  genuine index `Rel.le / Rel.eq` on the judgments, so each `⊲`-rule of the paper
  is literally two rules (§3.1).
* **Contexts.** `Ctx = List Term`, head = innermost binding. `x ≤ t ∈ Γ` is
  `Ctx.Bound Γ x t`, which shifts the bound into whole-context scope.
  `x ∈ dom(Γ)` is `x < Γ.length`; the freshness premises of W-GAM2/P-CTX2 are
  vacuous in de Bruijn style. `fv(t) ⊆ dom(Γ)` is `Term.ClosedUnder Γ.length t`.
* **Mutual structure is preserved.** Figure 1's four judgments are one mutual
  block (DS-TRANS mentions `wf`, W-APP mentions `≤wf`); Figure 2's three are
  another (SRE-APP's premise is `≤*`). Lean's `induction` tactic cannot eliminate
  mutual predicates, so `Pss/Induction.lean` provides the joint induction
  principles (`decl_induction`, `alg_induction`) used throughout.
* **Conjectures are `Prop`s, never axioms.** Results the paper leaves open (or
  proves only in the PhD thesis [19]) and that are not yet mechanized are stated
  as `def ... : Prop` (collected in `Pss.Statements.*` namespaces) with status
  docstrings. The build contains **no `sorry` and no `axiom`**.

## Paper ↔ Lean correspondence

### Figure 1 — syntax, reduction, declarative system (`Syntax/Reduction/Declarative.lean`)

| Paper | Lean | Status |
|---|---|---|
| Terms `s,t,u ::= x \| Top \| λx≤t.u \| t(u)` | `Pss.Term` | defined |
| Values `v,w ::= Top \| λx≤t.u` | `Pss.Term.Value` | defined |
| Type contexts `Γ` | `Pss.Ctx` | defined |
| Type relations `⊲ ::= ≤ \| ≡` | `Pss.Rel` | defined |
| One-hole contexts `C`, `C[t]` | `Pss.TermCtx`, `TermCtx.fill` | defined |
| `[x ↦ t]u`, `fv`, `dom`, `x ≤ t ∈ Γ` | `Term.subst1`, `Term.ClosedUnder`, `· < Γ.length`, `Ctx.Bound` | defined |
| Reduction `t ⟶ t'` (E-CONG, E-APP) | `Pss.Step` | defined; depth-one closure equivalence `Step.step_iff_compat` proved |
| `Γ wf` (W-GAM1, W-GAM2) | `Pss.CtxWf` | defined |
| `Γ ⊢ t wf` (W-VAR, W-TOP, W-FUN, W-APP) | `Pss.Wf` | defined |
| `Γ ⊢ t ⊲wf u` (W-SUB) | `Pss.WellSub` | defined |
| `Γ ⊢ t ⊲ u` (DS-TRANS … DS-EVAR) | `Pss.Sub` | defined, one constructor per rule |
| Arrow sugar `t → u` (§3) | `Term.arrow` | defined |

### Figure 2 — algorithmic system (`Algorithmic.lean`)

| Paper | Lean | Status |
|---|---|---|
| `Γ prevalid` (P-CTX1, P-CTX2) | `Pss.Prevalid` | defined |
| `E≡`, `E≤` congruence contexts | `Pss.ECtx` (indexed by `Rel`) | defined |
| `t ⊲→ t'` (SRS-PROM, SRS-TOP, SRE-APP, SRE-TOPAPP, SR-CONG, SR-FUN, SR-EQ) | `Pss.Red` | defined, one constructor per rule |
| `Γ ⊢A t ⊲ u` (AS-REFL, AS-LEFT, AS-RIGHT) | `Pss.ASub` | defined |
| `Γ ⊢A t ⊲* u` (AST-SUB, AST-TRANS) | `Pss.ATSub` | defined |
| `⊲→*` sequences | `Pss.RedStar` | defined |
| p. 294 join characterization of `⊲` | `asub_iff_join`, `ASub.to_join`, `ASub.of_join` | **proved** |

### §3.5 — examples (`Examples.lean`)

| Paper | Lean | Status |
|---|---|---|
| Church `Nat`, `3` encodings | `Examples.nat`, `Examples.three` (+ `rfl` checks of the de Bruijn forms) | **proved** |
| `f(f(f(a))) ≤ x` derivation | `Examples.fff_le_x` (all DS-TRANS wf middles discharged) | **proved** |
| `3 ≤ Nat` | `Examples.three_le_nat` (declarative), `three_le_nat_wf` (`≤wf`), `three_le_nat_alg` (algorithmic) | **proved** |
| §3.5.1 `Nat + 3 ≡ Nat` | `Examples.nat_plus_three_eq_nat` (eight guarded SRE-APP steps; the `3 ≤* Nat` guard is the paper's "dynamic type check") | **proved** |

### §3.6 / §4.1 — universes (`Universes.lean`)

| Paper | Lean | Status |
|---|---|---|
| Tagged syntax `x^K`, universes `0/1` | `Universes.Tm`, tagged σ-calculus | defined |
| `t ∈ U(K)` judgment table | `Universes.InU` (+ uniqueness, totality, renaming-invariance) | **proved** |
| §4.1 modified W-APP | tagged duplicate of the Figure 1 block (`CtxWfT/WfT/WellSubT/SubT`) | defined |
| Tagged `Nat ∈ U(1)`, `3 ∈ U(0)` | `NatT_in_U1`, `ThreeT_in_U0` | **proved** |
| "universes preserved under β" | `InU.subst`, `subst1_preserves`, `beta_preserves` (substitution core); full wf version `Statements.universes_preserved_under_reduction` | core **proved**; full version stated (rests on Lemma 5.2 ⇒ Conjecture 5.1) |

### §7 — toy conditional rewrite system (`SimpleARS.lean`)

| Paper | Lean | Status |
|---|---|---|
| `A ⟶ C(A)`; `D(x,y) ⟶ x / ⟶ y if x = y`; `=` sym+trans closure of `⟶` | `SimpleARS.Step` / `SimpleARS.Conv`, mutually inductive | defined (verbatim; refl of `=` *derived*, not assumed) |
| local diagram around `D(a,b)` | `d_local_diagram`, generalized `Step.local_conv` | **proved** |
| `a = b ⇒ a ⟶⟶ · ⟵⟵ b` under confluence | `conv_joinable_of_confluent`, `conv_iff_joinable_of_confluent` | **proved** |
| confluence of the §7 system | `Statements.simpleARS_confluent` | stated (open; paper conjectures a proof adapts to λ⊲) |

### §4 — embedding of a PTS (`Embedding/`; intentionally minimal)

The user-facing focus of this development is λ⊲ itself and its type safety,
so §4 gets the minimal honest treatment: systems and translation defined,
the mechanical results proved, the thesis-level one stated.

| Paper | Lean | Status |
|---|---|---|
| System λ* (PTS, `* : *`) | `Pss.LambdaStar` (`Tm`, `Beta`, `Conv`, `Typing`) | defined |
| translation `⟨·⟩` | `Embedding.transTm` / `transCtx` | defined |
| Lemma 4.1 (substitution preserved) | `Embedding.lemma_4_1` | **proved** |
| Theorem 4.2 (reduction preserved) | `Embedding.thm_4_2` | **proved** |
| Theorem 4.3 (typing preserved) | `Statements.thm_4_3` | stated (thesis-level [19]; blockers documented) |
| Theorem 4.4 (λ⊲ not SN) | `Embedding.thm_4_4` | **proved** conditional on `GirardsParadox` (Barendregt [4]) and `Statements.thm_4_3` |

### §5, §6 (statuses finalized at merge)

| Paper | Lean | Status |
|---|---|---|
| §5 Conjecture 5.1, Lemmas 5.2–5.4, Thms 5.5–5.6 | `Pss/Safety.lean` & co. | _in progress_ |
| §6 Thm 6.1, Conjecture 6.2, Lemmas 6.3–6.4 | `Pss/Transitivity.lean` & co. | _in progress_ |

## Layout

```
Pss/
  Star.lean         closures (reflexive-transitive, symmetric)
  Syntax.lean       terms, σ-calculus substitution library, contexts, C[·]
  Reduction.lean    t ⟶ t' (Figure 1), strong normalization statement
  Declarative.lean  Figure 1 mutual block: CtxWf / Wf / WellSub / Sub
  Algorithmic.lean  Figure 2 mutual block: Prevalid / ECtx / Red / ASub / ATSub
  Induction.lean    joint induction principles for both mutual blocks
  Basic.lean        refl, prevalidity extraction, join characterization
```
