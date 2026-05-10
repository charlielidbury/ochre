# PSS Paper-to-Codebase Index

> Pasquale & García-Pérez 2024, "Towards the type safety of Pure Subtype
> Systems (Full version)" — arXiv 2407.13882 v2 (Dec 2025).
> Local PDF: `papers/pasquale-garcia-perez-2024-mpss.pdf` (46 pages).
>
> **This document is the source of truth for every proof in our codebase.**
> Before attempting any residual discharge, find the paper's proof here and
> read it.
>
> Pages cited are PDF page numbers (`9:N` in the paper's running heads).
>
> ## How to read the codebase column
>
> The active formalization is the **de Bruijn refactor** in `Pss/Syntax/DeBruijn.lean`,
> `Pss/Context/DeBruijn.lean`, and `Pss/Mpss/DeBruijn*.lean`. The locally-nameless
> tree was retired during Phase B. Per `AXIOMS.md`, the de Bruijn `_proved`
> endpoints depend only on kernel axioms (`propext`, `Quot.sound`,
> `Classical.choice`) plus *named residual hypotheses* (`UniformStrongCommutes`,
> `UniformEqDiamonds`, `BetaInstantiationPreservesWfM`, `AbsFunctionBoundInversion`,
> `WfMSubHeadReplaceOfNewWf`, plus per-cell transport payloads). Residuals are
> NOT custom Lean `axiom` declarations — they are explicit theorem arguments.
>
> Status legend:
> - **MECHANIZED** — direct Lean counterpart found, statement matches paper up to
>   de Bruijn vs. named-binder cosmetics.
> - **MECHANIZED-DIFFERENTLY** — counterpart exists but with a divergent
>   formulation (e.g. residual hypothesis instead of unconditional theorem).
> - **MECHANIZED (residual)** — Type/Prop residual is shipped; full discharge
>   open. The paper has a full proof.
> - **MISSING** — no counterpart exists in the de Bruijn tree. Often because
>   the paper-side lemma is folded into a different proof skeleton in our
>   formalization.
> - **DEFINITION-ONLY** — paper introduces a definition (no proof obligation).

---

## Section 2 — MPSS definitions

### Term grammar (paper p. 9:4)

**Statement.** `t, u, v, α ∈ Λ ::= x | Top | (λx ≤ t.u) | (u v)`. The Greek
letter `α` is a metavariable for terms originating as operands from the
stack. `α`-equivalence is assumed.

**Lean (de Bruijn form):** `Pss.DeBruijn.Term` at
`Pss/Syntax/DeBruijn.lean:18`.
```
inductive Term where
  | bvar : Nat → Term
  | top  : Term
  | abs  : (bound : Term) → (body : Term) → Term
  | app  : Term → Term → Term
```
**Difference vs paper:** de Bruijn `bvar i` replaces named `x`; the paper's
`λx ≤ t.u` is `.abs t body` with body's `bvar 0` referring to the abstracted
variable. There is no separate metavariable for stack operands.

### Logical context grammar (paper p. 9:4)

**Statement.** `Γ ::= ε | Γ, x ≤ t | Γ, x ≡ α`. Two annotation kinds: subtype
`x ≤ t` and equivalence `x ≡ α`. Notation `x ⊲ t` for either.

**Lean:** `Pss.DeBruijn.CtxEntryKind` at `Pss/Context/DeBruijn.lean:18`,
`Pss.DeBruijn.CtxEntry` at `Pss/Context/DeBruijn.lean:25`,
`Pss.DeBruijn.Ctx := List CtxEntry` at `Pss/Context/DeBruijn.lean:45`.

### Stack grammar (paper p. 9:4)

**Statement.** `s ::= nil | α :: s` — continuation stack à la Krivine.

**Lean:** `Pss.DeBruijn.Stack := List Term` at `Pss/Context/DeBruijn.lean:1303`.

### Substitution `u[x \ v]` (paper p. 9:4)

**Statement.** Standard capture-avoiding named substitution.

**Lean (de Bruijn analogue):** `Pss.DeBruijn.Term.instantiate` at
`Pss/Syntax/DeBruijn.lean:203`. Substitutes `v` for `bvar k` in `t`,
decrementing outer indices.

### Prevalidity of logical contexts `Γ prevalid` (Figure 1, p. 9:4)

| Rule | Paper page | Lean |
|---|---|---|
| `Pv-Emp` | 9:4 | `Pss.DeBruijn.Prevalid.empty` at `Pss/Context/DeBruijn.lean:1625` |
| `Pv-Ctx` (`Γ, x ≤ t prevalid`) | 9:4 | `Pss.DeBruijn.Prevalid.sub` at `Pss/Context/DeBruijn.lean:1627` |
| `Pv-EqA` (`Γ, x ≡ α prevalid`) | 9:4 | `Pss.DeBruijn.Prevalid.equ` at `Pss/Context/DeBruijn.lean:1631` |

**Difference:** the de Bruijn version drops the `x ∉ dom(Γ)` premise (no names)
and replaces `fv(t) ⊆ dom(Γ)` with the implicit scoping captured by
`Term.Scoped`; see `Pss/Context/DeBruijn.lean:1624`.

### Prevalidity of extended contexts `Γ; s prevalid` (Figure 1, p. 9:4)

| Rule | Paper page | Lean |
|---|---|---|
| `Pv-Nil` | 9:4 | `Pss.DeBruijn.PrevalidExt.nil` at `Pss/Context/DeBruijn.lean:1637` |
| `Pv-Sta` | 9:4 | `Pss.DeBruijn.PrevalidExt.cons` at `Pss/Context/DeBruijn.lean:1639` |

### Equivalence reduction `Γ; s ⊢ u →ᵉᵠᵘ v` (Figure 2, p. 9:5)

| Rule | Paper page | Lean (`MEqRed.*` at `Pss/Mpss/DeBruijnReductions.lean:18`) |
|---|---|---|
| `Me-Pro`  (variable promotion through `≡` binding) | 9:5 | `MEqRed.pro` at line 19  |
| `Me-Bet`  (β-step `(λx ≤ t.u) v →ᵉᵠᵘ u'[x\v']`) | 9:5 | `MEqRed.bet` at line 27. **Difference:** in de Bruijn, the body sub-derivation is a *single* derivation in context `(t :: Γ)` with shifted stack, not a cofinite quantification. The conclusion is `Term.instantiate 0 v' body'`. |
| `Me-Top` | 9:5 | `MEqRed.top` at line 35 |
| `Me-App`  (push operand to stack) | 9:5 | `MEqRed.app` at line 39 |
| `Me-Var`  (reflexive on in-scope variable) | 9:5 | `MEqRed.var` at line 45 |
| `Me-Fun`  (descend under unapplied abstraction with stack `nil`) | 9:5 | `MEqRed.fun_` at line 51 |
| `Me-TAp`  (`Top u →ᵉᵠᵘ Top`) | 9:5 | `MEqRed.tAp` at line 57 |
| `Me-FOp`  (pop operand into `≡` binding) | 9:5 | `MEqRed.fOp` at line 64 |

### Subtype reduction `Γ; s ⊢ u →ˢᵘᵇ v` (Figure 2, p. 9:5)

| Rule | Paper page | Lean (`MSubRed.*` at `Pss/Mpss/DeBruijnReductions.lean:72`) |
|---|---|---|
| `Ms-Pro` (variable to its `≤` annotation) | 9:5 | `MSubRed.pro` at line 73 |
| `Ms-Top` (any term to `Top`) | 9:5 | `MSubRed.top` at line 80 |
| `Ms-Equ` (subsume one equivalence step) | 9:5 | `MSubRed.equ` at line 86 |
| `Ms-App` (push operand to stack) | 9:5 | `MSubRed.app` at line 91 |
| `Ms-Fun` (descend under abstraction with stack `nil`) | 9:5 | `MSubRed.fun_` at line 97 |
| `Ms-FOp` (pop operand into `≡` binding) | 9:5 | `MSubRed.fOp` at line 104 |

### Diagrammatic subtype `u ≤ t` (paper p. 9:7, defined as ↦∗ followed by ←ᵉᵠᵘ)

**Statement.** `u ≤ t` iff `∃v. t →ᵉᵠᵘ v ∧ u ↦∗ v` where `↦` is the transitive
closure of `→ˢᵘᵇ`.

**Lean:** `Pss.DeBruijn.MSub` at `Pss/Mpss/DeBruijnTransitivityElim.lean:19`:
```
def MSub (Γ : Ctx) (s : Stack) (u v : Term) : Prop :=
  ∃ w, MSubRedStar Γ s u w ∧ MEqRedStar Γ s v w
```
**Difference:** the codebase uses `MSubRedStar` (`Relation.ReflTransGen MSubRed`)
in lieu of `↦∗`; equivalence reduction is also `Relation.ReflTransGen MEqRed`.

### Reduction of extended context `Γ; s ↣ Γ'; s'` (paper p. 9:7)

**Statement.** Two rules:
- `Ct-Ann`: `Γ; s ↣ Γ'; s'` and `Γ; nil ⊢ t →ᵉᵠᵘ t'` then `Γ, x ⊲ t; s ↣ Γ', x ⊲ t'; s'`
- `Ct-Stk`: `Γ; s ↣ Γ'; s'` and `Γ; nil ⊢ α →ᵉᵠᵘ α'` then `Γ; α :: s ↣ Γ'; α' :: s'`

**Lean:** in the de Bruijn refactor this evolution relation is folded into the
direct context- and stack-shift machinery; the explicit relation `↣` is not
maintained as an inductive. Rather, `MEqRedStar.weaken_head` and friends
(`Pss/Mpss/DeBruijnReductions.lean:1241`,
`Pss/Mpss/DeBruijnReductions.lean:1252`) and the `Stack.shift` /
`Stack.instantiate` operations (`Pss/Context/DeBruijn.lean:1308`,
`Pss/Context/DeBruijn.lean:1316`) play the corresponding role.

**Status:** MECHANIZED-DIFFERENTLY. The paper expresses context evolution as a
named relation; the de Bruijn formulation handles context evolution
pointwise via `Ctx.replaceAt`, `Ctx.insertAt`, and `Ctx.instantiateBetaPrefix`.

---

## Section 3 — Commutativity

The paper's headline theorem here is Theorem 1 (= Lemma 1 of the appendix);
the body of Section 3 is mostly motivation and the example in Figure 3.

### Theorem 1 / Lemma 1 (Strong commutativity, paper p. 9:7 statement; full proof p. 9:17–25)

**Statement.** Let `Γ; s` be a prevalid extended context. Let `t₀, t₁, t₂` be
terms. If `Γ; s ⊢ t₀ →ˢᵘᵇ t₁` and `Γ; s ⊢ t₀ →ᵉᵠᵘ t₂`, then for any extended
context `Γ'; s'` such that `Γ; s ↣ Γ'; s'`, there exists `t₃` such that
`Γ; s ⊢ t₂ →ᵉᵠᵘ t₃` and `Γ'; s' ⊢ t₁ →ˢᵘᵇ t₃`.

Diagrammatically (solid → dashed):
```
t₂ ─ᵉᵠᵘ──→ t₃
↑           ↑
ˢᵘᵇ        ˢᵘᵇ
↑           ↑
t₀ ─ᵉᵠᵘ──→ t₁
```

**Proof status (paper).** Full proof given (pages 17–20, before Lemma 2).

**Technique.** Induction on the term structure of `t₀`, then case analysis on
the *last rule* applied in the horizontal (subtype) and vertical (equivalence)
edges. The "horizontal edge" is `Ms-*`; the "vertical" is `Me-*`. Some cases
are trivial (`Top`, `TAp`); the `Ms-Equ` case dispatches to **Lemma 2**
(diamond on equivalence) and reflexivity (Proposition 18). The `Ms-Pro × Me-Pro`
case is impossible by prevalidity. The `Me-Var × Me-Pro` (sic — `Ms-Pro` with
`Me-Var`) case uses **Lemma 36** (context weakening commutes with `↣`) and
**Lemma 19** (weakening). The `Me-App × Me-App` case recurses on the operator,
threading the operand through the stack via `Ct-Stk`.

The proof carries a side observation: if the vertical edge does not apply
`Me-Pro` to a particular variable `x`, then the resulting top dashed
`Γ; s ⊢ t₂ →ᵉᵠᵘ t₃` need not apply `Me-Pro` to `x` either. This is the
"non-promotion-of-`x`" invariant inherited by Lemma 2.

**Case enumeration (Lemma 1, the paper case grid is at p. 9:17 onwards).**
All cases are subtype rule × equivalence rule combinations from the bottom-
left corner of the diagram.

| Last subtype (horiz.) | Last equiv. (vert.) | Paper page | Argument |
|---|---|---|---|
| `Ms-Top` | any `Me-*`           | 9:17 | trivial: `Me-Top` closes top, `Ms-Top` closes right. |
| `Ms-TAp` (means `Ms-Top` w/ `TopApp`) | `Me-TAp` | 9:17 | trivial. |
| any                       | `Me-Top`             | 9:17 | top edge by `Me-Top`, right edge by `Ms-Top`. |
| any                       | `Me-TAp`             | 9:17 | symmetric to above. |
| `Ms-Equ`                  | any `Me-*`           | 9:17 | reduce to **Lemma 2** + reflexivity (Prop. 18). |
| `Ms-Pro`                  | `Me-Pro`             | 9:17 | impossible by prevalidity (one variable cannot have both `≤` and `≡` annotations). |
| `Ms-Pro`                  | `Me-Var`             | 9:18 | use Lemma 36 (commutativity of context weakening), Ct-Ann to reflect equivalence step on context, Lemma 19 (weakening) to lift bound's reduction, then `Ms-Pro` from the new context. |
| `Ms-App`                  | `Me-App`             | 9:18 | recurse on operator under the stack (Ct-Stk gives the matching `Γ'; v₁ :: s'`); recurse on operand (Lemma 36 + IH); reassemble both edges via `Me-App` / `Ms-App`. |
| `Ms-App` (= `Me-App` head)| `Me-Bet`             | 9:22 | the operator is an abstraction. Equivalence side does β; subtype side does `Ms-App` whose result is necessarily `λx ≤ t.u₂` because no rule changes the bound. After the Ms-FOp inversion the body sub-derivation lives at `Γ, x ≡ v₀; s` which closes by IH on the body; final assembly uses **Lemma 32** (substitution-respecting reduction, `(λy ≤ a.b)c →ᵉᵠᵘ b'[y\c']` lemma). |
| `Ms-Fun`                  | `Me-Fun`             | 9:18 | both descend with `s = nil`, IH on `t` (bound) and on `u` (body in extended ctx). Reassemble. |
| `Ms-FOp`                  | `Me-FOp`             | 9:19 | both pop the same operand into `≡`-binding; IH on body; reassemble. |
| `Ms-Pro` / `Ms-Top`       | `Me-Bet`             | (subsumed by trivial / variable cases — `Ms-Pro` of an application is structurally absurd) | |

**Lean counterpart.** The paper's "single-step Lemma 1" is the following Prop:
```
abbrev StrongCommutes (Γ : Ctx) (s : Stack) : Prop :=
  ∀ {t₀ t₁ t₂ : Term},
    MSubRed Γ s t₀ t₁ →
    MEqRed Γ s t₀ t₂ →
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MSubRedJ Γ s t₂ t₃
```
at `Pss/Mpss/DeBruijnTransitivityElim.lean:695`, with alias
`Lemma_1_DeBruijn_StrongCommutativity` at line 703.

The de Bruijn formulation **drops** the explicit "for all `Γ'; s'` such that
`Γ; s ↣ Γ'; s'`" generalization. In de Bruijn, name freshness is built in,
so the right edge lives in the same `Γ; s` and the generalization is vacuous.
This is one of the structural payoffs of the encoding switch.

The chain-form lifting from single-step to chain-of-steps is at:
- `Lemma_1_DeBruijn_StrongCommutativityStar_of` at line 17546 (Prop chain).
- `Lemma_1_DeBruijn_StrongCommutativityChain_of` at line 17523 (Type chain).
- `Lemma_1_DeBruijn_step_eqStar_of` at line 17535 (single subtype step
  against equivalence chain).

The **proved endpoints**, conditional on `UniformStrongCommutes` (universal
single-step `StrongCommutes Γ s` at every extended context):
- `Pss.DeBruijn.Lemma_1_DeBruijn_StrongCommutativityStar_proved` at
  `Pss/Mpss/DeBruijnTypeSafety.lean:36684`.
- `Pss.DeBruijn.Lemma_1_DeBruijn_StrongCommutativityChain_proved` at
  `Pss/Mpss/DeBruijnTypeSafety.lean:36697`.

**Per-cell case grid in Lean.** The `StrongCommutes` namespace at
`Pss/Mpss/DeBruijnTransitivityElim.lean` lines 706–onward gives per-cell
helpers. Exhaustive list (filename: `DeBruijnTransitivityElim.lean`):
- `top` (line 710), `pro_var` (720), `pro_pro_vacuous` (728), `pro_any`
  (738), `equ_var` (749), `equ_of` (758), `top_of` (766), `bvar_any_of`
  (775), `bvar_any` (789), `appTop_top_tAp` (802), `appTop_top_app` (807),
  `appTop_app_tAp` (817), `appTop_any` (829), and the cross-β cells
  (`equ_bet_chain_*`, `app_bet_chain_*`, `equ_bet_chain_ArgNoBinders_of`,
  etc.) shipped as restricted partial discharges (see commits described
  in `AXIOMS.md`).

**Status:** MECHANIZED (residual). Closure depends on `UniformStrongCommutes`
(universal companion) which expands the case grid into the full ~36 sub-cells.
Each cell is either complete or shipped restricted (see `AXIOMS.md` Group A /
Group C taxonomy).

---

### Lemma 2 (Diamond property of `→ᵉᵠᵘ`, paper p. 9:9 statement; full proof p. 9:21–25)

**Statement.** Let `Γ₀; s₀` be a prevalid extended context. Let `t₀, t₁, t₂`
be terms. If `Γ₀; s₀ ⊢ t₀ →ᵉᵠᵘ t₁` and `Γ₀; s₀ ⊢ t₀ →ᵉᵠᵘ t₂`, then for any
extended contexts `Γ₁; s₁` and `Γ₂; s₂` such that `Γ₀; s₀ ↣ Γ₁; s₁` and
`Γ₀; s₀ ↣ Γ₂; s₂`, there exists `t₃` such that `Γ₁; s₁ ⊢ t₁ →ᵉᵠᵘ t₃` and
`Γ₂; s₂ ⊢ t₂ →ᵉᵠᵘ t₃`. Plus the non-promotion-of-`x` invariant: if neither
input derivation promotes `x` via `Me-Pro`, neither output does either.

**Proof status (paper).** Full proof given (p. 9:21–25).

**Technique.** Induction on the derivation tree of `Γ₀; s₀ ⊢ t₀ →ᵉᵠᵘ t₁`,
case analysis on the last two rules (one in each derivation), starting from
the bottom-left corner. Base cases when both are `Me-Top` (resp. both
`Me-Var`).

**Case enumeration (Lemma 2 case grid, p. 9:21–25).**

| Last `Me-*` (left) | Last `Me-*` (right) | Paper page | Argument |
|---|---|---|---|
| `Me-Pro` | `Me-Var` | 9:21 | use Lemma 36 + Ct-Ann + Lemma 19 (weakening) + IH on bound; reassemble with `Me-Pro` on the new ctx. |
| `Me-Pro` | `Me-Pro` | 9:21 | same `α₀ ≡ x` annotation by prevalidity uniqueness; IH on bound; both sides reassemble with `Me-Pro`. |
| `Me-App` | `Me-App` | 9:21–22 | recurse on operator under stack `v₀ :: s₀` via Ct-Stk on the right edges; recurse on operand at empty stack via Lemma 36; reassemble each side with `Me-App`. |
| `Me-App` | `Me-Bet` | 9:22 | mixed: subtype-side `Me-App` of `λx ≤ t₀.u₀ v₀` reduces to `λx ≤ t₁.u₁ v₁`; equiv-side does β to `u₂[x\v₂]`. The `Ms-FOp` inversion in `Me-App` exposes the body derivation in `Γ₀, x ≡ v₀; s₀`; IH on body and operand; reassemble equiv side with `Me-Bet`; reassemble subtype side with **Lemma 32** (substitution under reduction). |
| `Me-App` | `Me-TAp` | 9:23 | `Me-TAp`'s output is `Top`; closure trivial via `Me-Top` and `Me-TAp`. |
| `Me-Fun` | `Me-Fun` | 9:23 | `s₀ = nil` forced; IH on bound (closed) and IH on body in extended ctx; both reassemble with `Me-Fun`. |
| `Me-FOp` | `Me-FOp` | 9:24 | shared operand `α₀` from stack; IH on bound (Ct-Stk), IH on body (Ct-Ann under `≡`-extension); reassemble. |
| `Me-Bet` | `Me-Bet` | 9:25 | both do β; IH on body in `Γ₀; s₀ ⊢ u₀`; IH on operand at empty stack; both sides re-fire β with the IH targets. Lemma 19 weakening lifts body residuals into the right-edge contexts. |
| `Me-TAp` | `Me-TAp` | 9:25 | both produce `Top`; close with `Me-Top`. |

**Lean counterpart.** Single-step:
```
abbrev EqDiamonds (Γ : Ctx) (s : Stack) : Prop :=
  ∀ {t₀ t₁ t₂ : Term}, MEqRed Γ s t₀ t₁ → MEqRed Γ s t₀ t₂ →
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MEqRedJ Γ s t₂ t₃
```
at `Pss/Mpss/DeBruijnTransitivityElim.lean:230`, with alias
`Lemma_2_DeBruijn_DiamondMEqRed` at line 238.

Star and chain forms at:
- `Lemma_2_DeBruijn_DiamondMEqRedStar_of` at line 656.
- `Lemma_2_DeBruijn_DiamondMEqRedChain_of` at line 682.
- `Lemma_2_DeBruijn_step_eqStar_of` at line 646.

Proved endpoints, conditional on `UniformEqDiamonds` and per-cell transports:
- `Pss.DeBruijn.Lemma_2_DeBruijn_DiamondMEqRedStar_proved` at
  `Pss/Mpss/DeBruijnTypeSafety.lean:22249`.
- `Pss.DeBruijn.Lemma_2_DeBruijn_DiamondMEqRedChain_proved` at
  `Pss/Mpss/DeBruijnTypeSafety.lean:22263`.

Per-cell case grid in `EqDiamonds` namespace at
`Pss/Mpss/DeBruijnTransitivityElim.lean:241`+: `top` (245), `var_var` (255),
`refl_left` (263), `refl_right` (270), `pro_var` (276), `var_pro` (283),
`pro_pro_of` (294), `bvar_any_of` (306), and many `appTop_*`, `app_app_of`,
`fun_fun_of`, `fOp_fOp_of`, plus the cross-β cells discharged restricted
under `Term.NoBinders` / `Term.AbsFree` premises (see
`AXIOMS.md` Group C).

**Status:** MECHANIZED (residual). Closure depends on `UniformEqDiamonds` and
per-cell transports `MEqRedArgTransportPayload`,
`MEqRedOpStackHeadTransportPayload`, `MEqRedSubBridgePayload`. Restricted
variants (`*_NoBinders_proved`, `*_AbsFree_proved`) are unconditional.

---

### Theorem 3 (Transitivity is admissible, paper p. 9:9 statement; proof on p. 9:25–26)

**Statement.** Let `Γ; s` be an extended context. Let `u, v` be terms. If
`Γ; s ⊢ u ≤∗ v` (the transitive closure of `≤`) then `Γ; s ⊢ u ≤ v`.

**Proof status (paper).** Full proof given (p. 9:25–26 — proof at top of
9:26).

**Technique.** Induction on the number of intermediate `≤` steps in
`u ≤∗ v`. Base case (0 or 1): trivial. Inductive step: from `t ≤ u` and
`u ≤ v` one gets a "stair" diagram of `→ˢᵘᵇ` chains and `→ᵉᵠᵘ` chains; the
diagram is flattened to a single `≤` step using **Theorem 1** (Lemma 1
strong commutativity) on each corner.

**Lean.** `Pss.DeBruijn.Theorem_3_DeBruijn_TransitivityIsAdmissible_of` at
`Pss/Mpss/DeBruijnTransitivityElim.lean:17695`. Proved endpoint:
`Pss.DeBruijn.Theorem_3_DeBruijn_TransitivityIsAdmissible_proved` at
`Pss/Mpss/DeBruijnTypeSafety.lean:36743`.

**Status:** MECHANIZED (residual). Closure depends on `UniformStrongCommutes`.

---

## Section 4 — Towards a Type-Safe System

### Term well-formedness `Γ ⊢ t wf` (Figure 4, paper p. 9:11)

| Rule | Paper | Lean (`WfM.*` at `Pss/Mpss/DeBruijnWellFormed.lean:23`) |
|---|---|---|
| `Wf-PrS` (`x ≤ t ∈ Γ`) | 9:11 | `WfM.varSub` at line 25 |
| `Wf-PrE` (`x ≡ α ∈ Γ`) | 9:11 | `WfM.varEqu` at line 28 |
| `Wf-Top`           | 9:11 | `WfM.top` at line 31 |
| `Wf-Fun`           | 9:11 | `WfM.fun_` at line 34 |
| `Wf-App`           | 9:11 | `WfM.app` at line 39 — note that the paper's `Γ ⊢ u ≤∗_wf λx ≤ t.Top` becomes `WSubMStar Γ u (.abs t .top)`. |

### Transitive well-subtyping `Γ ⊢ v ⊲∗_wf t` (Figure 4, p. 9:11)

| Rule | Paper | Lean (`WSubMStar.*` at `Pss/Mpss/DeBruijnWellFormed.lean:68`) |
|---|---|---|
| `Ws-Sub` | 9:11 | `WSubMStar.sub` at line 69 |
| `Ws-Trs` | 9:11 | `WSubMStar.trs` at line 73 |

### Well-subtyping `Γ ⊢ u ⊲_wf t` (Figure 4, p. 9:11)

| Rule | Paper | Lean (`WSubM.*` at `Pss/Mpss/DeBruijnWellFormed.lean:45`) |
|---|---|---|
| `Ws-Rfl`  | 9:11 | `WSubM.rfl` at line 46 |
| `Ws-Lf1` (prepend `→ᵉᵠᵘ`) | 9:11 | `WSubM.lf1` at line 49 |
| `Ws-Lf2` (prepend `→ˢᵘᵇ` with both endpoints wf) | 9:11 | `WSubM.lf2` at line 54 |
| `Ws-Rgh` (append `→ᵉᵠᵘ` on right)  | 9:11 | `WSubM.rgh` at line 61 |

The paper's `≤_wf` and `≡_wf` are projections of `⊲_wf`; in Lean we expose
both `WSubM` and `WEquM` (`Pss/Mpss/DeBruijnWellFormed.lean:88`).

### Operational semantics `t ↦ t'` (paper p. 9:12)

**Statement.** Reduction inside arbitrary contexts (`Os-Con`) of β-reduction
(`Os-Bet`). Evaluation contexts `C ::= □ | (λx ≤ C.t) | (λx ≤ t.C) | (C t) | (t C)`.

**Lean:** `Pss.DeBruijn.StepAt` at `Pss/Reduction/DeBruijnOperational.lean:21`,
with closed alias `Step := StepAt 0` at line 44. The de Bruijn version is
indexed by ambient depth, allowing congruence under abstractions to be stated
directly at `depth + 1` without context syntax.

| Paper rule | Lean constructor (`StepAt.*`) |
|---|---|
| `Os-Bet`            | `StepAt.beta` at line 22 |
| `Os-Con` (left arg) | `StepAt.appL` at line 26 |
| `Os-Con` (right arg) | `StepAt.appR` at line 30 |
| `Os-Con` (under abs, bound) | `StepAt.absBound` at line 34 |
| `Os-Con` (under abs, body) | `StepAt.absBody` at line 38 |

### Theorem 4 (Progress, paper p. 9:12 statement; proof p. 9:26)

**Statement.** Let `t` be a term. For every logical context `Γ`, if
`Γ ⊢ t wf` then either `t` is in normal form, or there exists `t'` such that
`t ↦ t'`.

**Proof status (paper).** Full proof given (p. 9:26).

**Technique.** Structural induction on `t`. Case analysis: `Top` is NF,
variable is NF, abstraction `λx ≤ t.u`: if `u ∉ NF` use IH; if `u ∈ NF` and
`t ∈ NF` then NF; otherwise reduce `t`. Application `u v`: if `u ∉ NF` reduce
operator; if `v ∉ NF` reduce operand; if both NF, do case analysis on `u`:
- `u = Top` impossible by **Lemma 11** (no supertype of `Top` is a function).
- `u` is a function `λx ≤ a.b`: redex; reduce by `Os-Bet`.
- `u` is a neutral applied to NFs: stay in NF.

The codebase phrases progress for *closed* terms with `Γ = []`; the paper's
"every logical context" generalization isn't separately mechanized.

**Lean.**
- `Theorem_4_DeBruijn_Progress_of` at `Pss/Mpss/DeBruijnTypeSafety.lean:108`
  — conditional on `NoTopFunctionSupertypes` (factor extracted from the
  paper's Lemma 11 use).
- `Theorem_4_DeBruijn_Progress_of_StrongCommutativity` at line 156 —
  derives the `NoTopFunctionSupertypes` premise from `StrongCommutes [] []`.
- `Theorem_4_DeBruijn_Progress_proved` at line 36755 — conditional on the
  universal residual `UniformStrongCommutes`.
- Auxiliary: `NoTopFunctionSupertypes` (line 17), `NoTopFunctionSupertypesAt`
  (22), `NoTopAbstractionSupertypesAt` (27), each derived from
  `StrongCommutes` via `NoTopAbstractionSupertypesAt_of` (61),
  `NoTopFunctionSupertypes_of` (81). The derivation chain corresponds to
  the paper's Lemma 11 use.

**Status:** MECHANIZED (residual). Closure depends on `UniformStrongCommutes`.

---

### Theorem 5 (Preservation, paper p. 9:12 statement; proof p. 9:26)

**Statement.** Let `Γ` be a logical context. Let `t, t', u` be terms. If
`Γ ⊢ t ≤∗_wf u` and `t ↦ t'`, then `Γ ⊢ t' ≤∗_wf u`.

**Proof status (paper).** Full proof given (p. 9:26).

**Technique.** Use `Ws-Trs` to split: prove `Γ ⊢ t' ≤∗_wf t` (which composes
with the assumption to give `t' ≤∗_wf u`). For `t' ≤∗_wf t` it suffices to
show `t' ⊲∗_wf t`; from `t ↦ t'` use **Lemma 6** (evaluation preserves
well-formedness) and Proposition 12 to get `Γ ⊢ t' wf`. Then `Ws-Lf1`
prepends one equivalence step from operational reduction (Proposition 17) to
get `Γ ⊢ t' ⊲_wf t`, hence `Γ ⊢ t' ⊲∗_wf t`, hence `Γ ⊢ t' ≤∗_wf t` by
`Ws-Sub`. Compose by `Ws-Trs`.

**Lean.**
- `Theorem_5_DeBruijn_Preservation_of` at
  `Pss/Mpss/DeBruijnTypeSafety.lean:16307` — conditional on
  `StepPreservesWfM`.
- `Theorem_5_DeBruijn_ClosedPreservation_of` at line 16321.
- Component closures from `Pss/Mpss/DeBruijnTypeSafety.lean:16332`+:
  `_components`, `_components_and_direct_sub_replace`,
  `_components_and_immediate_sub_replace_and_under`,
  `_diagram_components`, `_chain_diagram_components`,
  `_chain_shape_components`, `_chain_shape_meq_components`,
  `_chain_shape_meq_components_and_direct_sub_replace`,
  `_chain_shape_meq_components_and_immediate_sub_replace_and_under`.
- **Proved endpoints:**
  - `Theorem_5_DeBruijn_Preservation_proved` at line 36772.
  - `Theorem_5_DeBruijn_ClosedPreservation_proved` at line 36785.

**Status:** MECHANIZED (residual). Conditional on
`BetaInstantiationPreservesWfM` (Lemma 7 analogue),
`AbsFunctionBoundInversion` (Lemma 10 analogue), and
`WfMSubHeadReplaceOfNewWf` (sharpened `.sub` head replacement). See
`AXIOMS.md` Group B for the discharge taxonomy. v4/v5/v6 partial surfaces
exist (`Pss/Sanity.lean:68`+) reducing premises further.

---

### Lemma 6 (Evaluation preserves well-formedness, paper p. 9:12 statement; proof p. 9:27)

**Statement.** Let `Γ` be a logical context. Let `t, t'` be terms such that
`t ↦ t'` and `Γ ⊢ t wf`. We have `Γ ⊢ t' wf`.

**Proof status (paper).** Full proof given (p. 9:27).

**Technique.** Induction on `t ↦ t'` by last operational rule:
- `Os-Bet` (β): use **Lemma 10** (Inversion) on `λx ≤ u.v ≤∗_wf λx ≤ z.Top` to
  obtain `Γ ⊢ u ≡_wf z`. Use Lemmas 15, 16 to lift this to `≤∗_wf` and apply
  `Ws-Sub`. By transitivity (Ws-Trs) `Γ ⊢ w ≤∗_wf u`. From the substitution
  side (Wf-Fun, Prop 12) get `Γ, x ≤ u ⊢ v wf`. Apply **Lemma 7**
  (Substitution preserves well-formedness) to conclude `Γ ⊢ v[x\w] wf`.
- `Os-Con` for `λx ≤ u.v` with `u ↦ u'`: IH on bound, then **Proposition 17**
  to lift `u ↦ u'` to `Γ; nil ⊢ u →ᵉᵠᵘ u'`, then **Lemma 23**
  (well-formedness narrowing under context bound change) to migrate body's
  well-formedness, then `Wf-Fun`.
- `Os-Con` for `λx ≤ u.v` with `v ↦ v'`: IH on body in extended ctx, `Wf-Fun`.
- `Os-Con` for `u v` with `u ↦ u'`: IH; use **Lemma 27** (well-subtyping
  preserved under reduction) to migrate the operator's `≤∗_wf` against the
  new operator. `Wf-App` reassembles.
- `Os-Con` for `u v` with `v ↦ v'`: similar with **Lemma 27** on the operand.

**Lean.** This lemma is folded into `StepPreservesWfM` and its components
in `Pss/Mpss/DeBruijnTypeSafety.lean`. There is no single Lean theorem named
`Lemma_6_*`. Direct counterparts:
- `MEqRedPreservesWfM` (Type) at line 4222 — equivalence-step preservation.
- `MEqRedPreservesWfMContextual` at line 4227.
- `MEqRedPreservesWfM_top` (4257), `_var` (4264), `_tAp` (4273) —
  unconditional case discharges.
- `MEqRedPreservesWfM_partial` (4287) — assembles partial discharge with
  the four open arms (`pro`, `bet`, `app`, `fun_`) as named hypotheses.
- The closed operational version is `StepPreservesWfM` (assembled from
  `BetaInstantiationPreservesWfM`, `AbsFunctionBoundInversion`,
  `WfMSubHeadReplaceOfNewWf`).

**Status:** MECHANIZED-DIFFERENTLY (residual). The single paper Lemma 6 is
factored across MEqRedPreservesWfM and StepPreservesWfM; closure goes through
`Theorem_5_DeBruijn_*_proved`'s residuals. No sole `Lemma_6_*` symbol exists.

---

### Lemma 7 (Substitution preserves well-formedness, paper p. 9:12 statement; proof p. 9:27–30)

**Statement.** Let `Γ, Γ'` be logical contexts; `t, u, α` be terms; `x` a
variable. If `Γ, x ≤ t, Γ' ⊢ u wf`, and `Γ ⊢ α ≤∗_wf t`, then
`Γ, Γ'[x\α] ⊢ u[x\α] wf`.

**Proof status (paper).** Full proof given (p. 9:27–30, with subinduction).

**Technique.** First show `Γ, Γ'[x\α]` is prevalid by **Lemma 28**
(substitution preserves prevalidity). Induction on `Γ, x ≤ t, Γ' ⊢ u wf`:
- `Wf-PrS / Wf-PrE` with `u = y ≠ x`: substitution descends; conclude by
  `Wf-PrS`/`Wf-PrE` from the substituted annotation.
- `Wf-PrS / Wf-PrE` with `u = x`: well-formed `α` lifts via Lemma 19 (weakening).
- `Wf-Top`: Wf-Top reuses prevalidity.
- `Wf-Fun`: assume `y ≠ x` by α-conversion. IH on bound and body.
- `Wf-App`: separate sub-induction on the inner `u' ≤∗_wf λx ≤ z.Top`
  derivation, transforming step-by-step using `Ws-Sub`/`Ws-Trs`. Crucial
  helper: a sub-induction proving that for every `a ≤_wf b` subterm of the
  outer `≤∗_wf`, the substituted `a[x\α] ≤∗_wf b[x\α]` exists, with
  intermediate witnesses `a', b', c'` linked by `→∗ᵉᵠᵘ`. Two sub-cases on
  `a ≤_wf b`:
  - `Ws-Lf1`, `Ws-Lf2`, `Ws-Rgh`, `Ws-Rfl` — each produces a witness via
    **Lemma 31** (reduction under substitution), with case `Ws-Lf2` further
    splitting on whether the sub-derivation makes promotion-of-`x`. If yes,
    use **Lemma 9** to get `a[x\α] ≤∗_wf a₀[x\α]` directly. If no, use
    **Lemma 30** for the equivalent reduction on the substituted side.
- `(λy ≤ z.Top)[x\α]` reasoning collapses similarly.

**Lean.** Mechanized as `BetaInstantiationPreservesWfM` (Type) at
`Pss/Mpss/DeBruijnTypeSafety.lean:193`:
```
def BetaInstantiationPreservesWfM : Type :=
  ∀ {Γ : Ctx} {bound body arg : Term}, ...
```
Family of helpers feeding it: `BetaInstantiationPreservesWSubMStar` (201),
`BetaInstantiationPreservesWSubM` (210), `BetaInstantiationPreservesMEqRed`
(218), `BetaInstantiationPreservesMSubRed` (226), and many "under heads"
generalizations starting line 337. The reduction-under-substitution side is
covered by `MEqRedRespectsBetaInstantiateStack_proved` (proved, commit
`a5aaf59`) and `BetaInstantiationPreservesMEqRedStack_proved` (proved, commit
`7ec6954`). The kind-narrowing helper
`MEqRedFusedKindNarrowedBetaSubstStack_proved` (proved, commit `98a62a2`)
covers the cross-`.sub`/`.equ` migration.

**Status:** MECHANIZED (residual). The `BetaInstantiationPreservesWfM` Type
itself is shipped as a residual feeding `Theorem_5_DeBruijn_Preservation_proved`.
Most supporting infrastructure is unconditional.

---

### Conjecture 8 (Well-subtyping is context independent, paper p. 9:13)

**Statement.** Let `Γ` be a logical context and `u, t` be terms such that
`Γ ⊢ u ≤∗_wf t`. Let `Co` be a covariant context such that both `Co[u]` and
`Co[t]` are well-formed in `Γ`. We conjecture that `Γ ⊢ Co[u] ≤∗_wf Co[t]`.

**Proof status (paper).** Conjecture (no proof). Used in **Lemma 9**
(Promotion under substitution outside of covariant contexts).

**Lean.** Per `AXIOMS.md`, Conjecture 8 is the one permanent paper-level
axiom. The de Bruijn analogue is not currently shipped as an `axiom`
declaration (the de Bruijn side has zero custom axioms); rather, downstream
consumers carry it as a hypothesis where needed. Lemma 9's partial uses are
folded into the substitution machinery without instantiating Conjecture 8.

**Status:** MISSING (intentional — paper-faithful open problem).

---

## Appendix A — Theorems of the text

This appendix repeats Theorem 1, Lemma 2, Theorem 3, Theorem 4, Theorem 5,
Lemma 6, Lemma 7, then **Lemma 9–36** as supporting lemmas.

### Lemma 9 (Promotion under substitution outside of covariant contexts, paper p. 9:30 statement; proof p. 9:31)

**Statement.** Let `Γ; s` be an extended context, `Γ'` a logical context,
such that `Γ, Γ'[x\α]; nil` is prevalid. Let `u, v, t, α` be terms with
both `u[x\α]` and `v[x\α]` well-formed in `Γ, Γ'[x\α]`. If
`Γ, x ≤ t, Γ'; nil ⊢ u →ˢᵘᵇ v` and `Γ ⊢ α ≤∗_wf t`, then
`Γ, Γ'[x\α] ⊢ u[x\α] ≤∗_wf v[x\α]`.

**Proof status (paper).** Full proof given (p. 9:31). Two sub-cases on the
shape of the derivation:
- **If** the derivation is `Co[x] →ˢᵘᵇ Co[t]` for a covariant context `Co`:
  use weakening (Lemma 19) on `Γ ⊢ α ≤∗_wf t` then **Conjecture 8** to get
  `Co[x][x\α] ≤∗_wf Co[t][x\α]`. Prevalidity removes residual `x` instances.
- **Else:** apply **Lemma 30** to get `Γ, Γ'[x\α]; nil ⊢ u[x\α] →ˢᵘᵇ v[x\α]`,
  then `Ws-Rfl` and `Ws-Lft` give the result.

**Lean.** No standalone `Lemma_9_*` declaration exists. Supporting role
shipped via `MSubRed.respect_substitution_*` helpers and the
`BetaInstantiationPreserves*` family. Used implicitly inside Lemma 7
(`BetaInstantiationPreservesWfM`).

**Status:** MISSING (folded into substitution preservation suite). Conjecture 8
covers half the case grid.

---

### Lemma 10 (Inversion lemma, paper p. 9:31)

**Statement.** Let `Γ` be a logical context and `λx ≤ t.u, λx ≤ t'.u'` be
terms. If `Γ ⊢ λx ≤ t.u ≤∗_wf λx ≤ t'.u'`, then `Γ ⊢ t ≡_wf t'`.

**Proof status (paper).** Full proof given (p. 9:31).

**Technique.** Induction on the number of transitivity steps in
`λx ≤ t.u ≤∗_wf λx ≤ t'.u'`, applying **Proposition 13** (well-subtyping →
subtyping) then **Theorem 3** (transitivity elimination) to flatten to one
`λx ≤ t.u ≤ λx ≤ t'.u'`. Definition unpacking yields a reduction `→∗ z` from
both sides; only `Me-Fun` (or `Ms-Fun`) can apply on these abstractions, so
`z = λx ≤ t_z.u_z`. Use `Ws-Rfl` and induction on the reduction lengths to
chain `Γ ⊢ t ≡_wf t_z` and `Γ ⊢ t' ≡_wf t_z`, then **Ws-Rgh** + **Ws-Lf1**
to close `t ≡_wf t'`.

**Lean.** `AbsFunctionBoundInversion` (Type) at
`Pss/Mpss/DeBruijnTypeSafety.lean:4051`. Plus the under-WfCtx variant
`AbsFunctionBoundInversionUnderWfCtx`. The pipeline
`Theorem_3_DeBruijn_AbsFunctionBoundChainShapePayload_of` (line 10500) is
the Lean realization of the paper's chain-shape inversion idea, conditional
on `UniformStrongCommutes` and `MEqRedPreservesWfM`.

**Status:** MECHANIZED (residual). Conditional on `UniformStrongCommutes` +
`MEqRedPreservesWfM`. Open as a free-standing theorem; chain-shape pipeline
discharges it modulo those two universal residuals.

---

### Theorem 11 (No supertype of `Top` is a function, paper p. 9:31)

**Statement.** Let `Γ; s` be an extended context. Let `λx ≤ t.u` be a term.
We cannot have `Γ; s ⊢ Top ≤∗ λx ≤ t.u`.

**Proof status (paper).** Full proof given (p. 9:31–32).

**Technique.** First apply Theorem 3 (transitivity elimination) to flatten
to `Top ≤ λx ≤ t.u`. By definition there exists `w` with `Top →ˢᵘᵇ∗ w` and
`λx ≤ t.u →ᵉᵠᵘ∗ w`. Only `Ms-Equ` and `Ms-Top` can apply to `Top`, forcing
`w = Top`. Only `Me-Fun` or `Me-FOp` apply to `λx ≤ t.u`, so `w` is an
abstraction — contradicting `w = Top`.

**Lean.** Folded into `NoTopFunctionSupertypes` and `NoTopAbstractionSupertypesAt`
at `Pss/Mpss/DeBruijnTypeSafety.lean:17`+, derived from `StrongCommutes`
via `NoTopAbstractionSupertypesAt_of` (61) and `NoTopFunctionSupertypes_of`
(81). Used by `Theorem_4_DeBruijn_Progress_of` (line 108).

**Status:** MECHANIZED. Conditional on `StrongCommutes` (so transitively on
`UniformStrongCommutes`).

---

## Appendix B — Rest of the appendix

### Proposition 12 (Well-formedness extraction, paper p. 9:32)

**Statement.** Let `Γ` be an extended context and `u, v` be terms. If
`Γ ⊢ u ≤∗_wf v` then both derivations `Γ ⊢ u wf` and `Γ ⊢ v wf` exist in the
derivation tree of `Γ ⊢ u ≤∗_wf v`.

**Proof status (paper).** Full proof given (p. 9:32). Induction on the
`≤∗_wf` derivation; `Ws-Sub` and `Ws-Trs` cases.

**Lean.** Direct counterparts:
- `WSubMStar.wf_left` at `Pss/Mpss/DeBruijnWellFormed.lean:441`.
- `WSubMStar.wf_right` at line 461.
- `WSubMStar.wf_pair` at line 481.

**Status:** MECHANIZED.

---

### Proposition 13 (From well-subtyping to subtyping, paper p. 9:32)

**Statement.** Let `Γ` be a logical context and `u, v` be terms. If
`Γ ⊢ u ≤_wf v` then `Γ; nil ⊢ u ≤ v`.

**Proof status (paper).** Full proof given (p. 9:32). Induction on
`Γ ⊢ u ≤_wf v` by last rule (`Ws-Rfl`, `Ws-Lf1`, `Ws-Lf2`, `Ws-Rgh`).

**Lean.** Realized inside the `WSubM.toMSub` map at
`Pss/Mpss/DeBruijnTransitivityElim.lean:17703`. The map sends one
well-subtyping derivation to one diagrammatic subtyping witness.
Continuation via `WSubMStar.toMSubStar` at line 17743 lifts this to chains.

**Status:** MECHANIZED.

---

### Proposition 14 (From well-equivalence to equivalence, paper p. 9:32)

**Statement.** If `Γ ⊢ u ≡_wf v` then `Γ; nil ⊢ u ≡ v`.

**Proof status (paper).** Full proof given (p. 9:32–33). Mirror of
Proposition 13.

**Lean.** Realized inside `WEquM.toMSub` at
`Pss/Mpss/DeBruijnTransitivityElim.lean:17782` via `WEquM.toWSubM` then
Proposition 13's `WSubM.toMSub`.

**Status:** MECHANIZED.

---

### Lemma 15 (Symmetry of `≡_wf`, paper p. 9:33)

**Statement.** If `Γ ⊢ u ≡_wf v` then `Γ ⊢ v ≡_wf u`.

**Proof status (paper).** Full proof given (p. 9:33). Induction on
`Γ ⊢ u ≡_wf v` by last rule.

**Lean.** Direct counterpart: `WEquM.symm` (would be at
`Pss/Mpss/DeBruijnWellFormed.lean`). Search:

**Status:** MECHANIZED-DIFFERENTLY. In the de Bruijn tree, well-equivalence
symmetry is a derived property used in `WEquMStar.toWSubMStar` and
`WEquM.toWSubM`; no standalone `Lemma_15_*` declaration. Search for
`WEquMStar.symm` / `WEquM.symm` in `DeBruijnWellFormed.lean` if needed.

---

### Lemma 16 (`≡_wf` ⊆ `≤_wf`, paper p. 9:33)

**Statement.** If `Γ ⊢ u ≡_wf v` then `Γ ⊢ u ≤_wf v`.

**Proof status (paper).** Full proof given (p. 9:33). Induction on
derivation; `Ws-Rfl`, `Ws-Lf1`, `Ws-Rgh` cases (no `Ws-Lf2` because `≡_wf`
disallows it).

**Lean.** `WEquM.toWSubM` (lifts a `WEquM Γ v t` to a `WSubM Γ v t`) at
`Pss/Mpss/DeBruijnWellFormed.lean` (search for `WEquM.toWSubM`).

**Status:** MECHANIZED.

---

### Proposition 17 (From reduction semantics to equivalence reduction, paper p. 9:33)

**Statement.** Let `u, v` be terms. If `u ↦ v` then `Γ; s ⊢ u →ᵉᵠᵘ v` for all
extended context `Γ; s`.

**Proof status (paper).** Full proof given (p. 9:33).

**Technique.** Induction on `u ↦ v` by last rule. Base: `Os-Bet` closes by
`Me-Bet` and reflexivity (Proposition 18). Inductive: `Os-Con` closes by
`Me-Fun`, `Me-FOp`, or `Me-App` depending on the surrounding evaluation
context.

**Lean.** `Pss.DeBruijn.MEqRed.of_StepAt` at
`Pss/Mpss/DeBruijnOperationalSem.lean:116`. The de Bruijn version is
**unconditional** — there is no axiom for the β case (the body sub-
derivation is built by `MEqRed.refl` under the indexed binder context,
without need for cofinite quantification).

**Status:** MECHANIZED. No axiom required (the LN version had
`Proposition_17_beta_axiom`, retired during the refactor).

---

### Proposition 18 (Reflexivity of equivalence reduction, paper p. 9:33)

**Statement.** Let `Γ; s` be an extended context, `u` a term. We have
`Γ; s ⊢ u →ˢᵘᵇ u` and `Γ; s ⊢ u →ᵉᵠᵘ u`.

**Proof status (paper).** Full proof given (p. 9:33). Straightforward
induction on `u`'s structure.

**Lean.** `Pss.DeBruijn.MEqRed.refl` (in `Pss/Mpss/DeBruijnReductions.lean`,
search by name) — equivalence reflexivity. `MSubRed.refl` (search likewise)
— subtype reflexivity. Both used pervasively.

**Status:** MECHANIZED.

---

### Lemma 19 (Weakening of context, paper p. 9:34)

**Statement.** Let `Γ; s` and `Γ'; s'` be two extended contexts such that
`Γ, Γ'; s @ s'` is prevalid. The following weakening relations hold:
- `Γ ⊢ u wf → Γ, Γ' ⊢ u wf`
- `Γ ⊢ u ≤_wf v → Γ, Γ' ⊢ u ≤_wf v`
- `Γ ⊢ u ≤∗_wf v → Γ, Γ' ⊢ u ≤∗_wf v`
- `Γ; s ⊢ u ≤ v → Γ, Γ'; s ⊢ u ≤ v`
- `Γ; s ⊢ u ≤∗ v → Γ, Γ'; s ⊢ u ≤∗ v`
- `Γ; s ⊢ u →ˢᵘᵇ v → Γ, Γ'; s ⊢ u →ˢᵘᵇ v`
- `Γ; s ⊢ u ↦ˢᵘᵇ v → Γ, Γ'; s ⊢ u ↦ˢᵘᵇ v`
- `Γ; s ⊢ u →ᵉᵠᵘ v → Γ, Γ'; s @ s' ⊢ u →ᵉᵠᵘ v`
- `Γ; s ⊢ u ↦ᵉᵠᵘ v → Γ, Γ'; s @ s' ⊢ u ↦ᵉᵠᵘ v`

**Proof status (paper).** Full proof given via three combined inductions
(p. 9:34–36): one for `wf / ≤_wf / ≤∗_wf`, one for `→ˢᵘᵇ`, one for `→ᵉᵠᵘ`.
The combined induction is forced by mutual reference between the three
relations (via `Wf-App`).

**Lean.** Splits across multiple definitions in `Pss/Mpss/DeBruijnReductions.lean`
and `Pss/Mpss/DeBruijnWellFormed.lean`:
- `MEqRedJ.weaken_head` at `Pss/Mpss/DeBruijnReductions.lean:1163`.
- `MSubRedJ.weaken_head` at line 1198.
- `MEqRedStar.weaken_head` at line 1241.
- `MSubRedStar.weaken_head` at line 1284.
- `MEqRedJ.insertAt` at line 1150 (general insertion).
- `MSubRedJ.insertAt` at line 1186.
- `MEqRedStar.insertAt` at line 1222.
- `MSubRedStar.insertAt` at line 1265.
- `WfM.insertAt` at `Pss/Mpss/DeBruijnWellFormed.lean:1882`.
- `WfM.weaken_head` at line 1993.
- `WSubM.insertAt` at line 1891. `WSubM.weaken_head` at 2095.
- `WSubMStar.weaken_head` at line 2104.
- `WEquM.weaken_head` at line 2114.

**Status:** MECHANIZED. The de Bruijn version uses index-shifting
machinery (`Term.shift`, `Stack.shift`, `Ctx.insertAt`) to express
weakening, which has a richer surface area than the paper's named-binder
formulation but the relationships are direct.

---

### Lemma 20 (Weakening of context — auxiliary, paper p. 9:34)

**Statement.** Three statements for the case of weakening with ordinary
(non-extended) contexts: `Γ ⊢ u wf → Γ, Γ' ⊢ u wf`, `Γ ⊢ u ≤_wf v → Γ, Γ' ⊢ u ≤_wf v`,
`Γ ⊢ u ≤∗_wf v → Γ, Γ' ⊢ u ≤∗_wf v`.

**Proof status (paper).** Full proof given (p. 9:35–36) via combined induction
on derivation tree (because the three relations cross-reference).

**Lean.** Subsumed by `WfM.insertAt`, `WSubM.insertAt`, `WSubMStar.insertAt`
listed above.

**Status:** MECHANIZED (subsumed by Lemma 19's mechanization).

---

### Lemma 21 (Weakening of context — subtyping reduction, paper p. 9:36)

**Statement.** Let `Γ; s` and `Γ'` be two contexts such that `Γ, Γ'; s` is
prevalid. If `Γ; s ⊢ u →ˢᵘᵇ v` then `Γ, Γ'; s ⊢ u →ˢᵘᵇ v`.

**Proof status (paper).** Full proof given (p. 9:36–37). Induction on the
derivation tree of `→ˢᵘᵇ` by last rule.

**Lean.** Subsumed by `MSubRedJ.weaken_head` /
`MSubRed.weaken_head` (search for it in
`Pss/Mpss/DeBruijnReductions.lean`).

**Status:** MECHANIZED (subsumed).

---

### Lemma 22 (Weakening of context — equivalence reduction, paper p. 9:37)

**Statement.** Let `Γ; s` and `Γ'; s'` be two extended contexts such that
`Γ, Γ'; s @ s'` is prevalid. If `Γ; s ⊢ u →ᵉᵠᵘ v` then `Γ, Γ'; s @ s' ⊢ u →ᵉᵠᵘ v`.

**Proof status (paper).** Full proof given (p. 9:37). Induction on the
derivation tree by last rule.

**Lean.** Subsumed by `MEqRedJ.weaken_head` (line 1163).

**Status:** MECHANIZED (subsumed).

---

### Lemma 23 (Narrowing of context in well-formedness, paper p. 9:37)

**Statement.** Let `Γ` and `Γ'` be two contexts; `t, t', u` be terms. If
`Γ, x ≤ t, Γ' ⊢ u wf`, `Γ; nil ⊢ t →ᵉᵠᵘ t'`, and `Γ ⊢ t' wf`, then
`Γ, x ≤ t', Γ' ⊢ u wf`.

**Proof status (paper).** Full proof given (p. 9:37–38). Induction on
`Γ, x ≤ t, Γ' ⊢ u wf` by last rule. `Wf-App` case has internal
sub-decomposition similar to Lemma 7.

**Lean.** This lemma is folded into the `WfMSubHeadReplaceOfNewWf` family at
`Pss/Mpss/DeBruijnTypeSafety.lean:11003` (a Type residual for
Theorem 5). Variants:
- `WfMSubHeadReplaceDirectPayloads`.
- `WfMSubHeadReplaceImmediateDirectPayloads`.
- `WfMSubUnderHeadReplaceOfNewWf`.

**Status:** MECHANIZED (residual). Shipped as `WfMSubHeadReplaceOfNewWf` to
`Theorem_5_DeBruijn_Preservation_proved`. Closure depends on its discharge.

---

### Lemma 24 (Narrowing of context in subtyping reductions, paper p. 9:38)

**Statement.** Let `Γ; s` be an extended context, `Γ'` an additional context.
If `Γ, x ≤ t, Γ'; nil ⊢ u →ˢᵘᵇ v`, `Γ; nil ⊢ t →ᵉᵠᵘ t'`, both `u, v` are
well-formed in `Γ, x ≤ t', Γ'`, and `Γ ⊢ t' wf`, then there exists `v'` such
that `Γ, x ≤ t', Γ'; nil ⊢ u →ˢᵘᵇ v'`, `Γ, x ≤ t', Γ'; nil ⊢ v →ᵉᵠᵘ v'`, and
`Γ, x ≤ t', Γ' ⊢ v' wf`.

**Proof status (paper).** Full proof given (p. 9:38–39). Case on whether the
derivation makes a promotion of `x` to `t`. If not, the substitution is
identity; else use weakening-to-Co context and Lemma 19.

**Lean.** No standalone `Lemma_24_*` symbol in the de Bruijn tree. The role
is played by `WfMSubHeadReplaceOfNewWf` and the broader `BetaInstantiationPreservesMSubRed`
family (`Pss/Mpss/DeBruijnTypeSafety.lean:226`+).

**Status:** MECHANIZED-DIFFERENTLY. Folded into the substitution preservation
pipeline rather than exposed as a single named theorem.

---

### Lemma 25 (Narrowing of context in equivalence reductions, paper p. 9:39)

**Statement.** Let `Γ; s` be an extended context, `Γ'` an additional context.
If `Γ, x ≤ t, Γ'; s ⊢ u →ᵉᵠᵘ v` and `Γ; nil ⊢ t →ᵉᵠᵘ t'`, then
`Γ, x ≤ t', Γ'; s ⊢ u →ᵉᵠᵘ v`.

**Proof status (paper).** Full proof given (p. 9:39). Induction on the
derivation by last rule. Each rule's premise transports because `→ᵉᵠᵘ` does
not promote a variable to its `≤` annotation.

**Lean.** Subsumed by the `BetaInstantiationPreserves*` family
(`Pss/Mpss/DeBruijnTypeSafety.lean:218`+) and the kind-narrowing helpers at
`Pss/Mpss/DeBruijnTypeSafety.lean:1909`+. The proved
`MEqRedFusedKindNarrowedBetaSubstStack_proved` covers cross-`.sub`/`.equ`
migration in the de Bruijn version.

**Status:** MECHANIZED-DIFFERENTLY. Folded into the kind-narrowing β-substitution
infrastructure.

---

### Lemma 26 (Narrowing prevalidity, paper p. 9:39)

**Statement.** Let `Γ, x ⊲ t, Γ'; s` be a prevalid context, and `t'` such
that `Γ; s ⊢ t →ᵉᵠᵘ t'`. Then `Γ, x ⊲ t', Γ'; s` is prevalid.

**Proof status (paper).** Full proof given (p. 9:39–40). Induction on the
derivation tree by last `Pv-*` rule.

**Lean.** Direct counterpart: `Prevalid.replaceAt` at
`Pss/Context/DeBruijn.lean:1657` and `Prevalid.sub_head_replace` at line
1703. Together these realize the "replace one annotation while preserving
prevalidity" operation.

**Status:** MECHANIZED.

---

### Proposition 27 (Reduction preserves subtyping derivation, paper p. 9:40)

**Statement.** Let `Γ; s` be an extended context. Let `u, u', v` be terms
such that `Γ ⊢ u ≤∗_wf v` and `u ↦ u'`, and `Γ ⊢ u' wf`. Then
`Γ ⊢ u' ≤∗_wf v`.

**Proof status (paper).** Full proof given (p. 9:40). Use Proposition 17 to
lift `u ↦ u'` to `Γ; nil ⊢ u →ᵉᵠᵘ u'`. Then `Ws-Rfl` and `Ws-Lf1` give
`Γ ⊢ u' ≤_wf u`. Compose by `Ws-Sub` and `Ws-Trs`.

**Lean.** Folded directly into the body of
`Theorem_5_DeBruijn_Preservation_of` at
`Pss/Mpss/DeBruijnTypeSafety.lean:16307`:
```
have hBack : WSubMStar Γ t' t := WSubMStar.of_StepAt_back hstep hwfT hwfT'
exact WSubMStar.trans hwfT hBack hwf
```

**Status:** MECHANIZED-DIFFERENTLY. No standalone `Proposition_27_*` symbol;
its argument is inlined into Theorem 5.

---

### Lemma 28 (Substitution preserves prevalidity, paper p. 9:40)

**Statement.** Let `Γ, x ⊲ t, Γ'; s` be an extended context. If
`Γ, x ⊲ t, Γ'; s` is prevalid then `Γ, Γ'[x\t]; s[x\t]` is prevalid. Also: if
`Γ, x ⊲ t, Γ'` is prevalid then `Γ, Γ'[x\t]` is prevalid.

**Proof status (paper).** Full proof given (p. 9:40–41). Induction on the
prevalidity derivation by last `Pv-*` rule.

**Lean.** Direct counterpart in `Pss.DeBruijn.Prevalid.instantiateBetaPrefix`
machinery at `Pss/Context/DeBruijn.lean:118` (the `Ctx.instantiateBetaPrefix`
operation) plus the `Prevalid` prevalidity transports
(search `Pss/Context/DeBruijn.lean` for `Prevalid.instantiate` family).

**Status:** MECHANIZED.

---

### Lemma 29 (Promotion under substitution outside of covariant contexts, paper p. 9:41)

**Statement.** Let `Γ; s` be an extended context, `Γ'` a logical context such
that `Γ, Γ'[x\α]; nil` is prevalid. Let `t, α` be terms. If
`Γ, x ≤ t, Γ'; nil ⊢ Co[x] →ˢᵘᵇ Co[t]` is a derivation for some covariant
context `Co`, then `Γ, x ≤ t, Γ'[x\α]; nil ⊢ Co_{[x\α]}[x] →ˢᵘᵇ Co_{[x\α]}[t]`.

**Proof status (paper).** Full proof given (p. 9:41–42). Induction on `u`'s
shape (the term filling the covariant context).

**Lean.** No standalone Lean symbol. Conjecture 8 partially absorbs this in
the de Bruijn formulation; the rest is folded into the substitution
preservation suite.

**Status:** MISSING (folded into substitution preservation pipeline).

---

### Lemma 30 (Promotion under substitution inside of covariant contexts, paper p. 9:42)

**Statement.** Let `Γ; s` be an extended context. Let `Γ'` be a logical
context, such that `Γ, Γ'[x\α]; s[x\α]` is prevalid. Let `u, v, t, α` be
terms; `x` a variable. If `Γ, x ≤ t, Γ'; s ⊢ u →ˢᵘᵇ v`, such that this
derivation is NOT of the form `Γ, x ≤ t, Γ'; s ⊢ Co[x] →ˢᵘᵇ Co[t]` for some
covariant context `Co`, then `Γ, Γ'[x\α]; s[x\α] ⊢ u[x\α] →ˢᵘᵇ v[x\α]`.

**Proof status (paper).** Full proof given (p. 9:42–43). Induction on the
`→ˢᵘᵇ` derivation by last rule.

**Lean.** Folded into the `BetaInstantiationPreservesMSubRed` family at
`Pss/Mpss/DeBruijnTypeSafety.lean:226`+ and the related
`MSubRedRespectsBetaInstantiate*` lemmas. The de Bruijn formulation does not
need the explicit "Co context" exclusion because index-based substitution
handles the promotion-of-`x` case structurally.

**Status:** MECHANIZED-DIFFERENTLY. Substitution preservation handles
both Lemma 29 and Lemma 30 cases inside one pipeline.

---

### Lemma 31 (Reduction under substitution, paper p. 9:43)

**Statement.** Let `Γ; s` be an extended context. Let `Γ'` be a logical
context such that `Γ, Γ'[x\α]; s[x\α]` is prevalid. Let `u, v, t, α` be
terms; `x` a variable. If `Γ, x ≤ t, Γ'; s ⊢ u →ᵉᵠᵘ v`, then
`Γ, Γ'[x\α]; s[x\α] ⊢ u[x\α] →ᵉᵠᵘ v[x\α]`.

**Proof status (paper).** Full proof given (p. 9:43–44). Induction on the
`→ᵉᵠᵘ` derivation by last rule. Each rule's transport. Key non-trivial cases:
`Me-Pro` uses prevalidity to know `α'[x\α] = α'`. `Me-Bet` invokes
**Barendregt's substitution lemma** (Reference [5]) to transport
`b[y\c'][x\α] = b[x\α][y\c'[x\α]]`.

**Lean.** Direct counterpart: `MEqRedRespectsBetaInstantiateStack_proved`
(proved, commit `a5aaf59`) at `Pss/Mpss/DeBruijnTypeSafety.lean:1904`. The
underlying type is `MEqRedRespectsBetaInstantiateStack` at line 1535. Plus
restricted partial discharges for under-heads variants.

**Status:** MECHANIZED. The proved version is unconditional.

---

### Lemma 32 (Reduction under substitution — auxiliary for the commutation theorem, paper p. 9:44)

**Statement.** Let `Γ; s` be an extended context. Let `u, u', v, v'` be terms;
`x` a variable. If `Γ, x ≡ v, Γ'; s ⊢ u →ᵉᵠᵘ u'` and `Γ; nil ⊢ v →ᵉᵠᵘ v'`, then
`Γ, Γ'[x\v]; s[x\v] ⊢ u[x\v] →ᵉᵠᵘ u'[x\v']`.

**Proof status (paper).** Full proof given (p. 9:44–45). Induction on the
`→ᵉᵠᵘ` derivation. Crucial in **Lemma 1** (the Me-App × Me-Bet case at p.
9:23 cites Lemma 32 explicitly).

**Lean.** Direct counterpart: `BetaInstantiationPreservesMEqRedStack_proved`
(proved, commit `7ec6954`) at `Pss/Mpss/DeBruijnTypeSafety.lean:1175`. The
de Bruijn version internalizes the asymmetry between `u`'s side (using `v`)
and `u'`'s side (using `v'`).

**Status:** MECHANIZED. Proved unconditional.

---

### Lemma 33 (Congruence of `≤`, paper p. 9:45)

**Statement.** Six congruence relations (all under prevalid extended ctx
`Γ; s`):
- If `Γ; v :: s ⊢ u ≤ u'` then `Γ; s ⊢ u v ≤ u' v`.
- If `Γ; v :: s ⊢ u ≤∗ u'` then `Γ; s ⊢ u v ≤∗ u' v`.
- If `Γ, x ≤ t; nil ⊢ u ≤ u'` then `Γ; nil ⊢ λx ≤ t.u ≤ λx ≤ t.u'`.
- If `Γ, x ≤ t; nil ⊢ u ≤∗ u'` then `Γ; nil ⊢ λx ≤ t.u ≤∗ λx ≤ t.u'`.
- If `Γ, x ≡ α; s ⊢ u ≤ u'` then `Γ; α :: s ⊢ λx ≤ t.u ≤ λx ≤ t.u'`.
- If `Γ, x ≡ α; s ⊢ u ≤∗ u'` then `Γ; α :: s ⊢ λx ≤ t.u ≤∗ λx ≤ t.u'`.

**Proof status (paper).** Proof given (p. 9:45) — the first case worked out;
the other five are stated as "similar".

**Lean.** Realized in the `MSub` and `MSubStar` weaken/transport theorems.
The single-step subtyping congruence is at
`Pss/Mpss/DeBruijnTransitivityElim.lean:103` (`MSub.weaken_head`); the
under-abstraction operations are at multiple `meqRedStar_abs_*` /
`msubRedStar_abs_*` helpers in the same file. Search for
`fun_body_fixed_bound`, `fOp_body_fixed_bound`.

**Status:** MECHANIZED-DIFFERENTLY (multiple per-shape helpers, no single
`Lemma_33_*` symbol).

---

### Lemma 34 (Congruence of `↦ˢᵘᵇ`, paper p. 9:45–46)

**Statement.** Three congruence relations for `↦ˢᵘᵇ` (the transitive closure
of `→ˢᵘᵇ`).

**Proof status (paper).** Full proof given (p. 9:46). Lift each `→ˢᵘᵇ` step
under `Ms-App`, `Ms-Fun`, or `Ms-FOp`.

**Lean.** Realized in the `MSubRedStar.app_*`, `MSubRedStar.fun_*`,
`MSubRedStar.fOp_*` family at `Pss/Mpss/DeBruijnReductions.lean:613`+.

**Status:** MECHANIZED-DIFFERENTLY.

---

### Lemma 35 (Congruence of `↦ᵉᵠᵘ`, paper p. 9:46)

**Statement.** Three congruence relations for `↦ᵉᵠᵘ` (the transitive closure
of `→ᵉᵠᵘ`).

**Proof status (paper).** Proof given (p. 9:46) — "similar to Lemma 34".

**Lean.** Realized in the `MEqRedStar.app_*`, `MEqRedStar.fun_*`,
`MEqRedStar.fOp_*` family at `Pss/Mpss/DeBruijnReductions.lean`.

**Status:** MECHANIZED-DIFFERENTLY.

---

### Lemma 36 (Commutativity — context weakening, paper p. 9:46)

**Statement.** Let `Γ; s` and `Γ'; s'` be extended contexts such that
`Γ; s ↣ Γ'; s'`. Then `Γ; nil ↣ Γ'; nil`.

**Proof status (paper).** Full proof given (p. 9:46). Induction on `s`. Base
`s = nil`: holds. Inductive `s = α :: s₀`: by Ct-Stk we have `Γ; s₀ ↣ Γ'; s₁`
with `s' = α' :: s₁`. Apply IH to get `Γ; nil ↣ Γ'; nil`.

**Lean.** No direct counterpart — the de Bruijn formulation doesn't carry
the explicit `↣` relation (see Section 2 above). The role this lemma plays
in the Lemma 1 / Lemma 2 grid (peeling stack annotations) is internalized
into the structural shape of `MEqRed.app` / `MSubRed.app` (which split off
the empty-stack operand premise) and the `Stack.shift` machinery.

**Status:** MISSING (subsumed by structural design — no explicit `↣` relation
to lemma about).

---

## Summary statistics

- **Total numbered items in the paper:** 8 theorems (Theorems 1, 3, 4, 5,
  11) — wait, actually 5 distinct theorems labelled (1, 3, 4, 5, 11) — plus
  1 conjecture (8), plus 24 numbered lemmas (2, 6, 7, 9, 10, 15, 16, 19, 20,
  21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 34, 35, 36) and 4
  propositions (12, 13, 14, 17, 18). So roughly **34 numbered items** with
  proof obligations.

- **Coverage in this index:** all 34 above. Paper Sections 2 and 4
  definitions (Term grammar, contexts, `Me-*` rules, `Ms-*` rules, `Wf-*`
  rules, `Ws-*` rules, `↦` operational rules, evaluation contexts, prevalidity)
  are mapped to Lean entries.

- **Closure status of the eight de Bruijn `_proved` headlines** (per
  `AXIOMS.md`):
  - `Lemma_1_DeBruijn_StrongCommutativityStar_proved` ← `UniformStrongCommutes`.
  - `Lemma_1_DeBruijn_StrongCommutativityChain_proved` ← `UniformStrongCommutes`.
  - `Lemma_2_DeBruijn_DiamondMEqRedStar_proved` ← `MEqRedArgTransportPayload`,
    `MEqRedOpStackHeadTransportPayload`, `MEqRedSubBridgePayload`,
    `UniformEqDiamonds`.
  - `Lemma_2_DeBruijn_DiamondMEqRedChain_proved` ← same as above.
  - `Theorem_3_DeBruijn_TransitivityIsAdmissible_proved` ← `UniformStrongCommutes`.
  - `Theorem_4_DeBruijn_Progress_proved` ← `UniformStrongCommutes`.
  - `Theorem_5_DeBruijn_Preservation_proved` ← `BetaInstantiationPreservesWfM`,
    `AbsFunctionBoundInversion`, `WfMSubHeadReplaceOfNewWf`.
  - `Theorem_5_DeBruijn_ClosedPreservation_proved` ← same as above.

- **Conjecture 8** (`WellSubtypingContextIndependent`) is the **single
  permanent paper-level open problem** — the paper does not prove it. The
  formalization mirrors this; it is not currently shipped as a Lean axiom in
  the de Bruijn tree (the LN-side declaration was retired in Phase B).

- **Notable architectural divergence:** the paper's explicit `↣` relation
  (reduction of extended context) and the cofinite-style "for all `Γ'; s'`
  with `Γ; s ↣ Γ'; s'`" generalizations in Lemmas 1 and 2 are vacuous in the
  de Bruijn tree because freshness is structural. Lemma 36, which exists
  solely to decompose `↣` for the Lemma 1 / Lemma 2 grids, is therefore not
  separately mechanized.

- **Notable loss of paper-faithfulness:** Theorem statements that mention
  binders no longer textually match Pasquale & García-Pérez 2024 (the
  paper's `λx ≤ t.u` becomes `Term.abs t body` with `bvar 0`). The
  meta-mathematical content is the same, but the statements differ
  cosmetically.

---

## Where to look for things not in this index

- **Build verification & axiom audits:** `Pss/Sanity.lean` (de Bruijn
  endpoints with `#print axioms` checks), `AXIOMS.md` (full taxonomy with
  discharge status, partial-discharge commits, restricted variants).

- **Per-cell case grid for Lemma 1 (StrongCommutes):**
  `Pss/Mpss/DeBruijnTransitivityElim.lean` namespace `StrongCommutes` from
  line 706, plus the cross-β cells in
  `Pss/Mpss/DeBruijnTypeSafety.lean` from line 36000+.

- **Per-cell case grid for Lemma 2 (EqDiamonds):**
  `Pss/Mpss/DeBruijnTransitivityElim.lean` namespace `EqDiamonds` from
  line 241, plus universal/uniform witnesses in
  `Pss/Mpss/DeBruijnTypeSafety.lean`.

- **Substitution / β-instantiation infrastructure (Lemmas 7, 28, 30, 31, 32
  combined):** `Pss/Mpss/DeBruijnTypeSafety.lean` from line 193 onwards
  (`BetaInstantiationPreservesWfM` family, `MEqRedRespectsBetaInstantiate*`,
  `MEqRedFusedKindNarrowedBetaSubst*`).

- **Operational ⇒ MPSS lift (Proposition 17):**
  `Pss/Mpss/DeBruijnOperationalSem.lean` (the entire file).
