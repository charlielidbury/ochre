# STOP — Paper bug in Pasquale & García-Pérez 2024 Lemma 32

**Status:** Paper bug confirmed. Lean-checked obstruction in
`Pss/Paper/Investigation/Lemma_32_Asymmetric.lean`.

**Cost to formalization:** Forces the codebase into the symmetric
kind-narrowed approximation
(`MEqRedFusedKindNarrowedBetaSubstStack_proved`) plus chain-shaped
composition at the bet × bet call sites of Lemmas 1 and 2. Prior
campaign work (~70k lines of factoring) was driven by attempts to
match paper-faithfulness against this asymmetric form.

## TL;DR

The paper's Lemma 32 (p. 9:44–45) states:

> Let `Γ; s` be an extended context. Let `u, u', v, v'` be terms;
> `x` a variable. If `Γ, x ≡ v, Γ'; s ⊢ u →ᵉᵠᵘ u'` and
> `Γ; nil ⊢ v →ᵉᵠᵘ v'`, then `Γ, Γ'[x\v]; s[x\v] ⊢ u[x\v] →ᵉᵠᵘ u'[x\v']`.

The induction on the source derivation **walls at the `Me-Var × x = y`
case** (i.e., when the source step is reflexivity on the substituted
variable). The paper's proof closes this case by reflexivity of `→ᵉᵠᵘ`
on `v`, producing `v →ᵉᵠᵘ v` — but the lemma's stated conclusion
requires `v →ᵉᵠᵘ v'` over the post-substitution stack `s[x\v]`. The
paper's text contains a typographical error that renames `v[x\v']` to
`v[x\v]` in the case analysis, hiding the gap.

## The Lean witness

In `Pss/Paper/Investigation/Lemma_32_Asymmetric.lean`:

* `Lemma_32_Asymmetric_Goal` — the asymmetric statement.
* `MEqRedStackExtensionWall` — the precise obligation that the proof
  attempt cannot discharge from the lemma's hypotheses alone.
* `Lemma_32_Asymmetric_via_wall` — a constructive proof that,
  **given an oracle for the wall**, the asymmetric Lemma 32 holds. The
  body walks every case of the induction; every case except
  `Me-Var × substituted slot` closes directly. That single case
  applies the wall hypothesis. Builds with no `sorry`, no new axioms,
  kernel three only (`propext`, `Classical.choice`, `Quot.sound`).
* `Lemma_32_Asymmetric_via_wall_closed` — the same, specialised to
  empty preserved-prefix (the natural paper surface).

The wall's statement (paraphrased): given `MEqRed Γ [] arg arg'`,
arbitrary substitution prefix `heads`, arbitrary stack `s` over which
the substituted context is prevalid, derive
`MEqRed (heads[arg] ++ Γ) (s[arg]) (shifted arg) (shifted arg')`.

## Why the wall is real (counterexample sketch)

If `arg = .abs Top body` and `arg' = .abs Top body'`, the empty-stack
step `MEqRed Γ [] arg arg'` is via **Me-Fun**, which requires the body
sub-derivation to live under `.sub Top`-headed context. To extend to a
non-empty target stack `[β]`, the Lean encoding requires **Me-FOp**,
whose body sub-derivation lives under `.equ β`-headed context (taking
the stack head as the binder annotation). The two body sub-derivation
contexts are **structurally incompatible** — there is no general way
to convert a `Me-Fun` body derivation into a `Me-FOp` body derivation
without re-deriving the body in the new context, which has no
canonical lift in general. (Concrete obstruction: if the body uses
`bvar 0` to lookup the head, the `.sub Top`-headed context produces a
subtype-side promotion target, while the `.equ β`-headed context
produces an equivalence-side promotion target — mathematically
distinct.)

## What's wrong with the paper

The paper's Me-Var case (p. 9:44, second-to-last paragraph of the
Lemma 32 proof) reads:

> **Rule Me-Var:** In this case, we have `u = y` and `v = y` with
> `Γ, x ≡ v, Γ'` prevalid. If `y = x`, then `u[x\v] = v` and
> `v[x\v] = v`. We need to show `Γ, Γ'[x\v]; s[x\v] ⊢ v →ᵉᵠᵘ v`,
> which holds by reflexivity (Proposition 18).

The error: per the lemma's asymmetric statement, the second equation
should be `u'[x\v'] = v'` (recall `u' = y = x`, so `u'[x\v'] = v'`),
**not** `v[x\v] = v`. The proof obligation is `v →ᵉᵠᵘ v'` over
`s[x\v]`, not `v →ᵉᵠᵘ v`. Closing by reflexivity gives the symmetric
form, not the asymmetric form the lemma claims.

The same typographical collapse appears in the **Me-Pro with `u = y ≠
x`** case (line `α'[x\v] →ᵉᵠᵘ α''[x\v]` should be `α''[x\v']`), the
**Me-App** case (similar), the **Me-Fun** / **Me-FOp** / **Me-Bet**
cases. These secondary cases are all internally consistent (the IH
applies asymmetrically, and the constructor reassembly threads
arg/arg' correctly — verified by transcribing every case in Lean).
Only the Me-Var case is **structurally** broken.

## Suggested authors' email

> Subject: Lemma 32 (Reduction under substitution) — proof obligation
> in Me-Var case
>
> Dear Vincenzo, Adrián,
>
> We have been mechanising your MPSS metatheory in Lean 4 and have run
> into an issue with Lemma 32 (Reduction under substitution —
> auxiliary for the commutation theorem, p. 9:44–45). We believe the
> proof of the **Me-Var** case (top of p. 9:44, in the case `y = x`)
> contains an error that hides a structural gap.
>
> The lemma states (asymmetric):
>
> > If `Γ, x ≡ v, Γ'; s ⊢ u →ᵉᵠᵘ u'` and `Γ; nil ⊢ v →ᵉᵠᵘ v'`, then
> > `Γ, Γ'[x\v]; s[x\v] ⊢ u[x\v] →ᵉᵠᵘ u'[x\v']`.
>
> In the **Me-Var** case with `u = u' = y = x`, the proof obligation
> after substitution is:
>
> > `Γ, Γ'[x\v]; s[x\v] ⊢ v →ᵉᵠᵘ v'`
>
> over the **substituted stack** `s[x\v]` (which can be non-empty if
> the original derivation had `s` non-empty). The paper closes this
> case by reflexivity of `→ᵉᵠᵘ`, producing `v →ᵉᵠᵘ v` — but the
> required conclusion is `v →ᵉᵠᵘ v'` (the asymmetric form), and the
> hypothesis `Γ; nil ⊢ v →ᵉᵠᵘ v'` is over the **empty** stack, not
> `s[x\v]`.
>
> If `v` is an abstraction `λy ≤ a.b`, the empty-stack step
> `Γ; nil ⊢ v →ᵉᵠᵘ v'` is necessarily via Rule **Me-Fun** (the unique
> applicable rule for abstractions over empty stack), which puts the
> body derivation under `Γ, y ≤ a; nil`. To derive
> `Γ; β :: s'' ⊢ v →ᵉᵠᵘ v'` for a non-empty stack, we need Rule
> **Me-FOp**, whose body derivation lives under `Γ, y ≡ β; s''` — a
> different context kind (`≡` vs `≤`) and a non-empty stack. The two
> body sub-derivations are not interderivable in general.
>
> We have a Lean-checked artifact at
> `Pss/Paper/Investigation/Lemma_32_Asymmetric.lean` that reduces the
> full Lemma 32 to a stack-extension hypothesis on `→ᵉᵠᵘ` and
> demonstrates that the wall-point is exactly Me-Var × `y = x`. Every
> other case (Me-Pro, Me-App, Me-Top, Me-TAp, Me-Fun, Me-FOp, Me-Bet)
> closes by direct case analysis with no extra hypotheses.
>
> We suspect the textual statement of Me-Var has a typo — the line
> `v[x\v] = v` after `u[x\v] = v` should perhaps be `v[x\v'] = v'`
> (matching the asymmetric statement's `u'[x\v']`), in which case
> reflexivity does NOT close the case; some other argument is needed.
>
> Could you confirm whether (i) the lemma is intended in the
> asymmetric form (as stated), and the Me-Var case requires an
> additional argument we're missing; or (ii) the lemma is actually
> intended in a symmetric form (LHS and RHS both substitute `[x\v]`),
> in which case the conclusion's `[x\v']` is a typo? In case (ii),
> Lemma 1's invocation of Lemma 32 (p. 9:23, Me-App × Me-Bet cell)
> would also need re-examining since it appears to need the
> asymmetric form.
>
> Thank you for the wonderful paper — closing Hutchins' transitivity
> gap is a substantial achievement and we have learnt a lot from
> mechanising it.
>
> Best,
> Charlie Lidbury

## Recommendation for the formalization

* **Do NOT attempt to close `MEqRedStackExtensionWall`.** It is
  mathematically equivalent to a stack-extension property on `MEqRed`
  that is *false* for abstraction-shaped terms.
* **Continue using `MEqRedFusedKindNarrowedBetaSubstStack_proved`**
  (the symmetric kind-narrowed surface) for downstream consumers. The
  bet × bet diamond cell composes this symmetric form with separate
  body and operand diamond closures to produce the chain
  `MEqRedStar`-target needed by Lemma 2.
* **Update `Pss/Paper/Aux/Substitution.lean`** to reference this
  finding: the asymmetric form is `paper-bug-blocked`, not
  `mechanization-divergence-blocked`. The current docstring frames
  the issue as a Lean-encoding limitation; it is actually a paper-
  level gap.
* **Open a follow-up dispatch** to investigate whether a
  *restricted* asymmetric Lemma 32 — restricted to non-abstraction
  `v` — would suffice for the bet × bet diamond consumer. If yes, we
  could ship a paper-faithful asymmetric form for atomic `v` and the
  symmetric kind-narrowed form for general `v`.
