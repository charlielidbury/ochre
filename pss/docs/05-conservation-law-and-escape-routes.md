# D2: The Budget Conservation Law, and the Escape Routes That Survive It

> **Status of this document.** Analysis, not proof. It extends `04-depth-transport-problem.md` (which remains the statement of record for Problem D2) with: (i) a *negative meta-result* — the **budget conservation law** — showing that an entire class of model repairs, including every attack in 04-§8 and roughly ten further variants worked end-to-end here, fails by exactly one index level, always, and why; (ii) the two proof programs that are structurally exempt from the law (**graded Howe's method** and **context truncation**), each worked far enough to name its single pivot risk; (iii) a catalogue of newly-explored dead variants with one-line failure points, so they are not re-attempted; (iv) the prior-art map (DOT's bad bounds, Compagnoni–Goguen, Howe/environmental bisimulation) locating D2 in the literature. Nothing here changes the Lean development; the single open `sorry` remains `Pss/Semantic/RulesApp.lean: sound_app_le`.

---

## 0. Where we stand, in one paragraph

The graded-extension model proves every rule of the instrumented system except DS-APP(≤) (Problem D2). The failure is always the same event: a value's pair/tier data is needed at depth `k`, but every supply route decays by the type side's evaluation length or by one level per tier descent, capping at `k−1`. D1 (member conversion) was the same event with less structure and is **false** for raw terms (the lockstep countermodel), so no raw invariant can break the wall; D2's hope rests on the well-formedness of the bounds. The question 04 left open is *how* wf could possibly be cashed out. This document's answer: **not by any re-budgeting of the model** (§2 proves this informally but robustly), and plausibly by either of two known proof technologies whose induction orders are different in kind (§3, §4).

## 1. Sharpening D2: the telescope works; the motive doesn't

Two observations that reframe the problem.

**1a. Single-layer D2 telescopes.** Fix one DS-APP node. Its semantic premises at `(k, γ)` supply pair data for `(T, T′)` at grade `k`-ish; one tier descent at the (maximally good) argument `U` yields contractum-pair data at grade `k−1`; the goal's member-side demands, unfolded through (m3), consume generation-`g` pair data only at grades `≤ k−g`. Supply and demand *both* decay by one per generation. A standalone, semantically-stated, one-application-layer transport lemma has no internal deficit. (This is why every failed proof "almost" works.)

**1b. The deficit is a compositionality deficit of the FT motive, not of the transport.** The off-by-one appears exactly when the *output* of a DS-APP case must be re-consumed: by an outer DS-APP (nested applications `t(u)(w)`), or inside a λ-body whose tier discharge re-enters the judgement at the tier's (capped) goodness level. The motive must be uniform in grade to be a motive; the consumption sites need one more grade than uniformity can supply. That tension — not the transport itself — is D2.

This reframing is what makes §2 provable and §3 plausible.

## 2. The budget conservation law

**Claim.** In any model of this family — stratified by a single index, term-generic (one definition for all terms), with the type side `=β`-free — and any FT motive whose judgement, context-goodness, and tier data are related by *uniform* grade arithmetic, the rule set pins the grades exactly, and DS-APP comes up short by one level. No assignment of lags, reserves, degrees, or tier conventions closes it.

**The ledger.** Write `g_J(k)` for the grade of pair data the judgement asserts at `(k, γ ∈ ⟦Γ⟧ₖ)`; `g_G(j)` for the grade stored in goodness at level `j`; and consider a tier of pair data at carrier grade `m`, domain `c ∈ G_j`, conclusion grade `g_T(j, m)`. The rules impose:

1. **(DS-EVAR)** `g_J(k) ≤ g_G(k)` — the variable case reads the judgement off goodness, nothing else.
2. **(Stratification)** Recursive carriers force `g_T(j, m) < m` strictly: a tier's conclusion must be defined before its carrier. (Coinductive carriers can have `g_T = m`; see pin 5.)
3. **(DS-FUN/W-FUN discharge)** A tier obligation at domain `G_j` is discharged by the body judgement at context `γ[x↦c]`, which is good at `j` only: `g_T(j, m) ≤ g_J(j)`. Moreover the body is an *arbitrary term*: if its own application-nesting depth is `d_b`, iterating this pin costs `d_b` grades, and `d_b` is unbounded over the (semantic) domain of the tier.
4. **(DS-APP harvest)** The conclusion's pair data at grade `g_J(k)` must be harvested from the premise's pair data (grade `g_J(k)`) through one tier descent at `c := U`, whose goodness the premises cap at `≤ k`. By pin 2 the harvest yields `< g_J(k)`. Deficit: one level, independent of all the dials.
5. **(Coinductive escape closes the wrong door)** Making the carrier a per-grade gfp lets the top tier conclude *at* grade `m` (pin 2 evaded), and DS-APP then closes — but pin 3 becomes undischargeable: the full-grade tier obligation for a merely `j`-good `c` demands body data at grade `m` from a judgement capped at `g_J(j) < m`. The deficit moves from DS-APP to DS-FUN; it does not vanish.

**Worked corollaries** (each variant was walked through every FT case; the pin that kills it is listed):

| Variant | Killed by |
|---|---|
| 04-§8 attacks 1–6 (index-raising, bounded conversion, MATCH composition, ∀-good substitutions, ∀-good tiers, closed-judgement restriction) | pins 4, 3, 4, 3, stratification, 3 respectively — all instances of the law |
| Judgement lag (`INC_{k−λ}`), goodness lag, any relabeling `λ, τ, γ_g` | the ledger is invariant under uniform relabeling; deficit conserved |
| Recursive pair-relation `INC_k` in judgement+goodness, tiers `∀j≤k, c∈G_j ⊢ INC_{j−1} ∧ plain@j` ("Model II") | every case closes except DS-APP: harvest gives `INC_{k−2}` vs demand `INC_{k−1}` (pin 4). The cleanest uniform design; still loses by exactly one |
| Per-grade gfp `INC_k` with full-budget tier over `G_k` | DS-APP ✓, DS-FUN ✗ (pin 5) |
| Index-free coinductive `INC_∞` in goodness | goodness ↔ MATCH-domain ↔ `⟦·⟧` circularity: not stratifiable; and with plain domains instead, DS-EVAR or W-FUN dies (the judgement-content/goodness/tier-domain chain must agree) |
| Derivation-degree motives (`∃d₀ ∀d≥d₀: INC_{k−d}`) | DS-APP arithmetic closes (!), but DS-FUN's tier obligation must hold for *all* bodies over a *semantic* domain, and a body's nesting `d_b` exceeds any uniform tier convention (pin 3, unbounded form). `∃e`-graded tier domains then break stratification (unbounded `G_{j+e}` lookahead) or break the harvest (the harvester needs small `e`, the discharger large `e`) |
| Type-side step budgeting (`MATCH_{k−j−j_T}`, max-discipline, etc.) | `⟦Iᴺ(T)⟧ₖ ≠ ⟦T⟧ₖ` below `N`: Lemma 4.4 and DS-EQ die under β-expansion of the type. Bound invariance and the ≡-fragment make the type side's `=β`-freeness non-negotiable |
| Pure depth-indexing (member steps cost nothing) | member conversion becomes provable (!) but W-APP's diagonal accounting dies: the self-MATCH of the application's value needs depth `k`, the function's tier supplies `< k`, and there is no member step to pay the descent. Step-budgeting the member side is *forced* by W-APP |
| Syntactic tier domains (`c` with `∅ ⊢ c ≤wf a` derivable) | stratification ✓, harvest ✓, but the variable/binder interface circularizes: DS-EVAR needs semantic facts for `γx` from a derivation of unrelated size — the term-model circularity that semantic goodness exists to break |
| CBV-style value substitutions (`γx` values, tiers over value args) | `[x↦U]B` vs `[x↦w_U]B` differ by member-side conversion — refuted (D1). Full β is not CBV |
| Payload-carrying value probes (manufacture a member of `⟦T⟧ₖ` whose tiers encode `B`'s behavior) | any probe with non-vacuous tier content must *pre-pay* its own self-MATCH at full depth — the wall itself. Only vacuous-tier probes (Ω-bodies, `Top`) are free; that is §7 of 04, already exhausted |
| Ω as least argument (`⟦[Ω]b⟧ ⊆ ⟦[c]b⟧`, harvest tiers at the bottom element) | false: `b := λy≤x.Top` — bound positions are *invariant*, so instantiation is not monotone in the argument. Bound invariance giveth (no contravariance) and taketh away (no order-theoretic magic) |
| Retreat to the paper's syntactic §5 skeleton with semantic inversion at ∅ | doubly blocked: Cor 9.3 (inversion) consumes the FT, hence D2 — circular; and the syntactic skeleton independently needs `SubShiftWeakening` (the unstated assumption in the paper's Lemma 5.4 — see PROGRESS 2026-06-10), which Conjecture 5.1 does not supply |

**Moral.** The wall is not bookkeeping. The model conflates a *payload* (self-membership / (m1)-safety — genuinely inductive, must be earned per term) with a *simulation shell* (shape, bound, tier-pair data — freely reflexive, freely transitive, freely evaluation-invariant; the recursive-`INC` reflexivity proof makes this precise). Uniform grading forces the shell to ride the payload's budget, so shell data decays with computation; DS-APP needs shell data that doesn't decay. Within the uniform-grading family these are contradictory requirements. **Stop re-budgeting; change the induction.**

## 3. Escape A (primary): graded Howe's method

D2 is, in classical terms, a *congruence* property of a simulation-like relation: application congruence for an applicative similarity whose argument domain is conditioned by the bound. Congruence-of-similarity has one standard proof technology — Howe's method — whose key lemma inducts on **the member's evaluation length, then term structure**, with a substitutive *precongruence candidate* closure. Two features make it structurally exempt from §2's law:

- **Tier discharge is by closure substitutivity, not judgement instantiation.** In the key lemma's λ-case, the bodies are related in the Howe closure `R^H` *as open terms*; a tier argument `c` (merely `j`-good) enters by `c R^H c` (reflexivity of a compatible closure — free, uncapped) plus substitutivity of `R^H`. Pin 3 never fires: no body judgement at a capped `γ[x↦c]` is consulted.
- **Pair data propagates through the closure's syntax tree and the evaluation induction, never through a value's warranty.** Pin 4's harvest (tier-of-a-judgement-carrier) is replaced by the substitution lemma in the β-case. The grades that remain are consumed monotonically downward (`k₁ := k−1` at each β-unfolding), with `k` a universal of the key lemma rather than a property of `γ`.

λ⊲-specific luck: the classical obstruction to Howe for *typed/bounded* similarity is contravariant bounds. λ⊲'s bounds are **invariant** (`α =β a`), so the closure's λ-rule can compare bounds by raw `=β` (substitutive, by Church–Rosser — all already in `BetaTheory`), and tier domains transport across `=β` by Lemma 4.4. The classical killer is absent.

**Concrete shape (drop-in; nothing existing changes).** Prove `sound_app_le` as a standalone theorem about *semantic* premises (this would also answer 04-§10 Question 3 positively):

1. **Base relation.** `⊴ := SemLe`-instances (the six premise judgements and their consequences), used only through: inclusions (unbudgeted in evaluation length), probe-derived shape/bound/convergence facts (§7 kit, proven), and goodness of real arguments (≤ `k`).
2. **Closure.** `R^H` on open terms: compatible closure (one constructor layer, `R^H` children; λ-case compares bounds by `=β`) composed on the right with `⊴` ("semi-transitivity" `R^H; ⊴ ⊆ R^H` built in). Prove: reflexive, substitutive (`c R^H c′` and `b R^H b′` give `[c]b R^H [c′]b′`), contains `⊴`.
3. **Graded key lemma.** If `X R^H Y` (closed), `X ⇓ʲ v`, `j < k`, then `Y`'s value exists with matching shape/bound and tier data at grade `k−j` — by induction on `j`, then `X`'s structure, with `k` universally quantified in the IH. β-case: factor `X = X₁(X₂)`, IH on `X₁` (strictly fewer steps), substitution lemma, IH on the contractum (strictly fewer steps), compose with the base via semi-transitivity.
4. **Read-back.** Key lemma ⟹ `⟦X⟧ₖ ⊆ ⟦Y⟧ₖ` for `R^H`-pairs, all `k` ≤ ambient — by strong induction on `k` with MATCH-transport (the same composition as 04-§6's DS-FUN case, now with undecayed tier supply).
5. `sound_app_le` = instance: `T(U) R^H T′(U′)` by compatibility from the premises.

**The pivot risk, named.** In the key lemma's λ-case (j = 0, X a value), the composition with the base pair `Z ⊴ Y` needs something about *`Z`'s value against `Y`'s value*. If the proof can route all such needs through (i) inclusions (no decay), (ii) probes (no decay), and (iii) the IH/closure (decays only with member steps), it closes. If it irreducibly needs tier content of `Z`'s value above `Z`'s own evaluation warranty, the wall has re-entered through the base and the method fails *for the same reason as everything else*. This is the single question a focused 1–2 day attempt should answer before any mechanization: **write the λ-case of the graded key lemma in full, on paper, tracking every consumption of the base.** Everything else in the program is standard.

Acceptance tests the finished theorem must pass: the D1 countermodel must *not* become derivable for raw terms (check: `R^H` built over `SemLe` bases never relates `λy≤c.y(⊤)` to `λy≤c.⊤` at starved `c`, because the *premise kit* for those is unsatisfiable — the lockstep refutation lives below the instrumented hypotheses, not below the closure); and `sound_app_le`'s statement must remain exactly the one in `RulesApp.lean`.

## 4. Escape B (secondary): context truncation / Top-completion

04-§8's obstruction notes already observe: "an evaluation cannot distinguish a capped tower from its Top-completion without itself sticking", and D2 at `Γ = ∅` is **proven** (the ∀-index mode is legitimate there). The reduction this suggests:

> **Truncation lemma (wanted).** Every `γ ∈ ⟦Γ⟧ₖ` admits `γ* ∈ ⋂ⱼ⟦Γ⟧ⱼ` (∀-good) with `⟦γt⟧ᵢ = ⟦γ*t⟧ᵢ` for all `i ≤ f(k)` and all terms `t` — k-observational equivalence stable under substitution into arbitrary terms.

Given it, D2-open transports to the ∀-good instantiation (where the ∅-style proof applies) and back. Both directions of the equivalence are required (bound positions are invariant, so `x` occurs at both polarities) — so naive Top-completion (one-sided: makes things *bigger*) is insufficient; the completion must agree *exactly* to depth `k`.

**The pivot risk, named: definability.** The needed `γ*x` is a term realizing "γx's behavior to observation depth k, clean above" — a *behavioral* truncation, and depth is computational, not syntactic. Two sub-questions, either of which could kill or save the program: (i) is every depth-`k` behavior of a `k`-good term realized by some term that is ∀-good (a definability/fullness property of the model)? (ii) if not in general, is it true for the specific γ-images the FT ever constructs (which are built from tier arguments and judgement images — a much tamer class)? A wildcard worth recording: untyped λ admits fuel-bounded self-interpreters, so "run `γx` under a depth-`k` fuel counter, default to Top-shaped junk past the fuel" is not obviously inexpressible in λ⊲ — but threading bound-annotations through such an interpreter is heavy machinery for one lemma.

Verdict: conceptually the *direct* formalization of 04's wf-relative desideratum, and the only program that would yield a reusable structural theorem about the model (the derivable fragment is `ω`-converged); but the definability question makes it higher-variance than Escape A. Attempt second, or run a cheap falsification first: look for a `k`-good `γx` whose depth-`k` behavior provably has *no* ∀-good realizer (a cardinality/diagonalization argument inside the model would refute the general form (i) and refocus on (ii)).

## 5. Prior art, located precisely

- **DOT's "bad bounds" ≙ D1's starvation bound.** In DOT (Amin–Rompf–Odersky; Rapoport et al.), a type member with absurd bounds makes subtyping locally degenerate; safety is recovered not by repairing subtyping but by consuming dangerous eliminations only under **inert** typing contexts — contexts whose entries provably cannot introduce bad bounds. D1's `c := λy≤K⊤.y(⊤)(⊤)` is exactly a bad bound (spine-typed body on good arguments), and 04's observation that the countermodel's bound is not semantically wf is exactly DOT's inertness boundary. This is independent evidence that **D2 is true** and that wf-of-bounds is the right hypothesis — but note DOT never proves a semantic FT for open judgements; its safety is a syntactic preservation proof over machine states (closed configurations). The analogous retreat here is blocked (see ledger: `SubShiftWeakening` + inversion circularity), which is *why* we need Escape A or B rather than DOT's own move.
- **Compagnoni–Goguen** (typed operational semantics for F^ω_≤, cited in the paper's §8 as the only successful relative): their technique requires strong normalization, which λ⊲ lacks by design (Girard's paradox, Thm 4.4). Does not transfer; the graded model's divergence-friendliness must be kept.
- **Howe (1996), Lassen, Pitts; Sangiorgi–Kobayashi–Sumii.** Congruence of applicative (bi)similarity by precongruence candidates; environmental bisimulation for when the relation's argument domain is self-referential. Escape A is Howe over a *predefined* graded goodness (so the classical negativity issue — the tier domain mentioning the relation — does not even arise at the closure level: `⟨a⟩ⱼ` is already built). The graded twist (threading `k−j` through the key lemma) appears to be novel; if it works it is a publishable lemma independent of PSS.
- **Step-indexed transitivity folklore.** The inclusions-in-the-model design (03/04) is the standard cure for step-indexed transitivity failure; D2 shows the cure relocates the disease to congruence. Worth stating publicly if either escape lands.

## 6. Recommendation

1. **Do not attempt anything in the §2 table.** The ledger is checked; one-level deficits are conserved under all uniform re-gradings. (If someone believes they have a budget fix, have them locate which pin their design violates *first*.)
2. **Attack Escape A's pivot directly** (hardest-first): the λ-case of the graded key lemma, on paper, base-consumption-tracked. 1–2 focused days. If it survives, the rest of §3's program is mechanizable with current infrastructure (`Model.lean`'s goodness, `BetaTheory`'s substitutive `=β`, the §7 observer kit) and `sound_app_le` closes without touching any existing file.
3. If A's pivot fails, the failure analysis will say exactly what base data was missing — feed that into **Escape B**: either as the truncation lemma's target ("the missing data is realizable at a completed γ") or as the seed of a D2 countermodel (04-§10 Question 5) — at which point the model repair is the type-side-budget family, which §2 shows requires abandoning `=β`-free types, i.e., a redesign of the ≡-fragment, not a patch.
4. Either way, record the §2 law and the §5 DOT correspondence in any writeup of this work; the negative result is publishable context for the positive one.

— Analysis session 2026-06-10, branch `pss-2`. The Lean development is untouched by this document; statements referenced: `Pss/Semantic/RulesApp.lean:sound_app_le` (the open D2), `Pss/Semantic/ConversionCounterexample.lean` (D1's refutation), `Pss/Semantic/RulesApp.lean:primed_head` and the probe kit (§7 of 04).
