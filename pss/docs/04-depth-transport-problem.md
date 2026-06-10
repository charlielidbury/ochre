# Type Safety for System λ⊲ via Graded Extensions: The Proof, and the Depth-Transport Problem

> **Status of this document.** Self-contained apart from references to Hutchins, *Pure Subtype Systems* (POPL 2010); it supersedes `03-revised-proof.md`, whose §6 DS-APP case contains a quantifier-budget error and whose Lemma 4.5 (member conversion) is **false outright** — both found during verification of that document, and analyzed here. Everything stated below as *proven* or *refuted* has a complete proof or countermodel, reproduced or sketched in place; the document's purpose is to present the one remaining obstruction — **the depth-transport problem**, §8 — precisely enough to be attacked, branched on, or refuted. §10 lists the concrete questions.

---

## 0. The approach, and the scoreboard

Hutchins' type-safety argument for λ⊲ (his §5) rests on Conjecture 5.1 (transitivity elimination), through two consequences: inversion of λ-subtyping (his Lemma 5.2) and the underivability of `Top ≤ function`. The present development proves safety *semantically* instead: every closed term is interpreted as a graded set of closed terms ("its subtypes, to observation depth `k`"), every instrumented declarative rule is proved sound for the model, and safety is read off the model. The design goals, all achieved:

- **DS-TRANS costs nothing** — subtyping is membership *plus set inclusion of graded extensions*, and inclusions compose set-theoretically at a fixed index (§5). Conjecture 5.1 is never invoked.
- **No normalization is assumed** — divergent terms are vacuously related, mandatory since λ⊲ admits Girard's paradox (Hutchins' Theorem 4.4).
- The only imported rewriting facts are **Church–Rosser** and a **standardization corollary** for *plain unconditional β* (§2) — not the contested algorithmic relations of Hutchins' §6.

Scoreboard:

| Item | Status |
|---|---|
| Church–Rosser, shape/whnf standardization, convergence transfer (§2) | **Proven** |
| The model: well-founded graded definition, unfolding, antitonicity, step-shift, type-evaluation invariance, **type-conversion invariance (4.4)** (§3–4) | **Proven** |
| Member conversion (Lemma 4.5 of the predecessor document) | **Refuted** — false on closed terms (§4.4); consumed by *nothing* downstream |
| DS-TRANS is set-theoretic (Theorem 5.1) | **Proven** |
| ≡-fragment collapses to `=β` (Lemma 6.1) | **Proven** |
| Fundamental theorem, every rule case except DS-APP(≤) — including **W-APP in full** (§6) | **Proven** |
| The observer kit: probes, primed-head forcing, the bound chain (§7) | **Proven** |
| Soundness of DS-APP(≤) | **Open** — Problem D2 (§8); conjectured true *for the reshaped reasons below* |
| Safety (7.1), progress (7.2), inversion (7.3), `Top ≰ λ` (7.4) (§9) | **Proven modulo D2** (their proofs are complete and consume the fundamental theorem only) |

Both items above arise from a single phenomenon: the model budgets the *member's* computation and λ-depth but never the *type's*, and certain proofs need a value's self-description (its MATCH data) at depths the diagonal budget cannot reach. We call this the **depth-transport problem**. Its first instance (member conversion) is now **resolved negatively** — the needed transport is simply false for raw terms, by an explicit countermodel whose engine is a quantitative *lockstep* lemma (§4.4). Its second instance (DS-APP) remains open, and the countermodel **does not transfer**: it requires a bound that is not semantically well-formed, and DS-APP's instrumentation carries well-formedness of all four bounds. The depth-transport problem is thereby sharpened from "find an index-raising invariant" to: *show that well-formed bounds cannot starve the budget the way raw bounds can* (§8).

## 1. The systems under discussion

**Syntax, reduction, values** are those of Hutchins' Figure 1: terms `s,t,u ::= x | Top | λx≤t.u | t(u)`; values `v,w ::= Top | λx≤t.u`; full reduction `⟶` is `(λx≤t.u)(s) ⟶ [x↦s]u` closed under all contexts (including under binders and inside bounds); `=β` is the generated conversion. We write `↦` for **weak-head reduction**: the unique redex contracted is the head one (`(λx≤a.b)(c) ↦ [x↦c]b`; `t ↦ t′ ⟹ t(u) ↦ t′(u)`). `↦` is deterministic. `t ⇓ʲ w` means `t ↦ʲ w` with `w` `↦`-normal; `t ⇓ w` means `∃j`; `t⇑` means no such `w`.

**Fact 1.1 (closed weak-head normal forms).** A closed `↦`-normal term is `Top`, a λ-abstraction, or a **spine** `Top(d₁)…(dₙ)`, `n ≥ 1`. A closed `⟶`-normal non-value is a spine with `⟶`-normal arguments. *(Induction on the term.)* "Going wrong" for closed programs means exactly: reaching, under `⟶*`, a normal spine.

**The instrumented judgements.** Well-formedness `Γ ⊢ t wf` is Figure 1's. The **instrumented subtyping** `Γ ⊢ t ≤wf u` is Figure 1's declarative subtyping under the paper's §3.4 reading — *"any derivation of `t ≤wf u` only compares well-formed subterms"* — made explicit: every rule carries wf premises for the terms it mentions. Two instrumentation choices deserve emphasis, because the fundamental theorem's induction consumes premises rule-locally:

- **DS-APP carries its endpoints' W-APP instrumentations *unpacked***: the rule relating `t(u) ⊲ t′(u′)` carries, with explicit bounds `s, s′`, the four judgements `t ≤wf λx≤s.Top`, `u ≤wf s`, `t′ ≤wf λx≤s′.Top`, `u′ ≤wf s′` (rather than opaque premises `t(u) wf`, `t′(u′) wf`). An induction over derivations obtains the semantic content of premises only; the DS-APP case needs the semantic content of the W-APP *sub-derivations*, which an opaque wf premise would not deliver.
- **DS-EAPP relates a well-formed redex to a well-formed contractum**; if the contractum's wf is not derivable, the rule instance is unavailable.

Targets: `∅ ⊢ t wf ⟹ t` never goes wrong; inversion; `Top` is not a function.

## 2. Facts about raw reduction

All for **plain, unconditional β** — a left-linear orthogonal system; Tait–Martin-Löf/Takahashi apply.

**Lemma 2.1 (Church–Rosser).** `⟶` is confluent; hence `t =β u` iff `t, u` have a common reduct, and `=β` is substitutive (`t =β t′, s =β s′ ⟹ [x↦s]t =β [x↦s′]t′`). *(Parallel reduction with the Takahashi complete development `t*`; the triangle property `t ⇒ u ⟹ u ⇒ t*` gives the diamond. The naive diamond induction is unworkable: in the critical pair `β` vs. congruence-through-a-λ, a single parallel step cannot contract a redex that appears only after contraction.)*

**Lemma 2.2 (whnf standardization).** If `t ⟶* u` with `u` weak-head normal, then `t ⇓ u′` for some `u′` with `u′ ⟶* u`. In particular (shape standardization): if `t ⟶* λx≤p.q` then `t ⇓ λx≤p′.q′` with `p′ ⟶* p`, `q′ ⟶* q`; if `t ⟶* Top` then `t ⇓ Top`; if `t ⟶* Top(d₁)…(dₙ)` then `t ⇓ Top(e₁)…(eₙ)` with `eᵢ ⟶* dᵢ`.

*Proof route.* Not by bookkeeping over single parallel steps — the head lemma "if `t ⇒ u` and `u ⇓` then `t ⇓` compatibly" resists induction, because in the β-case the recursive call is on a substituted parallel derivation at the *same* evaluation length, which is not smaller in any structural or fuel order. Instead, by an inductively defined **standard reduction** relation `St` (Kashima-style): `St t u` is a weak-head prefix `t ↦* ·` followed by standard reductions of the target's top-level components. Every lemma about `St` is then a plain structural induction: `St` absorbs a trailing parallel step (`t St p ⇒ n ⟹ t St n`; the β-case inverts two prefixes, appends one head step, and closes by substitutivity of `St` on genuine subderivations), hence `⟶* ⊆ St`, and Lemma 2.2 is inversion of `St` at the rigid target. ∎

The full whnf form of 2.2 (arbitrary rigid targets, not just the three closed-value shapes) is needed below; note also that **rigid heads stay rigid**: a reduct of a weak-head normal term is weak-head normal of the same head shape.

**Corollary 2.3 (convergence transfer).** If `t =β v` with `v` a value, then `t ⇓ v′` where `v′` is a value of the same constructor whose components are `=β` the components of `v`.

*Proof.* 2.1 gives a common reduct `d` of `t` and `v`; `d` is a value of `v`'s constructor (reducts of values keep their constructor) with `=β` components. By 2.2, `t ⇓ u′` with `u′ ⟶* d`. It remains to see `u′` is a *value* — this does **not** follow from `u′ =β v` alone (that would be circular: value-ness of weak-head normal forms is often exactly what is being established); it follows because `u′` is weak-head normal and `u′ ⟶* d` with `d` a value, and a weak-head-normal *non*-value (a spine or variable-headed term) has a rigid head, so all its reducts share that head and never become values. ∎

## 3. The model: graded extensions with inclusions

Every term `T` is interpreted as a set `⟦T⟧ₖ` of terms — "the terms below `T`, to observation depth `k`". Typing is the diagonal: `t` is semantically well-formed iff `t ∈ ⟦t⟧ₖ` for all `k`. The index is consumed by **the member's weak-head steps** and by **descent into λ-bodies**; the type side is never budgeted; divergence costs nothing.

**Definition 3.1.** By strong induction on the index (at stage `n ≥ 1`, `MATCHₙ` is defined from `{⟦·⟧ⱼ}_{j<n}`, and `⟦·⟧ₙ` from `{MATCHₘ}_{m≤n}`; `⟦·⟧₀` is everything):

For `s, T`:
> `s ∈ ⟦T⟧ₖ` iff for all `j < k`: if `s ⇓ʲ v` then
> (m1) `v` is a value, and
> (m2) `T ⇓ w` for some value `w`, and
> (m3) `MATCH_{k−j}(v, w)`.

For values `v, w`:
> `MATCHₘ(v, w)` holds iff:
> - `w = Top`: always;
> - `w = λx≤a.b`: `v = λx≤α.β` for some `α =β a`, and for all `j < m` and all `c ∈ ⟨a⟩ⱼ`:
>   - (t1) `[x↦c]β ∈ ⟦[x↦c]b⟧ⱼ`, **and**
>   - (t2) `⟦[x↦c]β⟧ⱼ ⊆ ⟦[x↦c]b⟧ⱼ`;

with the **good arguments** of a bound at depth `j`:
> `⟨a⟩ⱼ ≜ { c : c ∈ ⟦a⟧ⱼ, c ∈ ⟦c⟧ⱼ, and ⟦c⟧ᵢ ⊆ ⟦a⟧ᵢ for all i ≤ j }.`

*Well-foundedness.* `MATCHₘ` references `⟦·⟧` only at indices `< m`, and `⟦·⟧ₖ` references `MATCHₘ` only for `m ≤ k`, whose references stay `< k`. The inclusions occur negatively; that is fatal for an inductive definition and irrelevant for a recursive one.

Remarks. (i) `⟦T⟧ₖ`, `k ≥ 1`, contains every divergent term; if `T` diverges or sticks, nothing else. (ii) `Top ∉ ⟦λx≤a.b⟧ₖ` for `k ≥ 1` — (m3) demands a λ on the member side; this single line is the semantic "Top is not a function". (iii) Bounds are compared by raw conversion `α =β a` — the paper's bound *invariance* (§3.3) means the model needs only an equivalence between bounds. (iv) The inclusions (t2) and the goodness inclusions exist to make DS-TRANS set-theoretic (§5): inclusions at index `j` are consumed at index `j`; no escalation exists. (v) Goodness is downward-closed **by fiat** (the `i ≤ j` quantifier): memberships are antitone automatically, inclusions are not.

> **(vi) No upward closure — the budget discipline.** Goodness strengthens strictly with the index: `c ∈ ⟨a⟩ₖ` says nothing about `c ∈ ⟨a⟩_{k′}` for `k′ > k`, and no upward closure exists (a term may converge only after `k` steps, making all its depth-`≤k` obligations vacuous and its depth-`k′` obligations false). Consequently, for the ∀-quantified judgements of Definition 3.2, the **only legitimate instantiations** inside a proof that has fixed `(k, γ)` with `γ ∈ ⟦Γ⟧ₖ` are: at any index `≤ k` with the *same* `γ` (Lemma 4.1), or at an arbitrary index with a *different* substitution good at that index. The predecessor document's fundamental-theorem preamble asserted a third mode — "at ∀-index via the ∀ in Definition 3.2" with the same `γ` — which is **unsound**; both of its erroneous proofs (§4.4, §8) used exactly this mode.

**Definition 3.2 (semantic judgements).** For `Γ = x₁≤t₁,…,xₙ≤tₙ` and substitution `γ`:
- `γ ∈ ⟦Γ⟧ₖ` iff `γxᵢ ∈ ⟨γtᵢ⟩ₖ` for each `i`.
- `Γ ⊨ t ≤ u` iff `∀k ∀γ ∈ ⟦Γ⟧ₖ`: `γt ∈ ⟦γu⟧ₖ` **and** `⟦γt⟧ₖ ⊆ ⟦γu⟧ₖ`.
- `Γ ⊨ t wf` iff `Γ ⊨ t ≤ t` (the content is self-membership).
- `Γ ⊨ t ≡ u` iff `t =β u` and `Γ ⊨ t wf` and `Γ ⊨ u wf`.

**Lemma 3.3 (membership from inclusion).** If `Γ ⊨ t wf` and `∀k ∀γ ∈ ⟦Γ⟧ₖ: ⟦γt⟧ₖ ⊆ ⟦γu⟧ₖ`, then `Γ ⊨ t ≤ u`. *(γt ∈ ⟦γt⟧ₖ ⊆ ⟦γu⟧ₖ.)* Since every instrumented `≤`-rule carries wf of its left endpoint, per-rule obligations in §6 reduce to inclusion halves.

## 4. Structural lemmas

**Lemma 4.1 (antitonicity).** `j ≤ k ⟹ ⟦T⟧ₖ ⊆ ⟦T⟧ⱼ`; `MATCHₘ` antitone in `m`; `⟨a⟩ₖ ⊆ ⟨a⟩ⱼ`; `⟦Γ⟧ₖ ⊆ ⟦Γ⟧ⱼ`. *(MATCH directly — the tier quantifier's domain shrinks; memberships from MATCH-antitonicity; goodness from both plus the by-fiat closure. No induction is needed anywhere.)*

**Lemma 4.2 (step shift).** If `s ↦ s₁` then: `s₁ ∈ ⟦T⟧ₖ ⟹ s ∈ ⟦T⟧ₖ₊₁`, and `s ∈ ⟦T⟧ₖ₊₁ ⟹ s₁ ∈ ⟦T⟧ₖ`. *(Determinism of `↦`; the arithmetic `(k+1)−(j+1) = k−j`.)*

**Lemma 4.3 (type evaluation invariance).** If `T ↦ T′` then `⟦T⟧ₖ = ⟦T′⟧ₖ`. *(The clause inspects only `T`'s weak-head value.)* Iterates along any `T ↦* T′`.

**Lemma 4.4 (type conversion invariance).** `T =β T′ ⟹ ⟦T⟧ₖ = ⟦T′⟧ₖ`, and `a =β a′ ⟹ ⟨a⟩ⱼ = ⟨a′⟩ⱼ`.

*Proof.* One strong induction on the index proves both claims jointly; within the induction step the set claim at the current index `k` must be established *before* the goodness claim at `k`, because goodness at `j` consumes the set claim at indices `≤ j` (not `< j`): its membership components transport directly, its inclusion components ride the set *equalities*. For the set claim: let `s ∈ ⟦T⟧ₖ`, `s ⇓ʲ v`, `j < k`. Then `T ⇓ w` (value) and `MATCH_{k−j}(v,w)`. By Corollary 2.3 on `T′ =β T ⇓ w`: `T′ ⇓ w′`, same constructor, `=β` components. Transport `MATCH_{k−j}` across the componentwise conversion: `w = Top` trivial; `w = λ`: the bound clause composes by transitivity of `=β`; tier domains coincide by the goodness claim at `j′ < k−j ≤ k` (IH); (t1) transports by the IH set claim at `j′` along substitutivity of `=β` (Lemma 2.1); **(t2) rides the IH's set equality** — `⟦[c]b⟧ⱼ′ = ⟦[c]b″⟧ⱼ′` as sets, composed on the relevant side. All indices consumed are `≤ k`; the budget discipline of remark (vi) is respected throughout. ∎

### 4.4. Member conversion is open

The predecessor document's Lemma 4.5 asserted: *if `s =β s′` and `s′ ∈ ⟦T⟧ₖ` for **all** `k`, then `s ∈ ⟦T⟧ₖ` for all `k`* — the member-side counterpart of 4.4, with the ∀-index hypothesis motivated by the member side being budgeted (conversion changes step counts; the converted member's evaluation length `i′` is unrelated to the goal index).

**Its proof is broken**, at tier (t1) of the MATCH transport. The proof runs: `s ⇓ʲ v` with `j < k`; by 2.3 `s′ ⇓^{i′} v′` componentwise-convertible to `v`; instantiating the hypothesis at `i′+1+n` for every `n` gives `MATCHₙ(v′, w)` at every `n`; transport `MATCH_{k−j}` to `v`. In the λ-case, tier `j′ < k−j`, `c ∈ ⟨a⟩ⱼ′`: the proof claims "(t1) `[c]β′ ∈ ⟦[c]b⟧` *at every index* (from MATCH at every index), so the index-induction IH applies along `[c]β =β [c]β′`". The parenthetical is false: extracting `[c]β′ ∈ ⟦[c]b⟧ᵢ` from `MATCH_{i+1}(v′, w)` requires `c ∈ ⟨a⟩ᵢ` *at that `i`* — and the tier supplies goodness at `j′` only, downward-closed by remark (v), never upward (remark (vi)). The supply is capped at `i ≤ j′` while the induction demands every index.

The cap cannot be dodged by weakening the statement to match the supply. **The bounded variant is false:**

> *(Counterexample.)* `(∀ k′ ≤ k, s′ ∈ ⟦T⟧_{k′}) ⟹ s ∈ ⟦T⟧ₖ` fails at `s := Top`, `s′ := I¹⁰⁰(Top)` (a 100-step delay of `Top`, where `I := λx≤Top.x`), `T := λx≤Top.Top`, `k := 5`: every bounded membership of `s′` is vacuous (`s′` converges only after 100 steps), yet `Top ∈ ⟦λx≤Top.Top⟧₅` fails at (m3) — the member side must be a λ.

> *(Stronger counterexample — adding the inclusion halves does not help.)* `(∀ i ≤ j, s′ ∈ ⟦T⟧ᵢ) ∧ (∀ i ≤ j, ⟦s′⟧ᵢ ⊆ ⟦T⟧ᵢ) ∧ s =β s′ ⟹ s ∈ ⟦T⟧ⱼ` fails at `s := Top(Top)` (a stuck spine), `s′ := Iʲ(s)`, `T := s′`: the bounded memberships are vacuous, the inclusions are reflexive, and the goal fails at (m1).

So any true version of member conversion would have to use the *context* in which the transport is demanded — the goodness of `c` and the ∀-index MATCH of the source value — essentially. Everything in the broken proof *except* tier (t1) is sound; the lemma reduces to **Tier-Transport**: *if `q =β β′`, `MATCH_{n+1}(λx≤α′.β′, λx≤a.b)` for every `n`, and `c ∈ ⟨a⟩_{j₁}`, then `[x↦c]q ∈ ⟦[x↦c]b⟧_{j₁}`* — with no residual index induction ((t1) was the proof's only recursive step; the bound clause and (t2) transport unconditionally).

**Theorem 4.5⁻ (member conversion is FALSE).** Tier-Transport — and with it member conversion in full — is refuted, on closed terms. Writing `⊤ := Top`, `I := λx≤⊤.x`, `K⊤ := λx≤⊤.⊤`, take
> `c := λy≤K⊤. y(⊤)(⊤)`,  `s := λy≤c. y(⊤)`,  `s′ := λy≤c. I(I(y(⊤)))`,  `T := λy≤c. ⊤`,  `k := 4`.

Then `s =β s′` and `s′ ∈ ⟦T⟧ₖ` at *every* `k`, yet `s ∉ ⟦T⟧₄`. Two ingredients:

1. *A bound whose body is spine-typed on good arguments.* `c` is a value, but instantiating its body at good arguments produces types that evaluate toward stuck spines built on `⊤(⊤)` — and (m2) bans **any** convergence of a stuck type's members. This caps `c`'s good-argument space exactly: `c ∈ ⟨c⟩₂`, and *nothing* is good at greater depth. The ∀-index MATCH hypothesis on `s′` is thereby starved: its tiers quantify over good arguments that do not exist at the depths where they would have to bite.
2. *The lockstep lemma* — the quantitative "cap anatomy" that §8's analyses called for, landing on the **falsity** side. `⊤`-instantiation *reflects* weak-head steps: `M[⊤]` and `M[K⊤]` run in lockstep, and a non-value weak-head normal form of a `⊤`-instance resolves under `K⊤` within **one** extra step. Consequently no good argument can fire a non-value tier obligation for the padded body `I(I(y(⊤)))` — its obligations sit one step *outside* the goodness cap — while the unpadded body's stuck path `c(⊤) ⇓¹ ⊤(⊤)(⊤)` sits one step *inside* it. The padding shifts the two paths in opposite directions across the cap.

So the model **genuinely distinguishes `=β`-equal members**: type-side conversion is a set equality at every fixed index (Lemma 4.4), while member-side conversion fails even with the hypothesis supplied at every index. This asymmetry is a structural fact about graded extensions with unbudgeted type sides, not a defect of one proof. Two saving graces: **nothing downstream consumes member conversion** (its single intended use, §6 DS-APP step (d), is derivable without it — §7), and **the countermodel does not transfer to DS-APP** — `c` is not semantically well-formed (its self-application body sticks on good arguments), while DS-APP's instrumentation carries well-formedness of all four bounds (§8).

## 5. Transitivity is set-theoretic

**Theorem 5.1 (DS-TRANS is free).** If `Γ ⊨ s ≤ t` and `Γ ⊨ t ≤ u` then `Γ ⊨ s ≤ u`.

*Proof.* Fix `k`, `γ ∈ ⟦Γ⟧ₖ`. Membership: `γs ∈ ⟦γt⟧ₖ ⊆ ⟦γu⟧ₖ`. Inclusion: `⟦γs⟧ₖ ⊆ ⟦γt⟧ₖ ⊆ ⟦γu⟧ₖ`. ∎

Composition happens at a single fixed index; the middle term is never evaluated. The original promise of the approach — transitivity without elimination — survives everything below: **the open problem of §8 is located in the application congruence, not in transitivity.**

## 6. The fundamental theorem

**Lemma 6.1 (the ≡-fragment is conversion).** If `Γ ⊢ t ≡wf u` then `t =β u`. *(No rule produces `≡` from `≤`; every ≡-rule is valid for `=β`.)*

**Theorem 6.2 (fundamental theorem — modulo Problem D2).** For the instrumented system:
1. `Γ ⊢ t wf ⟹ Γ ⊨ t wf`;
2. `Γ ⊢ t ≤wf u ⟹ Γ ⊨ t ≤ u`;
3. `Γ ⊢ t ≡wf u ⟹ Γ ⊨ t ≡ u`.

*Proof.* Mutual induction on derivations. Fix `k` and `γ ∈ ⟦Γ⟧ₖ` per case; per remark (vi), premise judgements are instantiated at indices `≤ k` with the same `γ`, or at other indices only with substitutions good there. Membership halves reduce to inclusion halves by Lemma 3.3. Every case is proven, except the ≤-form of DS-APP:

**(W-VAR, W-TOP, DS-TOP, DS-ETOP, DS-EVAR, DS-EQ, DS-SYM, DS-EAPP, DS-TRANS)** As in the predecessor document; all stay within budget. DS-EVAR reads both halves directly off the goodness of `γx` — this is *why* goodness stores inclusions. DS-EQ composes 4.4's set equality (under substitutivity of `=β`) with 3.3. DS-TRANS is Theorem 5.1.

**(W-FUN)** Goal `Λ ∈ ⟦Λ⟧ₖ`, `Λ ≜ λx≤γa.γb`. `Λ ⇓⁰ Λ`; (m3) at `m = k`: bound reflexive; tier `j < k`, `c ∈ ⟨γa⟩ⱼ`: then `γ[x↦c] ∈ ⟦Γ, x≤a⟧ⱼ` (ambient entries by 4.1 — `j < k`; the new entry is *literally* the tier's domain condition), so IH(1) of the body at `(j, γ[x↦c])` gives (t1); (t2) is reflexivity. *All instantiations diagonal.* ∎

**(DS-FUN, ≤-form)** Inclusion half, elementwise: `s ∈ ⟦Λ⟧ₖ`, `s ⇓ʲ v`, `j < k` gives `MATCH_{k−j}(v, Λ)`; build `MATCH_{k−j}(v, Λ′)`: bound clause composes the member's bound conversion with `γt =β γt′` (Lemma 6.1 on the ≡-premise, substitutive); tier `j′ < k−j`, `c ∈ ⟨γt′⟩ⱼ′ = ⟨γt⟩ⱼ′` (4.4): the member's own tier gives (t1),(t2) against `[c]γu`; the body IH at `(j′, γ[x↦c])` gives the inclusion `⟦[c]γu⟧ⱼ′ ⊆ ⟦[c]γu′⟧ⱼ′`; compose both at the fixed index `j′`. *No escalation.* ∎

**(W-APP)** Premises (via W-SUB): `Γ ⊨ t ≤ λx≤s.Top`, `Γ ⊨ u ≤ s`, `Γ ⊨ t wf`, `Γ ⊨ u wf`. Write `T, U, S` for the γ-images. Goal: `T(U) ∈ ⟦T(U)⟧ₖ`. Let `T(U) ⇓ʲ v`, `j < k`. Head evaluation factors: `T ⇓^{j₁} w_T` with `j₁ ≤ j`.
- *Shape (the progress-critical step):* the first premise's membership at index `j₁+1 ≤ k` gives `T ∈ ⟦λx≤S.Top⟧_{j₁+1}`, whose (m3) forces `w_T = λx≤A.B`, `A =β S` — were `w_T` `Top`, the member side of MATCH would fail.
- So `T(U) ↦^{j₁+1} [x↦U]B ⇓^{j₂} v`, `j = j₁+1+j₂`.
- *`U` is good at every depth `< k−j₁−1`:* memberships and self-memberships from the second premise and `u`'s wf at those indices (`≤ k` ✓); the **inclusion** components from the second premise's inclusion halves at each `i` (`≤ k` ✓); transport across `A =β S` by 4.4.
- *Self-description of the contractum:* `t`'s wf at index `j₁+1+m` for `m := k−j₁−1` — that is, **at exactly the ambient `k`** — gives `MATCH_{k−j₁}(w_T, w_T)`; its tier at `j′ = k−j₁−1` with argument `U` gives `[x↦U]B ∈ ⟦[x↦U]B⟧_{k−j₁−1}`.
- *Conclude:* `j₂ < k−j₁−1` (from `j < k`), so (m1) holds; the type side evaluates to `v` itself; `MATCH_{(k−j₁−1)−j₂} = MATCH_{k−j}` ✓. ∎

> **Why W-APP fits the budget — the diagonal identity.** The member here *is* the type: `j = j₁ + 1 + j₂` ties the member's steps to the head's steps, and the `j₁+1` consumed steps pay exactly for the tier descent to depth `k−j₁−1`. Every "at every index" in this case is realized at indices `≤ k`. This identity is precisely what DS-APP lacks (§8).

**(DS-APP, ≡-form)** `=β` by congruence from the premises (6.1); wf of both applications by the W-APP case applied to the carried instrumentations. ∎

**(DS-APP, ≤-form)** **Open** — Problem D2, §8. The paper-trail: the predecessor document's argument for this case instantiated the premise judgements "at every index" with the fixed `γ` at its steps (a′), (b), (d), (e), (g) — the unsound mode of remark (vi). Steps (a′), (c), (d) have since been *recovered* by budget-free arguments (§7); steps (b)/(e)/(g)'s deep content is the open residual. ∎ *(modulo D2)*

## 7. The observer kit

The following proven lemmas recover most of the DS-APP case, and close every shape, bound, and convergence channel of the problem. They exploit the model's partiality-friendliness: divergence is a *resource*.

**Lemma 7.1 (divergence is universal).** Let `Ω := (λx≤Top.x(x))(λx≤Top.x(x))`, which weak-head loops. Every divergent term inhabits `⟦X⟧ₖ` for every `X, k` (all clauses vacuous). Consequently `λx≤A.Ω` is a value all of whose MATCH tiers are vacuous.

**Lemma 7.2 (probes).** For every `A`: `λx≤A.Ω ∈ ⟦X⟧ₖ` *at every* `k` **iff** `X ⇓ Top` or `X ⇓ λx≤a.b` with `a =β A`. Likewise `Top ∈ ⟦X⟧ₖ` at every `k` iff `X ⇓ Top`. *(Membership inspects only the probe's value — a λ with vacuous tiers, or `Top` — against `X`'s weak-head value: only the shape and bound clauses bite.)* The probes are **definable observers**: they detect a type's weak-head shape and bound class through any *inclusion* `⟦X⟧ₖ ⊆ ⟦Y⟧ₖ`, since inclusions fire at member steps (the probe's: zero) and never at type steps.

**Lemma 7.3 (primed-head forcing and the bound chain).** Under the DS-APP premises (the two endpoint judgements and the four carried instrumentations), if `T ⇓ λx≤A.B` at *any* evaluation length — in or out of budget — then `T′ ⇓ λx≤A′.B′` for some `A′, B′` with the full chain
> `S =β A =β A′ =β S′.`

*Proof.* `λx≤A.Ω ∈ ⟦T⟧₁` by `T`'s own convergence (a type-side, unbudgeted fact). Push it through the inclusion halves of `t ≤ λx≤s.Top`, `t ≤ t′`, `t′ ≤ λx≤s′.Top` at index 1: the probe lands in `⟦λx≤S.Top⟧₁` (giving `A =β S`), in `⟦T′⟧₁` (giving: `T′ ⇓ Top` or `T′ ⇓ λ`-with-bound-`=β A`), and in `⟦λx≤S′.Top⟧₁`. The case `T′ ⇓ Top` is refuted by the `Top`-probe transported into `⟦λx≤S′.Top⟧₁` — a shape clash. The remaining case yields `A′ =β A` and `A′ =β S′`. *No budget condition on either evaluation length appears anywhere.* ∎

**Lemma 7.4 (the argument is good at the primed bound, in budget).** `U ∈ ⟨A′⟩ᵢ` for every `i ≤ k`: membership from `u`'s wf composed with the second premise's inclusion half into `⟦S⟧ᵢ`, then 4.4 along the chain of 7.3. *(This derivation replaces the predecessor document's appeal to member conversion — Lemma 4.5 is redundant for DS-APP.)*

**Lemma 7.5 (the primed contractum converges, head-length-free).** Whenever `j₁ ≤ k−2`, the probe of `[x↦U]B`'s weak-head shape sits in `⟦[x↦U]B⟧₁` by the contractum's own type-side convergence, and the function-pair tier (t2) at depth 1 transports it: `[x↦U′]B′` converges either to `Top`'s shape (in which case the goal MATCH below is trivial) or to a λ with linked bound. The *contractum's* evaluation length never enters — tier inclusions ride 4.3/4.4 on the type side; only the head length `j₁` is consumed.

What the probes cannot do: supply the **tier content** of a MATCH at depths the budget does not reach — tiers of a λ-value are exactly what a divergent-body probe is vacuous about. That residue is the open problem.

## 8. The depth-transport problem

**The phenomenon.** The model budgets member steps and λ-depth; the type side is free. A value `w` arising as the weak-head normal form of a term `t` with `t ∈ ⟦t⟧ₖ` carries self-description `MATCH_{k−j₁}(w, w)` where `j₁` is `t`'s evaluation length — *the deeper the computation, the shallower the warranty*. Proofs that relate **fast members to slow types** need a value's MATCH data at depths above its warranty: they must *transport tier content past the budget*. Two independent proofs in this development die at exactly this point, and at no other.

**Instance D1 (Tier-Transport) — RESOLVED: FALSE.** §4.4's Theorem 4.5⁻: for raw terms, tier content genuinely cannot be transported past the budget — the lockstep lemma exhibits a bound whose goodness cap starves the supply while the goal demands one step more. The cap-anatomy question is thereby *answered* for raw bounds, negatively. What keeps D2 alive is that the refuting bound is not well-formed; the open problem is now **wf-relative**.

**Problem D2 (soundness of DS-APP(≤)) — OPEN.** Under the premises `Γ ⊨ t ≤ t′`, `Γ ⊨ u ≡ u′`, and the four carried instrumentations — which include `Γ ⊨ s wf`, `Γ ⊨ λx≤s.Top wf`, `Γ ⊨ s′ wf`, `Γ ⊨ λx≤s′.Top wf` for the bounds: `Γ ⊨ t(u) ≤ t′(u′)` — specifically the inclusion half `⟦T(U)⟧ₖ ⊆ ⟦T′(U′)⟧ₖ` at each `(k, γ)`.

**D2's irreducible core.** Elementwise: `σ ∈ ⟦T(U)⟧ₖ`, `σ ⇓ʲ v`, `j < k`; the goal is `MATCH_{k−j}(v, w″)` against the value of `T′(U′)`. Shape, bound, and convergence of `w″` are forced (§7). The tiers remain: they require the value-pair body inclusions `⟦[c]b_{app}⟧_{j″} ⊆ ⟦[c]b″⟧_{j″}` up to `j″ = k−j−1`, where `b_{app}` is the body of `⟦T(U)⟧`'s value. Every hypothesis-derivable pair fact caps at depth `(k−j₁−1) − j₂′` (the first premise at the ambient `k` yields `MATCH_{k−j₁}` for the function pair; one tier descent and the contracta's evaluations consume the rest). The shortfall is
> `(j₁ + 1 + j₂′) − j > 0` whenever the member out-runs its type —
and `j` is *independent* of `j₁+1+j₂′`: a value σ already in normal form (`j = 0`) demands full-depth tiers of a type that may compute for arbitrarily long. The natural descent does not terminate: transporting the application's own value across the pair tiers requires `MATCH_m(w_{app}, w_{app})` at `m` above `k − (its source's evaluation length)` — the **self-MATCH wall** — and this recurs at every level. D1 was the same wall with less surrounding structure — and D1 is *false*: so no wall-breaking invariant exists at the level of raw model hypotheses. Any proof of D2 must consume the well-formedness of the bounds (or some other hypothesis the D1 countermodel violates) **essentially**.

**Failed attacks (each with its precise failure).**
1. *Index-raising along 4.2.* Stepping the member backwards raises its index, but the needed fact is the *pair's* MATCH at depth above the warranty; for `j₁ = 0` there are no steps to raise along at all.
2. *Bounded member-conversion.* False — two counterexamples in §4.4. Boundary datum: any solution must use the goodness/MATCH context essentially; index bookkeeping alone is refuted.
3. *MATCH composition.* MATCH does compose at a fixed index (bound clauses by transitivity; (t1)∘(t2), (t2)∘(t2)) — but composition is index-*preserving*; the problem is index-*raising*.
4. *∀-good substitutions in Definition 3.2* (quantify judgements over `γ` good at every index). DS-APP's case then transcribes verbatim — but W-FUN breaks symmetrically: its tier supplies `c` good at the tier depth only, which cannot extend an ∀-good `γ`. The gap moves; it does not close.
5. *∀-good tiers in MATCH.* Making tier domains ∀-good breaks Definition 3.1's stratification: tiers would reference memberships at unbounded indices, and the recursion ceases to be well-founded.
6. *Restricting the fundamental theorem to closed judgements.* Safety (§9) consumes only `Γ = ∅`, where the identity substitution is good at *every* index and the ∀-index mode is legitimate — but the induction passes under binders: W-FUN's tier descent re-enters nonempty contexts. A closed-judgement variant needs a strengthened W-FUN motive; its shape is unclear.

**Why D2's truth is conjectured — the countermodel constraint system.** D1's refutation supplies a *recipe* for falsification — a self-capping bound starving the tier supply — and D2's hypotheses supply a *proven blocker*: the instrumentation carries `Γ ⊨ s wf` for all four bounds, and the recipe's bound is essentially ill-formed (its body is spine-typed on good arguments, which is exactly what well-formedness excludes). Beyond this, extensive search for a D2-falsifying configuration fails in a *patterned* way; the obstructions are themselves informative:
- *Closed pairs die at ∀-good substitutions:* for closed `t, t′` the hypotheses can be instantiated at every index (constant-`Top` substitutions, towers, copiers-under-binders are good at every depth), forcing all-index pair facts; each rejection mechanism then contradicts the all-index diagonal membership.
- *Context-manufactured pairs self-defeat:* with `Γ = x₂ ≤ x₁` and wrappers of `x₂, x₁` as the pair, `γ ∈ ⟦Γ⟧ₖ` requires `Good_k(γx₁, γx₂)` — whose inclusion component **is** the conclusion at full `k`. The break always needs index `cap+1`; the hypothesis supplies `cap`.
- *Head-padding is invisible:* delaying a term by `Iᴺ(·)` strips its memberships below `N` but neither the inclusions nor the goal — both are 4.3-invariant on the type side.
- *Divergence cannot be capped:* a divergent body is good at every bound (this model never forces body convergence), so a primed side that "digs deeper" into a variable than the unprimed side is refuted at the substitution `γx := λy≤a.Ω` — digging deeper is never semantically `≤`. And one-sided divergence at the capped `γ` only is unrealizable: caps require *reachable* defects (spine leaves), and an evaluation cannot distinguish a capped tower from its `Top`-completion without itself sticking.
- *The probes (§7) close every shape, bound, and convergence channel*, so a countermodel must live purely in deep tier content — and the model-level arithmetic for that *is* realizable (towers `c_D := λy≤Top.c_{D−1}`, `c₀ := Top(Top)` have `⟨Top⟩`-goodness capped exactly at `D`, and suitable members realize the off-by-one) — but every syntactic realization attempted flows into one of the four obstructions above.

**The desideratum, sharpened by D1's refutation.** The raw cap-anatomy hope — "in-budget-invisible defects are unreachable along converging evaluations" — is **false**: the lockstep lemma is its refutation, with the defect reachable exactly one step past the cap. What survives is the **wf-relative** version. The refuting bound `c` self-caps because its body is spine-typed on good arguments — and such a bound is not semantically well-formed. For well-formed bounds the situation is structurally different: a (closed) well-formed bound is *its own good argument at every index* (self-membership at every index is exactly `⊨ s wf` at the empty context; the inclusion components are reflexive), so its good-argument space is inhabited at all depths and the starvation mechanism is unavailable. The desideratum is therefore: **prove that semantic well-formedness of the bounds (as carried by DS-APP's instrumentation) excludes every starvation pattern** — i.e., a wf-relative cap anatomy — and convert that into the tier supply D2's self-MATCH wall needs. Equivalently: determine whether D2 is true as a *pure semantic* statement, or only for hypothesis-images of actual derivations; in the latter case, identify the additional semantic content the fundamental theorem's motive must carry (it can carry anything derivation-induction supplies).

**Partial results that already hold.** D2 restricted to *diagonal* members (those with `j ≥ j₁+1+j₂′` — the member's computation includes the type's) is provable by W-APP's accounting. D2 at `Γ = ∅` is provable (the ∀-index mode is legitimate there). The ≡-form of DS-APP is proven outright.

**If D2 is also false.** Then the instrumentation or the model must change. The principal candidate: **budget the type side in (m3)** — discount the type's weak-head steps in the MATCH index (e.g. `MATCH_{k−j−j_T}` or a max-of-both-sides discipline). This dissolves the member/type asymmetry that creates the problem, at the cost of re-proving §4 (4.4's fixed-index transport relies on the type side being free) and re-examining W-APP, whose exact diagonal accounting becomes slack. D1's refutation supplies the variant's **acceptance test**: any model in which member conversion holds must accept `λy≤c.y(⊤)` below `λy≤c.⊤` at every depth — the design tension is now concrete. Feasibility unexplored.

## 9. Safety and the recovered lemmas — modulo D2

The following proofs are complete; they consume Theorem 6.2 (hence Problem D2) and nothing else open.

**Theorem 9.1 (type safety).** If `∅ ⊢ t wf` then every `s` with `t ⟶* s` is a value or has a reduct. *Proof.* If some reachable `s` is normal and not a value it is a spine (Fact 1.1; closedness of `t` follows from wf and is preserved by reduction). By Lemma 2.2 `t ⇓` a spine — a non-value weak-head normal form. But Theorem 6.2 gives `t ∈ ⟦t⟧ₖ` for all `k` (the identity substitution is in `⟦∅⟧ₖ` for every `k`), and (m1) at `k` above the evaluation length makes `t`'s weak-head normal form a value. Contradiction. ∎

**Corollary 9.2 (progress).** `∅ ⊢ t wf ⟹ t` is a value or reduces. Preservation of safety is built into 9.1's quantification over all reducts.

**Corollary 9.3 (semantic inversion — the content of Hutchins' Lemma 5.2).** If `∅ ⊢ (λx≤a.b) ≤wf (λx≤a′.b′)` then `a =β a′`, and for every `j` and every `c ∈ ⟨a′⟩ⱼ`: `[x↦c]b ∈ ⟦[x↦c]b′⟧ⱼ` and `⟦[x↦c]b⟧ⱼ ⊆ ⟦[x↦c]b′⟧ⱼ`. *(Both sides `⇓⁰`; unfold 6.2's conclusion at every index.)*

**Corollary 9.4 (Top is not a function).** `∅ ⊢ Top ≤wf λx≤s.Top` is underivable; more generally any `t ≤wf λx≤s.b` with `t ⇓ Top` is refuted. *(Membership at index 1: (m3) demands a λ on the member side.)* Note the underlying **model** fact — `Top ∉ ⟦λx≤s.b⟧₁` — is unconditional; only the lift to underivability passes through 6.2.

## 10. Summary, and the questions

The semantic program stands: transitivity is free (§5), the rewriting imports are classical (§2), the model is well-founded with inclusions doing exactly the work they were designed for (§3–5), and the fundamental theorem is proven for every rule — **except that the application congruence DS-APP(≤) demands tier content at depths the diagonal budget cannot reach** (§8). The same wall fells member conversion, which is moreover **refuted outright** (§4.4) — so the wall is real, no raw invariant can break it, and D2's hope rests precisely on the well-formedness of its bounds. All shape/bound/convergence components of the case are recovered by definable observers (§7); the residue is purely quantitative.

For the author of the original approach, and for any attacker:

1. **(Intent.)** Definition 3.2 binds the index and the substitution's goodness jointly; was a budget-uniform reading intended? If so, in what form — given that ∀-good substitutions break W-FUN (attack 4), and ∀-good tiers break well-foundedness (attack 5)?
2. **(Wf-relative cap anatomy.)** The raw cap-anatomy claim is refuted by the lockstep lemma (§4.4). Prove the well-formed version: a semantically well-formed bound's good-argument space is inhabited at every depth (e.g. by the bound itself), and no starvation pattern à la `c := λy≤K⊤.y(⊤)(⊤)` is expressible with wf bounds; then convert this supply into the tier content D2's self-MATCH wall needs.
3. **(Semantic vs. derivable.)** Is D2 true as a *pure semantic* statement (arbitrary hypotheses satisfying the stated judgements), or only for hypothesis-images of actual derivations? If only the latter, what additional semantic content must the fundamental theorem's motive carry — it may carry anything a derivation induction supplies, and the instrumentation can be strengthened further if needed.
4. **(Model variant.)** Is the type-side-budgeted MATCH (`MATCH_{k−j−j_T}`) viable — do 4.1–4.4 and W-APP survive it? Acceptance test from §4.4: the variant must accept `λy≤c.y(⊤)` below `λy≤c.⊤` at every depth.
5. **(Countermodel.)** Exhibit a D2-falsifying configuration — i.e., realize the junk-tower arithmetic syntactically while evading all obstructions of §8 *including* the well-formedness of the four bounds — or prove the obstructions exhaustive (which is Question 2 in disguise).

A resolution of D2 in either direction completes the program: *true* gives unconditional type safety for λ⊲ with transitivity elimination retired; *false* identifies the precise model repair the approach always needed — with its acceptance test already in hand.
