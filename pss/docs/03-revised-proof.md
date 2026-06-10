# Type Safety for System λ⊲ Without Transitivity Elimination

## A semantic proof via a graded logical relation with extension inclusions

> **Status of this document.** Self-contained and mechanization-ready: it supersedes `00-proof-sketch.md` (whose Theorem 5.1 had a quantifier gap, found in `01-response.md` and repaired per `02-lean-workarounds.md`). Nothing here depends on those documents. Read §9 first if you are the mechanizing agent.

---

## 0. What is proven, and how it relates to the paper's open problems

Hutchins' type-safety argument (his §5) has exactly two gaps, both consequences of Conjecture 5.1 (transitivity elimination):

1. **Inversion** (his Lemma 5.2): from `Γ ⊢ (λx≤a.b) ≤wf (λx≤a′.b′)` conclude `a ≡ a′` — needed in the β-redex case of preservation.
2. **Top is not a function** — needed in progress, to rule out a well-formed `Top(v)` ever arising.

This document proves (1) and (2) — and the whole safety theorem — *semantically*: every closed term is interpreted as a graded set of closed terms ("its subtypes, to observation depth `k`"), every declarative rule is proved sound for the model (a fundamental theorem), and safety, inversion, and non-derivability facts are read off the model. The model is built so that:

- **DS-TRANS costs nothing**: subtyping is interpreted as membership *plus set inclusion of graded extensions*, and inclusions compose set-theoretically at a fixed index. Conjecture 5.1 is never invoked, and no transitivity lemma about the model is needed (§5).
- **No strong normalization is assumed anywhere** — divergent terms are first-class citizens (vacuously related), mandatory since λ⊲ admits Girard's paradox (his Theorem 4.4).
- The only imported facts about reduction are **Church–Rosser** and a **standardization corollary**, both for *plain unconditional β* on this syntax — *not* the contested commutativity of the algorithmic `≡⟶`/`≤⟶` of his §6. Plain β here is a left-linear orthogonal system (λ-calculus with one extra annotation subterm on binders); Tait–Martin-Löf/Takahashi apply verbatim.

Relative to the paper:

| Claim in the paper | Status here |
|---|---|
| Theorem 5.5 (Progress) | **Proven**, unconditionally (Cor. 7.2) |
| Theorem 5.6 (Preservation), in its role for safety | **Subsumed**: safety of all reducts proven directly (Thm 7.1) |
| Lemma 5.2 (Inversion), semantic content | **Proven**: bounds of related λs are β-convertible, bodies related at every depth (Cor. 7.3) |
| "Top ≤ function" underivable | **Proven** (Cor. 7.4) |
| Conjecture 5.1 (syntactic transitivity elimination) | **Not proven** — but no longer load-bearing for safety; see §8 |
| Conjecture 6.2 (`≡⟶` commutes with `≤⟶`) | **Not proven**; see §8 |

One modeling decision, flagged up front. Following the paper's §3.4 — *"The complete subtype relation is written `t ≤wf u` … Any derivation of `t ≤wf u` only compares well-formed subterms"* — we work with the **instrumented declarative system**: every node of a derivation carries well-formedness premises for the terms it mentions (§1). The result is type safety for that (§3.4) reading of Figure 1; §8 discusses what this does and does not cost.

## 1. The systems under discussion

**Syntax, reduction, values** are those of Figure 1: terms `s,t,u ::= x | Top | λx≤t.u | t(u)`; values `v,w ::= Top | λx≤t.u`; full reduction `⟶` is `(λx≤t.u)(s) ⟶ [x↦s]u` closed under all contexts (including under binders and inside bounds); `=β` is the generated conversion. We write `↦` for **weak-head reduction**: the unique redex contracted is the head one (`(λx≤a.b)(c) ↦ [x↦c]b`; `t ↦ t′ ⟹ t(u) ↦ t′(u)`). `↦` is deterministic. `t ⇓ʲ w` means `t ↦ʲ w` with `w` `↦`-normal; `t ⇓ w` means `∃j`; `t⇑` means no such `w`.

**Fact 1.1 (closed weak-head normal forms).** A closed `↦`-normal term is `Top`, a λ-abstraction, or a **spine** `Top(d₁)…(dₙ)`, `n ≥ 1`. A closed term that is `⟶`-normal and not a value is exactly a spine with `⟶`-normal `dᵢ`. *(Induction on the term: the head of a maximal application spine of a closed term cannot be a variable, and cannot be a λ or an application without creating a redex.)*

So "going wrong" for closed programs means exactly: reaching, under `⟶*`, a normal spine — `Top` applied to arguments, the paper's canonical stuck state.

**The judgements.** Well-formedness `Γ ⊢ t wf` is exactly Figure 1's. The **instrumented subtyping** `Γ ⊢ t ≤wf u` is Figure 1's declarative subtyping with the §3.4 discipline made explicit: every rule carries `Γ ⊢ · wf` premises for the terms it mentions (DS-TRANS already carries the middle one in Figure 1; W-SUB carries both endpoints; the instrumented DS-EAPP relates a well-formed redex to a well-formed contractum — if the contractum's wf is not derivable, that rule instance simply isn't available, and nothing below needs it to be). This is the relation the W-rules actually consume (W-APP's premises are `≤wf`), so it is the right relation for type safety.

Targets: `∅ ⊢ t wf ⟹ t` never goes wrong (safety); inversion; `Top` is not a function.

## 2. Facts about raw reduction

The only imported results; both concern **plain, unconditional β**.

**Lemma 2.1 (Church–Rosser).** `⟶` is confluent; hence `t =β u` iff `t, u` have a common reduct, and `=β` is substitutive (`t =β t′, s =β s′ ⟹ [x↦s]t =β [x↦s′]t′`). *(Tait–Martin-Löf/Takahashi parallel reduction; the bound is just another position.)*

**Lemma 2.2 (shape standardization).** If `t ⟶* λx≤p.q` then `t ⇓ λx≤p′.q′` with `p′ ⟶* p`, `q′ ⟶* q`. If `t ⟶* Top` then `t ⇓ Top`. If `t ⟶* Top(d₁)…(dₙ)` then `t ⇓ Top(e₁)…(eₙ)` with `eᵢ ⟶* dᵢ`. *(Corollary of standardization for orthogonal systems — Barendregt 11.4.7 / Takahashi: a standard reduction to a term with a stable head computes that head by head steps first; head reduction of these shapes is exactly `↦`.)*

**Corollary 2.3 (convergence transfer).** If `t =β v` with `v` a value, then `t ⇓ v′` where `v′` is a value of the same constructor whose components are `=β` the components of `v`. *(2.1 gives a common reduct; reducts of values keep their constructor; then 2.2.)*

## 3. The model: graded extensions with inclusions

Every closed term `T` is interpreted as a set `⟦T⟧ₖ` of closed terms — "the terms that are subtypes of `T`, to observation depth `k`". This takes the paper's own semantics literally: a term *denotes the set of terms below it* (`3` is a singleton, `Top` is everything), and §3.2's "subtypes are subsets" becomes the literal interpretation of DS-TRANS. Typing is the diagonal: `t` is semantically well-formed iff `t ∈ ⟦t⟧`.

The index `k ∈ ℕ` is consumed by **the member's weak-head steps** and by **descent into λ-bodies**; the type side is never budgeted. Divergence costs nothing.

**Definition 3.1.** By strong induction on the index — at stage `n ≥ 1` define `MATCHₙ` from `{⟦·⟧ⱼ}_{j<n}`, then `⟦·⟧ₙ` from `{MATCHₘ}_{m≤n}`; `⟦·⟧₀` is everything and `MATCH₀` imposes only the index-free shape clauses:

For closed `s, T`:
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

where the **good arguments** of a bound at depth `j` are
> `⟨a⟩ⱼ ≜ { c closed : c ∈ ⟦a⟧ⱼ, and c ∈ ⟦c⟧ⱼ, and ⟦c⟧ᵢ ⊆ ⟦a⟧ᵢ for all i ≤ j }.`

*Well-foundedness.* `MATCHₘ` references `⟦·⟧` only at indices `< m` ((t1), (t2) at `j < m`; goodness at `i ≤ j < m`), and `⟦·⟧ₖ` references `MATCHₘ` only for `m ≤ k`, whose own references stay `< k`. The inclusions (t2) and the goodness inclusions are ordinary propositions about *already-constructed* sets; the polarity of an inclusion's left-hand side is irrelevant because the family is defined by recursion on the index, not as a fixed point of a monotone operator.

Remarks. (i) `⟦T⟧₀` is everything; `⟦T⟧ₖ` for `k ≥ 1` contains every divergent term, and if `T` diverges or sticks, nothing else. (ii) `Top ∉ ⟦λx≤a.b⟧ₖ` for `k ≥ 1` — clause (m3) demands a λ on the member side. This single line is the semantic "Top is not a function". (iii) Bounds are compared by **raw conversion** `α =β a`: the paper's bound *invariance* (§3.3) means the model never needs a subtyping relation between bounds, only an equivalence, and the ≡-fragment of the declarative system collapses into `=β` (Lemma 6.1). (iv) The inclusion components (t2) and the goodness inclusions exist for exactly one reason: they make DS-TRANS set-theoretic (§5). A membership-only model must interpret DS-TRANS by composing through the middle term's *value*, which demands ∀-indexed facts that exceed the finite goodness depth of tier arguments — the classic transitivity failure of step-indexed relations. Inclusions at index `j` are consumed at index `j`; no escalation exists. (v) Goodness is downward-closed **by fiat** (the `i ≤ j` quantifier): memberships are antitone automatically (Lemma 4.1), inclusions are not, so their downward closure must be imposed for `⟨a⟩` to be antitone.

**Definition 3.2 (semantic judgements).** For `Γ = x₁≤t₁,…,xₙ≤tₙ` and closing substitution `γ` (each `γxᵢ` closed; `γtᵢ` closed by the telescope discipline):
- `γ ∈ ⟦Γ⟧ₖ` iff `γxᵢ ∈ ⟨γtᵢ⟩ₖ` for each `i`.
- `Γ ⊨ t ≤ u` iff `∀k ∀γ ∈ ⟦Γ⟧ₖ`: `γt ∈ ⟦γu⟧ₖ` **and** `⟦γt⟧ₖ ⊆ ⟦γu⟧ₖ`.
- `Γ ⊨ t wf` iff `Γ ⊨ t ≤ t` (the inclusion half is reflexivity; the content is self-membership).
- `Γ ⊨ t ≡ u` iff `t =β u` and `Γ ⊨ t wf` and `Γ ⊨ u wf`.

**Lemma 3.3 (membership from inclusion).** If `Γ ⊨ t wf` and `∀k ∀γ ∈ ⟦Γ⟧ₖ: ⟦γt⟧ₖ ⊆ ⟦γu⟧ₖ`, then `Γ ⊨ t ≤ u`. *(γt ∈ ⟦γt⟧ₖ ⊆ ⟦γu⟧ₖ.)*

Lemma 3.3 is the workhorse of the fundamental theorem: every instrumented `≤`-rule carries `Γ ⊢ t wf` for its left endpoint, so per-rule semantic obligations reduce to the **inclusion half**.

## 4. Structural lemmas

**Lemma 4.1 (antitonicity).** `j ≤ k ⟹ ⟦T⟧ₖ ⊆ ⟦T⟧ⱼ`; `MATCHₘ` antitone in `m`; `⟨a⟩ₖ ⊆ ⟨a⟩ⱼ`; hence `⟦Γ⟧ₖ ⊆ ⟦Γ⟧ⱼ`. *(Memberships: larger index imposes a superset of obligations. Goodness: the membership components by the former; the inclusion components by their explicit `i ≤ j` closure.)*

> **Discipline.** Extension inclusions `⟦t⟧ₖ ⊆ ⟦u⟧ₖ` are **not** antitone in `k`. They are therefore carried ∀-indexed in judgements (Def. 3.2 quantifies `k`) and per-index inside MATCH tiers (t2), and every use below consumes an inclusion at exactly the index at which it is supplied.

**Lemma 4.2 (step shift).** If `s ↦ s₁` then: `s₁ ∈ ⟦T⟧ₖ ⟹ s ∈ ⟦T⟧ₖ₊₁`, and `s ∈ ⟦T⟧ₖ₊₁ ⟹ s₁ ∈ ⟦T⟧ₖ`. *(`s ⇓^{j+1} v ⟺ s₁ ⇓ʲ v`; determinism of `↦`.)*

**Lemma 4.3 (type evaluation invariance).** If `T ↦ T′` then `⟦T⟧ₖ = ⟦T′⟧ₖ`. *(The clause inspects only `T`'s weak-head value.)* Note this presupposes the step `T ↦ T′` exists; uses below establish the type's convergence first (typically from (m2) of a converging member).

**Lemma 4.4 (type conversion invariance).** `T =β T′ ⟹ ⟦T⟧ₖ = ⟦T′⟧ₖ`, and `a =β a′ ⟹ ⟨a⟩ⱼ = ⟨a′⟩ⱼ`.

*Proof.* Strong induction on `k` (the goodness claim at `j` follows from the set claim at indices `≤ j`: memberships directly, inclusions because `⟦a⟧ᵢ = ⟦a′⟧ᵢ` as sets). Let `s ∈ ⟦T⟧ₖ`, `s ⇓ʲ v`, `j<k`. Then `T ⇓ w` value, `MATCH_{k−j}(v,w)`. By Corollary 2.3 applied to `T′ =β T ⇓ w`: `T′ ⇓ w′`, same constructor, `=β` components. Transport `MATCHₘ` (`m ≜ k−j`) across `w =β-componentwise w′`: `w=Top` trivial; `w = λx≤a.b`, `w′ = λx≤a″.b″`, `a″ =β a`, `b″ =β b`: bound condition composes (`α =β a =β a″`); for `j′<m` and `c ∈ ⟨a″⟩ⱼ′ = ⟨a⟩ⱼ′` (IH): (t1) transports by IH at `j′` with `[c]b =β [c]b″` (substitutivity, 2.1); (t2) transports because `⟦[c]b⟧ⱼ′ = ⟦[c]b″⟧ⱼ′` is a set *equality* by the same IH. ∎

**Lemma 4.5 (member conversion).** If `s =β s′` and `s′ ∈ ⟦T⟧ₖ` **for all** `k`, then `s ∈ ⟦T⟧ₖ` for all `k`. *(For extensions, conversion is already Lemma 4.4 — `⟦s⟧ₖ = ⟦s′⟧ₖ` — so 4.5 is only ever needed for raw memberships.)*

*Proof.* Strong induction on the goal index `k`. Let `s ⇓ʲ v`, `j < k`. Then `s′ =β v`, so by 2.3 `s′ ⇓^{i′} v′`, a value, `=β`-componentwise `v` — `i′` is unrelated to `k`, which is why the hypothesis must be ∀-quantified. Instantiating `s′ ∈ ⟦T⟧_{i′+1+n}` for every `n`: `v` is a value (same constructor as `v′`), `T ⇓ w` value, and `MATCHₙ(v′,w)` at **every** index `n`. Goal: `MATCH_{k−j}(v,w)`. `w=Top`: ✓. `w=λx≤a.b`: `v′=λx≤α′.β′` with `α′ =β a`; `v=λx≤α.β`, `α =β α′ =β a` ✓; tier `j′ < k−j ≤ k`, `c ∈ ⟨a⟩ⱼ′`: (t1) `[c]β′ ∈ ⟦[c]b⟧` at every index (from MATCH at every index), `[c]β =β [c]β′`, so IH at `j′ < k` gives `[c]β ∈ ⟦[c]b⟧ⱼ′`; (t2) `⟦[c]β⟧ⱼ′ = ⟦[c]β′⟧ⱼ′ ⊆ ⟦[c]b⟧ⱼ′` by 4.4 and the tier of `MATCH_{j′+1}(v′,w)`. ∎

The asymmetry between 4.4 (fixed index) and 4.5 (∀-index) is principled: the type side is unbudgeted, the member side counts steps, and conversion changes step counts. Every use of 4.5 below has ∀-index facts available, because semantic judgements are ∀-quantified.

## 5. Transitivity is set-theoretic

**Theorem 5.1 (DS-TRANS is free).** If `Γ ⊨ s ≤ t` and `Γ ⊨ t ≤ u` then `Γ ⊨ s ≤ u`.

*Proof.* Fix `k`, `γ ∈ ⟦Γ⟧ₖ`. Membership: `γs ∈ ⟦γt⟧ₖ ⊆ ⟦γu⟧ₖ`. Inclusion: `⟦γs⟧ₖ ⊆ ⟦γt⟧ₖ ⊆ ⟦γu⟧ₖ`. ∎

That is the entire interpretation of DS-TRANS: composition happens at a single fixed index, the middle term is never evaluated, and its value is never inspected. (This is why the inclusions are in the model. Without them, transitivity must be composed through `MATCH` of the middle's value, whose ∀-indexed facts are capped by the finite goodness depth of tier arguments — the standard failure mode of step-indexed transitivity. With them, there is no transitivity lemma left to prove.)

## 6. The fundamental theorem

**Lemma 6.1 (the ≡-fragment is conversion).** If `Γ ⊢ t ≡wf u` then `t =β u`. *(Induction: every ≡-rule — DS-EAPP, the ≡-instances of DS-FUN/DS-APP/DS-TRANS, DS-SYM, DS-VAR, DS-TOP — is valid for `=β`; DS-EQ produces only `≤`, and no rule produces `≡` from `≤`, so ≡-derivations contain only these.)*

**Theorem 6.2 (fundamental theorem).** For the instrumented system:
1. `Γ ⊢ t wf ⟹ Γ ⊨ t wf`;
2. `Γ ⊢ t ≤wf u ⟹ Γ ⊨ t ≤ u`;
3. `Γ ⊢ t ≡wf u ⟹ Γ ⊨ t ≡ u`.

*Proof.* Mutual induction on derivations. Fix `k` and `γ ∈ ⟦Γ⟧ₖ` per case; premise judgements may be instantiated at any index `≤ k` (Lemma 4.1) with the same `γ`, and at ∀-index via the ∀ in Definition 3.2. **For every `≤`-rule, the membership half follows from the inclusion half by Lemma 3.3** (the instrumented node carries `Γ ⊢ t wf` for its left endpoint; IH(1) gives `Γ ⊨ t wf`); the cases below therefore establish inclusions for `≤`-rules, self-memberships for wf-rules, and `=β`+wf for ≡-rules.

**(W-VAR)** `γx ∈ ⟦γx⟧ₖ` is the self-membership component of `γx ∈ ⟨γ(Γx)⟩ₖ`. ✓

**(W-TOP, DS-TOP)** `Top ⇓⁰ Top`, `MATCH(Top,Top)` ✓.

**(W-FUN)** Goal `Λ ∈ ⟦Λ⟧ₖ`, `Λ ≜ λx≤γa.γb`. `Λ ⇓⁰ Λ`, a value; (m3) at `m=k`: bound `γa =β γa` ✓; tier `j<k`, `c ∈ ⟨γa⟩ⱼ`: `γ[x↦c] ∈ ⟦Γ, x≤a⟧ⱼ` (ambient components by 4.1; the new entry is *literally* the tier's domain condition — strengthened goodness in the tier matches strengthened goodness in Def. 3.2), so IH(1) of `Γ,x≤a ⊢ b wf` at `j` gives (t1) `[c]γb ∈ ⟦[c]γb⟧ⱼ`; (t2) is reflexivity. ✓

**(W-APP)** Premises (via W-SUB): `Γ ⊢ t ≤wf λx≤s.Top`, `Γ ⊢ u ≤wf s`, with wf of `t, u, λx≤s.Top`. Write `T ≜ γt, U ≜ γu, S ≜ γs`. Goal: `T(U) ∈ ⟦T(U)⟧ₖ`. Suppose `T(U) ⇓ʲ v`, `j<k`. The head evaluation factors through `T ⇓^{j₁} w_T` (else `T(U)⇑`):
- `w_T` is a value: IH(1) `T ∈ ⟦T⟧_{j₁+1}` (∀-index, instantiate above `j₁`) gives (m1).
- `w_T` is a λ with the right bound: IH(2) membership gives `T ∈ ⟦λx≤S.Top⟧_{j₁+1}`, whose (m3) forces `w_T = λx≤A.B` with `A =β S`. *(Were `w_T = Top`, the member side of (m3) would fail — the progress-critical step.)*
- So `T(U) ↦^{j₁} (λx≤A.B)(U) ↦ [x↦U]B ⇓^{j₂} v` with `j = j₁+1+j₂`.
- `U` is a **good argument at every depth**: `U ∈ ⟦S⟧ⱼ′ = ⟦A⟧ⱼ′` (IH(2) membership for `u ≤ s` at every index; 4.4), `U ∈ ⟦U⟧ⱼ′` (IH(1)), and `⟦U⟧ᵢ ⊆ ⟦S⟧ᵢ = ⟦A⟧ᵢ` (IH(2) **inclusion** for `u ≤ s` at every `i`; 4.4). So `U ∈ ⟨A⟩ⱼ′` for all `j′`.
- Self-description of the body: IH(1) `T ∈ ⟦T⟧_{j₁+1+m}` for every `m` gives `MATCH_{m+1}(w_T, w_T)` for every `m`; its tier (t1) at `j′ ≔ k−j₁−1` with argument `U`: `[x↦U]B ∈ ⟦[x↦U]B⟧_{k−j₁−1}`.
- Conclude: `[x↦U]B ⇓^{j₂} v` with `j₂ < k−j₁−1` (since `j<k`), so `v` is a value (m1), and `MATCH_{(k−j₁−1)−j₂}(v, ·) = MATCH_{k−j}(v, ·)` against the type side: `⟦T(U)⟧ₖ = ⟦[x↦U]B⟧ₖ` by 4.3 (the steps exist, as just established), whose weak-head value is `v` itself — (m2) ✓, `MATCH_{k−j}(v,v)` ✓. ✓

The member's `j₁+1` consumed steps pay precisely for the tier descent `j′ = k−j₁−1`; nothing erodes.

**(DS-EVAR)** Inclusion `⟦γx⟧ₖ ⊆ ⟦γ(Γx)⟧ₖ` is the inclusion component of `γx ∈ ⟨γ(Γx)⟩ₖ` (at `i = k`); membership likewise. ✓ *(This is precisely where storing inclusions in goodness breaks the circularity: deriving the inclusion from the membership would itself be a transitivity argument.)*

**(DS-ETOP)** Inclusion `⟦γt⟧ₖ ⊆ ⟦Top⟧ₖ`: for `s ∈ ⟦γt⟧ₖ` with `s ⇓ʲ v`, `j<k`: `v` is a value by `s`'s own (m1); `Top ⇓⁰ Top`; `MATCH(v,Top)` ✓. ✓

**(DS-EQ)** IH(3): `t =β u`; 4.4 gives the set *equality* `⟦γt⟧ₖ = ⟦γu⟧ₖ` — both halves. ✓ **(DS-SYM)** symmetric in `=β` and wf ✓. **(DS-EAPP)** `(λx≤γt.γu)(γs) =β [x↦γs]γu` is one β-step; both endpoints' wf are instrumented premises; the conclusion is an ≡-judgement ✓.

**(DS-TRANS, both forms)** Theorem 5.1. ✓ *(The instrumented middle-wf premise is not even needed semantically.)*

**(DS-FUN, ≤-form)** Premises `Γ ⊢ t ≡wf t′` (so `γt =β γt′` by 6.1) and `Γ, x≤t ⊢ u ≤wf u′`, plus instrumented wf of both λs. Goal (inclusion half): `⟦Λ⟧ₖ ⊆ ⟦Λ′⟧ₖ`, `Λ ≜ λx≤γt.γu`, `Λ′ ≜ λx≤γt′.γu′`. Take `s ∈ ⟦Λ⟧ₖ`, `s ⇓ʲ v`, `j<k`. `Λ ⇓⁰ Λ`, so `MATCH_{k−j}(v,Λ)`: `v = λx≤α.β`, `α =β γt =β γt′` ✓ (bound clause for `Λ′`); `Λ′ ⇓⁰ Λ′` (m2) ✓. Tiers for `Λ′` at `j′ < k−j`, `c ∈ ⟨γt′⟩ⱼ′ = ⟨γt⟩ⱼ′` (4.4): `γ[x↦c] ∈ ⟦Γ,x≤t⟧ⱼ′`, so IH(2) of the body premise at `j′` gives the inclusion `⟦[c]γu⟧ⱼ′ ⊆ ⟦[c]γu′⟧ⱼ′`; from `s`'s own tier: (t1) `[c]β ∈ ⟦[c]γu⟧ⱼ′` and (t2) `⟦[c]β⟧ⱼ′ ⊆ ⟦[c]γu⟧ⱼ′`. Compose both through the IH inclusion: (t1) `[c]β ∈ ⟦[c]γu′⟧ⱼ′` ✓, (t2) `⟦[c]β⟧ⱼ′ ⊆ ⟦[c]γu′⟧ⱼ′` ✓. So `s ∈ ⟦Λ′⟧ₖ`. *(Everything composes at the fixed index `j′`; no ∀-escalation.)* (The ≡-form needs only 6.1 and the wf parts.) ✓

**(DS-APP, ≤-form)** Premises: `Γ ⊢ t ≤wf t′`, `Γ ⊢ u ≡wf u′` (so `U =β U′` by 6.1), plus instrumented `Γ ⊢ t(u) wf` and `Γ ⊢ t′(u′) wf` with their W-APP sub-derivations (bounds `s`, `s′` respectively; all IHs available). Goal (inclusion half): `⟦T(U)⟧ₖ ⊆ ⟦T′(U′)⟧ₖ`. Take `σ ∈ ⟦T(U)⟧ₖ`; if `σ` never converges below `k` the goal membership is vacuous; otherwise `σ ⇓ʲ v`, `j<k`, and `σ`'s (m1)/(m2) give: `v` a value and `T(U) ⇓` a value. Then:

- (a) *Unprimed function value.* `T(U) ⇓` forces `T ⇓^{j₁} w_T`; `w_T` is a value (IH(1) of `t` wf above `j₁`) and `w_T = λx≤A.B` with `A =β S` (IH(2) membership of `t ≤wf λx≤s.Top`, (m3)). So `T(U) ↦^{j₁+1} [x↦U]B` and, by 4.3, `⟦T(U)⟧ᵢ = ⟦[x↦U]B⟧ᵢ` for all `i`.
- (a′) *Primed function value.* IH(2) membership of `t ≤wf t′` at `j₁+1`: since `T ⇓^{j₁} w_T`, (m2) gives `T′ ⇓ w_{T′}`, a value; the primed instrumentation (`T′ ∈ ⟦λx≤S′.Top⟧` at any index above `T′`'s own evaluation) forces `w_{T′} = λx≤A′.B′` with `A′ =β S′`. So `T′(U′) ↦* [x↦U′]B′` and `⟦T′(U′)⟧ᵢ = ⟦[x↦U′]B′⟧ᵢ` (4.3).
- (b) *Function values match at every index*: IH(2) membership of `t ≤wf t′` at `j₁+1+n` for every `n` gives `MATCH_∀(w_T, w_{T′})`.
- (c) ***The bound-conversion chain***: `S =β A` (a), `A =β A′` ((b)'s bound clause), `A′ =β S′` (a′). Hence `S =β S′` — note this connects the bounds of the **two independent W-APP instrumentations**, and is needed next.
- (d) *`U` is ∀-good at `A′`*: membership `U ∈ ⟦A′⟧_∀ `: `U′ ∈ ⟦S′⟧_∀` (IH(2) membership of the primed sub-derivation's `u′ ≤wf s′`), `U =β U′`, so **member conversion (4.5)** (∀-index available ✓) gives `U ∈ ⟦S′⟧_∀ = ⟦A′⟧_∀` (4.4). Self-membership `U ∈ ⟦U⟧_∀`: IH(1). Inclusions: `⟦U⟧ᵢ ⊆ ⟦S⟧ᵢ` (IH(2) **inclusion** of the unprimed `u ≤wf s`, every `i`) and `⟦S⟧ᵢ = ⟦S′⟧ᵢ = ⟦A′⟧ᵢ` (4.4 via (c)). So `U ∈ ⟨A′⟩ᵢ` for all `i`.
- (e) *Strengthened tier of (b) at `c = U`*, any index `j′`: (t1) `[x↦U]B ∈ ⟦[x↦U]B′⟧ⱼ′` and (t2) `⟦[x↦U]B⟧ⱼ′ ⊆ ⟦[x↦U]B′⟧ⱼ′`.
- (f) *Primed conversion*: `[x↦U]B′ =β [x↦U′]B′` (substitutivity), so `⟦[x↦U]B′⟧ᵢ = ⟦[x↦U′]B′⟧ᵢ` (4.4).
- (g) *Conclude*: `σ ∈ ⟦T(U)⟧ₖ = ⟦[x↦U]B⟧ₖ ⊆ ⟦[x↦U]B′⟧ₖ = ⟦[x↦U′]B′⟧ₖ = ⟦T′(U′)⟧ₖ`, using (a), (e)(t2) at `k`, (f), (a′). ✓

(Membership half: Lemma 3.3 with IH(1) of the instrumented `t(u)` wf. The ≡-form is 6.1 plus the wf parts.) **(W-SUB, W-GAM1/2)** bookkeeping. ∎

## 7. Safety and the recovered lemmas

**Theorem 7.1 (type safety — "well-formed terms don't go wrong").** If `∅ ⊢ t wf` then every `s` with `t ⟶* s` is a value or has a reduct.

*Proof.* Suppose some reachable `s` is normal and not a value, hence (Fact 1.1) a spine `Top(d⃗)`. By Lemma 2.2, `t ⇓ Top(e⃗)`, a non-value weak-head normal form. But Theorem 6.2 gives `t ∈ ⟦t⟧ₖ` for all `k` (the empty substitution is in `⟦∅⟧ₖ` trivially), and (m1) at any `k` exceeding the evaluation length says `t`'s weak-head normal form is a value. Contradiction. ∎

**Corollary 7.2 (progress).** `∅ ⊢ t wf ⟹ t` is a value or reduces. **Preservation of safety** is built in: Theorem 7.1 quantifies over all reducts, so it is closed under `⟶` by construction — the model-theoretic statement does the work the paper's Theorem 5.6 was for, without preserving derivations syntactically.

**Corollary 7.3 (semantic inversion — Lemma 5.2's content).** If `∅ ⊢ (λx≤a.b) ≤wf (λx≤a′.b′)` then `a =β a′`, and for every depth `j` and every `c ∈ ⟨a′⟩ⱼ`: `[x↦c]b ∈ ⟦[x↦c]b′⟧ⱼ` and `⟦[x↦c]b⟧ⱼ ⊆ ⟦[x↦c]b′⟧ⱼ`. *(Both sides `⇓⁰`; unfold Theorem 6.2's conclusion at every index.)* In particular the argument-compatibility fact needed in the paper's redex case holds: if also `∅ ⊢ c ≤wf a′` then `c`'s memberships and inclusions transfer to `a` by 4.4.

**Corollary 7.4 (Top is not a function).** `∅ ⊢ Top ≤wf λx≤s.Top` is underivable: it would give `Top ∈ ⟦λx≤s.Top⟧₁`, whose (m3) requires the member's value to be a λ. *(Likewise any `t ≤wf λx≤s.Top` with `t ⇓ Top` is refuted — the model proves non-derivability statements wholesale.)*

Sanity checks against the paper's examples: `3 ≤ Nat` (§3.5) — Church `3` and `Nat` weak-head evaluate to λs with `=β`-equal bounds at every level, the body memberships unfold along the encodings, and the inclusion halves hold because the bodies converge to the *same* shapes (the extensions coincide). Girard-paradox terms (Theorem 4.4 of the paper) are welcome: a wf looping term is in every `⟦·⟧ₖ` it needs to be in, vacuously where it diverges — no lemma above assumes termination of anything.

## 8. Scope and caveats

**Proven.** Type safety for λ⊲ — the conjunction the paper extracts from Theorems 5.5/5.6 — holds *unconditionally* for the §3.4 (instrumented) reading of the declarative system, with no appeal to Conjecture 5.1. The two load-bearing consequences of transitivity elimination (inversion; Top-not-a-function) are theorems of the model. DS-TRANS is interpreted by set inclusion — composition at a fixed index — so the missing induction principle of the paper's §6.7 is simply not needed: *member steps and λ-depth are budgeted on one side; the type side is never budgeted; inclusions are index-local.* That asymmetry is unavailable to a rewriting-style proof, which must treat both sides of `≤⟶`/`≡⟶` symmetrically as reductions.

**Not proven.** (1) **Syntactic transitivity elimination** (Conjecture 5.1) — that every `≤wf` derivation can be *rewritten* to end in DS-FUN/DS-ETOP — remains open, as does (2) **Conjecture 6.2** (commutativity of `≡⟶` with `≤⟶`) and with it the analysis of the algorithmic system of Figure 2. The model yields the *consequences* of transitivity elimination that safety needs, not the derivation-normalization fact itself. (3) The result is for the **instrumented** relation. The uninstrumented Figure-1 relation over ill-formed terms (the thing SRE-TOPAPP exists to repair) may relate junk; since W-APP only ever consumes `≤wf`, safety of well-formed programs is indifferent to this. (4) Universes (§3.6) are orthogonal exactly as in the paper.

**Why bound-invariance mattered.** The collapse of the ≡-fragment to `=β` (Lemma 6.1) is what lets bounds be compared by raw conversion, discharged by Church–Rosser for plain β. Contravariant bounds would force a negatively-occurring graded membership for bounds and forfeit the confinement of all rewriting theory to the standard λ-calculus. The paper's invariance choice is exactly what makes its metatheory semantically tractable.

## 9. Mechanization notes

Target: Lean 4, extending the existing development under `pss/` (no mathlib). What exists and what to build:

**Already in the repo** (reuse, do not redefine): `Pss.Term` syntax with the σ-calculus substitution library (`Pss/Syntax.lean` — `rename`/`subst`/`subst1`, composition lemmas, `shift_subst1`); full reduction `Pss.Step` and `Steps` (`Pss/Reduction.lean` — `Step.Compat` gives the per-constructor induction principle); `Star`/`Sym` closures (`Pss/Star.lean`). The Figure-1 judgments in `Pss/Declarative.lean` are the *uninstrumented* system — do **not** modify them.

**To define fresh:**
1. Weak-head reduction `↦` (deterministic; head-β plus head-of-application closure), `⇓ʲ`, `⇓`, divergence; Fact 1.1.
2. `=β` as `EqClosure Step`; plain-β confluence (Lemma 2.1 — Takahashi parallel reduction; strictly simpler than the *guarded* `Par` already worked out in `Pss/Confluence.lean`, which can serve as a template with all guard machinery deleted) and shape standardization (Lemma 2.2 — the heaviest import; prove the three shape cases directly via parallel-reduction head-step bookkeeping rather than full standardization if that is lighter).
3. The **instrumented system**: a new mutual inductive (`WfI`/`SubI` say) — Figure 1's rules with wf premises at every node per §1. Keep constructor-per-rule naming as in `Pss/Declarative.lean`.
4. The model: `Mem : Nat → Term → Term → Prop` (`Mem k s T` is `s ∈ ⟦T⟧ₖ`) by **strong recursion on `k`** — every recursive reference inside the body (through the inlined `MATCH` and goodness, Definition 3.1) is at an index `< k`, so this is an ordinary well-founded recursion, *not* an inductive predicate (the inclusions occur negatively; that is fine for recursion, fatal for induction). Then define `Match` and goodness as non-recursive definitions over `Mem` and prove the unfolding equation for `Mem k` in terms of `Match`.
5. Lemmas in dependency order: 4.1 (antitonicity, including goodness), 4.2, 4.3, 4.4 + 4.5 (mutual-ish: 4.5 uses 4.4; both by strong induction on the index), 3.3, 5.1, 6.1, then the FT (6.2) by induction on the instrumented derivation, then 7.1–7.4.

**Watchpoints** (the places a residual error would hide):
- The ∀-index discipline: inclusions are not antitone; never weaken an inclusion hypothesis to a smaller index implicitly — take it at the index of use.
- Lemma 4.4's MATCH-transport now carries the (t2) components; they ride the IH's set equalities and are easier than (t1), but must not be forgotten in the case analysis.
- DS-APP's bound-conversion chain (c): `S =β A =β A′ =β S′` — four links from three different sources (two instrumentations + one MATCH). Build it as an explicit lemma; it is the one fact connecting the two W-APP sub-derivations.
- 4.3 presupposes the type's weak-head step exists; in FT cases the step is licensed by (m2) of a converging member — keep the inclusion proofs elementwise (vacuous for never-converging members) rather than as set-algebra, so the convergence hypotheses are in scope when 4.3 is invoked.
- W-APP's step-accounting (`j = j₁+1+j₂` paying for tier depth `k−j₁−1`) is exact; off-by-ones here are the likeliest mechanical bug. Prove the head-factorization of `⇓` through application as a standalone lemma first.
- Closedness: the model is on closed terms; `γ` ranges over closing substitutions (telescope discipline: `γtᵢ` closed). Reuse `Term.ClosedUnder`; expect a small lemma kit relating `subst`, closedness, and `γ[x↦c]`.

**Statement-fidelity rules** (same as the rest of `pss/`): no `sorry`, no `axiom`; anything unfinished becomes a `Prop` in `Pss.Statements` with a status docstring; Conjectures 5.1/6.2 of the paper remain untouched statements; the deliverables are Theorem 7.1, Corollaries 7.2–7.4, and the fundamental theorem 6.2, in a new file group (suggested: `Pss/Semantic/WeakHead.lean`, `Pss/Semantic/BetaTheory.lean`, `Pss/Semantic/Instrumented.lean`, `Pss/Semantic/Model.lean`, `Pss/Semantic/Fundamental.lean`, `Pss/Semantic/Safety.lean`).

---

**Summary.** Interpret every closed term `T` as the graded set `⟦T⟧ₖ` of Definition 3.1 — members' weak-head steps and λ-depth consume `k`; bounds compared by `=β`; the type side unbudgeted; **tiers and goodness carry extension inclusions**. Interpret `t ≤ u` as membership *plus inclusion*, wf as self-membership, ≡ as conversion. Church–Rosser and shape standardization for plain β give the conversion lemmas; DS-TRANS composes set-theoretically at a fixed index (Theorem 5.1, three lines); the fundamental theorem (6.2) reduces per-rule work to inclusion halves via Lemma 3.3, with W-APP/DS-APP closing by exact step/depth accounting and the `S =β S′` bound chain; adequacy (7.1–7.4) delivers progress, preservation-of-safety, semantic inversion, and `Top ≰ λ` — type safety for System λ⊲ with transitivity elimination retired from the critical path and left, explicitly, as the still-open proof-theoretic question it always was.
