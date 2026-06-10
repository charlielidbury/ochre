# Type Safety for System λ⊴ Without Transitivity Elimination

## A semantic proof via a graded logical relation

---

## 0. What is proven, and how it relates to the paper's open problems

Hutchins' type-safety argument (his §5) has exactly two gaps, both consequences of Conjecture 5.1 (transitivity elimination):

1. **Inversion** (his Lemma 5.2): from `Γ ⊢ (λx≤a.b) ≤wf (λx≤a′.b′)` conclude `a ≡ a′` — needed in the β-redex case of preservation, so that an argument acceptable at the *declared* bound `a′` is acceptable at the *actual* bound `a`.
2. **Top is not a function** — needed in progress, to rule out a well-formed `Top(v)` ever arising.

Everything else in his §5 (substitution, narrowing, the induction skeleton of progress and preservation) goes through syntactically and I take it as given. My strategy is to prove (1) and (2) — and in fact the whole safety theorem — *semantically*: I construct a model of the declarative judgements as relations on closed terms defined by observation under weak-head evaluation, prove every declarative rule sound for the model (a fundamental theorem), and read safety, inversion, and non-derivability facts off the model. The model is built so that:

- **transitivity of the semantic relation is a lemma, not an axiom** — so DS‑TRANS costs nothing and Conjecture 5.1 is never invoked;
- **no strong normalization is assumed anywhere** — divergent terms are first-class citizens of the model (they are vacuously related), which is mandatory since λ⊴ admits Girard's paradox (his Theorem 4.4);
- the only facts imported about raw reduction are **Church–Rosser** and a **standardization corollary**, both for *plain unconditional β* on this syntax — emphatically *not* the contested commutativity of the algorithmic `≡⟶`/`≤⟶` of his §6. Plain β here is just the λ-calculus with one extra annotation subterm on binders; Tait–Martin-Löf and Takahashi's arguments apply verbatim.

What this document establishes, relative to the paper:

| Claim in the paper | Status here |
|---|---|
| Theorem 5.5 (Progress) | **Proven**, unconditionally (Cor. 9.2) |
| Theorem 5.6 (Preservation), in its role for safety | **Subsumed**: safety of all reducts proven directly (Thm 9.1) |
| Lemma 5.2 (Inversion), semantic content | **Proven**: bounds of related λs are β-convertible (Cor. 9.3) |
| "Top ≤ function" underivable | **Proven** (Cor. 9.4) |
| Conjecture 5.1 (syntactic transitivity elimination) | **Not proven** — but no longer load-bearing for safety; see §10 |
| Conjecture 6.2 (`≡⟶` commutes with `≤⟶`) | **Not proven**; see §10 for why this proof evades that obstruction |

One modeling decision must be flagged up front. Following the paper's §3.4 — *"The complete subtype relation is written `t ≤wf u` … Any derivation of `t ≤wf u` only compares well-formed subterms"* — I work with the **instrumented declarative system**: every node of

## 1. The systems under discussion

**Syntax, reduction, values** are those of Figure 1: terms `s,t,u ::= x | Top | λx≤t.u | t(u)`; values `v,w ::= Top | λx≤t.u`; full reduction `⟶` is `(λx≤t.u)(s) ⟶ [x↦s]u` closed under all contexts (including under binders and inside bounds); `=β` is the generated conversion. I write `↦` for **weak-head reduction**: the unique redex contracted is the head one (`(λx≤a.b)(c) ↦ [x↦c]b`; `t ↦ t′ ⟹ t(u) ↦ t′(u)`). `↦` is deterministic. `t ⇓ʲ w` means `t ↦ʲ w` with `w` `↦`-normal; `t ⇓ w` means `∃j`, and `t⇑` means no such `w` exists.

**Fact 1.1 (closed weak-head normal forms).** A closed `↦`-normal term is `Top`, a λ-abstraction, or a **spine** `Top(d₁)…(dₙ)`, `n ≥ 1`. A closed term that is `⟶`-normal and not a value is exactly a spine with `⟶`-normal `dᵢ`. *(Induction on the term; the head of a maximal application spine of a closed term cannot be a variable, and cannot be a λ or an application without creating a redex.)*

So "going wrong" for closed programs means exactly: reaching, under `⟶*`, a normal spine — `Top` applied to arguments, the paper's canonical stuck state.

**The judgements.** I prove safety for the system the paper calls the *complete* relation (§3.4): well-formedness `Γ ⊢ t wf` exactly as in Figure 1, and the **instrumented subtyping** `Γ ⊢ t ⊴wf u`, which is Figure 1's declarative rules with the §3.4 discipline made explicit: every node relates well-formed terms (each rule carries `Γ ⊢ t wf` premises for the terms it mentions; DS-TRANS already carries the middle one in Figure 1, W-SUB carries both endpoints). In particular the instrumented DS-EAPP relates a well-formed redex to its well-formed contractum — no substitution lemma is smuggled in; if the contractum's wf is not derivable the rule instance simply isn't available, and nothing below needs it to be. This is the relation the W-rules actually consume (W-APP's premises are `≤wf`), so it is the right relation for type safety. I return in §8 to what this choice does and doesn't cost.

Two judgements are the targets: `∅ ⊢ t wf ⟹ t` never goes wrong (safety), and the two missing lemmas (inversion; `Top` is not a function).

## 2. Facts about raw reduction

These are the only imported results, and they concern **plain, unconditional β** on this syntax — a left-linear orthogonal system, the λ-calculus with one extra subterm slot on binders. Neither has anything to do with the conditional, context-sensitive reductions of the paper's §6.

**Lemma 2.1 (Church–Rosser).** `⟶` is confluent; hence `t =β u` iff `t, u` have a common reduct, and `=β` is substitutive (`t =β t′, s =β s′ ⟹ [x↦s]t =β [x↦s′]t′`). *(Tait–Martin-Löf/Takahashi parallel reduction, verbatim; the bound is just another position.)*

**Lemma 2.2 (shape standardization).** If `t ⟶* λx≤p.q` then `t ⇓ λx≤p′.q′` with `p′ ⟶* p`, `q′ ⟶* q`. If `t ⟶* Top` then `t ⇓ Top`. If `t ⟶* Top(d₁)…(dₙ)` then `t ⇓ Top(e₁)…(eₙ)` with `eᵢ ⟶* dᵢ`. *(Corollary of the standardization theorem for orthogonal systems — Barendregt 11.4.7 / Takahashi's parallel-reduction proof: a standard reduction to a term with a stable head must compute that head by head steps first; head reduction of these shapes is exactly `↦` and terminates in the displayed forms.)*

**Corollary 2.3 (convergence transfer).** If `t =β v` with `v` a value, then `t ⇓ v′` where `v′` is a value of the same constructor whose components are `=β` the components of `v` (for λ: bound to bound, body to body). *(2.1 gives a common reduct of `t` and `v`; reducts of values keep their constructor; then 2.2.)*

## 3. The model: graded extensions

Every closed term `T` is interpreted as a set `⟦T⟧ₖ` of closed terms — "the terms that are subtypes of `T`, to observation depth `k`". This is the paper's own semantics taken literally: a term *denotes the set of terms below it*; `3` is a singleton, `Top` is everything, and membership of `t` in `⟦u⟧` is the semantic reading of `t ≤ u`. Typing is the diagonal: `t` is semantically well-formed iff `t ∈ ⟦t⟧` — "every term is a subtype of itself", self-membership as self-description.

The index `k ∈ ℕ` is consumed by **the member's weak-head steps** and by **descent into λ-bodies**; the type side is never budgeted. Divergence costs nothing — mandatory, since λ⊴ is not SN.

**Definition 3.1.** By strong induction on `k`, with `MATCH` defined after the memberships of strictly smaller index (the order is `⟦·⟧₀, MATCH₀-at-tiers<0… , ⟦·⟧₁, …`; precisely: `MATCHₘ` refers to `⟦·⟧ⱼ` only for `j < m`, and `⟦·⟧ₖ` refers to `MATCHₘ` for `m ≤ k`):

For closed `s, T`:
> `s ∈ ⟦T⟧ₖ` iff for all `j < k`: if `s ⇓ʲ v` then
> (m1) `v` is a value, and
> (m2) `T ⇓ w` for some value `w`, and
> (m3) `MATCH_{k−j}(v, w)`.

For values `v, w`:
> `MATCHₘ(v, w)` holds iff:
> - `w = Top`: always;
> - `w = λx≤a.b`: `v = λx≤α.β` for some `α =β a`, and for all `j < m` and all `c ∈ ⟨a⟩ⱼ`: `[x↦c]β ∈ ⟦[x↦c]b⟧ⱼ`;

where the **good arguments** of a bound at depth `j` are
> `⟨a⟩ⱼ ≜ { c closed : c ∈ ⟦a⟧ⱼ and c ∈ ⟦c⟧ⱼ }.`

Remarks. (i) `⟦T⟧₀` is everything; `⟦T⟧ₖ` for `k ≥ 1` contains every divergent term, and if `T` diverges or sticks, nothing else. (ii) `Top ∉ ⟦λx≤a.b⟧ₖ` for `k ≥ 1` — clause (m3) demands a λ on the member side. This single line is the semantic "Top is not a function". (iii) Bounds are compared by **raw conversion** `α =β a`. This is where the paper's *invariance* of bounds (§3.3) is cashed in: invariance means the model never needs a subtyping relation between bounds, only an equivalence — and the ≡-fragment of the declarative system will collapse into `=β` (Lemma 6.1), so conversion is exactly enough. This collapse is what frees the construction from comparing bounds by a (negatively occurring, circularity-inducing) semantic relation.

**Definition 3.2 (semantic judgements).** For `Γ = x₁≤t₁,…,xₙ≤tₙ` and closing substitution `γ` (each `γxᵢ` closed; note `γtᵢ` is closed by the telescope discipline):
- `γ ∈ ⟦Γ⟧ₖ` iff `γxᵢ ∈ ⟨γtᵢ⟩ₖ` for each `i` (membership in the bound's extension, plus self-membership).
- `Γ ⊨ t ≤ u` iff `∀k ∀γ ∈ ⟦Γ⟧ₖ: γt ∈ ⟦γu⟧ₖ`.
- `Γ ⊨ t wf` iff `Γ ⊨ t ≤ t`.
- `Γ ⊨ t ≡ u` iff `t =β u` and `Γ ⊨ t wf` and `Γ ⊨ u wf`.

Subtyping is modeled as membership, well-formedness as self-membership, equivalence as conversion-plus-well-formedness. There are no relation-pairs and no set inclusions in the judgements; this is what makes the whole development go through.

## 4. Structural lemmas

**Lemma 4.1 (antitonicity).** `j ≤ k ⟹ ⟦T⟧ₖ ⊆ ⟦T⟧ⱼ` and `MATCHₘ` antitone in `m`. Hence `⟦Γ⟧ₖ ⊆ ⟦Γ⟧ⱼ`. *(Immediate: larger index imposes a superset of obligations.)*

**Lemma 4.2 (step shift).** If `s ↦ s₁` then: `s₁ ∈ ⟦T⟧ₖ ⟹ s ∈ ⟦T⟧ₖ₊₁`, and `s ∈ ⟦T⟧ₖ₊₁ ⟹ s₁ ∈ ⟦T⟧ₖ`. *(`s ⇓^{j+1} v ⟺ s₁ ⇓ʲ v`; determinism of `↦`.)*

**Lemma 4.3 (type evaluation invariance).** If `T ↦ T′` then `⟦T⟧ₖ = ⟦T′⟧ₖ`. *(The clause inspects only `T`'s weak-head value.)*

**Lemma 4.4 (type conversion invariance).** `T =β T′ ⟹ ⟦T⟧ₖ = ⟦T′⟧ₖ`, and `a =β a′ ⟹ ⟨a⟩ⱼ = ⟨a′⟩ⱼ`.

*Proof.* Strong induction on `k` (the second claim at index `j` follows from the first at `j`). Let `s ∈ ⟦T⟧ₖ`, `s ⇓ʲ v`, `j<k`. Then `T ⇓ w` value, `MATCH_{k−j}(v,w)`. By Corollary 2.3 applied to `T′ =β T ⇓ w`: `T′ ⇓ w′`, same constructor, `=β` components. It remains to transport `MATCHₘ` across `w =β-componentwise w′` (m ≜ k−j). `w=Top`: trivial. `w = λx≤a.b`, `w′ = λx≤a″.b″`, `a″ =β a`, `b″ =β b`: bound condition composes (`α =β a =β a″`); for `j′<m` and `c ∈ ⟨a″⟩ⱼ′ = ⟨a⟩ⱼ′` (IH at `j′<k`), we have `[c]β ∈ ⟦[c]b⟧ⱼ′ = ⟦[c]b″⟧ⱼ′` by IH at `j′` with `[c]b =β [c]b″` (substitutivity, 2.1). ∎

**Lemma 4.5 (member conversion).** If `s =β s′` and `s′ ∈ ⟦T⟧ₖ` **for all** `k`, then `s ∈ ⟦T⟧ₖ` for all `k`.

*Proof.* Strong induction on the goal index `k`. Let `s ⇓ʲ v`, `j < k`. Then `s′ =β v`, so by 2.3 `s′ ⇓^{i′} v′` with `v′` a value, `=β`-componentwise `v` — note `i′` is unrelated to `k`, which is why the hypothesis must be ∀-quantified. Instantiating `s′ ∈ ⟦T⟧_{i′+1+n}` for every `n`: `v′` is a value (m1 ✓ so `v` is a value too: same constructor), `T ⇓ w` value, and `MATCH_{n+1}(v′,w)` for every `n`, i.e. `MATCH` at **every** index. Goal: `MATCH_{k−j}(v,w)`. `w=Top`: ✓. `w=λx≤a.b`: `v′=λx≤α′.β′` with `α′ =β a`; `v=λx≤α.β`, `α =β α′ =β a` ✓; for `j′ < k−j ≤ k` (strict since `j ≥ 0`... if `j = 0` then `j′ < k` still strict ✓) and `c ∈ ⟨a⟩ⱼ′`: we have `[c]β′ ∈ ⟦[c]b⟧_at-every-index (from `MATCH_∀`), and `[c]β =β [c]β′`; by IH at `j′ < k`: `[c]β ∈ ⟦[c]b⟧ⱼ′`. ∎

The asymmetry between 4.4 (fixed index) and 4.5 (∀-index) is principled: the type side is unbudgeted, the member side counts steps, and conversion changes step counts. Every use of 4.5 below has ∀-index facts available, because semantic judgements are ∀-quantified.

## 5. Transitivity

This is the heart — the semantic counterpart of transitivity elimination — and it is here that the design earns its keep. The statement composes *memberships*, and the proof needs no measure on derivations, no strong normalization, no commutation of reductions: the middle term's evaluation cost is absorbed by instantiating a ∀-quantified hypothesis, and the recursion descends through `MATCH`'s depth tiers, which are structurally decreasing.

**Theorem 5.1 (membership transitivity).**
(MT) If `x ∈ ⟦y⟧ₖ` and `y ∈ ⟦z⟧ₖ′` **for all** `k′`, then `x ∈ ⟦z⟧ₖ`.
(MC) If `MATCHₘ(vₓ, v_y)` and `MATCH_{m′}(v_y, v_z)` for all `m′`, then `MATCHₘ(vₓ, v_z)`.

*Proof.* By strong induction on the index, ordering at each `n`: MC(n) before MT(n); MC(n) may use MT(j) for `j<n`; MT(n) may use MC(m) for `m ≤ n`.

(MT at `k`.) Let `x ⇓ʲ vₓ`, `j<k`. From `x ∈ ⟦y⟧ₖ`: `vₓ` value, `y ⇓ⁱ v_y` value, `MATCH_{k−j}(vₓ, v_y)`. Here `i` is arbitrary — and harmless: instantiate the second hypothesis at `k′ = i+1+n` for each `n`: since `y ⇓ⁱ v_y` with `i < k′`, we get `z ⇓ v_z` value and `MATCH_{n+1}(v_y, v_z)` for every `n` — `MATCH` at every index. By MC at `k−j ≤ k`: `MATCH_{k−j}(vₓ, v_z)`. The conjuncts (m1),(m2),(m3) for `x ∈ ⟦z⟧ₖ` are assembled. ✓

(MC at `m`.) If `v_z = Top`: trivial. If `v_z = λx≤a₃.b₃`: from `MATCH_∀(v_y,v_z)`, `v_y = λx≤a₂.b₂` with `a₂ =β a₃`; from `MATCHₘ(vₓ,v_y)`, `vₓ = λx≤a₁.b₁`-shaped member, `a₁ =β a₂ =β a₃` ✓. Tiers: fix `j′ < m`, `c ∈ ⟨a₃⟩ⱼ′ = ⟨a₂⟩ⱼ′` (4.4). First hypothesis gives `[c]b₁ ∈ ⟦[c]b₂⟧ⱼ′`. Second gives `[c]b₂ ∈ ⟦[c]b₃⟧ⱼ″` **for all** `j″` (its tiers are available at every index). By MT at `j′ < m`: `[c]b₁ ∈ ⟦[c]b₃⟧ⱼ′`. ✓ ∎

Note where the two classical obstructions died. The *middle-term budget* (which killed every binary-simulation variant of this proof, and which is the semantic shadow of the paper's failed decreasing-diagram measure — §6.6.3's "reductions absorbed into the subtype premise alter its depth") is dissolved because the middle `y` occurs once as a *type* (unbudgeted) and once as a *member of a ∀-quantified fact* (instantiable above its own cost). The *negative occurrence* of the relation (bounded argument quantification, the paper's bounded quantification itself) is confined to `⟨a⟩ⱼ` at strictly smaller depth, so the definition is well-founded without any normalization assumption.

## 6. The fundamental theorem

**Lemma 6.1 (the ≡-fragment is conversion).** If `Γ ⊢ t ≡wf u` then `t =β u`. *(Induction: every ≡-rule — DS-EAPP, the ≡-instances of DS-FUN/DS-APP/DS-TRANS, DS-SYM, DS-VAR, DS-TOP — is valid for `=β`; DS-EQ produces only `≤`, and no rule produces `≡` from `≤`, so ≡-derivations contain only these.)*

**Theorem 6.2 (fundamental theorem).** For the instrumented system:
1. `Γ ⊢ t wf ⟹ Γ ⊨ t wf`;
2. `Γ ⊢ t ≤wf u ⟹ Γ ⊨ t ≤ u`;
3. `Γ ⊢ t ≡wf u ⟹ Γ ⊨ t ≡ u`.

*Proof.* Mutual induction on derivations. Fix `k` and `γ ∈ ⟦Γ⟧ₖ` per case; all premise judgements may be instantiated at any index `≤ k` (Lemma 4.1) with the same `γ`, and at ∀-index when needed via the ∀ in Definition 3.2 — the case analyses below only ever need indices `≤ k` for graded facts and ∀-index for member-conversion/transitivity, both available.

**(W-VAR)** `γx ∈ ⟦γx⟧ₖ` is half of the `⟨·⟩ₖ` condition in `γ ∈ ⟦Γ⟧ₖ`. **(W-TOP, DS-TOP)** `Top ⇓⁰ Top`, `MATCH(Top,Top)` ✓.

**(W-FUN)** Goal `Λ ∈ ⟦Λ⟧ₖ`, `Λ ≜ λx≤γa.γb`. `Λ ⇓⁰ Λ`, a value; (m3) at `m=k`: bound `γa =β γa` ✓; tier `j<k`, `c ∈ ⟨γa⟩ⱼ`: then `γ[x↦c] ∈ ⟦Γ, x≤a⟧ⱼ` (ambient components by 4.1; the new one is literally the tier's domain condition), so IH(1) of the premise `Γ,x≤a ⊢ b wf` at index `j` gives `[c]γb ∈ ⟦[c]γb⟧ⱼ`. ✓

**(DS-FUN, ≤-form)** Premises `Γ ⊢ t ≡wf t′` (so `γt =β γt′` by 6.1) and `Γ, x≤t ⊢ u ≤wf u′`. Goal: `λx≤γt.γu ∈ ⟦λx≤γt′.γu′⟧ₖ`. Both sides `⇓⁰`; member is a λ ✓; bound: `γt =β γt′` ✓. Tier `j<k`, `c ∈ ⟨γt′⟩ⱼ = ⟨γt⟩ⱼ` (4.4): `γ[x↦c] ∈ ⟦Γ,x≤t⟧ⱼ`, and IH(2) at `j` gives `[c]γu ∈ ⟦[c]γu′⟧ⱼ`. ✓ (The ≡-form of the rule needs only 6.1 and the wf parts.)

**(DS-EVAR)** Goal `γx ∈ ⟦γ(Γ(x))⟧ₖ`: the other half of the `⟨·⟩ₖ` condition. ✓

**(DS-ETOP)** Goal `γt ∈ ⟦Top⟧ₖ`: if `γt ⇓ v` then `v` is a value by the instrumented wf premise (IH(1): `γt ∈ ⟦γt⟧ₖ` gives (m1)); `Top ⇓ Top`; `MATCH(v,Top)` ✓.

**(DS-EQ)** From IH(3): `t =β u`, and IH(1) gives `γt ∈ ⟦γt⟧ₖ`; `⟦γt⟧ₖ = ⟦γu⟧ₖ` by 4.4 (with `γt =β γu` by substitutivity). ✓ **(DS-SYM)** symmetric in `=β` and wf ✓. **(DS-EAPP)** `(λx≤γt.γu)(γs) =β [x↦γs]γu` is one β-step; both wf premises are instrumented; conclusion is an ≡-judgement ✓.

**(DS-TRANS, ≤-form)** IH gives `Γ ⊨ s ≤ t` and `Γ ⊨ t ≤ u`. Then `γs ∈ ⟦γt⟧ₖ` and `γt ∈ ⟦γu⟧ₖ′` for **all** `k′`; Theorem 5.1 (MT) yields `γs ∈ ⟦γu⟧ₖ`. ✓ — This is the entire cost of DS-TRANS.

**(W-APP)** Premises (via W-SUB): `Γ ⊢ t ≤wf λx≤s.Top`, `Γ ⊢ u ≤wf s`, with wf of `t, u, λx≤s.Top`. Write `T ≜ γt, U ≜ γu, S ≜ γs`. Goal: `T(U) ∈ ⟦T(U)⟧ₖ`. Suppose `T(U) ⇓ʲ v`, `j<k`. The head evaluation factors: `T ⇓^{j₁} w_T` (else `T(U)⇑`), and:
- `w_T` is a value: IH(1) `T ∈ ⟦T⟧_{j₁+1}` (∀-index, instantiate above `j₁`) gives (m1).
- `w_T ≠ Top` and `w_T` is a λ with the right bound: IH(2) gives `T ∈ ⟦λx≤S.Top⟧_{j₁+1}`, whose (m3) forces `w_T = λx≤A.B` with `A =β S`. *(Were `w_T = Top`, the member side of (m3) would fail — this is the progress-critical step.)*
- So `T(U) ↦^{j₁} (λx≤A.B)(U) ↦ [x↦U]B ⇓^{j₂} v` with `j = j₁+1+j₂`.
- `U` is a good argument at every depth: `U ∈ ⟦S⟧ⱼ′ = ⟦A⟧ⱼ′` (IH(2) for `u ≤ s` at every index; 4.4) and `U ∈ ⟦U⟧ⱼ′` (IH(1)); so `U ∈ ⟨A⟩ⱼ′` for all `j′`.
- Self-description of the body: IH(1) `T ∈ ⟦T⟧_{j₁+1+m}` for every `m` gives `MATCH_{m+1}(w_T, w_T)` for every `m`; its tier at `j′ ≔ k−j₁−1` with argument `U`: `[x↦U]B ∈ ⟦[x↦U]B⟧_{k−j₁−1}`.
- Conclude: `[x↦U]B ⇓^{j₂} v` with `j₂ < k−j₁−1` (since `j<k`), so (m1) `v` is a value, and `MATCH_{(k−j₁−1)−j₂}(v, w′) = MATCH_{k−j}(v, v)` where the type side `[x↦U]B ⇓ v` as well. Finally the goal's type side: `⟦T(U)⟧ₖ = ⟦[x↦U]B⟧ₖ` by 4.3 (iterated), and its value is `v` — value ✓ (m2), `MATCH_{k−j}(v,v)` ✓ (m3). ✓

Note the exactness: the member's `j₁+1` consumed steps pay precisely for the tier descent `j′ = k−j₁−1`; nothing erodes.

**(DS-APP, ≤-form)** Premises: `Γ ⊢ t ≤wf t′`, `Γ ⊢ u ≡wf u′` (so `γu =β γu′`), plus instrumented `Γ ⊢ t(u) wf` and `Γ ⊢ t′(u′) wf` with their W-APP sub-derivations (bounds `s`, `s′`). Goal: `T(U) ∈ ⟦T′(U′)⟧ₖ`, primes denoting `γt′, γu′`. Suppose `T(U) ⇓ʲ v`, `j = j₁+1+j₂` as above, `w_T = λx≤A.B` (same reasoning from `t`'s own instrumentation). On the type side: `T′ ⇓ w_{T′} = λx≤A′.B′` with `A′ =β S′` (from `t′`'s instrumentation: `T′ ∈ ⟦T′⟧` forces a value, `T′ ∈ ⟦λx≤S′.Top⟧` forces a λ — for the **type-side** convergence note `T ∈ ⟦T′⟧_{j₁+1}` (IH(2)) makes `T′ ⇓` because `T ⇓`).
- From IH(2) at every index: `MATCH_∀(w_T, w_{T′})`, so `A =β A′` and, at every tier with `c ≔ U`: we need `U ∈ ⟨A′⟩ⱼ′` — indeed `U′ ∈ ⟦S′⟧_∀` (primed instrumentation) and `U =β U′` give `U ∈ ⟦S′⟧_∀ = ⟦A′⟧_∀` by **member conversion (4.5)** (∀-index available ✓), and `U ∈ ⟦U⟧_∀ ✓`. Hence `[x↦U]B ∈ ⟦[x↦U]B′⟧ⱼ′` **for every** `j′`.
- Type conversion: `[x↦U]B′ =β [x↦U′]B′`, so by 4.4 `⟦[x↦U]B′⟧ = ⟦[x↦U′]B′⟧` at every index; and `⟦T′(U′)⟧ₖ = ⟦[x↦U′]B′⟧ₖ` by 4.3. So `[x↦U]B ∈ ⟦T′(U′)⟧_{j′}` for every `j′`.
- Step shift (4.2, iterated `j₁+1` times): `T(U) ∈ ⟦T′(U′)⟧ₖ` follows from `[x↦U]B ∈ ⟦T′(U′)⟧_{k−j₁−1}`. ✓
(The ≡-form is 6.1 plus the wf parts.) **(W-SUB, W-GAM*)** bookkeeping. ∎

## 7. Safety and the recovered lemmas

**Theorem 7.1 (type safety — "well-formed terms don't go wrong").** If `∅ ⊢ t wf` then every `s` with `t ⟶* s` is a value or has a reduct.

*Proof.* Suppose not: some reachable `s` is normal and not a value, hence (Fact 1.1) a spine `Top(d⃗)`. By Lemma 2.2, `t ⇓ Top(e⃗)`, a non-value weak-head normal form. But Theorem 6.2 gives `t ∈ ⟦t⟧ₖ` for all `k` (the empty substitution is in `⟦∅⟧ₖ` trivially — closedness is where the instrumented context machinery bottoms out harmlessly), and (m1) at any `k` exceeding the evaluation length says `t`'s weak-head normal form is a value. Contradiction. ∎

**Corollary 7.2 (progress).** `∅ ⊢ t wf ⟹ t` is a value or reduces. **(Preservation of safety)** is built in: the property quantifies over all reducts, so it is closed under `⟶` by construction — the model-theoretic statement does the work Theorem 5.6 was for, without needing syntactic preservation of derivations.

**Corollary 7.3 (semantic inversion — Lemma 5.2's content).** If `∅ ⊢ (λx≤a.b) ≤wf (λx≤a′.b′)` then `a =β a′`, and moreover for every depth `j` and every `c ∈ ⟨a′⟩ⱼ`, `[x↦c]b ∈ ⟦[x↦c]b′⟧ⱼ`. *(Both sides `⇓⁰`; unfold 6.2's conclusion.)* In particular the argument-compatibility fact needed in the redex case holds: if also `∅ ⊢ c ≤wf a′` then `c`'s memberships transfer to `a` by 4.4 — exactly what the substitution step of the paper's Theorem 5.6 proof needed from `a ≡ a′`.

**Corollary 7.4 (Top is not a function).** `∅ ⊢ Top ≤wf λx≤s.Top` is underivable: it would give `Top ∈ ⟦λx≤s.Top⟧₁`, whose clause (m3) requires the member's value to be a λ. *(Likewise any `t ≤wf λx≤s.Top` with `t ⇓ Top` is refuted — the model proves non-derivability statements wholesale.)*

Sanity checks against the paper's examples: `3 ≤ Nat` (§3.5) is untouched — Church `3` and `Nat` weak-head evaluate to λs with `=β`-equal bounds at every level, and the body memberships unfold along the encodings; the derivation given in the paper maps onto the FT cases used. Girard-paradox terms (Theorem 4.4) are welcome: a wf looping term is in every `⟦·⟧ₖ` it needs to be in, vacuously where it diverges — at no point did any lemma assume termination of anything.

## 8. Discussion: what is and is not resolved

**What this proves.** Type safety for λ⊴ — the conjunction the paper extracts from Theorems 5.5/5.6 — holds *unconditionally* for the §3.4 (instrumented) reading of the declarative system, with no appeal to Conjecture 5.1. The two load-bearing consequences of transitivity elimination (inversion; Top-not-a-function) are theorems of the model. DS-TRANS is interpreted by Theorem 5.1, whose proof is the announced replacement of the missing induction principle: where §6.7 could not reconcile induction on simultaneous reductions with induction on derivation depth, the model splits the measure differently — *member steps and λ-depth on one side (a single well-founded index), type-side evaluation cost on no side at all* (absorbed by ∀-instantiation). That asymmetry — budget the left, quantify the right — is unavailable to a rewriting-style proof, which must treat both sides of `≤⟶`/`≡⟶` symmetrically as reductions; it is, I believe, the precise reason the ARS route walls where this one doesn't.

**What this does not prove.** (1) **Syntactic transitivity elimination** (Conjecture 5.1) — that every `≤wf` derivation can be *rewritten* to end in DS-FUN/DS-ETOP — remains open as a proof-theoretic statement, as does (2) **Conjecture 6.2** (commutativity of `≡⟶` with `≤⟶`), and with it the completeness/decidability-style analysis of the algorithmic system of Figure 2. The model yields the *consequences* of transitivity elimination that safety needs, not the normalization-of-derivations fact itself. My honest reading: 5.1 and 6.2 are best reattempted, if at all, with this model in hand — e.g., algorithmic completeness would now be provable by showing the algorithmic relation is also sound and that the model is the common semantics — but nothing in type safety waits on them anymore. (3) The result is for the instrumented relation. The uninstrumented Figure-1 relation over ill-formed terms (the thing SRE-TOPAPP exists to repair) may relate junk like `Top(t)`; since W-APP only ever consumes `≤wf`, safety of well-formed programs is indifferent to this. (4) Universes (§3.6) are orthogonal here exactly as in the paper: tags pass through every definition untouched.

**Why the bound-invariance mattered.** The collapse of the ≡-fragment to `=β` (Lemma 6.1) is what let bounds be compared by raw conversion inside the model, discharged by Church–Rosser for plain β. Had λ⊴ adopted *contravariant* bounds (§3.3), the clause for `MATCH` would need a negatively-occurring graded membership for bounds, and while the same index discipline appears to accommodate it, the ≡-collapse — and with it the pleasant confinement of all rewriting theory to standard λ-calculus — would be lost. The paper's design choice to keep bounds invariant is, on this analysis, exactly what makes its metatheory tractable semantically even though it remains hard syntactically.

**Relation to the paper's diagnosis (§9).** The three fatal ingredients — bounded quantification over type operators, point-wise subtyping, non-normalizing types — are all present here, and the model handles them by, respectively: depth-graded good-argument sets `⟨a⟩ⱼ`; membership-as-subtyping (point-wise subtyping is just (m3)'s tier clause); and partial-correctness-style clauses that never demand convergence. So I'd sharpen the paper's conclusion: those three ingredients doom the *rewriting-theoretic* program (transitivity elimination as derivation surgery), but not type safety itself, which survives by changing the question from "can derivations be normalized?" to "do derivations have a sound model that validates inversion?".

---

**Summary.** Take the §3.4 instrumented declarative system; interpret every closed term `T` as the graded set `⟦T⟧ₖ` of Definition 3.1 (members' weak-head steps and λ-depth consume `k`; bounds compared by `=β`; the type side unbudgeted); interpret `t ≤ u` as membership, wf as self-membership, ≡ as conversion. Church–Rosser and shape standardization for plain β give the conversion lemmas; membership transitivity (Theorem 5.1) interprets DS-TRANS with no normalization assumption; the fundamental theorem (6.2) is a per-rule induction whose application cases fit exactly by step/depth accounting; adequacy (7.1–7.4) then delivers progress, preservation-of-safety, semantic inversion, and `Top ≰ λ` — type safety for System λ⊴, with transitivity elimination retired from the critical path and left, explicitly, as the still-open proof-theoretic question it always was.
