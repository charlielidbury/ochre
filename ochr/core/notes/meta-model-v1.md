# meta-model v1: RULES v1/v1.1 in the model, the metatheory section, and a Lean work plan

## 5-line summary

1. **Verdict:** v1 closes the five round-1 findings in the model (C1 at function types, C2, C3's entry-value guard, C4, C5), and it makes the metatheory *simpler*. With loans as variables and [End] as plain substitution, T1(a) is just commutation of substitutions, and T5 holds on the nose (equal environments up to renaming of loans), not merely "up to resolution" as in v0. v1 as issued was unsound in two places, both exploiting P5. v1.1, which landed mid-round, fixes R2. **R1 is still open in v1.1.** A third hole (R4) opens under one reading of the stuck-block rule. *Superseded: false as stated, see lean-meta F3 and paper meta.typ Theorem 7.*
2. **Most important finding:** (R1) P5 is keyed on *calls*, while D15 and the observation rule turn a stuck Prop-typed *block* into a call. So a Prop-typed match that writes has no effect while its scrutinee is abstract, and its full effect once the scrutinee is refined. That is a failure of naturality, and it gives a closed proof of `Eq Nat (S Z) Z` (§1.1). (R2) [Rec] constrains recursive *calls* only, so `fix f (n) := Apply(f, n)` passes. Because P5 means Prop-valued calls are never run, the checker now accepts `Boom(Z) : Eq Nat Z (S Z)` without diverging. This is breaker-close A4, which P5 turns from a divergence into a closed proof; v1.1's escape clause fixes it (§1.2). R1 was found independently by breaker-close-v1 (N1) and deriver-e346-v1 (N12). (R4) Closing off a stuck match on a *sealed program*, whose arms [Split] never checked, has no model; it gives deriver-e346-v1's `Knot3` (§1.4).
3. **RULES must change (v1.1):**
   - P5 becomes "a *term* whose type is a proposition, argument evaluation included, runs on a private copy". Merged with P2 this is one rule: whatever the runtime erases (types and proofs), the machine runs on a private copy.
   - P2 must get back v0's "on a private copy", or a type that writes breaks adequacy (§1.3).
   - The stuck-block rule must be lambda lifting done right: capture modes at least as strong as any arm's use, a stated codomain, and only for arms already checked; a match on a non-σ neutral generalises first.
   - A call with a neutral head is stuck at once.
   - `J` carries its endpoints.
   - [Call-type] evaluates at the call point.
4. **Confidence:** high for R1 and R2 (the derivations use only v1's text, and two other agents reproduced both independently). High for the validations of [End], [Access], the [Close] table, [Seal]'s guard, D16 and D18. Medium-high for the on-the-nose form of T5: I checked it by hand on `TailM`, `Pick` and a partially refined `TailM`, but did not prove it. §2 states what I believe is provable, and argues the hardest case of each theorem.
5. **Not checked:** E1–E4 re-derived under v1 (that is the derivers' job); completeness of D15 (I checked only its soundness and naturality); the dependent layer beyond its key cases; nothing is mechanised yet (§3 is the plan).

**Correction to my round-1 report.** meta-model.md §3.1 recommended fix (d) as "a call whose result type is a proposition runs on a private copy". Phrased for calls, it has exactly R1's flaw. The correct fix is term-keyed (§1.1). v1's P5 inherited my wording.

## 0. How to read this

§1 checks every rule that is new in v1 against the model of meta-model.md (§1 there), and gives the rules the model rejects (R1–R4; R2 is already fixed in v1.1), each with a bad derivation and a minimal fix. §2 is the metatheory section in paper form (prose and mathematics, self-contained), with T0–T5 restated for v1.1. §3 is a work plan for one Lean 4.33 agent.

Notation as in v1. v1 has no `⊥` in its syntax, so "a closed proof of false" below means a closed inhabitant of `Eq Nat Z (S Z)`, or equivalently of `Π(P : Prop). P` (from one you get the other with `J` and a large-elimination motive).

## 1. The new rules in the model

### 1.0 Verdicts

| v1 rule (decision) | Verdict | Where |
|---|---|---|
| [End] without side condition, loans as variables (D11) | **validated**; [End] *is* the model's substitution `h_ℓ := ⟦v⟧`, and End steps commute given acyclicity | §1.4, T1 |
| [Access] ends loans on the path and inside the content (D19) | **validated**; provides W4 (loan-free arguments), which T2 needs | §1.4 |
| [Close] port table (D11) | **validated** (three rows); implicit gap: a neutral head (`σ_f(…)`, `⌈t⌉(…)`) must be stuck at once | §1.4 |
| [Seal] head-call guard (D9) | **validated** and natural; it is what makes T5 hold on the nose. *Superseded: false as stated, see lean-meta F3 and paper meta.typ Theorem 7.* | §1.4, T5 |
| stuck non-tail matches closed off (D15) | **natural**, being [Close] of a definable anonymous function, **except** Prop-typed blocks under call-keyed P5 (R1) | §1.1, §1.4 |
| [Def] at the generic call + [Call-type] (D12, D13) | **validated**, given owner sets and the injective subset for abstract returned-borrow functions | §1.4, T2c |
| P5, proofs not run (D14) | avoids C1 cleanly **at function types**: a Prop-valued Π over borrows is a CIC `Prop`. But call-keyed P5 is **not natural** (R1) | §1.1 |
| trimmed Eq rules, `refl : ⊤` (D16) | **validated** (`propext` instances) | §1.4 |
| owner sets (D18) | **validated**: exactly the hypothesis of Lemma Inj | T2c |
| [Rec] on entry values (D17) | v1: **incomplete** (R2: `f` may escape). **v1.1: validated** (escape clause); say explicitly that it applies to calls of `f` inside nested functions and block arms | §1.2 |
| stuck-block close-off as lambda lifting (D15, the details) | natural **only if** capture modes are at least as strong as any arm's use, the codomain is stated, and the arms were checked; closing off unchecked arms (a match on a sealed program) is unsound (R4) | §1.4 |
| `J(A, P, h, t)`, [Call-type] "at Ω" | the model needs `J`'s endpoints (normal forms erase them) and the call point (after the arguments) | §1.4 |
| P2 wording ("evaluated … against the current environment") | **adequacy gap**: v0's "private copy" was lost (R3) | §1.3 |

### 1.1 R1: P5 is keyed on calls, but stuck blocks become calls (new; soundness)

A stuck Prop-typed block is closed off as a call to an anonymous function whose result type is a proposition. P5 then declines to run that call, so the block's writes vanish. Once the scrutinee is refined, the same block is no longer stuck, is not a call, and runs with its writes. The normaliser is therefore not natural (T5 fails), and [Call-type] can see the two behaviours at once.

```
Q : Π(b : Nat) (a : Nat). Id ⊤ (match b { Z => (a := S Z; refl) | S _ => (a := S Z; refl) }) refl
Q := fix Q (b : Nat) (a : Nat) : Id ⊤ (match b {…}) refl := refl
```

```
ε ⊢ Q : …                                                                      // [Def], generic call Q(σ_b, σ_a)
  goal = [Call-type] of Q(σ_b, σ_a):  W = {a}  (a is on the left of :=)
    obs(match b {…}): on a copy, match on σ_b is stuck, so it is closed off as a block:   // §3 "Stuck blocks"
      g(a' : &Nat, b' : Nat) : ⊤, called as g(&a, σ_b)                          // a written ⇒ borrow argument; b read ⇒ value argument
      [Close], row "borrow-free D": loan of a := ⌈let c = σ_a; g(&c, σ_b); c⌉
      nf of that fill: the head call g is a call at a proposition: P5, not run; &c ends unchanged; c = σ_a
      obs = (refl, σ_a)
    obs(refl) = (refl, σ_a)
    Id ≡ Eq (⊤ × Nat) (refl, σ_a) (refl, σ_a) ≡ ⊤                               // Eq A a b ≡ ⊤ when a ≡ b
  body refl : ⊤ ✓
ε ⊢ Q(Z, Z) : Eq Nat (S Z) Z                                                   // [Call-type]; P5: Q(Z, Z) is not run
  B with b := Z, a := Z: obs(match Z {…}) runs the Z arm (not stuck, not a call): a := S Z;  obs = (refl, S Z)
  obs(refl) = (refl, Z)
  Id ≡ Eq ⊤ refl refl ∧ Eq Nat (S Z) Z ≡ ⊤ ∧ Eq Nat (S Z) Z ≡ Eq Nat (S Z) Z
ε ⊢ J(Nat, λn. match n { Z => Π(P : Prop). P | S _ => ⊤ }, Q(Z, Z), refl) : Π(P : Prop). P    // closed proof of false
```

The same happens in a checked program: a non-tail Prop-typed block that writes (`(match b {Z => (*x := S Z; refl) | S _ => …}); rest`) is closed off, and P5 cancels the write in the continuation, but a concrete run performs it. And even without blocks, v1's P5 lets the *arguments* of a Prop-valued call have lasting effects (`P((a := S Z; &a))` writes `a`) while the runtime erases the whole call.

**In the model**, P5 is only sound if every Prop-typed computation acts as the identity on state: `⟦t⟧ = λs. (•, s)` for `t : P`, `P : Prop`. The machine must agree for every Prop-typed term, not just for calls; otherwise the square `nf(nf(t)·α) = nf(t·α)` fails, as `Q` shows.

**Minimal fix:** *P5: a term whose type is a proposition runs on a private copy of Ω. Nothing it does, argument evaluation included, persists, and the runtime erases it.* Stuck Prop-typed blocks then need no close-off (they are not run for effect), and the observation of a Prop-typed `t` leaves its owners unchanged. With P2 fixed as in §1.3 this becomes one principle: **what the runtime erases, the machine runs hypothetically.**

Two other agents found R1 independently and proposed repairs; the model accepts any repair under which checker, runtime and naturality agree:
- (i) *Term-keyed private copy* (above; deriver-e346-v1 recommends the same). In the model, `⟦t⟧ = λs. (•, s)` holds by definition.
- (ii) *A static restriction* (breaker-close-v1): a Prop-typed term may not write, borrow or move a place from outside itself, except as an argument to a Prop-valued call. Skipping and running then coincide, so P5 becomes a theorem, and `⟦t⟧ = λs. (•, s)` is a lemma rather than a definition.
- (iii) *Erase the body but keep the arguments at runtime* (deriver-e1-v1 G2). This addresses only the arguments of calls, and must be combined with (i) or (ii) for blocks.

I recommend (i): it is one sentence, needs no new check, and merges with P2. (ii) rejects more programs, but no write ever silently vanishes, which may read better to a programmer.

### 1.2 R2: [Rec] lets `f` escape, and P5 removes the divergence that hid it (breaker-close A4; soundness; fixed in v1.1)

[Rec] constrains the *recursive calls* in the body of `fix f`. It says nothing about occurrences of `f` that are not calls, such as passing `f` to another function or binding it to a variable. In v0 such a definition was caught, by accident, by divergence: the checker ran the call and never returned. Under P5 a call whose result type is a proposition is not run, so nothing diverges and the definition is accepted.

```
Apply : Π(g : Π(n : Nat). Eq Nat Z (S Z)) (n : Nat). Eq Nat Z (S Z)
Apply := fix Apply (g, n) : Eq Nat Z (S Z) := g(n)
Boom  : Π(n : Nat). Eq Nat Z (S Z)
Boom  := fix f (n : Nat) : Eq Nat Z (S Z) := Apply(f, n)
```

```
ε ⊢ Apply : …            // [Def] at Apply(σ_g, σ_n): body g(n) has [Call-type] Eq Nat Z (S Z); P5, not run
ε ⊢ Boom : …             // [Def] at f(σ_n): body Apply(f, n); f : Π(n : Nat). Eq Nat Z (S Z) ✓, n : Nat ✓
                         // [Call-type] Eq Nat Z (S Z) = goal ✓; P5: not run; [Rec]: the body has no recursive call ✓
ε ⊢ Boom(Z) : Eq Nat Z (S Z)                                   // [Call-type]; P5: not run. Closed, and the checker terminates.
```

`let g = f; g(n)` does the same with no helper at all. **In the model**, `⟦fix f …⟧` is a well-founded recursor, and inside its body `f` exists only as the induction hypothesis at arguments strictly below the entry value; an unapplied `f` has no meaning. **Minimal fix:** *[Rec]: in the body of `fix f`, `f` occurs only as the head of a saturated call whose recursive argument is a strict subterm of the entry value.* This is CIC's guard condition. Note the general lesson of P5: once proofs are not run, the logical guards (recursion, and anything else that used to be backed by divergence) are the *only* barrier, and must be exact.

### 1.3 R3: types must run on a private copy (adequacy, not consistency)

v0's P2 said a term inside a type "is run hypothetically, on a private copy of the current environment". v1's P2 says a type "is evaluated once, when it is formed, against the current environment", and only `Id`'s two sides are guaranteed private copies (P6). A type that is not an `Id` can then write:

```
H : Π(x : Nat). Nat
H(x) := let T = Eq Nat (x := Z; x) Z; x          // forming T writes x in H's frame
```

The checker computes `H(σ) ⇓ Z`, so it proves `Π(x : Nat). Id Nat (H(x)) Z` by `refl`, while the compiled `H`, whose types are erased, is the identity. This does not break consistency (the checker is self-consistent and natural), but it breaks the end goal that proofs are about the compiled program. **Fix:** restore the private copy for type formation. With R1's fix this is the single rule: *a term that the runtime erases (a type or a proof) is run on a private copy.* In the model: `⟦t⟧ = λs. (⟦value⟧, s)` whenever `t`'s type is a sort or a proposition.

### 1.4 The rules the model validates, and what each costs or buys

- **[End] without side condition (D11).** In the model a loan was already a variable `h_ℓ` and ending was already a substitution. v1 now makes the syntax say so. Consequences: (i) two [End] steps commute as substitutions whenever "`loan_ℓ` occurs in the content of `borrow_m`" is acyclic, which every reachable environment satisfies (a loan enters a borrow's content only by reborrowing a sub-place of that content, and reading never copies a loan, by [Access]); so T1(a) needs no enabling condition. (ii) Pending anonymous bindings disappear: at [Pop], a parameter borrow whose content holds the returned borrow's loan simply ends, and the loan travels into the caller's owner. The concrete machine and the refined symbolic machine then end in *the same shape*, which is why T5 now holds on the nose (§2.5). *Superseded: false as stated, see lean-meta F3 and paper meta.typ Theorem 7.*
- **[Access] (D19).** Supplies invariant W4: every value that is read, moved, borrowed or passed is loan-free. T2's locality and [Close]'s claim that `L = let cᵢ = uᵢ` is closed both need it. Eager ending on value arguments of a closed-off block can make the checker end a borrow that a concrete run of the chosen arm would not have ended. That changes *definedness* only (a later use of that borrow errors), never a value (T1), so it costs completeness, not soundness.
- **[Close] port table.** Each row is the model's call clause: `()` / `⌈L; C⌉` / `borrow_k ⌈L; let r = C; *r⌉` denote the forward result, `⌈L; C; cᵢ⌉` denotes `f_backᵢ ū w̄`, and `⌈L; let r = C; *r := loan_k; cᵢ⌉` denotes `f_backᵢ ū w̄ h_k`, by δβζ only. The Unit row is η on `Unit`. There is no Prop row, correctly: with P5, Prop-typed computations never reach [Close]. One implicit gap: [Call] is stated for `f = fix …`; a call whose head is a neutral (`σ_f`, or a sealed program of function type) must be declared stuck at once, so that [Close] applies.
- **[Seal]'s head-call guard (D9).** The head call unfolds and is not re-closed; inner calls may close. This is exactly what makes re-normalisation after a refinement do the same work as running the refined program directly (T5's [Close] case). It is also CIC's fixpoint guard, as D9 says.
- **D15, stuck non-tail matches closed off.** A stuck block `m` with free places `p̄` becomes a call `g(ā)` to the anonymous definable function `g(x̄) := m[p̄ ↦ x̄]`, so it is natural because [Close] is (T5), the model denotes the fills by `g`'s backward functions (a `natCase` on the scrutinee, precisely), and BackInj covers `g` (for `AddToOne`'s block, `back = natCase σ_b (λw. (w, σ₂)) (λw. (σ₁, w))`, jointly injective). The two exceptions are R1 (fixed by term-keyed P5) and the eager-[Access] incompleteness above. Compared with [Join]: no generalisation, no information loss, no non-natural rule left anywhere in v1. The argument, though, is that the closed-off call *is* the block, and that holds only if the one-line rule is real lambda lifting.
  - **Capture modes.** The lifted call must be at least as strong as every arm's use of each free place: move a borrow variable if some arm moves or assigns it, reborrow if some arm writes or borrows through it, copy otherwise (deriver-e346-v1 N2 and breaker-close-v1 N2–N4, found independently). The model is indifferent to over-strong capture, which only adds errors (T5 is one-directional: symbolic success implies refined success). It forbids under-strong capture: reborrowing a borrow that one arm moves lets the symbolic run succeed where a refined run reads a moved place, which fails T5 and adequacy.
  - **Codomain.** The lifted function's codomain must be stated, because P5 and [Close]'s table both read it (breaker-close-v1 N5).
  - **R4: the arms must have been checked.** T3's non-tail [Split] case builds `⟦g⟧` from the arms' typing derivations; an unchecked arm has none. v1.1's [Split] is defined only for an abstract `σ`, so a non-tail match on a *sealed program* (after an opaque call, say) is "a stuck match that is not the body of a call" with unchecked arms. Closing it off skips [Rec] and the borrow checker inside them, and deriver-e346-v1's `Knot3` is then a closed proof of `Eq Nat Z (S Z)`. **Fix:** a checked program that matches on a neutral other than an abstract value first generalises it (fresh `σ` in Ω, the goal and the stored types) and then [Split]s. The model validates this (dependent elimination on a generalised variable; completeness is lost, soundness is not); it is my round-1 §3.5 recommendation, now load-bearing.
- **[Def] at the generic call and [Call-type] (D12, D13).** The generic call environment `{cᵢ ↦ σᵢ}` with arguments `&cᵢ` is, in the model, the entry environment `E(d̄)` of meta-model §1.3 with the owners `cᵢ` in place of v0's ghosts; the goal is `⟦B⟧(d̄)` by definition. [Call-type] at a real call site is T2c: the caller's `Id` observations are the generic ones under the owners' resolution contexts, which are jointly injective by Lemma Inj (needs D18) and BackInj (needs the injective subset for *abstract* returned-borrow functions: v1 still proves meta-model's `Q`, so the model still needs the subset). "`B` evaluated at Ω" must mean at the *call point*, after the arguments are evaluated (deriver-e1-v1 G1). The model's `⟦B⟧(ū)` is indexed by the argument contents, and before the arguments are evaluated their loans do not exist, so the footprint would be empty.
- **P5 and C1.** Under P5, `Out(d̄) = ⟦B⟧(d̄)` when `B : Prop`: a Prop-valued Π over borrows translates to the CIC `Prop` `Π(d̄ : D̄). ⟦B⟧(d̄)`, both `P₁` and `P₂` of C1 denote `λd. •`, and definitional proof irrelevance identifies things that are equal. So C1 is avoided cleanly *at function types*; R1 is the same phenomenon at the level of terms, and term-keyed P5 closes it.
- **D16 (`Eq` on pairs, `Eq A a b ≡ ⊤` when `a ≡ b`, ⊤ a unit for ∧, `refl : ⊤`).** Each is a `propext` instance: `((a, b) = (a', b')) = (a = a' ∧ b = b')`, `(a = a) = True`, `(True ∧ P) = P`; `refl` translates to `True.intro`, cast along `(a = a) = True` where needed. `Eq A a b ≡ ⊤ when a ≡ b` is natural: after a refinement makes `a ≡ b`, re-normalising the stored type yields `⊤`, as computing it afresh would. Dropping the `Nat` injectivity and `⊥` rules changes nothing in the model (they were `propext` instances too). One consequence to fix: since `Eq A a b` normalises to `⊤` when `a ≡ b`, a normal-form type no longer records `J`'s endpoints, and the translation of `J` to `Eq.rec` needs them. So write `J(A, a, b, P, h, t)` (deriver-e1-v1 G3).
- **D18 (owner sets).** Exactly the hypothesis of Lemma Inj: jointly, the owners' contexts are injective, because in each concrete run the returned borrow lands in exactly one parameter. C2's `Bad` is now rejected (`h : Π(e : ⊤ ∧ Eq Nat Z (S Z)). …` in the `S` arm, and `refl` does not inhabit the domain).

### 1.5 Summary of the model's demands on the rule set

Everything in v1.1 is validated once the following change:
- P5 and P2 merge into "what the runtime erases (types and proofs) the machine runs on a private copy" (R1, R3).
- [Call] adds "a call whose head is a neutral is stuck".
- The stuck-block rule is stated as lambda lifting (capture modes, codomain), applied only to checked arms, with a match on a non-σ neutral generalised first (R4).
- `J` carries its endpoints.
- [Call-type] is evaluated at the call point.

v1.1's [Rec] escape clause (R2) is already in. §2 assumes all of this.

## 2. Metatheory (paper text)

*This section is written to be adapted directly into the paper. It assumes RULES v1.1 with the amendments of §1.5.*

### 2.1 Setting

A *program* is a finite set of closed definitions `f := fix f (x̄ : Ā) : B := b`, each accepted by [Def] and [Rec]. Values, neutrals and environments are as in §2 of the rules; we write `abs(Ω)` for the abstract values occurring in `Ω` and `loans(Ω)` for the loan names occurring in it. An environment is **well formed** when:

- **(W1) unique holders.** Each loan name `ℓ` is held by at most one binding, as `borrow_ℓ v`.
- **(W2) bound loans.** Every occurrence of `loan_ℓ` either has its borrow `borrow_ℓ` held in `Ω`, or lies inside a sealed program. Outside sealed programs a loan occurs at most once; inside them it may occur several times ([Close] with two borrow arguments and a borrow result).
- **(W3) acyclicity.** The relation `ℓ ◁ m`, "`loan_ℓ` occurs in the content of `borrow_m`", is well founded.
- **(W4) clean crossings.** Every value that is read, moved, borrowed, or passed as an argument is loan-free.

**Lemma 0 (invariance).** Every step of the machine preserves (W1)–(W4). *Proof sketch.* (W4) is enforced by [Access]. (W3): a loan enters the content of a borrow only when a sub-place of that content is reborrowed, and by (W4) no read copies a loan, so no cycle can be created; [End] substitutes a content for its own loan's occurrences, which only shortens chains. (W1) and (W2) hold because loan names are fresh and [End] removes the borrow together with all occurrences of its loan.

**Lemma 1 (termination).** For a program accepted by [Rec], every run, concrete or symbolic, terminates in a value, an error, or a stuck state. *Proof sketch.* Types and proofs are run only hypothetically and are guarded like everything else. A Tait-style reducibility argument over the simple structure of the fragment (first-order data, n-ary functions, closures capturing borrow-free values) reduces termination to well-foundedness of recursion. That well-foundedness is exactly [Rec]: each recursive call's argument is a strict subterm of the entry value, and `f` has no other occurrence. For the first-order fragment (no function-typed values) a lexicographic measure on the multiset of entry values of active calls suffices.

### 2.2 The model

**Target.** Let CIC_L be the type theory of Lean 4 as axiomatised by Carneiro: universes `Prop : Type₀ : Type₁ : …`, an impredicative `Prop` with definitional proof irrelevance, inductive types, η for structures, and the axiom `propext`. ECIC_L adds equality reflection. Both have Carneiro's set-theoretic model, in which `Prop = {∅, {•}}`; this model validates `propext` (two propositions with the same truth value are the same set) and reflection (`⟦a = b⟧ ≠ ∅` implies `⟦a⟧ = ⟦b⟧`).

**Types.** Data and propositions translate homomorphically: `⟦Nat⟧ = ℕ`, `⟦Unit⟧ = Unit`, `⟦A × B⟧ = ⟦A⟧ × ⟦B⟧`, `⟦Prop⟧ = Prop`, `⟦Type_i⟧ = Type_i`, `⟦Eq A a b⟧ = (⟦a⟧ = ⟦b⟧)`, `⟦⊤⟧ = True`, `⟦P ∧ Q⟧ = ⟦P⟧ ∧ ⟦Q⟧`. A function type `Π(x₁ : A₁ … xₙ : Aₙ). B` with borrow positions `I = {i | Aᵢ = &Tᵢ}` translates to *forward and backward functions*:

```
Dᵢ = ⟦Tᵢ⟧ (i ∈ I),  Dⱼ = ⟦Aⱼ⟧ (j ∉ I)            Fin = ∏_{i ∈ I} ⟦Tᵢ⟧

Out_B(d̄) =  ⟦B⟧(d̄)                       if B is a proposition
            ⟦B⟧(d̄) × Fin                 if B is borrow-free and not a proposition
            ⟦T⟧ × (⟦T⟧ → Fin)            if B = &T

⟦Π(x̄ : Ā). B⟧  =  Π(d̄ : D̄). Out_B(d̄)               restricted, when B = &T, to  { F | ∀d̄. π₂(F d̄) injective }
```

`⟦B⟧(d̄)` is the translation of the normal form of `B` in the *generic call environment* `G(d̄) = {cᵢ ↦ loan_i}_{i∈I} ‖ {xᵢ ↦ borrow_i dᵢ}_{i∈I} ∪ {xⱼ ↦ dⱼ}_{j∉I}`, extended by the values the Π-type captured when it was formed. For `F = ⟦f⟧` we write `fwd_f d̄ = π₁(F d̄)` and `backᵢ_f d̄ = πᵢ(π₂(F d̄))`. These functions exist only in the model; the programmer never writes or sees them. Three features deserve comment. A proposition-valued function has no `Fin` component: under P5 it has no effect, so it is a proof and not a state transformer, and proof irrelevance at its type is sound. The backward part of a returned-borrow function is a function of the final value the caller leaves in the returned borrow; this is Aeneas's backward function, and the region abstraction of Aeneas's symbolic semantics is here simply a λ. And the restriction to injective backward functions is the one place where the model is a logical relation rather than a translation. It is forced: Ochr proves, by [Call-type], that every abstract function returning a borrow into its argument has an injective backward function (meta-model §1.3, `Q`), which is false for arbitrary CIC functions of that type and true for every definable one (Lemma 4).

**Environments.** Each abstract value `σ ∈ abs(Ω)` is a CIC variable of the translated type; `Γ_Ω` lists them. Each loan name `ℓ` is a CIC variable `h_ℓ`, a *hole* standing for the final content of borrow `ℓ`. The *view* `⟦Ω⟧` is the tuple of translated contents of the bindings of `Ω`, where `⟦borrow_ℓ v⟧ = ⟦v⟧` (a borrow is seen as its current content), `⟦loan_ℓ⟧ = h_ℓ`, `⟦σ⟧ = σ`, and `⟦⌈t⌉⟧ = Run(t) := π₁(⟦t⟧(⟦ε⟧))`, the result of running the closed program `t`. The *resolution* `ρ_Ω` is the substitution `h_ℓ := ⟦v_ℓ⟧[ρ_Ω]` for every `borrow_ℓ v_ℓ` held in `Ω`, well defined by (W3); it is the meaning of "end every borrow".

**Terms.** A run `Ω ⊢ t ⇓ v ⊣ Ω'` determines an input *shape* `S(Ω)` (which bindings exist and where borrows and loans sit) and an output shape `S(Ω')`. The machine computes shapes exactly, independently of the values of the abstract values, which is what the borrow checker guarantees. The translation `⟦t⟧_S : ⟦S⟧ → ⟦A⟧ × ⟦S'⟧` is state passing, with these key clauses (`s` ranges over views):

```
[End ℓ]          s  ↦  (s ∖ holder(ℓ))[h_ℓ := s.holder(ℓ)]
p := t           s  ↦  let (v, s₁) = ⟦t⟧ s in (⋆, s₁[p := v])
match p {…}      s  ↦  natCase (s.p) (⟦t_Z⟧ s[p := 0]) (λσ'. ⟦t_S⟧ s[p := succ σ'])
f(ā), B data     s  ↦  let (r, φ̄) = ⟦f⟧ ū w̄ in (r, (s ∖ args)[h_ℓᵢ := φᵢ])
f(ā), B = &T     s  ↦  let (c, β) = ⟦f⟧ ū w̄ in (c, (s ∖ args)[h_ℓᵢ := βᵢ(h_k)])        k fresh
t erased         s  ↦  (⟦value of t⟧, s)                                              t a type or a proof
```

where `ū` are the current contents of the borrow arguments (loans `ℓᵢ`) and `w̄` the other arguments. A definition translates by strong recursion on the entry value of its recursive argument: `⟦f⟧ d̄ = finish(⟦b⟧(⟦G(d̄)⟧))`, where `finish` pairs the result with the resolved final contents of the owners `cᵢ` (for a borrow result, with `λh_k.` of them), and where a recursive call is available only at arguments strictly below `d_rec`.

**Observations.** For a footprint `W` (§4 of the rules, with owner *sets*), `obs_W(Ω, t) = (v, ρ_Ω'(o))_{o ∈ W}` where `Ω ⊢ t ⇓ v ⊣ Ω'` on a private copy, and `⟦Id A t u⟧_Ω = (⟦obs_W(Ω, t)⟧ = ⟦obs_W(Ω, u)⟧)`.

### 2.3 Simulation (T0)

**Theorem 1 (simulation).** Let `Ω` be well formed and `Ω ⊢ t ⇓ v ⊣ Ω'` by the symbolic machine. Then, in CIC_L, in the context `Γ_Ω` extended with the holes of `Ω`,

```
⟦t⟧_{S(Ω)}(⟦Ω⟧)  ≡  (⟦v⟧, ⟦Ω'⟧).
```

Moreover, the sealed programs that [Close] produces at a call `f(ā)`, with borrow contents `ū` and other arguments `w̄`, denote the forward and backward functions of `f`:

```
⟦⌈L; C⌉⟧ ≡ fwd_f(ū, w̄)      ⟦⌈L; C; cᵢ⌉⟧ ≡ backᵢ_f(ū, w̄)      ⟦⌈L; let r = C; *r⌉⟧ ≡ π₁(⟦f⟧ ū w̄)      ⟦⌈L; let r = C; *r := loan_k; cᵢ⌉⟧ ≡ backᵢ_f(ū, w̄)(h_k)
```

The same holds for the concrete machine, with `Γ` empty.

*Proof.* By induction on the derivation. [Access] and [End] are the substitution clause. Reading, borrowing, assignment, `let` and [Drop] are projections, record updates and substitutions. [Match] on a constructor is ι-reduction of `natCase`. A call that unfolds is δβ, followed by the induction hypothesis for the body and a sequence of [End]s for the popped frame. A call at a proposition, and every erased term, is the erased clause. For [Close], the four equations hold by unfolding `Run` (δβζ only). The call clause produces exactly these projections whether or not `⟦f⟧ ū w̄` reduces further, because conversion includes unfolding, so discarding the partial run loses nothing. [Seal] computes `nf(⌈t⌉)` by running `t`, and the induction hypothesis on that sub-run gives `Run(t) ≡ ⟦nf(⌈t⌉)⟧`. Refinement and [End] into a sealed program are substitutions followed by [Seal], and `⟦−⟧` commutes with substitution because every clause is compositional and atoms translate to variables. ∎

*Hardest case:* [End k] when `loan_k` occurs inside sealed programs (the hole of a returned-borrow [Close]). The model substitutes `h_k := ⟦w⟧` into `Run(t)`. The machine substitutes `w` for `loan_k` inside `t` and re-runs. These agree by compositionality of `Run`, `Run(t)[h_k := ⟦w⟧] ≡ Run(t[loan_k := w])`. That in turn needs the hole to be inert *during* the run of `t`, which is [Seal]'s clause "loans whose borrow is outside the run are inert". If the run could end borrow `k`, it would reach outside the sealed program, and `Run` would not be a function of `t`.

The theorem says that a sealed program is not an approximation of a backward function but a *name* for it, written in source syntax. The [Close] equations are definitional equalities of the model, not axioms to be justified.

### 2.4 Frame (T2)

**Theorem 2 (frame).**
(a) *Locality.* Let `Ω = Ω₁ ⊎ Ω₂` be well formed, with every free variable of `t` bound in `Ω₁` and every loan occurring in `Ω₁` held in `Ω₁` (`Ω₁` is *loan-closed*; a borrow held in `Ω₁` may have its loan in `Ω₂`). Then `Ω ⊢ t ⇓ v ⊣ Ω'` iff `Ω₁ ⊢ t ⇓ v ⊣ Ω₁'` and `Ω' = Ω₁' ⊎ Ω₂θ`, where `θ = [loan_ℓ := v_ℓ]` ranges over the borrows held in `Ω₁` that the run ended, with their contents at ending. The same holds for stuck runs, with identical sealed programs.
(b) *Call effect.* At a call `f(ā)` from `Ω` with borrow arguments `borrow_ℓᵢ uᵢ`, the run of the call from `Ω` is the run from the callee's frame alone, followed by `loan_ℓᵢ := (the final content of the callee's i-th borrow)`. In the model, the caller's view after the call is the call clause with `F = ⟦f⟧`.
(c) *Call typing.* Let `f : Π(x̄ : Ā). B` be called at the call point `Ω` (after the arguments are evaluated) with borrow arguments of loans `ℓ̄`, and `O = ⋃ᵢ owners(ℓᵢ)`. For every `Id`-atom `Id A t u` of `B`, the caller-side observation is the generic-call observation mapped through `Ctx(v, φ̄, r̄) = (v, (C_o(φ̄))_{o ∈ O}, r̄)`, where `C_o` is the resolution context of `o` around the final contents `φ̄` of `ℓ̄`. If `Ctx` is jointly injective, then `⟦B@Ω⟧ = ⟦B⟧(ū)` (by `propext`).

**Lemma 3 (injectivity).** At a well-formed call site, `Ctx` is jointly injective, provided `O` contains *every* owner of the loans. *Proof.* `Ctx` is a composition of constructors (injective), of backward functions of returned-borrow calls applied at their hole argument (jointly injective: abstract ones by the restriction built into `⟦Π⟧`, definable ones by Lemma 4), and of components constant in the hole, for owners that do not contain it. Constant components preserve joint injectivity only if the component that does carry the hole is kept. Hence the footprint must observe every owner (D18); observing one lets [Call-type] prove `Id Nat (S Z) Z` (meta-model C2). ∎

**Lemma 4 (backward functions are injective).** For every definable `f : Π(x̄ : Ā). &T` and every `d̄`, `π₂(⟦f⟧ d̄)` is jointly injective. *Proof.* This is the fundamental lemma of the injective logical relation, by induction on `f`'s typing derivation, with the invariant that in the output view the hole `h_k` of the returned borrow occurs in jointly injective position across the owners' resolutions. The returned borrow is a parameter; or a reborrow of a sub-place of one parameter's content (`h_k` sits under constructors); or the result of an inner call (`h_k` at the hole argument of an injective backward function, by induction or by the restriction for an abstract callee); or the result of a closed-off block (the anonymous function's backward function, a `natCase` of injective maps). No rule discards a returned borrow's final value: [Assign] and [Drop] end the loans inside a content before overwriting or dropping it ([Access]), and [End] substitutes into every occurrence. ∎

*Proof of Theorem 2.* (a) By induction on the run. Every rule touches only places reachable from `t`'s free variables (there are no globals, and closures capture no borrows). [Access] and [End] find the borrow of any loan they touch inside `Ω₁`, by loan-closedness. The only way a run affects `Ω₂` is [End] of a borrow held in `Ω₁` whose loan lies in `Ω₂`, which is `θ`. (b) is (a) with `Ω₁` the callee's frame, followed by the pop; the frame is loan-closed by (W4). (c) Both observations run from `Ω` on private copies and, by (a), change nothing outside `ℓ̄` and their own locals. Ending every borrow at the end substitutes the final contents of `ℓ̄` into the owners' contexts. With Lemma 3 the `Eq`-atoms are equivalent, and the rest of `B` (Π, ∧, sorts) follows by congruence. ∎

*Hardest case:* (b) when `f` returns a borrow. When the frame is popped, the callee's parameter borrow still holds the returned borrow's loan, and [End] substitutes that content, loan and all, into the caller's owner. So the caller ends the call holding `K[loan_r]`: a place whose final value depends on something the caller has not produced yet. In the model this is `βᵢ(h_r) = K[h_r]`, and (c)'s injectivity is a property of `K` over all possible futures of `r`. That is why it needs Lemma 4, an induction over definitions, and cannot be read off `Ω`.

### 2.5 Naturality and adequacy (T5)

A **refinement** `α` of `Ω` is a type-respecting substitution on atoms: an abstract value `σ` goes to `Z`, to `S σ'` with `σ'` fresh, or to a closed value; an abstract function goes to a closed definable closure; a loan not held in `Ω` (an inert loan inside a sealed program) goes to a value whose own loans are held in `Ω` without creating a cycle. We write `Ω↓` for `Ω` with every sealed program re-normalised by [Seal], and `≈` for equality up to a bijective renaming of loan names and α-equivalence of binders inside sealed programs.

**Theorem 5 (naturality).** If `Ω` is well formed, `Ω ⊢ t ⇓ v ⊣ Ω'` by the symbolic machine, and `α` refines `Ω`, then `(Ωα)↓ ⊢ tα ⇓ v'' ⊣ Ω''` with `(Ω'', v'') ≈ ((Ω'α)↓, (vα)↓)`.

*Superseded: false as stated, see lean-meta F3 and paper meta.typ Theorem 7.*

**Corollary 6 (adequacy).** If `α` is ground, the run of `tα` uses no [Close]: it is a concrete run, it terminates (Lemma 1), and it computes the instantiated symbolic result. In particular every observation, and so every `Id`, computed on abstract inputs is the observation the program makes on every concrete input.

*Proof of Theorem 5.* By induction on the symbolic derivation. Every step except [Close] and [Seal] commutes with `α` on the nose. `α` substitutes atoms, the machine is deterministic, and every rule is uniform in atoms except [Match], which inspects a head. Symbolically, [Match] takes an arm only on a constructor head, which `α` preserves; a match on an atom is stuck, and is resolved by [Close] or by a stuck-block close-off, both of which are the [Close] case. [End] commutes with `α` because both are substitutions (with loans renamed consistently).

For [Close] at a call `C = f(ā)` with contents `ū`, the refined run reaches the same call with `ūα` and runs `f`'s body in a fresh frame; by Theorem 2(a) this is the run of the body alone. Re-normalising each sealed program `⌈L; C; …⌉α` runs `L; C`: the same body, from the same argument values, in a fresh frame. [Seal]'s head-call guard makes it unfold `C` exactly once and lets inner calls close exactly where the direct run closes them. By determinism the two runs take the same steps. Either both stop at the same stuck match, and both produce `⌈Lα; C…⌉` (the direct run by [Close], the re-normalisation by returning the sealed program with its values normalised); or both complete. When both complete with a borrow-free result, the direct run substitutes the final contents for `loan_ℓᵢ`, and the re-normalised fills are those same final contents. ∎

*Hardest case:* a returned borrow, with `α` letting the call complete. The direct run of `tα` pops `f`'s frame while the parameter's borrow holds the returned borrow's loan `loan_q`, so [End] substitutes `K[loan_q]` into the caller's owner and the call returns `borrow_q c`. The symbolic side holds the fill `⌈L; let r = C; *r := loan_k; cᵢ⌉` and the result `borrow_k ⌈L; let r = C; *r⌉`. Re-normalising the fill after `α` runs `C`, which returns `borrow_{q'} c` and leaves `cᵢ` holding `K[loan_{q'}]` after the pop. It then writes the inert `loan_k` into `r`, and finally reads `cᵢ`. By [Access], that read ends `q'`, whose borrow is *inside* the run, substituting `loan_k`. So the fill normalises to `K[loan_k]`, and the result to `c`. The two final states, `(owner ↦ K[loan_k], borrow_k c)` and `(owner ↦ K[loan_q], borrow_q c)`, are equal up to `k ↔ q`. Three rules make this work: loans as variables ([End] carries `loan_q` into the owner), [Access] ending run-internal loans while outside loans stay inert, and [Seal]'s head-call guard. When `α` refines only partially (the call proceeds and then gets stuck deeper), the same argument gives `S ⌈…loan_k…⌉` on both sides. Under the earlier design, where a pending anonymous binding kept the parameter's borrow alive in the caller, the two sides had different shapes and the theorem held only up to resolution.

*Remark (a design criterion).* Theorem 5 says that type-level evaluation is natural in the abstract values: normalising and then instantiating is the same as instantiating and then normalising. In the forcing model of dependent call-by-push-value, a computation is thunkable exactly when it is natural in this sense (Pédrot and Tabareau 2020, Prop. 18), so Theorem 5 is the precise sense in which Ochr's types are effect-free even though they run effectful programs. It is also a test that any proposed normalisation rule must pass. Two rules considered during the design fail it. One generalises the results of a stuck match to fresh abstract values (anti-unification), which forgets values a later refinement would recover. The other declines to run a proposition-valued *call* while running the same computation when it is not a call (§1.1). Recursion that is not structural on entry values fails it too: the call closes off while its argument is abstract, and diverges once the argument is instantiated.

### 2.6 Canonical observation (T1)

**Theorem 7 (canonical observation).** Let `Ω` be well formed.
(a) For distinct borrows `ℓ, m` held in `Ω`, `([End m] ∘ [End ℓ])(Ω)↓ ≈ ([End ℓ] ∘ [End m])(Ω)↓`.
(b) If `t` runs successfully from `Ω` under the lazy schedule (borrows ended only by [Access] and [Drop]) to `⟨Ω₁, v₁⟩`, and under any other schedule the rules permit (extra [End] steps at arbitrary points) to `⟨Ω₂, v₂⟩`, then `v₁ ≈ v₂` and `ρ_Ω₁ = ρ_Ω₂`.
Consequently `obs_W(Ω, t)` does not depend on when loans are ended, and `Id` is well defined.

*Proof.* (a) Up to `↓`, [End] is the substitution `h_ℓ := v_ℓ`. If `ℓ ◁ m` (the loan of `ℓ` lies in `m`'s content `v_m`), ending `ℓ` first updates `v_m` and then ending `m` substitutes `v_m[h_ℓ := v_ℓ]`; ending `m` first carries `h_ℓ` into `m`'s loan positions and then ending `ℓ` substitutes `v_ℓ` everywhere, including there. The two composites agree because `h_m` does not occur in `v_ℓ` (W3). The `↓` steps commute by Theorem 5, since substituting for a hole is a refinement. (b) Suppose the second schedule ends `ℓ` at point A, and the lazy one at a later point B, or at the final resolution. Between A and B the second run cannot use borrow `ℓ` (it would read `⊥`, contradicting success), so `ℓ`'s content is the same at A and at B. No step between them can move or overwrite an occurrence of `loan_ℓ`: such an occurrence lies inside a loaned-out content, where any access would trigger the lazy [End] first, or inside a sealed program, which is a value. So both schedules substitute the same content. Induct on the number of extra ends. ∎

*Hardest case:* a loan inside a sealed program, where [End] is followed by re-normalisation. The order of two ends then matters syntactically unless re-normalising commutes with later substitutions, which is Theorem 5. Canonicity, which the design notes single out as the most important theorem of the design, is in this sense a corollary of naturality.

*Superseded: false as stated, see lean-meta F3 and paper meta.typ Theorem 7.*

### 2.7 Soundness of the model (T3)

**Theorem 8 (soundness).** For a program accepted by [Def] and [Rec]:
(a) *Types.* If `A` is a type at `Ω` with normal form `A↓`, then `Γ_Ω ⊢ ⟦A↓⟧ : ⟦s⟧`, where `s` is its sort.
(b) *Conversion.* If `Ω ⊢ A ≡ B`, then `⟦A⟧ = ⟦B⟧` is provable in CIC_L, and `⟦A⟧ ≡ ⟦B⟧` holds in ECIC_L.
(c) *Typing.* If `Ω ⊢ t : A`, typed by the machine with [Split], then `Γ_Ω ⊢ ⟦t⟧_{S(Ω)} : ⟦S(Ω)⟧ → ⟦A⟧ × ⟦S(Ω')⟧`.
(d) *Definitions.* If `fix f (x̄ : Ā) : B := b` is accepted by [Def], then `⊢ ⟦f⟧ : ⟦Π(x̄ : Ā). B⟧`, including membership of the injective subset when `B = &T`.

*Proof.* By induction on derivations.
- *[Def].* The goal of [Def] is the [Call-type] of the generic call, which is `⟦B⟧(d̄)` by the definition of `G(d̄)`. The body, run from `⟦G(d̄)⟧` and finished, has type `Out_B(d̄)`. For `B = &T`, membership of the injective subset is Lemma 4.
- *[Split], tail position.* Dependent elimination on the CIC variable `σ`, with a motive that abstracts `σ` in the goal and in every stored type. The rule's "apply the refinement to Ω, the goal and all stored types" *is* this motive. Because `σ` is a variable, this is ordinary CIC dependent elimination.
- *[Split], non-tail position.* The arms are checked as in the tail case, and together they define the anonymous function `g` of the closed-off block, well typed by the induction hypothesis. The continuation runs from the state in which the block is `g(ā)`, closed off; by Theorem 1 that state denotes the application of `⟦g⟧`. Nothing is generalised.
- *[Call-type].* `⟦f⟧ ū w̄ : Out_B(ū)`, cast along Theorem 2(c) to `⟦B@Ω⟧`.
- *[Rec].* `⟦fix⟧` is strong recursion on the entry value of the recursive argument. Each recursive call is at a strict subterm, and `f` occurs nowhere else (§1.2), so the recursor's induction hypothesis supplies every occurrence.
- *Erased terms* (types and proofs, under P2 and P5 as amended). The erased clause: the value is typed by the induction hypothesis and the state is unchanged, which is what the machine does.
- *Conversion.* Terms with the same normal form have the same translation (Theorem 1). The `Eq` rules are instances of `propext`: `((a, b) = (a', b')) = (a = a' ∧ b = b')`, `(a = a) = True`, `(True ∧ P) = P`, with `refl` translated to `True.intro`. Proof irrelevance is definitional in CIC_L, and it is sound because every Ochr proposition translates to a CIC proposition: a proposition-valued Π over borrows has no `Fin` component. Unit η is definitional in CIC_L. `J` translates to `Eq.rec`, with casts along the `Eq` rules. ∎

*Hardest case:* [Call-type]. It needs, at once: Theorem 2(b) (the callee's effect is `⟦f⟧ ū w̄`); Theorem 2(c) (the caller's observations are the generic ones under an injective context); Lemma 3, and so owner sets; Lemma 4, and so the injective restriction for abstract functions; `propext`, to turn an equivalence of propositions into an equality of types; the escape-free guard, so that the induction hypothesis exists; and P2's capture of formation-time values, without which `⟦B@Ω⟧` is not an instance of `⟦B⟧` at all (meta-model C4).

**What the model needs from type theory.** Computations need nothing extensional: every machine step is intensional conversion (Theorem 1). Propositions need `propext`, because Ochr's conversion identifies propositions that CIC proves only logically equivalent: the `Eq` rules, and above all [Call-type]'s caller-side codomain with the generic one (Theorem 2(c)). A translation that sends conversion to conversion therefore targets ECIC_L; a translation into CIC_L inserts casts along `propext` equalities, which is the reflection-elimination of Winterhalter, Sozeau and Tabareau (needing UIP, definitional in Lean, and funext, a theorem in Lean). Function extensionality is never needed, since Ochr compares functions only by normal form.

### 2.8 Consistency (T4)

**Corollary 9 (consistency).** No closed Ochr term has type `Eq Nat Z (S Z)`, or `Π(P : Prop). P`. More strongly, if `⊢ t : P` for a closed proposition `P`, then `⟦P⟧` holds in the set model.

*Proof.* By Theorem 8, `⊢ ⟦t⟧ : ⟦P⟧` in ECIC_L (the state component of a closed term is empty). ECIC_L has Carneiro's model in ZFC with one inaccessible cardinal per universe level used, in which `⟦Eq Nat Z (S Z)⟧ = [0 = 1] = ∅`. ∎

The corollary is deliberately stated in its strong form. Under P5, no proof is ever run, so consistency cannot lean on the checker diverging, as it could in earlier drafts (meta-model C3, where every closed instance of a false theorem made the checker loop). The model is the only argument, and it is the right one.

### 2.9 Where Ochr sits among effectful type theories

Pédrot and Tabareau's fire triangle says that substitution, dependent elimination and observable effects cannot coexist consistently. Ochr has dependent elimination ([Split] refines abstract values in the goal and every stored type). It restricts substitution to values: typing is call-by-value evaluation, and [Call-type] binds a parameter to the argument's value, never to a computation. And it has no observable effects in their sense: a closed program owns all its state (Theorem 2(a) with nothing outside), so by Corollary 6 it runs to a canonical value. Effects are observable only relative to *open* borrows, and those are exactly what the state-passing model makes pure. Theorem 5 is the precise form of "types are effect-free": it is naturality of the normaliser under refinement, which is what thunkability amounts to in the forcing model (their Prop. 18). We do not claim an embedding of Ochr into dependent call-by-push-value; the correspondence is between the invariants, and it predicted exactly which candidate rules had to go.

## 3. Work plan: one agent, Lean 4.33, shallow target

### 3.1 Scope and design decisions

- **Where.** A Lake package `OchrCore` under `ochr/core/lean/`, on toolchain `leanprover/lean4:v4.33.0` (the same as `dllbc/`), with no Mathlib, `autoImplicit := false`, and `precompileModules := true` once the tests start calling the interpreter heavily (dllbc's lakefile is the template). Lean 4.33 API reminders: `l[i]?` not `List.get?`, `List.zipIdx` not `List.enum`, `List.flatten` not `List.join`.
- **The fragment "FO".** First-order data (`Nat`, `Unit`, pairs); v1's places (`x`, `*p`, `p.1`); `&p`, `:=`, `let`, `;`, `match p {Z ⇒ t | S y ⇒ u}` with `y` an alias of `p.1`; saturated calls to named n-ary definitions, possibly recursive; results that are data or `&T`. *Opaque* definitions (declared, no body) stand in for abstract functions: a call to one is stuck at once. A flag `isProp` on a definition marks a proposition-valued result, and a term former `erase t` marks a Prop-typed block; both run on a private copy (P5, term-keyed). There are no closures, no Π, `Id` or `Eq` in the object language: observations are meta-level functions, and `Id` becomes Lean's `=` on them. This keeps object-level dependent types out entirely and still covers every novel rule.
- **"Shallow".** The target is Lean itself. Ground values are Lean data, and the meaning of a computation is its concrete run, a Lean relation over Lean data. Consequently T0 for FO *is* the adequacy statement (symbolic run, instantiated, equals concrete run), and the [Close] equations become Lean lemmas saying that a fill's instance is the corresponding component of the callee's concrete run. The propositional layer (Lemmas 3–4, T2c) is stated with Lean's `=` and `Function.Injective`.
- **One relation, both machines.** `Eval P Ω t r`, with results `ok Ω v | stuck | err`. [Close] and [Seal] are always available, and a lemma shows [Close] never fires on ground inputs, so concrete runs are just `Eval` runs on ground environments. Next to it sits a fuelled interpreter `run` with `run_sound`, used by all tests.
- **Names.** [Close] must generate its binders deterministically (`c₀, c₁, …` by argument position), so that "≈" is only a renaming of loan ids. Implement `≈` as equality after `canon`, which renames loans in order of first occurrence; this makes it decidable.

### 3.2 Modules, in build order

| Module | Contents |
|---|---|
| `OchrCore/Syntax.lean` | `Place`, `Ty`, mutual `Term`/`Val` (`Val.seal : Term → Val`, `Term.val : Val → Term`), `FunDef` (`params`, `ret`, `isProp`, `body : Option Term`, `recPos`), `Prog`, `Env := List Frame`, `Res` |
| `OchrCore/Subst.lean` | `substLoan ℓ w` and `substAbs α` on `Val`/`Term`/`Env` (into sealed programs too); `loans`, `abs`, `fv`; `canon` and `≈` |
| `OchrCore/Env.lean` | `content`, `update`, `endBorrow` ([End]), `access` ([Access], with a mode for match), `owners` (sets), `resolve`, `WF` (W1–W4), `LoanClosed` |
| `OchrCore/Machine.lean` | `Eval`, `EvalArgs`, `CallRun` (a call from its own frame), the [Close] port table, `Norm` ([Seal] with the head-call guard), erased terms |
| `OchrCore/Interp.lean` | `run (fuel)`, `norm (fuel)`, `run_sound`, `norm_sound` |
| `OchrCore/Guard.lean` | the [Rec] check *with the escape clause*, `WellGuarded P`, and Lemma 1 (termination) for FO by a lexicographic measure |
| `OchrCore/Frame.lean` | T2a, T2b, `Invariance` (Lemma 0) |
| `OchrCore/Sim.lean` | `Inst` (ground instantiation: sealed programs by concrete runs), the [Close] equations, T0-FO |
| `OchrCore/Canon.lean` | T1 |
| `OchrCore/Inj.lean` | `BackSem`, Lemma 4, `Ctx`, Lemma 3, `obs`, T2c |
| `OchrCore/Natural.lean` | T5(a), on the nose up to `≈` (stretch goal). *Superseded: false as stated, see lean-meta F3 and paper meta.typ Theorem 7.* |
| `OchrCore/Tests/*.lean` | §3.4 |

### 3.3 The theorems, in the order to prove them

These are target statements. The auxiliary definitions they name are the ones in §3.2, and the agent will adjust arities; the shape of each statement should not change. `hP : WellGuarded P` and `hwf : WF Ω` are standing hypotheses.

**Phase 1: T2 (frame), the base everything else stands on.**

```lean
/-- T2a. `Res.frame` appends `Ω₂`, substituting into it the loans of borrows held in Ω₁ that the run ended. -/
theorem frame_local (hlc : LoanClosed Ω₁) (hfv : t.fv ⊆ Env.dom Ω₁) :
    Eval P (Ω₁ ++ Ω₂) t r ↔ ∃ r₁, Eval P Ω₁ t r₁ ∧ r = r₁.frame Ω₁ Ω₂

/-- T2b. A call's effect is its isolated run, plugged back into the loans of its borrow arguments. -/
theorem call_effect :
    Eval P Ω (.call f args) r ↔
      ∃ Ωa vs rc, EvalArgs P Ω args Ωa vs ∧ CallRun P f vs rc ∧ r = rc.plug Ωa (borrowLoans vs)

/-- Lemma 0. Every run preserves W1–W4. -/
theorem eval_wf (h : Eval P Ω t (.ok Ω' v)) : WF Ω'
```

**Phase 2: T0 for FO (simulation into Lean), hardest case first.**

```lean
/-- On ground inputs, in a program with no opaque definitions, [Close] never fires. -/
theorem ground_no_close (hno : P.NoOpaque) (hg : Env.Ground Ω) (h : Eval P Ω t r) : r ≠ .stuck

/-- The [Close] equations: each fill instantiates to the matching component of the callee's concrete run.
    `rc.fin i` is the final content of the i-th borrow parameter; `rc.back i w` the same after writing `w`
    into the returned borrow (the returned-borrow row). -/
theorem close_fill (hγ : Ground γ) (hrc : CallRun P f (vs.inst P γ) rc) :
    Inst P γ (.seal (closeFill f vs i)) (rc.fin i) ∧
    ∀ w, Ground w → Inst P γ ((Val.seal (closeHoleFill f vs i k)).substLoan k w) (rc.back i w)

/-- T0-FO: symbolic runs are sound for every ground instantiation (Theorem 1 with Corollary 6).
    `Completes P' P`: P' agrees with P and gives every opaque definition a (well-guarded) body,
    which is how abstract functions are instantiated. -/
theorem sim (h : Eval P Ω t (.ok Ω' v)) (hc : Completes P' P) (hγ : GroundFor γ Ω) :
    ∃ Ωc vc, Eval P' (Ω.inst P' γ) (t.inst P' γ) (.ok Ωc vc) ∧ Ωc ≈ Ω'.inst P' γ ∧ vc ≈ v.inst P' γ
```

Start `sim` at the case of a returned-borrow [Close] followed by the caller writing through the borrow and ending it: the key lemma is `Inst` commuting with `substLoan` (the paper's `Run(t)[h_k := w] ≡ Run(t[loan_k := w])`).

**Phase 3: T1.**

```lean
theorem end_comm (hℓ : Env.Holds Ω ℓ) (hm : Env.Holds Ω m) (hne : ℓ ≠ m) :
    ((Ω.endBorrow ℓ).bind (·.endBorrow m)).map Env.norm ≈ ((Ω.endBorrow m).bind (·.endBorrow ℓ)).map Env.norm

/-- `EvalS P s` is `Eval` with extra [End] steps at the points listed in the schedule `s`. -/
theorem schedule_indep (h₁ : EvalS P s Ω t (.ok Ω₁ v₁)) (h₂ : Eval P Ω t (.ok Ω₂ v₂)) :
    v₁ ≈ v₂ ∧ Env.resolve Ω₁ ≈ Env.resolve Ω₂
```

**Phase 4: injectivity and [Call-type] (Lemmas 3 and 4, T2c).**

```lean
/-- The hypothesis the model builds into abstract function types. -/
def OpaqueInj (P : Prog) : Prop :=
  ∀ f d, P f = some d → d.body = none → ∀ vs, Ground vs → Function.Injective (BackSem P f vs)

/-- Lemma 4. -/
theorem back_inj (hopq : OpaqueInj P) (hf : (P f).map (·.ret) = some (.ref T)) (hvs : Ground vs) :
    Function.Injective (BackSem P f vs)

/-- Lemma 3. `W` must be *all* owners of the argument loans; the lemma is false for a proper subset (test C2). -/
theorem ctx_inj (hopq : OpaqueInj P) (hW : W = ownersOf Ω (argLoans args)) : Function.Injective (Ctx P Ω args W)

/-- T2c for one `Id`-atom: the caller-side observation is the generic one under `Ctx`. -/
theorem call_obs (h : GenericObs P f t gObs) :
    obs P Ω (t.bindParams args) (callerFootprint Ω args) = gObs.map (Ctx P Ω args (callerFootprint Ω args))

/-- The consequence [Call-type] uses; Lean's `propext` turns it into an equality of the Eq-atoms. -/
theorem call_type_atom (hopq : OpaqueInj P) (ht : GenericObs P f t gT) (hu : GenericObs P f u gU) :
    obs P Ω (t.bindParams args) (callerFootprint Ω args) = obs P Ω (u.bindParams args) (callerFootprint Ω args)
      ↔ gT = gU
```

**Phase 5 (stretch): T5(a) on the nose.** *Superseded: false as stated, see lean-meta F3 and paper meta.typ Theorem 7.*

```lean
theorem natural (hα : Refines α Ω) (h : Eval P Ω t (.ok Ω' v)) :
    ∃ Ω'' v'', Eval P (Ω.subst α).norm (t.subst α) (.ok Ω'' v'') ∧ Ω'' ≈ (Ω'.subst α).norm ∧ v'' ≈ (v.subst α).norm
```

### 3.4 Regression and property tests

**(A) In the FO mechanisation** (`Tests/*.lean`, `#guard` or `example … := by native_decide` over `run`/`norm`):

| Test | Checks | Source |
|---|---|---|
| `e1e2_runs` | `AddM`, `Add`, `TailM`, `AddM'` on inputs `0..5`: concrete results are the expected numerals | E1, E2 |
| `close_eqs` | for `AddM`, `TailM`, `Pick` on ground arguments `0..4`: each [Close] fill normalises to the concrete run's final content, and each hole fill with `w ∈ 0..4` to `back w` | T0, `close_fill` |
| `natural_prop` | for `Add x 0`, `AddM'(x, y)`, `TailM(x)` with `x ↦ σ`, `α ∈ {σ := Z, σ := S σ', σ := k for k ≤ 4}`: `canon (norm (run t)·α) = canon (run (t·α))` *Superseded: false as stated, see lean-meta F3 and paper meta.typ Theorem 7.* | T5 |
| `canon_sched` | for the three-borrow program `let b = &a; let r = &(*b).1; …` and for `Pick`'s result: every order of [End] steps yields the same `resolve` | T1 |
| `owners_pick` | after `let r = Pick(n, &a, &b)` with `n ↦ σ`, `owners Ω k = {a, b}` | C2, D18 |
| `back_inj_small` | `BackSem` of `TailM` and `Pick(σ := Z)`, `Pick(σ := S Z)` injective on `0..6` | Lemma 4 |
| `ctx_needs_all_owners` | `Ctx` restricted to `{a}` for `Pick` is *not* injective in the `S` branch (a negative test, so a future "optimisation" of owners fails loudly) | C2 |
| `access_inner` | moving `b` in `let a = S Z; let b = &a; let r = &(*b).1; G(b, n)` ends `r` first, so a later `*r := …` is `err` | C5, breaker-close A1 |
| `erase_natural` | a Prop-typed `erase (match b {Z ⇒ a := S Z | S _ ⇒ a := S Z})` leaves `a` unchanged both at `b ↦ σ` and at `b := Z` | R1 |
| `guard_rejects` | the [Rec] check rejects `Grow`, e346's `Loop`, `Apply(f, n)` and `let g = f; g(n)`, and accepts `AddM`, `TailM`, `AddMZero` | C3, R2 |

**(B) For the checker (whoever owns it).** Expected outcomes under v1 with the §1.5 amendments. Each rejection test should also assert the *reason* (rule name), so a test that passes for the wrong reason is caught.

| Test | Expected | Reason |
|---|---|---|
| `C1_J`, `C1_seal` (meta-model §3.1, `Π(P : Prop). P` in place of `⊥`) | reject | `F P₁ ≡ F P₂ ≡ ⊤` under P5, so `J` yields `⊤` |
| `C2_pick` | reject `h refl` in the `S` arm | owner set `{a, b}` |
| `C3_grow`, `C3_loop` (e346 F6) | reject | [Rec]: argument not a strict subterm of the entry value |
| `C4_oops2` (e346 F5) | reject | `h()`'s type is captured at formation |
| `C5_A1` (breaker-close A1) | reject | [Access] ends `r` before the move; the later write reads `⊥` |
| `R1_Q` (= breaker-close-v1 N1, deriver-e346-v1 N12) | reject the final `J` | term-keyed P5: `Q(Z, Z) : ⊤`. *Accepted by v1.1 as written: the test documents the bug.* |
| `R2_apply`, `R2_letf`, `R2_nested` (`Apply(fix _ (y) := f(y), x)`) | reject | [Rec] escape clause (v1.1); the nested case, because [Rec] also applies inside nested functions |
| `R4_knot3` (deriver-e346-v1 §E6.8) | reject | the match on a sealed program generalises and [Split]s; [Rec] then rejects both recursive calls |
| `N2_capture` (deriver-e346-v1 N2): `let r = match b {Z ⇒ x1 | S _ ⇒ x2}; AddM(r, y); AddM(x1, 0)` | reject | `x1` is moved by one arm, so the lifted call moves it |
| `G1_callpoint` (deriver-e1-v1 G1): `refl : Π(x : &Nat). Id Unit (AddM(x, S Z)) ()` | reject | [Call-type] at the call point: `W = {c}` |
| `R3_typewrite` | reject `Π(x). Id Nat (H(x)) Z` | types run on a private copy, so `H(σ) ⇓ σ` |
| E1, E2 (all eight definitions), E3 `AddToOne` (now accepted by D15), E4 `Twice`, `TwiceM`, `TwiceMZero` | accept | |

### 3.5 Milestones for the one agent

1. **M0 (2–3 days).** Package, `Syntax`, `Subst`, `Env` (with `endBorrow`, `access`, `owners`), `Interp`; the tests `e1e2_runs`, `owners_pick`, `access_inner` pass on the interpreter. Commit.
2. **M1 (1–2 weeks).** `Eval`, `run_sound`, Lemma 0, T2a, T2b. Commit.
3. **M2 (1–2 weeks).** `Inst`, `close_fill`, `ground_no_close`, `sim`, starting with the returned-borrow [Close] then `end k` case; the tests `close_eqs`, `natural_prop` (ground α). Commit. *This milestone is the mechanical validation of the paper's central claim: sealed programs are backward functions.*
4. **M3 (1 week).** `end_comm`, `schedule_indep`, `canon_sched`. Commit.
5. **M4 (1–2 weeks).** `Guard` with Lemma 1 for FO, `back_inj`, `ctx_inj`, `call_obs`, `call_type_atom`, the injectivity tests. Commit.
6. **M5 (stretch).** `natural` (T5(a) on the nose), and `natural_prop` for non-ground α. *Superseded: false as stated, see lean-meta F3 and paper meta.typ Theorem 7.*

Estimated size, as in round 1: roughly 3–5k lines for M0–M4. Working practice that has held up in this repo: write at most about 120 lines per edit, build the narrowest target after each chunk, and commit at each milestone. The dependent layer (Π over `Id`, universes, [Split]'s motive, Corollary 9) stays on paper. It would need a universe of codes for Ochr types inside Lean, which is a separate project; a middle road covering a fixed stock of types (`Nat`, `Unit`, `×`, `Eq` at first-order types, one `Prop` layer) would take 1–2 more months after M4.
