# meta-model: a CIC model of the Ochr core, the soundness theorems, and what the model refuses

## 5-line summary

1. **Verdict:** Ochr has a clean model: an Aeneas-style state-passing translation into Lean's type theory (CIC + definitional proof irrelevance + `propext`), in which a sealed program is literally an application of a backward function, a loan hole is the argument of a backward function, and `Id` is `Eq` on tuples. [Close] (both forms), [Seal], refinement, D6, [Lam], [Split] and (read as generalisation) [Join] are validated. RULES v0 is nonetheless unsound in four places; C1 is new here and C2's closed proof of ⊥ is new here (e346 F11 found the duplicated hole but not the bug).
2. **Most important finding:** (C1) a Π-type with a borrow parameter cannot be a proof-irrelevant `Prop`: `λx. ⟨⟩` and `λx. (*x := 7; ⟨⟩)` are different functions in the model, and `J` turns their definitional identification into a closed proof of `⊥` (§3.1). (C2) with two borrow parameters and a returned borrow, [Close] puts the same hole in both parameters, and a footprint that observes one owner lets [App] prove `Id Nat (S Z) Z` (§3.2). Behind C2 is a model fact worth a paragraph in the paper: [App] is valid only because every backward function is injective in the final value of the returned borrow, so the model of a returned-borrow function type is the injective subset (a unary logical relation), not all CIC functions of that shape.
3. **RULES.md must change:** a Π over a borrow parameter is in `Type`, or (better, and the same rule as e346 F8) a call whose result type is a proposition runs on a private copy; the footprint observes *every* owner of a hole; §6 needs the entry-value guard (= e346 F6); Π-types close over formation-time values and [App] binds only the parameters (= e346 F5); every access ends the loans and holes *inside* the accessed content, not only on its path; holes are variables (= e2 F3); `Type : Type` must be excluded.
4. **Confidence:** high for C1 and C2 (full derivations below) and for the value-level model (T0, [Close], [Seal]); medium-high for the T1/T2/T5 sketches; medium for T3 on the full dependent layer (key cases argued, not every case); the ∂CBPV link (§4) is a structural correspondence I can state precisely, not a theorem I have proved.
5. **Not checked:** [Join] completeness and E3; universe levels beyond "no `Type : Type`"; decidability and termination of the checker itself; anything mechanised; loops, shared borrows and borrows in data (out of scope, D8).

## 0. How to read this

§1 defines the translation ⟦-⟧. §2 states the theorems T0–T5 with proofs sketched and the hardest case of each argued. §3 goes through RULES v0 rule by rule; the four rules the model does not validate come with a bad derivation and a minimal fix. §4 is the fire-triangle connection. §5 says what to mechanise in Lean and how. §6 is the theorem list on one page.

I assume the repairs other agents already found and that do not bear on soundness: calls are saturated and n-ary (e1 F2); a sealed program built by [Close] is normal, and re-running it after a refinement does not re-close the sealed call itself (e1 F1, e2 F1); the call point is "after the arguments are evaluated, before the frame is pushed" (e1 F6).

Terminology used throughout. The *current content* of a borrow is the value stored inside `borrow_ℓ v` (LLBC keeps it there). The *final content* is what it holds when it ends. A *hole* `?k` is the placeholder that [Close] writes into a sealed program for "the final content of borrow `k`, not known yet" (RULES writes it `loan_k`; §3.5 explains why it must be a variable). The *owners* of a borrow are the owned places (ordinary variables not of borrow type, and ghosts `x°`) whose content, once every borrow is ended, depends on that borrow's final content.

## 1. The model

### 1.0 In plain words

A program that mutates what it borrows means a pure function that takes the current contents of its borrows and returns its result together with their final contents. This is Aeneas's reading, and it is the whole model: places become state passing. A function that returns a borrow means a pair: the current content of the returned borrow, and a *backward function* that, given the final content the caller eventually leaves in it, says what each borrowed parameter ends up holding. Abstract values `σ` are ordinary CIC variables. A sealed program is a closed program, so it means whatever that program computes; for `⌈L; C; c⌉` that is, by unfolding, the backward function of the call `C` applied to the argument values. A hole `?k` is a CIC variable `h_k`, bound when borrow `k` ends. `Id` computes to an equation between tuples, and that equation is a CIC equation. The programmer never sees any of this: the forward and backward functions exist only here.

### 1.1 Target theory, and what needs extensionality

The target is **CIC_L**, Lean's type theory as axiomatised by Carneiro (theory-of-lean §2): universes `Prop : Type₀ : Type₁ …`, impredicative `Prop` with definitional proof irrelevance, `ℕ`, `𝟙` with η, `×`, `Σ`, `PProd` (a pair whose first component may be a proof), `Eq`, `True`, `False`, `∧`, and the axiom `propext`. For a statement of the form "Ochr conversion is sent to conversion" I use **ECIC_L** = CIC_L + equality reflection.

The model splits cleanly in two, and the split is the answer to "extensional if unavoidable":

- **Values and computations need nothing extensional.** Every step of the machine, including [Close], [Seal], refinement and ending a loan, is sent to intensional CIC conversion (δβιζ, ι on `ℕ`, η on `𝟙`). This is T0 below.
- **Propositions need `propext`.** Ochr's conversion identifies propositions that CIC only proves equivalent: D6's `Eq Nat (S a) (S b) ≡ Eq Nat a b`, `⊤ ∧ P ≡ P`, and, more importantly, [App]'s caller-side codomain with the callee's (T2c). A translation that sends Ochr conversion to conversion therefore needs `propext` plus reflection (ECIC_L); a translation into plain CIC_L inserts casts along `propext` equalities instead (the reflection-elimination of Winterhalter, Sozeau and Tabareau, which needs UIP, true definitionally in Lean, and funext, a theorem in Lean). Deleting D6 (simplifier's proposal) does not remove the need: [App]'s contexts contain backward functions, which are neutral, so no definitional trick makes the two sides of [App] convertible. D6 on its own could be made definitional in intensional CIC by translating `Eq` at first-order types to an observational equality defined by recursion (OTT style), but that buys nothing once [App] needs `propext` anyway.
- **funext is never needed**: Ochr compares functions only by normal form, never extensionally.

Both targets are consistent by Carneiro's set model (theory-of-lean §6): `Prop` is `{∅, {•}}`, so two propositions with the same truth value are the same set (this validates `propext` and every D6 rule at once), and `⟦a = b⟧ ≠ ∅` implies `⟦a⟧ = ⟦b⟧` (this validates reflection).

### 1.2 Data types and propositions

```
⟦Nat⟧ = ℕ      ⟦Unit⟧ = 𝟙      ⟦A × B⟧ = ⟦A⟧ × ⟦B⟧      ⟦Prop⟧ = Prop      ⟦Type⟧ = Type₀
⟦Eq A a b⟧ = (⟦a⟧ =_⟦A⟧ ⟦b⟧)      ⟦⊤⟧ = True      ⟦⊥⟧ = False      ⟦P ∧ Q⟧ = ⟦P⟧ ∧ ⟦Q⟧
```

`Id` is not translated: it is derived, and its normal form (an `Eq` on observations, §1.7) is.

### 1.3 Function types: forward and backward functions

For `Π(x₁ : A₁) … (xₙ : Aₙ). B`, let `I` be the borrow positions (`Aᵢ = &Tᵢ`).

```
Dᵢ     = ⟦Tᵢ⟧ if i ∈ I, else ⟦Aᵢ⟧          what the function receives: the current content of each borrow
Fin    = ∏_{i ∈ I} ⟦Tᵢ⟧                    the final contents of the borrowed places
Out(d̄) = ⟦B⟧(d̄) ⊗ Fin                      if B is borrow-free            (⊗ is PProd)
Out(d̄) = ⟦T'⟧ × (⟦T'⟧ → Fin)               if B = &T'

⟦Π(x̄ : Ā). B⟧   = Π(d̄ : D̄). Out(d̄)                                           borrow-free result
⟦Π(x̄ : Ā). &T'⟧ = { F : Π(d̄ : D̄). Out(d̄)  |  ∀ d̄. π₂ (F d̄) is injective }    returned borrow
```

The *forward function* is `f_fwd d̄ = π₁ (F d̄)`. The *backward function* for parameter `i` is `f_backᵢ d̄ = πᵢ (π₂ (F d̄))`: a value when the result is borrow-free, a function of the returned borrow's final content otherwise. "Injective" is joint: equal tuples of final contents come from equal final values of the returned borrow.

`⟦B⟧(d̄)` is the translation of the normal form of `B` at the **entry environment** `E(d̄) = { xᵢ° ↦ loan_i | xᵢ ↦ borrow_i dᵢ (i ∈ I), xⱼ ↦ dⱼ (j ∉ I) }`, extended by the Π-type's own closure (the formation-time values of its other free variables, C4). This is [Lam]'s "evaluate the goal once, at entry".

Three remarks.

- **The injective subset is the one place where the model is a logical relation rather than a plain translation.** Without it [App] is not validated for abstract functions. Ochr proves `Q : Π(h : Π(x : &Nat). &Nat) (a : Nat). Π(e : Id Unit (let r = h &a; *r := Z) (let r = h &a; *r := S Z)). ⊥` by `Q h a := let r = h &a; G r` (with `G` from §3.2; [App] gives `G r` exactly the goal). The codomain normalises to `Eq Nat A(Z) A(S Z) → ⊥` with `A(w) = ⌈let c = a; let r' = h &c; *r' := w; c⌉`, so `Q` says "every function returning a borrow into its argument has an injective backward function". That is false for arbitrary CIC functions of that shape (take a constant backward function) and true for every Ochr-definable one (Lemma BackInj, under T2), so the model must quantify over the injective ones only. This is the same move as Pédrot–Tabareau's Θ-types (functions restricted to those that preserve thunkability) and Bowman et al.'s parametricity equation: a rule of the source theory holds on the definable part of the function space, and the model builds that part in. It is also a design constraint for later extensions: any construct that lets a backward function forget the final value of a returned borrow makes [App] unsound.
- **Sort.** `Out` contains `Fin`, which is data, so `⟦Π(x̄ : Ā). B⟧ : Type` whenever `I ≠ ∅`, even when `B : Prop`. The Ochr Π-type must agree, or definitional proof irrelevance identifies functions with different effects: that is C1 (§3.1). Under the alternative fix (a call whose result type is a proposition runs on a private copy), `Out(d̄) = ⟦B⟧(d̄)` when `B : Prop`, and the Π-type is a `Prop` again.
- The recursion checker is not needed to *state* the model but is needed to *inhabit* it: `⟦fix …⟧` is a CIC structural recursor, which exists only if the recursive argument's entry content decreases (C3).

### 1.4 Environments, abstract values, holes, resolution

Let `Ω` be well-formed (invariants I1–I4, stated with T1). It translates to three things.

- **The context `Γ_Ω`.** Every abstract value `σ : τ` in `Ω` becomes a CIC variable `σ : ⟦τ⟧`; `Γ_Ω` lists them. Abstract functions `σ_f` are variables of the (subset) function type. Join variables are ordinary abstract values (they are generic, §3.7). Refinement `σ := Z` / `σ := S σ'` is the CIC substitution `σ ↦ 0` / `σ ↦ succ σ'`, with `σ' : ℕ` added to `Γ`.
- **The current view `cv_Ω`.** For every live binding `y` (named variables, ghosts `x°`, anonymous pending borrows), `cv_Ω(y)` is the translation of `y`'s content with `borrow_ℓ w ↦ ⟦w⟧` (a borrow is seen as its current content) and `loan_ℓ ↦ h_ℓ`, `?ℓ ↦ h_ℓ`. A loan at a place and a hole inside a sealed program are the same thing in the model: a variable for a final content not known yet. The binding that holds `borrow_ℓ` is the *holder* of `ℓ`. The variables `h_ℓ` are **not** in `Γ_Ω`; resolution binds them.
- **The shape `S_Ω`.** `Ω` with the translated leaves erased: which bindings exist, which hold borrows, where the loans and holes sit, and the types. The symbolic machine computes shapes exactly, and the shape is the same for every instantiation of the `σ`s. That is what the borrow checker guarantees and what [Join] enforces ("the loan/borrow structure must be identical in all arms").

**Resolution** ("end every borrow"). `fill(ℓ) := cv_Ω(holder(ℓ))[h_ℓ' := fill(ℓ')]` for the `ℓ'` occurring in it; this is well-founded because "the content of borrow ℓ contains hole ℓ'" is acyclic (I3). For an owner `o`, `ρ_Ω(o) := cv_Ω(o)[h := fill]`. `fill` substitutes into *every* occurrence of `h_ℓ`; with two borrow parameters and a returned borrow the hole occurs twice (C2), and resolution handles that without comment.

So an environment with abstract values `σ̄` means: in context `Γ_Ω`, a tuple of CIC terms `cv_Ω` over the hole variables, and a map `ρ_Ω` from that tuple to the owners' final contents.

### 1.5 Values, and why the [Close] equations are definitions

```
⟦Z⟧ = 0     ⟦S v⟧ = succ ⟦v⟧     ⟦()⟧ = ⋆     ⟦(v, w)⟧ = (⟦v⟧, ⟦w⟧)     ⟦σ⟧ = σ     ⟦?k⟧ = h_k
⟦⌈t⌉⟧ = Run(t) := π₁ (⟦t⟧_∅ ⋆)           the result of the closed program t, run from the empty environment
⟦n v⟧ = π₁ (⟦n⟧ ⟦v⟧)                      stuck application of an abstract function
⟦closure⟧ = the CIC function of §1.6, with the captured values substituted
proof values ↦ their CIC proofs (all equal);  type values ↦ their translation
```

Unfolding `Run` and the call clause of §1.6 (δβζ only) gives, for `L = let cᵢ = uᵢ` and `C = f ā`:

```
⟦⌈L; C⌉⟧                        ≡  f_fwd ū w̄              the call's result
⟦⌈L; C; cᵢ⌉⟧                    ≡  f_backᵢ ū w̄            final content of the i-th borrowed place
⟦⌈L; let r = C; *r⌉⟧            ≡  f_fwd ū w̄              current content of the returned borrow
⟦⌈L; let r = C; *r := ?k; cᵢ⌉⟧  ≡  f_backᵢ ū w̄ h_k        final content of place i, awaiting the returned borrow's final value
```

So "the sealed program's value is the backward function's value" is not a rule the model has to validate: it is how the model reads a sealed program. What has content is that the *machine* puts these values into the loans, i.e. that the real run of the call agrees with them. That is T2b and T5.

### 1.6 Terms: state passing

A run `Ω ⊢ t ⇓ v : A ⊣ Ω'` fixes an input shape `S = S_Ω` and an output shape `S' = S_Ω'`. Write `⟦S⟧` for the product of the current-view types of `S`'s bindings; then `⟦t⟧_S : ⟦S⟧ → ⟦A⟧ ⊗ ⟦S'⟧`. With `s` a current view and `s.y` its component for binding `y`:

```
read p (copy)             λs. (s.p, s)
read p (move a borrow)    λs. (s.p, s ∖ p)                               the borrow's content travels in the result
&p                        λs. (s.p, s[p := h_ℓ])                          ℓ fresh; the result is the borrow, its view s.p
p := t                    λs. let (v, s₁) = ⟦t⟧ s in (⋆, s₁[p := v])
let x = t; u              λs. let (v, s₁) = ⟦t⟧ s in drop_x (⟦u⟧ (s₁ + {x ↦ v}))
match p {Z ⇒ t | S y ⇒ u} λs. natCase (s.p) (⟦t⟧ s[p := 0]) (λσ'. ⟦u⟧ s[p := succ σ'])     y names the σ' position
end ℓ  ([Reorg])          λs. s[h_ℓ := s.holder(ℓ)] ∖ holder(ℓ)                              a substitution
f ā,  B borrow-free       λs. let (r, fin) = F ū w̄ in (r, (s ∖ args)[h_ℓᵢ := finᵢ])
f ā,  B = &T'             λs. let (c₀, back) = F ū w̄ in (c₀, (s ∖ args)[h_ℓᵢ := backᵢ h_k])     k fresh; the result is borrow k, its view c₀
```

In the call clauses `F = ⟦f⟧`, `ū` are the current contents of the borrow arguments (loans `ℓᵢ`) and `w̄` the owned arguments. The two call clauses are Aeneas's T-Call-Forward and T-Call-Backward (Aeneas Fig. 9) fused into one CIC application: the region abstraction `A(ρ)` is the substitution `h_ℓᵢ := backᵢ h_k`, and ending it is substituting for `h_k`. `drop_x` ends `x`'s borrow (a substitution) or, for an owned `x`, relies on the checker having ensured it holds no loan. An anonymous pending borrow is an ordinary binding of `s` whose view contains hole variables.

`fix f (x̄ : Ā) : B := t` with recursive position `j` is `Nat.rec` on the entry content `dⱼ`, the recursive calls being at the strict subterms that the guard (C3) certifies. A checked function is `λd̄. finish(⟦t⟧ cv_{E(d̄)})`, where `finish` pairs the result with the ghosts' final contents `ρ(xᵢ°)`, which is `Fin`; for a returned borrow `k` it pairs `c₀` with `λh_k. (ρ(xᵢ°))ᵢ`. [Join] has one output shape by construction; its output view is the `natCase` of the arms' views (§3.7 says why its fresh variables are sound).

### 1.7 Observation and `Id`

`obs_W(Ω, t) = (v, ρ_Ω'(o))_{o ∈ W}` where `⟨Ω, t⟩ ⇓ ⟨Ω', v⟩` runs on its own copy of `Ω`, and `W = W(t, u)` is RULES §4's footprint with "owner" read as *all* owners (C2). Then

```
⟦Id A t u⟧_Ω  =  ( ⟦obs_W(Ω, t)⟧  =  ⟦obs_W(Ω, u)⟧ )      in ⟦A⟧ × ∏_{o ∈ W} ⟦T_o⟧
```

Both observations start from the same `Ω`, independently; the model has no sequential reading (breaker-frame's point 10 is therefore a spec clarification the model forces).

Proof irrelevance is a property of *values* of `Prop` type, never of computations. `Id P t u` with Prop-typed computations still observes their effects: with `Seven = λ(x : &Nat). (*x := 7; ⟨⟩)`, `Id ⊤ (Seven &a) ⟨⟩ ≡ Eq Nat 7 σ_a`, never `⊤`. RULES gets this right (P1 compares normal forms), but an implementation that compared Prop-typed *terms* by irrelevance before running them, as Lean's checker would, is inconsistent. C1 is the same phenomenon one level up, at function types.

### 1.8 The examples, in the model

```
⟦AddM⟧ : Π(d y : ℕ). 𝟙 ⊗ ℕ
⟦AddM⟧ 0 y        = (⋆, y)
⟦AddM⟧ (succ d) y = let (r, f) = ⟦AddM⟧ d y in (r, succ f)                   so AddM_back d y = d + y

⟦AddMZero⟧ : Π(d : ℕ). ((⋆, AddM_back d 0) = (⋆, d)) ⊗ ℕ
⟦AddMZero⟧ 0        = (refl, 0)
⟦AddMZero⟧ (succ d) = let (e, f) = ⟦AddMZero⟧ d in (cong (λp. (⋆, succ p.2)) e, succ f)

⟦TailM⟧ : { F : Π(d : ℕ). ℕ × (ℕ → ℕ) | ∀d. injective (F d).2 }
⟦TailM⟧ 0        = (0, λw. w)
⟦TailM⟧ (succ d) = let (c, b) = ⟦TailM⟧ d in (c, λw. succ (b w))             so TailM_back d w = d + w

⌈let c = σ; AddM &c 0; c⌉                    ↦  AddM_back σ 0
⌈let c = σ; let r = TailM &c; *r := ?k; c⌉   ↦  TailM_back σ h_k
```

`⟦AddMZero⟧`'s goal at `succ d` is `(⋆, AddM_back (succ d) 0) = (⋆, succ d)`, which ι-reduces to `(⋆, succ (AddM_back d 0)) = (⋆, succ d)`. The one cast in the model's proof is `cong` under the caller context `(⋆, succ □)`, and that is exactly what [App] does when it evaluates the codomain at the call site (T2c). `⟦AddMEq⟧` is the same with `AddM_back d y` against `TailM_back d y`. The Ochr proofs are bare structural recursion because Ochr's conversion performs this `cong`; the model's proofs are structural recursion plus one `cong` per recursive call, which is the congruence the environment does for free (01 §6).

## 2. The theorems

Standing assumptions: the fixes of §3 are in, and `Ω` is **well-formed**:

- **I1** (unique holder) each borrow `ℓ` is held by at most one binding;
- **I2** (holes) every `loan_ℓ` and every hole `?ℓ` refers to the one borrow `ℓ`; a hole may occur several times (C2), and all its occurrences are filled together; holes occur only in the continuation of a sealed program, never in its argument prefix `L`;
- **I3** (acyclic) "the content of borrow `ℓ` contains loan or hole `ℓ'`" is acyclic;
- **I4** (clean crossings) a value moved or copied out of a place, or passed as a call argument, contains no loan and no hole (C5).

### T0 Simulation (the workhorse)

**Statement.** If `Ω ⊢ t ⇓ v ⊣ Ω'` by the symbolic machine (lazy [Reorg], [Close], [Seal], refinements), then in context `Γ_Ω`, in intensional CIC_L,

```
⟦t⟧_{S_Ω} (cv_Ω)  ≡  (⟦v⟧, cv_Ω')
```

and the same holds for the concrete machine with `Γ = ∅`.

**Proof sketch.** Induction on the run. Reads, borrows and assignments are record projections and updates; `end ℓ` is the substitution of its clause; `match` on a constructor is ι; a call that unfolds is δβ, then the IH on the body, then [Pop] (substitutions). [Close] with a borrow-free result: the machine restores `Ω` to the call point, fills `loan_ℓᵢ` with `⌈L; C; cᵢ⌉` and returns `⌈L; C⌉`; by §1.5 these denote `f_backᵢ ū w̄` and `f_fwd ū w̄`, which is what the call clause produces. That the machine does not unfold is harmless, because `F ū w̄` is one CIC term whether or not it reduces. [Seal]: `Run(t) ≡ ⟦v⟧` by the IH on `t`'s run; the Unit collapse is η on `𝟙`. Refinement: `⟦-⟧` commutes with substitution (every clause is compositional and `σ` is a variable), then [Seal].

**Hardest case:** [Close] with a returned borrow, followed later by `end k`. After the call, `cv` holds `backᵢ h_k` at the loans and the result is borrow `k` with view `c₀`; the caller may write `w` through `k` and then end it, which in the model substitutes `h_k := w`. The machine instead substitutes `?k := w` into the sealed programs and re-runs them. They agree because `Run` is compositional: `Run(t)[h_k := w] ≡ Run(t[?k := w])`. This needs the hole to be an inert variable while the sealed program runs (§3.5); if `?k` were a loan, re-running the sealed program would try to end borrow `k`, which lives outside the sealed program.

### T1 Canonical observation

**Statement.** Let `Ω` be well-formed. (a) Every maximal sequence of `end` steps from `Ω` gives the same environment up to renaming, and the owners' contents in it are `ρ_Ω` (after normalisation). (b) If `⟨Ω, t⟩` runs successfully under any [Reorg] schedule the rules allow (loans ended at any time, including eagerly) to `⟨Ω₁, v₁⟩`, and under the lazy schedule to `⟨Ω₂, v₂⟩`, then `v₁ = v₂` and `ρ_Ω₁ = ρ_Ω₂`. Hence `obs_W` does not depend on the order in which loans are ended.

**Proof sketch.** (a) Two enabled `end` steps commute: `end ℓ` is enabled only when borrow `ℓ`'s content holds no loan or hole, so it does not contain `h_ℓ'`, and the two substitutions touch disjoint positions. Each step removes a borrow, so the system terminates, and Newman's lemma gives a unique normal form. In the model it is just that `ρ_Ω` is one composite substitution. (b) Simulation: suppose the eager run ends `ℓ` at point A and the lazy run at point B (a demand or a drop). Between A and B the eager run cannot use borrow `ℓ` (it would read `⊥` and fail), so the content that lands is the same at A and at B; and nothing can write the loan position in between, because its container is loaned and any access to it makes the lazy run end `ℓ` first. So both runs substitute the same term for `h_ℓ`.

**Hardest case:** a hole `?k` inside a sealed program. Ending `k` substitutes and then *re-normalises* the sealed program, so (a) needs "substitute, normalise, substitute, normalise" to equal "substitute both, normalise": naturality of the normaliser under `h_k := w`, which is T5. The canonicity theorem 01 §8 calls the most important in the design reduces, in its only non-trivial case, to adequacy. Two fixes are also ingredients: every occurrence of `?k` must be filled (C2: a single-owner implementation leaves the other occurrence dangling once `borrow_k` is gone, and resolution is undefined), and every access must end the loans *inside* the accessed content (C5: otherwise a moved value carries a live loan across a frame and I4 fails). With those, I found no counterexample; without them, T1 is not even well-posed.

### T2 Frame

**(a) Locality.** Let `Ω = Ω₁ ⊎ Ω₂`, where every variable free in `t` is bound in `Ω₁` and every loan or hole *occurring in `Ω₁`* has its holder in `Ω₁` (`Ω₁` is *loan-closed*; a holder in `Ω₁` of a loan in `Ω₂` is fine, because borrowed content lives in the borrow). Then `⟨Ω, t⟩ ⇓ ⟨Ω', v⟩` iff `⟨Ω₁, t⟩ ⇓ ⟨Ω₁', v⟩` with `Ω' = Ω₁' ⊎ Ω₂`, with the same [Close] steps and identical sealed programs. *Proof:* induction on the run. Every rule touches only places reachable from `t`'s free variables (P5: no globals; closures capture borrow-free values), [Reorg]'s search for `borrow_ℓ` succeeds inside `Ω₁` by loan-closedness, and sealed programs are closed.

**(b) Call frame.** At a call `f ā`, the callee's initial frame `[x̄ ↦ w̄]` is loan-closed (I4). By (a) the callee runs as if alone, and its only effects on the caller are filling the loans `ℓᵢ` of the borrow arguments at [Pop] and, when it returns a borrow, one anonymous pending binding. So the caller's view after the call is the call clause of §1.6 with `F = ⟦f⟧`, and when the body is stuck, [Close]'s sealed programs denote the same `F ū w̄`. In one sentence: *the effect of a call on its caller is a function of its argument values* (P5 made precise). This is what [Close] rests on.

**(c) Observation frame (what [App] rests on).** At a call site `Ω`, let the borrow arguments have loans `ℓ̄` and let `O` be the set of **all** owners of `ℓ̄` in `Ω`. For every `Id`-atom `Id A t u` in the codomain `B`, with callee-side footprint `W` (containing the ghosts `xᵢ°`) and caller-side footprint `W'` (each `xᵢ°` replaced by the owners of `ℓᵢ`):

```
⟦obs^caller_W'(t)⟧  =  Ctx( ⟦obs^callee_W(t)⟧ ),        Ctx(v, f̄, r̄) = (v, (C_o f̄)_{o ∈ O}, r̄)
```

where `C_o` is owner `o`'s resolution context around the final contents `f̄` of `ℓ̄`, and `r̄` are the other components. `C` is the same for `t` and for `u`: both run from `Ω` and, by (a), change nothing outside `ℓ̄`. If `Ctx` is jointly injective, then `⟦obs^caller t = obs^caller u⟧ ↔ ⟦obs^callee t = obs^callee u⟧`, and by `propext` and congruence, `⟦B@caller⟧ = ⟦B⟧(ū)`.

**Lemma Inj.** In the model, every such resolution context is jointly injective. *Proof:* it is built from constructors and from backward functions applied at their hole argument. Constructors are injective; backward functions are jointly injective (for abstract functions by the subset of §1.3, for definable ones by BackInj); composition preserves injectivity. The components for owners that do not contain the hole are constant, so joint injectivity holds only if the owner that does contain it is included, which is why `W'` must contain every owner (C2).

**Lemma BackInj** (fundamental lemma of the injective relation). For every well-typed `f : Π(x̄ : Ā). &T'` and all `d̄`, `π₂ (⟦f⟧ d̄)` is jointly injective. *Proof:* induction on the typing derivation of `f`'s body, with the invariant that in the output view the returned borrow's hole `h_k` occurs in jointly injective position across the ghosts' resolutions. The returned borrow is a parameter, or a reborrow of a sub-place of one parameter's content (`h_k` sits under constructors), or a borrow returned by an inner call on such (`h_k` sits at the hole argument of that call's backward function: IH, or the subset for an abstract callee). A `natCase` of injective maps is injective pointwise. Nothing in v0 can discard a returned borrow's final value: [Pop] keeps a borrow whose content still holds a loan as a pending binding instead of dropping it, and writing a place ends the loans inside it first (C5).

**Hardest case of T2:** (b) with a returned borrow. The callee's parameter borrow cannot end at [Pop] (its content still holds the returned borrow's loan), so it crosses into the caller's frame as a pending binding, and the callee's effect on the caller is a value with a hole: a function of something the caller has not produced yet. The frame boundary moves, so (a)'s static separation does not cover it. And (c) inherits the difficulty: injectivity is a property of the backward function, i.e. of the whole future of the borrow, which is why it takes a logical relation and cannot be read off `Ω`.

### T3 Typing and conversion are preserved

**Statement.** (a) *Types.* If `A` is a type at `Ω` with normal form `A↓`, then `Γ_Ω ⊢ ⟦A↓⟧ : ⟦s⟧` for its sort `s`. (b) *Conversion.* If `Ω ⊢ A ≡ B` (same normal form up to α, D6, proof irrelevance on values, η on Unit), then `Γ_Ω ⊢ ⟦A⟧ ≡ ⟦B⟧` in ECIC_L; equivalently `⟦A⟧ = ⟦B⟧` is provable in CIC_L. (c) *Typing.* If `Ω ⊢ t ⇓ v : A ⊣ Ω'`, then `Γ_Ω ⊢ ⟦t⟧_{S_Ω} : ⟦S_Ω⟧ → ⟦A⟧ ⊗ ⟦S_Ω'⟧`, with value `(⟦v⟧, cv_Ω')` at `cv_Ω` (T0). For a checked definition `f : Π(x̄ : Ā). B`, `⊢ ⟦f⟧ : ⟦Π(x̄ : Ā). B⟧`, including membership of the injective subset when `B` is a borrow.

**Proof sketch** (induction on derivations; the cases that are not bookkeeping):

- [Lam]: `λd̄. finish(⟦body⟧ cv_{E(d̄)})`, whose type is `⟦B⟧(d̄) ⊗ Fin` by the definition of `E(d̄)`: the entry snapshot is literally the codomain of the CIC Π.
- [Split] on `σ`: dependent `natCase` on the CIC variable `σ`, with a motive that abstracts `σ` in the goal and in every stored type. "Apply the refinement to Ω, to the goal and to every stored type" *is* that motive. Because `σ` is a variable, this is plain CIC dependent elimination, and the fire triangle does not bite (§4).
- [Join]: `(λσ̄ⱼ. ⟦continuation⟧) (natCase σ (arm values))`. The continuation is checked generically in the fresh `σ̄ⱼ`, so it is a CIC function of them, applied to the precise joined values. Sound for any continuation, provided the goal and stored types after the join are the *pre-split* ones. e346's reading J1 (stored types taken from an arm, F2) violates that and is unsound; the model says why: a type refined inside an arm holds only in that arm.
- D6: instances of `propext`: `(succ a = succ b) = (a = b)`, `(0 = succ b) = False`, `(p = q in 𝟙) = True`, `(True ∧ P) = P`, `((a, b) = (a', b')) = (a = a' ∧ b = b')`. e346's proposed `Eq A a a ≡ ⊤` is also `propext` (`(a = a) = True`), so the model accepts it.
- Proof irrelevance: definitional in CIC_L, applied to values of `Prop` type only; after C1 every Ochr `Prop` translates to a CIC `Prop`, so this is sound.
- [App] at `f ā : B@caller`: `F ū w̄ : ⟦B⟧(ū)`, cast to `⟦B@caller⟧` along T2c. For a recursive call inside `fix`, `F` is the recursor's induction hypothesis at a strict subterm (C3).
- [Close], [Seal] and refinement inside types: T0, since the values in types are computed by the same machine.

**Hardest case:** [App]. It needs, at once: T2b (the callee's effect is `F ū w̄`); T2c (the caller's observation is the callee's under an injective context); Lemma Inj, hence the multi-owner footprint (C2) and the injective subset for abstract functions; `propext`, to turn the equivalence into an equality of types; the guard (C3) so that the induction hypothesis exists; and C4: [App] must evaluate `B` with *only the parameters* rebound, every other free variable of `B` taking its value from the Π-type's formation, or `⟦B@caller⟧` is not an instance of `⟦B⟧` at all (e346's `Oops2`).

### T4 Consistency

**Statement.** No closed Ochr term has type `⊥`; in particular none has type `Id Nat Z (S Z)`. More strongly, every closed proposition with a closed Ochr proof is true in Carneiro's set model.

**Proof.** By T3 a closed `t : ⊥` gives `⊢ ⟦t⟧ : False ⊗ 𝟙` in ECIC_L. ECIC_L has a model in ZFC with ω inaccessible cardinals (theory-of-lean §6.2–6.3): reflection holds because `⟦a = b⟧ ≠ ∅` forces `⟦a⟧ = ⟦b⟧`; `propext` holds because a proposition is a subset of `{•}`; the injective subsets are sets. `⟦False⟧ = ∅` has no element. With only `Prop : Type₀ : Type₁`, one inaccessible suffices. `Type : Type` must be excluded (Girard); RULES lists the sorts `Prop | Type` without saying what `Type` has type, which needs one sentence.

C1, C2 and C4 break even the narrow form (each gives a closed proof of `⊥`); C3 breaks only the stronger one. e346's `Bot' : Π(n : Nat). ⊥` is a closed proof of a proposition that is false in the model, even though, in the literal big-step reading, every closed instance makes the checker diverge, so no closed `⊥` is derivable from it. Consistency that survives only because the checker loops is not a property worth claiming; the model is what makes the claim robust.

### T5 Adequacy: the normaliser is natural

**Statement.** Let `nf` be the type-level normaliser (the machine with close-off, no [Join]). A *refinement* `α` substitutes constructor patterns for abstract values, values for holes, or definable closures for abstract functions. (a) For every term `t` at `Ω` whose value is borrow-free (in particular every observation, hence every `Id`), `nf_{Ω·α}(t·α) = nf(nf_Ω(t)·α)`. (b) If `α` is ground, the concrete run of `t·α` terminates, and its value (for an observation: its tuple) is `nf(nf_Ω(t)·α)`.

**Proof sketch.** Induction on the symbolic run of `t`. Every step but [Close] commutes with `α` on the nose. At a [Close] step on the call `C = f ā` with argument contents `ū`, the refined run reaches the same call with arguments `ū·α` and runs `f`'s body in a fresh frame; re-normalising the sealed programs `⌈L; C…⌉·α` runs the same body on the same argument values in its own fresh frame; by T2a and determinism the two runs agree, including where (and whether) they get stuck. With a returned borrow the two runs pass through environments of different shapes (next paragraph), which is why (a) is stated for borrow-free results: the observation resolves every borrow, and by T1 the resolutions agree. Termination for (b) comes from the guard (C3). There is also a proof of (b) through the model: by T0, `⟦t·α⟧(cv·α) ≡ ⟦nf(t·α)⟧` and `⟦t⟧(cv)·α ≡ ⟦nf t⟧·α`; the left sides are equal because `⟦-⟧` is compositional; both right sides are closed CIC terms of first-order type (and, for programs that do not transport data along proofs, contain no `propext` casts), and CIC_L is Church–Rosser up to proof irrelevance (Carneiro Thm 4.7), so they have the same numeral or tuple normal form.

**Hardest case:** [Close] with a returned borrow, under an `α` that lets the call run to completion. The concrete run of `t·α` returns a borrow *into the argument's content* and leaves the parameter's borrow as a pending binding whose content holds the returned borrow's loan; `nf(t)·α` instead has `borrow_k c₀` and sealed programs holding the hole `?k`, which now re-normalise to values like `S ?k`. Different shapes, same resolution. A direct proof needs a simulation relation that pairs the pending binding with the filled sealed programs; this is the same object as T1's and T2b's hardest cases, and the place a mechanisation should start.

What fails naturality is informative. [Join] is not natural: after `match b {Z ⇒ () | S _ ⇒ ()}` the place `b` holds a fresh `σⱼ`, and refining the original `σ_b` does not bring the value back; so [Join] must stay out of type-level evaluation, as RULES already has it. Non-structural recursion is not natural: `Loop`'s call closes off while its argument is abstract and diverges once it is instantiated, so the naturality square has no bottom-right corner (C3). And C1 is a failure of substitution at function types: `P₁ ≡ P₂`, yet substituting them for an abstract `h` gives normal forms that are not convertible.

## 3. RULES v0, rule by rule, in the model

### 3.0 Verdicts

| Rule | Verdict in the model | Where |
|---|---|---|
| [Reorg], lazy ending | validated (T1), given C5 and holes-as-variables | T1, §3.5 |
| [Read], [Borrow], [Assign] | incomplete: undefined or frame-breaking when the content holds a loan inside it; fix C5 | §3.5 |
| [Let], [Match], [Pop] (incl. pending bindings) | validated | T0, T2b |
| [Close], borrow-free result | validated, definitionally (δβζ) | §1.5, T0, T2b |
| [Close], returned borrow (hole form) | validated, given holes as variables and all owners observed | §1.5, T0, §3.2 |
| [Close], abstract function | validated, given the injective subset for returned borrows | §1.3 |
| [Seal] (with e1 F1's stop condition), Unit collapse | validated | T0 |
| Refinement re-normalises sealed programs | validated: it is naturality | T5 |
| Observation, footprint `W` | validated only with "all owners" (C2) and independent copies | §1.7, T2c |
| D6 `Eq` rules | validated, via `propext` | T3 |
| `Prop` proof irrelevance | **not validated** for a Π over a borrow parameter (C1) | §3.1 |
| [Lam] | validated | T3 |
| [Split] | validated: plain dependent elimination on a variable | T3 |
| [Join] | validated as generalisation if goal and stored types revert to their pre-split form; not natural | §3.7 |
| [App] | **not validated as written**: needs C2 and C4 | §3.2, §3.4 |
| §6 recursion check | **not validated** (C3) | §3.3 |
| sorts `Prop`, `Type` | `Type : Type` must be excluded | T4 |

### 3.1 C1: a Π over a borrow parameter is not a proposition (new)

Under CIC's sort rule for Π (codomain in `Prop` ⇒ Π in `Prop`; RULES states no other), `Π(x : &Nat). ⊤ : Prop`, and definitional proof irrelevance identifies all its values, including two with different effects.

```
P₁ : Π(x : &Nat). ⊤          P₁ x := ⟨⟩
P₂ : Π(x : &Nat). ⊤          P₂ x := *x := 7; ⟨⟩
F  : Π(h : Π(x : &Nat). ⊤). Prop
F h := Id Nat (let a = 0; h &a; a) 0
Boom : ⊥
Boom := J (λg _. F g) ⟨⟩ (refl : Eq (Π(x : &Nat). ⊤) P₁ P₂)
```

```
ε ⊢ J (λg _. F g) ⟨⟩ refl : ⊥                                            // J at A = Π(x : &Nat). ⊤, from P₁ to P₂
  ε ⊢ Π(x : &Nat). ⊤ : Prop                                               // Π rule: the codomain ⊤ is a Prop
  ε ⊢ refl : Eq (Π(x : &Nat). ⊤) P₁ P₂                                    // needs P₁ ≡ P₂
    P₁ ≡ P₂                                                               // definitional proof irrelevance: two values of one Prop
  ε ⊢ ⟨⟩ : F P₁                                                           // the motive at P₁
    F P₁ ≡ Id Nat (let a = 0; P₁ &a; a) 0                                 // β
      run: a ↦ 0; P₁ (borrow_0 0) returns ⟨⟩; [Pop] ends borrow_0, a ↦ 0; read a = 0; W = ∅ (a is local)
         ≡ Eq Nat 0 0 ≡ ⊤
  result type F P₂                                                        // the motive at P₂
    F P₂ ≡ Id Nat (let a = 0; P₂ &a; a) 0
      run: a ↦ 0; P₂ (borrow_0 0): [Assign] *x := 7, borrow_0 7; [Pop] ends it, a ↦ 7; read a = 7
         ≡ Eq Nat 7 0 ≡ ⊥
```

A second route needs neither `J` nor `Eq` at the Π-type, only proof irrelevance where [Seal] compares embedded values of a neutral:

```
Boom' : ⊥
Boom' := (λ(k : Π(h : Π(x : &Nat). ⊤). Nat). (refl : Eq Nat (k P₁) (k P₂))) (λh. let a = 0; h &a; a)
```

```
ε ⊢ Boom' : ⊥                                                             // [App]
  ε ⊢ λk. refl : Π(k : …). Eq Nat (k P₁) (k P₂)                           // [Lam], k ↦ σ_k
    k P₁ ≡ ⌈σ_k P₁⌉,  k P₂ ≡ ⌈σ_k P₂⌉                                      // abstract function: closes off at once
    ⌈σ_k P₁⌉ ≡ ⌈σ_k P₂⌉                                                   // embedded values P₁, P₂ of a Prop: irrelevant
    refl ✓
  codomain at k := (λh. let a = 0; h &a; a): Eq Nat 0 7 ≡ ⊥                // [App], same runs as above
```

`P₂` checks by [Lam] (goal `⊤` at entry; the body writes and returns `⟨⟩`). With a conversion checker that compares applications of the same head argument-wise before unfolding (Lean's `isDefEq` tries this first), `F P₁ ≡ F P₂` holds directly and `J` is not even needed. In the model, `⟦P₁⟧ = λd. (•, d)` and `⟦P₂⟧ = λd. (•, 7)` are different elements of `Π(d : ℕ). True ⊗ ℕ`, which is a `Type`.

**Minimal fix, two options.**
- (b) *Sort rule:* `Π(x̄ : Ā). B : Prop` only if `B : Prop` and no `Aᵢ` is a borrow type; otherwise `Type`. This is §1.3 read back into the source. Cost: theorems about borrows (`AddMZero`, `AddMEq`) live in `Type`; they are still usable as induction hypotheses and can be applied, but not put under `Prop`-only formers.
- (d) *Proof calls run on a private copy* (e346 F8): a call whose result type is a proposition does not affect its caller, and proofs are erased at runtime. Then `Out(d̄) = ⟦B⟧(d̄)` for `B : Prop`, the Π is a CIC `Prop`, and proof irrelevance is sound. On the counterexample, `P₂ &a` no longer writes `a`, so `F P₂ ≡ ⊤ ≡ F P₁`.

I recommend (d): it is one rule, it also fixes e346 F8 (the natural proof of `TwiceMZero`) and e1 N2 (the adequacy hole of a Prop-valued function that writes), and it makes the model simpler (proof-valued functions are ordinary CIC proofs). It is P2 ("terms in types run hypothetically") extended to proofs. (b) is the smaller textual change if the lead prefers to keep proofs operationally ordinary.

### 3.2 C2: with two borrow parameters and a returned borrow, the owner is a set (new derivation)

[Close] with result `&T'` fills *each* borrow argument's loan with a sealed program containing the same hole `?k` (e2 F4, e346 F11). RULES §4 speaks of "the owner" of a borrow. If the footprint observes one owner, [App] is unsound. Below, the rule picks `a`; if it picks `b`, swap `Pick`'s arms.

```
Pick : Π(n : Nat) (x : &Nat) (y : &Nat). &Nat
Pick n x y := match n { Z => x | S _ => y }

G : Π(z : &Nat). Π(e : Id Unit (*z := Z) (*z := S Z)). ⊥          -- the codomain is ⊥ → ⊥ at entry (W = {z°})
G z := λe. e

Bad : Π(n : Nat) (a : Nat) (b : Nat). Id Nat n Z
Bad n a b := let r = Pick n &a &b; let h = G r; match n { Z => refl | S m => h refl }
```

```
ε ⊢ Bad : Π(n a b : Nat). Id Nat n Z                                                      // [Lam]
  { n ↦ σ_n, a ↦ σ_a, b ↦ σ_b }, goal ≡ Eq Nat σ_n Z                                         // W = ∅
  let r = Pick n &a &b                                                                      // [Let], [App]
    arguments σ_n, borrow_2 σ_a (a ↦ loan_2), borrow_3 σ_b (b ↦ loan_3)
    Pick's body: match n on σ_n is stuck; [Close] with result &Nat, fresh k:
      r ↦ borrow_k ⌈L; let r' = Pick σ_n &c₁ &c₂; *r'⌉                     // L = let c₁ = σ_a; let c₂ = σ_b
      a ↦ A(?k) = ⌈L; let r' = Pick σ_n &c₁ &c₂; *r' := ?k; c₁⌉            // loan_2 filled
      b ↦ B(?k) = ⌈L; let r' = Pick σ_n &c₁ &c₂; *r' := ?k; c₂⌉            // loan_3 filled: ?k occurs twice
  let h = G r                                                                               // [App], at the call point
    type: Π(e : Id Unit (*z := Z) (*z := S Z)). ⊥ with z := r
      W' = the owner of borrow_k = {a}                                     // single-owner reading
      obs(*z := Z) = ((), A(Z)),  obs(*z := S Z) = ((), A(S Z))            // write through k, resolve: ?k := the written value
      ≡ Π(e : Eq Nat A(Z) A(S Z)). ⊥                                       // D6
  match n { Z => refl | S m => h refl }                                                     // [Split] on σ_n
    arm σ_n := Z: goal Eq Nat Z Z ≡ ⊤; refl ✓
    arm σ_n := S σ_m: goal Eq Nat (S σ_m) Z ≡ ⊥
      h's stored type, refined: A(w) re-runs Pick (S σ_m) &c₁ &c₂, which returns c₂'s borrow;
        *r' := w writes c₂; reading c₁ gives σ_a; so A(w) ≡ σ_a                                // refinement, [Seal]
      h : Π(e : Eq Nat σ_a σ_a). ⊥;  h refl : ⊥ ✓                                             // [App]
ε ⊢ Bad (S Z) Z Z : Id Nat (S Z) Z ≡ ⊥                                                       // [App]; the concrete run terminates
```

The typing of `G r` must happen before the split, while both `a` and `b` hold the hole; after `σ_n := S σ_m` the hole survives only in `b` and the owner is unambiguous. In the model, `W' = {a}` makes the context `Ctx = A(·)`, which is constant in the `S` branch, so T2c's equivalence fails: `⟦G⟧` proves `0 = 1 → False`, from which `σ_a = σ_a → False` does not follow.

**Minimal fix:** *the owners of a borrow are all owned places (variables not of borrow type, and ghosts) whose content contains its loan or its hole, directly or through the contents of other borrows; `W` contains all of them, and ending the borrow fills every occurrence of its hole.* With `W' = {a, b}`, `h : Π(e : Eq Nat A(Z) A(S Z) ∧ Eq Nat B(Z) B(S Z)). ⊥`, which in the `S` arm is `Π(e : ⊤ ∧ ⊥). ⊥`, and `h refl` is rejected. Lemma Inj shows this is enough in general: jointly, the owners' contexts are injective, because in each concrete run the returned borrow lands in exactly one parameter.

### 3.3 C3: the recursion check must measure the entry value (confirms e346 F6)

e346 F6 gives the bad derivation (`Loop`, `Bot' : Π(n : Nat). ⊥`, with a write before the inner match). The model says precisely what is missing: `⟦fix …⟧` is a CIC structural recursor on the **entry content** of the recursive argument, so the recursive call must be at a strict subterm of that entry value. §6's syntactic rule checks that the argument is a pattern variable of a match on the parameter's content, which is weaker in two ways: a write before the match (e346's `Loop`), and a write to the pattern variable after the match, which RULES' note does not mention:

```
Grow : Π(b : Nat) (x : &Nat). Id Unit (*x := Z) ()          -- "writing Z changes nothing": false
Grow b x := (match b { Z => () | S _ => () });               -- [Split]+[Join] leave b ↦ σⱼ, so recursive runs stop at once
            match *x { Z => refl | S p => (p := S p; Grow b &p) }
```

```
S arm (σ := S σ'): goal ≡ Eq Nat Z (S σ') ≡ ⊥                              // W = {x°}: ((), 0) against ((), S σ')
  p := S p: x ↦ borrow_0 (S (S σ'))                                        // p's content is now S σ', x's entry value
  Grow b &p: §6 ✓ (p is a pattern variable of a match on *x)
    type at the call point: W' = {x°}: ((), S Z) against ((), S (S σ')) ≡ Eq Nat Z (S σ') ≡ ⊥ ✓
    value: the callee's first match is on σⱼ, stuck; [Close]
```

**Minimal fix** (e346's, which the model confirms and makes exact): *at every recursive call, the content of the recursive argument (read through the borrow when the argument is `&p`) must be an abstract value `σ'` obtained from the recursive parameter's entry value `σ` by one or more refinements `σ := S σ'`; a join variable, a sealed program, or any other value is rejected.* This is CIC's guard condition applied to the translated program; it is decidable because the symbolic machine already tracks exactly these values, and it sees writes before and after matches alike. `AddM`, `AddMZero`, `AddZero`, `TailM`, `AddMEq` pass.

### 3.4 C4: a Π-type closes over values; [App] rebinds only the parameters (confirms e346 F5)

e346 F5 (`Oops2`) reads [App]'s "B evaluated at the call site, in the caller's environment" literally: a hypothesis `h : Π(_ : Unit). Id Nat x Z` is re-read after `x := S x`. In the model, a Π-type formed at `Ω` means `Π(d̄ : D̄). ⟦B⟧(d̄)` with every free variable of `B` other than the parameters fixed to its value at `Ω`; there is no CIC object that re-reads `x` later. So [App] is validated only in the form: *evaluate `B` with the parameters bound to the arguments, and every other free variable bound to its value when the Π-type was formed (Π-types are closures over values, like λ).* The caller's environment then contributes exactly one thing: the owners of the borrow arguments, through `W'` (T2c). The two readings of "at the call site" are different rules, and only the second is sound.

### 3.5 Gaps the proofs need (no bad derivation, but T1 and T2 fail without them)

- **C5, an access ends the loans inside what it accesses.** [Reorg] ends a loan when it is the accessed content "or a prefix of its path". It says nothing about a loan *inside* the content. Then [Read] of an owned value with a loan inside is undefined (it is neither borrow-free nor a borrow), moving a borrow whose content holds a loan carries a live loan into the callee (I4 fails, T2a's loan-closedness fails, and [Close]'s `L = let c = u` contains a live loan, so the "closed" sealed program is not closed), and [Assign] over such a content drops the loan (breaker-frame's point 1). Fix, one sentence: *an access to `p` (read, borrow, assign) first ends every loan and hole on `p`'s path and inside `p`'s content; [Match] needs only the path and the root.* This is Aeneas's `loan ∉ v` premises on E-Move, E-Copy and E-Mut-Borrow and "no outer loans" on E-Assign, implemented lazily as Aeneas §3.4 describes.
- **Holes are variables** (e2 F3). [Close] writes `loan_k` into a sealed program. [Seal] re-running that program would treat it as a loan and look for `borrow_k` outside the sealed program's own environment. The model needs `?k` to be a variable while the sealed program runs, and a loan from `Ω`'s point of view (reading a place whose content contains `?k` ends `k` first, by C5). Ending `k` substitutes every `?k` and re-normalises: the same operation as refinement, which is why T1's hole case is an instance of T5.
- **The call point** (e1 F6): [App] evaluates `B` in the environment after the arguments are evaluated and before the call runs. The model's `⟦B⟧(ū)` is at the entry contents `ū`; evaluating after the call would observe the callee's effects twice.
- **Matching on a neutral** in the checked term (e2 F10, e346 F10) is valid in the model as *generalise, then split*: replace the neutral by a fresh `σ` (in as many of its occurrences as the checker likes), then [Split]. In CIC this is dependent elimination with a generalised motive; generalising fewer occurrences loses completeness, never soundness.

### 3.6 D6, and the proposal to delete it

D6 is validated: each rule is an instance of `propext` (T3). The simplifier proposes deleting D6 because the borrow examples never use it. The model is indifferent: `propext` is needed for [App] anyway (T2c), so deleting D6 does not buy an intensional model, and keeping it costs no consistency. e346's `Eq A a a ≡ ⊤` is also valid (`(a = a) = True`). The decision is about the size of the rule set, not soundness.

### 3.7 [Join]

[Join] is sound when read as generalisation (T3): the continuation is a CIC function of the fresh variables, applied to the precise joined values, and the goal and stored types after the join are the pre-split ones. It is **not natural** (T5): once `b`'s place holds `σⱼ`, refining `σ_b` cannot recover it, so [Join] must never run inside type-level evaluation (RULES already restricts it to the checked term), and a join variable must never be accepted as a recursion argument (C3's fix covers this). e346 F1 proposes to replace anti-unification by closing off a stuck non-tail match as a nullary call over its free places. The model prefers that: the closed-off match is a sealed program whose value is the precise `natCase`, so it is natural, T5 then holds for checked terms as well as for types, and [Join] disappears into [Close]. That touches D7, so it is the lead's and the user's call; from the metatheory side it removes the only non-natural rule.

## 4. The fire triangle, and "thunkable = natural"

**Where Ochr sits.** Pédrot–Tabareau's no-go theorem: substitution, dependent elimination and observable effects together are inconsistent. Ochr has dependent elimination ([Split] refines `σ` in the goal and every stored type). It restricts substitution to values: typing is evaluation, call-by-value, and [App] binds a parameter to the argument's *value*; no computation is ever substituted into a type. That is the paper's call-by-value corner (§2.2 there). And Ochr has **no observable effects** in their sense (Def. 3: a closed boolean not observationally equal to a value): a closed program owns all its state (T2a with nothing outside), so by T5(b) it runs to a canonical value, and `C[t]` and `C[v]` agree for every context. Effects are observable only relative to *open* borrows, and state passing makes exactly those pure. So Ochr escapes the triangle twice over (breaker-frame's attack 6 reached the same place).

**The real connection is naturality.** In ∂CBPV's forcing model (P–T §10), a computation is a family over forcing conditions with restriction maps, and Proposition 18 says a computation is thunkable iff it is natural; the presheaf model of CIC is the thunkable part. Ochr's type-level normaliser is such a family. `nf_Ω(t)` is computed at a *condition* `Ω` (which abstract values exist, and what has been learned about them), and refinements `α` (constructor patterns for `σ`, values for holes, closures for abstract functions) are the restriction maps. [Split] is dependent elimination at a condition, with the type refined in lockstep, which is ∂CBPV's `dlet` (the type evaluates what the term evaluates). T5(a) is precisely the naturality square `nf_{Ω·α}(t·α) = nf_Ω(t)·α` (re-normalised). So "every type-level computation is thunkable" is Ochr's adequacy theorem, and T5 is the exact sense in which Ochr's types are effect-free although they run effectful programs.

This gives a usable criterion: **a rule may run inside type-level evaluation iff it is natural.** [Close] is natural, by the frame lemma (closing off at the innermost stuck call and discarding the partial run commutes with refinement). [Join] is not, so it must stay in the checked term, where the checker uses its output only generically. Non-structural recursion is not (C3): its naturality square has no corner. C1 is the triangle's *substitution* leg failing: `P₁ ≡ P₂`, yet substituting them into one type gives inequivalent types; fix (d) makes the identified values really equal, fix (b) stops identifying them. The injective subset of §1.3 is the analogue of P–T's `El`/`Θ`: a function space restricted to a semantic property that the source rules silently rely on (thunkability there, "a function gives back what it was given" here), just as Bowman et al.'s parametricity equation is thunkability seen through CPS.

**What this is not.** I have not built a ∂CBPV model of Ochr or proved that Ochr embeds in ∂CBPV. The claim is that P–T's characterisation is the right invariant, and that it predicts which rules fail. A full statement would take the category of symbolic conditions and refinements, read the normaliser as a presheaf on it, and derive T5 from Proposition 18. That would make a good section of the paper; soundness does not need it, since the CIC model of §1–2 already gives it.

## 5. What to mechanise in Lean 4, and how

The target of the model *is* Lean's type theory, so the model can be a **shallow embedding**: Ochr syntax and machines deep, their meaning a Lean function. That makes the novel part cheap and the standard part expensive.

**Realistic now (weeks), in this order, hardest first inside step 4:**

1. Syntax and the concrete and symbolic machines for the first-order effectful fragment (`Nat`, `Unit`, pairs, places, `&`, `:=`, `let`, `match`, n-ary `fix`, calls, [Close] in both forms, [Seal], refinement, holes as variables), as inductive big-step relations, plus a fuelled interpreter shared with the checker.
2. The shallow model: `Shape`, `View : Shape → Type`, `den : Term → View S → Val × View S'` into Lean, and `resolve`. First-order data only, so no object-level dependent types are needed.
3. **T0** (simulation), including both [Close] forms and [Seal]: this is the mechanical validation of the [Close] equations. Induction on the big-step derivation; the key lemma is `Run(t)[h_k := w] = Run(t[?k := w])`. Start with the returned-borrow [Close] followed by `end k`.
4. **T2a/T2b** (locality, call frame), needed by 3.
5. **T1** for the fragment: diamond and termination of `end` steps, invariance of `resolve`. A few hundred lines.
6. **T5** for first-order observations, as a corollary of T0: `den` is a Lean function, so the ground case is evaluation, and the square commutes by the substitution lemma.
7. **Lemma Inj / BackInj** for first-order functions and the D6 lemmas (`propext`, `Nat.succ.inj`). Small.
8. The counterexamples C1–C3 as regression tests in the executable checker: cheap and high value, independent of 1–7.

Rough size: 1 ≈ 600–900 lines, 2 ≈ 300, 3+4 ≈ 1500–3000, 5–7 ≈ 700. The Rocq development in `aeneas/` (Ho–Fromherz–Protzenko 2024) proves that LLBC♯ (symbolic) refines LLBC⁺ (concrete) without function calls, i.e. T5 without [Close]; its simulation relation is the template for T5's hardest case. It is in Rocq, so what transfers is the relation, not the proofs.

**Keep on paper (or long-term):** T3 and T4 for the dependent layer (Π over `Id`, impredicative `Prop`, universes, types as values, snapshots, [App] at the type level). Mechanising them needs a model of Ochr's *types* inside Lean: a universe of codes with an interpretation function (induction-recursion, which Lean lacks, encoded as an inductive typing predicate on codes plus a function), i.e. Lean4Lean/MetaCoq-scale work. A middle road is feasible in a month or two: T3 for a fixed stock of types (`Nat`, `Unit`, `×`, `Eq` at first-order types, Π with first-order domains, one `Prop` layer), which covers E1–E4. The ∂CBPV presentation of §4 stays on paper.

## 6. The theorems on one page

- **T0 Simulation.** A symbolic run `Ω ⊢ t ⇓ v ⊣ Ω'` implies `⟦t⟧(cv_Ω) ≡ (⟦v⟧, cv_Ω')` in intensional CIC_L. Hardest case: returned-borrow [Close] then `end k` (hole substitution commutes with `Run`).
- **T1 Canonical observation.** On well-formed `Ω` (I1–I4), `end` steps are confluent and terminating with result `ρ_Ω`, and any successful [Reorg] schedule gives the lazy schedule's value and resolution. Hardest case: a hole inside a sealed program, which reduces to T5.
- **T2 Frame.** (a) Loan-closed separation is preserved by runs. (b) A call's effect on its caller is `⟦f⟧ ū w̄`. (c) The caller-side observation of an `Id` in the codomain is the callee-side one under a context that is jointly injective (Lemma Inj, using BackInj and the injective subset), so `⟦B@caller⟧ = ⟦B⟧(ū)`. Hardest case: a returned borrow crossing the frame as a pending binding.
- **T3 Preservation.** Types, conversion (into ECIC_L, or as `propext` equalities in CIC_L) and typing are preserved; definitions land in the injective subset. Hardest case: [App].
- **T4 Consistency.** No closed proof of `⊥` (or of `Id Nat Z (S Z)`); every closed provable proposition is true in the set model, relative to ZFC with inaccessibles (one suffices without `Type : Type`, which must be excluded).
- **T5 Adequacy.** The type-level normaliser is natural under refinements, and ground instances run concretely to the instantiated normal form. Hardest case: returned-borrow [Close] when the refined call completes (different shapes, same resolution).

Dependencies: T2 gives T0's call case; T0 gives T3 and T5; T5 gives T1's hole case; T3 gives T4; the guard (C3) gives T3's recursors and T5's termination.

**Rules the model does not validate**, with the fix:

- **C1** (new) `Prop` proof irrelevance at a Π over a borrow parameter: closed `⊥` via `J` (§3.1). Fix: proof calls run on a private copy (= e346 F8), or such Π-types live in `Type`.
- **C2** (new derivation) the single-owner footprint, via [App] and [Close]'s duplicated hole: closed `Id Nat (S Z) Z` (§3.2). Fix: `W` observes all owners; ending a borrow fills every occurrence of its hole.
- **C3** (= e346 F6) §6's syntactic recursion check: `Bot' : Π(n : Nat). ⊥`, false in the model (§3.3). Fix: the entry-value guard.
- **C4** (= e346 F5) [App] re-reading a Π-type's free variables at the call site: closed `⊥` (§3.4). Fix: Π-types close over values; [App] rebinds only the parameters.
- **C5** (gap, no `⊥`) accesses must end loans inside the accessed content, and holes are variables (§3.5); T1 and T2 are not well-posed without them.
