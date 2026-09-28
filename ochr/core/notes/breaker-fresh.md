# breaker-fresh: fresh-eyes soundness attack on RULES.md v1.3

**Verdict:** v1.3 is inconsistent as written. There is a closed proof of `Eq Nat Z (S Z)` (F1), and a runtime borrow violation that the checker accepts, together with an accepted `Id` assertion that is false of the compiled run (F2).
**Most important finding (F1):** whether a term is erased ("is a type" or "is a proof") is decided from the *normal form* of its type. That decision changes when a parameter is instantiated. A call `W(&c, n) : U(n)`, where `U(n)` computes to the universe `Prop`, writes to `c` for real at the generic `n`, but is skipped at `n = Z`. [Call-type] re-evaluates a lemma's statement at `n = Z`, so a statement proved generically as `S Z = S Z` becomes `Z = S Z` at the instance.
**What must change:** (1) decide erasure once per definition, from its declared codomain at the generic call, and never re-decide it on an instance's normal form (F1). (2) Matching must end every loan inside a neutral at the head, or generalisation must refuse a sealed program that contains a live loan (F2). (3) Specify the normal form of a closure as the observation of its generic call, not the normal form of its body's result (F3). (4) Make [Rec] cover every `fix`, and say that `f` is unbound when `by` is omitted (F4).
**Confidence:** high for F1 under the literal P2 reading, and F2 needs no particular reading. For F3 and F4 the rules are silent, so these are unsound under a natural reading rather than under every reading.
**Not checked:** the Lean formalisation and any mechanised run (all derivations below are by hand), the paper's universe rules for Π and ×, the E3/E4/E6 regression suite, and the canonical-observation and adequacy proofs in `meta.typ`.

Method: I read BRIEF, RULES v1.3, both papers in full, and the paper sections `calculus`, `eval`, `typing`, `obs` and `overview`. Only after finishing the attacks did I read `DECISIONS.md` (see the end of this report). I did not read `notes/`.

Guiding observation. Fire-triangle reading: Ochr is call-by-value, so dependent elimination ([Split] on an abstract value) is sound and substitution is value-restricted. There are two places where Ochr substitutes something that is not a plain value, or where a decision depends on the substituted value. The first is *generalise-then-split*: a sealed program is abstracted to σ, which is sound only if the sealed program is thunkable, that is, it denotes a value that does not depend on future events. The second is anything that classifies a term by the normal form of its type. F1 and F2 are one example of each. Other attacks mostly bounce off a single structural fact: a type is a closed statement about values, and every lemma instance is an observation *of whatever state the checker holds*. An unfaithful checker state therefore yields true statements about the wrong state (F2), not false value-level statements. A false value-level statement needs either a conversion that identifies different values (F3) or a statement whose evaluation differs between the generic call and an instance (F1).

---

## F1. Erasure is not stable under substitution: closed proof of `Eq Nat Z (S Z)` (target 1)

P2 says that types and proofs are evaluated on a private copy, and the paper says the same of "a term whose type is a proposition, **or which is a type**". Whether a term *is a type* (its type is a universe) is a property of the *value* of its type, and a stuck type family can compute to a universe. Nothing needs cumulativity. `Prop : Type_0`, so a `Type_0`-valued family may return `Prop`.

```
U(n : Nat) : Type_0 := match n { Z => Prop | S _ => Prop }
V(n : Nat) : U(n)   := match n { Z => ⊤ | S _ => ⊤ }
W(x : &Nat, n : Nat) : U(n) := *x := S Z; V(n)
Lie(n : Nat) : Id Nat (let c = Z; W(&c, n); c) (S Z) := refl
Boom : Eq Nat Z (S Z) := Lie(Z)
```

**U.** At the generic call `n ↦ σ`, the match does a [Split]. In each arm, `Prop : Type_0` holds. Accepted.

**V.** The goal is [Call-type] `U(σ)`. U's body is stuck, so it is closed off as `⌈U(σ)⌉`. In the [Split] arm `σ := Z`, the goal re-normalises to `Prop` and `⊤ : Prop` holds; the `S` arm is the same. Accepted.

**W.** Generic call: `{c₀ ↦ σ_c}`, `x ↦ borrow₀ σ_c`, `n ↦ σ`. The goal is `⌈U(σ)⌉`.
```
*x := S Z                          [Assign]    x ↦ borrow₀ (S Z)
V(σ)                               [Call]      its type ⌈U(σ)⌉ is not (yet) a universe and not a proposition, so the call runs for real
  body stuck on σ                  [Close]     row "borrow-free D": result ⌈V(σ)⌉ (no borrow args)
result ⌈V(σ)⌉ : ⌈U(σ)⌉ ≡ goal                  W's own body is not stuck: the stuck call was an inner call
pop frame                          [Drop]      borrow₀ ends, c₀ ↦ S Z
```
Accepted.

**Lie.** At the generic call `n ↦ σ`, the goal is [Call-type]: evaluate `Id Nat t (S Z)` on a private copy, with `t = let c = Z; W(&c, n); c`. The footprint is W(t, u) = ∅, because `c` is bound inside `t`.
```
⟦t⟧: let c = Z                                   c ↦ Z
     W(&c, σ)                     [Call]         type [Call-type] = ⌈U(σ)⌉: neither a type-of-types nor a proposition, so it runs for real
        *x := S Z; V(σ) closed off; W returns    c ↦ S Z   (as in W's check)
     c                            [Read]         S Z
⟦S Z⟧ = S Z
Id Nat t (S Z) ≡ Eq Nat (S Z) (S Z) ≡ ⊤
```
`refl : ⊤`. Accepted.

**Boom.** Evaluate `Lie(Z)`'s [Call-type] with `n ↦ Z`:
```
⟦t⟧: let c = Z                                   c ↦ Z
     W(&c, Z)                     [Call]         type [Call-type] = U(Z), which normalises to Prop; the call IS A TYPE (its type is a universe), so by P2 it is evaluated on a private copy and discarded
     c                            [Read]         Z
Id Nat t (S Z) ≡ Eq Nat Z (S Z)
```
So `Lie(Z) : Eq Nat Z (S Z)`, a closed proof. Then `J(Nat, Z, S Z, P, Lie(Z), refl) : Π(Q : Prop). Q`, with the motive `P(m) := match m { Z => ⊤ | S _ => Π(Q : Prop). Q }`.

The same term also gives a checker/compiler disagreement (target 2). Take `Main(n : Nat) : Nat := let c = Z; W(&c, n); c`. A compiler cannot erase `W(&c, n)` when `n` is only known at runtime, so `Main(0)` returns 1. The checker's normal form of `Main(Z)` is `Z`.

**Variant on the proof half (applies only under a "shape" reading).** Use `Q(n : Nat) : Prop := match n { Z => ⊤ | S _ => ⊤ }` in place of U. Suppose "whose type is a proposition" is decided from the *shape* of the normal form of the type (`Eq`/`⊤`/`∧`/Π-into-Prop). Then `⌈Q(σ)⌉` is not recognised as a proposition, while `Q(Z) = ⊤` is, and the same four definitions (with V returning `refl`) give `Eq Nat Z (S Z)`. This variant is blocked only if propositionhood is read from the *sort* of the type (`Q(σ) : Prop` from Q's signature). That reading is stable under substitution only because Ochr, like Lean, has no `Prop ≤ Type_0` cumulativity. With cumulativity, `U'(n) : Type_0 := match n {Z => ⊤ | S _ => Unit}` breaks the proof half under every reading. RULES.md does not say whether universes are cumulative; it should say they are not, and that this is load-bearing.

**Principle implicated.** P2 is right that erased terms leave no trace. What is missing is a requirement that *which* terms are erased be invariant under substitution, both for refinement at a [Split] and for instantiation at [Call-type]. The existing rule "Π-types capture values" makes the *statement* a closure. But its evaluation re-decides erasure at each instance, and erasure is decided on normal forms, which is exactly the thing substitution changes. This is the fire triangle in miniature. The effect `*x := S Z` is observable, so the statement is not linear in `n`, and dependent elimination or instantiation desynchronises the type from the term. This is Pédrot–Tabareau's "desynchronisation between effects performed in the term and effects performed in the type".

**Minimal fix.** Decide erasure per *definition*, not per call.
- A call `f(ā)` is erased iff `f`'s codomain *as a term* is syntactically a sort (so `f` returns types), or has sort `Prop` (so `f` returns proofs). This is decided once at `f`'s generic call and reused at every instance. Under this rule `W`'s codomain `U(n)` is neither, so `W(&c, Z)` runs for real at every instance.
- The same applies to non-call terms: erasure follows the syntactic position of the term (type annotation, Π domain or codomain, the type slots of `Eq`/`Id`/`J`) and the declared sort. It never follows a normal form.
- A shorter equivalent: "a term is erased iff it is erased at its generic call". This mirrors how the goal is formed once at the generic call. It is the same move, and it is uniform with [Def].

Also state that universes are not cumulative.

---

## F2. Generalise-then-split abstracts a live hole: accepted program writes through an ended borrow (targets 2 and 3)

[Access] for *matching* ends only loans "on the path to p or as the head of content(p)". Reading, borrowing and assigning end loans anywhere inside the content. A sealed program with a hole, `H = ⌈…; *r := loan_k; c₁⌉`, has a *neutral* head, so `loan_k` does not count as "at the head". Yet the hole may *be* the head: when σ turns out to be `Z`, H is `loan_k` itself. [Split] then generalises H to a fresh σ_g. This deletes the only occurrence of `loan_k`, so the returned borrow is now orphaned: owners(k) = ∅, and ending it writes nowhere. (The paper's Figure caption for [Access] says "on the path to p or *inside its content*" for all four accesses, so RULES.md and the paper disagree here. With the paper's wording, F2 is blocked.)

```
TailM(x : &Nat) : &Nat by x := match *x { Z => x | S p => TailM(&p) }
Bad(x : &Nat) : Unit := let t = TailM(&*x); match *x { Z => (*t := S Z; let h : Id Nat (*x) Z = refl; ()) | S _ => () }
Main(n : Nat) : Nat := let c = n; Bad(&c); c
```

Check Bad at its generic call `{c₀ ↦ σ}`, `x ↦ borrow₀ σ`:
```
&*x                               [Access],[Borrow]  tmp ↦ borrow₁ σ, x ↦ borrow₀ loan₁
TailM(tmp)                        [Close] &T row     t ↦ borrow_k T,  loan₁ := H
                                                     T = ⌈let c₁ = σ; let r = TailM(&c₁); *r⌉
                                                     H = ⌈let c₁ = σ; let r = TailM(&c₁); *r := loan_k; c₁⌉      x ↦ borrow₀ H
match *x   (tail)                 [Access] match     path clean; head of content(*x) is H, a neutral, not a loan: nothing ends
                                  [Split]            H is not σ: generalise H ↦ σ_g everywhere; x ↦ borrow₀ σ_g; loan_k now occurs nowhere
  Z arm (σ_g := Z)                                   x ↦ borrow₀ Z, t ↦ borrow_k T (live)
    *t := S Z                     [Assign]           t ↦ borrow_k (S Z)
    Id Nat (*x) Z                 (private copy)     *x = Z, W = ∅, so ≡ Eq Nat Z Z ≡ ⊤;  h := refl  ✓
    trailing drops                [End k]            substitutes S Z for loan_k: no occurrences; c₀ ↦ Z
  S arm                                              () ✓
```
Bad is accepted, and so is `Main`: at the symbolic `n`, `Bad(&c)` is simply closed off.

Concrete run `Main(0)`:
```
c ↦ 0;  x ↦ borrow₀ 0;  &*x: x ↦ borrow₀ loan₁, tmp ↦ borrow₁ 0
TailM(tmp): Z arm returns x   t ↦ borrow₁ 0,  x ↦ borrow₀ loan₁
match *x: head of content(*x) IS loan₁   [Access] ends borrow₁: t ↦ ⊥, x ↦ borrow₀ 0
Z arm: *t := S Z                  reading ⊥: borrow error
```
The machine errors on a program the checker accepted. Compiled with pointers, `t` aliases `*x`: the match reads `0`, then `*t := 1` writes through the alias. So `h : Id Nat (*x) Z` is asserted at a point where the compiled program has `*x = 1` (target 3), and `Main(0)` returns 1.

**Why this is not a proof of False.** The goal is formed before `TailM` runs, so it never contains the hole. Every later statement is an observation of the checker's (orphaned-borrow) state. The frame property holds for any state, orphaned borrows included, so those statements are true value statements about the wrong state (h is literally `Eq Nat Z Z`). I tried to connect the broken state back to the goal through recursive-call types. That does not work: after generalisation everything the checker knows about `*x` is phrased in the fresh σ_g, which the goal cannot mention, and in the `Z` arm [Rec] forbids a recursive call because `Z` is not a subterm of σ.

**Principle.** Generalisation is substitution in reverse, so it is sound only for a term that is a value independent of the future (thunkable, in fire-triangle terms). A sealed program with a live hole is a function of a value that has not been decided yet. It is the same situation as trying to abstract a term that mentions a bound variable. A loan *is* a bound variable (RULES §2), and generalisation here escapes its binder.

**Minimal fix (either one).**
- (a) [Access] for matching: treat every loan occurring inside a neutral head as being at the head, and end its borrow. This is also what the paper already says.
- (b) [Split]: "a sealed program with a live loan in it is not generalised; end the borrows of its loans first".

(a) is one clause and uniform: the position of a loan inside a neutral is unknown, so it has to be treated conservatively. In the example, fix (a) ends `t` at the match, and `*t := S Z` is rejected, as it is in the concrete run.

Related underspecification. RULES never says what [Seal] does when a run *errors* rather than getting stuck. "Otherwise it is the sealed program" leaves `⌈let c₁ = Z; Bad(&c₁); c₁⌉` as a neutral Nat, which [Split] can then generalise. I could not turn this into False: every provable statement about it is a ∀-instance, and the model can send an erroring program to an arbitrary value. It does falsify adequacy for accepted programs, and together with F2 it produces accepted programs whose concrete normal form does not exist. RULES should say: an error during normalisation is a type error at the point that triggered it.

---

## F3. Conversion of closures is unspecified; the literal P1 reading proves `Eq Nat (S Z) Z` (target 1, conditional)

P1 says definitional equality is "same normal form, normal forms being what the machine produces on symbolic inputs". For a function value, the Lean-style normal form is its body normalised under a fresh variable. Read literally, "what the machine produces" is the body's *result value*, and the final environment is not compared. Two effectful functions with equal results are then convertible:

```
F := fix _ (x : &Nat) : Unit := *x := S Z
G := fix _ (x : &Nat) : Unit := ()
P := fix _ (h : Π(x : &Nat). Unit) : Prop := Id Nat (let c = Z; h(&c); c) Z
Boom3 : Eq Nat (S Z) Z := J(Π(x:&Nat).Unit, G, F, P, refl, refl)
```
- Normal forms: `F` applied to a fresh abstract borrow gives `()`, and so does `G`. So `F ≡ G`, `Eq (Π…) G F ≡ ⊤`, and the first `refl` checks.
- P's generic check: `h ↦ σ_h`. `σ_h(&c)` has a neutral head, so it is closed off: `c ↦ ⌈let c₁ = Z; σ_h(&c₁); c₁⌉`. The body is a Prop. ✓
- `P(G)`: re-normalising gives `c = Z`, so `Eq Nat Z Z ≡ ⊤`. The second `refl : P(G)` checks.
- J's result type `P(F)`: re-normalising gives `c = S Z`, so the result is `Eq Nat (S Z) Z`.

This is not the known "proof irrelevance at Π over a borrow" attack. There, the identification came from Prop's irrelevance, and the private copy fixes it. Here both functions are relevant (`Unit` is a Type), and the identification comes from how conversion treats function values.

**Blocked if** closures are compared syntactically (code plus normalised captured values), which is sound but incomplete, or by the observation of their generic call. **Fix:** say in §3 that the normal form of a closure is its [Def]-style generic call observed as `Id` observes it: the result together with the final contents of the generic owned places `cᵢ`, plus the captured values. This is uniform with [Def] and `Id` (one notion of "what a computation is"), and it keeps "no pure/impure divide", since a function's effects are part of its normal form. The same applies to Π-types, where it is harmless because codomains are statements, and to the head of a sealed program.

---

## F4. [Rec] has a scope hole: `fix` without `by` (target 1, conditional)

[Rec] constrains only "the body of `fix f … by xⱼ`". The syntax still names `f` when `by` is omitted, and "(omitted: non-recursive, i.e. λ)" states an intent, not a rule. If `f` is bound in its own body:

```
Loop := fix f (x : Nat) : Eq Nat Z (S Z) := f(x)
Boom4 : Eq Nat Z (S Z) := Loop(Z)
```
[Def]: generic `x ↦ σ`, goal `Eq Nat Z (S Z)`. The body `f(σ)` has [Call-type] `Eq Nat Z (S Z)`, which equals the goal. [Rec] is not triggered. The call is a proof, so it is never run and nothing loops at runtime to reveal the problem. The same hole opens for a nested `fix g` without `by` inside another function.

**Fix:** one sentence. "Without `by`, `f` is not in scope in the body (nor in `Ā`, `B`)". Also say whether `f` is in scope in its own statement `B`. I found no exploit when it is, because [Call] never evaluates `B`, so `f(x)` in `B` only ever runs `f`'s body, which is checked. Still, `Π`-types mentioning the function being defined have no counterpart in Lean, and the paper should rule them out rather than rely on this accident.

---

## F5. Stuck-block captures ignore writes through pattern variables: closed proof of `Eq Nat (S Z) (S (S Z))` (target 1, under the literal capture rule)

The capture rule classifies the block's *free places* by how they appear: "under `&_` or left of `:=`". A match's pattern variable `p` is *bound* by the block, yet it denotes the sub-place `(*x).1` (RULES §1: "y is the sub-place p.1, not a copy"). Read literally, the parenthetical never sees `p := Z` as a write to `*x`, so `*x` is captured by copy and the write lands in the anonymous function's private copy.

```
Clear(x : &Nat) : Id Unit (match *x { Z => () | S p => p := Z }) () := refl
Boom5 : Eq Nat (S Z) (S (S Z)) := let c = S (S Z); Clear(&c)
```

**Clear at its generic call** `{c₀ ↦ σ}`, `x ↦ borrow₀ σ`. W = owners(ℓ₀) = {c₀}, because x is a borrow-typed variable.
```
⟦match *x {…}⟧: head σ, stuck outside any call  → stuck block F of its free places
    free places {*x}: not moved, not under &_ or left of := (only p is), matched/read  → copied
    F(σ): body stuck → [Close], no borrow args, Unit row → ()          Ω unchanged
    end all borrows: c₀ ↦ σ                                           ⟦t⟧ = ((), σ)
⟦()⟧ = ((), σ)
Id ≡ Eq (Unit × Nat) ((), σ) ((), σ) ≡ ⊤          refl ✓
```
**Boom5.** Evaluate [Call-type] of `Clear(&c)` at `c ↦ S (S Z)`, `x ↦ borrow₁ (S (S Z))`:
```
⟦t⟧: match *x: head S, NOT stuck, runs directly: p = (*x).1; p := Z   x ↦ borrow₁ (S Z); end: c ↦ S Z
⟦()⟧: c ↦ S (S Z)
Clear(&c) : Eq (Unit × Nat) ((), S Z) ((), S (S Z)) ≡ Eq Nat (S Z) (S (S Z))
```
The type of the `let` is this closed statement, so it is a closed proof, and J turns it into False as in F1.

The same gap in the footprint: `Id Unit (match c { Z => () | S p => p := Z }) ()` with `c` owned has W = ∅ under the literal rule. It is ⊤ by `refl` although it rewrites `c` (target 3). I found no route from that alone to False, because both the generic statement and its instances then observe nothing.

**The pattern shared by F1 and F5.** A lemma's statement is evaluated along *two different paths*. At the generic call it goes through the closing-off machinery: stuck blocks, sealed programs, erasure decided on a stuck type. At an instance it runs directly. [Call-type] then equates "true at generic" with "true at the instance". *Every* lossy or classification step on the closing-off path is therefore an inconsistency. The metatheory item "refinement commutes with closing off" (H6) has to cover stuck blocks, their captures, and the erasure decision, not only [Close] of named calls, and it has to cover instantiation at [Call-type] as well as refinement at [Split]. I would make it the first lemma the Lean development proves, because it is exactly the lemma all three of F1, F5 and the known "proof block" attack violate.

**Fix.** Before captures and footprints are computed, resolve every pattern variable to the place it denotes (`p ↦ (*x).1`), then take maximal prefixes. `Clear`'s block then captures `*x` by `&`, [Close] fills `loan₀` with `⌈let c₁ = σ; F(&c₁); c₁⌉`, the generic goal becomes `Eq Nat ⌈…⌉ σ`, and `refl` no longer checks. "As Rust infers closure captures" already implies this, since Rust sees a mutable use of the scrutinee. The parenthetical contradicts it and should be deleted or corrected.

---

## Attacks that are blocked (with the rule that blocks them, and whether the block is principled)

**B1. Entangled borrow arguments.** Goal: pass `y ↦ borrow_ℓ (S loan_m)` and its reborrow `z ↦ borrow_m v` to one call, so that the callee's generic proof (which treats its two borrows as independent) is instantiated at arguments that are not independent. `f(y, z)`: reading `y` ends every borrow whose loan is inside `content(y)`, so `z ↦ ⊥`, an error. `f(z, y)`: `z` goes into tmp₁, reading `y` ends `m`, tmp₁ ↦ ⊥, and the frame push fails. **Blocked by [Access]'s "anywhere inside content(p)" on read/borrow. Principled:** it is exactly the [Close] loan-free precondition, and it is also what makes the frame property's "independent arguments" true.

**B2. Multi-owner holes through a lemma.** State: `c₁, c₂` both hold `⌈…; *r := loan_k; cᵢ⌉` after a two-argument borrow-returning call, and `t ↦ borrow_k T`. I passed `t` to a generically true lemma `L(x : &Nat) : Id Unit (F(x)) (G(x))`. Instance W = owners(k) = {c₁, c₂}. The observation fills `loan_k` with `F`'s (respectively `G`'s) final content in both, and the generic proof gives `F(v) = G(v)` for every `v`, so the instance is true. **Blocked by owners being a set (meta-model C2), together with holes being variables. Principled:** the frame property holds by substitution. Observing only `c₁` would break it (the known C2 attack).

**B3. [Rec] circumvention.** (a) `*x := S *x` and then recurse on the predecessor: blocked, because the entry value is σ and `(*x).1` now holds σ itself, which is not a strict subterm. (b) Generalise a sealed program `⌈…σ…⌉` to σ_g, split `σ_g := S σ_g'`, and recurse on σ_g': blocked, because σ_g' is not a subterm of the entry σ. (c) A nested closure capturing the predecessor, returned and called later: allowed, and fine, because every call it makes is on the fixed strict subterm. (d) The recursive call placed in the *continuation* after a non-tail match, using a σ' introduced in an arm: blocked, because the arm's result leaves the block only as a sealed program `⌈F(…)⌉`, which is not a subterm. **Principled** (entry value, refinement-aware). The one real hole is F4 (unannotated `fix`).

**B4. [Close] row chosen from a stuck result type.** The [Close] table branches on the *shape* of `B` (`Unit`, borrow-free `D`, `&T`). A family `T(n) := match n { Z => &Nat | S _ => Nat }` used as a result type makes `B = ⌈T(σ)⌉` at the generic call and `&Nat` at an instance, which is the same generic-versus-instance split as F1. I tried to exploit it: close `f(&c, σ) : T(σ)` with the D row, then write through the returned value at the instance. At the generic call the value of type `T(σ)` is a sealed program or an abstract value, not a `borrow_ℓ`, so any `*r := …` in the statement, or in a helper checked generically, fails (`content(*r)` is undefined). **Blocked, but accidentally:** by "dereferencing a neutral is an error", not by any rule about which types may be computed. RULES should say that `&A` occurs only syntactically at the top of a binder or result type, never as the value of a type-level computation. Then the [Close] row, and "A must be borrow-free" in `Id`, are syntactic and substitution-stable.

**B5. J and the three `Eq` conversions.** I tried to get `h : Eq A a b` with `a ≢ b` from the conversions:
- pairs with a Prop component (`Eq (Nat × P) (n,h) (m,k) ≡ Eq Nat n m ∧ ⊤ ≡ Eq Nat n m`);
- `Eq Prop P (P ∧ ⊤) ≡ ⊤`, which needs propext (stated);
- J into `Type` with an abstract `h`, where a `P(σ)` value is used at `P(Z)` only under a hypothesis;
- `Eq A a b ≡ ⊤` when `a ≡ b` for a Prop-typed `A` (proof irrelevance).
Every rule identifies propositions with the same truth value in the proof-irrelevant set model with propext, and J's result is only used under its hypothesis. **Blocked, principled.** The residual risk is not in these rules but in what `≡` identifies (F3).

**B6. Universes.** I looked for Girard's paradox and type-in-type through: `Id` at large types (owners holding types, so `T_W : Type_{i+1}`); mutating a type-valued place (`T := Type_0` where `T : Type_0` is rejected by the typing of `:=`); stored types being values fixed when the place is bound; and impredicative Prop together with `Id`. Nothing found. **Blocked, principled, given standard Π/× universe rules**, which RULES leaves to "the paper" and which I did not check. Cumulativity is load-bearing (F1, proof half) and should be stated as absent.

**B7. Types formed while a returned borrow is live.** State: `c ↦ H(loan_k)`, `t ↦ borrow_k T`. A type that reads `c` (for example `Eq Nat c Z`, or a lemma call `L(&c)`) ends `borrow_k` *on its private copy*, so it captures `H(T)`: "c as if t ended now". The real program then does `*t := 5`, and `c` ends up `H(5)`. The type is now stale, but it is a closed statement about the value `H(T)`, so it is still true. **Blocked by P2's "types capture values". Principled.** It is worth one example in the paper, because a user will read `Eq Nat c Z` as a statement about `c`.

**B8. [Call-type] parameter types that mention earlier borrow parameters.** `f : Π(x : &Nat) (h : Eq Nat (*x) Z). B`, called as `f(&c, L(&c))`. The proof argument is evaluated after tmp₁ holds `borrow_ℓ v`, and borrowing `c` inside it ends tmp₁'s borrow, but only on the proof's private copy, so it sees `v`. `A₂` evaluated with `x ↦ borrow_ℓ v` also sees `v`. They agree. A later *non-proof* argument that touches `c` kills tmp₁ and the call fails. **Blocked by private copy plus exclusivity. Principled.**

**B9. Effects on borrow variables are not observed.** `Id Unit (x := y) ()` with `x, y : &Nat` (if assigning a borrow variable is allowed): W = owners(x) ∪ owners(y), and after "end every borrow" both sides agree, so it holds by `refl`. The continuation `(□; *x := 5)` tells the two apart. This is a meaning gap (target 3, weak): `Id` equates computations that leave borrow variables pointing at different places. It cannot become False, because nothing in the calculus uses `Id` as a congruence except [Call-type], and [Call-type]'s implicit context always ends every borrow. **Blocked by the absence of an `Id`-congruence rule. Principled, but it constrains the future:** a user-facing "rewrite by `Id`" tactic would be unsound. The paper's "transport along that equation would prove `Eq Nat 6 5`" (in `obs.typ`, about owned locals) suggests the authors have such a transport in mind. If so, the footprint has to include borrow *variables*, not only their owners.

**B10. Order of stuck-block captures.** Captures are evaluated in some order, and the order matters. Copying `*r` and then `&p` (where `r` borrows `p`) succeeds and kills `r`. `&p` then `*r` fails. Borrowing `&*r` then copying `*x`, when `x`'s content holds `r`'s loan, fails. I found no order that succeeds *and* differs from the direct run: every conflict ends in `⊥` and a rejection. **Blocked by exclusivity. Principled, but underspecified:** acceptance currently depends on an unstated order. Say "left to right in order of first occurrence", or "reject if any order fails".

**B11. Splitting inside a proof that is not at the program's tail.** `let h : T = match n {…}; rest`. The split refines σ only on the proof's private copy, and `rest` continues unrefined. Even if an implementation leaked the refinement into `rest`, a case split on a value is sound wherever it occurs (call-by-value dependent elimination). **Blocked. Principled.**

**B12. Termination and decidability of conversion.** Every run executes either [Rec]-checked code or non-recursive anonymous blocks. [Seal]'s head guard stops re-closing. Refinement and [End] re-normalisation substitute into finitely many sealed programs. So I believe conversion terminates, *given F4's fix*. With F4's hole, `fix f (x : Nat) : Nat := f(x)` makes any concrete call, and hence the checker, loop. Performance warning, not soundness: a call that gets stuck after inner calls is run twice (partial run, then [Seal] re-run from scratch), and so is every inner stuck call inside the re-run. Stuck-call nesting of depth d costs about 2^d runs. That is decidable, but it is the kind of blow-up the dllbc work hit ("encoding is the cost"), so memoise [Seal] normal forms per sealed program.

**B13. Scoping in [Call-type].** "Push a frame binding each xᵢ … evaluate B there" reads as dynamic scoping over the caller's environment, while P2 says B's other free variables were captured. Under the dynamic reading: `f : Π(u : Unit). Eq Nat n Z`, formed where `n = Z`, so `f := λu. refl` checks, is called inside a function with a local `n = S Z`, and gives `Eq Nat (S Z) Z`. **Blocked by P2's text ("captured when the Π-type was formed"). Principled, but the mechanism sentence invites the wrong implementation:** say "evaluate B in the Π-closure's captured environment, extended with the parameter frame, with the caller's Ω visible only for owner lookup".

---

## Underspecified points where a reasonable reading is unsound (or at least disagrees with compiled code)

1. **What "is a type" / "is a proof" means** (F1). The candidates are: syntactic position, declared sort, or normal-form shape. The last two, read on normal forms, are unsound. Decide it per definition at the generic call.
2. **Cumulativity** (F1, proof half). Say there is none. With `Prop ≤ Type_0`, the proof half of F1 breaks under every reading.
3. **[Access] for matches.** RULES says "path or head". The paper's Figure caption says "path or inside its content". The RULES version enables F2 unless a neutral's inner loans count as being at its head.
4. **[Seal] on a run that errors** (F2). An erroring sealed program stays a neutral value and can be generalised. Make it a type error at the triggering point.
5. **Normal form of a closure** (F3). Result only (unsound), syntax (sound), or generic-call observation (sound and uniform).
6. **`fix` without `by`** (F4). Is `f` bound in the body? Is `f` bound in its own `Ā`, `B`?
7. **Pattern variables in captures and footprints** (F5). They must resolve to the sub-places they denote.
8. **`&A` produced by a type-level computation** (B4). This is not excluded by "never inside another type", and [Close]'s row choice and `Id`'s "A borrow-free" then depend on a normal form.
9. **Capture order for stuck blocks** (B10).
10. **Scoping of B in [Call-type]** (B13).
11. **Arms of stuck blocks inside types are never checked.** RULES says "Only matches whose arms have been checked (by [Split]) *or that occur inside types* are closed off this way". An ill-typed or borrow-erroring arm inside a statement surfaces only after a later refinement, as an erroring [Seal] run (see 4). The "match's type … inferred from the arms" is then inferred from unchecked arms. Either check type-level arms with [Split], or say explicitly that a statement's normalisation error is a type error at the use site.
12. **J's non-type arguments.** Endpoints `a`, `b` and the motive `P` are neither types nor proofs, so the machine runs them for real, effects included. A Lean-style compiler erases them as computationally irrelevant. `J(Nat, (x := 5; Z), Z, P, refl, t)` then disagrees between the checker and the compiled code. State that they are in type positions (private copy), matching F1's positional fix.
13. **A stuck block that reassigns a borrow variable** (`x := &d` in an arm). Capturing it "as &" would need `&(&Nat)`, which is not a type. Say "moved".
14. **Closed-off calls whose head is a local closure.** [Close] says "`f` is a top-level name, or an anonymous function". A local `fix` has to be embedded in `C` as a closure value, including its captured values, so that refinements reach them. Otherwise the sealed program is not closed.
15. **Universe rules for Π, ×, `Id`**, left to "the evident ones in the paper". Impredicativity of Prop and the level of `A × T_W` need to be explicit for the model argument.

---

## Cross-check against DECISIONS.md (read after the attacks)

- **F1 is new.** D26 claims naturality ("a Prop-typed block has no effect whether its scrutinee is abstract or refined"). That holds for Prop-sorted terms, because sort is stable. It fails for *type-valued* terms: whether `W(&c, n) : U(n)` is a type depends on whether `U(n)` normalises to a universe. D27's Q3 ("a sealed program of sort Prop is a type") fixes the proof half by sort, as I recommend, but does not reach this case. D2/D13 make statements closures, but they re-decide erasure at each instance.
- **F2 contradicts D19's own text.** D19 says "[Access] ends loans on the path *and inside the content*". RULES v1.3 narrows this to "path or head" for matches, and the paper caption keeps D19's version. Either restore D19 for matches or add the neutral-head clause.
- **F3 is new.** D14's `λx.⋆` vs `λx.(*x := 7; ⋆)` is the Prop instance. F3 is the Type instance through conversion of function values.
- **F4 is new.** D17 and D23 cover `fix … by xⱼ` only.
- **F5 is new.** It is D5's own revisit trigger ("the footprint misses writes"), through pattern variables rather than returned borrows. D22's capture rule has the same gap.
- B1, B2, B3(a) and B13 are regressions of D19, D18, D17 and D13 respectively. They still hold.

## Attack list (distinct attacks and outcomes)

| # | Attack | Outcome |
|---|---|---|
| F1 | effectful call whose type is a stuck family computing to `Prop`; [Call-type] re-decides erasure at the instance | **closed `Eq Nat Z (S Z)`** (literal P2); proof-half variant needs a shape reading or cumulativity |
| F2 | TailM hole inside a neutral, `match` does not end it, [Split] generalises it away | **accepted program writes through an ended borrow**; false `Id` assertion vs compiled run; no False |
| F3 | effectful closures convertible by result-only normal form, then transport with J | **closed `Eq Nat (S Z) Z`** under the literal P1 reading; unspecified |
| F4 | `fix` without `by` recursing on itself | **closed `Eq Nat Z (S Z)`** and a looping checker if `f` is bound; unspecified |
| F5 | write through a pattern variable inside a type-level stuck block | **closed `Eq Nat (S Z) (S (S Z))`** under the literal capture parenthetical |
| B1 | entangled borrow arguments | blocked by [Access] (principled) |
| B2 | multi-owner holes through a lemma | blocked, the frame property holds by substitution (principled) |
| B3 | [Rec]: mutate-then-recurse, generalised σ_g, escaping closure, continuation σ' | blocked by entry values (principled) |
| B4 | [Close] row from a stuck `&`-valued type family | blocked accidentally (neutral deref errors); unspecified |
| B5 | J and the three Eq conversions | blocked (set model + propext) |
| B6 | universes / Girard via `Id`, type-valued places | nothing found; Π/× levels unspecified |
| B7 | types formed while a returned borrow is live | stale but true snapshot (principled) |
| B8 | parameter types over earlier borrow params | consistent (private copy + exclusivity) |
| B9 | `Id Unit (x := y) ()` | provable (meaning gap); no False without an Id-congruence rule |
| B10 | stuck-block capture order | conservative in every order; order unspecified |
| B11 | split inside a non-tail proof | sound |
| B12 | termination of conversion | terminates given F4's fix; 2^depth re-runs (performance) |
| B13 | dynamic scoping in [Call-type] | blocked by P2's text; the mechanism sentence is misleading |
