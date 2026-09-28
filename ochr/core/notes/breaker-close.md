# breaker-close: attacks on [Close], [Seal], loan holes, [Reorg], [Join], §6

**Summary.**
1. Verdict: RULES.md v0 is **unsound**. Four closed proofs of `⊥` (A2, A3 twice, A4), one accepted program that goes wrong at runtime (A1), and normalisation that diverges on every stuck call, including the E1 derivation (A5).
2. Most important finding: [Close] is only sound if each borrow argument's content is **loan-free** at the call (A1). v0's [Read] moves a borrow without ending the loans inside it, so [Close] copies a live loan into a sealed program. After refinement the sealed program no longer agrees with the program it stands for. Second: an impredicative, proof-irrelevant `Prop` that contains `Π(x : &T). P` is inconsistent, because inhabitants of that type have effects (A2).
3. Must change: add Aeneas's `loan ∉ v` premise to move, copy and borrow, applied lazily and also looking inside sealed programs, and make it a precondition of [Close]. Put `Π(x : &T). B` in `Type`, never in `Prop`. Replace §6 by a semantic guard: the recursive argument's value must be a strict subterm of the parameter's *entry* value, and `f` may occur only as the head of such a call. [Seal] must not re-close its own canonical call. Replace loan holes by deferred fills (Aeneas region abstractions) (A6). Specify the goal in [Join] and nullary close-off.
4. Confidence: high on A1–A5 (each derivation is written out below and uses only v0's text). Medium on A6: v0 is silent there, and I show every reading fails. High that [Join] and the ending order are sound once those fixes are in, but that is argued, not proved.
5. Not checked: the frame lemma and the typing of the induction hypothesis in [App] (breaker-frame's area); the footprint `W` beyond what these attacks touch; full re-derivation of E1–E4 under the proposed fixes.

## Index (attack → outcome)

| # | Attack | Outcome |
|---|---|---|
| A1 | [Close] on a moved borrow whose content holds a live reborrow's loan | **BUG**: accepted program writes through an ended borrow; the sealed normal form differs from running the call; `Π`-instantiation fails |
| A2 | `Π(x:&Nat). Eq Nat Z Z` is a `Prop`, so an effectful and an effect-free inhabitant are definitionally equal | **BUG**: closed `⊥` via `J`; variant through sealed-program conversion |
| A3 | §6 entry value: write before the match / write *after* the match through an alias pattern variable | **BUG**: two closed `⊥`s; alias pattern variables are the root cause |
| A4 | §6 says nothing about `f` occurring unapplied (`fix f x := Apply f x`) | **BUG**: closed `⊥`; normaliser unfolds forever |
| A5 | [Seal] running a stuck sealed program re-closes it and yields itself | **BUG** (wording): `nf` loops on every refinement in E1 |
| A6 | Loan hole `loan_k` inside a sealed program re-run at a refinement | **GAP**: every reading either rejects valid Rust, crashes the checker, or ends a real borrow from inside normalisation |
| A7 | Returned borrow into one of two arguments depending on a value (`Choose`) | Sound; needs `loan_k` in *both* fills, which breaks LLBC's unique-loan invariant: [Reorg] must fill all occurrences |
| A8 | Write before getting stuck; stuck on a by-value argument; two borrow arguments; order of writes | Sound (blocked by determinism + re-running from entry); costs only completeness |
| A9 | Canonicity: one stuck call, two syntactically different seals; or two different things convert | No unsoundness beyond A2's variant; three incompleteness sources (head name vs closure, currying, `α` on `cᵢ` and `k`) |
| A10 | Nullary close-off of a stuck top-level term | **GAP**: free places are unbound; the literal reading is incomplete, the "resolve in current Ω" reading gives `⊥` |
| A11 | [Reorg] "at any other time": find an observable ending order | Observable only through definedness (early end ⇒ later use errors). A1 is the real counterexample to "lazy is canonical", between concrete and symbolic runs |
| A12 | [Join] by anti-unification: unsound generalisation or non-unique lgg | No unsound join found if Ω (with stored types), goal and result are anti-unified *jointly*; v0 omits the goal; lgg unique on normal forms |
| A13 | Sealed program whose normalisation loops | None beyond A4/A5 once §6 is fixed |

---

## A1. [Close] copies a live loan into a sealed program (BUG)

**Idea.** [Close] assumes the callee owns everything reachable from its borrow arguments, so re-running the call on a copy `let cᵢ = uᵢ` is the same as running it in place. v0's [Read] moves a borrow `borrow₁ (S loan₂)` whose content still contains another borrow's loan. [Reorg] fires only when the accessed place's content *is* `loan_ℓ`, or a prefix of its path is. The callee would have ended `borrow₂` the moment it wrote over that cell. [Close] discards the callee's run, so that ending never happens, and the loan is copied into `L`.

```
G   : Π(x : &Nat) (n : Nat). Unit
G x n := match n { Z => () | S _ => *x := Z }

Bad : Π(n : Nat). Nat
Bad n := let a = S Z; (let b = &a; let r = &(*b).1; G b n; *r := S Z); a
```

(Rust rejects this program: E0505, cannot move `b` while it is borrowed by `r`, which is used later.)

Typing, which is the symbolic run with `n ↦ σ`:

```
{} ⊢ Bad : Π(n : Nat). Nat                                                    // [Lam], n ↦ σ; accepted, result below
  ⟨{n ↦ σ}, let a = S Z; …⟩
  ⟨{n ↦ σ, a ↦ S Z}, let b = &a; …⟩                                              // [Let]
  ⟨{…, a ↦ loan₁, b ↦ borrow₁ (S Z)}, let r = &(*b).1; …⟩                        // [Borrow]
  ⟨{…, a ↦ loan₁, b ↦ borrow₁ (S loan₂), r ↦ borrow₂ Z}, G b n; *r := S Z⟩       // [Borrow] of the sub-place (*b).1
  ⟨{…, b ↦ ⊥, r ↦ borrow₂ Z}, G (borrow₁ (S loan₂)) σ⟩                           // [Read] b holds a borrow: moved; loan₂ inside it is not ended
    ⟨{… | x ↦ borrow₁ (S loan₂), n ↦ σ}, match n {…}⟩ stuck                      // [App] push frame; [Match] content σ
  ⟨{…, a ↦ ⌈let c = S loan₂; G &c σ; c⌉, b ↦ ⊥, r ↦ borrow₂ Z}, *r := S Z⟩       // [Close] u₁ = S loan₂, L = let c = S loan₂; fill loan₁; result ()
  ⟨{…, r ↦ borrow₂ (S Z)}, ()⟩                                                   // [Assign] through r: r is still live
  ⟨{n ↦ σ, a ↦ ⌈let c = S (S Z); G &c σ; c⌉}, a⟩                                // [Pop] r: loan-free borrow ends, S Z goes into loan₂ inside the seal; b is ⊥
  ⟨{n ↦ σ}, ⌈let c = S (S Z); G &c σ; c⌉⟩                                       // [Read] copy; [Pop] a
```

So `Bad` is well-typed. For the same reason the following is accepted, since both sides normalise to the same seal:

```
BadThm : Π(n : Nat). Id Nat (Bad n) (let c = S (S Z); G &c n; c)
BadThm n := refl
```

At `σ := S Z` the seal `⌈let c = S (S Z); G &c (S Z); c⌉` normalises to `Z`. The concrete program does something else:

```
⟨{}, Bad (S Z)⟩ goes wrong
  ⟨{a ↦ loan₁, b ↦ borrow₁ (S loan₂), r ↦ borrow₂ Z}, G b (S Z); *r := S Z⟩
  ⟨{… | x ↦ borrow₁ (S loan₂), n ↦ S Z}, *x := Z⟩                                 // [App], [Match] S arm
    // [Assign] must drop the old content S loan₂. Aeneas (E-Assign): end borrow₂ first, r ↦ ⊥.
    // v0 does not say. If the loan is silently dropped, compiled in-place code frees the S cell r points into.
  ⟨{a ↦ Z, b ↦ ⊥, r ↦ ⊥}, *r := S Z⟩                                             // [Pop] G's frame: borrow₁ ends
  error: write through ⊥ (or write-after-free in the in-place compilation)       // [Ref]
```

Three consequences, each on its own enough to count as a bug:
- **Well-typed code goes wrong** (`Bad (S Z)`).
- **[Seal] is inconsistent with running the call.** Normalising the seal after refinement gives `Z`; running the unsealed call gives an error. This contradicts the Adequacy conjecture (§7): the symbolic machine does not commute with substitution.
- **Instantiation fails.** `BadThm : Π(n:Nat). T n` is accepted, but [App] must evaluate `T (S Z)` at the call site, and doing so runs `Bad (S Z)` concretely and errors. A well-typed function applied to a well-typed argument has an ill-formed type.

**Minimal fix (principled).** Restore Aeneas's premises. E-Move, E-Copy and E-Mut-Borrow all require `loan ∉ v`, and the lazy strategy discharges that by ending every loan found inside `v`. In v0 terms:
- [Reorg] fires when the accessed value *contains* `loan_ℓ` anywhere, including inside a sealed program, not only when it *is* one.
- [Close] states as a precondition that every `uᵢ` is loan-free. That is what "sealed programs are closed and own their state" (P4) requires.

With the fix, moving `b` ends `borrow₂` (so `r ↦ ⊥`), `*r := S Z` is a [Ref] error, and `Bad` is rejected, as in Rust.

**Decision implicated.** P3/[Read] as worded, and the §3 claim "the lazy strategy is canonical". Lazy ending happens at different points in the concrete run (inside `G`) and the symbolic run (never, because `G`'s run was discarded). The loan-free premise forces the ending to happen at the call boundary in both, which makes the two agree.

---

## A2. Effectful inhabitants of an impredicative, proof-irrelevant `Prop` (BUG, closed `⊥`)

This is outside the four rules I was pointed at. I found it while looking for "two different things that convert" (A9), and it is the cleanest `⊥` I have.

v0 takes Lean's sorts ("`Prop` has definitional proof irrelevance"; §4: "consistency is inherited from the proof-irrelevant set model of Lean"). In Lean, `Π(x:A). P : Prop` whenever `P : Prop`, whatever `A` is. Take `A = &Nat`:

```
Q  := Π(x : &Nat). Eq Nat Z Z                  // a Prop by impredicativity
p₁ := λ(x : &Nat). refl                          : Q
p₂ := λ(x : &Nat). (*x := S Z; refl)             : Q    // [Lam]: goal Eq Nat Z Z ≡ ⊤ is formed at entry and never reads x, so refl checks after the write
```

Definitional proof irrelevance makes `p₁ ≡ p₂`, but they do different things to the place they are given:

```
e : Eq Q p₁ p₂ := refl                                   // p₁ ≡ p₂: both inhabit the Prop Q
P : Π(h : Q). Prop := λh. Id Nat (let y = Z; h &y; y) Z
d : P p₁ := refl
  Id Nat (let y = Z; p₁ &y; y) Z ≡ Eq Nat Z Z ≡ ⊤          // [Id] below; W = ∅ (y is local to the left side)
    ⟨{}, let y = Z; p₁ &y; y⟩ ⇓ ⟨{}, Z⟩                    // [Let], [Borrow], [App] p₁ returns refl, [Pop] borrow ends, [Read]
J P d e : P p₂
  P p₂ ≡ Id Nat (let y = Z; p₂ &y; y) Z ≡ Eq Nat (S Z) Z ≡ ⊥
    ⟨{}, let y = Z; p₂ &y; y⟩ ⇓ ⟨{}, S Z⟩
      ⟨{y ↦ loan₁ | x ↦ borrow₁ Z}, *x := S Z; refl⟩       // [Let], [Borrow], [App]
      ⟨{y ↦ loan₁ | x ↦ borrow₁ (S Z)}, refl⟩               // [Assign]
      ⟨{y ↦ S Z}, y⟩                                       // [Pop] borrow₁ ends into loan₁
```

`J P d e : ⊥` is closed.

**Variant through sealed programs** (this is the [Seal]-canonicity form of the same bug: two different things convert):

```
Use : Π(h : Q) (x : &Nat) (n : Nat). Unit
Use h x n := match n { Z => h x | S _ => h x }

T : Π(n : Nat). Id Nat (let c = Z; Use p₁ &c n; c) (let c = Z; Use p₂ &c n; c)
T n := refl
  // n ↦ σ: both calls are stuck on σ; [Close] gives ⌈let c₁ = Z; Use p₁ &c₁ σ; c₁⌉ and ⌈let c₁ = Z; Use p₂ &c₁ σ; c₁⌉.
  // Comparing two neutrals compares their embedded values by conversion; p₁ ≡ p₂, so refl checks.
T Z : Eq Nat Z (S Z) ≡ ⊥                                   // [App]: the type is evaluated at n = Z; both seals now run
```

(The variant is blocked if sealed programs are compared purely syntactically. The `J` version is not blocked.)

**Why the consistency argument misses it.** In the §7 model (state-passing translation), `Π(x : &Nat). P` becomes `Nat → Nat × ⟦P⟧`. That is not a subsingleton even when `⟦P⟧` is. The proof-irrelevant *set* model interprets v0's `Prop`, but v0's `Prop` then contains types the state-passing model cannot put in `Prop`. §4's sentence "each of these conversions identifies two propositions with the same truth value" is true, but it is not the whole consistency argument.

**Minimal fix (principled).** `Π(x : &T). B : Type`, always. A function with no borrow parameter can write only its own frame (P5, and closures capture only borrow-free values), so it has no observable effect, and `Π(x : A). P` for borrow-free `A` can stay in `Prop`. The criterion is visible in the type, so this does not introduce a purity annotation (end goal 2 is intact). Nothing in E1–E4 needs `AddMZero`'s type to be proof-irrelevant.

**Consequence worth knowing.** Proofs with borrow parameters become relevant computations. A lemma call `AddMZero &p` (A8) *does* fill `p`'s loan with a seal of the lemma. That is now correct rather than a curiosity: such "proofs" can write.

**Decision implicated.** §4's consistency paragraph and D6's justification. The model that has to validate `Prop` is the §7 translation, not the set model applied directly.

---

## A3. §6: the entry-value gap is real, and writes *after* the match open it too (BUG, closed `⊥` ×2)

§6 accepts a recursive call on `y` or `&y` whenever `y` is a pattern variable from a match on the parameter's content. The note says "the symbolic execution is where that gap is closed", but no rule closes it.

**(a) Write before the match.**

```
Loop : Π(x : Nat). ⊥
Loop x := match x {
  Z   => (x := S Z;     match x { Z => () | S y => Loop y })
  S p => (x := S (S p); match x { Z => () | S y => Loop y })
}
```

```
{} ⊢ Loop : Π(x : Nat). ⊥                               // [Lam] x ↦ σ; §6: every call is Loop y, y a pattern variable of a match on x ✓
  arm Z: {x ↦ Z}                                        // [Split] σ := Z
    ⟨{x ↦ S Z}, match x {…}⟩                              // [Assign]
    ⟨{x ↦ S Z}, Loop x.1⟩ : ⊥                            // [Match] content S Z (concrete: the inner Z arm is never visited); [App] type ⊥
  arm S: {x ↦ S σ'}, p = x.1                            // [Split] σ := S σ'
    ⟨{x ↦ S (S σ')}, match x {…}⟩                        // [Read] p (copy σ'), [Assign]
    ⟨{x ↦ S (S σ')}, Loop x.1⟩ : ⊥                       // y = x.1 holds S σ', the entry value
Loop Z : ⊥                                              // closed; concretely Loop Z → Loop Z → …
```

The inner `Z => ()` arms are ill-typed but dead. v0's typing is a run, so it never visits them. A checker that insisted on visiting them would have no refinement that makes them impossible, so it is v0's "typing is running" that licenses them. Either way, the recursive calls are the bug.

**(b) Write after the match: pattern variables are aliases.** In `match x { S y => … }`, `y` is the *place* `x.1`, not a copy and not a borrow. No loan is created, so the borrow checker does not stop a write to `x`, and after the write `y` names the new tail.

```
Spin : Π(x : Nat). ⊥
Spin x := match x {
  Z   => (x := S Z; match x { Z => () | S y => Spin y })
  S y => (x := S x; Spin y)                            // after x := S x, y = x.1 is the old x: the entry value
}
```

```
arm S: {x ↦ S σ'}, y = x.1                              // [Split]
  ⟨{x ↦ S (S σ')}, Spin x.1⟩                             // [Read] x (copy), [Assign]; x.1 now holds S σ' = entry
  : ⊥                                                   // §6 ✓ (y is a pattern variable, written after the match)
Spin (S Z) : ⊥                                          // closed; Spin (S Z) → Spin (S Z) → …
```

The same shape works through a borrow (`match *x { S y => (*x := S (S Z); Spin &y) }`). §6's caveat only mentions writes *before* the match, so (b) is not covered by it.

**Minimal fix (principled).** Make the guard semantic, on values, as the §3 rule already is. At a recursive call, the value of the argument (the content behind a borrow argument) in the current Ω must be a strict subterm of the parameter's entry value σ, *as refined by the [Split]s on the way*. For (a) and (b) the argument's value is `σ` or `S σ'` against entry `S σ'`, so both are rejected. `AddMZero`, `AddZero`, `TailM` and `AddMEq` all pass: the argument is `σ'` where `σ := S σ'` was a split.

**Underlying cause (flag, not fixed here).** Alias pattern variables with no loan. Aeneas states outright (§4.1) that soundness requires forbidding a change of variant while a field is borrowed. Ochr's alias `y` has no loan, so `match x { S y => (x := n; y) }` reads `x.1` through whatever `n` is. v0 has no rule for following `.1` through an abstract value: it is neither [Match] nor stuck. Treating it as stuck (and closing off) would turn it into a seal that crashes at `n = Z`. Either make pattern variables into reborrows, which is Aeneas's choice and gives the loan, or say that a write to a prefix of `y`'s path invalidates `y`. With either, (b) is also rejected syntactically.

**Decision implicated.** §6, plus the "pattern variables are sub-places" design in §1.
