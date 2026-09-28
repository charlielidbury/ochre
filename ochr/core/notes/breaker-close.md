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

---

## A4. §6 does not stop `f` escaping unapplied (BUG, closed `⊥`)

§6 constrains "every recursive call". It says nothing about `f` occurring anywhere else.

```
Apply : Π(h : Π(_ : Nat). ⊥) (n : Nat). ⊥
Apply h n := h n

Knot : Π(x : Nat). ⊥
Knot := fix f (x : Nat) : ⊥ := Apply f x
```

```
{} ⊢ Knot : Π(x : Nat). ⊥                     // [Lam] for fix: x ↦ σ, f : Π(x:Nat). ⊥ in scope
  §6: the body contains no call with head f      ✓ (vacuously)
  Apply f x : ⊥                                  // [App]: result type ⊥[h := f, n := x]
Knot Z : ⊥                                       // closed
```

Evaluation: [App] unfolds a `fix` on *any* argument, unlike CIC, which needs a constructor. v0 relies on every recursive call being preceded by a match on the parameter, so that a symbolic argument gets stuck. `Knot Z` → `Apply f Z` → `f Z` → `Apply f Z` → … never reaches a match, so it is never stuck, and neither the machine nor the normaliser terminates. v0 also does not say what *value* `f` has while its own body is checked. If it is the fix-closure, checking `Knot` itself loops. If it is an abstract `σ_f` (the right answer; say so), checking succeeds and the `⊥` above goes through.

**Minimal fix (accidental omission).** The CIC guard. `f` may occur only as the head of a call that passes A3's semantic check. While checking the body, `f` is bound to an abstract function. Decision implicated: §6 only.

---

## A5. [Seal] re-closes its own call, so `nf` diverges (BUG, wording, bites E1)

[Seal]: "run `t` from the empty environment; if it completes with `v`, the result is `nf(v)`; otherwise `⌈t'⌉`". A seal has the shape `L; C; …`, where `L` only binds values, so the only place its run can get stuck is inside the call `C`. But a stuck call does not leave the run stuck: [App] hands it to [Close], which returns a seal, and the run *completes*. The "otherwise" branch is unreachable. For a genuinely stuck seal, `v` is the same seal again (up to `α`), and `nf(v)` recurses forever.

This fires on E1's first refinement. `AddMZero`'s entry goal holds the fill `x° ↦ ⌈let c = σ; AddM &c 0; c⌉`, and the S arm substitutes `σ := S σ'`:

```
nf(⌈let c = S σ'; AddM &c 0; c⌉)                                            // Refinement re-normalises
  ⟨{}, let c = S σ'; AddM &c 0; c⟩ ⇓ ⟨{}, S ⌈let c₁ = σ'; AddM &c₁ 0; c₁⌉⟩   // [Let] [Borrow] [App] [Match] S arm; inner call stuck: [Close]; [Pop] [Read]
  = S nf(⌈let c₁ = σ'; AddM &c₁ 0; c₁⌉)                                     // [Seal]: completed with v, so nf(v)
    ⟨{}, let c₁ = σ'; AddM &c₁ 0; c₁⟩ ⇓ ⟨{}, ⌈let c₂ = σ'; AddM &c₂ 0; c₂⌉⟩  // AddM stuck at once: [Close]; the run completes
    = nf(⌈let c₂ = σ'; AddM &c₂ 0; c₂⌉)                                     // α-equal to the input: loops
```

**Minimal fix (accidental).** A seal is normal when unfolding its canonical call `C` once gets stuck in `C`'s own body. That is the same condition [Close] uses, so [Close] is never applied to the seal's own call. Otherwise run it, and seals created *inside* that run (by other calls) are normal by the same rule. Also, "at type `Unit` every value normalises to `()`" needs the seal to carry its type (`⌈t⌉ : T`), since values are untyped.

---

## A6. Loan holes break under refinement (GAP; D4's revisit trigger fires early)

A returned borrow leaves `loan_k` inside each fill `⌈L; let r = C; *r := loan_k; cᵢ⌉`, written with the same syntax as a real loan. A refinement re-runs every seal that mentions the refined `σ`, including seals that still have an unfilled hole. Inside that re-run, the hole behaves as a real loan.

```
G2 : Π(x : &Nat) (n : Nat). &Nat
G2 x n := match n { Z => x | S _ => x }

P : Π(x : &Nat) (n : Nat). Unit                  // the Rust analogue compiles
P x n := let t = G2 x n; match n { Z => () | S _ => () }; *t := Z
```

```
{x° ↦ loan₀ | x ↦ borrow₀ σ, n ↦ σₙ}                                           // [Lam]
⟨{x° ↦ ⌈let c = σ; let r = G2 &c σₙ; *r := loan_k; c⌉ | x ↦ ⊥, t ↦ borrow_k ⌈let c = σ; let r = G2 &c σₙ; *r⌉}, match n {…}; *t := Z⟩
                                                                                // [Close], result &Nat, k fresh
  arm Z: [Split] σₙ := Z, and Refinement re-normalises x°'s fill:
    ⟨{}, let c = σ; let r = G2 &c Z; *r := loan_k; c⟩
    ⟨{c ↦ loan_j, r ↦ borrow_j σ}, *r := loan_k; c⟩                             // G2 returns its argument
    ⟨{c ↦ loan_j, r ↦ borrow_j loan_k}, c⟩                                      // [Assign] writes the embedded value loan_k
    [Reorg] on c: end borrow_j; its content is loan_k, so end borrow_k first;
    borrow_k is t, which is in the outer Ω, not in this run                      // no rule applies
```

Every reading fails:
- **(i) Error.** `P` is rejected. So is any proof that case-splits while a returned borrow is live, which is the E2 pattern plus one match.
- **(ii) Search the outer Ω for `borrow_k`.** A hypothetical normalisation then ends `t` in the *real* environment, contrary to P2, and `*t := Z` becomes a [Ref] error. The result also depends on whether a refinement happened.
- **(iii) Treat the hole as inert inside seal runs.** Then the same syntax means two things: at top level it must still count as a loan (reading the owner must end `k`, or a type can snapshot a value that the returned borrow later changes), while inside seal runs it must not. An inert hole that reaches a type is a prophecy variable, which D4 rejected.

**Principled fix: deferred fill (Aeneas region abstractions).** On [Close] with result `&T`, leave each `loan_ℓᵢ` in place. The consumed borrows `ℓᵢ` go into a region node `A_k{ ℓᵢ ↦ λw. ⌈L; let r = C; *r := w; cᵢ⌉ }` which owns `loan_k`. When `borrow_k` ends with content `w`, the node ends and each `loan_ℓᵢ` receives its seal applied to `w`. This is End-Abstract-Mut followed by End-Abstraction, with backward functions written as sealed `λw`, which is exactly 01 §9's `λfinal. (last_mut♯ σ).back final`. Accessing `x` (content `loan_ℓᵢ`) forces `ℓᵢ` to end, which forces `A_k`, which forces `k`. That is the right borrow-checking behaviour, with no new rule.

What this buys:
- Seals never contain loans, so A1's premise holds by construction.
- Refinement only ever re-runs closed programs. In `P`'s arms the fills become `λw. w` in both, and the join goes through.
- A loan never appears twice (A7).
- No hole names reach conversion (A9c).

It costs one runtime structure (the region node) and removes the hole syntax, so the value grammar gets no bigger.

**Decision implicated.** D4 ("Revisit if the loan-hole form breaks down for borrows stored in data"). It breaks down earlier than that: under refinement, with no data involved.

---

## A7. Returned borrow into one of two arguments, chosen by a value (sound; one wording fix)

```
Choose : Π(b : Nat) (x : &Nat) (y : &Nat). &Nat
Choose b x y := match b { Z => x | S _ => y }
```

```
⟨{p ↦ 1, q ↦ 2, b ↦ σ}, let z = Choose b &p &q; *z := 5; (p, q)⟩
⟨{p ↦ loan₁, q ↦ loan₂, …}, Choose σ (borrow₁ 1) (borrow₂ 2)⟩                    // [Borrow] ×2
⟨{p ↦ ⌈L; let r = C; *r := loan_k; c₁⌉, q ↦ ⌈L; let r = C; *r := loan_k; c₂⌉,
  z ↦ borrow_k ⌈L; let r = C; *r⌉}, *z := 5; (p, q)⟩                             // [Close]: L = let c₁ = 1; let c₂ = 2, C = Choose σ &c₁ &c₂
⟨{…, z ↦ borrow_k 5}, (p, q)⟩                                                    // [Assign]
⟨{p ↦ ⌈…; *r := 5; c₁⌉, q ↦ ⌈…; *r := 5; c₂⌉, z ↦ ⊥}, (p, q)⟩                    // reading p ends k (A1's [Reorg]); loan_k occurs TWICE
```

At `σ := Z` this gives `(5, 2)`, and at `σ := S _` it gives `(1, 5)`, both correct. The only problem is textual. [Reorg] says "find the unique `borrow_ℓ`… replace `loan_ℓ` by `w`", and LLBC's invariant is one loan per borrow. [Close] with two borrow arguments and a borrow result duplicates `loan_k`. A reading that fills only one occurrence leaves `q` holding a hole whose borrow no longer exists. Fix: "replace every occurrence", or better, A6's deferred fill, where one region node owns both `ℓ₁` and `ℓ₂` and nothing is duplicated.

Imprecision, not unsoundness: once `σ := Z`, `z` points only into `p`, but reading `q` has already killed `z`. Aeneas's region abstraction makes the same trade.

---

## A8. The cases [Close] was designed for: all sound

- **Write before getting stuck.** `WB x n := *x := S Z; match n { Z => () | S _ => () }`, with `a ↦ Z` and `n ↦ σ`. The partial run's write is discarded, and `a ↦ ⌈let c = Z; WB &c σ; c⌉`. After either refinement this reruns the whole call from its entry state and gives `S Z`. Sound because the seal is a function of the argument values and the machine is deterministic. The cost is completeness: `Id Nat (WB &a n; a) (S Z)` needs a split on `n`, not `refl`.
- **Stuck on a by-value argument** (the same `WB`, or `G` in A1). This is no different from being stuck on the borrow: `σ` sits in `C`'s argument list, and refinement reaches it.
- **Two borrow arguments and write order.** `Sw a b n := *a := *b; *b := n; match n { Z => () | S _ => *a := *b }`. Each fill `⌈L; C; cᵢ⌉` is a complete rerun, so the order of writes inside `C` is reproduced exactly.
- **Result depends on both content and write order.** `⌈L; C⌉` is also a complete rerun. The link between result and fill ("the result equals the final content") is lost symbolically and comes back under refinement. Completeness cost only.
- **Lemma calls rewrite their borrow arguments.** A call to a proof with a borrow parameter gets its *value* from the machine, so in `AddMZero`'s S arm, `p`'s loan is filled with `⌈let c = σ'; AddMZero &c; c⌉`. This is sound, and after A2's fix it is necessary. But a proof that calls a borrow lemma and then keeps using the place (`L₁ &p; L₂ &p`) finds `L₂`'s induction hypothesis stated over `L₁`'s seal. Worth knowing before writing E-examples that chain lemmas.

The blocking rule is principled: discarding the partial run is exactly what makes the seal a function of its arguments (P5).

---

## A9. Canonicity (no unsoundness beyond A2's variant)

*Can two syntactically equal seals mean different things?* Only if a seal is not closed. That happens through a loan inside `L` (A1), a hole (A6) or a free place (A10). With those fixed, a seal is a closed, deterministic program over closed values, and syntactic equality implies semantic equality. *Can conversion identify two seals whose embedded values differ?* Yes, through proof irrelevance (A2's variant), and that is a bug in the sorts, not in [Seal].

Sources of "one stuck call, two different seals" (completeness only):
- **(a) Head: name vs closure.** `let g = AddM; g x 0`. [App] sees only the closure value, and [Close] uses "the function's name if it is a top-level definition, else its closure". The value has lost its name, so the seal is `⌈…; (fix …) &c 0⌉`, not `⌈…; AddM &c 0⌉`. Fix: pick one uniformly. Top-level constants are values that unfold only in [App], so the head is always the value.
- **(b) Currying.** The core has only unary `λ` and application, so `AddM x y = (AddM x) y`. Evaluating `AddM x` pushes a frame holding the borrow and returns `λy. …`, a closure capturing a borrow, which §1 forbids. [Pop] would end the borrow in any case. So `AddM` itself has no v0 semantics, and [Close]'s `f w₁ … wₙ` quietly assumes saturated n-ary calls. Fix: n-ary `λ` and calls in the core. Without it, a partial application capturing a borrow would sit inside a seal, which is an A1-type breach of closedness.
- **(c) Binders.** `cᵢ` and `r` need `α`-equivalence. Hole names `k` differ between two runs of the same program (04's "N up to renaming of l"). A6's deferred fill turns holes into a `λw` binder, and `α` covers that.

---

## A10. Nullary close-off (GAP; one reading gives `⊥`)

§4: "if `t` itself gets stuck outside any call, close it off as if it were the body of a nullary call". A nullary call's body can name no places, but `t` can: `match n {…}`, or writes through a free `x : &Nat`.

- **Literal reading** ([Seal] runs "from the empty environment"). `⌈match n { Z => Z | S _ => Z }⌉` has `n` unbound. It never normalises, and refinement "re-normalises every sealed program that mentions σ", but this one mentions the place `n`, not `σ`. So `Π(n:Nat). Id Nat (match n { Z => Z | S _ => Z }) Z` is unprovable even by splitting on `n`. Incomplete.
- **"Resolve free places against the current Ω" reading.** Unsound:

```
Liar : Π(n : Nat). Id Nat (match n { Z => Z | S _ => S Z }) (S Z)
Liar n := n := S Z; refl
  // entry goal: Eq Nat ⌈match n {…}⌉ (S Z) (the stuck match is closed off; the seal names the place n)
  // after n := S Z, conversion normalises the seal in the current Ω: S Z; so refl : Eq Nat (S Z) (S Z) checks
Liar Z : Eq Nat Z (S Z) ≡ ⊥
```

This is E6's "proof formed after a mutation", with the mutation hidden behind a seal that captured a *place* instead of a value (it breaks D2).

**Fix (uniform, no special case).** Close `t` over its free variables as an ordinary call: `C := (λ(x₁:A₁)…(xₘ:Aₘ). t) a₁ … aₘ`, where `aᵢ = &cᵢ` for borrow-typed variables and for places `t` writes, and the current value otherwise. Then apply [Close] as usual. This is 01 §5's "the unit of closing off is any subterm whose footprint is known", stated as a rule.

---

## A11. [Reorg] "at any other time": is the ending order observable?

- **Only through definedness, within one run.** In `let r = &x; *r := 5; x`, ending `r` before `*r := 5` makes the write go through `⊥`. So the machine, read as a relation, has an erroring run and a succeeding run from the same state. The sentence should say that other orders are a proof device, and that the machine (and the checker) is lazy.
- **Resolution (the observation).** No writes happen during resolution. Each End moves loan-free content into the matching loan, which is a tree contraction. Independent Ends touch disjoint positions and commute, and dependent ones are forced into order. I found no order-dependence. The two places where the argument needs care are A7's duplicated holes (fill all, or defer) and [Pop]'s eager ending of anonymous pending borrows (unobservable, because nothing can access them).
- **The real counterexample is between runs, not within one: A1.** The lazy strategy ends `borrow₂` inside `G` in the concrete run, and never in the symbolic run, because `G`'s run was discarded. So "the lazy strategy is canonical" is false for v0. With the loan-free premise, both runs end it at the call boundary.

Suggested restatement of the §7 conjecture: (1) for runs that do not error, the resolved observation does not depend on the ending order; (2) the concrete and symbolic runs agree on it. Part (2) is Adequacy, and A1 refutes it for v0.

---

## A12. [Join] by anti-unification (no unsound join found; v0 must name the goal)

**Why it is sound when done jointly.** Suppose the joined state generalises *everything the continuation reads*: Ω including binding types (types are values, so v0's "output environments" already covers stored types), the goal, and the match's result value and type. Then each arm's state is an instance of the joined state, obtained by substituting only for the fresh variables. The continuation's derivation is parametric in those variables, so it specialises to each arm. Plotkin's lgg gives this, *including* "same disagreement pair ⇒ same variable". That sharing is sound because every equality it records holds in every arm. I tried stored proofs (`h : Eq Nat x Z`), stored type values (`T ↦ Eq Nat x Z`), seals that share an `L`, closures, and positions coinciding by accident. All are instances.

**The gap: the goal.** v0 joins "output environments". After a non-tail match the arms' goals are refined differently, and v0 does not say which goal the continuation is checked against. One natural implementation (keep "the current refinement" as mutable state) is unsound:

```
Wrong : Π(n : Nat). Id Nat n Z
Wrong n := let u = match n { Z => () | S _ => () }; refl
  // arm Z: goal Eq Nat Z Z ≡ ⊤;  arm S: goal Eq Nat (S σ') Z ≡ ⊥;  [Join]: n ↦ σ_j, u ↦ ()
  // continuation checked against arm Z's goal: refl : ⊤  ✓
Wrong (S Z) : ⊥
```

The unrefined goal `G(σ)` is sound but leaves `σ` orphaned: every occurrence in Ω was substituted in both arms, so Ω's `σ_j` is unrelated to it, and proofs that do a non-tail match first become impossible. **Right rule:** anti-unify the goal jointly with Ω. With one more step it loses nothing. When the pair is exactly a split's `(Z, S σ')`, return `σ` itself ("split restoration"). That is sound because in each arm every such position equals `σ`.

**Uniqueness.** On normal forms, first-order lgg is unique up to renaming. Binders inside closures and seals are handled by `α`, and loan-id renaming is fixed by the positions of the borrow holders. The one choice point, whether to descend into seals and closures, gives two different results, but both are sound. It should be fixed for the canonicity of the checker's output, not for soundness. Arms that mint fresh `σ`s from the same counter can produce a shared name for unrelated values. That is still sound (the name is unconstrained outside each arm), but it is confusing, so mint names local to each arm.

**Interaction with A6.** Under refinement, a hole-bearing seal can normalise to a plain `loan_k` in one arm and stay a seal in the other. "Loan structure identical" then fails and valid code is rejected. Deferred fill keeps each loan at its place in both arms.

---

## A13. Termination of normalisation

Beyond A4 and A5, nothing. With A3's semantic guard and A4's occurrence rule, every seal's canonical call terminates on every instance. `nf`'s recursion into embedded values is structural. A seal can never contain itself, because that would need a recursive call on the same argument values, which the guard forbids. The risk comes back only if §6 stays syntactic.

---

## Smaller gaps found on the way

- **G1.** [Read]/[Borrow] of a value that *contains* a loan (as opposed to *being* one): v0 has no rule. Subsumed by A1's fix.
- **G2.** Following `p.1` through an abstract value: neither [Match] nor stuck (A3b). It must be an error, or a split in the style of Aeneas's symbolic expansion.
- **G3.** [Close] chooses its borrow-free or `&T` form from the result type. A computed result type (a large elimination that becomes `&Nat` after refinement) breaks the choice. Require `&` to appear syntactically in the codomain.
- **G4.** A match in the checked term on a seal (not on a `σ`) is not covered by [Split]. Lean generalises the neutral; v0 needs to say something.
- **G5.** Evaluated-but-unbound arguments are not in Ω, so in `f (&x) (&x.1)`, [Reorg] cannot find `borrow_x` to end it. That should be an error, and the rules should say so.

## Proposed changes, in priority order

1. The `loan ∉ v` premise on move, copy and borrow, lazily discharged and looking inside seals; a loan-free `uᵢ` as a precondition of [Close]. (A1, G1)
2. `Π(x : &T). B : Type`. (A2)
3. §6 → semantic guard on entry values, plus the CIC occurrence rule, plus `f` abstract while its body is checked. Separately, give pattern variables a loan, or invalidate them when their parent is written. (A3, A4, G2)
4. [Seal]: a seal is normal when its own call is stuck; seals carry their type. (A5)
5. Replace loan holes by deferred fills, i.e. region nodes whose fills are sealed `λw`. (A6, A7, A9c)
6. Nullary close-off = [Close] on the λ-lift of `t` over its free variables. (A10)
7. [Join] anti-unifies the goal jointly, with split restoration. (A12)
8. n-ary calls in the core. (A9b)
