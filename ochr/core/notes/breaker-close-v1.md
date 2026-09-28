# breaker-close, round 2: A1–A13 re-run against RULES v1.1, and attacks on what is new

**Summary.**
1. Verdict: v1.1 blocks A1–A13, but it has one **new closed proof of `Id Nat (S Z) Z`** (N1). P5 ("a call whose result type is a proposition is not run") applies to *calls*, and the new stuck-block rule turns a non-call block into a call. So a Prop-typed block that writes gives one normal form when it is sealed and later refined, and a different one when it is run directly.
2. Most important finding: N1. D14 is a stipulation about calls, so calls are no longer transparent: inlining or outlining a proof changes what a program does. The stuck-block rule outlines code. The principled repair is to make P5 a *consequence* rather than a stipulation: a proposition-typed term may not write, borrow or move any place from outside itself, except as an argument to a proposition-typed call. Skipping a proof is then the same as running it.
3. Check (1): D14 kills A2 in both versions (`J` and seal conversion), and `Π(x:&T).B : Type` is **not** needed. But D14 must be decided from the codomain's declared sort, and N1 needs the repair in line 2. Check (2): the inert-loan clause, together with [End] having no side condition, **does** handle A6. Deferred fill is not needed for soundness; it remains a simplification only.
4. Also must change (stuck blocks): infer each free place's capture mode the way Rust infers closure captures (copy what is only read, `&mut` what is written or borrowed, move what some arm moves) (N2, N3, N4). State the anonymous function's codomain (N5). A match on a seal in a checked program needs a rule (G4, which v1 makes pressing: after any non-tail match through a borrow, the place's content is a seal). Confidence: high on N1 (full derivation, v1.1 text only) and on the A-statuses; medium on "[End] without a side condition is sound", which is argued, not proved.
5. Not checked: the frame/[Call-type] soundness (breaker-frame's area); D12's generic-call check beyond what these attacks touch; universe levels. In-flight arguments (`f(&x, &x)`, G5) are still unspecified.

## Status of A1–A13 under v1.1

| # | v0 attack | v1.1 status | Blocked by |
|---|---|---|---|
| A1 | live loan copied into `L` | blocked | [Access] "before reading … also end every borrow whose loan occurs inside `content(p)`": reading `b` ends `borrow₂`, `r ↦ ⊥`, `*r := S Z` is an error. [Close]'s precondition states the invariant. Residual: in-flight arguments (G5 below) are the one route [Access] does not cover. |
| A2 | effectful inhabitants of a `Prop` | blocked, both versions | P5/[Call] (check (1) below). New companion bug N1. |
| A3 | entry value: writes before/after the match | blocked | [Rec] "strict subterm of that parameter's entry value σ, as refined so far": `Loop`'s and `Spin`'s arguments hold `Z` against entry `Z`, and `S σ'` against `S σ'`. Alias pattern variables remain; reading `(*x).1` after `*x := n` still has no rule (G2), which must be an error. |
| A4 | `f` escaping unapplied | blocked | [Rec] "`f` occurs only as the head of a call". `Knot`'s `Apply(f, x)` is rejected. |
| A5 | [Seal] re-closes itself | blocked | [Seal] "head call of `t` not eligible for [Close]" (D9). |
| A6 | holes re-run at a refinement | blocked | [End] (no side condition) + [Seal]'s inert loans (check (2) below). |
| A7 | hole in two fills | blocked | [End] "substitute … for every occurrence"; D18's owner sets. |
| A8 | writes before stuck, by-value stuck, two borrows, order | sound, as before | Unchanged [Close]; the lemma-overwrite cost is gone (P5). |
| A9 | canonicity | blocked / moot | (a) v1 has no top-level names in [Call] (`f` is the `fix` value), so the head is uniform. (b) D10. (c) loan names never reach a comparison: types capture by reading, and reading ends loans. |
| A10 | nullary close-off | blocked (`Liar`: the seal captures `σ`, not the place `n`) | Stuck-block rule. But the λ-lift has new problems: N1–N5. |
| A11 | ending order | no counterexample | [End] is substitution. Independent Ends commute by the substitution lemma, and dependent ones compose to the same value. Re-normalisation after a partial End treats the remaining loans as inert, which is a refinement; so canonicity now reduces to adequacy, which N1 breaks. |
| A12 | [Join] | blocked | D15: [Join] deleted. `Wrong`'s continuation runs against the unrefined goal `Eq Nat σ Z`, and `refl : ⊤` fails. |
| A13 | normalisation loops | none | [Rec] + D9. Stuck-block functions are non-recursive. |

---

## Check (1): is D14 enough for A2?

**`J` version.** `P h := Id Nat (let y = Z; h(&y); y) Z`. `h(&y)` has result type `Eq Nat Z Z`, which is a proposition, so [Call] does not run it and `&y` ends unchanged. So `P p₁ ≡ P p₂ ≡ Eq Nat Z Z ≡ ⊤`, and `J P d e : ⊤`. Blocked.

**Seal-conversion version.** `Use(p₁, &c, σ)` and `Use(p₂, &c, σ)` still convert (proof irrelevance on the embedded `p₁ ≡ p₂`). But at `n := Z` both run `h(x)`, which is P5-skipped, so both give `c = Z`. The conversion is now *true*. Blocked.

**Why it is enough.** A value `p : Π(x:&T). P` can be eliminated only by calling it, and every call is P5-skipped. So all inhabitants of the type are observationally equal, and proof irrelevance at that type is sound (meta-model §3.1, option (d)). `Π(x:&T).B : Type` is not needed.

Two conditions it silently relies on:
- **"B is a proposition" must be decided from the codomain's declared sort, statically.** That is when runtime erasure decides it. If v1 admits Coq-style cumulativity (`Prop ≤ Type_0`), then `G2(A : Type_0, a : A, x : &Nat) : A := (*x := S Z; a)` at `A := ⊤` is P5-skipped by a machine that looks at the instantiated `B`, but runs (and writes) in type-erased compiled code. v1 states `Prop : Type_0` but not whether cumulativity holds. Say "no cumulativity" (Lean's choice).
- **Calls must be the only way code gets outlined.** They are not: the stuck-block rule creates calls. That is N1.

## Check (2): does the inert-loan clause handle A6?

Yes. A6's program under v1.1:

```
P(x, n) := let t = G2(x, n); match n { Z => () | S _ => () }; *t := Z            // G2(x, n) := match n { Z => x | S _ => x }
[Def]: c₁ ↦ σ; x ↦ borrow₀ σ; t ↦ borrow_k ⌈L; let r = G2(&c, σₙ); *r⌉;  c₁ ↦ ⌈L; let r = G2(&c, σₙ); *r := loan_k; c⌉   // [Close], L = let c = σ
arm Z: σₙ := Z re-normalises c₁'s seal:
  ⟨{}, let c = σ; let r = G2(&c, Z); *r := loan_k; c⟩
  ⟨{c ↦ loan_j, r ↦ borrow_j σ}, *r := loan_k; c⟩                      // head call runs (not eligible for [Close])
  ⟨{c ↦ loan_j, r ↦ borrow_j loan_k}, c⟩                                // [Assign]; loan_k is inert (its borrow is outside the run)
  ⟨{c ↦ loan_k, r ↦ ⊥}, c⟩ ⇓ loan_k                                    // [Access] ends j: [End j] has no side condition, so loan_k travels
  c₁ ↦ loan_k                                                            // exactly the concrete LLBC state
```

The step that failed in v0 ("`w` must itself contain no loans") is gone. The continuation (checked once, from the closed-off state) writes `*t := Z`, drops `t`, and [End k] fills the seal. `P` is accepted. Deferred fill is **not needed for soundness**.

Two wording points it depends on:
- [Read] must treat an inert loan as borrow-free ("inert, like abstract values"). Otherwise `c ↦ loan_k` is neither borrow-free nor a borrow, and [Read] has no case.
- An unstated invariant: **every live loan inside a seal occurs after the seal's head call.** `L` is loan-free by [Close]'s precondition, and later [End]s substitute only into holes, which sit after `C`. So the head call never meets an inert loan, and only the final copy of `cᵢ` does. This invariant is what makes "inert" safe. It should be stated, because any future rule that places values into `L` after closing would break it.

What deferred fill would still buy is only simplicity: one meaning for `loan_k` (no "inert" mode) and no duplication (D18's owner sets become unnecessary). It is not a soundness reason.

---

## N1. P5 × stuck blocks: a closed proof of `Id Nat (S Z) Z` (BUG)

```
T : Π(n : Nat). Id Nat (let a = Z; let h = match n { Z => (a := S Z; refl) | S _ => refl }; a) Z
T(n) := refl
```

Checking `T` ([Def] at the generic call `T(σ)`):

```
{n ↦ σ} ⊢ refl : Id Nat (let a = Z; let h = match n {…}; a) Z                    // goal = [Call-type] of T(σ)
  Id Nat t Z ≡ Eq Nat ⟦t⟧ Z                                                      // W = ∅: a is bound inside t
  ⟦t⟧ on a private copy:
    ⟨{n ↦ σ, a ↦ Z}, let h = match n {…}; a⟩                                       // [Let]
    match n: content σ, stuck; not the body of a call, in a type-level term       // Stuck blocks (§3)
      anon := fix _ (n : Nat, a : &Nat) : ⊤ := match n { Z => (*a := S Z; refl) | S _ => refl }
      n is only read → value argument σ;  a is written → borrow argument &a       // the λ-lift
      [Close] on anon(σ, &a): row "borrow-free D" (D = ⊤); a ↦ ⌈let c = Z; anon(σ, &c); c⌉
    "values are kept in normal form": nf(⌈let c = Z; anon(σ, &c); c⌉)             // [Seal]
      ⟨{}, let c = Z; anon(σ, &c); c⟩
      [Call] anon: B = ⊤ is a proposition, so do not run it; &c ends unchanged     // P5
      ⇓ Z
    ⟨{n ↦ σ, a ↦ Z, h ↦ ⋆}, a⟩ ⇓ Z
  goal ≡ Eq Nat Z Z ≡ ⊤;  refl : ⊤ ✓                                               // D16
```

(If the stuck block is taken to [Call] first rather than straight to [Close], P5 fires there and `a` stays `Z` without any seal. Same outcome.)

Instantiating at `Z`:

```
T(Z) : [Call-type] with n ↦ Z
  ⟦t⟧: ⟨{n ↦ Z, a ↦ Z}, let h = match n {…}; a⟩
       match n: content Z, first arm, run inline (it is not a call): a := S Z; refl
       ⇓ S Z
  T(Z) : Eq Nat (S Z) Z                                                           // = Id Nat (S Z) Z; J gives Id Nat Z (S Z)
```

The same term `t` at the same instance `n = Z` has two normal forms. Sealing and then refining gives `Z`, because the block became a proposition-typed call and was skipped. Running directly gives `S Z`, because the block is inline code and does its write. The symbolic machine does not commute with substitution (Adequacy, §6), and `refl` turns the gap into a false equation. No runtime is involved: this is inconsistency inside the checker.

**Minimal fix (a).** A stuck block's anonymous call is exempt from P5: it is a device for naming a stuck computation and must not change its meaning. Then arm Z of the goal re-normalises to `Eq Nat (S Z) Z`, and `refl` fails.

**Principled fix (b), recommended.** Make P5 a theorem instead of a stipulation. A term whose type is a proposition may not write, borrow or move a place from outside itself, except as an argument to a proposition-typed call. In §4's terms, its footprint `W` outside proposition-typed calls must be empty. Then:
- Running a proof and skipping it agree, so calls, blocks and inlining are interchangeable, and N1's block `(a := S Z; refl)` is rejected when the type is formed.
- C1/A2 stay dead: `p₂ := λx. (*x := S Z; refl)` is rejected, so there is nothing for proof irrelevance to wrongly identify.
- The model's "`Out(d̄) = ⟦B⟧` for proposition-typed `B`" becomes true rather than enforced.
- The cost is nothing a user can see: a proof's writes to outer places are thrown away by P5 anyway. Local mutation inside proofs (on `let`-bound places) stays allowed, and it is still type-directed rather than a purity annotation (end goal 2).

**Decision implicated.** D14. It is right about *what* happens (proofs have no effects), but it achieves this by special-casing calls, and "complexity is evidence" applies: the special case is exactly what N1 exploits.

---

## N2–N5. The stuck-block λ-lift: how free places are passed

v1's rule is: "borrow variables it uses and places it writes become borrow arguments, places it only reads become value arguments". This leaves some places unclassified and classifies others wrongly.

**N2. A place that is only *borrowed* (passed as `&a`) is neither "written" nor "only read" (GAP; the narrow reading is unsound).**

```
Lost : Π(n : Nat). Id Nat (let a = Z; match n { Z => AddM(&a, S Z) | S _ => () }; a) Z
Lost(n) := refl
```

Suppose `a` is classed as "only read" because it never appears on the left of `:=`. Then it is a value argument: `anon(σ, Z)` borrows its *own* copy, `a` stays `Z`, the goal is `Eq Nat Z Z`, and `refl` checks. Directly, `Lost(Z)`'s type runs `AddM(&a, S Z)` and gets `Eq Nat (S Z) Z`: a second closed false proof. Fix: use §4's footprint criterion, *under `&_`*, on the left of `:=`, or a borrow-typed variable, applied to root places (so pattern-variable sub-places count for their root).

**N3. A borrow variable that is only *read* becomes a borrow argument, so its content turns into a seal (incompleteness, and it makes G4 pressing).**

```
F : Π(x : &Nat). Unit
F(x) := match *x { Z => () | S _ => () }; match *x { Z => () | S p => F(&p) }
```

The first match is non-tail. It is closed off with `x` as a borrow argument (it is a borrow variable the block uses), so `x ↦ borrow₀ ⌈let c = σ; anon(&c); c⌉`. That seal stays stuck on `σ` even though `anon` writes nothing. The second match now finds a *seal* at the head of `content(*x)`. [Split] only fires on an abstract `σ`, so there is no rule and `F` is rejected. `F` is fine Rust and terminates. So D15's "closing off is precise" is false for places the block only reads. Fix: a borrow variable the block only reads through (`*x` read or matched, never written, borrowed or moved) is passed as a *value* argument (a copy of `*x`), leaving `x`'s content untouched.

**G4 (still open, now pressing).** A match in a checked program on a place whose content head is a seal `⌈t⌉` has no rule. After any non-tail match that *writes* through a borrow, that place's content is a seal, so a second match on it is stuck. The standard answer is Lean's `generalize` then `cases`: replace every occurrence of `⌈t⌉` (in Ω, the goal and the stored types) by a fresh `σ''` and split on that. This is sound because the seal is a closed term, and it loses only the link between `σ''` and the seal's own inputs.

**N4. A borrow variable moved in one arm is reborrowed by the closed-off block (adequacy gap; harmless in compiled code).**

```
M : Π(x : &Nat) (n : Nat). Unit
M(x, n) := match n { Z => AddM(x, S Z) | S _ => () }; *x := Z
```

[Split] checks the arms separately: arm Z moves `x` into `AddM`, which is fine inside the arm. The continuation is checked once from the closed-off state. If `x` is passed by reborrow `&*x`, it survives, and `*x := Z` is accepted. The concrete machine at `n = Z` reads a moved `x` (`⊥`), which is an error. If instead `x` is passed by move, `x ↦ ⊥` and the valid `match n { Z => *x := Z | S _ => () }; *x := Z` is rejected. The compiled pointer code happens to do the right thing (it behaves like Rust's implicit reborrow), so this is a spec/adequacy gap rather than a false proof. Fix: move `x` into the block iff some arm moves it.

N2–N4 are one rule: **infer each free place's capture mode as Rust infers a closure's.**
- by copy, if it is only read;
- by `&mut`, if it is written or borrowed;
- by move, if some arm moves it.

**N5. The anonymous function's codomain is unstated (GAP).** [Close] picks its row, and P5 decides whether to run, from `B`. For a stuck block, `B` has to come from somewhere, and the arms are checked separately with no expected type. With `let v = match n { Z => Z | S _ => () }; S v`, a checker that takes `B` from the first arm treats `v : Nat` and accepts a program that builds `S ()` at `n = S _`. Fix: the block's type is a motive, and each arm is checked against it under its refinement (CIC's `match … return`). In type-level terms, which are only run and never checked arm by arm, stuck blocks need their arms split to establish that motive.

---

## N6. [End] without Aeneas's side condition (no bad derivation found)

Aeneas's End-Mut requires the ended borrow's content to be loan-free. v1 drops this: "loans inside `v` travel with it". Five attacks:

1. **Cycles.** A cycle needs a borrow's content to contain its own loan. That cannot happen:
   - Values in flight are loan-free. [Access] ends contained loans on every read, borrow and assign, and a moved borrow's content is loan-free by the same rule.
   - Loans are created only in two places. [Borrow] puts a fresh `ℓ` at the borrowed place, outside the new borrow's content. [Close] puts a fresh `k` into fills at the owners, outside `borrow_k`'s content, which is a loan-free seal.
   - [End] moves a content to its loan's position, which is outside the moved loans' own borrows.
2. **Reborrow outliving its parent.**
   ```
   let r2 = (let z = &x; &(*z).1); *r2 := S Z; x
   ```
   Dropping `z` ends it and `x ↦ S loan₂`; the write goes through `r2`; reading `x` ends `loan₂`, giving `S (S Z)`. Correct, and Rust accepts the same (a reborrow through a moved-in reference).
3. **Parent accessed while the reborrow is used later.**
   ```
   let z = &x; let r2 = &(*z).1; let t = x; *r2 := Z
   ```
   Reading `x` ends `z` (the loan travels), then "inside `content(x)`" ends `r2`, and `*r2 := Z` is an error. Rust also rejects.
4. **Match on the parent while the reborrow lives.** `match x` ends `z` only (it is on the path), leaving `x ↦ S loan₂`. The arm may still use `r2`. Rust rejects this, v1 accepts it, and it is sound: the match reads only the head `S`, which `r2` cannot change. This is D11's "more permissive, not unsound". Wording: "on the path to `p`" must include `p` itself when `content(p)` *is* a loan, or [Match] sees `loan_z` at the head and has no rule.
5. **Assign to the parent while the reborrow lives.** [Access] ends it (it is inside the content). Correct.

D11's own caveat (Rust rejects some accepted programs "once data has several fields") cannot bite yet. v1's places are `x | *p | p.1`, a chain with one child per node, so a borrow's siblings do not exist. Re-check this when pairs become places.

## N7 = G5. In-flight arguments (still open)

`f(&x, &x)` (Rust E0499). After the first argument, `x ↦ loan₁` and `borrow₁ (…)` is an *in-flight value*: big-step evaluation of the next argument does not see it. [Access] on the second `&x` must "end every borrow whose loan occurs on the path", but [End 1] can neither find `borrow₁` (to make it `⊥`) nor its content `v` (to substitute). No rule applies.

An implementation that skips the unfindable End, or re-reads `x`, hands `f` two live borrows of one place. Two borrows of one cell, one writing where the other points, is a use-after-free in compiled code. It also breaks [Close]'s "guaranteed by [Access]" and the frame lemma.

Fix: ending a borrow held by an in-flight argument is an error. Equivalently, bind each argument to a fresh `let` before evaluating the next, so [End] marks it `⊥` and the call is rejected for receiving `⊥`.

## N8. Type formation outside `Id` runs in the real Ω (incompleteness)

P2 says a type "is evaluated once, when it is formed, against the current environment"; only `Id` says "private copy". Forming `Π(_:Unit). Eq Nat x x` reads `x`, and [Access] ends any live reborrow into `x` in the *real* environment. So `let r = &x.1; let T = Π(_:Unit). Eq Nat x x; *r := Z` is rejected, although types are erased at runtime. It is not unsound: the checker is only stricter, and the snapshot value is the same. Fix: every type formation runs on a private copy, as `Id` already does.

---

## Proposed changes, in priority order

1. **N1.** Make P5 a consequence: a proposition-typed term's footprint outside proposition-typed calls is empty. If a smaller change is wanted, exempt stuck-block calls from P5 instead.
2. **N2–N4.** Stuck blocks capture free places in Rust closure modes: copy if only read, `&mut` if written or borrowed (§4's criterion, on root places), move if some arm moves.
3. **N5.** The stuck block's codomain is a motive, and each arm is checked against it under its refinement.
4. **G4.** A match in a checked program on a seal: generalise every occurrence of the seal to a fresh `σ''`, then [Split].
5. **G5.** Ending a borrow held by an in-flight argument is an error (or A-normalise calls).
6. **Wording.**
   - [Read] treats inert loans as borrow-free.
   - State the invariant "every live loan inside a seal occurs after its head call".
   - [Access]'s path includes `p`.
   - All type formation runs on a private copy.
   - "Proposition" in P5 is the codomain's declared sort, with no cumulativity.
   - G2: following `.1` through an abstract value is an error.

## Attacks this round (one line each)

- A1 blocked ([Access]; residual G5).
- A2 blocked, `J` and seal versions (P5); `Π(x:&T).B : Type` not needed.
- A3 blocked ([Rec] entry value; G2 wording open).
- A4 blocked ([Rec] head-only).
- A5 blocked (D9).
- A6 blocked (inert loans + [End]); deferred fill optional.
- A7 blocked (D11, D18).
- A8 sound.
- A9 blocked or moot.
- A10 blocked (λ-lift), but see N1–N5.
- A11 no counterexample (reduces to adequacy).
- A12 blocked (D15).
- A13 none.
- N1 **BUG**: closed `Id Nat (S Z) Z` from P5 × stuck blocks.
- N2 **GAP**: under the narrow reading of "writes", a second closed false proof.
- N3 incompleteness: a read-only borrow variable becomes a seal; with G4, blocks `F`.
- N4 adequacy gap: a move in one arm vs a reborrow in the block.
- N5 **GAP**: stuck-block codomain unstated.
- N6 [End] with no side condition: no bad derivation (five attacks).
- N7 = G5 still open.
- N8 incompleteness: types formed in the real Ω.
