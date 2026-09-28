# deriver-e346-v1: E3, E4, E6 under RULES.md v1 (and v1.1, which landed mid-round)

## Summary

1. **Verdict:** E3 and E4 go through under v1: `AddToOne` is accepted with the right backward functions in the loans, `AddToOneZero` checks with no `refl` padding, and the modular proof of `TwiceMZero` checks as first written (P5). Every round-1 attack is blocked: `Oops2` by D13, `Bad` by D15, `Bot'`/`Loop`, `Grow` and `Spin` by [Rec]. v1 as first issued had a closed proof, `fix f (x) := Apply(f, x)` (N1; meta-model-v1 R2 and breaker-close A4 found it too). v1.1, which landed during this round, fixes it. Under v1.1 two holes remain: a Prop-typed stuck block (N12, confirming meta-model-v1 R1), and, under a reading the text permits, a match on a sealed program whose arms are never checked (N6, `Knot3`).
2. **Most important finding:** the stuck-block sentence of §3 is lambda lifting stated in one line, and three of its unstated choices decide soundness or adequacy. How is a borrow variable passed? Reborrowing it always accepts a use of a maybe-moved borrow (N2). What if the scrutinee is a sealed program? Closing off unchecked arms gives `Knot3`, a closed proof (N6). Does a Prop-typed block run? If P5 skips it, it gives meta-model's `Q` (N12).
3. **RULES.md must change:** the stuck-block rule must say how each free place is passed (move iff some arm moves or assigns it, reborrow iff an arm writes or borrows through it, otherwise copy what is read; maximal prefixes only), what the block's type is (plus a `let x : T =` form), and that the lifted function is canonical (N2–N5). A match on a non-σ neutral must generalise, not close off unchecked arms (N6). P5 must be keyed on Prop-typed *terms*, not calls (N12). Restore "an abstract function closes off at once" (N7). Add `⊥`/`⋆` to the grammar (N8). v1.1's [Rec] should say that it applies inside nested functions too (N1 residual).
4. **Confidence:** high for the E3/E4 derivations, for the blocked attacks, for N1 under v1 and for my re-check of `Q` (N12). Medium for N6, which needs a reading the text permits but does not state, and medium that N2's three-way classification is the simplest correct one (breaker-close-v1 proposes the same Rust-closure-style inference independently).
5. **Not checked:** RULES moved to v1.1 during this round; I re-checked N1 and `Knot3` against the v1.1 diff (it touches only [Close]'s precondition and [Rec]), not everything else. Other agents' attacks (breaker-close A1/A6, breaker-frame, meta-model C1/C2) are checked only as far as naming the v1 rule that answers them. N9 is only re-noted. The Lean formalisation is not checked.

## Findings (one line each)

- **N1** SOUNDNESS in v1, FIXED in v1.1: `Knot := fix f (x : Nat) : Eq Nat Z (S Z) := Apply(f, x)` passed v1's [Rec] vacuously, and `Knot(Z)` was a closed proof checked in finite time (P5 does not run it); the same with `let g = f; g(x)`. v1.1's "f occurs only as the head of a call" rejects both. Residual: `Apply(fix _ (y) := f(y), x)` has `f` in head position inside a nested function; the literal v1.1 text makes [Rec] check it against `f`'s entry value (rejected), but say so explicitly.
- **N2** §3 "Stuck blocks": "borrow variables it uses … become borrow arguments" does not say move or reborrow. Move-always rejects `(match b { Z => *x := Z | S _ => () }); AddM(x, 0)`, which is fine in both arms. Reborrow-always accepts `let r = match b { Z => x1 | S _ => x2 }; AddM(r, y); AddM(x1, 0)`, which reads a moved `x1` when `b = Z` (adequacy fails). Fix: move iff some arm moves or assigns the variable; else reborrow if some arm writes or borrows through it; else copy the places read (breaker-close-v1 N2–N4 proposes the same Rust-closure-style inference, independently).
- **N3** §3 "Stuck blocks": free places are not reduced to maximal prefixes. A block that writes `*x` in one arm and `p = (*x).1` in the other passes `&*x` and `&p`, and borrowing the second ends the first. Fix: pass the maximal written prefixes, and rename sub-places inside the lifted body.
- **N4** §3/§5: the lifted function's result type is never stated. The [Close] table needs it, and so does P5 (whether the block runs). For arms whose types depend on the scrutinee (proof arms), it has to come from an annotation `let h : T = match …`, with each arm checked against `T` refined. Fix: say so.
- **N5** §3: the anonymous function must be built canonically (parameter order, names), else the same inline match in a goal and in a proof gives two non-convertible neutrals. With it, inline `SelAdd` checks (§E3.4).
- **N6** §5 [Split] is still defined only for an abstract `σ` (round-1 F10). A non-tail match on a sealed program is "a stuck match that is not the body of a call", and closing it off without checking its arms skips [Rec] and the borrow checker inside them: `Knot3` (§E6.8) is a closed proof of `Eq Nat Z (S Z)` under that reading. Fix: generalise the neutral to a fresh `σ` and [Split], or reject (breaker-close-v1 G4 flags the missing rule; `Knot3` shows the unsound reading).
- **N7** §3 [Call]/[Close]: v1 dropped v0's "abstract functions close off immediately"; `σ_f(())` has no rule (E4). Fix: restore the clause.
- **N8** §1/§2: `⊥` (used in D17 and in every negation) and `⋆` (returned by P5) are not in the grammar. D16 dropped the `⊥` rule, so `Eq Nat Z (S Z)` no longer computes to anything. The negations in E6 go through with `noConf` via `J` (§E6.4).
- **N9** (re-noted, breaker-close A3) pattern variables are aliases with no loan. After `x := n` inside `S y => …`, reading `y` follows `.1` through an abstract `σ_n`, and v1 has no rule for that.
- **N10** (precision, not soundness) closing off loses what the arms agree on. `(match b { Z => *x := Z | S _ => *x := Z }); (refl : Id Nat *x Z)` is rejected: `*x` holds a sealed program, where v0's [Join] kept `Z`. The workaround is to split the continuation or hoist the common write. A fix exists but costs two re-runs per seal (§E3.5); I recommend living with it.
- **N12** SOUNDNESS (confirms meta-model-v1 R1), P5: it is keyed on *calls*, but a stuck Prop-typed block becomes a call (writes skipped) while the same block run concretely writes. `Q(Z, Z) : Eq Nat (S Z) Z`. Arguments of a skipped call also keep their effects. Fix: any Prop-typed term runs on a private copy, arguments included.
- **N11** (observation) granularities differ: the machine closes off a whole call whose body is stuck, the checker closes off the stuck block inside a body it checks. That is harmless as long as proofs about `F` are stated through `F` (they are); it is why an inline-match proof does not match a `Sel`-stated goal (§E3.4).

## Conventions (changes from round 1)

- As v1: definitions are checked at the generic call ([Def]). The fresh owned places are `c1, c2, …`, so there are no ghosts, and they sit in the frame below the call. `d1, d2, …` are the locals [Close] binds in `L`. `A(v, w) := ⌈let d = v; AddM(&d, w); d⌉`, `A(v) := A(v, 0)`, `A₁(v) := A(v, S Z)`; as before `A(Z, w) ≡ w` and `A(S v, w) ≡ S A(v, w)` by [Seal] re-runs.
- `⊥ := Π(P : Prop). P` (N8). `noConf : Π(h : Eq Nat Z (S Z)). ⊥ := λh P. J(Nat, λn. match n { Z => ⊤ | S _ => P }, h, refl)`. The motive's type-level match is fine: the motive returns `Prop` (a sort, not a proposition), so its calls run.

## E3. Join is gone: closing off the non-tail match

### E3.1 `AddToOne` is accepted

```
AddToOne := fix AddToOne (b : Nat, x1 : &Nat, x2 : &Nat, y : Nat) : Unit := let r = match b { Z => x1 | S _ => x2 }; AddM(r, y)
```

```
[Def]: generic call AddToOne(σ_b, &c1, &c2, τ) from { c1 ↦ σ1, c2 ↦ σ2 }; goal Unit
  Ω₀ = { c1 ↦ loan_1, c2 ↦ loan_2 | b ↦ σ_b, x1 ↦ borrow_1 σ1, x2 ↦ borrow_2 σ2, y ↦ τ }
  let r = match b {…}: content σ_b abstract, not in tail position                        // [Split]
    arm σ_b := Z: x1 holds a borrow, moved; result borrow_1 σ1; no error                   // [Read]
    arm σ_b := S σ_b': x2 moved; result borrow_2 σ2; no error                              // [Read]
    close off, from Ω₀ (the arms' refinements and runs are discarded):                      // §3 stuck block
      free places: b read → value; x1, x2 moved by some arm → moved in (N2)
      g := fix _ (b' : Nat, x1' : &Nat, x2' : &Nat) : &Nat := match b' { Z => x1' | S _ => x2' }    // result type: the arms' (N4)
      g(σ_b, borrow_1 σ1, borrow_2 σ2); x1 ↦ ⊥, x2 ↦ ⊥                                     // [Read] ×3
      g's body stuck on σ_b; B = &Nat, fresh k; L = let d1 = σ1; let d2 = σ2; C = g(σ_b, &d1, &d2)   // [Close], row &T
        result borrow_k V,  V = ⌈L; let r = C; *r⌉
        loan_1 := H1[loan_k] = ⌈L; let r = C; *r := loan_k; d1⌉,  loan_2 := H2[loan_k] = ⌈…; d2⌉      // one loan, two occurrences (D11)
  Ω₁ = { c1 ↦ H1[loan_k], c2 ↦ H2[loan_k] | b ↦ σ_b, x1 ↦ ⊥, x2 ↦ ⊥, y ↦ τ, r ↦ borrow_k V }
  AddM(r, y): arguments borrow_k V (r ↦ ⊥), τ                                            // [Read] ×2
    body: match *x on V, a neutral: stuck                                                 // [Match]
    L' = let d = V, C' = AddM(&d, τ): result (); every loan_k := A(V, τ)                  // [Close], row Unit
  Ω₂ = { c1 ↦ H1[A(V, τ)], c2 ↦ H2[A(V, τ)] | b ↦ σ_b, x1 ↦ ⊥, x2 ↦ ⊥, y ↦ τ, r ↦ ⊥ }
  result () : Unit ≡ goal ✓; [Drop] the frame: nothing holds a loan ✓
```

Refining `σ_b := Z` re-runs the fills to `c1 ≡ A(σ1, τ)`, `c2 ≡ σ2`, and `σ_b := S σ'` to `c1 ≡ σ1`, `c2 ≡ A(σ2, τ)`. That is what the hand-duplicated version produces.

### E3.2 Errors in the continuation are reported once

```
AddToOneX(b, x1, x2, y) : Unit := let r = match b { Z => x1 | S _ => x2 }; AddM(r, y); AddM(x1, 0)
  … as E3.1 up to Ω₂ …
  AddM(x1, 0): x1 ↦ ⊥                                                                    // [Read]: ERROR, once, at this line
```

The error says "x1 may have been moved", with no "in the case where b = Z". That is Rust's E0382 for the same program. Errors inside an arm are still reported per arm, as they must be. One small duplication: if an arm reads a place that is already `⊥`, the arm check reports it and evaluating the block's arguments reports it again, so stop after the arm error.

### E3.3 Proving something about it

```
AddToOneZero : Π(b : Nat, x1 : &Nat, x2 : &Nat). Id Unit (AddToOne(b, x1, x2, 0)) ()
AddToOneZero(b, x1, x2) := match b { Z => AddMZero(x1) | S _ => AddMZero(x2) }
```

```
[Def]: Ω₀ = { c1 ↦ loan_1, c2 ↦ loan_2 | b ↦ σ_b, x1 ↦ borrow_1 σ1, x2 ↦ borrow_2 σ2 }
  goal ([Call-type]): W = owners(1) ∪ owners(2) = {c1, c2}
    ⟦AddToOne(b, x1, x2, 0)⟧ on a copy: the machine runs AddToOne's body; its match on σ_b is stuck inside a
      running call, so [Close] fires at the call (not a stuck block, N11): L = let d1 = σ1; let d2 = σ2,
      C = AddToOne(σ_b, &d1, &d2, Z); result (); c1 ↦ P1 = ⌈L; C; d1⌉, c2 ↦ P2 = ⌈L; C; d2⌉; observation ((), (P1, P2))
    ⟦()⟧: end borrow_1, borrow_2: ((), (σ1, σ2))
    G ≡ Eq Unit () () ∧ (Eq Nat P1 σ1 ∧ Eq Nat P2 σ2) ≡ Eq Nat P1 σ1 ∧ Eq Nat P2 σ2                        // pairs, reflexivity, ⊤ unit
  [Split] σ_b := Z (tail):
    P1: re-run with the head call ineligible; AddToOne(Z, …) takes the Z arm, the inner AddM closes off: ≡ A(σ1)
    P2: x2's borrow ends when AddToOne returns: ≡ σ2
    goal_Z ≡ Eq Nat A(σ1) σ1 ∧ Eq Nat σ2 σ2 ≡ Eq Nat A(σ1) σ1 ∧ ⊤ ≡ Eq Nat A(σ1) σ1                             // reflexivity drops the untouched owner
    AddMZero(x1): [Call-type] with x := borrow_1 σ1, W = {c1}: ≡ Eq Nat A(σ1) σ1 ✓; not run (P5): borrow_1 ends unchanged
  [Split] σ_b := S σ': symmetric ✓
```

Round-1 F12 is gone: the natural proof checks with no `refl` padding. A second theorem exercises a stuck block *inside a type*:

```
AddToOneSpec : Π(b : Nat, x1 : &Nat, x2 : &Nat, y : Nat). Id Unit (AddToOne(b, x1, x2, y)) (match b { Z => AddM(x1, y) | S _ => AddM(x2, y) })
AddToOneSpec(b, x1, x2, y) := match b { Z => refl | S _ => refl }

goal: W = {c1, c2}; LHS as above, ((), (P1, P2)) with y := τ
  RHS: a type-level match, stuck, not the body of a call: stuck block over b, x1, x2 (moved), y       // §3
    g_u(σ_b, borrow_1 σ1, borrow_2 σ2, τ), [Close] row Unit: c1 ↦ R1 = ⌈L; g_u(σ_b, &d1, &d2, τ); d1⌉, c2 ↦ R2
  G ≡ Eq Nat P1 R1 ∧ Eq Nat P2 R2
arm σ_b := Z: P1, R1 ≡ A(σ1, τ);  P2, R2 ≡ σ2;  G_Z ≡ ⊤ ∧ ⊤ ≡ ⊤; refl ✓.  arm S: symmetric ✓
```

### E3.4 Pick, KeepB, SelAdd re-run

**Pick.** `Pick(b, x1, x2) : &Nat := match b { Z => x1 | S _ => x2 }` has its match in tail position. [Split] runs each arm: one returns its borrow, and [Drop] of the frame ends the other. Accepted. `let r = Pick(b, x1, x2); AddM(r, y)` then runs exactly as E3.1, with `Pick` in place of `g` in `C`. The inline version and the helper version are both accepted now, as D15 says. Their neutrals differ only in the head (`g` versus `Pick`).

**KeepB** (round-1 F3, the read-only match that cut `b` loose):

```
KeepB(b) : Id Nat (Add(b, 0)) b := (match b { Z => () | S _ => () }); AddZero(b)
[Def]: { b ↦ σ_b }, goal ≡ Eq Nat A(σ_b) σ_b                                                        // W = ∅
  non-tail match on σ_b: arms fine; stuck block over b (read → value): g(σ_b), row Unit → ()            // [Split], §3
  b ↦ σ_b still: closing off never replaces a scrutinee
  AddZero(b): [Call-type], x := σ_b: ≡ Eq Nat A(σ_b) σ_b ✓; not run (P5)                              // ACCEPTED
```

**SelAdd** (`Sel(b, x, y) := match b { Z => x | S _ => y }`):

```
goal stated with Sel:  Id Nat (Add(Sel(b, x, y), 0)) (Sel(b, x, y))  ≡ Eq Nat A(s) s,  s = ⌈Sel(σ_b, σ_x, σ_y)⌉
(a) let r = match b { Z => x | S _ => y }; AddZero(r)     r ↦ ⌈g(σ_b, σ_x, σ_y)⌉ ≢ s: REJECTED (N11: different heads)
(b) let r = Sel(b, x, y); AddZero(r)                     [Call] Sel closes off: r ↦ s; AddZero(r) ≡ Eq Nat A(s) s ✓
(c) match b { Z => AddZero(x) | S _ => AddZero(y) }       [Split] in tail position; arm Z: s ≡ σ_x ✓
goal stated inline:  Id Nat (Add(match b { Z => x | S _ => y }, 0)) (match b { Z => x | S _ => y })
  both occurrences are stuck blocks: ≡ Eq Nat A(m) m, m = ⌈g(σ_b, σ_x, σ_y)⌉
(a') proof (a) against it: r ↦ ⌈g(σ_b, σ_x, σ_y)⌉ = m ✓, provided the goal's g and the proof's g are the same closure (N5)
```

So the rule is uniform: a statement and its proof agree when they name the stuck computation the same way. That needs the lifted function to be canonical (N5), e.g. parameters in order of first occurrence and the arms as written.

### E3.5 What closing off loses (N10)

A value on which both arms agree survives [Join]'s anti-unification, but not closing off:

```
fix _ (b : Nat, x : &Nat) : Unit := (match b { Z => *x := Z | S _ => *x := Z }); let e = (refl : Id Nat *x Z); ()
[Def]: { c ↦ loan_1 | b ↦ σ_b, x ↦ borrow_1 σ }
  stuck block: x written through, not moved → reborrowed (N2): &*x → borrow_2 σ, x ↦ borrow_1 loan_2
    g(σ_b, borrow_2 σ), row Unit: loan_2 := K = ⌈let d = σ; g(σ_b, &d); d⌉; x ↦ borrow_1 K         // [Close]; K stays sealed (head ineligible, stuck on σ_b)
  (refl : Id Nat *x Z): W = {c}: ⟦*x⟧ = (K, K), ⟦Z⟧ = (Z, K); ≡ Eq Nat K Z ∧ ⊤ ≡ Eq Nat K Z; refl : ⊤ ✗    // REJECTED
```

`K` is `Z` under both refinements, but no rule looks. v0's [Join] kept `*x ↦ Z`, since the two arms agree there. Workarounds: write `*x := Z` once after the match, or move the continuation into the arms. A fix that keeps naturality: *[Seal] may normalise `⌈t⌉`, whose head call is stuck on `σ`, to `v` when re-running it under `σ := Z` and under `σ := S σ'` both give `v` with `σ'` not free.* It is natCase with equal branches, valid in the model, but costs two re-runs per seal, exponential in nesting, on every seal and not just blocks. I would not add it: Lean does not identify `match b with | 0 => 0 | _ => 0` with `0` either.

## E4. Opaque functions under v1

### E4.1 `Twice`, `TwiceM`

`Twice := fix _ (f : Π(u : Unit). Unit) : Unit := f(()); f(())`. [Def]: `{ f ↦ σ_f }`, goal `Unit`. `f(())` evaluates `f` to `σ_f`, and v1 has no rule for calling an abstract function: [Call] is for `fix` values, and [Close] needs "a stuck body" (N7). Restoring v0's clause ("an abstract function closes off at once": `L` empty, `C = σ_f(())`, row Unit → `()`), both calls return `()`, and `Twice` checks as before.

`TwiceM := fix _ (f : Π(z : &Nat). Unit, x : &Nat) : Unit := f(&*x); f(&*x)`. With N7 restored the run is the round-1 run with `c` in place of the ghost: `*x` ends as `N₂ = ⌈let d = ⌈let d = σ; σ_f(&d); d⌉; σ_f(&d); d⌉` and `c ↦ N₂` after [Drop].

### E4.2 `TwiceMZero`, the direct proof: no Eq rule needed

```
TwiceMZero : Π(x : &Nat). Id Unit (TwiceM(g, x)) ()        g := fix _ (z : &Nat) : Unit := AddM(z, 0)
TwiceMZero(x) := match *x { Z => refl | S p => TwiceMZero(&p) }
```

```
[Def]: Ω₀ = { c ↦ loan_1 | x ↦ borrow_1 σ }; W = owners(1) = {c}
  ⟦TwiceM(g, x)⟧: the two g-calls each run AddM, which closes off (innermost stuck call, top-level head):
    loan_2 := A(σ), then loan_3 := A(A(σ)); TwiceM's [Drop] ends borrow_1: c ↦ A(A(σ)); observation ((), A(A(σ)))
  ⟦()⟧ = ((), σ);  G ≡ Eq Nat A(A(σ)) σ
  [Split] σ := Z: A(A(Z)) ≡ Z; G ≡ Eq Nat Z Z ≡ ⊤; refl ✓
  [Split] σ := S σ': x ↦ borrow_1 (S σ'), p = (*x).1
    G_S ≡ Eq Nat (S A(A(σ'))) (S σ')                                     // A(S v) ≡ S A(v), inner first; no injectivity in v1, so it stays
    TwiceMZero(&p): &p → borrow_2 σ', x ↦ borrow_1 (S loan_2)             // [Access]: no loan on the path; [Borrow]
      [Rec]: content σ', a strict subterm of the refined entry S σ' ✓
      [Call-type]: x̂ := borrow_2 σ'; loan_2 sits in borrow_1's content, so W = owners(1) = {c}
        ⟦TwiceM(g, x̂)⟧: loan_2 := A(A(σ')), then end borrow_1: c ↦ S A(A(σ')). ⟦()⟧: c ↦ S σ'
        ≡ Eq Nat (S A(A(σ'))) (S σ') = G_S, symbol for symbol ✓
      not run (P5): borrow_2 ends unchanged, x ↦ borrow_1 (S σ')
```

Dropping D6's injectivity costs nothing here: the owner of the IH's argument is the outer place `c`, so the `S` sits inside both observations.

### E4.3 The modular proof now checks (P5)

The core has no implicit arguments, so the middle term of `trans` has to be named; `let v = *x` gives a name for `σ`, and `Add(v, 0)` evaluates to `A(σ)`.

```
trans : Π(T : Type_0, a : T, b : T, c : T, p : Eq T a b, q : Eq T b c). Eq T a c           -- from J
TwiceMZero'(x) := let v = *x; let h1 = AddMZero(&*x); AddM(&*x, 0); let h2 = AddMZero(&*x);
                  trans(Nat, Add(Add(v, 0), 0), Add(v, 0), v, h2, h1)
```

```
[Def]: { c ↦ loan_1 | x ↦ borrow_1 σ }, goal G ≡ Eq Nat A(A(σ)) σ (E4.2)
  let v = *x: v ↦ σ                                                                  // [Read] copy
  let h1 = AddMZero(&*x): &*x → borrow_2 σ
    type: W = owners(2) = owners(1) = {c}: ≡ Eq Nat A(σ) σ                            // [Call-type]
    not run: borrow_2 ends unchanged, x ↦ borrow_1 σ                                  // P5 (round 1: x ↦ borrow_1 Q(σ))
  AddM(&*x, 0): Unit, runs; stuck on σ; [Close]: x ↦ borrow_1 A(σ)                     // [Call], [Close]
  let h2 = AddMZero(&*x): &*x → borrow_3 A(σ); AddM stuck on the neutral A(σ):
    ≡ Eq Nat A(A(σ)) A(σ); not run, x ↦ borrow_1 A(σ)                                 // [Call-type], P5
  trans(…): arguments evaluate to Nat, A(A(σ)), A(σ), σ, ⋆, ⋆                         // Add(v, 0) runs Add: AddM closes off, x read: A(σ)
    p = h2 : Eq Nat A(A(σ)) A(σ) ✓, q = h1 : Eq Nat A(σ) σ ✓; result Eq Nat A(A(σ)) σ ≡ G ✓; not run
```

Accepted. The proof's own `AddM(&*x, 0)` does write `x` in the checker's run, but nothing observes it: the goal was fixed at the generic call, and the whole proof is erased at runtime.

## E6. Must fail, re-run under v1

### E6.1 Use of a moved borrow: rejected

`fix _ (x : &Nat) : Unit := AddM(x, 0); AddM(x, 0)`: the first call moves `x` (`x ↦ ⊥`), and [Close] fills `loan_1` with `A(σ)`. The second call's [Read] of `x` finds `⊥`: an error. P5 does not change the moving: `AddMZero(x); AddM(x, 0)` is still rejected, because P5 ends the moved borrow unchanged and `x` stays `⊥`. The programmer writes `AddMZero(&*x)`, as P3 intends.

### E6.2 Write, then `refl` against the fixed goal: rejected

```
fix _ (x : &Nat) : Id Nat *x 5 := *x := 5; refl
[Def]: { c ↦ loan_1 | x ↦ borrow_1 σ }; W = {c}; ⟦*x⟧ = (σ, σ), ⟦5⟧ = (5, σ); goal ≡ Eq Nat σ 5 ∧ ⊤ ≡ Eq Nat σ 5
  *x := 5; refl : ⊤;  ⊤ ≡ Eq Nat σ 5 needs σ ≡ 5                                                    // REJECT at [Def]'s conversion
```

### E6.3 Closed proofs of `Eq Nat Z (S Z)`: every round-1 attack, and which v1 rule stops it

| attack | v1 outcome | rule |
|---|---|---|
| `refl` | rejected: `Eq Nat Z (S Z)` does not reduce, and `refl : ⊤` needs `Z ≡ S Z` | §4 |
| D2 snapshot (`let h : Id Nat x Z := refl; x := S Z; h`) | rejected: stored types are values | P2 |
| `Oops2` (Π-typed hypothesis re-read after a write) | rejected, below | D13, [Call-type] |
| `Bad` (stored types across [Join]) | rejected: nothing is merged; the continuation starts from the pre-split state, where `h : Eq Nat σ_b Z` | D15, [Split] |
| `Loop` / `Bot'` (write before the match) | rejected at the recursive call, §E6.10 | [Rec] (D17) |
| `Grow`, `Spin` (write to the pattern variable after the match) | rejected, §E6.10 | [Rec] |
| write outside the footprint | none found: owners are sets, holes are followed through borrow contents | §4, D18 |
| Unit collapse hiding a write | none: row Unit collapses the result only | [Close] |
| loan-ending order | none found; ending is substitution with no side condition | D11 |
| meta-model C1 (`P₁`/`P₂` under proof irrelevance) | blocked: `P₂(&a)` is not run, so `F(P₁) ≡ F(P₂) ≡ ⊤` | P5 |
| **`Knot`, `Alias` (`f` passed unapplied)** | **v1: ACCEPTED, closed proof** (§E6.9); v1.1: rejected | [Rec] head-only clause (v1.1) |
| **`Knot3` (match on a sealed program, arms unchecked)** | **accepted under one reading**, §E6.8 | N6 |

`Oops2` in v1 form, with target `Eq Nat (S Z) Z`:

```
Oops2 := fix _ (x : Nat, h : Π(u : Unit). Id Nat x Z) : Id Nat (S x) Z := x := S x; h(())
[Def]: generic call Oops2(σ_x, σ_h); h's domain is formed with x := σ_x and captures it: h : Π(u : Unit). Eq Nat σ_x Z
  goal ≡ Eq Nat (S σ_x) Z
  x := S x: x ↦ S σ_x                                                                            // [Assign]
  h(()): [Call-type]: B's free x was captured, ≡ Eq Nat σ_x Z; not run (P5)
  Eq Nat σ_x Z ≢ Eq Nat (S σ_x) Z                                                                 // REJECT
```

### E6.4 `Π(x : Nat). Id Unit (AddM(&x, 0)) (AddM(&x, 1))`: unprovable; negation provable (now with `noConf`)

The goal at the generic call is `Eq Nat A(σ) A₁(σ)` (`W = {x}`). The Z arm gives `Eq Nat Z (S Z)`, which no longer reduces to `⊥` (D16 dropped the rule) but is not `⊤` either, so `refl` is rejected. The negation, with `inj : Π(a b : Nat, e : Eq Nat (S a) (S b)). Eq Nat a b` from `J`:

```
NotAddM01 := fix f (x : Nat, h : Id Unit (AddM(&x, 0)) (AddM(&x, 1))) : ⊥ := match x { Z => noConf(h) | S p => f(p, inj(Add(p, 0), Add(p, 1), h)) }
[Def]: { x ↦ σ, h ↦ σ_h }, h : Eq Nat A(σ) A₁(σ), goal ⊥
  [Split] σ := Z: h : Eq Nat Z (S Z); noConf(h) : ⊥ ✓
  [Split] σ := S σ': h : Eq Nat (S A(σ')) (S A₁(σ'))                                   // refinement of the stored type
    Add(p, 0) ⇓ A(σ'), Add(p, 1) ⇓ A₁(σ'): inj(…) : Eq Nat A(σ') A₁(σ') ✓                  // the sealed programs have source names
    f(p, …): [Rec] σ' ✓; [Call-type]: h's domain at x := σ' ≡ Eq Nat A(σ') A₁(σ') ✓; result ⊥ ✓
```

### E6.5 A type formed before a mutation

`fix _ (x : Nat) : Id Nat x x := let h = (refl : Id Nat x x); x := S x; h` is accepted, correctly. The goal is now `⊤` outright (reflexivity), and `h : ⊤` is stored before the write. D2's variant (`x ↦ Z`; `h : Id Nat x Z` stored as `⊤`; `x := S Z`; `(h : Id Nat x Z)` now `Eq Nat (S Z) Z`) is rejected: `⊤ ≢ Eq Nat (S Z) Z`. The types-in-places variant (`T := Unit` after `n : T` was stored as `Nat`) is rejected. The Π variant is `Oops2`, above. (Ascription `(t : T)` is not in v1's grammar; I use it as sugar for a `let` with a type, which v1 also lacks, N4.)

### E6.6 Returning a borrow of a local: rejected

`fix _ (u : Unit) : &Nat := let z = Z; &z`: [Let]'s [Drop] of `z` finds `loan_1`, an error. `let z = n; TailM(&z)`: [Close] row &T leaves `z ↦ ⌈…; *r := loan_k; d⌉`; a loan inside a dropped owned value is an error, and since D11 loans inside sealed programs count. `fix _ (z : Nat) : &Nat := let r = &z; &*r`: dropping `r` ends `borrow_1`, which substitutes `loan_2` into `z` (loans travel, D11); the frame's [Drop] of `z` then finds `loan_2`, an error.

### E6.7 New piece: closing off a stuck block. What are its free places? (N2–N4)

**Move or reborrow (N2).** The rule makes "borrow variables it uses" borrow arguments. Two programs pull in opposite directions:

```
Bump := fix _ (b : Nat, x : &Nat) : Unit := (match b { Z => *x := Z | S _ => () }); AddM(x, 0)
  move reading: x moved into g; x ↦ ⊥; AddM(x, 0) reads ⊥                            // REJECTED, though both arms leave x live
  reborrow reading: &*x → borrow_2 σ, x ↦ borrow_1 loan_2; g(σ_b, borrow_2 σ), row Unit: loan_2 := K = ⌈let d = σ; g(σ_b, &d); d⌉
    x ↦ borrow_1 K; AddM(x, 0): stuck on K; [Close]: loan_1 := A(K)                     // ACCEPTED ✓

AddToOneX (§E3.2) under the reborrow reading:
  g(σ_b, &*x1, &*x2): x1 ↦ borrow_1 H1[loan_k], x2 ↦ borrow_2 H2[loan_k], r ↦ borrow_k V
  AddM(r, y) fills loan_k; AddM(x1, 0): x1 holds a borrow → ACCEPTED
  but the concrete run with b = Z moved x1 into r: x1 ↦ ⊥, and AddM(x1, 0) is an error         // adequacy fails
```

So neither uniform reading works. The rule that does: *a borrow variable is moved into the block iff some arm moves it or assigns it; otherwise it is reborrowed (`&*x`) iff some arm writes, borrows or reborrows through it; otherwise the places read through it are copied.* The first clause is Rust's "maybe moved", the second keeps `Bump`, and the third keeps a read-only block from turning `*x` into a sealed program. One consequence is worth recording: a block that *assigns* a borrow variable (`match b { Z => r := a | S _ => () }`) must move `r` in and cannot hand it back (that would need `&&Nat`, excluded by D8), so `r` is `⊥` afterwards. The workaround is the functional form `let r = match b { Z => a | S _ => r }`, which is accepted (both borrows are moved into a block returning `&Nat`).

**Overlapping places (N3).**

```
Ov := fix _ (b : Nat, x : &Nat) : Unit := match *x { Z => () | S p => ((match b { Z => *x := Z | S _ => p := Z }); ()) }
  outer [Split] σ := S σ', p = (*x).1; the inner block writes *x (arm Z) and p (arm S)
  literal rule: arguments &*x and &p. Evaluating &*x: *x ↦ loan_a, argument borrow_a (S σ').
    Evaluating &p: [Access] finds loan_a on the path x → *x → (*x).1 and ends borrow_a, the first argument   // the block is broken
```

Each arm is fine alone. The fix is to pass only maximal prefixes (`&*x`) and to rename `p` to `(*x').1` inside the lifted body.

**The block's type (N4).** The [Close] table is indexed by the callee's result type, and P5 by whether it is a proposition. For `let r = match b { Z => x1 | S _ => x2 }` the arms agree (`&Nat`). For proof arms they do not:

```
KeepH(b) : Id Nat (Add(b, 0)) b := let h = match b { Z => refl | S p => cong(S, AddZero(p)) }; h
  arm Z : ⊤, arm S : Eq Nat (S A(σ')) (S σ'): no common type, so the block has none
  with an annotation `let h : Id Nat (Add(b, 0)) b = …`: g := fix _ (b' : Nat) : Id Nat (Add(b', 0)) b' := match b' {…},
    each arm checked against the annotation refined; P5: g(σ_b) not run; h ≡ Eq Nat A(σ_b) σ_b; h ✓
```

v1 has neither the annotation nor the ascription form. Add `let x : T = t; u`: the annotation is the block's motive, which is what a dependent match needs.

**Recursive calls inside a block.** An arm that calls the enclosing `f` puts `f` inside the lifted `g`. Lifting must keep `f` as a direct reference: passing it to `g` as a value argument, as "places it only reads become value arguments" would suggest, makes it escape, which v1.1's head-only clause forbids. The guard applies to the source program. The arms are checked by [Split] before lifting, so [Rec] sees those calls with the right entry value.

### E6.8 A match on a sealed program (N6)

[Split] fires only when the content's head is an abstract `σ`. After an opaque call the content is a sealed program, and the stuck-block rule reads as if it covers that case ("a stuck match that is not the body of a call … a non-tail match in a checked program after its arms have been checked"), but no rule checks those arms.

```
Knot3 := fix f (x : &Nat, h : Π(z : &Nat). Unit) : Eq Nat Z (S Z) :=
  h(&*x); let e = match *x { Z => f(&*x, h) | S p => f(&p, h) }; e
[Def]: { c ↦ loan_1 | x ↦ borrow_1 σ, h ↦ σ_h }, goal Eq Nat Z (S Z)
  h(&*x): σ_h closes off at once (N7); x ↦ borrow_1 N₁, N₁ = ⌈let d = σ; σ_h(&d); d⌉
  match *x: content N₁, not an abstract σ: [Split] does not apply
    reading (ii): it is a stuck non-tail match, so close it off; its arms were never checked
    block type: both arms have type Eq Nat Z (S Z), a proposition → not run (P5); e ↦ ⋆
  e : Eq Nat Z (S Z) ≡ goal ✓. [Rec]: both recursive calls sit in unchecked arms, so they are never examined
let a = Z; Knot3(&a, fix _ (z : &Nat) : Unit := ()) : Eq Nat Z (S Z)                       // closed, not run: PROOF under reading (ii)
```

Under reading (i) ("no [Split], so no rule: reject") `Knot3` is rejected, and so is every ordinary program that matches on a place after an opaque call (E4's `f(&*x); match *x {…}`). The fix that keeps both: *when a checked program matches on a neutral that is not an abstract value, generalise it (replace it by a fresh `σ` in Ω, the goal and the stored types) and [Split] on `σ`*. Then `Knot3`'s arms are checked: with `N₁` generalised to `σ_g`, the recursive calls pass contents `Z` and `σ_g'`, neither of them a subterm of `f`'s entry value `σ`, and [Rec] rejects both. Generalising is sound (the continuation is checked for every `σ_g`); it only forgets how `N₁` was built, which costs completeness.

### E6.9 New piece: P5. Is a writing proof observable? Not through a call. But P5 is keyed on calls (N12), and it removed a safety net (N1)

```
W5 := fix _ (x : &Nat) : ⊤ := *x := S Z; refl
  [Def]: { c ↦ loan_1 | x ↦ borrow_1 σ }; *x := S Z; refl : ⊤ ✓                            // accepted: a proof whose body writes
NoEffect := fix _ (n : Nat) : Id Nat (let a = n; W5(&a); a) n := refl
  goal: W = ∅ (a is local to the term); a ↦ σ_n; W5(&a): ⊤ is a proposition, not run, borrow ends unchanged;
        result σ_n; ⟦n⟧ = σ_n; ≡ Eq Nat σ_n σ_n ≡ ⊤; refl ✓
```

`NoEffect` states that the erased program leaves `a` alone, which is true. The write exists only in `W5`'s own [Def] run, whose final environment nothing reads (the goal was fixed at the generic call). Proof values are irrelevant, a proof cannot return a borrow, and every call of a Prop-valued function is skipped at check time and erased at runtime, so the checker and the runtime agree. Through a *call*, nothing is observable. Two cases are not calls, and in both P5's keying on calls leaks:

- **A Prop-typed block.** A stuck block whose arms are proofs is closed off into a call, and P5 skips it, so its writes vanish. Run concretely, the same match is not a call, and its writes happen. meta-model-v1 R1 (`Q`) turns this into a closed proof of `Eq Nat (S Z) Z`. I re-checked `Q` step by step: it uses only §3's stuck block, [Close], P5 and a concrete [Match]. My N4 (iv) below originally said "P5 applies to the block like any call". That is exactly the rule `Q` breaks, so I withdraw it.
- **The arguments of a Prop-valued call.** They are evaluated, and their effects persist: `Id Nat (let a = Z; AddMZero((a := S Z; &a)); a) (S Z)` computes to `⊤`. That is correct only if the runtime, when it erases the call, still evaluates the arguments. P5 says "the call is erased" without saying which.

The fix covering both (meta-model-v1's): *a term whose type is a proposition runs on a private copy of Ω, arguments included; the runtime erases it whole.* The price is that the checker never runs a proof, so termination of proofs rests on [Rec] alone. Before P5, running a non-terminating proof made the checker loop; now nothing notices:

```
Apply := fix _ (h : Π(n : Nat). Eq Nat Z (S Z), n : Nat) : Eq Nat Z (S Z) := h(n)     -- a genuine function; checks (P5: h(n) not run)
Knot  := fix f (x : Nat) : Eq Nat Z (S Z) := Apply(f, x)
  [Def]: { x ↦ σ }, goal Eq Nat Z (S Z)
  Apply(f, x): arguments f (its own closure, copied) and σ                                 // [Read]
    f : Π(x : Nat). Eq Nat Z (S Z) ✓, σ : Nat ✓; type ≡ Eq Nat Z (S Z) ≡ goal ✓               // [Call-type]
    not run: the result type is a proposition                                                // P5
  [Rec]: "each recursive call": the body has no call with head f ✓ (vacuous)
ε ⊢ Knot(Z) : Eq Nat Z (S Z)                                                                 // not run (P5): CLOSED PROOF, checker terminates
```

`Alias := fix f (x : Nat) : Eq Nat Z (S Z) := let g = f; g(x)` works the same way if "recursive call" means "call whose head is `f`". At runtime (were proofs run) `Knot(Z)` calls `f(Z)` forever; in the model `Knot` has no CIC counterpart. This is breaker-close A4, made worse by P5; v1.1 adopted its fix ("`f` occurs only as the head of a call"), which rejects `Knot` and `Alias`. Fix (CIC's guard): *`f` occurs in its body only as the head of a call; every such call, including one inside a nested function or a block arm, passes the entry-value check.* The nested case needs saying: `Apply(fix _ (y : Nat) : Eq Nat Z (S Z) := f(y), x)` has `f` only in head position, and it is rejected only if [Rec] also applies when the nested function's body is checked (`y`'s content `σ_y` is not a subterm of `σ`).

### E6.10 New piece: [Rec] on entry values

```
Loop := fix f (x : &Nat, y : Nat) : Eq Nat Z (S Z) :=                         -- structural: x (with y instead, arm Z passes σ_x for y and fails too)
  match y { Z => (*x := S *x; match *x { Z => … | S p => let q = p; f(&p, q) }) | S q => (*x := S *x; match *x { Z => … | S p => f(&p, q) }) }
  arm σ_y := Z: *x := S *x gives x ↦ borrow_1 (S σ_x); the inner match takes S, p ↦ σ_x
    f(&p, q): content σ_x, the entry value itself, not a strict subterm                       // [Rec]: REJECT

Grow := fix f (b : Nat, x : &Nat) : Id Unit (*x := Z) () :=
  (match b { Z => () | S _ => () }); match *x { Z => refl | S p => (p := S p; f(b, &p)) }
  block over b (read) → g(σ_b) → (); b ↦ σ_b                                                    // §3
  [Split] σ := S σ': p := S p gives x ↦ borrow_1 (S (S σ')); f(b, &p): content S σ' = the refined entry S σ'
    not strict                                                                                  // [Rec]: REJECT

Spin := fix f (x : Nat) : Eq Nat Z (S Z) := match x { Z => (x := S Z; match x { Z => … | S y => f(y) }) | S y => (x := S x; f(y)) }
  arm S σ': x := S x gives x ↦ S (S σ'); y = x.1 now holds S σ' = entry: REJECT
  arm Z: x := S Z; y = x.1 holds Z, entry refined to Z, not strict: REJECT                        // [Rec]
```

All three rejected, at the recursive call, because the check reads the argument's *current* content against the *entry* value. There is a small completeness cost: `S p => (p := Z; f(&p))` terminates but is rejected (`Z` is not a syntactic subterm of `S σ'`). The guard is exactly CIC's, so this is what Lean would say too.

**Still open (N9, breaker-close A3's cause).** Pattern variables are aliases with no loan, so a write to the parent is not stopped:

```
fix _ (x : Nat, n : Nat) : Nat := match x { Z => Z | S y => (x := n; y) }
  arm S: x := n gives x ↦ σ_n; reading y = x.1 needs content(x.1) through σ_n: no rule (not [Match], not stuck, not an error)
```

Concretely `n = Z` makes this read a field that does not exist. v1 has no clause for "the path runs through a value whose head is not `S`". The simplest fix is Aeneas's: treat the sub-place as borrowed while a pattern variable is live, so the write to `x` ends it (`y` becomes `⊥`). Or state that such a path is an error.

## F. Fixes, collected

- **N1 [Rec]:** done in v1.1 ("`f` occurs only as the head of a call"). Add: "including calls inside nested functions and block arms, checked against `f`'s own entry value". Now that P5 means proofs are never run, [Rec] is the only thing between a proof and non-termination.
- **N2–N4 stuck blocks (§3):** (i) a borrow variable is moved in iff some arm moves or assigns it, reborrowed iff some arm writes or borrows through it, otherwise the places read are copied; (ii) pass maximal prefixes only; (iii) the block's type is the arms' common type, or the `let x : T = …` annotation (add that form), with arms checked against `T` refined; (iv) a Prop-typed block is never closed off for effect: with N12's fix it runs on a private copy like any Prop-typed term.
- **N5:** the lifted function is canonical (parameters in order of first occurrence, arms verbatim), so that equal inline matches give equal neutrals.
- **N6 [Split]:** a match on a neutral that is not an abstract value generalises it to a fresh `σ` first. Never close off unchecked arms.
- **N7:** restore "a call whose head is an abstract function closes off at once".
- **N8:** add `⊥` (or define `⊥ := Π(P : Prop). P`) and `⋆` to the grammar; with D16's rule gone, `noConf` and `inj` are the standard `J` derivations and every negation above uses them.
- **N9:** a live pattern variable borrows its sub-place (Aeneas), or paths through a non-`S` head are errors.
- **N10:** accept the precision loss (Lean-like); optionally a "constant arms" [Seal] rule later.

## What complexity pointed at

- D15 did what round 1 hoped: [Join]'s four ambiguities and its unsound reading are gone, `AddToOne` is accepted with the precise backward function, and continuation errors are reported once. The complexity that came with it is all in one sentence of §3 ("borrow variables it uses and places it writes become borrow arguments"). That sentence is doing lambda lifting, and it needs lambda lifting's usual care: how each captured variable is passed, overlapping places, and the type of the lifted function (N2–N5). This is not evidence against D15; it is the part v1 left implicit.
- P5 (D14) is right: it fixes C1, the lemma-pollution problem, and the modular `TwiceMZero`, and nothing a proof writes is observable. But it moves all of termination onto [Rec], and [Rec] as written checks only calls whose head is literally `f`. N1 was the price of stating [Rec] as a semantic check without the syntactic half of CIC's guard (v1.1 adds it). N12 is the same pattern: a rule keyed on the syntactic form "call", when the stuck-block rule creates calls. The robust statement is meta-model-v1's: what the runtime erases (Prop-typed terms), the machine runs hypothetically.
