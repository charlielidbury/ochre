# deriver-e346: join (E3), opaque functions (E4), must-fail (E6) under RULES.md v0

## Summary

1. **Verdict:** E3 and E4 behave as RULES intends once the gaps are filled: [Join] rejects `AddToOne`, the hand-duplicated version checks, `Twice` and `TwiceM` check, and `TwiceMZero` is provable by the same induction as `AddMZero`. E6 (a), (b), (d), (f) fail where they should. E6 (c) does not hold: the text permits two closed proofs of `⊥` (a Π-typed hypothesis re-read after a mutation, F5; stored types across [Join], F2), and the §6 recursion check accepts a function of type `Π(n : Nat). ⊥` (F6).
2. **Most important finding:** [Join] is a second, weaker copy of [Close]. Move the match into a helper function (`Pick`) and the program [Join] rejects is accepted, with exactly Aeneas's backward function in the loans. Replacing [Join] with "close off a stuck non-tail match like a call" (the clause §4 already has for observations) removes anti-unification and every [Join] problem below (F1–F4). This revisits D7 (and D8's "branch-dependent live borrows are out").
3. **RULES.md must change:** [App] (a Π-type's free variables must be fixed at formation, F5; the argument must be checked, F7). [Join]: replace it (F1), or at least specify the result value, goal and stored types (F2, F3). §6 needs an actual rule: the recursive argument must be a strict subterm of the parameter's *entry* value (F6). Calls at Prop type should run on a private copy (F8, confirms E2-F8/E1-N1). Add `Eq A a a ≡ ⊤` (F12).
4. **Confidence:** high for the derivations, for the two closed proofs of `⊥` and for `Bot'` (each is a few machine steps under a reading the text allows, shown below). Medium for the proposed replacement of [Join]: derived on `AddToOne`, `Pick`, `SelAdd`, `KeepB`, not re-checked against E1/E2 end to end.
5. **Not checked:** E1/E2 beyond the fragments reused here; J/transport typing (I use `trans` as if derived from J); the Canonical-observation conjecture (no counterexample found, not proven); the Lean formalisation.

## Findings (one line each; details in §F)

- **F1** §5 [Join] vs §3 [Close]: `AddToOne` is rejected inline but accepted, precisely, once the match is a call (`Pick`, §E3.4). The D8 exclusion is enforced only by [Join]. Fix: a stuck non-tail match is closed off like a nullary call over its free places; delete anti-unification. Decision: D7.
- **F2** §5 [Join]: silent on the match's result value, on the goal, on stored types, and on whether arms are refined. One permitted reading (stored types taken from an arm) gives a closed proof of `⊥` (`Bad`, §E3.6). Fix: F1, or restore the pre-split goal and stored types after the join.
- **F3** §5 [Join] "positions where the arms' values differ become fresh": this includes the scrutinee, because each arm refined it. A read-only `match b` cuts `b` loose from the goal (`KeepB`, §E3.5). Fix: F1, or un-refine (a position holding the refinement images of its pre-split value keeps that value).
- **F4** §5 [Join] "after ending whatever loans can be ended": every loan can be ended; without a liveness criterion the join may kill the live result. Fix: F1, or end only borrows held by bindings that are `⊥` in another arm.
- **F5** SOUNDNESS, §5 [App] ("B evaluated ... in the caller's environment") + [Lam] ("evaluate the goal"): a Π-typed hypothesis whose codomain mentions an outer variable is re-read at the call site after a mutation. `Oops2 Z (λ_. refl) : ⊥` (§E6.3). Fix: a Π-type, when formed, captures the values of its other free variables, like a λ-closure (and, like one, no borrows); [App] then binds only the parameter.
- **F6** SOUNDNESS (model), §6: write-before-match recursion passes the syntactic check; `Loop` gives `Bot' : Π(n : Nat). ⊥` (§E6.3). Closed instances make the checker diverge, which is the only thing between this and a closed `⊥`. Fix: at every recursive call, the recursive argument's content must be a strict subterm of the parameter's entry value.
- **F7** §5 [App] never says the argument is checked against the domain. Fix: check `u : A`, with `A` evaluated at the call point.
- **F8** §5 [App] runs proof calls for effects (confirms E2-F8, E1-N1, and makes E1-N2 concrete): the natural modular proof of `TwiceMZero` is rejected because `AddMZero &*x` rewrites `*x` to a sealed program (§E4.4); `AddMZero x` consumes `x`. Fix: a call whose result type is a Prop runs on a private copy (P2); proofs are erased.
- **F9** §3 [Seal] loops as written (confirms E1-F1, E2-F1). I use their fix throughout.
- **F10** §5 [Split]/[Join] undefined when the scrutinee is a sealed program; `f &*x; match *x {…}` (§E4.3) is the natural instance (confirms E2-F10).
- **F11** §3 [Close] with two borrow arguments and a borrow result: one `borrow_k`, two `loan_k` holes, two owners. Derived in full for `Pick` (§E3.4); it works if every occurrence is filled and the owner is a set (confirms E2-F4, which sketched it).
- **F12** §4 Eq rules: with no `Eq A a a ≡ ⊤`, every untouched borrow in the footprint must be padded with an explicit `refl`, in an unspecified order (`AddToOneZero`, §E3.3). Fix: add the rule; it subsumes `Eq Nat Z Z ≡ ⊤` (and `Eq Unit a b ≡ ⊤` if every Unit value is `()`), and makes `refl` checkable against any reflexive goal (cf. E1-F3). Decision: D6 is one rule short.
- **F13** §2 lists `n v` (stuck application of an abstract function) as a neutral, but [Close] turns `σ_f v` into `⌈σ_f …⌉`. One of them is redundant.
- **F14** §3 [Match] on a known constructor runs one arm, so dead arms are never checked (`Loop`'s inner `Z =>` arms). Sound on its own; together with runtime erasure of effectful proofs (F8) the runtime can reach code the checker never examined.

## Conventions

- Environments as in deriver-e2: `{ x° ↦ loan_1 | x ↦ borrow_1 σ, y ↦ τ }`, ghosts in their own frame below the function's frame (E2-F7, E1-F5). Loan names are fresh per borrow parameter (RULES writes `loan_0` for every one).
- Calls are saturated and n-ary (E1-F2); multi-parameter definitions `F x y := t` are n-ary `fix`, and I say which parameter is structural.
- Call point = after the arguments are evaluated, before the callee frame is pushed (E1-F6, E2-F6). [App]'s result type is evaluated there on a private copy.
- [Seal] per E2-F1: a sealed program built by [Close] is normal; refinement re-runs those mentioning the refined variable, innermost first, and inside that run [Close] fires for inner calls but not for the sealed call itself.
- "Contains a loan" everywhere, including inside sealed programs (E2-F2). Owner = follow the loan outward to the first owned place or ghost (E2-F5); a set when a hole is duplicated (F11).
- `0 = Z`, `1 = S Z`, `5 = S⁵ Z`. `T_∅ = Unit` (E1-F8). W is ordered by Ω (E1-F8).
- Abbreviations (binders inside `⌈…⌉` compared up to renaming, E1-F7):

```
A(v)   := ⌈let c = v; AddM &c 0; c⌉        final content after AddM _ 0 got stuck on v   (= E2's A(v, 0))
A₁(v)  := ⌈let c = v; AddM &c 1; c⌉        same for AddM _ 1
Q(v)   := ⌈let c = v; AddMZero &c; c⌉      final content after the *proof* AddMZero got stuck on v (F8)
```

- Normal forms used repeatedly (by [Seal] re-runs, as in E1 lemma S2 / E2 §3): `A(Z) ≡ Z`, `A(S v) ≡ S A(v)`, `A₁(Z) ≡ S Z`, `A₁(S v) ≡ S A₁(v)`. `Add v 0` evaluates to `A(v)`: `Add`'s body `AddM &x y; x` closes `AddM` off and reads `x`.

## E3. Join

### E3.0 Bool: not needed

`Nat` with `Z` as false and `S _` as true costs nothing: the match is the existing one, the "true" arm refines `σ_b := S σ_b'` and never uses `σ_b'`. Adding `Bool` would add a type, two constructors, a match form, a refinement and at least two Eq rules, and change nothing below. (Pattern `S _` is `S y` with an unused `y`.)

### E3.1 `AddToOne` is rejected, and exactly why

```
AddToOne : Π(b : Nat) (x1 : &Nat) (x2 : &Nat) (y : Nat). Unit
AddToOne b x1 x2 y := let r = match b { Z => x1 | S _ => x2 }; AddM r y
```

```
ε ⊢ AddToOne : Π(b : Nat) (x1 x2 : &Nat) (y : Nat). Unit                                  // [Lam]
  Ω₀ = { x1° ↦ loan_1, x2° ↦ loan_2 | b ↦ σ_b, x1 ↦ borrow_1 σ1, x2 ↦ borrow_2 σ2, y ↦ τ }, goal Unit
  Ω₀ ⊢ let r = match b { Z => x1 | S _ => x2 }; AddM r y : Unit                           // [Let]
    Ω₀ ⊢ match b { Z => x1 | S _ => x2 }                                                  // [Join]: not in tail position, content σ_b abstract
      arm Z, σ_b := Z:
        Ω₀[σ_b := Z], x1                                                                   // [Read] content borrow_1 σ1 is a borrow: move
        Ω_Z = { x1° ↦ loan_1, x2° ↦ loan_2 | b ↦ Z, x1 ↦ ⊥, x2 ↦ borrow_2 σ2, y ↦ τ }, result borrow_1 σ1
      arm S, σ_b := S σ_b':
        Ω_S = { x1° ↦ loan_1, x2° ↦ loan_2 | b ↦ S σ_b', x1 ↦ borrow_1 σ1, x2 ↦ ⊥, y ↦ τ }, result borrow_2 σ2
      compare loan/borrow structure:
        x1 : ⊥ vs borrow_1;  x2 : borrow_2 vs ⊥;  result : borrow into x1° vs borrow into x2°
      end what can be ended: in Ω_Z the borrow in x2, in Ω_S the borrow in x1              // [Reorg] "at any other time": content returns to the ghost
        Ω_Z' = { x1° ↦ loan_1, x2° ↦ σ2 | …, x1 ↦ ⊥, x2 ↦ ⊥ }, result borrow_1 σ1
        Ω_S' = { x1° ↦ σ1, x2° ↦ loan_2 | …, x1 ↦ ⊥, x2 ↦ ⊥ }, result borrow_2 σ2
      residual difference: which ghost is loaned out, i.e. which place the result borrows
      removing it means ending the result's borrow, but that is `r`, used by `AddM r y`    // REJECT
```

Why: after the match, the live borrow `r` has its loan in `x1°` in one arm and in `x2°` in the other. That is the only irreducible difference. The `⊥`-versus-borrow differences on `x1` and `x2` vanish by ending the unused parameter borrow in each arm, which the rule permits only because "whatever loans can be ended" is unconstrained (F4). D7 says errors land on the arm that caused them; here neither arm is at fault, so the error has to be reported at the join.

### E3.2 The hand-duplicated version is accepted

```
AddToOne' b x1 x2 y := match b { Z => AddM x1 y | S _ => AddM x2 y }
```

```
Ω₀ ⊢ match b { Z => AddM x1 y | S _ => AddM x2 y } : Unit                                  // [Split]: tail position, σ_b abstract
  arm Z (σ_b := Z): Ω₀[Z] ⊢ AddM x1 y : Unit                                               // [App]
    args: borrow_1 σ1 (x1 ↦ ⊥), τ (copy)                                                   // [Read] ×2; call point
    unfold AddM: { … | x₁ ↦ borrow_1 σ1, y₁ ↦ τ }, match *x₁: content σ1                    // [Match] stuck
    C = AddM &c τ, L = let c = σ1: result ⌈L; C⌉ ≡ (), x1° := ⌈let c = σ1; AddM &c τ; c⌉      // [Close] borrow-free result
    result type Unit ≡ goal Unit ✓
    end of body: x2's borrow ends (x2° ↦ σ2), b, y dropped, x1 is ⊥                        // [Pop]
  arm S (σ_b := S σ_b'): the same with x2, and x1's borrow ends at [Pop] ✓
```

### E3.3 A proof about it, and what it says about the Eq rules (F12)

```
AddToOneZero : Π(b : Nat) (x1 x2 : &Nat). Id Unit (AddToOne' b x1 x2 0) ()
AddToOneZero b x1 x2 := match b { Z => ⟨AddMZero x1, refl⟩ | S _ => ⟨refl, AddMZero x2⟩ }
```

```
Ω₀ ⊢ Id Unit (AddToOne' b x1 x2 0) () ≡ G                                                   // [Lam]: goal evaluated once
  W = { x1°, x2° }                                                                           // x1, x2 are borrow-typed and free
  ⟦AddToOne' b x1 x2 0⟧: args σ_b, borrow_1 σ1, borrow_2 σ2, Z; unfold; match b on σ_b        // stuck
    C = AddToOne' σ_b &c1 &c2 Z, L = let c1 = σ1; let c2 = σ2                                // [Close]
    result () ; x1° := P1 = ⌈L; C; c1⌉, x2° := P2 = ⌈L; C; c2⌉ ; observation ((), P1, P2)
  ⟦()⟧: resolve both borrows: ((), σ1, σ2)
  G ≡ Eq Nat P1 σ1 ∧ Eq Nat P2 σ2                                                           // [Eq ×], [Eq Unit], [⊤ ∧]
arm Z (σ_b := Z): P1 ↦ A(σ1) (Z arm, AddM stuck on σ1), P2 ↦ σ2 (x2's borrow ends when the callee returns)   // refinement re-runs P1, P2
  goal_Z ≡ Eq Nat A(σ1) σ1 ∧ Eq Nat σ2 σ2
  AddMZero x1 : [App] at the call point, x̂ := borrow_1 σ1, W = {x1°} ≡ Eq Nat A(σ1) σ1
  refl : Eq Nat σ2 σ2
  ⟨AddMZero x1, refl⟩ : goal_Z ✓
arm S: symmetric ✓
```

The proof one would write, `match b { Z => AddMZero x1 | S _ => AddMZero x2 }`, is rejected: `Eq Nat A(σ1) σ1` is not `Eq Nat A(σ1) σ1 ∧ Eq Nat σ2 σ2`. The untouched borrow `x2` is in the footprint because it is free in the statement, and `Eq Nat σ2 σ2` does not reduce. The programmer has to pad with `refl`, and has to know W's order (unspecified in §4). With `Eq A a a ≡ ⊤` the natural proof checks.

### E3.4 The same program through a helper function is accepted (F1, F11)

```
Pick : Π(b : Nat) (x1 x2 : &Nat). &Nat
Pick b x1 x2 := match b { Z => x1 | S _ => x2 }                 -- [Split]; each arm returns one borrow, [Pop] ends the other
AddToOne'' b x1 x2 y := let r = Pick b x1 x2; AddM r y
```

```
Ω₀ ⊢ let r = Pick b x1 x2; AddM r y : Unit                                                    // [Let]
  Ω₀ ⊢ Pick b x1 x2 ⇓ borrow_k V : &Nat                                                         // [App]
    args σ_b, borrow_1 σ1 (x1 ↦ ⊥), borrow_2 σ2 (x2 ↦ ⊥); unfold Pick; match b on σ_b              // stuck
    result type &Nat, fresh k: C = Pick σ_b &c1 &c2, L = let c1 = σ1; let c2 = σ2                  // [Close] second bullet
      returns borrow_k V, V = ⌈L; let r = C; *r⌉
      x1° := ⌈L; let r = C; *r := loan_k; c1⌉,  x2° := ⌈L; let r = C; *r := loan_k; c2⌉              // one borrow, two holes
  Ω₁ = { x1° ↦ …loan_k…, x2° ↦ …loan_k… | b ↦ σ_b, x1 ↦ ⊥, x2 ↦ ⊥, y ↦ τ, r ↦ borrow_k V }
  Ω₁ ⊢ AddM r y : Unit                                                                          // [App]
    args borrow_k V (r ↦ ⊥), τ; unfold; match *x₁ on V, a neutral                                // stuck
    C' = AddM &c τ, L' = let c = V: returns (), loan_k := ⌈let c = V; AddM &c τ; c⌉ =: W_k          // [Close], fills BOTH holes
  Ω₂ = { x1° ↦ ⌈L; let r = C; *r := W_k; c1⌉, x2° ↦ ⌈L; let r = C; *r := W_k; c2⌉ | … }
  end of body: no loans left in the frame                                                        // [Pop] ✓
```

Accepted. The fills are Aeneas's `pick_back b v1 v2 w = if b then (w, v2) else (v1, w)` written as source: refining `σ_b := Z` re-runs them to `x1° ≡ ⌈let c = σ1; AddM &c τ; c⌉`, `x2° ≡ σ2`, which is what `AddToOne'` produces in its Z arm, and symmetrically for `S`. So [Close] already handles the branch-dependent live borrow that D8 lists as out of scope and that [Join] rejects. It needs E2-F4's two repairs (every occurrence of `loan_k` is filled; `owner(borrow_k) = {x1°, x2°}`), nothing else. `AddToOneZero` goes through for `AddToOne''` with the same proof term as §E3.3, since the refined ghosts coincide.

### E3.5 [Join] succeeds but loses what a later proof needs

**(a) The scrutinee itself (F3).** A match that only *reads* `b`:

```
KeepB : Π(b : Nat). Id Nat (Add b 0) b
KeepB b := (match b { Z => () | S _ => () }); AddZero b
```

```
[Lam]: { b ↦ σ_b }, goal G ≡ Eq Nat A(σ_b) σ_b                                                  // W = ∅
[Join] on `match b`: arm Z leaves b ↦ Z, arm S leaves b ↦ S σ_b'; they differ → b ↦ σ_j fresh
AddZero b : [App], x̂ := σ_j ≡ Eq Nat A(σ_j) σ_j                                                  // ≢ G: REJECT
```

Nothing wrote `b`; the two arms differ only because each refined it. Un-refining (both arm values are the refinement images of the pre-split `σ_b`, so keep `σ_b`) fixes this case.

**(b) Genuinely different values.** Un-refining cannot help when the arms produce different values:

```
SelAdd : Π(b x y : Nat). Id Nat (Add (Sel b x y) 0) (Sel b x y)
SelAdd b x y := let r = match b { Z => x | S _ => y }; AddZero r            -- REJECTED: r ↦ fresh σ_r, since (σ_x, σ_y) is no refinement image
```

The goal is `Eq Nat A(s) s` with `s = ⌈Sel σ_b σ_x σ_y⌉` (`Sel b x y := match b { Z => x | S _ => y }` closes off on `σ_b`). The two workarounds:

```
SelAdd b x y := match b { Z => AddZero x | S _ => AddZero y }   -- duplicate: [Split]; arm Z: s ↦ σ_x, goal ≡ Eq Nat A(σ_x) σ_x = type of AddZero x ✓
SelAdd b x y := let r = Sel b x y; AddZero r                     -- factor: [App] gives r ↦ s by [Close]; AddZero r : Eq Nat A(s) s = G ✓
```

Factoring is better than duplicating: nothing is copied, and a later split on `b` re-runs `s` to the exact arm value, which no anti-unifier can recover. It is also what F1 proposes to do automatically. With F1, the inline `let r = match b {…}` gives `r ↦ ⌈match σ_b { Z => σ_x | S _ => σ_y }⌉`, which is a *different* neutral from `⌈Sel σ_b σ_x σ_y⌉`; so the inline version still fails against a goal stated with `Sel`, and succeeds against a goal stated with the same inline match, provided §4's "close off t as a whole" is also changed to close off at the stuck match. Two textually different matches not converting is the loss 01 §9 already accepts.

### E3.6 [Join], the snapshot goal, and stored types

**The goal.** [Lam] fixes the goal at entry and [Split] refines it per arm. [Join] does not say what the continuation's goal is. The reading that works is "the pre-split goal". If instead the per-arm goals are anti-unified, sealed programs that mention `σ_b` normalise differently per arm (`A(Z) ≡ Z` against `A(S σ') ≡ S A(σ')`), and the anti-unifier invents a variable unrelated to the one it gave `b`: `KeepB` fails even with un-refinement.

**Stored types that mention a value written away** behave correctly: after `let h = AddMZero &*x` and a join where one arm did `*x := Z`, `h` still has type `Eq Nat A(σ) σ` about the entry value `σ`, which is what the entry goal is about. Snapshots are robust here.

**Stored types refined inside the arms** are where the text allows an unsound reading (F2):

```
Bad : Π(b : Nat) (h : Id Nat b Z). ⊥
Bad b h := (match b { Z => () | S _ => () }); h
```

```
[Lam]: { b ↦ σ_b, h ↦ σ_h }, h's stored type Eq Nat σ_b Z, goal ⊥
[Join] on `match b`:
  arm Z (σ_b := Z applied to Ω and stored types): b ↦ Z,    h : Eq Nat Z Z ≡ ⊤
  arm S (σ_b := S σ'):                              b ↦ S σ', h : Eq Nat (S σ') Z ≡ ⊥
  values: b → fresh σ_j; h ↦ σ_h and result () agree
  stored types: RULES is silent. Reading J1: the joined bindings keep one arm's types (here the last) → h : ⊥
h : ⊥ ≡ goal ✓                                                                                  // under J1
ε ⊢ Bad Z refl : ⊥                                                                              // [App]: refl : Eq Nat Z Z ≡ ⊤ ✓; the run is match Z → (); h. Terminates.
```

Under J2 (anti-unify the types: `h : σ_P` for a fresh proposition) or J3 (restore the pre-split type `Eq Nat σ_b Z`) `Bad` is rejected. RULES must pick J3, or adopt F1, where the arms are never merged at all.

## E4. Opaque functions

### E4.1 `Twice`

```
Twice : Π(f : Π(_ : Unit). Unit). Unit
Twice f := f (); f ()
```

```
ε ⊢ Twice : Π(f : Π(_ : Unit). Unit). Unit                                                     // [Lam]
  { f ↦ σ_f }, goal Unit
  ⊢ f () ⇓ () : Unit                                                                             // [App]
    f: σ_f is borrow-free (a function value): copy                                              // [Read]
    σ_f (): abstract function, closes off at once; no borrow arguments, C = σ_f (), L empty        // [Close]
    returns ⌈σ_f ()⌉ ≡ ()                                                                       // [Seal] at Unit
    result type Unit
  ⊢ f () ⇓ () : Unit                                                                             // the same
  Unit ≡ Unit ✓
```

`f` is used twice because function values are data and are copied (D3). Also `Π(f). Id Unit (Twice f) ()` holds by `refl`: `W = ∅`, both observations are `()`. That is P5 at work: an `f` with no borrow argument cannot write anything, so its calls collapse to `()`.

### E4.2 `TwiceM` and the value of `*x` afterwards

```
TwiceM : Π(f : Π(_ : &Nat). Unit) (x : &Nat). Unit
TwiceM f x := f &*x; f &*x
```

```
ε ⊢ TwiceM : …                                                                                  // [Lam]
  Ω₀ = { x° ↦ loan_0 | f ↦ σ_f, x ↦ borrow_0 σ }, goal Unit
  Ω₀ ⊢ f &*x ⇓ () : Unit ⊣ Ω₁                                                                    // [App]
    &*x: *x ↦ loan_1, value borrow_1 σ; x ↦ borrow_0 loan_1                                      // [Borrow]
    σ_f (borrow_1 σ): closes off at once; C = σ_f &c, L = let c = σ                               // [Close]
      returns ⌈let c = σ; σ_f &c⌉ ≡ (), loan_1 := N₁ = ⌈let c = σ; σ_f &c; c⌉
  Ω₁ = { x° ↦ loan_0 | f ↦ σ_f, x ↦ borrow_0 N₁ }
  Ω₁ ⊢ f &*x ⇓ () : Unit ⊣ Ω₂                                                                    // [App]
    &*x: value borrow_2 N₁; x ↦ borrow_0 loan_2                                                  // [Borrow]
    C = σ_f &c, L = let c = N₁: loan_2 := N₂ = ⌈let c = N₁; σ_f &c; c⌉                           // [Close]
  Ω₂ = { x° ↦ loan_0 | f ↦ σ_f, x ↦ borrow_0 N₂ }
  end of body: x's borrow ends, x° ↦ N₂                                                          // [Pop]
```

Afterwards `*x` is `N₂ = ⌈let c = ⌈let c = σ; σ_f &c; c⌉; σ_f &c; c⌉`: two nested sealed programs, as expected. Refining `σ` re-runs them but they stay neutral, since `σ_f` is never refined. A check that reborrowing and moving agree: `Id Unit (TwiceM f x) (f &*x; f x)` holds by `refl` (RHS: the first call leaves `x ↦ borrow_0 N₁`; the second moves `x`, and [Close] with `L = let c = N₁` fills `loan_0` with `N₂`; both observations are `((), N₂)`).

### E4.3 Matching after an opaque call (F10)

`λ(f : Π(_ : &Nat). Unit) (x : &Nat). f &*x; match *x { Z => () | S _ => () }`: after the call `*x` holds `N₁`, which is neither a constructor nor an abstract value. [Match] says "content a neutral → stuck"; [Split] and [Join] are defined only for "an abstract value" with refinements `σ := Z | S σ'`. So the checker has no rule for this ordinary program. Generalising (replace `N₁` by a fresh `σ` everywhere, then split) is the usual answer (E2-F10). Under F1 the match is simply closed off.

### E4.4 A theorem about `TwiceM` for a specific `f`

```
TwiceMZero : Π(x : &Nat). Id Unit (TwiceM (λ(z : &Nat). AddM z 0) x) ()
TwiceMZero x := match *x { Z => refl | S p => TwiceMZero &p }
```

Entry goal (write `g` for the closure `λ(z : &Nat). AddM z 0`):

```
Ω₀ = { x° ↦ loan_0 | x ↦ borrow_0 σ }, W = { x° }
⟦TwiceM g x⟧:
  unfold TwiceM: { … | f₁ ↦ g, x₁ ↦ borrow_0 σ }                                                // [App], x moved
  &*x₁ → borrow_1 σ; g (borrow_1 σ): unfold g; AddM (borrow_1 σ) 0: match on σ                    // stuck
  innermost stuck call is AddM (top-level), not g: C = AddM &c 0, L = let c = σ; loan_1 := A(σ)     // [Close]
  g returns (); x₁ ↦ borrow_0 A(σ)
  &*x₁ → borrow_2 A(σ); AddM stuck on the neutral A(σ); L = let c = A(σ); loan_2 := A(A(σ))         // [Close]
  pop TwiceM: x₁'s borrow ends, x° ↦ A(A(σ)); observation ((), A(A(σ)))                            // [Pop]
⟦()⟧ = ((), σ)
G ≡ Eq Nat A(A(σ)) σ
```

```
arm Z (σ := Z): A(Z) ≡ Z, so A(A(Z)) ≡ Z; G ≡ Eq Nat Z Z ≡ ⊤; refl ✓
arm S (σ := S σ'), x ↦ borrow_0 (S σ'), p = (*x).1:
  A(S σ') ≡ S A(σ'); A(A(S σ')) = A(S A(σ')) ≡ S A(A(σ'))                                        // re-run inner first
  G_S ≡ Eq Nat (S A(A(σ'))) (S σ') ≡ Eq Nat A(A(σ')) σ'
  TwiceMZero &p: &p → x ↦ borrow_0 (S loan_1), argument borrow_1 σ'                               // [Borrow]
    type at the call point, x̂ := borrow_1 σ', owner x° (loan_1 in x, loan_0 in x°)                  // [App]
    ⟦TwiceM g x̂⟧ fills loan_1 with A(A(σ')); resolve: x° ↦ S A(A(σ')). ⟦()⟧: x° ↦ S σ'
    ≡ Eq Nat A(A(σ')) σ' = G_S ✓
  §6: `&p`, p a pattern variable of the match on *x ✓
```

Accepted, by the same induction as `AddMZero`. Because the innermost stuck call is `AddM` itself, the closure `g` never appears in a sealed program, and the neutral `A` is shared with `AddMZero`'s goal.

**The modular proof fails (F8).** The proof one would write from `AddMZero` ("each `g` is the identity"):

```
TwiceMZero' x := let h1 = AddMZero &*x; AddM &*x 0; let h2 = AddMZero &*x; trans h2 h1
  intended: h1 : Eq Nat A(σ) σ, h2 : Eq Nat A(A(σ)) A(σ), trans h2 h1 : Eq Nat A(A(σ)) σ
```

```
let h1 = AddMZero &*x: type ≡ Eq Nat A(σ) σ ✓, but the machine runs the call:                   // [App]
  AddMZero (borrow_1 σ) stuck on σ → [Close]: loan_1 := Q(σ); x ↦ borrow_0 Q(σ)                    // the lemma rewrote *x
AddM &*x 0: x ↦ borrow_0 A(Q(σ))
let h2 = AddMZero &*x: type ≡ Eq Nat A(A(Q(σ))) A(Q(σ))
trans h2 h1: A(Q(σ)) ≢ A(σ)                                                                      // REJECT
```

Workaround that checks: do the work on a copy, so the two lemmas touch different places.

```
TwiceMZero'' x := let a = *x; AddM &a 0; trans (AddMZero &a) (AddMZero &*x)
  a ↦ σ; AddM &a 0 → a ↦ A(σ)
  AddMZero &a : Eq Nat A(A(σ)) A(σ)   (then a ↦ Q(A(σ)), never used again)
  AddMZero &*x : Eq Nat A(σ) σ        (*x untouched so far)
  trans … : Eq Nat A(A(σ)) σ ≡ G ✓
```

So the neutrals compose (`A(A(σ))` is literally `A` applied to `A(σ)`), and modular proofs work, but only if the programmer knows that citing a lemma on a borrow destroys what the checker knows about it. With F8's fix (Prop-typed calls on a private copy) `TwiceMZero'` checks as written.

## E6. Must fail

### E6.1 Use of a moved borrow: rejected

```
λ(x : &Nat). AddM x 0; AddM x 0        against Π(x : &Nat). Unit
  { x° ↦ loan_0 | x ↦ borrow_0 σ }
  AddM x 0: x holds a borrow, moved (x ↦ ⊥); [Close] fills loan_0 with A(σ)                         // [Read], [Close]
  AddM x 0: x holds ⊥                                                                               // [Read]/[Ref]: REJECT
```

The repair `AddM &*x 0; AddM x 0` checks (`x° ↦ A(A(σ))`). Inside a type the same program is ill-formed for the same reason: the private copy still tracks moves. Note that lemma applications move too: `let h = AddMZero x; AddM x 0` is rejected, and the programmer must write `AddMZero &*x` (F8).

### E6.2 Write, then `refl` against the entry goal: rejected

```
λ(x : &Nat). (*x := 5; refl)        against Π(x : &Nat). Id Nat *x 5
  [Lam]: { x° ↦ loan_0 | x ↦ borrow_0 σ }
  goal, once: W = { x° } (x is a borrow-typed free variable)
    ⟦*x⟧ = (σ, σ) (copy, then resolve);  ⟦5⟧ = (5, σ)
    G ≡ Eq Nat σ 5 ∧ Eq Nat σ σ
  *x := 5: x ↦ borrow_0 5                                                                          // [Assign]
  refl against G: needs σ ≡ 5                                                                      // REJECT at [Lam]'s final conversion
```

The variant `(*x := 5; (refl : Id Nat *x 5))` also fails: the ascription is evaluated now (≡ `Eq Nat 5 5 ∧ Eq Nat 5 5 ≡ ⊤`), so `refl` checks against it, but the body's type `⊤` is not `G`. Had the goal been evaluated at exit (D2's rejected option), both would be accepted, and a caller `F &a` would get `Eq Nat σ_a 5` for arbitrary `σ_a`.

### E6.3 A closed proof of `Id Nat Z (S Z)`

`Id Nat Z (S Z)` at `ε` is `Eq Nat Z (S Z) ≡ ⊥`, so this is the same as a closed proof of `⊥`. Attacks, in the order tried:

1. `refl`: needs `Z ≡ S Z`. Fails.
2. D2's snapshot attack (`let h : Id Nat x Z := refl; x := S Z; h`): fails, stored types are values (§E6.5).
3. **A Π-typed hypothesis re-read after a mutation: succeeds under the literal [App] (F5).**
4. **Stored types across [Join]: succeeds under reading J1 (F2, `Bad` in §E3.6).**
5. **Recursion that writes before it matches: gives `Π(n : Nat). ⊥`; closed instances make the checker diverge (F6).**
6. A write outside the footprint: fails. Every write outside `t`'s own `let`s goes through a place rooted in Ω (`p := _`, `&p`) or through a borrow reachable from `t`'s free variables. Data and closures hold no borrows (D8), so the latter are the free borrow-typed variables. Both kinds are in W.
7. Hiding a write behind the Unit collapse of [Seal]: fails. Only the *result* collapses; the writes are in the loan fills, which W observes.
8. Loan-ending order: ending a loan early only turns later accesses into errors and never changes a value, because an ended borrow's content is final when it ends. No counterexample found (this is §7's canonicity conjecture, not a proof).

**Attack 3 in full (F5).**

```
Oops2 : Π(x : Nat) (h : Π(_ : Unit). Id Nat x Z). ⊥
Oops2 x h := x := S x; h ()
```

```
ε ⊢ Oops2 : …                                                                                    // [Lam] x
  { x ↦ σ_x }, goal Π(h : Π(_ : Unit). Id Nat x Z). ⊥
    "evaluate the goal": a Π; RULES never says evaluation goes under the binder, so the body stays as written (reading R1)
  [Lam] h: { x ↦ σ_x, h ↦ σ_h }, h's stored type Π(_ : Unit). Id Nat x Z, goal ⊥
  x := S x: x ↦ S σ_x                                                                            // [Assign]
  h (): f = h : Π(_ : Unit). B with B = Id Nat x Z                                               // [App]
    value: σ_h () closes off at once
    type: "B evaluated at the call site ... in the caller's environment": x ↦ S σ_x, W = ∅
      ≡ Eq Nat (S σ_x) Z ≡ ⊥
  ⊥ ≡ goal ✓
ε ⊢ Oops2 Z (λ(_ : Unit). refl) : ⊥                                                              // [App]
  argument against Π(_ : Unit). Id Nat x Z with x := Z: [Lam], goal Eq Nat Z Z ≡ ⊤, refl ✓       // (if checked at all, F7)
  value: the run is x := S Z; (λ_. refl) () → refl. Terminates.
  type: ⊥                                                                                        // CLOSED PROOF OF ⊥
```

Under reading R2 (normalise under the binder at formation, so `h : Π(_ : Unit). Eq Nat σ_x Z`) `h ()` has type `Eq Nat σ_x Z` and `Oops2` is rejected. R1 is what [App]'s wording says. P2 ("a type that has been formed is a closed statement") intends R2, but the only formed types for which the two readings differ are Π-types, and RULES says nothing about them. The same hole opens through a let-annotated closure: `let x = Z; let g : Π(_ : Unit). Id Nat x Z = λ_. refl; x := S Z; g ()`.

**Attack 5 in full (F6).** §6 checks the recursive call syntactically; the note under it admits that a write before the match breaks the measure and says symbolic execution "is where that gap is closed", but no rule closes it.

```
Loop : Π(x : &Nat) (y : Nat). ⊥                                   -- structural parameter: x
Loop x y := match y {
    Z   => *x := S *x; match *x { Z => () | S p => let q = p; Loop &p q }
  | S q => *x := S *x; match *x { Z => () | S p => Loop &p q } }
```

The first match on `y` exists only to make every recursive unfolding stop at once, so the checker terminates. The inner `Z =>` arms are dead and never examined (F14).

```
[Lam]: { x° ↦ loan_0 | x ↦ borrow_0 σ_x, y ↦ σ_y }, goal ⊥
[Split] on σ_y; arm σ_y := Z:
  *x := S *x: *x read as σ_x (copy); x ↦ borrow_0 (S σ_x)                                          // [Read], [Assign]
  match *x: content S σ_x, S arm, p = (*x).1                                                       // [Match], no split
  let q = p: q ↦ σ_x                                                                               // [Read] copy
  Loop &p q: arguments borrow_1 σ_x (x ↦ borrow_0 (S loan_1)) and σ_x                               // [App]
    value: unfold; `match y` on σ_x is stuck; loan_1 := ⌈let c = σ_x; Loop &c σ_x; c⌉               // [Close]
    type: ⊥
    §6: `&p`, p bound by a match on the content of the parameter x ✓ (but p's content is σ_x, the entry value)
  ⊥ ≡ goal ✓
arm σ_y := S σ_q: the same with q ↦ σ_q ✓

Bot' : Π(n : Nat). ⊥
Bot' n := let a = n; Loop &a n
  { a ↦ σ_n }; Loop (borrow_0 σ_n) σ_n: `match y` on σ_n stuck; [Close]; type ⊥ ✓; a holds a loan-free sealed program at [Pop] ✓
```

At runtime `Loop &a Z` with `a = Z` writes `*x := 1`, recurses on the tail `0` with `y = 0`, and never stops. `Bot'` is a checked proof of a false statement, so §7's model conjecture fails (`Bot'` has no CIC counterpart). A closed `⊥` needs a concrete call such as `Bot' Z`; [App] runs it, and the checker loops. That is the only thing standing between this and a closed `⊥`, and it disappears under F8's fix (proof calls not run). Fix: at every recursive call the content of the recursive argument must be a strict subterm of the parameter's entry value as refined so far. `Loop` fails that (the content is `σ_x` itself); `AddM`, `AddMZero`, `AddZero`, `AddMEq` and `TwiceMZero` pass (content `σ'` with `σ := S σ'`).

### E6.4 `Π(x : Nat). Id Unit (AddM &x 0) (AddM &x 1)`: unprovable; its negation is provable

```
[Lam]: { x ↦ σ }, W = { x } (x appears under &)
  ⟦AddM &x 0⟧: &x → x ↦ loan_0, borrow_0 σ; AddM stuck on σ; [Close]: x := A(σ); observation ((), A(σ))
  ⟦AddM &x 1⟧: likewise, x := A₁(σ); observation ((), A₁(σ))
  G ≡ Eq Nat A(σ) A₁(σ)
```

The obvious proof `match x { Z => refl | S p => IH p }` dies in the Z arm: `A(Z) ≡ Z`, `A₁(Z) ≡ S Z`, so `G_Z ≡ Eq Nat Z (S Z) ≡ ⊥` and `refl` does not check. In general, in the set model `A(σ) = σ` and `A₁(σ) = σ + 1`, so `G` is empty for every `σ` and a proof would break the model (which stands only once F2, F5, F6 are fixed).

The negation, pointwise, by the same induction:

```
NotAddM01 : Π(x : Nat) (h : Id Unit (AddM &x 0) (AddM &x 1)). ⊥
NotAddM01 x h := match x { Z => h | S p => NotAddM01 p h }

[Lam]: { x ↦ σ, h ↦ σ_h }, h's stored type Eq Nat A(σ) A₁(σ) (formed at entry), goal ⊥
[Split] σ := Z: h's type refines to Eq Nat Z (S Z) ≡ ⊥; `h` : ⊥ ✓
[Split] σ := S σ': h's type refines to Eq Nat (S A(σ')) (S A₁(σ')) ≡ Eq Nat A(σ') A₁(σ')
  NotAddM01 p h: [App], x̂ := σ' (copy of p); domain of h at the call point ≡ Eq Nat A(σ') A₁(σ'), h has it ✓ (F7); result ⊥ ✓
```

And the global form: `λ(H : Π(x : Nat). Id Unit (AddM &x 0) (AddM &x 1)). H Z` has type `(Π…) → ⊥`, because [App] evaluates `H`'s codomain at `x̂ := Z`, which runs concretely to `Eq Nat Z (S Z) ≡ ⊥`.

### E6.5 A type formed before a mutation, used after it

```
λ(x : Nat). let h = (refl : Id Nat x x); x := S x; h        against Π(x : Nat). Id Nat x x
  [Lam]: { x ↦ σ }, goal Eq Nat σ σ (W = ∅)
  let h: the ascription is evaluated now, Eq Nat σ σ; refl ✓; h stored with that type
  x := S x: x ↦ S σ                                                                                 // [Assign]
  h : Eq Nat σ σ ≡ goal ✓                                                                           // ACCEPTED, correctly: both are about the entry value
```

Variants:

- D2's example, `match x { Z => let h = (refl : Id Nat x Z); x := S Z; (h : Id Nat x Z) | S _ => … }`: `h` is stored at `Eq Nat Z Z ≡ ⊤`; the second ascription is evaluated now, `Eq Nat (S Z) Z ≡ ⊥`; `⊤ ≢ ⊥`. Rejected.
- Types held in places: `let T = Nat; let n : T = Z; T := Unit; (n : T)`: `n`'s stored type is `Nat` (formed when `T` held `Nat`); `(n : T)` evaluates `T` now to `Unit`. Rejected.
- **The variant that goes wrong is a Π-type** (`Oops2`, §E6.3): its codomain is the one part of a formed type that RULES does not evaluate at formation, and [App] then re-reads it in the current environment.

### E6.6 Returning a borrow of a local: rejected

```
λ(_ : Unit). let z = Z; &z        against Π(_ : Unit). &Nat
  [Lam]: { _ ↦ σ_u }, goal &Nat
  let z = Z: z ↦ Z                                                                                  // [Let]
  &z: z ↦ loan_0, value borrow_0 Z                                                                   // [Borrow]
  end of the let: drop z, an owned binding holding loan_0                                             // [Pop]/[Ref]: REJECT
```

Variants, also rejected: `λ(n : Nat). let z = n; TailM &z` ([Close] returns `borrow_k …` and `z` holds `⌈…; *r := loan_k; c⌉`, so the drop of `z` finds a loan; needs E2-F2's "contains"). `λ(z : Nat). let r = &z; &*r` (dropping `r`, whose content `loan_1` contains a loan, makes the pending `_ ↦ borrow_0 loan_1`; dropping `z` then finds `loan_0`, in either drop order).

## F. Findings in detail (place in RULES.md, what I assumed, simplest fix, which decision)

**F1–F4: [Join] (§5), decision D7 (and D8's scope line).** [Join] needed four clarifications to run `AddToOne`, `KeepB` and `Bad` at all (F2 result/goal/stored types, F3 the scrutinee, F4 which loans to end), one of which is unsound under a permitted reading. Meanwhile [Close] already does everything [Join] was for, more precisely: `Pick` (§E3.4) is `AddToOne`'s match behind a call, and it checks with the exact backward function; a later split re-runs the sealed programs to exact per-arm values, which no anti-unifier can do. Proposed replacement, one rule for three places:

> **[Close-match]** A match whose scrutinee's content is neutral, which is not inside the body of a call being unfolded (those stay with [Close] at the call), and which is either in a checked term but not in tail position, or in a type-level term, is closed off like a stuck call: its free places are the arguments (borrowed places passed as borrows, the rest as values), it is the body of that call, and [Close] applies unchanged. Its result type is the arms' common type; when that depends on the scrutinee, a `let x : T = match …` annotation supplies it and each arm is checked against `T` by [Split].

This deletes anti-unification, the loan-shape comparison, "ending whatever can be ended" and the fresh abstracts. It replaces §4's "close t off as a whole" with closing off at the stuck match, so a checked `let r = match b {…}` and the same match inside a goal produce the same neutral. `AddToOne` becomes accepted. If the user wants D7's rejection kept (to hold D8's scope line), then for consistency [Close] must also refuse borrow-returning calls with two or more borrow arguments, and `Pick` is rejected too. Either way the two rules must agree, and today they do not. Cost of the replacement: the checker's Ω holds sealed programs where it held fresh `σ`s (bigger terms, same information or more).

If [Join] is kept, the minimum is: arms are run under their refinements; afterwards the goal and every stored type are restored to their pre-split forms (J3); a position whose arm contents are the refinement images of its pre-split content keeps that content (un-refinement, F3); the remaining differing positions, including the match's result, become fresh abstracts, the same pair of arm values giving the same abstract; before comparing shapes, end exactly the borrows held by bindings that are `⊥` in some other arm (F4).

**F5: [App] (§5) and "evaluate the goal" in [Lam], decision D2's scope.** Assumed reading R1 (Π bodies are not evaluated at formation and [App] reads their other free variables in the caller's current Ω) for the bad derivation, R2 elsewhere. Simplest fix: a Π-type, when formed, captures the *values* of its free variables other than its binder, as a λ-closure does, and like a closure it may not capture a borrow (D8). Then [App] evaluates `B` at the call point with only the parameter bound, and the caller's Ω matters only through the argument's loans, which is what the IH needs. D2 is right; it just has to say that Π-types are formed types too.

**F6: §6, no decision entry yet.** The note under §6 names the gap; `Loop` shows it is not hypothetical, and that the checker's divergence on concrete calls is the only barrier to a closed `⊥`. Simplest fix, stated in the machine's terms: at each recursive call in the checked body, the content of the argument in the structural position (through the borrow, if it is one) must be a strict subterm of the parameter's entry abstract value as refined by the splits so far. It is decidable, it is local to the symbolic run, and it rejects writes before the match without a separate analysis. It is conservative: a function that overwrites a sub-place with a smaller value before recursing is rejected. Also say which parameter is structural (E1-F2).

**F7: [App] (§5).** The rule gives the result value and type but never checks `u : A`. Assumed it does, at the call point. Fix: one clause.

**F8: [App] (§5), a missing decision on proof erasure.** Assumed: calls run for effects whatever their type (the literal rule). Consequences: citing a lemma on a borrow replaces the borrowed content by `Q(…)` (§E4.4), and citing it on `x` moves `x` (§E6.1). If proofs are erased at runtime, the checker's Ω and the runtime's disagree after every proof call that closes off. Simplest fix: *a call whose result type is a proposition runs on a private copy of Ω, as a type-level term does (P2)*: its result type is computed as now, its value is irrelevant, and its effects, moves included, do not persist. This is not a pure/impure split the programmer sees (end goal 2): the programmer marks nothing, the type decides. Order matters: once proof calls are not run, `Bot' Z : ⊥` checks immediately, so F6 must be fixed first.

**F9, F10, F11:** as E2-F1, E2-F10, E2-F4. New here: F11 is derived in full (§E3.4) and needed by F1, and F10 has a one-line natural instance with an opaque function (§E4.3).

**F12: §4 Eq rules, decision D6.** Assumed W ordered by Ω. `AddToOneZero` (§E3.3) needs `⟨AddMZero x1, refl⟩`, and the programmer has to know the tuple order. Adding `Eq A a a ≡ ⊤` (sides syntactically equal as normal forms) removes the padding, makes `refl` checkable against any goal whose conjuncts are all reflexive (the problem of E1-F3), and subsumes `Eq Nat Z Z ≡ ⊤`, and also `Eq Unit a b ≡ ⊤` if [Seal]'s "at type Unit every value normalises to `()`" is read for all values, abstract ones included. It is stable under refinement (substitution preserves syntactic equality) and holds in the proof-irrelevant set model (both sides are the true proposition). Net rule count goes down by one.

**F13: §2.** `n v` (a stuck application of an abstract function) and `⌈σ_f …⌉` (what [Close] produces for it) are two neutrals for one thing. Fix: drop `n v`; [Close] already covers abstract functions.

**F14: §3 [Match] and §5.** A match whose scrutinee is a known constructor runs one arm, so the other arm is never type-checked (`Loop` uses this; any ill-typed term would do there). Sound, since the arm is dead for every instantiation. Worth stating, because with runtime erasure of proofs (F8 unfixed) the runtime's Ω can differ from the checker's, and then the runtime can take an arm the checker never looked at.

## What complexity pointed at

- [Join] (D7) is where the extra machinery accumulated: four clarifications and an unsound reading, all to do less than [Close] already does. That is the decision I would revisit first.
- The two `⊥` results under literal readings (F2, F5) both come from one principle, "a formed type is a closed statement" (D2/P2), being applied to some formed types and not others: stored types refined per arm, and Π-type codomains. The fix in both cases is to apply P2 uniformly, not to add rules.
- F8 and F14 come from an unstated decision about what proofs are at runtime. Deciding "proofs are erased, and the checker runs them on a private copy" closes both, and removes the E1-N1/E2-F8 usability problem.
