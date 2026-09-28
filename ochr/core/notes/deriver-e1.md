# Deriver report: E1 under RULES v0

**Verdict:** all four E1 definitions (`AddM`, `AddMZero`, `Add`, `AddZero`) derive under RULES v0, but only after two real repairs: [Seal] as written either loops or fails to produce the `S` that the S arms need, and calls must be n-ary (currying over a borrow parameter breaks [Pop] and the closure-capture rule).
**Most important finding:** F1. `nf(⌈t⌉)` re-runs the sealed call; that call gets stuck again and [Close] turns it back into the same `⌈t⌉`, so under one reading [Seal] loops, and under the other (no [Close] inside [Seal]) `σ := S σ'` gives no `S ⌈…⌉` and both S arms fail to convert. One-sentence fix: in [Seal], [Close] fires for calls made inside the sealed call's body but never for the sealed call itself.
**RULES.md must change:** [Seal] stop condition (F1); n-ary calls in syntax/[App]/[Lam]/fix/§6 (F2); a checking rule for `refl` against a goal the Eq rules have already computed (F3); a recursive definition of "owner" (F4). F5–F10 are wording-level gaps (ghost frame, call point, α-equivalence, T_W for empty W, primitive typing, types on sealed programs).
**Confidence:** high on the derivations and on F1–F4 (each is shown step by step below); medium that F3's proposed fix is the simplest one.
**Not checked:** E2–E6, [Join], metatheory, checker termination; whether Prop is erased at runtime (N2: if it is, a Prop-valued function that writes is an adequacy hole; the IH call in AddMZero is exactly such a call, though harmless there).

## Findings (one line each; details in the last section)

- **F1** [Seal] (§3): running `⌈L; C; c⌉` re-closes `C` into itself; literal reading loops (with [Close]) or leaves `N(S σ', Z)` unreduced (without). Fix: never close off `C` itself inside its own [Seal] run.
- **F2** §1/§3 [App]/§5 [Lam]/§6: application and `fix` are unary but [Close] is n-ary; `(AddM x) 0` makes a closure capturing a borrow and then [Pop] ends that borrow under it. Fix: saturated n-ary calls, telescopes, a designated recursive position.
- **F3** §4 `refl : Eq A a a`: `refl` is argument-free so only checkable, but after the Eq rules the Z-arm goal is `⊤` (and ⊤ has no intro form in §1). Fix: `refl` checks against G iff nf(G) is reflexive (⊤, stuck `Eq A a a`, or ∧ of reflexive).
- **F4** §4 Footprint: "owner = the owned place that holds its loan once all borrows in Ω are ended" is vacuous (no loans remain) and "all other borrows" is blocked by [Reorg]. Fix: follow the loan outward through enclosing borrows to the first owned place.
- **F5** §5 [Lam] + [Pop]: if the ghost `x°` is in the frame [Lam] opens and is dropped before `x`, it still holds `loan₀` and [Pop] rejects every borrow-taking function; also [Lam] never says it pops the frame. Fix: ghost goes in the frame below; [Lam] ends with [Pop].
- **F6** §3 [Close] "just before the call" and §5 [App] "at the call site": both must mean "after the arguments are evaluated, before the callee frame is pushed", and [App] must bind the parameter in a fresh frame (the caller has its own `x`). Fix: define the call point once.
- **F7** P1 "same normal form": the goal's and the IH's `N(σ',Z)` bind different place names inside `⌈…⌉`. Fix: compare normal forms up to renaming of names bound inside sealed programs.
- **F8** §4 Observation: W is a set (tuple order unspecified) and `T_W` is undefined for `W = ∅` (Add, AddZero). Fix: Ω order, `T_∅ = Unit`.
- **F9** §5: no typing rules for read/borrow/assign/constructors/`refl`, and no rule for evaluating type formers (what "evaluate the goal B" does). Fix: a short table; `Id` evaluates via §4 at the current Ω, other formers are values.
- **F10** §3 [Seal] "At type Unit every value normalises to ()": sealed programs carry no type. Fix: [Close] annotates `⌈t⌉ : T`. (The clause is not load-bearing anywhere in E1.)
- **N1** (surfaced, not a defect in E1) the IH call `AddMZero &p` fills `loan₁` with `⌈let c = σ'; AddMZero &c; c⌉`: calling a lemma on a borrow forgets the borrowed content. Harmless in tail position.
- **N2** (surfaced) RULES does not say whether Prop is erased; if it is, a Prop-valued function that writes through a borrow makes the checker and the runtime disagree.
- **N3** (data for D6) the four proofs as written need only [Eq ×] and [Eq Nat S S], and only in the direct `AddZero`; `AddMZero` needs no Eq rule at all (IH and goal are syntactically identical). The ⊤/Unit collapse rules become load-bearing only in the cross proofs of N4.
- **N4** (positive) AddMZero's and AddZero's goals both normalise to `Eq Nat N(σ,Z) σ`; `AddZero x := AddMZero &x` and `AddMZero x := AddZero *x` both check (derived in §E1.4).

## The four worries

- **(i) Is the IH's footprint the goal's ghost `x°`?** Yes, under F4's recursive reading: at the IH call point `x̂ ↦ borrow₁ σ'`, `loan₁` sits inside `x`'s content `borrow₀ (S loan₁)`, and `loan₀` sits in `x°`. The literal wording defines nothing (F4). It matters that the owner is `x°` and not the immediate loan-holder `(*x).1`: with `x°`, the head `S` is inside the observed value, so the IH and the refined goal are syntactically identical with no Eq rule; with `(*x).1` (not allowed by the definition, which requires an owned variable) the proof would still go through but only via [Eq Nat S S].
- **(ii) Does [Pop] handle the frames in the S arm?** Yes. The pops that happen: in the [Seal] run of `N(S σ', Z)` (AddM's frame: the borrow's content `S N(σ',Z)` is loan-free, so it ends into `c`; [Let] then drops `c`, owned and loan-free), and at the end of the checked S arm (`x`'s borrow ends into `x°`, subject to F5's ordering). No pop happens in the IH's observation: [Close] discards AddM's frame, and resolving ends `borrow₁` before `borrow₀`, the order [Reorg] forces. The "anonymous pending borrow" clause never fires in E1.
- **(iii) Does `σ := S σ'` renormalise the goal's sealed program to `S ⌈…⌉`?** Yes, `nf(N(S σ', Z)) = S N(σ', Z)` (lemma S2), but only with F1's fix: the inner call must be closed off (else no `S` comes out) while the sealed call itself must not be (else the final `nf(v)` step loops on `N(σ', Z)`). RULES does not distinguish the two.
- **(iv) Is the Unit component dropped?** Yes: `Eq (Unit × Nat) ((), a) ((), b) ≡ Eq Unit () () ∧ Eq Nat a b ≡ ⊤ ∧ Eq Nat a b ≡ Eq Nat a b` by [Eq ×], [Eq Unit], [⊤ ∧]. It need not be for AddMZero (both sides carry the same Unit component); it must be for the cross proofs in N4, where the components come in the other order (`Unit × Nat` vs `Nat × Unit`).

## Conventions and assumptions used in the derivations

- Ω is written oldest frame first, frames separated by `‖`, bindings `x ↦ v` (types omitted when obvious); `ε` is the empty environment. `⟨Ω, t⟩` lines are machine states, one step per line, rule after `//`.
- Calls are saturated and n-ary (F2): `AddM a b` evaluates the head, then `a`, then `b`, and pushes one frame `x₁ ↦ …, y₁ ↦ …`. Callee parameters are subscripted by nesting depth to keep them apart from the caller's names. `0` is `Z`.
- The ghost owner is in its own frame below the one [Lam] opens (F5).
- The **call point** is the state after all arguments are evaluated and before the callee frame is pushed. [Close] restores to it; [App] evaluates the result type at it, binding the parameter as `x̂` in a fresh frame (F6).
- Abbreviations for the sealed programs [Close] makes for `AddM` (the only non-proof ones E1 needs):
  - `R(v, w) := ⌈let c = v; AddM &c w⌉ : Unit`, the call's result; the Unit clause of [Seal] sends it to `()`.
  - `N(v, w) := ⌈let c = v; AddM &c w; c⌉ : Nat`, the final content of the place the call borrowed.
  - Names bound inside `⌈…⌉` are compared up to renaming (F7).

## E1.1 AddM

`AddM := fix AddM (x : &Nat) (y : Nat) : Unit := match *x { Z => *x := y | S p => AddM &p y }`

```
⊢ AddM : Π(x : &Nat) (y : Nat). Unit                                         // [Lam] (n-ary, F2)
  Ω_A := x° ↦ loan₀ ‖ x ↦ borrow₀ σx, y ↦ σy                                 // [Lam] x : &Nat: ghost x° : Nat and a borrow; y : Nat ↦ σy
  goal: Unit                                                                  // [Lam] goal evaluated once at entry
  recursion: the only recursive call passes &p, p bound by the match on *x    // §6 ✓ (recursive position = first parameter, F2)
  Ω_A ⊢ match *x { Z => *x := y | S p => AddM &p y } ⇓ () : Unit             // [Split] below
    content(Ω_A, *x) = σx                                                     // x → borrow₀ σx → σx: abstract, and the match is in the checked term
    arm Z, σx := Z:
      x° ↦ loan₀ ‖ x ↦ borrow₀ Z, y ↦ σy  ⊢  *x := y ⇓ () : Unit              // [Assign]; its typing is invented (F9)
        ⟨x° ↦ loan₀ ‖ x ↦ borrow₀ Z, y ↦ σy, *x := y⟩
        ⟨x° ↦ loan₀ ‖ x ↦ borrow₀ Z, y ↦ σy, *x := σy⟩                        // [Read] y: σy is borrow-free, copy
        ⟨x° ↦ loan₀ ‖ x ↦ borrow₀ σy, y ↦ σy, ()⟩                             // [Assign] write at *x, i.e. inside borrow₀; old Z dropped
      Unit ≡ Unit                                                             // result type vs goal
      ⟨x° ↦ σy⟩                                                               // [Pop] x: borrow, content loan-free, ends into loan₀; y: owned, loan-free
    arm S, σx := S σ':
      Ω_S := x° ↦ loan₀ ‖ x ↦ borrow₀ (S σ'), y ↦ σy;   p := (*x).1          // [Split] refinement; [Match] p is the sub-place (*x).1
      Ω_S ⊢ AddM &(*x).1 y ⇓ () : Unit                                        // [App]
        ⟨Ω_S, AddM &(*x).1 y⟩
        ⟨x° ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁), y ↦ σy, AddM (borrow₁ σ') y⟩    // [Borrow] content((*x).1) = σ', ℓ = 1 fresh
        ⟨x° ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁), y ↦ σy, AddM (borrow₁ σ') σy⟩   // [Read] y copy; call point
        ⟨… ‖ x₁ ↦ borrow₁ σ', y₁ ↦ σy, match *x₁ {…}⟩                         // [App] push AddM's frame
        stuck                                                                 // [Match] content σ' neutral (callee body, so not [Split])
        ⟨x° ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁), y ↦ σy, AddM (borrow₁ σ') σy⟩   // [Close] discard the partial run, back to the call point
                                                                              // [Close] I = {1}, u₁ = σ', C = AddM &c σy, L = let c = σ'
        ⟨x° ↦ loan₀ ‖ x ↦ borrow₀ (S N(σ',σy)), y ↦ σy, R(σ',σy)⟩            // [Close] result type Unit, borrow-free: returns R, loan₁ := N(σ',σy)
        ⟨x° ↦ loan₀ ‖ x ↦ borrow₀ (S N(σ',σy)), y ↦ σy, ()⟩                   // [Seal] Unit clause (F10); N(σ',σy) is normal by S0 (needs F1)
        result type: Unit                                                     // [App] B at the call point with x̂ ↦ borrow₁ σ', ŷ ↦ σy
      Unit ≡ Unit
      ⟨x° ↦ S N(σ',σy)⟩                                                       // [Pop] x: content S N(σ',σy) loan-free, ends into loan₀; y dropped
```

AddM checks. Nothing about it is surprising once F2 is granted.

## Sealed-program lemmas (used by E1.2 and E1.3)

### S0. `nf(N(σ, w))` for abstract `σ`: loops as written (F1)

```
nf(N(σ, w)) = ?                                                // [Seal] run `let c = σ; AddM &c w; c` from ε
  ⟨ε, let c = σ; AddM &c w; c⟩
  ⟨c ↦ σ, AddM &c w; c⟩                                        // [Let]
  ⟨c ↦ loan₁, AddM (borrow₁ σ) w; c⟩                           // [Borrow]; call point
  ⟨c ↦ loan₁ ‖ x₁ ↦ borrow₁ σ, y₁ ↦ w, match *x₁ {…}⟩          // [App] push frame
  stuck                                                         // [Match] σ neutral, in the body of C itself
  reading A: the run of [Seal] is the machine, which includes [App]'s use of [Close]
    ⟨c ↦ loan₁, AddM (borrow₁ σ) w; c⟩                         // [Close] restore to the call point
    ⟨c ↦ N(σ,w), R(σ,w); c⟩                                    // [Close] loan₁ := ⌈let c' = σ; AddM &c' w; c'⌉, which is N(σ,w) up to renaming
    ⟨c ↦ N(σ,w), N(σ,w)⟩                                       // [Let] drop _; [Read] c copy
    ⟨ε, N(σ,w)⟩                                                // [Let] drop c
    completes with v = N(σ,w); "the result is nf(v)" = nf(N(σ,w))   // [Seal]: the same question again, loops
  reading B: the run of [Seal] has no [Close]
    the run is stuck, so the result is ⌈t'⌉ = N(σ,w)           // correct here, but breaks S2
  with F1 (the sealed call C is never closed off in its own run):
    stuck in C's own body, so nf(N(σ,w)) = N(σ,w)               // normal
```

### S1. `nf(N(Z, Z)) = Z`

```
nf(N(Z, Z)) = Z                                                 // [Seal]
  ⟨ε, let c = Z; AddM &c Z; c⟩
  ⟨c ↦ Z, AddM &c Z; c⟩                                        // [Let]
  ⟨c ↦ loan₁, AddM (borrow₁ Z) Z; c⟩                           // [Borrow]; call point
  ⟨c ↦ loan₁ ‖ x₁ ↦ borrow₁ Z, y₁ ↦ Z, match *x₁ {…}⟩          // [App] push frame
  ⟨c ↦ loan₁ ‖ x₁ ↦ borrow₁ Z, y₁ ↦ Z, *x₁ := y₁⟩              // [Match] content Z: Z arm
  ⟨c ↦ loan₁ ‖ x₁ ↦ borrow₁ Z, y₁ ↦ Z, *x₁ := Z⟩               // [Read] y₁ copy
  ⟨c ↦ loan₁ ‖ x₁ ↦ borrow₁ Z, y₁ ↦ Z, ()⟩                     // [Assign]
  ⟨c ↦ Z, (); c⟩                                               // [Pop] x₁: content loan-free, ends, Z into loan₁; y₁ dropped
  ⟨c ↦ Z, Z⟩                                                   // [Let] drop _; [Read] c copy
  ⟨ε, Z⟩                                                       // [Let] drop c: owned, loan-free
  nf(Z) = Z                                                     // completed, both readings agree
```

### S2. `nf(N(S σ', Z)) = S N(σ', Z)` (worry iii)

```
nf(N(S σ', Z)) = S N(σ', Z)                                              // [Seal]
  ⟨ε, let c = S σ'; AddM &c Z; c⟩
  ⟨c ↦ S σ', AddM &c Z; c⟩                                              // [Let]
  ⟨c ↦ loan₁, AddM (borrow₁ (S σ')) Z; c⟩                               // [Borrow]; call point of C
  ⟨c ↦ loan₁ ‖ x₁ ↦ borrow₁ (S σ'), y₁ ↦ Z, match *x₁ {…}⟩              // [App] push C's frame
  ⟨c ↦ loan₁ ‖ x₁ ↦ borrow₁ (S σ'), y₁ ↦ Z, AddM &(*x₁).1 y₁⟩           // [Match] content S σ': S arm, p := (*x₁).1
  ⟨c ↦ loan₁ ‖ x₁ ↦ borrow₁ (S loan₂), y₁ ↦ Z, AddM (borrow₂ σ') y₁⟩    // [Borrow] ℓ = 2
  ⟨c ↦ loan₁ ‖ x₁ ↦ borrow₁ (S loan₂), y₁ ↦ Z, AddM (borrow₂ σ') Z⟩     // [Read] y₁ copy; call point of the inner call
  ⟨… ‖ x₂ ↦ borrow₂ σ', y₂ ↦ Z, match *x₂ {…}⟩                           // [App] push inner frame
  stuck                                                                  // [Match] σ' neutral, in the INNER call's body
  ⟨c ↦ loan₁ ‖ x₁ ↦ borrow₁ (S loan₂), y₁ ↦ Z, AddM (borrow₂ σ') Z⟩     // [Close] restore to the inner call point
  ⟨c ↦ loan₁ ‖ x₁ ↦ borrow₁ (S N(σ',Z)), y₁ ↦ Z, R(σ',Z)⟩               // [Close] C' = AddM &c' Z, L' = let c' = σ'; loan₂ := N(σ',Z)
  ⟨c ↦ loan₁ ‖ x₁ ↦ borrow₁ (S N(σ',Z)), y₁ ↦ Z, ()⟩                     // [Seal] Unit clause; C's body completes
  ⟨c ↦ S N(σ',Z), (); c⟩                                                 // [Pop] x₁: content S N(σ',Z) loan-free, ends into loan₁; y₁ dropped
  ⟨c ↦ S N(σ',Z), S N(σ',Z)⟩                                             // [Let] drop _; [Read] c: borrow-free (no holes), copy
  ⟨ε, S N(σ',Z)⟩                                                         // [Let] drop c: owned, loan-free
  nf(S N(σ',Z)) = S nf(N(σ',Z)) = S N(σ',Z)                              // [Seal] "result is nf(v)"; the inner nf is S0
```

Under reading B (no [Close] inside [Seal]) the run is stuck at the inner call and the result is `N(S σ', Z)` unchanged, so the S arms below fail: the goal would be `Eq Nat N(S σ',Z) (S σ')` while the IH, computed by the checker's machine (which does close off), is `Eq Nat (S N(σ',Z)) (S σ')`. Under reading A the last line calls S0, which loops. Only F1's hybrid (close inner calls, never C itself) gives the stated result.

## E1.2 AddMZero

`AddMZero := fix AddMZero (x : &Nat) : Id Unit (AddM x 0) () := match *x { Z => refl | S p => AddMZero &p }`

```
⊢ AddMZero : Π(x : &Nat). Id Unit (AddM x 0) ()                          // [Lam]
  Ω₀ := x° ↦ loan₀ ‖ x ↦ borrow₀ σ                                       // [Lam] ghost x° : Nat in its own frame (F5); x : &Nat
  recursion: AddMZero &p, p bound by the match on *x                     // §6 ✓
  G₀ := Eq Nat N(σ,Z) σ                                                  // [Lam] goal evaluated once at entry: §E1.2a
  Ω₀ ⊢ match *x { Z => refl | S p => AddMZero &p } : G₀                  // [Split]: §E1.2b
```

### E1.2a Entry goal

```
Ω₀ ⊢ Id Unit (AddM x 0) () ≡ Eq Nat N(σ,Z) σ                            // [Id computes], then [Eq computes]
  W(AddM x 0, ()) = {x°}                                                 // Footprint: no &_ and no := in either term; x : &Nat is free on the left
    owner(x) = x°                                                        // x ↦ borrow₀ σ, and loan₀ sits directly in x° (a ghost, so owned)
    T_W = Nat                                                            // x° : Nat
  ⟦AddM x 0⟧_Ω₀^{x°} = ((), N(σ,Z))                                      // run (a)
  ⟦()⟧_Ω₀^{x°} = ((), σ)                                                  // run (b)
  Eq (Unit × Nat) ((), N(σ,Z)) ((), σ)                                   // [Id computes]
    ≡ Eq Unit () () ∧ Eq Nat N(σ,Z) σ                                    // [Eq ×]
    ≡ ⊤ ∧ Eq Nat N(σ,Z) σ                                                // [Eq Unit]
    ≡ Eq Nat N(σ,Z) σ                                                    // [⊤ ∧]
```

Run (a), the left side, on a private copy of Ω₀ (P2):

```
⟨x° ↦ loan₀ ‖ x ↦ borrow₀ σ, AddM x Z⟩
⟨x° ↦ loan₀ ‖ x ↦ ⊥, AddM (borrow₀ σ) Z⟩                               // [Read] x holds a borrow: move; call point
⟨x° ↦ loan₀ ‖ x ↦ ⊥ ‖ x₁ ↦ borrow₀ σ, y₁ ↦ Z, match *x₁ {…}⟩          // [App] push AddM's frame
stuck                                                                   // [Match] σ neutral
⟨x° ↦ loan₀ ‖ x ↦ ⊥, AddM (borrow₀ σ) Z⟩                               // [Close] restore to the call point
⟨x° ↦ N(σ,Z) ‖ x ↦ ⊥, R(σ,Z)⟩                                          // [Close] I = {1}, u₁ = σ, C = AddM &c Z, L = let c = σ; loan₀ := N(σ,Z)
⟨x° ↦ N(σ,Z) ‖ x ↦ ⊥, ()⟩                                              // [Seal] Unit clause; N(σ,Z) normal by S0 (F1)
resolve: no borrows remain                                              // §4 Observation
observe (v, x°) = ((), N(σ,Z))
```

Run (b), the right side:

```
⟨x° ↦ loan₀ ‖ x ↦ borrow₀ σ, ()⟩                                       // a value already
⟨x° ↦ σ ‖ x ↦ ⊥, ()⟩                                                   // resolve: end borrow₀ ([Reorg] End-Mut), σ into loan₀
observe (v, x°) = ((), σ)
```

### E1.2b The split

```
Ω₀ ⊢ match *x { Z => refl | S p => AddMZero &p } : G₀                   // [Split]
  content(Ω₀, *x) = σ                                                   // abstract, and the match is in the checked term
  arm Z, σ := Z:     Ω_Z ⊢ refl : G_Z                                   // §E1.2c
  arm S, σ := S σ':  Ω_S ⊢ AddMZero &(*x).1 : G_S                       // §E1.2d
```

### E1.2c Z arm

```
Ω_Z ⊢ refl ⇓ refl : G_Z                                                  // refl-check (F3)
  Ω_Z = x° ↦ loan₀ ‖ x ↦ borrow₀ Z                                      // [Split] refinement of Ω
  G_Z = G₀[σ := Z] = Eq Nat N(Z,Z) Z                                    // [Split] refinement of the goal
      = Eq Nat Z Z                                                      // Refinement: re-normalise N(Z,Z) = Z (S1)
      ≡ ⊤                                                               // [Eq Nat Z Z]
  refl : Eq Nat Z Z                                                     // A = Nat, a = Z: taken from G_Z BEFORE [Eq Nat Z Z]; on ⊤ no rule applies (F3)
  ⟨x° ↦ Z⟩                                                              // [Pop] x: content Z loan-free, ends into loan₀
```

### E1.2d S arm

Write `P(v) := ⌈let c = v; AddMZero &c⌉` (a proof) and `M(v) := ⌈let c = v; AddMZero &c; c⌉ : Nat` (what the proof call leaves in the place it borrowed).

```
Ω_S ⊢ AddMZero &(*x).1 ⇓ P(σ') : IH ⊣ Ω_S'        and   IH ≡ G_S        // [App], then conversion
  Ω_S = x° ↦ loan₀ ‖ x ↦ borrow₀ (S σ');   p := (*x).1                  // [Split] refinement; [Match] sub-place
  G_S = G₀[σ := S σ'] = Eq Nat N(S σ',Z) (S σ')                         // [Split] refinement of the goal
      = Eq Nat (S N(σ',Z)) (S σ')                                       // Refinement: re-normalise, S2 (needs F1)
  recursion: &p with p := (*x).1 from the match on *x                   // §6 ✓
  -- the value (machine)
  ⟨Ω_S, AddMZero &(*x).1⟩
  ⟨x° ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁), AddMZero (borrow₁ σ')⟩          // [Borrow] content((*x).1) = σ', ℓ = 1; call point, call it Ω_c
  ⟨… ‖ x₁ ↦ borrow₁ σ', match *x₁ {…}⟩                                   // [App] push AddMZero's frame (the definition being checked)
  stuck                                                                  // [Match] σ' neutral, callee body
  ⟨x° ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁), AddMZero (borrow₁ σ')⟩          // [Close] restore to Ω_c
  ⟨x° ↦ loan₀ ‖ x ↦ borrow₀ (S M(σ')), P(σ')⟩                           // [Close] result type is a Prop (not &T): returns P(σ'); loan₁ := M(σ')  (N1)
  -- the type
  IH := Ω_T ⊢ Id Unit (AddM x̂ 0) ()                                       // [App] B at the call point, parameter bound to the argument
    Ω_T = x° ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁) ‖ x̂ ↦ borrow₁ σ'            // Ω_c plus a fresh frame for the parameter, renamed x̂ (F6)
    W(AddM x̂ 0, ()) = {x°}                                               // x̂ : &Nat free on the left
      owner(x̂) = x°                                                      // loan₁ is inside x's borrow₀ content; loan₀ is in x° (F4, worry i)
      T_W = Nat
    ⟦AddM x̂ 0⟧_Ω_T^{x°} = ((), S N(σ',Z))                                 // run (c)
    ⟦()⟧_Ω_T^{x°} = ((), S σ')                                            // run (d)
    IH ≡ Eq (Unit × Nat) ((), S N(σ',Z)) ((), S σ')                      // [Id computes]
       ≡ Eq Unit () () ∧ Eq Nat (S N(σ',Z)) (S σ')                       // [Eq ×]
       ≡ ⊤ ∧ Eq Nat (S N(σ',Z)) (S σ')                                   // [Eq Unit]
       ≡ Eq Nat (S N(σ',Z)) (S σ')                                       // [⊤ ∧]
  -- conversion
  IH ≡ G_S                                                               // identical up to the name bound in N (F7); both further ≡ Eq Nat N(σ',Z) σ' by [Eq Nat S S], not needed
  -- end of the arm
  ⟨x° ↦ S M(σ')⟩                                                         // [Pop] x: content S M(σ') loan-free, ends into loan₀
```

Run (c), the left side of the IH, on a private copy of Ω_T:

```
⟨x° ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁) ‖ x̂ ↦ borrow₁ σ', AddM x̂ Z⟩
⟨x° ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁) ‖ x̂ ↦ ⊥, AddM (borrow₁ σ') Z⟩      // [Read] x̂ holds a borrow: move; call point
⟨… ‖ x̂ ↦ ⊥ ‖ x₁ ↦ borrow₁ σ', y₁ ↦ Z, match *x₁ {…}⟩                    // [App] push AddM's frame
stuck                                                                     // [Match] σ' neutral
⟨x° ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁) ‖ x̂ ↦ ⊥, AddM (borrow₁ σ') Z⟩      // [Close] restore to the call point
⟨x° ↦ loan₀ ‖ x ↦ borrow₀ (S N(σ',Z)) ‖ x̂ ↦ ⊥, R(σ',Z)⟩                // [Close] I = {1}, u₁ = σ', C = AddM &c Z; loan₁ := N(σ',Z)
⟨x° ↦ loan₀ ‖ x ↦ borrow₀ (S N(σ',Z)) ‖ x̂ ↦ ⊥, ()⟩                      // [Seal] Unit clause
⟨x° ↦ S N(σ',Z) ‖ x ↦ ⊥ ‖ x̂ ↦ ⊥, ()⟩                                     // resolve: end borrow₀, content S N(σ',Z) loan-free
observe ((), S N(σ',Z))                                                   // the S came from x's borrow content, not from any rule: the environment did the congruence
```

Run (d), the right side of the IH:

```
⟨x° ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁) ‖ x̂ ↦ borrow₁ σ', ()⟩               // a value already
⟨x° ↦ loan₀ ‖ x ↦ borrow₀ (S σ') ‖ x̂ ↦ ⊥, ()⟩                           // resolve: end borrow₁ first (borrow₀'s content holds loan₁, [Reorg])
⟨x° ↦ S σ' ‖ x ↦ ⊥ ‖ x̂ ↦ ⊥, ()⟩                                          // resolve: end borrow₀
observe ((), S σ')
```

Sanity check (not required by the rules, but it is the Adequacy conjecture of §7 on this instance): re-running the goal `Id Unit (AddM x 0) ()` from scratch in Ω_S instead of refining G₀ gives the same `Eq Nat (S N(σ',Z)) (S σ')`: `AddM x 0` moves `x`, unfolds, matches `S σ'`, borrows the tail, closes off the inner call into `N(σ',Z)`, and the pop carries `S N(σ',Z)` into `x°`. So refinement and re-evaluation agree here.

AddMZero checks, given F1, F3, F4 (and the wording-level assumptions). No Eq rule is load-bearing in it: the refined goal and the IH are the same expression `Eq (Unit × Nat) ((), S N(σ',Z)) ((), S σ')` before any Eq rule fires, and the Z arm is `refl` at `Eq (Unit × Nat) ((), Z) ((), Z)` if the goal is not normalised first.

## E1.3 Add and AddZero

`Add := λ(x : Nat) (y : Nat). AddM &x y; x`

```
⊢ Add : Π(x : Nat) (y : Nat). Nat                                        // [Lam] (n-ary)
  Ω₊ := x ↦ σx, y ↦ σy                                                   // [Lam] neither parameter is a borrow: no ghost
  goal: Nat
  Ω₊ ⊢ AddM &x y; x ⇓ N(σx,σy) : Nat                                      // t; u = let _ = t; u
    ⟨Ω₊, AddM &x y; x⟩
    ⟨x ↦ loan₀, y ↦ σy, AddM (borrow₀ σx) y; x⟩                          // [Borrow] ℓ = 0
    ⟨x ↦ loan₀, y ↦ σy, AddM (borrow₀ σx) σy; x⟩                         // [Read] y copy; call point
    ⟨… ‖ x₁ ↦ borrow₀ σx, y₁ ↦ σy, match *x₁ {…}⟩                         // [App] push AddM's frame
    stuck                                                                 // [Match] σx neutral; AddM's body, so [Close], not [Split]
    ⟨x ↦ loan₀, y ↦ σy, AddM (borrow₀ σx) σy; x⟩                         // [Close] restore to the call point
    ⟨x ↦ N(σx,σy), y ↦ σy, R(σx,σy); x⟩                                   // [Close] I = {1}, u₁ = σx, C = AddM &c σy; loan₀ := N(σx,σy)
    ⟨x ↦ N(σx,σy), y ↦ σy, (); x⟩                                         // [Seal] Unit clause; the call's type is Unit ([App])
    ⟨x ↦ N(σx,σy), y ↦ σy, x⟩                                             // [Let] drop _
    ⟨x ↦ N(σx,σy), y ↦ σy, N(σx,σy)⟩                                      // [Read] x: borrow-free, copy; type Nat (x's annotation)
  Nat ≡ Nat
  ⟨ε⟩                                                                     // [Pop] x, y owned and loan-free
```

`AddZero := fix AddZero (x : Nat) : Id Nat (Add x 0) x := match x { Z => refl | S p => AddZero p }`

```
⊢ AddZero : Π(x : Nat). Id Nat (Add x 0) x                               // [Lam]
  Ω₀ := x ↦ σ                                                            // [Lam]
  recursion: AddZero p, p bound by the match on x                        // §6 ✓
  G₀ := Eq Nat N(σ,Z) σ                                                  // [Lam] entry goal, below
    W(Add x 0, x) = ∅                                                     // no &_, no :=, no borrow-typed free variable (the & inside Add's body is not in the term)
    T_W = Unit                                                            // assumed (F8)
    ⟦Add x 0⟧_Ω₀^∅ = (N(σ,Z), ())                                         // run (e)
    ⟦x⟧_Ω₀^∅ = (σ, ())                                                    // [Read] x copy; nothing to resolve
    Eq (Nat × Unit) (N(σ,Z), ()) (σ, ())                                  // [Id computes]
      ≡ Eq Nat N(σ,Z) σ ∧ Eq Unit () ()                                   // [Eq ×]
      ≡ Eq Nat N(σ,Z) σ ∧ ⊤ ≡ Eq Nat N(σ,Z) σ                             // [Eq Unit], [∧ ⊤]
  Ω₀ ⊢ match x { Z => refl | S p => AddZero p } : G₀                      // [Split]
    content(Ω₀, x) = σ                                                    // abstract, in the checked term
    arm Z, σ := Z:
      x ↦ Z ⊢ refl : Eq Nat N(Z,Z) Z = Eq Nat Z Z                         // refinement, S1; refl with A = Nat, a = Z (F3)
    arm S, σ := S σ':
      Ω_S = x ↦ S σ';  p := x.1                                           // [Split]; [Match] sub-place
      G_S = Eq Nat N(S σ',Z) (S σ') = Eq Nat (S N(σ',Z)) (S σ')            // refinement, S2 (needs F1)
          ≡ Eq Nat N(σ',Z) σ'                                             // [Eq Nat S S]  (load-bearing here)
      Ω_S ⊢ AddZero x.1 ⇓ ⌈AddZero σ'⌉ : IH                                // [App]
        ⟨x ↦ S σ', AddZero x.1⟩
        ⟨x ↦ S σ', AddZero σ'⟩                                            // [Read] content(x.1) = σ' borrow-free: copy; call point
        ⟨x ↦ S σ' ‖ x₁ ↦ σ', match x₁ {…}⟩                                // [App] push frame
        stuck                                                             // [Match] σ' neutral
        ⟨x ↦ S σ', AddZero σ'⟩                                            // [Close] restore
        ⟨x ↦ S σ', ⌈AddZero σ'⌉⟩                                          // [Close] I = ∅, L empty, C = AddZero σ'; no loans to fill
        IH := Ω_T ⊢ Id Nat (Add x̂ 0) x̂                                    // [App] B at the call point
          Ω_T = x ↦ S σ' ‖ x̂ ↦ σ'                                         // F6
          W = ∅, T_W = Unit
          ⟦Add x̂ 0⟧ = (N(σ',Z), ())                                       // run (e) with σ' for σ, one frame deeper
          ⟦x̂⟧ = (σ', ())                                                  // [Read] copy
          IH ≡ Eq (Nat × Unit) (N(σ',Z), ()) (σ', ()) ≡ Eq Nat N(σ',Z) σ'  // [Eq ×], [Eq Unit], [∧ ⊤]
      IH ≡ G_S                                                            // up to the name bound in N (F7)
      ⟨ε⟩                                                                 // [Pop] x owned, loan-free
```

Run (e), `⟦Add x 0⟧` at Ω₀:

```
⟨x ↦ σ, Add x Z⟩
⟨x ↦ σ, Add σ Z⟩                                                          // [Read] x copy; call point
⟨x ↦ σ ‖ x₁ ↦ σ, y₁ ↦ Z, AddM &x₁ y₁; x₁⟩                                 // [App] push Add's frame
⟨x ↦ σ ‖ x₁ ↦ loan₀, y₁ ↦ Z, AddM (borrow₀ σ) y₁; x₁⟩                    // [Borrow]
⟨x ↦ σ ‖ x₁ ↦ loan₀, y₁ ↦ Z, AddM (borrow₀ σ) Z; x₁⟩                     // [Read] y₁ copy; call point of AddM
⟨… ‖ x₂ ↦ borrow₀ σ, y₂ ↦ Z, match *x₂ {…}⟩                               // [App] push AddM's frame
stuck                                                                     // [Match] σ neutral: the innermost call is AddM, so AddM closes, not Add
⟨x ↦ σ ‖ x₁ ↦ loan₀, y₁ ↦ Z, AddM (borrow₀ σ) Z; x₁⟩                     // [Close] restore
⟨x ↦ σ ‖ x₁ ↦ N(σ,Z), y₁ ↦ Z, R(σ,Z); x₁⟩                                 // [Close] loan₀ := N(σ,Z)
⟨x ↦ σ ‖ x₁ ↦ N(σ,Z), y₁ ↦ Z, N(σ,Z)⟩                                     // [Seal] Unit clause; [Let] drop _; [Read] x₁ copy
⟨x ↦ σ, N(σ,Z)⟩                                                           // [Pop] Add's frame: owned, loan-free; Add's body completed
resolve: nothing; observe (N(σ,Z), ())
```

Add and AddZero check, given F1, F2, F3 (and the wording-level assumptions). Unlike AddMZero, AddZero needs [Eq Nat S S]: `p := x.1` is read by copy, so the IH is about `σ'` alone and the `S` has to be stripped by a rule rather than carried by a borrow.

## E1.4 Cross proofs (N4): the in-place and the pure statement coincide

Both goals normalise to `Eq Nat N(σ,Z) σ`, so each lemma proves the other with one call and no recursion.

`AddZero x := AddMZero &x`, checked at `Ω₀ = x ↦ σ` against `G₀ = Eq (Nat × Unit) (N(σ,Z), ()) (σ, ()) ≡ Eq Nat N(σ,Z) σ`:

```
x ↦ σ ⊢ AddMZero &x ⇓ P(σ) : IH                                           // [App]
  ⟨x ↦ σ, AddMZero &x⟩
  ⟨x ↦ loan₀, AddMZero (borrow₀ σ)⟩                                       // [Borrow]; call point
  ⟨x ↦ loan₀ ‖ x₁ ↦ borrow₀ σ, match *x₁ {…}⟩                              // [App] push frame
  stuck                                                                    // [Match]
  ⟨x ↦ M(σ), P(σ)⟩                                                         // [Close] restore; loan₀ := M(σ)
  IH := Ω_T ⊢ Id Unit (AddM x̂ 0) ()                                         // [App] B at the call point
    Ω_T = x ↦ loan₀ ‖ x̂ ↦ borrow₀ σ
    W = {x}                                                                // owner(x̂) = x: loan₀ is directly in x, an owned Nat
    ⟦AddM x̂ 0⟧ = ((), N(σ,Z))                                              // [Read] move x̂; [App]; [Match] stuck; [Close] loan₀ := N(σ,Z); [Seal]
    ⟦()⟧ = ((), σ)                                                         // resolve: end borrow₀
    IH ≡ Eq (Unit × Nat) ((), N(σ,Z)) ((), σ) ≡ Eq Nat N(σ,Z) σ            // [Eq ×], [Eq Unit], [⊤ ∧]
IH ≡ G₀                                                                    // needs the Unit/⊤ collapse: the components are in opposite order
⟨ε⟩                                                                        // [Pop] x ↦ M(σ): owned, loan-free
```

`AddMZero x := AddZero *x`, checked at `Ω₀ = x° ↦ loan₀ ‖ x ↦ borrow₀ σ` against `G₀ = Eq Nat N(σ,Z) σ` (§E1.2a):

```
Ω₀ ⊢ AddZero *x ⇓ ⌈AddZero σ⌉ : IH                                        // [App]
  ⟨Ω₀, AddZero *x⟩
  ⟨Ω₀, AddZero σ⟩                                                          // [Read] content(*x) = σ borrow-free: copy (P3); call point
  ⟨Ω₀ ‖ x₁ ↦ σ, match x₁ {…}⟩                                              // [App] push frame
  stuck                                                                    // [Match]
  ⟨Ω₀, ⌈AddZero σ⌉⟩                                                        // [Close] restore; I = ∅
  IH := Ω_T ⊢ Id Nat (Add x̂ 0) x̂,   Ω_T = x° ↦ loan₀ ‖ x ↦ borrow₀ σ ‖ x̂ ↦ σ
    W = ∅
    ⟦Add x̂ 0⟧ = (N(σ,Z), ()),  ⟦x̂⟧ = (σ, ())                               // run (e), two frames deeper
    IH ≡ Eq Nat N(σ,Z) σ                                                   // [Eq ×], [Eq Unit], [∧ ⊤]
IH ≡ G₀
⟨x° ↦ σ⟩                                                                   // [Pop] x: borrow₀ σ ends into loan₀
```

This is a clean positive result for end goal 2: the statement about the in-place `AddM` and the statement about the pure-looking `Add` are definitionally the same proposition.

## Findings in detail

Format: (a) where in RULES.md, (b) what I assumed, (c) the simplest fix, (d) which decision it bears on.

**F1. [Seal] has no stop condition for the call it seals.**
(a) §3 [Seal] "run t from the empty environment; if it completes with v, the result is nf(v); otherwise ⌈t'⌉", with §3 [App] "If it gets stuck on a neutral match, use [Close]".
(b) The run of `⌈L; C; K⌉` uses the full machine, except that a stuck match directly in `C`'s own body counts as "does not complete". Both literal readings fail (S0, S2): with [Close], `nf(N(σ,w))` completes with `N(σ,w)` again and `nf(v)` recurses forever; without [Close], `N(S σ', Z)` stays stuck and the refined goals of AddMZero and AddZero no longer match their IHs.
(c) Add to [Seal]: "In this run [Close] applies to calls made from inside `C`'s body but not to `C` itself; if `C`'s body gets stuck, `⌈t⌉` is normal (with its embedded values normalised)." This is exactly the CIC guard: unfold a fixpoint only if its body gets past its own match.
(d) D4 stands; this is the missing half of "close off at the innermost stuck call".

**F2. Application is unary, [Close] is n-ary, and currying over a borrow breaks.**
(a) §1 `λ(x : A). t | t u`, `fix f (x : A) : B := t`; §3 [App] "push a frame [x ↦ w]"; §5 [Lam]; §6 "the recursive position"; versus §3 [Close] "the call f w₁ … wₙ".
(b) Assumed saturated n-ary calls with one frame per call and the first parameter as the recursive position.
(c) The curried reading of `AddM x 0` = `(AddM x) 0`: [App] on `AddM x` pushes `x₁ ↦ borrow₀ σ`, runs the body `λ(y : Nat). match *x₁ {…}` to a closure that captures the borrow `x₁` (forbidden by §1 "closures capture only borrow-free values"), then [Pop] ends `borrow₀` while the closure still names `x₁`. Fix: calls are saturated, `f t₁ … tₙ` with `f : Π(x₁:A₁)…(xₙ:Aₙ). B`; [Lam], [App], `fix` and §6 take telescopes, `fix` names its recursive parameter.
(d) Forced by D8 (closure capture); nothing to revert.

**F3. `refl` has no checking rule once Eq has computed.**
(a) §4 "`refl : Eq A a a`" together with the Eq conversions and P1 ("same normal form"); §1 lists `⊤` but no introduction form for it.
(b) Assumed `refl` is checked against the goal in its pre-Eq-rule form (`Eq Nat Z Z`, so `A = Nat`, `a = Z`).
(c) `refl` has no arguments, so it can only be checked, but the normal form of the Z-arm goal is `⊤`. Declaratively `refl : Eq Unit () () ≡ ⊤`, so it is derivable, but a checker must guess `A = Unit`. Fix, one rule: "`refl` checks against G iff nf(G) is reflexive, where `⊤` is reflexive, a stuck `Eq A a b` with nf(a) = nf(b) is reflexive, and `P ∧ Q` is reflexive when P and Q are." (Alternative: add `tt : ⊤` and let `refl` check only against stuck `Eq`, which is two rules.)
(d) D6: this rule is the price of Eq computing. N3 is the other side of the ledger.

**F4. "Owner" is not defined by its wording.**
(a) §4 Footprint: "The owner of a borrow is the owned place (…) that holds its loan once all borrows in Ω are ended", and "The footprint is syntactic".
(b) Literally, once all borrows are ended no loan exists, so nothing holds it. Reading "all *other* borrows" fails too: at the IH call point ending `borrow₀` requires its content `S loan₁` to be loan-free ([Reorg]), i.e. ending `borrow₁` first, the very borrow whose owner is wanted. Assumed the recursive definition below.
(c) Fix: "owner(ℓ): let r be the root variable of the place holding `loan_ℓ`; if r is owned (not of borrow type, or a ghost) then owner(ℓ) = r; if r holds `borrow_ℓ'` then owner(ℓ) = owner(ℓ')." Reword "The footprint is syntactic" to "Its variables are syntactic; their owners are read off Ω's loan structure, which refinement does not change."
(d) D5 stands. Worry (i): taking the outermost owner is what lets the environment perform the congruence in AddMZero with no Eq rule.

**F5. Where the ghost lives, and [Lam]'s missing pop.**
(a) §5 [Lam] "Open a frame. If A = &T: bind a ghost owner `x° : T ↦ loan_0` and `x : &T ↦ borrow_0 σ`"; §3 [Pop] "A dropped owned binding must contain no loans (else the program is rejected)".
(b) If `x°` is in the frame [Lam] opens and is dropped before `x`, it still holds `loan₀`, and every function with a borrow parameter is rejected. [Lam] also never says the frame is popped after the body, though [Pop]'s check is the borrow checker for locals. Assumed the ghost sits in its own frame below and is never popped by the body; [Lam] ends with [Pop] of the frame it opened.
(c) Fix: "[Lam] binds ghosts in a frame below the one it opens; after the body, pop the opened frame ([Pop])." Also make the loan label fresh (the text fixes `loan_0`; two borrow parameters need two).

**F6. The call point is not defined, and [App] can capture.**
(a) §3 [Close] "restore Ω to just before the call"; §5 [App] "B evaluated at the call site, with x bound to the argument".
(b) Assumed both mean: after all arguments are evaluated, before the callee frame is pushed. [Close] needs this (the loans ℓᵢ it fills are created by argument evaluation, e.g. `&(*x).1`), and so does [App] (the argument borrow must exist for the type to see "the caller's borrow structure around the argument"). Assumed B's parameter is bound in a fresh frame over the call-point Ω, renamed `x̂`: in AddMZero's S arm the caller has its own `x`, and B's `x` must not resolve to it.
(c) Fix: define "call point" once in [App], use it in [Close], and say "bind the parameters in a fresh frame".

**F7. Normal forms must be compared up to renaming.**
(a) P1 "same normal form"; §3 [Close] names `cᵢ`.
(b) The goal's `N(σ',Z)` (made in the [Seal] run of S2) and the IH's (made in run (c)) bind different place names. Assumed α-equivalence.
(c) Fix: "normal forms are compared up to renaming of places bound inside sealed programs (and, for E2, of loan labels local to one sealed program)."

**F8. `T_W` for an empty or unordered W.**
(a) §4 Observation "(v, Ω'_resolved(k) for k ∈ W)" and "Eq (A × T_W)".
(b) W is a set, so tuple order is unspecified, and for `W = ∅` (Add, AddZero) `T_W` is undefined. Assumed Ω order, `T_∅ = Unit`, observation `(v, ())`.
(c) Fix: "`T_W = T_k₁ × … × T_kₙ` in Ω order; `Unit` when W = ∅." Aside, not hit by E1: the first footprint clause ("the root owned place of every place under `&_` or left of `:=`") also catches places the term binds itself (`let n = 0; f &n; n`), which are not in Ω and cannot be observed; W should be restricted to places of Ω.

**F9. Typing of primitive forms and evaluation of types are not stated.**
(a) §5 gives only [Lam], [Split], [Join], [App], [Ref]; [Lam] says "Evaluate the goal B" but §3 has no rule for type formers.
(b) Assumed: a place has the type read off Ω (`x : &T` gives `*x : T`; `p : Nat` gives `p.1 : Nat`); `&p : &T` when `p : T`; `p := t : Unit` when `p, t : T`; `Z : Nat`; `S t : Nat` when `t : Nat`; `() : Unit`; `t; u` has u's type; `refl` per F3. A type evaluates to itself with its term arguments normalised, except `Id A t u`, which evaluates by §4 at the current Ω (this is what makes the entry goal a snapshot).
(c) Fix: a six-line table in §5 and one sentence in §3.

**F10. Sealed programs need a type for [Seal]'s Unit clause.**
(a) §3 [Seal] "At type Unit every value normalises to ()".
(b) Sealed programs carry no type, so nf cannot tell a Unit one from a Nat one. Assumed [Close] annotates each: the callee's result type for `⌈L; C⌉`, the type of `cᵢ` for `⌈L; C; cᵢ⌉`.
(c) Fix: write `⌈t⌉ : T`. The Unit clause is not load-bearing in E1: without it every `R(…)` either sits in an observation's result, where [Eq Unit] equates any two Unit values, or occurs identically on both sides of a conversion. It will matter when a Unit-typed sealed program is the argument of an abstract function (E4: `σ_f ⌈…⌉` vs `σ_f ()`), so keep it and say why.

**N1. A lemma call on a borrow forgets the borrowed content.** In AddMZero's S arm, [Close] on `AddMZero &p` fills `loan₁` with `M(σ') = ⌈let c = σ'; AddMZero &c; c⌉`, so after the call `(*x).1` no longer holds `σ'`. Harmless in E1 (tail position, and the goal is a snapshot), but a proof that calls a lemma on a borrow and then forms a type about the same place cannot prove, for example, that the place still equals a copy taken before, even though the lemma writes nothing. This is the right behaviour given that the lemma's type says nothing about its effect; it means lemmas over borrows are "havocking" calls, which E2's `AddMEqOwned` and any longer proof should expect.

**N2. Prop erasure is unspecified, and it matters.** Nothing in RULES says Prop terms are erased at runtime. If they are, a Prop-valued function that writes makes the checker and the compiled program disagree: `Evil : Π(x : &Nat). ⊤ := λx. (*x := 5; refl)` checks (with F3's rule), the checker's machine runs `Evil` inside `Id Nat (let n = 0; Evil &n; n) 5` and proves it by `refl`, while an erasing compiler drops the call and returns 0. Options for the lead: do not erase (proofs over borrows run at runtime, which is a cost); erase only the result value and keep the call; or reject writes in Prop-valued functions (a sort-based restriction, arguably not a pure/impure marker since the programmer writes no annotation). Not an E1 blocker; the IH call `AddMZero &p` is exactly such a Prop-valued call through a borrow.

**N3. What E1 actually uses of D6.** As written, the four proofs need (rather than merely apply) only [Eq ×] and [Eq Nat S S], and only in the direct `AddZero` (the IH there is about a copy `σ'`, so the `S` has to be stripped by a rule). AddMZero needs no Eq rule: its IH and refined goal are the same expression before any Eq rule fires. [Eq Unit] and the `⊤ ∧` rules become load-bearing only in the cross proofs of E1.4 (components in opposite order); `Eq Nat Z Z ≡ ⊤` is used only if the checker normalises the Z-arm goal before checking `refl`, which is what creates F3; the `⊥` rules are unused. For D6's "revisit if" clause: the rules earn their place through `AddZero`-direct and the cross proofs, and they cost exactly one checking rule (F3).
