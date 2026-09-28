# Deriver report, round 2: E1 under RULES v1

**Verdict:** under v1 all of E1 checks: AddM, AddMZero, Add, and AddZero (the direct proof, written with a `congS` defined from J), plus both cross proofs from round 1. The converse `AddMZero x := AddZero(*x)` checks as it stands. A third proof, `AddZero x := match x { Z => refl | S p => AddMZero(&p) }`, needs no `cong` at all. The round-1 blockers F1–F4 are fixed as intended, and P5 fixes N1/N2 up to one gap (G2).
**Most important finding:** G1. [Call-type] says "B evaluated at Ω" and does not say *after the arguments are evaluated*. Read literally, the argument's loan is not yet in Ω, so `owners(ℓ) = ∅` and every goal about a borrow parameter's effect computes to `⊤`: AddMZero's goal becomes `⊤`, and `refl` then "proves" `Π(x:&Nat). Id Unit (AddM(x, 1)) ()`. Fix: evaluate B at the call point (the state [Close] restores to).
**RULES.md must change:** G1 (call point in [Call-type]); G2 (P5 must keep argument evaluation of an erased Prop call, else checker and runtime disagree; concrete example below); G3 (J needs explicit endpoints, because Eq normalises to ⊤ and loses them); G4 (`cong` is not in v1's syntax, so §7's AddZero must be `congS(Add(p, 0), p, AddZero(p))`, or better go through AddMZero). G5–G10 are wording.
**Confidence:** high on the derivations and on G1, G2, G4; medium on how much G3 matters (E1 does not hit it).
**Not checked:** E2–E6; stuck blocks (no E1 program has a non-tail or type-level stuck match); [Seal]'s "inert loans" clause (no E1 sealed program has a hole); metatheory.

## Findings (one line each; details at the end)

- **G1** §5 [Call-type] "B evaluated at Ω": the rule must say "after the arguments are evaluated". Literally, loans made by the arguments are missing, `W = ∅`, and effect-observing goals collapse to `⊤`. [Def] inherits this. Fix: "at the call point, the state after all arguments are evaluated (the one [Close] restores to)".
- **G2** §0 P5 + §1 "Prop … is erased at runtime": the checker evaluates a Prop call's arguments (call-by-value) but does not run its body. If runtime erasure also drops the arguments, `refl` proves `Id Nat (let n = Z; Lemma(AddM(&n, S Z)); n) (S Z)` while the compiled program returns `Z`. Fix: erasure drops the body and the result only; the arguments still run. Also `⋆` is not in §2's values.
- **G3** §4 "J / transport … as in CIC", `J(A, P, h, t)`: the endpoints `a`, `b` must be read off `h`'s type, but types are kept in normal form, and `Eq A a b ≡ ⊤` (when `a ≡ b`) erases them. Not hit by E1. Fix: `J(A, a, b, P, h, t)`.
- **G4** §7 "`cong S (AddZero(p))`" is not v1 syntax: there is no `cong`, no curried application, `S` is not a function value, and there are no implicit arguments. The expressible form is `congS(Add(p, 0), p, AddZero(p))`, which restates the IH's endpoints. The borrow route (`S p => AddMZero(&p)`) needs nothing. Supports D16.
- **G5** §5 [Def] "the body runs in a pushed frame" never says the frame is popped, and the pop is where [Drop]'s "loan in a dropped owned value" check fires for locals. Fix: "push, run, pop ([Drop]), as [Call]".
- **G6** §5 [Rec] "the recursive position" is not designated (AddM has two parameters). Fix: "in one position, fixed per definition" (the checker may search for it, as Lean does).
- **G7** §3 [Seal] "the head call of t": the syntactic head of `let c₁ = σ; AddM(&c₁, Z); c₁` is `let`. Fix: "the call C that [Close] wrote (every sealed program is `L; C; K`)".
- **G8** §3 [Call] "If B is a proposition": should read "if B : Prop". The motive `P : Π(y:Nat). Prop` in congS has result type `Prop`, which is not a proposition, and must run. Minor.
- **G9** (round-1 F9, still open) §5 still has no typing rules for places, `&p`, `:=`, constructors, `t; u`, or J, and no rule for evaluating type formers. v1 leans on them more than v0 did: [Call-type]'s "each aᵢ must have type Aᵢ" needs the types of `&(*x).1`, `*x` and `Add(p, 0)`, and each Aᵢ must be evaluated with the earlier parameters bound (congS's `h : Eq Nat a b`). Fix: a short table.
- **G10** (round-1 F7) comparing normal forms up to renaming is still unstated. It goes away if [Close]'s `cᵢ` are read as the fixed names `c₁ … cₙ` (sealed programs are closed, so nothing can be captured). The goal's and the IH's `N(σ',Z)` are then identical symbol for symbol. Fix: one sentence saying so.

## Round-1 findings under v1

| round 1 | v1 | status |
|---|---|---|
| F1 [Seal] loops / no `S` | D9 head-call guard | fixed; S0 stops, S2 gives `S N(σ',Z)` |
| F2 unary calls | D10 saturated calls | fixed |
| F3 `refl` vs computed goal | `refl : ⊤` | fixed; the Z arms reduce the goal to `⊤` |
| F4 owner undefined | D18 owner sets | fixed; `owners(1) = owners(0) = {c₀}` at the IH |
| F5 ghost frame, missing pop | D12 generic call | ghost fixed (it is `c₀`, one frame down); pop still unstated (G5) |
| F6 call point | [Close] says "after its arguments are evaluated" | half fixed; [Call-type] still does not say it (G1) |
| F7 α-equivalence | none | open, but dissolvable (G10) |
| F8 `T_W` for `W = ∅`, order | "the pair is just A", "in the order of Ω" | fixed |
| F9 primitive typing | none | open (G9) |
| F10 Unit η needs types | [Close]'s Unit row returns `()` | fixed: no Unit-typed sealed program is ever made |
| N1 lemma call havocs | P5 | fixed: after `AddMZero(&p)`, `x ↦ borrow₀ (S σ')` |
| N2 Prop erasure | P5, §1 | fixed for bodies; arguments still open (G2) |

## v1 changes exercised

- **[Def], generic call, no ghosts:** AddM, AddMZero, Add, AddZero, congS and both cross proofs. It gives round 1's environment with `x°` renamed `c₀`, as simplifier §6.0 said.
- **[Call-type]:** every IH (AddMZero's S arm; AddZero's S arm; `congS`'s own call; both cross proofs). It works at the call point (G1).
- **Loans as variables, [End] substituting:** [Close]'s fills; the pop in S2; the IH's `()` observation, which ends `borrow₀` and `borrow₁` in either order with the same result.
- **[Seal] head-call guard:** S0 stops at the head call; S2 closes off the inner call and returns `S N(σ',Z)`.
- **P5:** the IH calls `AddMZero(&p)`, `AddZero(p)`, `congS(…)` are not run, and the borrow comes back unchanged.
- **Trimmed Eq, `refl : ⊤`:** the Z arms, the Unit component (dropped by the reflexivity rule, since both results are `()`), and the cross proofs (which need [Eq ×] plus reflexivity plus `⊤ ∧`). AddZero's S arm needs `cong`.
- **[Rec] on entry values:** AddM and AddMZero (borrow content `σ'`, a strict subterm of `S σ'`), AddZero (`σ'`). G6.

## Conventions

- Ω is written oldest frame first, frames separated by `‖`; `ε` is empty. `⟨Ω, t⟩` lines are machine states, one step per line, rule after `//`. [Access] is written only when it does something (in E1 it never ends anything in the checked programs).
- Callee parameters are subscripted by depth (`x₁`, `x₂`); a Π-type's parameter bound by [Call-type] is written `x̂`. `0` is `Z`.
- **Call point**: the state after all arguments are evaluated, before the callee frame is pushed (G1). [Call-type] is evaluated there, with the parameters in a fresh frame; [Close] restores to it.
- `N(v, w) := ⌈let c₁ = v; AddM(&c₁, w); c₁⌉`, the final content of the place a stuck `AddM(borrow v, w)` borrowed. [Close]'s Unit row returns `()` for the call itself. `c₁` is the fixed name (G10).
- `⋆` is the value of an unrun Prop call (G2).

## E1.1 AddM

`AddM := fix AddM (x : &Nat, y : Nat) : Unit := match *x { Z => *x := y | S p => AddM(&p, y) }`

```
⊢ AddM : Π(x : &Nat, y : Nat). Unit                                     // [Def]
  generic caller: c₀ ↦ σ;  call AddM(&c₀, σy)                           // [Def] one owned c₀ for the borrow parameter, σy for y
  ⟨c₀ ↦ σ, &c₀⟩ ⇓ ⟨c₀ ↦ loan₀, borrow₀ σ⟩                               // [Borrow]; call point
  goal: Unit                                                             // [Call-type] at the call point, x ↦ borrow₀ σ, y ↦ σy
  Ω_A := c₀ ↦ loan₀ ‖ x ↦ borrow₀ σ, y ↦ σy                             // [Def] body frame pushed
  Ω_A ⊢ match *x {…} ⇓ () : Unit                                        // [Split]
    content(Ω_A, *x) = σ                                                 // [Access] nothing on the path; head σ abstract
    arm Z, σ := Z:
      c₀ ↦ loan₀ ‖ x ↦ borrow₀ Z, y ↦ σy ⊢ *x := y ⇓ () : Unit           // [Assign] (typing assumed, G9)
        ⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ Z, y ↦ σy, *x := y⟩
        ⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ Z, y ↦ σy, *x := σy⟩                   // [Read] y: borrow-free, copy
        ⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ σy, y ↦ σy, ()⟩                        // [Assign] [Drop] old content Z (nothing to end); *x ↦ σy
      Unit ≡ Unit
      ⟨c₀ ↦ σy⟩                                                          // pop (G5): [Drop] x: [End 0], σy substituted for loan₀; y dropped
    arm S, σ := S σ':
      Ω_S := c₀ ↦ loan₀ ‖ x ↦ borrow₀ (S σ'), y ↦ σy;  p := (*x).1       // [Split]; [Match] sub-place
      Ω_S ⊢ AddM(&(*x).1, y) ⇓ () : Unit
        ⟨Ω_S, AddM(&(*x).1, y)⟩
        ⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁), y ↦ σy, AddM(borrow₁ σ', y)⟩  // [Borrow] ℓ = 1
        ⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁), y ↦ σy, AddM(borrow₁ σ', σy)⟩ // [Read] y copy; call point
        [Rec]: position 1 gets a borrow whose content σ' is a strict subterm of the entry value σ = S σ'   // ✓ (G6)
        type: Unit                                                       // [Call-type]; args: &Nat, Nat ✓
        ⟨… ‖ x₁ ↦ borrow₁ σ', y₁ ↦ σy, match *x₁ {…}⟩                     // [Call] Unit is not a Prop: push frame, run body
        stuck                                                            // [Match] head σ' neutral, in the callee's body
        ⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁), y ↦ σy, AddM(borrow₁ σ', σy)⟩ // [Close] discard, back to the call point
        ⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ (S N(σ',σy)), y ↦ σy, ()⟩               // [Close] I={1}, L = let c₁ = σ', C = AddM(&c₁, σy); Unit row: result (), loan₁ := N(σ',σy)
      Unit ≡ Unit
      ⟨c₀ ↦ S N(σ',σy)⟩                                                  // pop: [Drop] x: [End 0]; y dropped
```

## Sealed-program lemmas

### S0. `nf(N(σ, w)) = N(σ, w)` for abstract σ: the head-call guard stops it

```
nf(N(σ, w)) = N(σ, w)                                                    // [Seal]
  ⟨ε, let c₁ = σ; AddM(&c₁, w); c₁⟩
  ⟨c₁ ↦ σ, AddM(&c₁, w); c₁⟩                                            // [Let]
  ⟨c₁ ↦ loan₁, AddM(borrow₁ σ, w); c₁⟩                                  // [Borrow]; call point of the head call C
  ⟨c₁ ↦ loan₁ ‖ x₁ ↦ borrow₁ σ, y₁ ↦ w, match *x₁ {…}⟩                   // [Call] push frame
  stuck                                                                  // [Match] σ neutral, in C's own body
  C is the head call, not eligible for [Close]: the run does not complete // [Seal] (G7: "head call" = C)
  result ⌈t'⌉ = N(σ, w)                                                  // σ, w already normal
```

### S1. `nf(N(Z, Z)) = Z`

```
nf(N(Z, Z)) = Z                                                          // [Seal]
  ⟨ε, let c₁ = Z; AddM(&c₁, Z); c₁⟩
  ⟨c₁ ↦ Z, AddM(&c₁, Z); c₁⟩                                            // [Let]
  ⟨c₁ ↦ loan₁, AddM(borrow₁ Z, Z); c₁⟩                                  // [Borrow]
  ⟨c₁ ↦ loan₁ ‖ x₁ ↦ borrow₁ Z, y₁ ↦ Z, match *x₁ {…}⟩                   // [Call] push frame
  ⟨c₁ ↦ loan₁ ‖ x₁ ↦ borrow₁ Z, y₁ ↦ Z, *x₁ := y₁⟩                       // [Match] head Z
  ⟨c₁ ↦ loan₁ ‖ x₁ ↦ borrow₁ Z, y₁ ↦ Z, ()⟩                              // [Read] y₁ copy; [Assign]
  ⟨c₁ ↦ Z, (); c₁⟩                                                       // [Call] pop: [Drop] x₁: [End 1], Z for loan₁; y₁ dropped
  ⟨c₁ ↦ Z, Z⟩                                                            // [Let] drop (); [Read] c₁ copy
  ⟨ε, Z⟩                                                                 // [Let] [Drop] c₁: no loan in it
```

### S2. `nf(N(S σ', Z)) = S N(σ', Z)` (round-1 worry iii)

```
nf(N(S σ', Z)) = S N(σ', Z)                                              // [Seal]
  ⟨ε, let c₁ = S σ'; AddM(&c₁, Z); c₁⟩
  ⟨c₁ ↦ S σ', AddM(&c₁, Z); c₁⟩                                         // [Let]
  ⟨c₁ ↦ loan₁, AddM(borrow₁ (S σ'), Z); c₁⟩                             // [Borrow]; call point of C
  ⟨c₁ ↦ loan₁ ‖ x₁ ↦ borrow₁ (S σ'), y₁ ↦ Z, match *x₁ {…}⟩              // [Call] push C's frame
  ⟨c₁ ↦ loan₁ ‖ x₁ ↦ borrow₁ (S σ'), y₁ ↦ Z, AddM(&(*x₁).1, y₁)⟩         // [Match] head S σ': S arm
  ⟨c₁ ↦ loan₁ ‖ x₁ ↦ borrow₁ (S loan₂), y₁ ↦ Z, AddM(borrow₂ σ', Z)⟩     // [Borrow] ℓ = 2; [Read] y₁; inner call point
  ⟨… ‖ x₂ ↦ borrow₂ σ', y₂ ↦ Z, match *x₂ {…}⟩                           // [Call] push inner frame
  stuck                                                                  // [Match] σ' neutral, in the INNER call's body
  ⟨c₁ ↦ loan₁ ‖ x₁ ↦ borrow₁ (S loan₂), y₁ ↦ Z, AddM(borrow₂ σ', Z)⟩     // [Close] eligible (not the head call): restore
  ⟨c₁ ↦ loan₁ ‖ x₁ ↦ borrow₁ (S N(σ',Z)), y₁ ↦ Z, ()⟩                    // [Close] Unit row; loan₂ := N(σ',Z) (substituted)
  ⟨c₁ ↦ S N(σ',Z), (); c₁⟩                                               // [Call] pop C's frame: [Drop] x₁: [End 1] substitutes S N(σ',Z) for loan₁
  ⟨c₁ ↦ S N(σ',Z), S N(σ',Z)⟩                                            // [Let] drop (); [Read] c₁: borrow-free, copy
  ⟨ε, S N(σ',Z)⟩                                                         // [Let] [Drop] c₁
  completes; value S N(σ',Z), with N(σ',Z) normal by S0                  // [Seal]
```

## E1.2 AddMZero

`AddMZero := fix AddMZero (x : &Nat) : Id Unit (AddM(x, 0)) () := match *x { Z => refl | S p => AddMZero(&p) }`

```
⊢ AddMZero : Π(x : &Nat). Id Unit (AddM(x, 0)) ()                        // [Def]
  generic caller: c₀ ↦ σ;  call AddMZero(&c₀)
  ⟨c₀ ↦ σ, &c₀⟩ ⇓ ⟨c₀ ↦ loan₀, borrow₀ σ⟩                                // [Borrow]; call point
  G₀ := Eq Nat N(σ,Z) σ                                                  // [Call-type] at the call point, x ↦ borrow₀ σ: §E1.2a
  Ω₀ := c₀ ↦ loan₀ ‖ x ↦ borrow₀ σ                                       // [Def] body frame pushed
  entry value of x for [Rec]: σ
  Ω₀ ⊢ match *x { Z => refl | S p => AddMZero(&p) } : G₀                 // [Split]: §E1.2b, §E1.2c
```

### E1.2a Entry goal

```
Id Unit (AddM(x, 0)) ()  at  c₀ ↦ loan₀ ‖ x̂ ↦ borrow₀ σ   ≡  Eq Nat N(σ,Z) σ     // [Call-type]; x written x̂ in its fresh frame
  W(AddM(x̂, 0), ()) = owners(0) = {c₀}                                  // Footprint: x̂ is a free borrow-typed variable holding borrow₀; loan₀ occurs once, in the owned binding c₀
  T_W = Nat                                                              // c₀ : Nat
  ⟦AddM(x̂, 0)⟧ = ((), N(σ,Z))                                            // run (a)
  ⟦()⟧ = ((), σ)                                                         // run (b)
  Eq (Unit × Nat) ((), N(σ,Z)) ((), σ)                                   // [Id computes]
    ≡ Eq Unit () () ∧ Eq Nat N(σ,Z) σ                                    // [Eq ×]
    ≡ ⊤ ∧ Eq Nat N(σ,Z) σ                                                // [Eq ≡⊤]: () ≡ ()
    ≡ Eq Nat N(σ,Z) σ                                                    // [⊤ ∧]; stays stuck, N(σ,Z) ≢ σ
```

Run (a), on a private copy:

```
⟨c₀ ↦ loan₀ ‖ x̂ ↦ borrow₀ σ, AddM(x̂, Z)⟩
⟨c₀ ↦ loan₀ ‖ x̂ ↦ ⊥, AddM(borrow₀ σ, Z)⟩                                // [Read] x̂ holds a borrow: move; call point
⟨… ‖ x₁ ↦ borrow₀ σ, y₁ ↦ Z, match *x₁ {…}⟩                              // [Call] Unit is not a Prop: push, run
stuck                                                                    // [Match] σ neutral
⟨c₀ ↦ loan₀ ‖ x̂ ↦ ⊥, AddM(borrow₀ σ, Z)⟩                                // [Close] restore
⟨c₀ ↦ N(σ,Z) ‖ x̂ ↦ ⊥, ()⟩                                               // [Close] I={1}, L = let c₁ = σ, C = AddM(&c₁, Z); Unit row; loan₀ := N(σ,Z)
no borrows left to end; observe ((), c₀) = ((), N(σ,Z))                  // §4 Observation; N(σ,Z) normal (S0)
```

Run (b), on an independent copy:

```
⟨c₀ ↦ loan₀ ‖ x̂ ↦ borrow₀ σ, ()⟩                                        // a value
⟨c₀ ↦ σ ‖ x̂ ↦ ⊥, ()⟩                                                    // end every borrow: [End 0], σ substituted for loan₀
observe ((), σ)
```

### E1.2b Z arm

```
Ω_Z ⊢ refl : G_Z                                                         // refl : ⊤
  Ω_Z = c₀ ↦ loan₀ ‖ x ↦ borrow₀ Z                                       // [Split] σ := Z in Ω
  G_Z = Eq Nat N(Z,Z) Z                                                  // [Split] σ := Z in the goal
      = Eq Nat Z Z                                                       // [Seal] re-normalise, S1
      ≡ ⊤                                                                // [Eq ≡⊤]
  ⟨c₀ ↦ Z⟩                                                               // pop: [Drop] x: [End 0]
```

### E1.2c S arm

```
Ω_S ⊢ AddMZero(&(*x).1) ⇓ ⋆ : IH,   IH ≡ G_S                              // [Call-type], then conversion
  Ω_S = c₀ ↦ loan₀ ‖ x ↦ borrow₀ (S σ');   p := (*x).1                   // [Split] σ := S σ'; [Match] sub-place
  G_S = Eq Nat N(S σ',Z) (S σ')                                          // [Split] σ := S σ' in the goal
      = Eq Nat (S N(σ',Z)) (S σ')                                        // [Seal] re-normalise, S2; stuck (no injectivity in v1)
  ⟨Ω_S, AddMZero(&(*x).1)⟩
  ⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁), AddMZero(borrow₁ σ')⟩            // [Access] nothing to end; [Borrow] ℓ = 1; call point Ω_c
  [Rec]: a borrow whose content σ' is a strict subterm of the entry value σ = S σ'   // ✓
  argument type: &(*x).1 : &Nat ✓                                        // (G9)
  IH := Id Unit (AddM(x̂, 0)) ()  at  Ω_c ‖ x̂ ↦ borrow₁ σ'               // [Call-type] at the call point (G1)
    owners(1): loan₁ occurs inside the content of borrow₀ → owners(0) = {c₀}   // §4 Owners (round-1 worry i: yes, the generic caller's c₀)
    W = {c₀}, T_W = Nat
    ⟦AddM(x̂, 0)⟧ = ((), S N(σ',Z))                                       // run (c)
    ⟦()⟧ = ((), S σ')                                                    // run (d)
    IH ≡ Eq (Unit × Nat) ((), S N(σ',Z)) ((), S σ')                      // [Id computes]
       ≡ Eq Unit () () ∧ Eq Nat (S N(σ',Z)) (S σ')                       // [Eq ×]
       ≡ Eq Nat (S N(σ',Z)) (S σ')                                       // [Eq ≡⊤], [⊤ ∧]
  IH ≡ G_S                                                               // identical, including the name c₁ inside N (G10)
  ⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ (S σ'), ⋆⟩                                   // [Call] result type is a Prop: body not run, ⋆; [End 1] on the argument, σ' back into loan₁ (P5)
  ⟨c₀ ↦ S σ'⟩                                                            // pop: [Drop] x: [End 0]
```

Run (c), on a private copy of `Ω_c ‖ x̂ ↦ borrow₁ σ'`:

```
⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁) ‖ x̂ ↦ borrow₁ σ', AddM(x̂, Z)⟩
⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁) ‖ x̂ ↦ ⊥, AddM(borrow₁ σ', Z)⟩       // [Read] move; call point
⟨… ‖ x₁ ↦ borrow₁ σ', y₁ ↦ Z, match *x₁ {…}⟩                              // [Call] push, run
stuck                                                                     // [Match] σ' neutral
⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁) ‖ x̂ ↦ ⊥, AddM(borrow₁ σ', Z)⟩       // [Close] restore
⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ (S N(σ',Z)) ‖ x̂ ↦ ⊥, ()⟩                       // [Close] Unit row; loan₁ := N(σ',Z)
⟨c₀ ↦ S N(σ',Z) ‖ x ↦ ⊥ ‖ x̂ ↦ ⊥, ()⟩                                      // end every borrow: [End 0]
observe ((), S N(σ',Z))                                                   // the S is x's borrow content: the environment did the congruence
```

Run (d), on an independent copy. [End] has no side condition in v1, so either order gives the same result:

```
⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁) ‖ x̂ ↦ borrow₁ σ', ()⟩                // a value
order 1:  ⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ (S σ') ‖ x̂ ↦ ⊥⟩                       // [End 1]
          ⟨c₀ ↦ S σ' ‖ x ↦ ⊥ ‖ x̂ ↦ ⊥⟩                                      // [End 0]
order 2:  ⟨c₀ ↦ S loan₁ ‖ x ↦ ⊥ ‖ x̂ ↦ borrow₁ σ'⟩                          // [End 0]: loan₁ travels with the content
          ⟨c₀ ↦ S σ' ‖ x ↦ ⊥ ‖ x̂ ↦ ⊥⟩                                      // [End 1]: substituted inside c₀
observe ((), S σ')
```

AddMZero checks. No Eq rule is load-bearing in the S arm: IH and goal are the same expression before and after the Eq rules.

## E1.3 Add

`Add := fix Add (x : Nat, y : Nat) : Nat := AddM(&x, y); x`

```
⊢ Add : Π(x : Nat, y : Nat). Nat                                          // [Def]
  generic caller: ε; call Add(σx, σy)                                     // no borrow parameters: no cᵢ
  goal: Nat                                                               // [Call-type]
  Ω₊ := ε ‖ x ↦ σx, y ↦ σy                                                // body frame
  Ω₊ ⊢ AddM(&x, y); x ⇓ N(σx,σy) : Nat
    ⟨x ↦ σx, y ↦ σy, AddM(&x, y); x⟩
    ⟨x ↦ loan₀, y ↦ σy, AddM(borrow₀ σx, y); x⟩                          // [Borrow]
    ⟨x ↦ loan₀, y ↦ σy, AddM(borrow₀ σx, σy); x⟩                         // [Read] y copy; call point
    type of the call: Unit; args &Nat, Nat ✓                             // [Call-type]
    ⟨… ‖ x₁ ↦ borrow₀ σx, y₁ ↦ σy, match *x₁ {…}⟩                         // [Call] push, run
    stuck                                                                 // [Match] σx neutral, callee body: [Close], not [Split]
    ⟨x ↦ loan₀, y ↦ σy, AddM(borrow₀ σx, σy); x⟩                         // [Close] restore
    ⟨x ↦ N(σx,σy), y ↦ σy, (); x⟩                                         // [Close] Unit row; loan₀ := N(σx,σy)
    ⟨x ↦ N(σx,σy), y ↦ σy, N(σx,σy)⟩                                      // [Let] drop (); [Read] x: borrow-free, copy; type Nat
  Nat ≡ Nat
  ⟨ε⟩                                                                     // pop: x, y owned, no loans in them
```

## E1.4 AddZero, direct, with `congS`

v1 §7's `cong S (AddZero(p))` cannot be written in v1 (G4). The closest expressible term needs a helper defined from J. Assumed shape of J (G3): `J(A, P, h, t)` with `h : Eq A a b`, where `a` and `b` are read off `h`'s stuck type, `P : Π(y:A). Prop` (the proof argument of CIC's motive is dropped, which is harmless under definitional proof irrelevance), and `t : P(a)`, giving type `P(b)`.

```
congS := fix congS (a : Nat, b : Nat, h : Eq Nat a b) : Eq Nat (S a) (S b) :=
           J(Nat, fix P (y : Nat) : Prop := Eq Nat (S a) (S y), h, refl)
```

```
⊢ congS : Π(a : Nat, b : Nat, h : Eq Nat a b). Eq Nat (S a) (S b)        // [Def]
  generic caller: ε; call congS(σa, σb, σh)                               // σh's type: Eq Nat a b with a, b bound = Eq Nat σa σb (stuck); telescope, G9
  goal: Eq Nat (S σa) (S σb)                                              // [Call-type]; stuck, S σa ≢ S σb
  body frame: a ↦ σa, b ↦ σb, h ↦ σh
  ⊢ J(Nat, P, h, refl) : Eq Nat (S σa) (S σb)                              // J (typing assumed, G3/G9)
    P := closure of fix P (y : Nat) : Prop := Eq Nat (S a) (S y), capturing a = σa   // P2: borrow-free capture
    h : Eq Nat σa σb, so the endpoints are σa, σb                          // read off h's stuck type
    t = refl : P(σa)?                                                      // [Call] P: result type Prop is not a proposition (G8), so it runs
      P(σa) ⇓ Eq Nat (S σa) (S σa) ≡ ⊤                                     // [Eq ≡⊤]
      refl : ⊤ ✓
    J(…) : P(σb) ⇓ Eq Nat (S σa) (S σb) ≡ goal ✓                           // [Call] P runs again
```

`AddZero := fix AddZero (x : Nat) : Id Nat (Add(x, 0)) x := match x { Z => refl | S p => congS(Add(p, 0), p, AddZero(p)) }`

```
⊢ AddZero : Π(x : Nat). Id Nat (Add(x, 0)) x                              // [Def]
  generic caller: ε; call AddZero(σ)
  G₀ := Eq Nat N(σ,Z) σ                                                   // [Call-type] at ε ‖ x̂ ↦ σ:
    W(Add(x̂, 0), x̂) = ∅                                                   // no free place under &_ or :=, no borrow-typed variable (the & in Add's body is not in the term)
    ⟦Add(x̂, 0)⟧ = N(σ,Z)                                                  // run (e); W = ∅, so the observation is just the result
    ⟦x̂⟧ = σ                                                               // [Read] copy
    Id Nat … ≡ Eq Nat N(σ,Z) σ                                            // [Id computes] ("when W is empty the pair is just A"); stuck
  Ω₀ := ε ‖ x ↦ σ; entry value σ
  match x                                                                 // [Split] head σ abstract
  arm Z, σ := Z:  x ↦ Z ⊢ refl : Eq Nat N(Z,Z) Z = Eq Nat Z Z ≡ ⊤         // [Seal] S1; [Eq ≡⊤]
  arm S, σ := S σ':
    Ω_S = x ↦ S σ';  p := x.1
    G_S = Eq Nat N(S σ',Z) (S σ') = Eq Nat (S N(σ',Z)) (S σ')              // [Seal] S2
    Ω_S ⊢ congS(Add(p, 0), p, AddZero(p)) ⇓ ⋆ : T,  T ≡ G_S
      ⟨x ↦ S σ', congS(Add(x.1, Z), x.1, AddZero(x.1))⟩
      argument 1: ⟨x ↦ S σ', Add(x.1, Z)⟩ ⇓ ⟨x ↦ S σ', N(σ',Z)⟩             // [Read] x.1 copy σ'; [Call] Add runs (Nat is not a Prop): run (e) with σ'
      argument 2: ⟨x ↦ S σ', x.1⟩ ⇓ ⟨x ↦ S σ', σ'⟩                         // [Read] copy
      argument 3: AddZero(x.1)
        ⟨x ↦ S σ', AddZero(σ')⟩                                            // [Read] copy; call point
        [Rec]: σ' is a strict subterm of the entry value σ = S σ'  ✓
        type: Id Nat (Add(x̂, 0)) x̂ at Ω_S ‖ x̂ ↦ σ' ≡ Eq Nat N(σ',Z) σ'      // [Call-type]; W = ∅; run (e) with σ'
        ⟨x ↦ S σ', ⋆⟩                                                      // [Call] a Prop call: not run; no borrow arguments (P5)
      call point: congS(N(σ',Z), σ', ⋆)
      argument types: N(σ',Z) : Nat, σ' : Nat, and h's type                // [Call-type] "each aᵢ must have type Aᵢ"
        A₃ = Eq Nat a b with a ↦ N(σ',Z), b ↦ σ' = Eq Nat N(σ',Z) σ'  ≡ type of argument 3 ✓
      T = Eq Nat (S a) (S b) with a, b bound = Eq Nat (S N(σ',Z)) (S σ')   // [Call-type]
      ⟨x ↦ S σ', ⋆⟩                                                        // [Call] congS is a Prop call: not run
    T ≡ G_S ✓                                                              // identical
    ⟨ε⟩                                                                    // pop
```

Run (e), `⟦Add(x̂, 0)⟧` at `ε ‖ x̂ ↦ σ`, on a private copy:

```
⟨x̂ ↦ σ, Add(x̂, Z)⟩
⟨x̂ ↦ σ, Add(σ, Z)⟩                                                       // [Read] copy; call point
⟨x̂ ↦ σ ‖ x₁ ↦ σ, y₁ ↦ Z, AddM(&x₁, y₁); x₁⟩                              // [Call] Nat is not a Prop: push, run
⟨x̂ ↦ σ ‖ x₁ ↦ loan₀, y₁ ↦ Z, AddM(borrow₀ σ, Z); x₁⟩                     // [Borrow]; [Read] y₁; call point
⟨… ‖ x₂ ↦ borrow₀ σ, y₂ ↦ Z, match *x₂ {…}⟩                               // [Call] push, run
stuck                                                                     // [Match] σ neutral: innermost call is AddM, so AddM closes, not Add
⟨x̂ ↦ σ ‖ x₁ ↦ N(σ,Z), y₁ ↦ Z, (); x₁⟩                                    // [Close] restore; Unit row; loan₀ := N(σ,Z)
⟨x̂ ↦ σ ‖ x₁ ↦ N(σ,Z), y₁ ↦ Z, N(σ,Z)⟩                                    // [Let] drop (); [Read] x₁ copy
⟨x̂ ↦ σ, N(σ,Z)⟩                                                          // [Call] pop Add's frame
no borrows to end; observe N(σ,Z)
```

AddZero checks. The cost of dropping injectivity is the helper `congS` and restating the IH's left side `Add(p, 0)` as an argument, because v1 has no implicit arguments. §E1.5 shows that AddZero needs neither if it goes through AddMZero.

## E1.5 Cross proofs

### `AddZero x := AddMZero(&x)`: no match, no recursion, no cong

```
⊢ fix AddZero (x : Nat) : Id Nat (Add(x, 0)) x := AddMZero(&x)           // [Def]
  generic caller ε; call AddZero(σ); G₀ = Eq Nat N(σ,Z) σ                // [Call-type], as in §E1.4
  Ω₀ := ε ‖ x ↦ σ
  Ω₀ ⊢ AddMZero(&x) ⇓ ⋆ : IH,  IH ≡ G₀
    ⟨x ↦ loan₀, AddMZero(borrow₀ σ)⟩                                     // [Borrow]; call point Ω_c
    IH := Id Unit (AddM(x̂, 0)) () at x ↦ loan₀ ‖ x̂ ↦ borrow₀ σ           // [Call-type]
      W = owners(0) = {x}                                                // loan₀ occurs in the owned binding x
      ⟦AddM(x̂, 0)⟧ = ((), N(σ,Z))                                        // [Read] move x̂; [Call]; [Match] stuck; [Close] Unit row, loan₀ := N(σ,Z): x ↦ N(σ,Z)
      ⟦()⟧ = ((), σ)                                                     // [End 0]: x ↦ σ
      IH ≡ Eq (Unit × Nat) ((), N(σ,Z)) ((), σ)
         ≡ Eq Unit () () ∧ Eq Nat N(σ,Z) σ ≡ Eq Nat N(σ,Z) σ             // [Eq ×], [Eq ≡⊤], [⊤ ∧]
    ⟨x ↦ σ, ⋆⟩                                                           // [Call] Prop call: not run; [End 0] on the argument (P5)
  IH ≡ G₀ ✓                                                              // needs all three Eq rules: the goal is bare Nat (W = ∅), the IH is Unit × Nat
  ⟨ε⟩                                                                    // pop
```

### `AddMZero x := AddZero(*x)`: checks unchanged

```
⊢ fix AddMZero (x : &Nat) : Id Unit (AddM(x, 0)) () := AddZero(*x)       // [Def]
  generic caller c₀ ↦ σ; call point c₀ ↦ loan₀, x ↦ borrow₀ σ
  G₀ = Eq Nat N(σ,Z) σ                                                   // §E1.2a
  Ω₀ := c₀ ↦ loan₀ ‖ x ↦ borrow₀ σ
  Ω₀ ⊢ AddZero(*x) ⇓ ⋆ : IH,  IH ≡ G₀
    ⟨Ω₀, AddZero(σ)⟩                                                     // [Access] nothing on the path; [Read] *x: content σ borrow-free, copy (x keeps its borrow); call point
    IH := Id Nat (Add(x̂, 0)) x̂ at Ω₀ ‖ x̂ ↦ σ                            // [Call-type]
      W = ∅                                                              // no free place under &_ or :=, no borrow-typed variable
      ⟦Add(x̂, 0)⟧ = N(σ,Z)                                               // run (e) two frames deeper; ending borrow₀ in the copy is irrelevant (W = ∅)
      ⟦x̂⟧ = σ
      IH ≡ Eq Nat N(σ,Z) σ
    ⟨Ω₀, ⋆⟩                                                              // [Call] Prop call: not run; no borrow arguments
  IH ≡ G₀ ✓
  ⟨c₀ ↦ σ⟩                                                               // pop: [Drop] x: [End 0]
```

No adjustment is needed. The only v1 rules this touches are P3 (reading `*x` copies `σ` and leaves the borrow in place) and P5.

### `AddZero x := match x { Z => refl | S p => AddMZero(&p) }`: the owned statement, by borrowing the tail

The S arm of §E1.4, with the `congS` call replaced by a borrow of the tail:

```
Ω_S = x ↦ S σ'; p := x.1;  G_S = Eq Nat (S N(σ',Z)) (S σ')              // as in §E1.4
Ω_S ⊢ AddMZero(&x.1) ⇓ ⋆ : IH,  IH ≡ G_S
  ⟨x ↦ S loan₁, AddMZero(borrow₁ σ')⟩                                    // [Borrow] ℓ = 1; call point Ω_c
  [Rec]: not a recursive call (AddMZero ≠ AddZero), so no check
  IH := Id Unit (AddM(x̂, 0)) () at x ↦ S loan₁ ‖ x̂ ↦ borrow₁ σ'
    W = owners(1) = {x}                                                  // loan₁ occurs inside the owned binding x
    ⟦AddM(x̂, 0)⟧ = ((), S N(σ',Z))                                       // [Read] move; [Call]; stuck; [Close] loan₁ := N(σ',Z): x ↦ S N(σ',Z)
    ⟦()⟧ = ((), S σ')                                                    // [End 1]: x ↦ S σ'
    IH ≡ Eq Nat (S N(σ',Z)) (S σ')                                       // [Eq ×], [Eq ≡⊤], [⊤ ∧]
  ⟨x ↦ S σ', ⋆⟩                                                          // [Call] not run; [End 1] (P5)
IH ≡ G_S ✓
```

Here the head `S` sits in the owned `x` around `loan₁`, so the environment does the congruence exactly as it does in AddMZero. The pure-looking statement is proved by the in-place lemma with no `cong` and no Nat rule. This is the strongest data point for D16: the only E1 proof that needs injectivity or `cong` is the self-recursive AddZero, which copies its tail and so throws the `S` away.

## Data points for the simplifier

- **What each Eq rule does in E1.** `Eq A a b ≡ ⊤` (with `refl : ⊤`) closes every Z arm. [Eq ×] and `⊤ ∧` are load-bearing only in the two cross proofs, where the goal and the IH have different shapes (`Nat` vs `Unit × Nat`). In AddMZero's S arm and AddZero's S arm, IH and goal are identical before any Eq rule fires.
- **[Close]'s Unit row earns its place only through the cross proof.** Without it, a Unit call returns `U(v) := ⌈let c₁ = v; AddM(&c₁, Z)⌉`, and v1 has no rule equating two Unit values. AddMZero still checks: the Z arm's `U(Z)` runs to `()`, and in the S arm the goal's and the IH's Unit components are both `U(σ')`. But `AddZero x := AddMZero(&x)` fails, because the IH is `Eq Unit U(σ) () ∧ Eq Nat N(σ,Z) σ` while the goal is `Eq Nat N(σ,Z) σ`.
- **Injectivity (dropped by D16) is needed by no E1 proof** once AddZero goes through AddMZero (§E1.5). The self-recursive AddZero needs `congS` because it copies its tail and loses the `S`.

## Findings in detail

Format: (a) where in RULES.md, (b) what I assumed, (c) the simplest fix, (d) the decision it bears on.

**G1. [Call-type] does not say "after the arguments".**
(a) §5 [Call-type]: "At Ω, the type of `f(ā)` … is `B` evaluated at Ω with each `xᵢ` bound to `aᵢ`'s value". [Def]: "The goal is the [Call-type] of that call".
(b) Assumed Ω means the call point: the state after the arguments are evaluated, the same one [Close] restores to.
(c) Read literally, Ω is the state before the arguments run. A borrow argument's loan is then missing from Ω, the borrowed content appears twice (once in the place, once in the argument), and the footprint loses the owner. Concretely:
```
⊢ fix AddMOne (x : &Nat) : Id Unit (AddM(x, S Z)) () := refl             // [Def], literal reading
  generic caller Ω = c₀ ↦ σ; the argument &c₀ has value borrow₀ σ
  B at Ω (not at c₀ ↦ loan₀) with x̂ ↦ borrow₀ σ
    owners(0) = ∅                                                         // loan₀ occurs nowhere in Ω
    W = ∅, so the pair is just Unit
    ⟦AddM(x̂, S Z)⟧ = ()                                                   // move; stuck; [Close] Unit row: (); loan₀ := N(σ, S Z) substituted into nothing
    ⟦()⟧ = ()
    goal ≡ Eq Unit () () ≡ ⊤
  refl : ⊤ ✓                                                              // accepted: "adding 1 in place has no effect"
```
AddMZero's own goal becomes `⊤` the same way, and so does its IH. I found no closed proof of `⊥`, because every call site computes the same `⊤`. But every effect statement about a borrow parameter is vacuous, which empties end goal 3. Fix: "`B` evaluated at the call point (the state after all arguments are evaluated, which [Close] also restores to), with `x̄` bound in a fresh frame. `B`'s names are its parameters and its captured values; Ω contributes only the loan structure."
(d) Wording only: D12 and D13 stand.

**G2. P5 must not erase a Prop call's arguments.**
(a) §0 P5 "A call whose result type is a proposition is erased at runtime, so the machine does not run it either"; §1 "Prop … is erased at runtime"; §3 [Call] "If `B` is a proposition, do not run `b`: return `⋆`".
(b) [Call] is stated on argument values `w̄`, so the checker evaluates the arguments. Assumed the runtime does the same. `⋆` is not in §2's value grammar; assumed it is a new value.
(c) If the runtime erases the whole call, arguments included (as Lean does, where arguments are pure):
```
⊢ fix Lemma (u : Unit) : ⊤ := refl                                        // [Def]: goal ⊤, refl : ⊤
ε ⊢ refl : Id Nat (let n = Z; Lemma(AddM(&n, S Z)); n) (S Z)
  W = ∅                                                                   // n is bound inside the term, not a free place
  ⟨ε, let n = Z; Lemma(AddM(&n, S Z)); n⟩
  ⟨n ↦ Z, Lemma(AddM(&n, S Z)); n⟩                                        // [Let]
  ⟨n ↦ loan₀, Lemma(AddM(borrow₀ Z, S Z)); n⟩                             // [Borrow]
  ⟨n ↦ loan₀ ‖ x₁ ↦ borrow₀ Z, y₁ ↦ S Z, match *x₁ {…}⟩                   // [Call] AddM (Unit is not a Prop): push, run
  ⟨n ↦ loan₀ ‖ x₁ ↦ borrow₀ (S Z), y₁ ↦ S Z, ()⟩                          // [Match] Z arm; [Read]; [Assign]
  ⟨n ↦ S Z, Lemma(()); n⟩                                                 // [Call] pop: [Drop] x₁: [End 0]
  ⟨n ↦ S Z, ⋆; n⟩                                                         // [Call] Lemma's result type ⊤ is a Prop: not run
  ⟨ε, S Z⟩                                                                // [Let]; [Read] n; [Drop] n
  ⟦S Z⟧ = S Z;  Id … ≡ Eq Nat (S Z) (S Z) ≡ ⊤;  refl ✓
```
The compiled program erases the proof `Lemma(AddM(&n, S Z))` whole and returns `Z`. That is a checker/runtime disagreement (adequacy), not `⊥`. Fix: "a Prop call's body and result are erased; its arguments are evaluated as usual, at runtime as in the machine." The alternative, forbidding writes in Prop-call arguments, is an extra check. Add `⋆` to §2.
(d) D14: this completes it.

**G3. J cannot read endpoints off a normalised type.**
(a) §1 `J(A, P, h, t)`; §4 "J / transport and cong as in CIC"; §3 "Values are kept in normal form"; §4 `Eq A a b ≡ ⊤ when a ≡ b`.
(b) J reads `a`, `b` off `h`'s type when that type is a stuck `Eq` (true in congS's [Def], §E1.4).
(c) Once a split refines the type of `h : Eq Nat a Z` with `a := Z`, the stored type is `⊤`, and `J(Nat, P, h, t)` has no endpoints from which to compute `P(b)`. Checking it against a goal would mean solving `P(?a) ≡ goal`, which is higher-order matching. Such a J can always be replaced by `t` (when `a ≡ b`, `t : P(a) ≡ P(b)`), so this is a completeness wart, not a soundness issue. Fix: `J(A, a, b, P, h, t)`, with the endpoints written.
(d) D16: the reflexivity rule is what erases the endpoints. The cost is one argument.

**G4. `cong` is not in v1.**
(a) §7 "`AddZero`'s S arm is `cong S (AddZero(p))`"; §1 has no `cong`, calls are saturated `t(u₁,…)`, `S t` is a constructor form rather than a function value, and there are no implicit arguments.
(b) Defined `congS` from J with explicit endpoints (§E1.4). The call site must then restate the IH's left side: `congS(Add(p, 0), p, AddZero(p))`.
(c) Fix, preferred: make §7's AddZero `S p => AddMZero(&p)` (or `AddZero x := AddMZero(&x)`), which needs no helper, no `cong` and no Nat rule (§E1.5), and says the paper's point: the borrow structure does the congruence even for a pure statement. Otherwise keep the direct proof and list `congS` among the example definitions. In either case, remove "cong as in CIC" from §4, since `cong` is a definition, not a rule.
(d) D16: supports it.

**G5. [Def] never pops.** (a) §5 [Def] "The body runs in a pushed frame". (b) Assumed the frame is popped with [Drop] afterwards, as in [Call]. That pop is where `x`'s borrow ends into `c₀` and where [Drop]'s "loan in a dropped owned value" error catches a body that returns while one of its locals is still borrowed. (c) Fix: "push a frame, run the body, pop it ([Drop]), as [Call] does."

**G6. [Rec]'s "recursive position" is not designated.** (a) §5 [Rec] "in the recursive position". (b) Assumed position 1 for AddM (position 2 is `y`, which is passed unchanged). (c) Fix: "in some position, the same for every recursive call of the definition" (the checker may search for it, as Lean does), or annotate `fix`. Either way, one clause.

**G7. [Seal]'s "head call" is not defined.** (a) §3 [Seal] "with the *head call of t* not eligible for [Close]". (b) Every sealed program [Close] builds has the shape `L; C; K` (or `L; C`), and the head call is `C`. Syntactically the head of `let c₁ = σ; AddM(&c₁, Z); c₁` is `let`, not a call. (c) Fix: "the call `C` of the sealed program (every sealed program is `L; C` or `L; C; K`)". Stuck blocks are sealed the same way, with the anonymous function as `C`.

**G8. "If B is a proposition" should read "if B : Prop".** (a) §3 [Call], §0 P5. (b) `congS`'s motive `P : Π(y:Nat). Prop` has result type `Prop`, which is a sort, not a proposition, so `P` runs. That is the right behaviour, and the reading I assumed. A reader who takes "B is Prop" literally stops P from running and breaks J. (c) Fix: "if `B`'s type is `Prop`".

**G9. Typing of the primitive forms (round-1 F9) is still missing, and v1 leans on it more.** (a) §5 says "Typing is the machine on symbolic inputs, plus case splitting" and gives [Call-type], [Def], [Split], [Rec]. (b) Assumed, as in round 1:
- a place's type is read off Ω (`x : &T` gives `*x : T`; `p : Nat` gives `p.1 : Nat`);
- `&p : &T` when `p : T`; `p := t : Unit` when both are `T`;
- `Z : Nat`, `S t : Nat`, `() : Unit`; `t; u` has `u`'s type; `refl : ⊤`;
- J as in G3;
- a type is evaluated by evaluating its term arguments and then applying §4.

v1 adds two needs: "each `aᵢ` must have type `Aᵢ`" needs the types of arbitrary argument terms (`&(*x).1`, `*x`, `Add(p, 0)`), and in a dependent parameter list each `Aᵢ` must be evaluated with `x₁ … xᵢ₋₁` already bound (congS's `h : Eq Nat a b`). (c) Fix: a six-line table in §5, plus "each `Aᵢ` is evaluated with the earlier parameters bound".

**G10. Renaming (round-1 F7) disappears if `cᵢ` are fixed names.** (a) §0 P1 "same normal form"; §3 [Close] `L := let cᵢ = uᵢ`. (b) Read `cᵢ` as the fixed name for position `i`. Sealed programs are closed, so a fixed name cannot capture anything. With that reading, the goal's `N(σ',Z)` (made inside S2's [Seal] run) and the IH's (made in run (c)) are syntactically identical, and no renaming is needed. (c) Fix: one sentence in [Close]: "`cᵢ` is a fixed name for position `i`". (Returned-borrow holes `loan_k` in E2 still need a word, since `k` is fresh per run; not checked here.)
