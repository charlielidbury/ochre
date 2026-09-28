# Deriver report: E5, dependent types flowing through mutation (RULES v1.3)

**Verdict:** E5 works under v1.3 with no new rule and no new syntax. A proof built from a snapshot of `*x` with the *pure* `Add` is accepted where the callee demands a proof about the *current, mutated* `*x`, because the in-place `AddM` and the pure `Add` close off into the same sealed program. Inside `SubM`, the precondition survives `*x := p`, and the theorem about the whole program checks. I changed the suggested shape: `SubM` subtracts the old value, and the theorem is "`AddSub` sets `*x` to `y`". The literal shape (`AddM` then subtract `y`) needs arithmetic lemmas and a transport inside a sealed program (see "Why this shape").
**Most important finding:** Q1. [Def] binds a proof parameter to an abstract `σh`, while every other proof value is `⋆`. Sealed programs embed their proof arguments, so two runs that differ only in which proof they passed do not convert, although Prop is proof-irrelevant. Example: `refl : Id Unit (SubM(x, y, h)) (let h2 = LeId(y, *x, h); SubM(x, y, h2))` is rejected. Fix: [Def] passes `⋆` for a Prop-typed parameter. E5 itself avoids the bug.
**RULES.md must change:** Q1 (one clause). `False` need not be added (Q2): `Eq Nat Z (S Z)` is already an empty proposition no rule reduces, and E5 never eliminates it. Wording: a sealed program of sort Prop is a type (Q3); [Def]'s parameter types are evaluated in order and stored where [Split] refines them (Q4); J's motive sort (Q2).
**Confidence:** high on the derivations and on Q1; medium on Q6 (the ergonomics of proof arguments that read `*x`), which I derived only in outline.
**Not checked:** the "identity" variant with top-adding (sketched, not derived); ex falso into a `Type` (not needed: every `Type`-sorted type of the core is inhabited, so dead arms return a default); stuck blocks; metatheory.

## Final E5 code

```
Le(a : Nat, b : Nat) : Prop by a :=
  match a { Z => ⊤ | S a' => match b { Z => Eq Nat Z (S Z) | S b' => Le(a', b') } }     // "False" is Eq Nat Z (S Z)

LeAdd(n : Nat, m : Nat) : Le(n, Add(n, m)) by n :=                                        // a lemma about the PURE Add
  match n { Z => refl | S n' => LeAdd(n', m) }

SubM(x : &Nat, y : Nat, h : Le(y, *x)) : Unit by y :=                                     // peel y successors off the top of *x
  match y { Z => () | S q => match *x { Z => () | S p => *x := p; SubM(x, q, h) } }     // Z arm is dead: h : Eq Nat Z (S Z) there

AddSub(x : &Nat, y : Nat) : Unit :=
  let old = *x; AddM(&*x, y); SubM(x, old, LeAdd(old, y))                                 // proof from the snapshot, about the mutated *x

AddSubId(x : &Nat, y : Nat) : Id Unit (AddSub(x, y)) (*x := y) by x :=
  match *x { Z => refl | S p => let c = p; AddSubId(&c, y) }                              // IH on a COPY of the tail (Q5)
```
`AddM` and `Add` are §7's. Rejected, as they should be (§E5.6): the stale proof `…; AddM(&*x, y); *x := Z; SubM(x, old, LeAdd(old, y))`, the wrong subtrahend `SubM(x, S old, LeAdd(old, y))`, and the reborrow IH `S p => AddSubId(&p, y)`.

## Findings (one line each; details at the end)

- **Q1** §5 [Def] "the call `f(ā)` with `aᵢ = &cᵢ` or `σᵢ`": a Prop-typed parameter gets an abstract `σh`, but proof calls return `⋆`. Sealed programs keep proof arguments, so the same program run with `h` and with `LeId(…, h)` does not convert. Fix: pass `⋆` for Prop-typed parameters (definitional proof irrelevance at the value level).
- **Q2** `False` (lead's request): not needed as a primitive; `Eq Nat Z (S Z)` is a closed, irreducible, empty proposition (D16 removed the only rule that could touch it). E5 never eliminates it. Ex falso into Prop is derivable: `J(Nat, Z, S Z, P, h, refl)` with a Prop-valued motive `P(n) := match n { Z => ⊤ | S _ => G }`. §4 does not say whether J's motive may be `Type`-valued; say Prop only (E5 needs nothing more).
- **Q3** §2/§5: nothing says a neutral of sort Prop (here `⌈Le(σy, σx)⌉`) is a type that a variable can have. Every recursive precondition produces one. One sentence.
- **Q4** §5 [Def]: the generic call's parameter types must be evaluated left to right with the earlier parameters bound (said only in [Call-type]) and stored in the pushed frame, where [Split] refines them. SubM depends on both: `h`'s stored type is refined twice. One sentence.
- **Q5** (data, not a defect) `AddSubId`'s IH must be about a copy of the tail (`let c = p; AddSubId(&c, y)`). The reborrow IH `AddSubId(&p, y)` yields `Eq Nat (S K) (S σy)` against the goal `Eq Nat K σy`, which needs the injectivity D16 dropped. Borrowing the field supplies the congruence and copying it withholds it; the programmer picks one. D25 shows the borrow case, this shows the copy case.
- **Q6** (ergonomics) a proof argument that reads `*x` after `x` has been moved into an earlier argument is an error, even though the proof runs on a private copy. `SubM(&*x, y, P(*x))` works instead, because the proof's private copy ends the reborrow only in the copy, much like Rust's two-phase borrows. Worth a sentence in the paper, not a rule.
- **Q7** (positive) large elimination into Prop needs nothing new. `Le` is an ordinary `fix` with codomain `Prop`. Its stuck calls close off through [Close]'s borrow-free row into sealed *types*, refinement re-normalises them, and [Call] runs `Le` (its codomain `Prop` is a sort, not a proposition).

## What E5 demonstrates

Three conversions, each forced by mutation:
1. **Across a call, snapshot to current state (§E5.4).** `LeAdd(old, y) : ⌈Le(σ, N(σ,σy))⌉`, where `N(σ,σy)` comes from the pure `Add(old, y)`. SubM demands `Le(old, *x)` at a moment when `*x` holds `N(σ,σy)` because the in-place `AddM(&*x, y)` put it there. Both are `⌈let c₁ = σ; AddM(&c₁, σy); c₁⌉` because [Close] builds the same canonical program whether the borrowed place is a caller's field or `Add`'s local. This is end goal 2 at work: a lemma about the pure function certifies the state left by the in-place one.
2. **Inside a function, old state to new state (§E5.3).** In SubM's recursive arm, `h`'s type was formed about the entry `*x` and refined to `Le(S σq, S σp) ≡ ⌈Le(σq, σp)⌉`. After `*x := p`, the recursive call demands `Le(q, *x)` about the new `*x = σp`, which is `⌈Le(σq, σp)⌉`. The snapshot and the requirement meet because the machine knows the new content is the old content's tail.
3. **A theorem about the whole program (§E5.5),** by structural recursion on `*x`, with every precondition discharged as above.

## Why this shape, not the suggested one

The suggested `AddSub(x, y) := AddM(x, y); SubM(x, y, …)` with `AddSubId : Id Unit (AddSub(x, y)) ()` computes `(n + m) − m`, where `+` (AddM) appends `m` at the bottom and `−` (SubM) peels from the top. Symbolically, the S-case of any recursion leaves `SubM` peeling `N(σ', S σq)` by `σq` where the IH peels `N(σ', S σq)` by `S σq`. Connecting them needs `Add(n, S m) = S Add(n, m)` (a separate inductive lemma about AddM) and then a J-transport *inside* a sealed SubM program. That is two extra lemmas and a motive over sealed programs, which is heavier than E5 is meant to be. Two shapes line up structurally:
- **(A, derived here)** subtract the *old* value: `(n + m) − n = m`. SubM peels exactly the `S`s that AddM left above `m`.
- **(B, sketched only)** add on *top* with a recurse-then-wrap `AddTopM(x, y) by y := match y { Z => () | S q => AddTopM(&*x, q); *x := S *x }`, then subtract `y`. The theorem is then the identity `Id Unit (AddTopSub(x, y)) ()`, proved by recursion on `y` with the IH on `&*x`. I checked the key conversions (`AddTop(σn, S σq) = S T(σn, σq)`, `K'(σ, S σq) = K'(σ, σq)`) but did not write the derivation out.

(A) reuses E1's `AddM`, `Add` and sealed program `N`, and it uses the snapshot twice, as the subtrahend and in the proof. So it is the main example.

## Conventions

As in deriver-e1-v1: Ω oldest frame first, `‖` between frames; one machine step per line, rule after `//`; callee frames subscripted by depth; a parameter bound by [Call-type] is hatted (`x̂`). [Call] evaluates arguments into temporaries `t₁, t₂, …`. I show a temporary only when it holds a borrow; otherwise I show its value. [Access] is written only when it ends something. Abbreviations (all closed, with [Close]'s fixed names):

```
N(v, w)  := ⌈let c₁ = v; AddM(&c₁, w); c₁⌉                  : Nat   final content of a place given to a stuck AddM
K(v, w)  := ⌈let c₁ = N(v, w); SubM(&c₁, v, ⋆); c₁⌉          : Nat   final content of the place AddSub works on
Λ(a, b)  := ⌈Le(a, b)⌉                                       : Prop  a stuck Le (a sealed TYPE, Q3)
False    := Eq Nat Z (S Z)                                           irreducible: Z ≢ S Z, and v1.3 has no disjointness rule
```

## E5.0 Sealed-program lemmas

**L0–L2 (AddM).** These are deriver-e1-v1 S0–S2 with `y` general: `nf N(σ, w) = N(σ, w)` (head-call guard); `nf N(Z, w) = w`; `nf N(S σ', w) = S N(σ', w)`. The runs are the same line for line, with `w` for `Z`. L1 in full, since round 2 only did `w = Z`:

```
nf N(Z, w) = w                                                   // [Seal]
  ⟨ε, let c₁ = Z; AddM(&c₁, w); c₁⟩
  ⟨c₁ ↦ loan₁, AddM(borrow₁ Z, w); c₁⟩                           // [Let]; [Borrow]; call point of the head call
  ⟨c₁ ↦ loan₁ ‖ x₁ ↦ borrow₁ Z, y₁ ↦ w, match *x₁ {…}⟩            // [Call] push, run
  ⟨c₁ ↦ loan₁ ‖ x₁ ↦ borrow₁ w, y₁ ↦ w, ()⟩                       // [Match] Z arm; [Read] y₁ copy; [Assign]
  ⟨c₁ ↦ w, (); c₁⟩ → ⟨c₁ ↦ w, w⟩ → ⟨ε, w⟩                        // [Call] pop: [End 1]; [Let]; [Read] c₁; [Drop] c₁
```

**Le1–Le4 (the precondition).** Each is a run of `Le` from `ε`: a [Seal] run when the call is sealed, a plain [Call] otherwise.

```
Le(Z, b) ⇓ ⊤                                                     // Le1, any b
  ⟨a₁ ↦ Z, b₁ ↦ b, match a₁ {…}⟩ → ⊤                             // [Call] (codomain Prop is a sort, not a proposition: runs); [Match] Z arm
Le(S a, Z) ⇓ False                                               // Le2
  ⟨a₁ ↦ S a, b₁ ↦ Z, match a₁ {…}⟩ → match b₁ {…} → Eq Nat Z (S Z)   // [Match] S arm; [Match] Z arm
Le(σ, b) ⇓ Λ(σ, b)                                               // Le3: stuck on a; [Close], borrow-free row, L empty: ⌈Le(σ, b)⌉
Le(S a, n) ⇓ Λ(S a, n)       for a neutral n                     // Le3': [Match] a: S arm; [Match] b: neutral, stuck; [Close]
Le(S σa, S b) ⇓ Λ(σa, b)                                         // Le4
  ⟨a₁ ↦ S σa, b₁ ↦ S b, match a₁ {…}⟩
  ⟨…, match b₁ {…}⟩                                              // [Match] S arm, a' := a₁.1
  ⟨…, Le(a', b')⟩                                                // [Match] S arm, b' := b₁.1
  ⟨… ‖ a₂ ↦ σa, b₂ ↦ b, match a₂ {…}⟩                            // [Read] a', b' (copies); [Call] push
  stuck; [Close] → Λ(σa, b)                                      // the inner call is not the head call, so it may close even inside a [Seal] run
  the outer body completes with Λ(σa, b)                         // [Call] pop
```
A sealed `Λ(a, b)` whose head call gets stuck in its own body is normal (head-call guard). Refining a variable inside it re-runs it by Le1–Le4.

**K1–K3 (SubM after AddM).**

```
nf K(σ, w) = K(σ, w)                                             // K1: head call SubM(&c₁, σ, ⋆) matches y = σ: stuck in its own body
nf K(Z, w) = w                                                   // K2
  ⟨ε, let c₁ = N(Z, w); SubM(&c₁, Z, ⋆); c₁⟩
  ⟨ε, let c₁ = w; SubM(&c₁, Z, ⋆); c₁⟩                           // embedded value re-normalised first: L1
  ⟨c₁ ↦ loan₁, SubM(borrow₁ w, Z, ⋆); c₁⟩                        // [Let]; [Borrow]
  ⟨c₁ ↦ loan₁ ‖ x₁ ↦ borrow₁ w, y₁ ↦ Z, h₁ ↦ ⋆, match y₁ {…}⟩     // [Call] push (SubM's codomain is Unit: runs)
  ⟨c₁ ↦ loan₁ ‖ …, ()⟩                                           // [Match] Z arm
  ⟨c₁ ↦ w, w⟩ → ⟨ε, w⟩                                           // [Call] pop: [End 1]; [Read]; [Drop]
nf K(S σ', w) = K(σ', w)                                         // K3
  ⟨ε, let c₁ = S N(σ', w); SubM(&c₁, S σ', ⋆); c₁⟩               // L2 on the embedded value
  ⟨c₁ ↦ loan₁, SubM(borrow₁ (S N(σ',w)), S σ', ⋆); c₁⟩           // [Let]; [Borrow]; call point of the head call C
  ⟨… ‖ x₁ ↦ borrow₁ (S N(σ',w)), y₁ ↦ S σ', h₁ ↦ ⋆, match y₁ {…}⟩ // [Call] push C's frame (C not eligible for [Close])
  ⟨…, match *x₁ {…}⟩                                             // [Match] S arm, q := y₁.1
  ⟨…, *x₁ := p; SubM(x₁, q, h₁)⟩                                 // [Match] S arm, p := (*x₁).1
  ⟨c₁ ↦ loan₁ ‖ x₁ ↦ borrow₁ N(σ',w), …, SubM(x₁, q, h₁)⟩        // [Read] p copies N(σ',w); [Assign] [Drop] old S N(σ',w)
  ⟨c₁ ↦ loan₁ ‖ x₁ ↦ ⊥, t₁ ↦ borrow₁ N(σ',w), …, SubM(t₁, σ', ⋆)⟩ // [Read] x₁ moves; q copies σ'; h₁ copies ⋆
  ⟨… ‖ x₂ ↦ borrow₁ N(σ',w), y₂ ↦ σ', h₂ ↦ ⋆, match y₂ {…}⟩       // [Call] push the inner frame
  stuck                                                          // [Match] σ': in the INNER call's body, which is eligible
  ⟨c₁ ↦ K(σ', w) ‖ x₁ ↦ ⊥, …, ()⟩                                // [Close] I = {1}, u₁ = N(σ',w), L = let c₁ = N(σ',w), C' = SubM(&c₁, σ', ⋆); Unit row; loan₁ := K(σ',w)
  ⟨c₁ ↦ K(σ', w), K(σ', w)⟩ → ⟨ε, K(σ', w)⟩                      // C's body completes; [Call] pop; [Read] c₁; [Drop]
```

## E5.1 Le (large elimination into Prop)

```
⊢ Le : Π(a : Nat, b : Nat). Prop                                 // [Def]
  generic caller ε; call Le(σa, σb); goal: Prop                  // [Call-type]: the codomain is the sort Prop
  frame a ↦ σa, b ↦ σb
  match a                                                        // [Split] head σa
  arm Z (σa := Z):     ⊤ : Prop ✓
  arm S (σa := S σa'), a' := a.1:
    match b                                                      // [Split] head σb (a tail match inside the arm)
    arm Z (σb := Z):   Eq Nat Z (S Z) : Prop ✓                    // Z, S Z : Nat
    arm S (σb := S σb'), b' := b.1:
      Le(a', b') ⇓ Λ(σa', σb') : Prop ✓                           // [Read] copies; [Rec] by a: σa' is a strict subterm of S σa' ✓; [Call-type]: Prop; [Call] runs: stuck, [Close]
  pops: owned Nats, no loans ✓
```

## E5.2 LeAdd (a lemma about the pure Add)

```
⊢ LeAdd : Π(n : Nat, m : Nat). Le(n, Add(n, m))                   // [Def]
  generic caller ε; call LeAdd(σn, σm)
  G₀ := Le(n̂, Add(n̂, m̂)) at ε ‖ n̂ ↦ σn, m̂ ↦ σm, on a private copy // [Call-type]
    ⟨…, Add(σn, σm)⟩ ⇓ N(σn, σm)                                  // [Call] Add: AddM(&x₁, y₁) closes off, loan := N(σn,σm); [Read] x₁ (deriver-e1-v1 run (e), y general)
    ⟨…, Le(σn, N(σn,σm))⟩ ⇓ Λ(σn, N(σn,σm))                       // Le3
  G₀ = Λ(σn, N(σn, σm))
  frame n ↦ σn, m ↦ σm; match n                                  // [Split] head σn
  arm Z (σn := Z):
    G_Z = Λ(Z, N(Z, σm))  re-normalised:                          // [Split] refines the goal; [Seal] re-normalises
          N(Z, σm) = σm                                           // L1
          Le(Z, σm) ⇓ ⊤                                           // Le1: the head call now completes
    refl : ⊤ ✓
  arm S (σn := S σn'), n' := n.1:
    G_S = Λ(S σn', N(S σn', σm))  re-normalised:
          N(S σn', σm) = S N(σn', σm)                             // L2
          Le(S σn', S N(σn', σm)) ⇓ Λ(σn', N(σn', σm))             // Le4
    LeAdd(n', m):                                                 // a proof: typed on a private copy, value ⋆ (P2)
      args: σn' (copy of n.1), σm                                  // [Read]
      [Rec] by n: σn' is a strict subterm of the entry value σn = S σn' ✓
      type: Le(n̂, Add(n̂, m̂)) at … ‖ n̂ ↦ σn', m̂ ↦ σm ⇓ Λ(σn', N(σn', σm))   // [Call-type]: as for G₀, with σn'
    Λ(σn', N(σn', σm)) ≡ G_S ✓                                    // identical
```

## E5.3 SubM (the precondition survives `*x := p`)

```
⊢ SubM : Π(x : &Nat, y : Nat, h : Le(y, *x)). Unit               // [Def]
  generic caller c₀ ↦ σx; call SubM(&c₀, σy, σh)                  // Q1: σh; with the fix, ⋆
  ⟨c₀ ↦ loan₀, t₁ ↦ borrow₀ σx⟩                                   // [Borrow]; call point
  parameter types, left to right, earlier ones bound (Q4):
    x : &Nat;  y : Nat;  h : Le(ŷ, *x̂) with x̂ ↦ borrow₀ σx, ŷ ↦ σy
      ⟨…, Le(σy, *x̂)⟩ → ⟨…, Le(σy, σx)⟩ ⇓ Λ(σy, σx)                // [Read] *x̂ through the borrow: copy σx; Le3
  goal: Unit
  Ω₀ := c₀ ↦ loan₀ ‖ x ↦ borrow₀ σx, y ↦ σy, h : Λ(σy, σx) ↦ σh   // body frame; h's type stored here (Q4)
  entry value of y for [Rec]: σy
  match y                                                         // [Split] head σy
  arm Z (σy := Z):
    h : Λ(Z, σx) re-normalised ⇓ ⊤                                 // Le1
    () : Unit ✓;  pop: [End 0], c₀ ↦ σx
  arm S (σy := S σq), q := y.1:
    h : Λ(S σq, σx) re-normalised ⇓ Λ(S σq, σx)                     // Le3': stuck on b = σx, still sealed
    match *x                                                      // [Split] head σx (a tail match)
    arm Z (σx := Z):
      h : Λ(S σq, Z) ⇓ False                                      // Le2: this arm is dead
      () : Unit ✓                                                  // Unit is inhabited: no elimination of False needed (Q2)
      pop: [End 0], c₀ ↦ Z
    arm S (σx := S σp), p := (*x).1:
      Ω_S = c₀ ↦ loan₀ ‖ x ↦ borrow₀ (S σp), y ↦ S σq, h ↦ σh
      h : Λ(S σq, S σp) ⇓ Λ(σq, σp)                                // Le4: the snapshot type, about the OLD *x = S σp
      ⟨Ω_S, *x := p; SubM(x, q, h)⟩
      ⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ σp, …, SubM(x, q, h)⟩             // [Read] p = (*x).1 copies σp; [Assign] [Drop] old S σp; *x ↦ σp
      h's stored type is unchanged: Λ(σq, σp)                      // P2: a formed type is a closed statement
      ⟨c₀ ↦ loan₀ ‖ x ↦ ⊥, t₁ ↦ borrow₀ σp, …, SubM(t₁, σq, σh)⟩   // [Read] x moves into t₁; q copies σq; h copies σh; call point
      [Rec] by y: σq is a strict subterm of the entry value σy = S σq ✓
      [Call-type] frame x̂ ↦ borrow₀ σp, ŷ ↦ σq, ĥ ↦ σh:
        A₁ = &Nat ✓   A₂ = Nat ✓
        A₃ = Le(ŷ, *x̂) ⇓ Le(σq, σp) ⇓ Λ(σq, σp)                    // [Read] *x̂ copies the NEW content σp; Le3
        argument 3 has type Λ(σq, σp) ≡ A₃ ✓                       // conversion 2: the old-state proof meets the new-state requirement
        type of the call: Unit
      ⟨… ‖ x₁ ↦ borrow₀ σp, y₁ ↦ σq, h₁ ↦ σh, match y₁ {…}⟩         // [Call] push (codomain Unit: runs)
      stuck                                                        // [Match] σq
      ⟨c₀ ↦ ⌈let c₁ = σp; SubM(&c₁, σq, σh); c₁⌉ ‖ x ↦ ⊥, …, ()⟩   // [Close] Unit row; loan₀ := the sealed program (it embeds σh, Q1)
      Unit ✓;  pop: x is ⊥, y, h owned ✓
```

## E5.4 AddSub (a proof about the snapshot, accepted about the mutated state)

```
⊢ AddSub : Π(x : &Nat, y : Nat). Unit                              // [Def]; non-recursive
  generic caller c₀ ↦ σ; call AddSub(&c₀, σy); goal Unit
  Ω₀ := c₀ ↦ loan₀ ‖ x ↦ borrow₀ σ, y ↦ σy
  ⟨Ω₀, let old = *x; AddM(&*x, y); SubM(x, old, LeAdd(old, y))⟩
  ⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ σ, y ↦ σy, old ↦ σ, AddM(&*x, y); …⟩  // [Let] [Read] *x through the borrow: copy σ (the snapshot)
  ⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ loan₁, …, t₁ ↦ borrow₁ σ, AddM(t₁, σy); …⟩   // [Borrow] &*x, ℓ = 1; [Read] y; call point
  type: Unit; args &Nat, Nat ✓                                    // [Call-type]
  ⟨… ‖ x₁ ↦ borrow₁ σ, y₁ ↦ σy, match *x₁ {…}⟩                     // [Call] push (codomain Unit: runs)
  stuck                                                           // [Match] σ
  ⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ N(σ,σy), y ↦ σy, old ↦ σ, (); SubM(…)⟩ // [Close] L = let c₁ = σ, C = AddM(&c₁, σy); Unit row; loan₁ := N(σ,σy)
                                                                  // *x has been MUTATED: it now holds a sealed program on symbolic input
  SubM(x, old, LeAdd(old, y)):
    ⟨c₀ ↦ loan₀ ‖ x ↦ ⊥, t₁ ↦ borrow₀ N(σ,σy), …⟩                  // [Read] x: a borrow, moved into t₁
    t₂ ↦ σ                                                        // [Read] old copy
    LeAdd(old, y): a proof, run and typed on a private copy; t₃ ↦ ⋆  // P2, [Call]
      its type: Le(n̂, Add(n̂, m̂)) at … ‖ n̂ ↦ σ, m̂ ↦ σy               // [Call-type] (as E5.2's G₀, with σ, σy)
        Add(σ, σy) ⇓ N(σ, σy)                                     // the PURE Add on the snapshot: [Close] in Add's local x₁
        Le(σ, N(σ,σy)) ⇓ Λ(σ, N(σ,σy))                            // Le3
    call point: SubM(t₁, σ, ⋆)
    [Call-type] frame x̂ ↦ borrow₀ N(σ,σy), ŷ ↦ σ, ĥ ↦ ⋆:
      A₁ = &Nat ✓   A₂ = Nat ✓
      A₃ = Le(ŷ, *x̂) ⇓ Le(σ, N(σ,σy)) ⇓ Λ(σ, N(σ,σy))            // [Read] *x̂ copies the CURRENT content N(σ,σy); Le3
      argument 3 : Λ(σ, N(σ,σy)) ≡ A₃ ✓                            // conversion 1: the pure Add on the snapshot = the in-place AddM on *x
      type of the call: Unit
    ⟨… ‖ x₂ ↦ borrow₀ N(σ,σy), y₂ ↦ σ, h₂ ↦ ⋆, match y₂ {…}⟩        // [Call] push
    stuck                                                         // [Match] σ
    ⟨c₀ ↦ K(σ, σy) ‖ x ↦ ⊥, …, ()⟩                                  // [Close] L = let c₁ = N(σ,σy), C = SubM(&c₁, σ, ⋆); Unit row; loan₀ := K(σ,σy)
  Unit ✓;  pop: x is ⊥; y, old owned, loan-free ✓
```

Both sides of conversion 1 are literally `⌈let c₁ = σ; AddM(&c₁, σy); c₁⌉`. On the left, [Close] ran on `Add`'s local `x₁ ↦ σ`, borrowed as `&x₁`. On the right, it ran on `AddSub`'s reborrow `&*x` of the caller's place. [Close] writes both as the same canonical program because it abstracts the borrowed place into a fresh owned `c₁`.

## E5.5 AddSubId (the theorem)

```
⊢ AddSubId : Π(x : &Nat, y : Nat). Id Unit (AddSub(x, y)) (*x := y)   // [Def]
  generic caller c₀ ↦ σ; call point c₀ ↦ loan₀, x̂ ↦ borrow₀ σ, ŷ ↦ σy
  G₀:  W(AddSub(x̂, ŷ), *x̂ := ŷ) = owners(0) = {c₀}                  // x̂ is borrow-typed, and *x̂ is left of :=; loan₀ occurs in the owned c₀
    ⟦AddSub(x̂, ŷ)⟧ = ((), K(σ, σy))                                // [Read] x̂ moves; [Call] AddSub runs exactly as in E5.4 with c₀ the owner; nothing left to end
    ⟦*x̂ := ŷ⟧ = ((), σy)                                           // [Assign] x̂ ↦ borrow₀ σy; end every borrow: [End 0], c₀ ↦ σy
    G₀ = Eq (Unit × Nat) ((), K(σ,σy)) ((), σy) ≡ Eq Nat K(σ,σy) σy // [Eq ×]; [Eq ≡⊤] on () ≡ (); [⊤ ∧]; K1: K(σ,σy) is normal, so stuck
  Ω₀ := c₀ ↦ loan₀ ‖ x ↦ borrow₀ σ, y ↦ σy;  entry value of x for [Rec]: σ
  match *x                                                         // [Split] head σ
  arm Z (σ := Z):
    G_Z = Eq Nat K(Z, σy) σy = Eq Nat σy σy ≡ ⊤                     // K2; [Eq ≡⊤]
    refl : ⊤ ✓;  pop: [End 0], c₀ ↦ Z
  arm S (σ := S σ'), p := (*x).1:
    G_S = Eq Nat K(S σ', σy) σy = Eq Nat K(σ', σy) σy               // K3
    ⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ (S σ'), y ↦ σy, c ↦ σ', AddSubId(&c, y)⟩   // [Let] c: [Read] p copies σ'
    AddSubId(&c, y): a proof, typed on a private copy, value ⋆, real environment unchanged   // P2
      private copy: ⟨… c ↦ loan₂, t₁ ↦ borrow₂ σ', …⟩                // [Borrow] &c; [Read] y; call point
      [Rec] by x: the argument's content σ' is a strict subterm of the entry value σ = S σ' ✓
      [Call-type] frame x̂ ↦ borrow₂ σ', ŷ ↦ σy:
        W = owners(2) = {c}                                         // loan₂ occurs in the owned local c
        ⟦AddSub(x̂, ŷ)⟧ = ((), K(σ', σy))                            // as E5.4 with σ' and owner c: c ↦ K(σ',σy)
        ⟦*x̂ := ŷ⟧ = ((), σy)                                        // c ↦ σy
        IH = Eq Nat K(σ', σy) σy                                   // [Eq ×], [Eq ≡⊤], [⊤ ∧]
    IH ≡ G_S ✓                                                     // identical, including the embedded ⋆ and the fixed name c₁
    ⟨c₀ ↦ loan₀ ‖ x ↦ borrow₀ (S σ'), y ↦ σy, ⋆⟩                     // [Let] [Drop] c: σ', no loans
    pop: [End 0], c₀ ↦ S σ'
```

K3 is where the program's behaviour turns into the induction. Refining `σ := S σ'` re-runs the sealed `K`, whose head call now takes one step (SubM peels the `S` that AddM left on top) and closes off into `K(σ', σy)`, which is exactly the IH's program on the copy.

## E5.6 Rejections (the requirement really is about the current state)

**Stale proof.** `AddSubBad(x, y) := let old = *x; AddM(&*x, y); *x := Z; SubM(x, old, LeAdd(old, y))`:
```
after AddM: x ↦ borrow₀ N(σ,σy); after *x := Z: x ↦ borrow₀ Z          // as E5.4; then [Assign]
SubM's call point: x̂ ↦ borrow₀ Z, ŷ ↦ σ, ĥ ↦ ⋆
  A₃ = Le(σ, Z) ⇓ Λ(σ, Z)                                                // Le3: stuck on a = σ
  argument 3 : Λ(σ, N(σ,σy))                                             // unchanged: formed about the snapshot
  Λ(σ, N(σ,σy)) ≢ Λ(σ, Z)  →  "an argument not of the parameter's type"   // rejected (right: old ≤ 0 is false for old > 0)
```
**Wrong subtrahend.** `SubM(x, S old, LeAdd(old, y))`: `A₃ = Le(S σ, N(σ,σy)) ⇓ Λ(S σ, N(σ,σy))` (Le3': `b` is a sealed program), which is not `Λ(σ, N(σ,σy))`. Rejected.

**Reborrow IH (Q5).** `AddSubId`'s S arm written `AddSubId(&p, y)`:
```
call point (private copy): c₀ ↦ loan₀ ‖ x ↦ borrow₀ (S loan₁), y ↦ σy ‖ x̂ ↦ borrow₁ σ', ŷ ↦ σy
W = owners(1) = owners(0) = {c₀}                                          // loan₁ sits inside x's borrow content
⟦AddSub(x̂, ŷ)⟧: loan₁ := K(σ', σy); end borrows: c₀ ↦ S K(σ', σy)        // as E5.4 with σ'
⟦*x̂ := ŷ⟧: x̂ ↦ borrow₁ σy; end borrows: c₀ ↦ S σy
IH = Eq Nat (S K(σ',σy)) (S σy)  ≢  G_S = Eq Nat K(σ',σy) σy               // no injectivity rule since D16: rejected
```
The borrow structure supplies the head `S` on both sides of the IH. That is what made AddMZero bare recursion, and here it is unwanted, because AddSub on `S σ'` is not `S` of AddSub on `σ'`: SubM peels the head `S`. Copying the tail into a fresh owner `c` gives the IH without the context. Both IHs are available and neither needs a rule; the programmer picks the one that matches the goal.

## E5.7 The Q1 counterexample

```
LeId(a : Nat, b : Nat, h : Le(a, b)) : Le(a, b) := h                         // [Def]: goal Λ(σa,σb); h's stored type Λ(σa,σb) ✓
T(x : &Nat, y : Nat, h : Le(y, *x)) : Id Unit (SubM(x, y, h)) (let h2 = LeId(y, *x, h); SubM(x, y, h2)) := refl

⊢ T                                                                         // [Def], current rule: ĥ ↦ σh
  call point: c₀ ↦ loan₀ ‖ x̂ ↦ borrow₀ σ, ŷ ↦ σy, ĥ ↦ σh;  W = owners(0) = {c₀}
  ⟦SubM(x̂, ŷ, ĥ)⟧: args borrow₀ σ, σy, σh; [Match] σy stuck; [Close] → c₀ ↦ ⌈let c₁ = σ; SubM(&c₁, σy, σh); c₁⌉
  ⟦let h2 = LeId(ŷ, *x̂, ĥ); SubM(x̂, ŷ, h2)⟧: LeId(…) is a proof, h2 ↦ ⋆; then as before → c₀ ↦ ⌈let c₁ = σ; SubM(&c₁, σy, ⋆); c₁⌉
  goal ≡ Eq Nat ⌈…σh…⌉ ⌈…⋆…⌉: the sides differ only in the embedded proof, so no rule fires; stuck, not ⊤
  refl : ⊤ is rejected
```
In the model both sides are the same function of `σ, σy` (the proof argument is erased), so the statement is true, and by definitional proof irrelevance it should hold by `refl`. With the fix (`ĥ ↦ ⋆`) both sealed programs are `⌈let c₁ = σ; SubM(&c₁, σy, ⋆); c₁⌉` and `refl` checks. I don't see an alternative proof under the current rule: any recursion re-closes the two SubM calls with `σh` and `⋆` respectively. So this is a completeness failure and a gap between the rules and their stated proof irrelevance, not an unsoundness. The fix makes `⋆` the only proof value anywhere, so sealed programs never differ by a proof.

## E5.8 Q2: `False` and ex falso, without new machinery

```
ExFalso(G : Prop, h : Eq Nat Z (S Z)) : G := J(Nat, Z, S Z, fix P (n : Nat) : Prop := match n { Z => ⊤ | S m => G }, h, refl)

⊢ ExFalso                                                                   // [Def]: G : Prop is a TYPE parameter (σG); h's type has sort Prop, so it is a proof parameter (⋆ under Q1)
  goal: σG                                                                  // [Call-type]
  P := closure of fix P (n : Nat) : Prop := …, capturing G = σG               // P2: a closure over a borrow-free value; its own [Def] splits n: ⊤ : Prop, σG : Prop ✓
  J(Nat, Z, S Z, P, h, refl):                                               // §4: h : Eq A a b and t : P(a) give P(b)
    h : Eq Nat Z (S Z) ✓                                                    // exactly the declared endpoints
    P(Z) ⇓ ⊤ and refl : ⊤ ✓                                                 // [Call] P (codomain Prop is a sort: runs); [Match] Z arm
    P(S Z) ⇓ σG ≡ goal ✓                                                    // [Match] S arm
```
So the empty proposition and its elimination into Prop come for free from `Eq`, the large elimination `Le` already uses, and J. Elimination into a `Type` would need a `Type`-valued motive, and §4 does not say whether J allows one or what J computes to when `h` is `⋆`. E5 never needs it: the core's `Type`-sorted types (`Nat`, `Unit`, pairs, Π over them, `&T` given a borrow in scope) are all inhabited, so a dead arm can return a default value, as SubM's does.

## E5.9 Q6: a proof argument that reads the state an earlier argument borrowed

```
SubM(x, old, P(*x))                                                         // x moved first
  ⟨…, x ↦ ⊥, t₁ ↦ borrow₀ v, …⟩                                             // [Read] x moves
  P(*x) on the private copy: [Access] *x: the path goes through x ↦ ⊥  →  reading ⊥: error
SubM(&*x, old, P(*x))                                                       // reborrow instead
  ⟨…, x ↦ borrow₀ loan_k, t₁ ↦ borrow_k v, …⟩                               // [Borrow] &*x
  P(*x) on the private copy: [Access] *x: loan_k is the head of content(*x): [End k] IN THE COPY; *x = v; P(v) typed
  the real environment still has t₁ ↦ borrow_k v                           // P2: the copy is discarded
  [Call-type]: x̂ ↦ borrow_k v, so A₃ = Le(ŷ, *x̂) reads v, the value P's proof was about ✓
```
A proof argument may thus mention the state that an earlier argument reserved, much like Rust's two-phase borrows (`v.push(v.len())`). This is a consequence of P2, not a new rule. It deserves a sentence in the paper, and the error message for the moved form should suggest the reborrow.

## Findings in detail

Format: (a) where in RULES.md, (b) what I assumed, (c) the simplest fix, (d) the decision it bears on.

**Q1. Proof parameters must be `⋆`, not `σ`.**
(a) §5 [Def] "the call `f(ā)` with `aᵢ = &cᵢ` or `σᵢ`"; §2 "`⋆`: the (irrelevant) value of a proof"; the preamble's "`Prop` has definitional proof irrelevance".
(b) Read literally, a parameter whose type is a proposition gets a fresh `σ` like any other. Proof calls return `⋆` (§3 [Call]), and [Close] copies non-borrow arguments into the sealed program (`aᵢ = wᵢ`), so sealed programs carry proof values.
(c) §E5.7: two runs that differ only in the proof they pass (`σh` vs `⋆`) close off into different sealed programs, and `refl` is rejected for a true, proof-irrelevant equation. Fix, one clause in [Def]: "`aᵢ = ⋆` when `Aᵢ` is a proposition". Then `⋆` is the only proof value, and sealed programs can never differ by a proof. (Alternatively, have nf replace every proof-typed value by `⋆`. That needs types in nf, so it is worse.)
(d) Completes D26 (the erased terms principle): an erased value should be `⋆` everywhere, including at the generic call.

**Q2. `False` is not needed as a primitive; J's motive sort is unstated.**
(a) The lead's brief ("the core has no `False`; add `False : Prop`"); §4 `J(A, a, b, P, h, t) : P(b)`.
(b) Used `Eq Nat Z (S Z)`: closed, irreducible (`Z ≢ S Z`, and D16 removed disjointness), empty in the model. Ex falso into Prop is §E5.8.
(c) Add nothing. If a name is wanted, `False` is an abbreviation. State that J's motive is Prop-valued (`P : Π(y:A). Prop`), which is all E5 and ex falso need. A `Type`-valued motive would force J to compute on an erased `h`, a design question E5 does not raise.
(d) D16: dropping disjointness made `Eq Nat Z (S Z)` an irreducible empty proposition, which is exactly what `False` needs to be. So D16 is not undermined.

**Q3. Neutral types.**
(a) §2 values "`types`", neutrals "`σ | ⌈t⌉`"; §5 typing of variables.
(b) `h : Λ(σy, σx)` where `Λ(σy, σx) = ⌈Le(σy, σx)⌉` is a sealed program of sort Prop. Assumed a neutral whose type is a sort is a type, as `Nat.le n m` is a type in Lean when `n` is a variable.
(c) One sentence in §2: "a neutral whose type is a sort is a type".
(d) None; D4's sealed programs simply reach types for the first time here.

**Q4. [Def]'s parameter types.**
(a) §5 [Def]; §5 [Call-type] "each `aᵢ` must have type `Aᵢ`, evaluated with the earlier parameters bound"; §5 [Split] "applied to Ω, the goal and all stored types".
(b) At the generic call, each parameter's type is evaluated left to right with the earlier parameters bound (`h : Le(y, *x)` reads `*x` through `x ↦ borrow₀ σx`) and stored with the binding in the pushed frame. [Split] then refines it: SubM's `h : Λ(σy, σx)` becomes `⊤`, `Λ(S σq, σx)`, `False` or `Λ(σq, σp)` depending on the arm. SubM's correctness depends on this.
(c) One sentence in [Def]: "the parameter types are evaluated as in [Call-type] and stored with the bindings".
(d) None.

**Q5 (data for D16/D25).** When the program's effect on `S σ'` is not `S` of its effect on `σ'` (SubM peels the head), the reborrow IH carries the wrong context. A copy (`let c = p; …(&c)`) gives the context-free IH. No injectivity is needed either way. D25's point, that the borrow structure supplies the congruence, has a converse: copying withholds it. Both are one line of source.

**Q6 (ergonomics).** §E5.9. Nothing to change in the rules; the paper and the error messages should mention it.

**Q7 (positive, for the simplifier).** E5 adds no rule. The pieces it relies on are:
- `fix` with codomain `Prop`;
- [Close]'s borrow-free row producing a sealed type;
- [Seal] re-normalising a sealed type on refinement, including a stored hypothesis type;
- [Call-type] reading `*x̂` through a moved borrow on a private copy;
- P2 skipping proof calls.

Everything E5 needs was already there for E1/E2, which is evidence that v1.3's rule set is closed under this kind of example. The one fix (Q1) removes a special case (a non-`⋆` proof value) rather than adding one.
