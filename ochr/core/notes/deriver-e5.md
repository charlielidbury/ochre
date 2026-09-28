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
