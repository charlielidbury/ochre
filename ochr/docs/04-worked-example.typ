#set page(paper: "a4", margin: 1.5cm)
#set text(size: 10pt)
// Long derivation lines wrap. A wrapped continuation is indented past the
// line's own indentation, so the tree structure survives the wrap.
#show raw.where(block: true): it => {
  set text(size: 8pt)
  set par(spacing: 0.65em, leading: 0.65em)
  block(width: 100%, above: 1em, below: 1em, {
    for line in it.text.split("\n") {
      let lead = line.len() - line.trim(" ", at: start).len()
      par(hanging-indent: (lead + 6) * 0.6em, raw(if line == "" { " " } else { line }))
    }
  })
}

= 04: Worked example, `AddMZero`

One proof, type-checked in full. Derivations are written in the style of `docs/notation.md`: conclusion first, premises indented below it, comments after `//`. No general rules are stated here. The aim is to see every step of one derivation, and to extract the general principles from it afterwards.

== The program

```
let AddM = λx: &mut Nat. λy: Nat. (
    match x {
        Z    => *x := y,        // move y into the final node
        S px => AddM px y,      // px : &mut Nat, a reborrow of the tail
    }
);

let AddMZero = λx: &mut Nat. (
    match x {
        Z    => Refl,
        S px => AddMZero px,
    }
);

assert AddMZero : Πx: &mut Nat. Id (AddM x 0) ()
```

`AddM` adds `y` in place onto the number behind `x`, walking down the successors until it reaches the final `Z` and moving `y` into that spot. `AddMZero` claims that adding `0` this way changes nothing: `AddM x 0` returns `()`, and afterwards the number behind `x` is what it was before, because `()` on the right side touches nothing.

== Conventions

- Environments are written `{ A{loan₀} ‖ x ↦ borrow₀ σ }`. `‖` separates frames, oldest on the left. `A{…}` is the caller's side of the borrow that `x` was made from. It holds `loan₀`, and it is the only thing outside the function that the function can affect. It plays the role of Aeneas's region abstraction.
- `σ` is an abstract value: some `Nat` whose shape is not known.
- Reading a variable moves it: `⟨Ω[x ↦ v], x⟩ ⟶ ⟨Ω[x ↦ ⊥], v⟩`.
- A run `⟨Ω, e⟩ ⇓ ⟨outer, v⟩` evaluates `e` from `Ω` and then closes the function's scope: its variables are dropped and their borrows are returned to their loans. What is left is the outer environment, here just `A{…}`, and the result `v`. Runs performed while checking a type are hypothetical. Nothing they do persists.
- `Ω ⊢ Refl : Id M N` runs `M` and `N` from `Ω` and requires the two results and the two outer environments to agree.
- `N := AddM (borrowₗ σ) 0; loanₗ` names what a stuck call leaves behind its loan: run the call, then read what came back through the loan. The index `l` is local to `N`. How that locality is best formalised is left open.
- Typing rules are named in capitals, `[Lam]`, `[Case]`, `[Refl]`, `[App]`, `[Conv]`, `[Var]`. Machine steps inside a run are named in lower case, `[read]`, `[unfold]`, `[match]`, `[assign]`, `[pop]`, `[close]`, `[end-loan]`, `[rollback]`, `[close-off]`.
- `AddM`'s own parameters are written `x'`, `y` inside its frame, and `x''`, `y'` in a nested attempt, to keep them apart from `AddMZero`'s `x`.

== The derivation

=== Top level

```
{} ⊢ λx. match x { Z => Refl, S px => AddMZero px } : Πx: &mut Nat. Id (AddM x 0) () // [Lam]
  { A{loan₀} ‖ x ↦ borrow₀ σ } ⊢ match x { Z => Refl, S px => AddMZero px } : Id (AddM x 0) () // [Case] below
```

`[Lam]` opens the function's frame. The parameter is a borrow of something the caller owns, so `x` gets a fresh borrow of an abstract value, and the caller's side `A` holds the matching loan. The body is checked against the codomain with `x` in scope. `AddMZero` itself is in scope with its declared type, and the recursion is structural: `px` is a sub-borrow of `x`.

`[Case]` on `x ↦ borrow₀ σ` with `σ` abstract cannot pick an arm, so it checks every arm, refining `σ` in each:

```
{ A{loan₀} ‖ x ↦ borrow₀ σ } ⊢ match x { Z => Refl, S px => AddMZero px } : Id (AddM x 0) () // [Case]
  { A{loan₀} ‖ x ↦ borrow₀ Z } ⊢ Refl : Id (AddM x 0) () // arm Z: σ := Z, see The Z arm
  { A{loan₀} ‖ x ↦ borrow₀ (S loan₁), px ↦ borrow₁ σ } ⊢ AddMZero px : Id (AddM x 0) () // arm S: σ := S σ', field reborrowed, see The S arm
```

In the S arm the match goes through a borrow, so the pattern variable is a reborrow of the field: `px` holds `borrow₁ σ'` and the `S` stays behind in `x`, with `loan₁` in the tail position. From here on the tail `σ'` is written `σ`.

=== The Z arm

```
{ A{loan₀} ‖ x ↦ borrow₀ Z } ⊢ Refl : Id (AddM x 0) () // [Refl]
  ⟨{ A{loan₀} ‖ x ↦ borrow₀ Z }, AddM x 0⟩ ⇓ ⟨A{Z}, ()⟩ // left side
    ⟨{ A{loan₀} ‖ x ↦ ⊥ }, AddM (borrow₀ Z) 0⟩ // [read] x is moved into the argument
    ⟨{ A{loan₀} ‖ x ↦ ⊥ ‖ x' ↦ borrow₀ Z, y ↦ 0 }, match x' { Z => *x' := y, S p => AddM p y }⟩ // [unfold] AddM's frame is pushed
    ⟨{ A{loan₀} ‖ x ↦ ⊥ ‖ x' ↦ borrow₀ Z, y ↦ 0 }, *x' := y⟩ // [match] the content behind x' is Z: first arm
    ⟨{ A{loan₀} ‖ x ↦ ⊥ ‖ x' ↦ borrow₀ Z, y ↦ ⊥ }, ()⟩ // [read] y is moved; [assign] Z is written over Z through borrow₀
    ⟨{ A{Z} ‖ x ↦ ⊥ }, ()⟩ // [pop] AddM's frame: dropping x' ends borrow₀, Z lands in loan₀
    ⟨A{Z}, ()⟩ // [close] AddMZero's frame: x is ⊥, nothing to return
  ⟨{ A{loan₀} ‖ x ↦ borrow₀ Z }, ()⟩ ⇓ ⟨A{Z}, ()⟩ // right side
    ⟨{ A{loan₀} ‖ x ↦ borrow₀ Z }, ()⟩ // already a value
    ⟨A{Z}, ()⟩ // [close] dropping x ends borrow₀, Z lands in loan₀
  () = () // results agree
  A{Z} = A{Z} // outer environments agree
```

Both runs end with the caller's place holding `Z` and the result `()`. `Refl` is accepted. Everything here ran to completion because the value behind `x` was known.

=== The S arm

Write `Ωₛ` for `{ A{loan₀} ‖ x ↦ borrow₀ (S loan₁), px ↦ borrow₁ σ }`.

```
Ωₛ ⊢ AddMZero px : Id (AddM x 0) () // [Conv] the inferred type must match the expected type
  Ωₛ ⊢ AddMZero px : Id (AddM px 0) () // [App] the codomain with the parameter bound to px
    AddMZero : Πx: &mut Nat. Id (AddM x 0) () // the declared type of the function being defined
    Ωₛ ⊢ px : &mut Nat // [Var] px holds borrow₁ σ, a borrow of a Nat
  Id (AddM px 0) () ≡ Id (AddM x 0) () // [Conv] below
```

`[App]` gives the recursive call its declared type with `px` in the parameter position. Because `px` is a variable, binding the parameter to it and substituting it are the same thing. At the term level `px` is moved into the call. The type is computed in `Ωₛ` as it stands.

`[Conv]` on two `Id` types runs their sides in `Ωₛ` and compares: the two left sides must agree with each other, and the two right sides must agree with each other.

```
Id (AddM px 0) () ≡ Id (AddM x 0) () // [Conv]
  ⟨Ωₛ, AddM px 0⟩ ⇓ ⟨A{S N}, ()⟩ // left side of the inferred type, run (i)
  ⟨Ωₛ, AddM x 0⟩ ⇓ ⟨A{S N}, ()⟩ // left side of the expected type, run (ii)
  A{S N} = A{S N}, () = () // left sides agree, the two N up to renaming of l
  ⟨Ωₛ, ()⟩ ⇓ ⟨A{S σ}, ()⟩ // both right sides are this same run, run (iii)
  A{S σ} = A{S σ}, () = () // right sides agree
```

Run (i), the left side of the inferred type:

```
⟨Ωₛ, AddM px 0⟩ ⇓ ⟨A{S N}, ()⟩
  ⟨{ A{loan₀} ‖ x ↦ borrow₀ (S loan₁), px ↦ ⊥ }, AddM (borrow₁ σ) 0⟩ // [read] px is moved into the argument
  ⟨{ A{loan₀} ‖ x ↦ borrow₀ (S loan₁), px ↦ ⊥ ‖ x' ↦ borrow₁ σ, y ↦ 0 }, match x' { … }⟩ // [unfold] attempted: the content behind x' is σ, no arm applies
  ⟨{ A{loan₀} ‖ x ↦ borrow₀ (S loan₁), px ↦ ⊥ }, AddM (borrow₁ σ) 0⟩ // [rollback] the attempt is undone; the call is stuck
  ⟨{ A{loan₀} ‖ x ↦ borrow₀ (S N), px ↦ ⊥ }, ()⟩ // [close-off] the call returns (); loan₁ receives N := AddM (borrowₗ σ) 0; loanₗ
  ⟨A{S N}, ()⟩ // [close] px is ⊥; dropping x ends borrow₀, S N lands in loan₀
```

Run (ii), the left side of the expected type:

```
⟨Ωₛ, AddM x 0⟩ ⇓ ⟨A{S N}, ()⟩
  ⟨{ A{loan₀} ‖ x ↦ borrow₀ (S σ), px ↦ ⊥ }, AddM x 0⟩ // [end-loan] x is used while px reborrows its tail: borrow₁ ends, σ lands in loan₁
  ⟨{ A{loan₀} ‖ x ↦ ⊥, px ↦ ⊥ }, AddM (borrow₀ (S σ)) 0⟩ // [read] x is moved into the argument
  ⟨{ A{loan₀} ‖ x ↦ ⊥, px ↦ ⊥ ‖ x' ↦ borrow₀ (S σ), y ↦ 0 }, match x' { Z => *x' := y, S p => AddM p y }⟩ // [unfold] AddM's frame is pushed
  ⟨{ A{loan₀} ‖ x ↦ ⊥, px ↦ ⊥ ‖ x' ↦ borrow₀ (S loan₂), p ↦ borrow₂ σ, y ↦ 0 }, AddM p y⟩ // [match] the content is S σ: second arm; the field is reborrowed, the S stays in x'
  ⟨{ A{loan₀} ‖ x ↦ ⊥, px ↦ ⊥ ‖ x' ↦ borrow₀ (S loan₂), p ↦ ⊥, y ↦ ⊥ }, AddM (borrow₂ σ) 0⟩ // [read] p and y are moved into the arguments
  ⟨{ A{loan₀} ‖ x ↦ ⊥, px ↦ ⊥ ‖ x' ↦ borrow₀ (S loan₂), p ↦ ⊥, y ↦ ⊥ ‖ x'' ↦ borrow₂ σ, y' ↦ 0 }, match x'' { … }⟩ // [unfold] attempted: the content behind x'' is σ, no arm applies
  ⟨{ A{loan₀} ‖ x ↦ ⊥, px ↦ ⊥ ‖ x' ↦ borrow₀ (S loan₂), p ↦ ⊥, y ↦ ⊥ }, AddM (borrow₂ σ) 0⟩ // [rollback] the inner call is stuck
  ⟨{ A{loan₀} ‖ x ↦ ⊥, px ↦ ⊥ ‖ x' ↦ borrow₀ (S N), p ↦ ⊥, y ↦ ⊥ }, ()⟩ // [close-off] the call returns (); loan₂ receives N
  ⟨{ A{S N} ‖ x ↦ ⊥, px ↦ ⊥ }, ()⟩ // [pop] AddM's frame: dropping x' ends borrow₀, S N lands in loan₀
  ⟨A{S N}, ()⟩ // [close] x and px are ⊥
```

Run (iii), the right side of both types:

```
⟨Ωₛ, ()⟩ ⇓ ⟨A{S σ}, ()⟩
  ⟨{ A{loan₀} ‖ x ↦ borrow₀ (S loan₁), px ↦ borrow₁ σ }, ()⟩ // already a value
  ⟨{ A{loan₀} ‖ x ↦ borrow₀ (S σ), px ↦ ⊥ }, ()⟩ // [close] dropping px ends borrow₁, σ lands in loan₁
  ⟨A{S σ}, ()⟩ // [close] dropping x ends borrow₀, S σ lands in loan₀
```

Both left sides end at `⟨A{S N}, ()⟩` and both right sides at `⟨A{S σ}, ()⟩`, so `[Conv]` holds and the S arm checks. The whole definition is accepted.

== What happened in the S arm

Read as statements, the two `Id` types say the same thing. The expected type `Id (AddM x 0) ()` in this arm is the claim that the caller's place ends as `S N` on the left and `S σ` on the right, that is, `S N = S σ`. The inferred type `Id (AddM px 0) ()` is a claim about the recursive call on the tail, and it evaluates to the very same `S N = S σ`, because `loan₁` sits inside the `S` in `x`: when run (i) closes off the call and writes `N` into `loan₁`, `x` already holds `S N`, and closing the scope carries `S N` out to the caller's place. The environment performed the congruence step. Nothing in the proof term does.

So the arm is accepted by conversion alone. This is the induction: the hypothesis, read in the environment of the S arm, is the goal. The two runs differ in which variable they consumed, `px` in run (i) and `x` in run (ii), and this does not matter because `[close]` drops every local either way and the comparison is made on the caller's place after that.

The one place where something was not computed is `[close-off]`. The checker learned everything it could from `AddM`'s signature and stopped at the recursive call on `σ`. `N` names what that call leaves behind, and it is the same term on both sides because both stuck calls have the same function and the same argument values. Nothing more is known about `N` here, and nothing more is needed.

== Rules that appeared

Typing rules:

- `[Lam]`: open the function's frame; a `&mut` parameter becomes a fresh borrow of an abstract value, with its loan on the caller's side.
- `[Case]`: a match on an abstract value checks every arm, refining the abstract value by the arm's pattern; through a borrow, pattern variables are reborrows of the fields.
- `[Refl]`: run both sides, close the scope, compare results and outer environments.
- `[App]`: a call gets the declared codomain with the parameter bound to the argument.
- `[Var]`: a variable has the type of the value it holds.
- `[Conv]`: two `Id` types are equal when their left sides run to the same place and their right sides run to the same place.

Machine steps:

- `[read]`: reading a variable moves its value out and leaves `⊥`.
- `[unfold]`: push the callee's frame with its parameters bound, and evaluate its body.
- `[match]`: the constructor behind the scrutinee is known, so take that arm; through a borrow, reborrow the fields and leave the constructor in place.
- `[assign]`: write through a borrow.
- `[pop]`: drop a callee's frame; dropped borrows return their content to their loans.
- `[close]`: the same for the function's own frame, at the end of a run.
- `[end-loan]`: using a variable whose content has an outstanding loan ends that loan first.
- `[rollback]`: an `[unfold]` whose body reaches a match on an abstract value is undone.
- `[close-off]`: the stuck call is replaced by its return value, and its loan receives `N`, the call followed by a read of its loan.

== Open points to extract from this

- The locality of the index `l` in `N`, without introducing a quantifier if that can be avoided.
- `[App]` when the argument is not a variable: binding the parameter to a fresh location, rather than substituting a term into the codomain.
- What `[Conv]` compares exactly when the outer environment holds more than one place.
- The `[close-off]` step for a call that returns a borrow, where the loan must receive a function of the returned borrow's final content.
