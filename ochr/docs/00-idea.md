My long term goal is to create a programming language which is both an efficient systems language, and a theorem prover.

My short term goal is to design a core calculus which contains both
1. mutability via Rust-style mutable references and
2. dependent types.

There is other work in the repo regarding this effort, but I want to do some totally from-scratch thinking under this ochre/docs/ folder since I want to take a very different path from the existing DLLBC.

This new calculus (Ochre) takes inspiration primarily from:
1. Aeneas' LLBC (where I get the `loan` + `borrow` system from, see @aeneas.pdf for full details)
2. Lean's core kernel (where I get the CIC style dependent types from, see @theory-of-lean.pdf for full details)
I am happy to diverge from these sources, but my default answer for anything that I'm not trying to innovate with is "do it however Aeneas/Lean does it".

Making a language with mutability and dependent types is not too hard if you are willing to keep the mutability apart from the dependent types (e.g. separate expressions out into pure and impure expressions, then only allow pure expressions to appear in types). The difficulty I am trying to directly address is how can you get these combined 

I have been working on pen & paper for a while now, and have boiled down the central problem into a motivating example:

```ochr
// Iterates through the nodes of peano nat `x` until it gets to the final `Z` node,
// then replaces the final `Z` node with `y` (by move)
// This has the effect of `*x += y` without malloc'ing any new nodes
// NB: AddM borrows `x`, and consumes `y`
let AddM = λx: &mut Nat. λy: Nat. (
    match x {
        Z => *x := y, // Move `y` into the tail of our number
        S px => AddM px y, // Rust style "lift into references" means `px : &mut Nat` here
    }
);

// Add wraps AddM to give it a pure interface
let Add = λx: Nat. λy: Nat. (
    AddM (&mut x) y;
    x
);

// Proof of "forall x, x + 0 = x"
let AddZero = λx: Nat. (
    match x {
        Z => Refl,
        S px => ???,
    }
);

// Check the proof is correct
assert AddZero : Πx: Nat. Id Nat (Add x 0) x
```

NB: The language above is not anywhere in this repo, so do not go looking for an appropriate language reference, one does not exist. I am hoping you are able to read between the lines a bit and understand what I "mean" by the above code.

It would be desireable to have a language which could handle this example because the efficient implementation of `Add` which we want to use at runtime is reasoned about directly in the types and the proofs. Existing languages which intersect dependent types and mutability usually require you to have some pure specification, then show it is equivalent to your efficient in place version. I speculate this is because when you had types like `Id Nat (Add x 0) x` you need to use rules like "if e1 β-reduces down to e2, then e1=e2" so that in the `S px =>` case of `AddZero` the type system can realise `Add (S x) 0` equals `S (Add x 0)` and therefore replace `Id Nat (Add (S x) 0) (S x)` with `Id Nat (S (Add x 0)) (S x)` which holds by `cong S ih`.

The language implied by the example above has β-reduction with side effects, which means extreme care has the be taken with evaluation order and what it even means for a side effect to occur at the type level. Our task today will be to slowly explore this space and think about what set of typing rules could soundly allow for this example.

In Ochr programs will be type-and-borrow checked simultaneously via an abstract interpretation which is lifted almost entirely from Aeneas. Read the paper for more details, but the important bits are
1. an environment Ω is threaded through which maps variables onto _values_ in declaration order
2. the concept of an abstract value `(σ: τ)` which says "idk what the value is, but ik the type"
3. `borrow_N` and `loan_N` values which track borrow state (see example) below.

NB: Ochr does not have immutable references for the sake of simplicity. From now on `&M` is shorthand for `&mut M` 

Quick example:

```ochr
λx: Nat. (
    // Ω = { x ↦ (σ: Nat) } // in function body all we can say about `x` is it's _some_ Nat
    let y = &mut x;
    // Ω = { x ↦ loan_0, y ↦ borrow_0 (σ: Nat) } // value has _temporarily_ moved into y
    *y := 2;
    // Ω = { x ↦ loan_0, y ↦ borrow_0 2 } // `y` updated

    // the interpreter now wants to evaluate `x` but it can't immediately do so because it's been loaned out
    // so it _terminates_ the loan, making the value local to x again
    // Ω = { x ↦ 2 }
    x
)
```

A driving question is: what goes in that ??? hole in `AddZero`? And how should the derivation work, from the perspective of the people making the typing rules (us)?

NB: in this example all abtract variables happen to be `Nat`, so we omit the type annotation on abstracts.

Our goal is to show `Add x 0` equals `x` by inhabiting a term of type `Id Nat (Add x 0) x`. In the succ branch `x` has been narrowed down to some `S σ_px` ("successor fo some abstract σ_px") leaving us with roughly the obligation:

```
Ω = { x ↦ S σ_px, px ↦ σ_px }

Ω ⊢ ??? : Id Nat (Add x 0) x 
```

An idea I am exploring at the moment is considering the pair `⟨Ω, e⟩` together for equality checks, so the side effects of things are captured. For example `a := 2` and `()` are equal when you only look at the values, but the produce unequal effects on the environment:
```
⟨{ a ↦ 1 }, a := 2⟩
= ⟨{ a ↦ 2 }, ()⟩
≠ ⟨{ a ↦ 1 }, ()⟩
```

Lets start unfolding `Add x 0` with this paired understanding and see what happens
```
Goal: ⟨{ x ↦ S σ_px }, x⟩
or equivalently ⟨∅, S σ_px⟩

// Original statement
⟨Ω, Add x 0⟩            // Ω = { x ↦ S σ_px }

// outer `x` consumed as function argument, now we have inner one
= ⟨Ω', AddM &x 0; x⟩            // Ω' = { x ↦ ⊥, x ↦ S σ_px }

// `x` borrowed
= ⟨Ω'', AddM (borrow_0 (S σ_px)) 0; x⟩            // Ω'' = { x ↦ ⊥, x ↦ loan_0 }

// `AddM` goes into successor case, recurses with `px`
= ⟨Ω''', AddM px 0; x⟩         // Ω''' = { x ↦ ⊥, x ↦ loan_0, x ↦ borrow_0 (S loan_1), px ↦ borrow_1 σ_px }
= ⟨Ω'''', AddM (borrow_1 σ_px) 0; x⟩         // Ω'''' = { x ↦ ⊥, x ↦ loan_0, x ↦ borrow_0 (S loan_1) }
```

And now lets start unfolding our inductive hypothesis `AddZero px`'s type which is roughly `⟨Ω, Id Nat (Add x 0) x⟩` where `Ω = { x ↦ σ_px }`

```

⟨Ω, AddZero px⟩            // Ω = { x ↦ S σ_px, px ↦ σ_px }



```


... dot dot dot I get stuck here

but I know I want the argument to be something along the lines of:
1. inductive hypothesis tells us "`AddM &x 0` where `x ↦ σ_px` leaves `x` uneffected"
2. therefore "`AddM &x 0` where `x ↦ S σ_px` leaves `x` uneffected"
3. therefore "`AddM &x 0` leaves `x` uneffected forall `x`"
4. therefore "Add x 0 = x"

