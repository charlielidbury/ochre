# 02 — Literature review: "A has the same side effects as B"

For each system: what it means to say two effectful expressions are equal, how it is written, and who decides it (the checker by conversion, or the user by proof). Snippets are schematic unless marked verified. Ochre's own answer is row 0 for comparison.

## 0. Ochre (this repo, under design)

Answer: `Id N M` is on source terms. `Refl` checks by running both sides on symbolic values from the same environment and comparing final value and final environment. A call stuck on an abstract value is replaced by fresh abstracts for its return and for each borrowed location, shared between the two runs. Decided by the checker.

```
Ω ⊢ Refl : Id N M    iff   ⟨Ω, N⟩ ≡ ⟨Ω, M⟩

⟨{x ↦ S σ}, AddM (&mut x) 0⟩ ⟶* ⟨{x ↦ S σ_u}, ()⟩        recorded (σ_r, σ_u) ← AddM σ 0
⟨{x ↦ S σ}, ()⟩              =   ⟨{x ↦ S σ}, ()⟩
-- not Refl: the induction supplies σ_u = σ, via  ⟨ret: Refl, x: cong S (AddMZero px).px, px: Refl⟩
```

Cost: a proof of `Id` between runs is a bundle, one equation per slot; plug soundness is the frame rule; determinism of loan ending is the consistency-critical property.

## 1. ∂CBPV — Pédrot, Tabareau, "The Fire Triangle", POPL 2020

Answer: equal only if syntactically equal, up to eight reductions (β, `let x := return v`, `dlet x := return v`, `force (thunk t)`, three ι rules) plus whatever equations an effect instantiation adds axiomatically. Equality is a value type, so computations are compared as thunks. Nothing is ever run.

```
eq (U X) (thunk t) (thunk u)   inhabited by refl   iff   t ≡ u          (Definition 4)

thunk (let x := return v in t) ≡ thunk (t{x := v})                                        -- yes
thunk (let x := (let y := t in u) in w) ≡ thunk (let y := t in let x := u in w)          -- no (Remark 1)
```

Effects in types are tracked, not run: `dlet x := t in u` has type `let x := t in X`, so the type re-performs the effect syntactically. Same-effects for state is left to the models, and the state-like (forcing) model needs an extensional target theory (Section 10).

## 2. Lean 4, `StateM` — verified on Lean 4.33

Answer: a computation is literally the function `σ → α × σ`. Concrete programs are `rfl` after unfolding. With an unknown state the two sides are functions stuck on their argument, so you need `funext` (a theorem from `Quot.sound`, not definitional), then induction, then a congruence on the pair.

```lean
example : (do set 1; set 2 : StateM Nat Unit) = set 2 := rfl              -- accepted

def addM (y : Nat) : Nat → Unit × Nat
  | 0     => ((), y)
  | n + 1 => let (u, n') := addM y n; (u, n' + 1)                         -- the borrow of the tail, by hand

theorem addM_zero : addM 0 = (pure () : StateM Nat Unit) :=
  funext fun s => Nat.rec (motive := fun s => addM 0 s = ((), s))
    rfl (fun n ih => congrArg (fun p : Unit × Nat => (p.1, p.2 + 1)) ih) s

example : addM 0 = (pure () : StateM Nat Unit) := rfl                    -- rejected
```

`Unit × Nat` is the slot bundle and `congrArg` on it is the slotwise `cong S`. The recursion has to be on the state as an explicit argument, so the zoom-and-rewrap (Aeneas's backward function) is written by the user. Monad laws are theorems: `bind_assoc` for `StateM` is `funext s; rfl`.

## 3. eMLTT with fibred algebraic effects — Ahman, POPL 2018 (with Ghani, Plotkin, FoSSaCS 2016)

Answer: the effect theory's equations are definitional on computations, and the identity type sees them through `thunk`. Decided by the checker, algebraically, for theories whose equations normalize.

```
get (x. get (y. M x y)) ≡ get (x. M x x)       get (x. put x M) ≡ M
put s (get (x. M x))    ≡ put s (M s)          put s (put s' M) ≡ put s' M

refl : Id (U (F 1)) (thunk (put 1 (put 2 (return ())))) (thunk (put 2 (return ())))
```

Global cells only; no allocation, no borrowing. "Fibred" = operations and equations may depend on values and commute with substitution.

## 4. F\* — "Dijkstra Monads for Free", POPL 2017

Answer: `reify` turns a stateful computation into its state-passing function; equality is then ordinary equality on pure terms, discharged by normalization plus SMT. Schematic:

```fstar
let e1 () : ST unit (requires fun _ -> True) (ensures fun _ _ _ -> True) = put 1; put 2
let e2 () : ST unit (requires fun _ -> True) (ensures fun _ _ _ -> True) = put 2
let same () = assert (forall s. reify (e1 ()) s == reify (e2 ()) s)
```

"The Next 700 Relational Program Logics" (Maillard, Hriţcu, Rivas, Van Muylder, POPL 2020) makes "these two runs relate" a first-class spec.

## 5. Interaction Trees — Xia et al., POPL 2020

Answer: not `eq`. Effects are a free monad in Coq; two programs have the same effects if they are bisimilar after interpretation (`eutt`). Proved by the user with the `eutt` lemma library; Coq's `eq` is deliberately not used because it is too fine. Schematic:

```coq
Lemma same : forall s,
  eutt eq (run_state (trigger (Put 1) ;; trigger (Put 2)) s)
          (run_state (trigger (Put 2)) s).
```

## 6. Hoare Type Theory / Ynot — Nanevski, Morrisett, Birkedal, ICFP 2006; Ynot, ICFP 2008

Answer: no equality between computations at all. Each computation has a spec type; "same effects" is at best "same spec".

```
e1 : STsep (fun h => h = x :-> v) unit (fun _ h' => h' = x :-> 2)
e2 : STsep (fun h => h = x :-> v) unit (fun _ h' => h' = x :-> 2)      -- same type, still no e1 = e2
```

Relational HTT (Nanevski, Banerjee, Garg, IEEE S&P 2011) adds types over two runs: `{h1 = h2} e1 ~ e2 {r1 = r2 ∧ h1' = h2'}`.

## 7. Observational Type Theory — Altenkirch, McBride, Swierstra, PLPV 2007; Pujet, Tabareau, POPL 2022

Answer: the type of equality proofs is computed from the type. At a pair it is a pair of equalities, at a function it is pointwise. For `S → A × S` that reads "for every start state, same result and same end state". The user still supplies the proof; the theory supplies the bundle. Schematic:

```
(e1 == e2) at S → A × S    ⇝    ∀ s. fst (e1 s) == fst (e2 s)  ∧  snd (e1 s) == snd (e2 s)
```

Ochre's `⟨ret: …, x: …, px: …⟩` is this rule at the type of configurations.

## 8. Quotient / higher inductive types — e.g. Chapman, Uustalu, Veltri, ICTAC 2015 (delay monad)

Answer: define the type of computations with the effect equations as constructors. `Id` is then "same effects" by construction, and the proof is the constructor. Schematic cubical Agda:

```agda
data State (A : Set) : Set where
  return  : A → State A
  get     : (S → State A) → State A
  put     : S → State A → State A
  put-put : ∀ s s' m → put s (put s' m) ≡ put s' m
  ...

_ : put 1 (put 2 (return tt)) ≡ put 2 (return tt)
_ = put-put 1 2 (return tt)
```

Deciding `Id` is the word problem of the theory; for state it normalizes.

## 9. Algebraic theory of state — Plotkin, Power, FoSSaCS 2002; Staton, LICS 2013 (allocation); Ahman, Staton, MFPS 2013 (NbE)

Answer: "same effects" means provable from the state equations. Decidable by normalizing every term to read-once-then-write-once form.

```
every M : T A over one cell   ≡   get (x. put (f x) (return (g x)))     for some f : S → S, g : S → A
M ≡ N    iff    same (f, g)
```

Ochre's Ω machine is a normalizer of this kind for a structured, local, borrow-shaped state.

## 10. Aeneas, Creusot, RustHornBelt — Ho, Protzenko, ICFP 2022; Denis, Jourdan, Marché, ICFEM 2022; Matsushita et al., PLDI 2022

Answer: a `&mut` argument is a pair (value now, value at the end of the borrow). "Same effect on `x`" means "same final value". Aeneas computes the final value as an extra output of the translated function; Creusot and RustHorn name it with a prophecy variable `^x`.

```
// Aeneas, roughly:  fn add_m(x: &mut Nat, y: Nat)   ⇝   add_m : Nat → Nat → Result Nat   (returns the new x)
theorem add_m_zero (x : Nat) : add_m x 0 = .ok x

// Creusot
#[ensures(^x == *x)]
fn add_m_zero(x: &mut Nat) { add_m(x, 0) }
```

Ochre's `σ_u` plug is the prophecy; the difference is doing it inside conversion instead of in a translation.

## 11. Types that mention a location — Xanadu (Xi, LICS 2000), ATS views (Zhu, Xi, PADL 2005), Deputy (Condit et al., ESOP 2007), Flux (Lehmann et al., PLDI 2023), RefinedRust (Gäher et al., PLDI 2024)

Answer: no notion of "same effects". What these settle is what a proof about a mutable variable means after a write. Xanadu and Flux re-type the variable on write; ATS makes the proof a linear resource that the write consumes and reissues; Deputy re-checks every dependent type in scope at each assignment.

```rust
// Flux: strong reference, refinement updated by the call
#[flux::sig(fn(x: &strg Nat[@n], y: Nat[@m]) ensures x: Nat[n + m])]
fn add_m(x: &mut Nat, y: Nat) { ... }
```

```
// ATS, schematic:  pf : (0 @ x)  is consumed by  x := 1  and replaced by  pf' : (1 @ x)
```

Ochre closes hypotheses over values instead, so the question does not arise.

## 12. Kept apart — Krishnaswami, Pradic, Benton, POPL 2015; QTT (Atkey, LICS 2018); Idris 2

Answer: none. Effectful or linear terms cannot appear in a type, so `Id` cannot mention them. This is the "not too hard" design that 00-idea.md sets aside.

## 13. ReLoC — Frumin, Krebbers, Birkedal, LICS 2018

Answer: a refinement judgment in Iris, not a type: `e1 ≾ e2 : τ` says every behaviour of `e1` is a behaviour of `e2`. Proved interactively in a relational program logic.

```
⊢ (put 1; put 2) ≾ put 2 : ()
```

## Summary

| System | Who decides | Runs anything? | "Same" means |
|---|---|---|---|
| Ochre | checker | yes, symbolically | same final (value, environment), plugs shared |
| ∂CBPV | checker | no | syntactic, plus axiomatic effect equations |
| Lean `StateM` | user, via `funext` | unfolds to a function | same function `σ → α × σ` |
| eMLTT + effects | checker | no | the effect's equations |
| F\* `reify` | SMT | unfolds to a function | same function |
| Interaction trees | user | no | bisimulation |
| HTT / Ynot | nobody | no | same spec, at best |
| OTT | user, bundle from the theory | no | pointwise on the type's structure |
| HITs / QITs | constructor | no | quotient by the equations |
| Aeneas / Creusot | external prover | translation | same final value of the borrow |
| Flux / ATS / Xanadu | n/a | no | n/a; they settle proof-after-write |
| ReLoC | user | no | refinement |
