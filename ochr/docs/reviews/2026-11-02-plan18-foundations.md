# Referee report on docs/18: foundations and semantics

Attack on the consistency proof plan `ochr/docs/18-consistency-proof-plan.typ`, as it stood on 2026-11-02: the first, 26-page draft, before the set-theory background, the explainer boxes and the notation changes were added. The referee was a fresh, read-only Opus agent (`attack-foundations`), asked to produce a statement of the form "this plan for consistency will never lead to a final proof of consistency because X", where X is a real obstruction rather than a difficulty. Its angle: the set model and its interpretation of impredicative `Prop`, universes, large elimination, observational `Eq` and η at `Unit`; the conversion-soundness principles; function values and borrow-returning functions; what a "good" ground function value must be; Gödel; and circularity between soundness and the invariants it assumes. The report arrived in two parts; both are given here, lightly edited.

## 1. The statement

As written, the plan will never lead to a final proof of consistency. It defines "true" in the set model, which quantifies over arbitrary set-theoretic values. But its only argument for soundness (the walk), and every lemma beneath it ((P), (C), (Sp), the frame property, stability), speaks only about machine values. The checker accepts lemmas whose hypotheses are true in the set model but whose only witnesses are non-computable functions. On those lemmas the walk cannot keep its invariants, and its induction hypothesis cannot supply what it needs.

This blocks the plan's current definitions, not consistency itself, and not the operational strategy as a whole (section 4).

## 2. The argument, and where it breaks

- **Truth is set truth throughout.** A proposition is true when its meaning is `{•}`. Soundness clause (ii) asks for "hypotheses at β true", the walk's invariant asks that every proof place's type be true under α, and the walk's step for a match on a proof reasons "its meaning is inhabited by some constructor, whose fields' types are therefore true, so that arm's claim applies".
- **Instances are machine values.** Refinements assign values, and Q1 asks for good *ground values*.
- **Ochr can state "f decides halting".** The type `ExW(Prog → Nat, Decides)` below is true in the set model, because the characteristic function of the halting set is a witness. No machine value is a witness: a good closure computes a total computable function, and halting of two-counter machines started at zero is undecidable (Minsky).
- **The walk on `L3` at an instance `p := P0`.** `L3` is accepted; it proves excluded middle for halting from that hypothesis.
  - The step for a match on a proof, on `e`, binds the data field `w` to a fresh unknown `σ_w` and the proof field `h` to type `Decides(σ_w)`.
  - The walk's invariant then needs `Decides(α(σ_w))` to be true. Any machine closure chosen for `α(σ_w)` makes it false, so the invariant breaks.
  - If `σ_w` is left unrefined instead, the next step, generalising `n = ⌈σ_w(P0)⌉` before the split, needs `α(σ_n)` to be the normal form of that sealed program under α. That is stuck and has no head constructor, so the walk cannot choose an arm.
  - The characteristic function itself cannot go into a machine state.
  - So the walk cannot prove (ii) for `L3`, even though (ii) is true classically, and the induction over all accepted definitions fails at `L3`.
- **The same happens in a closed program**, which refutes Q1's hope that definability suffices because "consistency only needs closed terms".
  - `UseK := K(M)` is closed and accepted. The walk's step for the lemma call needs `M`'s type to be true: "every set-theoretic decider answers 0 on `HaltProg`".
  - The induction hypothesis (ii) for `M` covers only machine instances. No machine `f` satisfies `Decides`, so it is vacuous, and would hold just as well for an `M′` claiming the answer is 1.
  - So nothing available to the walk establishes `M`'s type, and the corollary's own walk is stuck on a closed program.
- **The plan's lemmas cannot fill the step.** (P), (C), (Sp), the frame property and stability all quantify over machine refinements. Filling the step needs their semantic counterparts under set-valued valuations, which together amount to a denotational soundness proof: the route the plan does not take.

## 3. Evidence

Every probe block also contained `def Control : False := refl`, and every control was rejected.

The central probe (with `run` a step-bounded interpreter for two-counter machines, `HaltsAt(p, k)` "`run` halts within `k` steps", and `Or` the usual two-constructor proposition):

```
inductive Halts (p : Prog) : Prop := HW(k : Nat, h : HaltsAt(p, k))
def Decides (f : Prog → Nat) : Prop :=
  Π(p : Prog). (Π(e : Eq(Nat, f(clone(p)), 0)). Halts(clone(p))) ∧ (Π(t : Halts(clone(p))). Eq(Nat, f(clone(p)), 0))
def App (A : Type) (P : Π(a : A). Prop) (w : A) : Prop := P(w)
inductive ExW (A : Type) (P : Π(a : A). Prop) : Prop := Wit(w : A, h : App(A, P, w))
def L3 (e : ExW(Prog → Nat, Decides)) (p : Prog) : Or(Halts(clone(p)), Π(t : Halts(clone(p))). False) := (
  match e { Wit(w, h) => (
    let hp = h(clone(p));
    match hp { Intro(l, r) => (
      let n = w(clone(p));
      match n { Z => Inl(l(refl)), S m => Inr(r) }) }) })
```

`run`, `Halts`, `Decides`, `ExW`, `M` and `L3` are all ACCEPTED, and a check by `refl` confirms the interpreter runs.

The closed program:

```
def M (f : Prog → Nat) (h : Decides(f)) : Eq(Nat, f(HaltProg), 0) := (
  let hp = h(HaltProg); match hp { Intro(l, r) => r(HaltsHalt) })
def K (k : Π(f : Prog → Nat) (h : Decides(f)). Eq(Nat, f(HaltProg), 0)) : Eq(Nat, 1, 1) := refl
def UseK : Eq(Nat, 1, 1) := (let u : Eq(Nat, 1, 1) = K(M); u)
```

`K` and `UseK` are ACCEPTED.

A stuck `J` at extensionally equal endpoints:

```
def Id0 (n : Nat) : Nat by n := match n { Z => 0, S m => S(Id0(m)) }
def f0 (n : Nat) : Nat := Id0(n)
def g0 (n : Nat) : Nat := n
def NotConv : Eq(Nat → Nat, f0, g0) := refl
def D (f : Nat → Nat) (g : Nat → Nat) (h : Eq(Nat → Nat, f, g)) : Nat := (
  let x = J(Nat → Nat, f, g, λ(k : Nat → Nat) : Type => Nat, h, 5);
  match x { Z => 0, S m => 1 })
```

`D` is ACCEPTED; `NotConv` is rejected ("the body of NotConv has type ⊤, but the goal is Eq(Π(_ : Nat). Nat, f0, g0)").

Further probes, all behaving as the rules intend:
- **Impredicativity:** `inductive SigP (P : Prop) := MkSigP(n : Nat, h : P)`, `NoInh : Prop := Π(A : Type) (a : A). False`, `SelfT : Type := SigP(NoInh)` and `Use (k : NoInh) (s : SelfT) : False := k(SelfT, s)` are all accepted.
- **Infinitely branching types** are rejected as "fields are first-order data", both through a parameter (`Sup1(f : Box(Π(n : Nat). W1))`) and through a type function (`Arr(A) := Π(n : Nat). A`, `Sup2(f : Arr(W2))`).
- **Large elimination** from a proposition with a data field is rejected, both into `Prop` and into `Nat`.
- No closed proof of `False` was found.

## 4. Confidence, and what would rescue the plan

- **High (about 90%)** that, with truth in the set model, the walk cannot prove soundness clause (ii). The weak point: (ii) itself is true (classically, for `L3`); what fails is the method. This blocks the plan's current definitions, not consistency and not the operational strategy as a whole.
- **Rescue 1: define truth over machine values.** A realizability model, or logical relation, with Girard-style candidates for impredicative quantification over `Type`. Then `L3`'s hypothesis is false at every instance (no good decider exists), and `M`'s type holds vacuously at every good instance. This replaces the set model, the injectivity relation as a set, and the inaccessible cardinals. It also lets conversion soundness follow from the plan's own machine-level lemmas ((P), (C), stability), and the relation lives in one Lean universe (candidates are sets of values), which disposes of Q8.
- **Rescue 2: add a denotational soundness proof** of the symbolic checker under set-valued valuations. That makes the walk redundant for consistency.

## 5. Secondary weaknesses (short of an obstruction)

1. **Conversion soundness has the same gap.** The principles for Π-types, function values and conversion under refinement are said to rest on (P). But at higher types a function's meaning ranges over all set functions, while (P) covers only machine refinements. The missing step, soundness of symbolic evaluation under set-valued valuations, is not in the dependency graph, and it is as strong as a denotational consistency proof. Separately, the meaning of a codomain at set arguments needs a semantics of terms at non-machine arguments, which the plan never gives; its model sketch covers only the inductive fixed points.
2. **Q3, made concrete (the `J` probe).** `D`'s hypothesis `Eq(Nat → Nat, f0, g0)` is true in the set model, but `f0` and `g0` are not convertible. At that instance the ground run meets `J` at unconvertible endpoints and gets stuck, so soundness clause (i) is false as stated. Under rescue 1, the choice of what an equation's truth means decides this: conversion excludes the instance, while extensional equality keeps the problem.
3. **Q8.** Programs admit a universe at every level (the core syntax has `sort (l : Nat)`), so the plan's model needs infinitely many inaccessibles at once, which Lean cannot supply. But Ochr has no infinitely branching inductives and no inductives above `Type₀`, so it is very plausibly far weaker than Lean. Gödel's theorem blocks this model, not a proof in Lean.
4. **Circularity in the dependency graph.** Q7's invariant must survive refinement, and refinement re-runs sealed programs of checked definitions, blocks of the current definition, and abstract functions refined to closures. That those re-runs return values of their declared readings is subject reduction, which is part of soundness (i). So soundness → Q7 → declared readings → decisions commute → naturality → runs agree → soundness is a cycle; the figure omits the soundness → Q7 edge. It can be resolved only as one simultaneous induction on (definition, entry size, position of the block in the body), with stability proved per index inside it, not standalone "for every reachable state". Closures formed in later definitions and called earlier still need goodness (Q1) to carry it.
5. **Q1's impredicativity worry is misplaced for `Prop`.** Proofs are all `⋆`, so quantification over `Prop` can range over the two truth values. The real problem is a Π over `Type` that lands in `Prop`: in the impredicativity probe, `SelfT := SigP(NoInh)` has good values only if `NoInh` is true, and `NoInh` quantifies over `SelfT`. This needs candidates at `Type₀` (sets of machine values), a standard technique.
6. **Minor.**
   - The injectivity relation is "defined by induction on A", but codomains are computed rather than subterms, so the induction is not well founded, and it is undefined at type variables. It belongs inside the interpretation of types, as a set paired with a subset. (Now open design question Q9 in the plan.)
   - The conversion principle that a constructor value's recorded parameters are never read is not quite what the checker does: `mkEqM` reads them as a fallback (`Machine.lean:1666–1667`). This is harmless, since they are convertible with the type's parameters.
