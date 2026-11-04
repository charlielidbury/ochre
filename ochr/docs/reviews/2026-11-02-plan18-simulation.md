# Referee report on docs/18: the simulation and stability

Attack on the consistency proof plan `ochr/docs/18-consistency-proof-plan.typ`, as it stood on 2026-11-02: the first, 26-page draft, before the set-theory background, the explainer boxes and the notation changes were added. The referee was a fresh, read-only Opus agent (`attack-simulation`), asked to produce a statement of the form "this plan for consistency will never lead to a final proof of consistency because X", where X is a real obstruction rather than a difficulty. Its angle: whether the agreement relation can be maintained step by step, whether naturality up to resolution and the lemmas (P), (C), (Sp) and M are true of the real machine, and whether the open design questions have answers at all. The report arrived in two parts; both are given here, lightly edited.

**Coordinator's note.** The closed proof of `False` below was confirmed independently on main `f5b030d4` (`Bad1` and `Boom` accepted, a control `def Control : False := refl` rejected). It is recorded, unfixed, at the top of `ochr/docs/17-consistency-status.md`.

## 1. The statement

The plan will never lead to a final proof of consistency as written, because the theorem it targets is false for the checker it targets. One of its own premises is false: the "worlds" rule that a split arm may pass on the η-refinements of one-constructor unknowns, because they are "true in every world, following from the type alone" (plan lines 133 and 341). The checker implements that rule (`Env.lean:316`), and it accepts a closed, hole-free proof of `False`.

## 2. The argument

1. **The checker.** `movedPlace` (`Machine.lean:2865–2878`) η-expands an abstract value σ of a one-constructor type to `C(σ₁ … σₖ)`. It computes the fields' types from σ's type *in the current world*, records the expansion in `etaRefs`, and reuses it whenever it finds one there.
2. **What survives an arm.** Leaving an arm (`exitWorld`) keeps `etaRefs` and the types of every unknown created inside the arm (`Env.lean:307–317`).
3. **The leak.** Let σ have type `DP(n)`, where a field's type depends on `n`. An η-expansion made in the arm `n := Z` stores field unknowns typed at `DP(Z)`. In the sibling arm `n := S(m)`, the next expansion of σ reuses that record, so the sibling world holds a field unknown whose recorded type is the other arm's.
4. **Why that is unsound.** The field is dependent, so the dependent-field rules see that its content, an unknown of type `Void`, does not fit the telescope's type `Nat`. They treat the value as open and type the field by its content, `Void`. A zero-arm match on it then proves anything.
5. **Where the plan breaks.**
   - The plan's rule that an arm keeps "the types of abstract values it created (nobody outside can name them)" fails: the kept η-refinement is exactly how code outside the arm names them. So the plan's principle that worlds are exclusive (X1) is violated by the plan's own list of what a world may keep.
   - Case splits commuting with refinement (Sp) is reduced in the plan to (X1)–(X4), and is therefore false. At the instance `n = 1`, `d = MkDP(true, 0, 0)`, no refinement can respect the symbolic state, since the field unknown would need a value of `Void`. So the walk's invariant "α covers and respects the symbolic state" (the definition of a refinement, and agreement clause A9) cannot be maintained at that step.

## 3. Evidence

```
ochr EtaBoom {
  inductive Void : Type
  inductive Bool := false | true
  def G (n : Nat) (b : Bool) : Type := ( match n { Z => Void, S(m) => Nat } )
  inductive DP (n : Nat) := MkDP(x : Bool, y : G(n, x), z : Nat)
  def Eat (k : Nat) : Unit := ()
  def Bad1 (n : Nat) (d : DP(n)) : False := (
    match n {
      Z => ( let u : Unit = match d { MkDP(x, y, z) => Eat(z) };
             match d { MkDP(x, y, z) => match y {} } ),
      S(m) => ( let u : Unit = match d { MkDP(x, y, z) => Eat(z) };
                match d { MkDP(x, y, z) => match y {} } ),
    }
  )
  def Boom : False := Bad1(S(Z), MkDP(true, Z, Z))
}
```

- **Verdicts:** every declaration is ACCEPTED, `Bad1` and `Boom` included. The control `def Control : False := refl` is rejected ("the body of Control has type ⊤, but the goal is False").
- **Against the Lean target.** Evaluating the exact hypotheses of `Ochr.Consistency.consistency` on this program gives `noHoles = true`, `Accepted = true`, and the parameterless definitions of type `False` are `[Boom]`. A scratch file proves `consistency_false`, the negation of the theorem, using `propext`, `Classical.choice`, `Quot.sound` and `native_decide`.
- **The twin.** `NoReuse`, the same program with the first block removed from the `S` arm so that no η-refinement is reused, is rejected with "[Match] on d.y, whose type Nat is not an inductive type". This isolates the cause.
- **The trace.** In `Bad1`'s `S` arm the arm's own split creates σ9–σ11, but the last line reads `[Call-type] G(S(σ8), σ5)`: σ5 is the `x` field created in the `Z` world, so `d` is the record from world `Z`, with `y : Void`.

## 4. Confidence, and what would rescue it

- **Very high** that the Lean target is false for the current checker, and that the plan's stated rule for what a world may keep is false.
- **It does not refute the overall route.** A plausible fix is to restore `etaRefs` when leaving an arm, while still carrying them through private copies (`restoreKeep`), which keeps the reason they were made global: a σ's fields are named the same in every private copy *within one world*. An alternative is to recompute the field types for each world when a stored η-refinement is reused. Neither was tested against the suite, since the referee was read-only.
- **What the plan then needs.**
  - (Sp) proved against the actual keep lists of `exitWorld` and `restoreKeep`, item by item, rather than "a paper argument from (X1)–(X4)".
  - The invariant stated explicitly: nothing a world keeps may name a value created inside the arm, or carry a type computed under the arm's refinement.
  - The same audit for the other kept items. The types of unknowns created in the arm are safe only while nothing kept names them; they also escape through `closeBlock`'s inferred block type when there is no annotation (no exploit found there). The `neutrals` table, which `restoreKeep` keeps. The class cache, keyed by values whose captured unknowns' readings come from world-refined types (the syntactic sort rules appear to block this, but it should be argued). The constant-declaration cache and the [Rec] candidates.
  - `Boom` and `Bad1` registered as `reject` tests, with `NoReuse` as the twin.
- With that done, this counterexample refutes the plan as written (its rule for what a world may keep, and the Lean target for the current checker), but not the route.

## 5. Secondary weaknesses (not obstructions)

1. **N = (P) + (C) + (Sp) is not a complete decomposition.** Some steps look at an unknown without getting stuck or splitting:
   - deciding copy or move from an abstract type: an abstract type is not a copy type, while a type refined to `Unit` or `Bool` copies;
   - η at `Unit` once a type is refined to `Unit`;
   - conversion or `Eq` answering "no" or staying stuck generically, but "yes" or `True` at the instance.

   None of (P), (C), (Sp) covers these, and the plan's list of decisions that must commute omits them (census sites 9, 16, 17 and 19). (P) as literally stated ("leaves the substituted state") is false: generically `x : T` is moved, leaving `⊥`, while at `T := Unit` it is copied. On the heap design every read in polymorphic code consults the type's unknown to decide copy or move, so (P) would not cover any run of a type-generic definition that reads a variable, and neither would (C) or (Sp). The heap slice's proof of (P) was for a slice in which reads copy and moves are not modelled, so it does not touch this. All of this needs a monotonicity argument and an ordering ⊑, which the plan states only for clause A2.
2. **M holds only up to ⊑, not as equality.** Typed runs decide copy or move from the stored type; untyped runs decide it from the value's constructor (46 uses of `valType?`). The untyped run is the more permissive, which is harmless only because the typed check already rejected any second read.
3. **The heap port's prerequisite "every unknown carries a type that refinement never changes" is false** for the field unknowns of value-parameterised types. A field's type such as `G(σ_n, σ_x)` must change when `σ_n` is refined: stuck generically, `Void` in one world, `Nat` in another. If each unknown's type is fixed when it is created, rather than being a heap node a refinement can fill, the heap design builds in this same η bug: a kept fill would carry another world's type by construction.
4. **(Sp) is labelled "paper argument"** but was argued from (X1)–(X4) without being checked against how the kept items interact. That is why the η bug passed the case-splitting and closing-off model lanes and every probe. Each kept item carries its own unproved claim that it holds in every world; those claims are the real content of (Sp), and the plan should list them as open obligations.
