# The mu experiment

## Background: what happened and why we're here

Och previously had two separate self-reference primitives:
- `fix` — general recursion (recursive functions)
- `iota` — self types (dependent elimination)

We discovered these are the same thing. In Och's "terms and types are the
same thing" framework, both express self-reference. The only difference is
how *determined* the self-reference is — and that's already handled by the
concrete/abstract evaluation split. See `docs/ideas/merge-fix-iota.md` for
the full analysis (READ THIS FIRST — it is the design document for this
experiment).

The unified primitive is `mu`:

```lean
| mu : Name → (ann : Expr) → (body : Expr) → Expr
```

`mu (x : T). body` means "the thing being defined can refer to itself as x,
and its annotation is T."

- **Concrete eval:** unroll — `body[x := mu x T body]` (like fix)
- **Abstract eval:** normalize body under binder, return `mu x T' body'` (like iota)
- **Subtyping:** mu-mu compares annotations; self-intro/elim unfold one level

The annotation `T` is load-bearing (not optional): it prevents divergence in
both abstract evaluation and subtype checking. See the "annotation argument"
section of merge-fix-iota.md for why (based on Victor Maia's Kind2 work).

## North Star: abstract appendVec

The goal is getting `appendVec` working end-to-end with **abstract** arguments
(`n : Nat, m : Nat`). Och is useless without this — a type system that can
only verify concrete computations adds nothing over an evaluator.

`appendVec` needs dependent elimination: when you branch on abstract `n : Nat`,
the return type must track which branch was taken (`Array 0 T` vs
`Array (succ k) T`). Self types (via mu) provide this — the return type
becomes `P n`, dependent on the input.

The end state also requires **Scott encoding** (recursive types via nested mu),
which gives O(1) pattern matching and clean separation of concerns. Church
encoding is a stepping stone — simpler to get working first because it avoids
recursive types. But Scott is the target. See `docs/ideas/scott-encoding-fix-iota.md`.

### Intermediate milestone: dependent `add`

Before appendVec, get `add n m` to typecheck with abstract `n : Nat, m : Nat`,
where `Nat` is self-typed Church Nat defined via mu. This is simpler than
appendVec (non-dependent motive, no arrays) but exercises the same core
machinery:

1. mu working as both recursion and self-types
2. Type-directed evaluation in absEval's app case (mu-elim on stuck variables)
3. β-reduction of the motive in types

See the worked example at the bottom of `docs/ideas/merge-fix-iota.md` for
a complete typing derivation of `add`, which identifies exactly what the
evaluator needs.

### Long-term: Scott encoding via recursive types

Once Church + mu is working, the path to Scott encoding is:

1. **Type-level mu** — `mu (T : Type). body` defines a recursive type.
   Abstract eval normalizes the body (doesn't unroll). Self-elim in the
   subtype checker gives one-step equi-recursive unfolding. The mu-mu
   annotation comparison (Victor's trick) prevents divergent unfolding.
2. **Scott-encoded Nat** — `mu (Nat : Type). mu (n : Nat). Π(P:Nat→Type).
   P zero → (Π(k:Nat). P (succ k)) → P n`. Two nested mus: outer for type
   recursion, inner for self-typing.
3. **Full induction via mu-as-fix** — `indNat = mu (ind : ...). lam n.
   n P z (lam k. s k (ind k P z s))`. Scott gives dependent case analysis;
   mu-as-fix adds recursion for full induction.

This should "just work" if mu is implemented correctly, because the same
primitive handles all three levels of self-reference. But it needs
verification. See `docs/ideas/scott-encoding-fix-iota.md` for full analysis.

## Roadmap

### 1. Replace fix+iota with mu in Syntax.lean

Replace the two constructors with one:

```lean
inductive Expr where
  | var  : Name → Expr
  | lam  : Name → (dom : Expr) → (body : Expr) → Expr
  | app  : Expr → Expr → Expr
  | asc  : (term : Expr) → (ty : Expr) → Expr
  | type : Expr
  | mu   : Name → (ann : Expr) → (body : Expr) → Expr
```

Update `subst` and `freeVars` accordingly (mu binds its name in the body,
like iota did, but also carries an annotation like lam's domain).

### 2. Update Eval.lean

**concEval:**
```
| .mu x ann body => concEval fuel (body.subst x (.mu x ann body))  -- unroll
```
Note: this uses substitution (not env extension) because the mu needs to
substitute ITSELF, not a neutral variable. Env extension would lose the
self-reference. This matches how fix currently works (it puts `fix inner`
in the env for `f`). Either approach (subst or env with the mu expression)
should work — use whichever is cleaner.

**absEval:**
```
| .mu x ann body =>
  match absEval fuel ((x, .var x) :: Γ) body with
  | some body' =>
    match absEval fuel Γ ann with
    | some ann' => some (.mu x ann' body')
    | none => none
  | none => none
```
This normalizes the body under the binder (iota behavior) AND normalizes
the annotation.

**App case — mu-elim (the hard part):**
When `absEval(f)` returns a mu (not a lambda), the app case needs to
unfold it:
```
| some (.mu x ann body), some aVal =>
  -- mu-elim: unfold self type, then apply
  let unfolded := body.subst x f_original  -- or (var x), depending on design
  -- unfolded should be a function type (lambda); apply it
  match unfolded with
  | .lam param dom retBody => absEval fuel ((param, aVal) :: Γ) retBody
  | _ => some (.app (.mu x ann body) aVal)  -- still stuck
```

**The context must carry types.** The worked example in merge-fix-iota.md
reveals that when `n` is a neutral variable with type `Nat = mu(...)`,
the app case needs to look up `n`'s TYPE (not just its abstract value) to
do mu-elim. This means the Env type may need to change from
`List (Name × Expr)` to `List (Name × Expr × Expr)` (name, value, type),
or the type information needs to come from somewhere else (e.g., lambda
domain annotations in scope).

This is the single biggest design question. The worked example shows it's
unavoidable. Figure out the cleanest way to thread type information through
absEval.

### 3. Update Subtyping.lean

**Subtype' inductive:**
```
| mu_body : Subtype' body₂ body₁ → Subtype' (.mu x ann body₂) (.mu x ann body₁)
```

**subCheckNF:**
```
| .mu x annA bodyA, .mu y annB bodyB =>
  -- Compare annotations (Victor's trick — avoids divergent unfolding)
  let bodyB' := if x == y then bodyB else bodyB.subst y (.var x)
  subCheckNF fuel ((x, .mu x annA bodyA) :: ctx) annA annB
  -- Optionally also check bodies covariant, or just use annotations
| a, .mu x ann body =>
  -- Self-intro: unfold, check a ⊑ body[x := a]
  subCheckNF fuel ctx a (body.subst x a)
| .mu x ann body, b =>
  -- Self-elim: unfold, check body[x := mu x ann body] ⊑ b
  subCheckNF fuel ctx (body.subst x (.mu x ann body)) b
```

**inferType:** Handle mu in function position (mu-elim to get function type).

### 4. Update Tests.lean

All existing `.fix` uses become `.mu` with appropriate annotations.
All existing `.iota` uses become `.mu` with appropriate annotations.

The fix translation is mechanical: `fix (lam f T body)` → `mu f T body`.
The iota translation adds an annotation: `iota x body` → `mu x ann body`
where `ann` needs to be determined (often the mu type itself, or Type).

**All existing tests must still pass.** The tests pin expressiveness.

### 5. Update proof files (Soundness.lean, Monotonicity.lean, Closure.lean)

Replace fix/iota cases with mu cases throughout. Many proofs will break.
Use `sorry` freely — the goal is to get `lake build` compiling, not to
re-prove everything immediately.

**Delete SoundnessS.lean** — it was stalled with 7 sorrys and is superseded.

Closure.lean is substantial (~1000+ lines). Use judgment on whether to adapt
it or remove it and rebuild later. Either is fine.

### 6. Prove soundness and monotonicity for mu

Once the syntax/eval/subtyping changes are stable and tests pass, the proofs
need to be redone. The mu case in soundness should combine the old fix case
(concrete unrolls, abstract returns annotation) with the old iota case
(normalize body under binder).

### 7. Type-directed evaluation for abstract appendVec

With mu working, tackle the stuck-application problem: when `n : Nat` is
abstract and applied to arguments, the evaluator needs mu-elim to discover
the function type. This requires the env to carry type information (see
roadmap item 2).

### 8. Dependent Nat and add

Define self-typed Nat with mu, prove `add` typechecks with abstract
arguments. This is the concrete validation of the whole approach. See the
worked example in merge-fix-iota.md for what the definitions and typing
derivation look like.

### 9. Recursive types

With mu handling both recursion and self-types, type-level recursion should
come "for free" — `mu T Type body` defines a recursive type. The self-elim
subtyping rule gives one-step equi-recursive unfolding. The mu-mu annotation
comparison (Victor's trick) prevents divergent unfolding. Verify this works
and move the standard library to Scott encoding.

## Design principles for this experiment

- **One primitive for self-reference.** If you find yourself wanting to add
  a second self-reference mechanism, stop and think about whether mu can do
  it. The whole point is that concrete/abstract evaluation provides the
  distinction.

- **The annotation is load-bearing.** Don't drop it or make it optional. It
  prevents divergence in both absEval and subtype checking.

- **Tests are sacred.** The existing test suite pins expressiveness. All
  tests must pass after the syntax change (adapted for mu syntax). Don't
  weaken tests.

- **Sorry freely, compile always.** `lake build` must pass. Use sorry for
  broken proofs. A compiling codebase with sorrys is infinitely more useful
  than a broken one.

- **Read merge-fix-iota.md.** It is the design document. The worked example
  at the bottom is especially important — it shows exactly what the typing
  rules need to look like and what the evaluator must do.
