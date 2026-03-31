# Body Anti-Monotonicity (Prop 5.2.9)

## The Problem

```
Not = λ(X:Bool). X Bool false true
g = λ(B:Bool). (Not B : B)
```

Under B:Bool: `Not Bool =β Bool`. Check `Bool ⊑ Bool`. ✓
Under B:true: `Not true =β false`. Check `false ⊑ true`. ✗

Narrowing B breaks the ascription check because `Not` is anti-monotone:
narrower input → wider output.

## Precise Analysis

`Not` maps: `true ↦ false`, `false ↦ true`, `Bool ↦ Bool`.

As a function on the subtyping lattice:
```
true ⊑ Bool  and  false ⊑ Bool  (both are elements of Bool)
```

`Not true = false ⊑ Bool = Not Bool`. So `Not true ⊑ Not Bool`. ✓ (monotone)
`Not false = true ⊑ Bool = Not Bool`. So `Not false ⊑ Not Bool`. ✓ (monotone)

Wait — this says `Not` IS monotone! Narrowing from Bool to true gives
`false ⊑ Bool`. What fails is `false ⊑ true` — comparing `Not B` to `B`
(not to `Not Bool`).

The anti-monotonicity is NOT in `Not` alone — it's in the comparison
`Not B ⊑ B` where BOTH sides depend on B:
- LHS `Not B`: anti-monotone in B (true→false, false→true)
- RHS `B`: monotone in B (trivially, identity)

The COMPARISON `Not B ⊑ B` is anti-monotone because the LHS and RHS move
in opposite directions.

## Reframing: The Issue is Mixed Polarity in Ascription

The ascription `(e : τ)` checks `e ⊑ τ`. Both `e` and `τ` may depend on
context variables. The check is preserved under narrowing iff:
- `e` gets narrower (⊑) — i.e., e is monotone in the context — AND
- `τ` gets wider (⊒) — i.e., τ is anti-monotone in the context — OR
- They move in the same direction and the gap is preserved

For `(Not B : B)`:
- `Not B` is anti-monotone in B: true → false (widens when B narrows)
- `B` is monotone in B: Bool → true (narrows when B narrows)

LHS widens while RHS narrows → gap can close and invert. Anti-monotone check.

## General Condition for Ascription Safety

`(e : τ)` is safe (preserved under context narrowing) when:
For all Γ₂ ⊑ Γ₁: if `Γ₁ ⊢ eΓ₁ ⊑ τΓ₁`, then `Γ₂ ⊢ eΓ₂ ⊑ τΓ₂`.

This holds when:
1. `τ` is context-independent (closed type) — then τΓ₂ = τΓ₁ and
   monotonicity of e gives eΓ₂ ⊑ eΓ₁ ⊑ τΓ₁ = τΓ₂. ✓
2. `e` and `τ` are both monotone and `τ` is "wider" — but this doesn't
   guarantee the gap is preserved.
3. The check is structurally preserved (each sub-check is monotone).

## How Other Systems Handle This

### System F / Hindley-Milner
No dependent types, so τ doesn't depend on context variables. Case 1
always applies. No issue.

### Coq / Agda / Lean
Dependent types exist, but subtyping is essentially equality (conversion).
The "check" is `e : τ` (typing), not `e ⊑ τ` (subtyping). With cumulativity,
there's a limited subtyping (Prop ⊑ Type), but nothing as rich as Och's
semantic subtyping. The Prop 5.2.9 issue doesn't arise because there's no
general subtyping relation that can be anti-monotone.

### Refinement Types (Liquid Haskell)
Refinement types have `{x:B | p(x)}`. The subtyping check is
`{x:B | p₁(x)} ⊑ {x:B | p₂(x)}` iff `∀x. p₁(x) ⟹ p₂(x)`. This is
an implication check, not a semantic inclusion. Anti-monotonicity can
arise in the refinement predicates, but the base types don't change, so
the structural checks are simpler.

### Semantic Subtyping (Castagna, Frisch)
Semantic subtyping uses set-theoretic models. Functions are typed by their
behavior on ALL inputs. Anti-monotonicity doesn't arise because subtyping
is defined semantically (set inclusion) and the evaluation model is fixed.

In Och, the issue arises because abstract evaluation is INTENSIONAL
(depends on the syntactic form, including domain annotations) rather than
purely EXTENSIONAL (behavior on inputs).

## Possible Resolutions

### Resolution 1: Restrict Ascription Targets

Only allow `(e : τ)` when `τ` is context-independent (no free variables
from Γ in τ, or τ is in a "stable" fragment).

This would reject `(Not B : B)` because `B` appears in the target.

But this also rejects useful patterns like:
```
f = λ(T:Type). λ(x:T). (x : T)
```

Here `T` appears in the target, but the check `x ⊑ T` is trivially
monotone (both sides are just `T`). So this restriction is too broad.

A refined version: allow `τ` to reference context variables only if the
LHS `e` is "monotone relative to τ." But formalizing "monotone relative to"
is the whole problem.

### Resolution 2: Check Ascription at the Widest Level Only

The Lam rule checks the body at the declared domain. If an ascription check
passes there, DON'T re-check at narrower domains. This is what the current
system does (Lam checks once). The question is: does the wider check
guarantee safety for all narrower inputs?

For `g = λ(B:Bool). (Not B : B)`:
At B:Bool: `Not Bool ⊑ Bool` ✓. Check passes.
At runtime, B is concrete (true or false). Concrete eval: `(Not B)` =
`Not true = false` or `Not false = true`. Ascription erased, so we get the
raw `Not B` value. This is a valid Bool. So soundness holds! The runtime
value IS in Bool.

The issue is: is the runtime value in `B` (the NARROW type)?
- B=true: Not true = false. Is false ⊑ true? NO. The runtime value is
  false, which is not in {true}.

But wait — soundness (as we stated it) says `v ⊑ τγ` where τ is the
ABSTRACT type from the CHECK (at the wide level), not from re-evaluation
at the narrow level.

The abstract evaluation at `B:Bool` gives `g ⇝ λ(B:Bool).(Not B : B)` by
Lam (body evaluates to B via Asc). So the TYPE of `g B` for abstract B:Bool
is `B` — which, after applying γ with B:=true, gives `true`.

But the concrete value is `false`! So soundness says `false ⊑ true` —
which is FALSE. **Soundness fails for this example.**

### Wait — Let Me Recheck

`g = λ(B:Bool). (Not B : B)`

Abstract eval of `g`:
```
Lam: g ⇝ λ(B:Bool). (Not B : B) = g
```
The Lam rule returns the lambda itself. The well-formedness check evaluates
the body under B:Bool:
```
B:Bool ⊢ Not B ⇝ ?
  Not ⇝ Not (Lam)
  B ⇝ Bool (Var)
  Not Bool ⇝ Bool (App, β-reduce)
B:Bool ⊢ (Not B : B) ⇝ B (Asc: Bool ⊑ B? No — B ⊑ Bool by Var but Bool ⊑ B?)
```

Hmm, the Asc rule checks `σ ⊑ τ` where σ is the abstract eval of `Not B`
and τ is B. Under B:Bool: σ = Bool, τ = Bool. `Bool ⊑ Bool` ✓.

But wait — `τ` in the Asc rule is the syntactic target. `(Not B : B)` has
target `B`. Under abstract evaluation, `B ⇝ Bool` (Var). So the Asc check
is `Bool ⊑ Bool` ✓.

Then the Asc result is `B` (the syntactic target). In the context B:Bool,
this is `Bool`.

Now `g true`:
```
g ⇝ g = λ(B:Bool).(Not B : B)
true ⇝ true
true ⊑ Bool ✓
body[B:=true] = (Not true : true) = (false : true)
```
Now abstract eval of `(false : true)`:
```
false ⇝ false
false ⊑ true? ✗
```

**The ascription check fails at application time!** When we apply `g` to
`true`, the App rule substitutes `true` for `B` in the body, getting
`(Not true : true)`, and the Asc rule checks `false ⊑ true`, which fails.

So `g true` is not well-typed. The type system REJECTS this application.

**This is correct behavior!** The function `g` promises `(Not B : B)` — the
output is ⊑ B. For B = true, it would need to return something ⊑ true. But
`Not true = false`, and `false ⋢ true`. So `g` can't deliver on its promise
for B = true.

The issue for monotonicity is: `g` type-checks under B:Bool (wide), but the
body doesn't type-check under B:true (narrow). Monotonicity says: if it
type-checks under the wide context, it should type-check under narrow contexts.
It doesn't.

But does this affect SOUNDNESS? If `g true` is rejected (not well-typed),
then there's no typing judgment to be unsound about. The system correctly
prevents you from calling `g` with a precise boolean.

### What If g Is Called with Abstract B?

`g` is well-typed when called with abstract `B:Bool`:
```
g Bool ⇝ (Not Bool : Bool) = Bool[B:=Bool] = Bool
```

Wait, `g ⇝ λ(B:Bool).(Not B : B)`. App with B = Bool (the TYPE Bool):

`g Bool ⇝ body[B:=Bool] = (Not Bool : Bool) ⇝ Bool` (Asc: Bool ⊑ Bool ✓).

So `g Bool ⇝ Bool`. The result is `Bool`.

Concrete evaluation: `g` applied to some concrete boolean, say `true`:
`g true = (Not true : true)` — but the CONCRETE evaluator erases ascription:
`(Not true : true) ⟶ Not true ⟶ false`.

So `v = false`. And `τγ = Bool` (abstract type, substituting γ(B)=true into
the abstract result Bool). `false ⊑ Bool` ✓. **Soundness holds!**

The key: the abstract evaluation at B:Bool gives `Bool` (the wide type), and
ANY concrete boolean is ⊑ Bool. So soundness is not violated.

### Monotonicity Failure vs Soundness

The monotonicity failure for `g` is:
- Under B:Bool: `g B ⇝ Bool`
- Under B:true: `g B` FAILS TO TYPE-CHECK (Asc check fails)

This is a failure of MONOTONICITY: the term doesn't type-check under the
narrow context. But it's NOT a failure of SOUNDNESS: the typing judgment at
the wide level correctly over-approximates the concrete behavior.

**Monotonicity failure means: you can't call `g` with a precise type.**
But `g` with abstract B:Bool works fine, and soundness holds for any
concrete instantiation of B:Bool.

### Does This Matter for Ochre?

For Ochre's strong mutation:
```
let B : Bool = true;
let result = g B;     -- type: (Not B : B) = (Not true : true) — TYPE ERROR
```

After the mutation `B = true`, the type checker re-evaluates `g B` with
the precise type B:true. The ascription check `Not true ⊑ true` fails.
The type checker rejects this program.

**This is a FALSE POSITIVE.** The runtime value of `result` is `false`,
which is a perfectly valid `Bool`. The type error is spurious — it arises
because the type checker tries to re-verify the body with the precise
type, and the body's ascription is too tight.

For Ochre, this means: after strong mutation (B narrowed to true), some
previously-valid expressions become ill-typed. This is the "invalidation"
that monotonicity was supposed to prevent.

But the FALSE POSITIVE is SAFE. The type checker is overly conservative,
not unsound. It rejects programs that would be safe to run. This is
annoying but not dangerous.

**The question becomes: is the false positive rate acceptable?**

For the specific pattern `(anti-monotone-expr : dependent-type)`, the
answer depends on how often this arises in real code. In most code,
ascription targets are either:
- Closed types (`Nat`, `Bool`) — no issue
- Simple type variables (`T`) — monotone, no issue
- Computed types (`Array n T`) — monotone in all arguments, no issue

The anti-monotone pattern (`Not B : B`) is contrived. It requires the LHS
to use the type variable in a way that inverts it, AND the RHS to be the
same variable. This is rare in practice.

## Conclusion

Body anti-monotonicity (Prop 5.2.9) causes:
1. **Monotonicity failure**: terms can type-check at the wide level but
   fail at narrow levels. This is REAL.
2. **No soundness failure**: the wide-level type correctly over-approximates
   the concrete behavior. Soundness is preserved.
3. **False positives for Ochre**: after strong mutation, some expressions
   become ill-typed even though they'd be safe. This is SAFE but annoying.

**The practical impact is small.** The anti-monotone pattern is rare in real
code. Most ascriptions use closed or monotone types.

## Does Soundness Require Monotonicity?

### The Optimistic Argument

For `g B` under B:Bool: the abstract type is Bool (from the wide evaluation).
Any concrete boolean is ⊑ Bool. So soundness holds without re-checking at
narrow levels.

### Why It's Not That Simple

The soundness proof's App case needs to connect the concrete sub-evaluation
to the abstract type:

```
body_c[x:=v_a] ⇓ v     (concrete: use true as argument)
bodyγ[x:=a'γ] = Bool    (abstract: use Bool as argument)
Need: v ⊑ Bool
```

We can show v ⊑ absEval(body_c[x:=v_a]) by the **simulation argument**:
abstract evaluation of a closed term always produces something ⊒ the concrete
value, because at each ascription node, abstract takes the wider rhs.

But absEval(body_c[x:=v_a]) might be UNDEFINED (Asc check fails for the
narrow term `(false : true)`). So the simulation argument doesn't apply to
body_c[x:=v_a] directly when it contains a failing ascription.

However: concrete evaluation IGNORES ascription types. So even though
absEval(body_c[x:=v_a]) fails, concreteEval(body_c[x:=v_a]) succeeds.
The concrete value `false` is perfectly fine — it's just that we can't
invoke the IH on a term that doesn't type-check.

### The Simulation Argument for Concrete Evaluation

**Key property:** For any closed term e where concrete evaluation erases
ascriptions: if each ascription (e':τ) in e has concreteEval(e') ⊑ τ
(the concrete value of the lhs is in the abstract type of the rhs), then
concreteEval(e) ⊑ absEval(e).

This works because:
- β-reduction is the same in both modes
- At ascriptions, concrete takes lhs and abstract takes rhs
- The Asc check guarantees lhs ⊑ rhs AT THE WIDE LEVEL

But the Asc check at the NARROW level might fail. And we need the check
AT THE NARROW level (after substituting the concrete argument) to invoke
the simulation.

This is where monotonicity sneaks back in: we need the Asc check to be
preserved under substitution of narrower values.

### Conclusion: Soundness DOES Require Some Form of Monotonicity

The App case requires bridging from `body[x:=v_concrete]` to
`body[x:=a'_abstract]`. This bridge is a form of monotonicity:
- Same body, different arguments (v ⊑ a')
- Need: evaluation with narrower argument gives result ⊑ evaluation with wider argument

**Without monotonicity, the soundness proof is stuck.** However, runtime
subtyping (⊑ᵣ, with domain erasure) IS monotone. So:

**Behavioral soundness** (v ⊑ᵣ τ) CAN be proved using runtime subtyping
and its monotonicity. This gives a meaningful guarantee: runtime values
behave consistently with abstract types, modulo domain annotations.

**For the Och mechanization:** Accept that:
1. Full syntactic monotonicity fails
2. Runtime monotonicity holds (domain-erased)
3. Behavioral soundness (v ⊑ᵣ τ) is provable
4. Full syntactic soundness (v ⊑ₛ τ) is open

**For Ochre:** When implementing strong mutation, accept that narrowing can
invalidate some typing judgments. Handle this by either:
- Re-checking and reporting errors (conservative, no unsoundness)
- Not re-checking bodies that passed at the wide level (optimistic, relies
  on behavioral soundness)
- Adding a monotonicity annotation/check that flags anti-monotone ascriptions
