# Lemma (S-Eval)

**Statement.**
If `Γ ⊢ M ⇒ M'`, then `Γ ⊢ M ⊑ M'`.

**Intuition.** A term is at least as precise as its abstract evaluation.
Typing can only lose precision (via ascription), so the raw term should
always be a subtype of its type.

**Proof attempt.** By induction on the derivation of `Γ ⊢ M ⇒ M'`.

---

## Case T-Top

```
Γ ⊢ ⊤ ⇒ ⊤
```

Goal: `Γ ⊢ ⊤ ⊑ ⊤`
  by S-Refl ✓

---

## Case T-Var

```
x: A ∈ Γ
──────────
Γ ⊢ x ⇒ A
```

Goal: `Γ ⊢ x ⊑ A`
  by S-Var, need:
  1. `x: A ∈ Γ`
     Given ✓
  2. `Γ ⊢ A ⊑ A`
     by S-Refl ✓

---

## Case T-Fun

```
────────────────────────────────
Γ ⊢ (x: A) → M ⇒ (x: A) → M
```

Goal: `Γ ⊢ (x: A) → M ⊑ (x: A) → M`
  by S-Refl ✓

---

## Case T-App-Top

```
Γ ⊢ M ⇒ ⊤
──────────────
Γ ⊢ M N ⇒ ⊤
```

Goal: `Γ ⊢ M N ⊑ ⊤`
  by S-Top ✓

---

## Case T-App

```
Γ ⊢ M ⇒ (x: A) → B
Γ ⊢ N ⇒ N'
Γ ⊢ N' ⊑ A
Γ ⊢ B[x ≔ N'] ⇒ R
────────────────────
Γ ⊢ M N ⇒ R
```

Goal: `Γ ⊢ M N ⊑ R`

By the induction hypothesis applied to each premise:
- IH on premise 1: `Γ ⊢ M ⊑ (x: A) → B`
- IH on premise 2: `Γ ⊢ N ⊑ N'`
- IH on premise 4: `Γ ⊢ B[x ≔ N'] ⊑ R`

**STUCK.** The subtyping rules have no way to derive `M N ⊑ R` (or
`M N ⊑ anything` non-trivially) for an application term `M N`.

The available subtyping rules that could apply to `M N` on the left are:
- **S-Top**: gives `M N ⊑ ⊤`, but R is not necessarily ⊤.
- **S-Refl**: gives `M N ⊑ M N`, but R is not syntactically `M N`.
- **S-Trans**: requires an intermediate term B such that `M N ⊑ B` and
  `B ⊑ R`, but we have no rule to derive `M N ⊑ B` for any useful B.

There is no **S-App** rule that decomposes application on the left of ⊑.
Unlike functions (which have S-Fun), applications are opaque to subtyping.

This is by design: subtyping is a structural relation on *values/types*,
and `M N` is a computation, not a value. After evaluation, `M N` would
reduce to a value that subtyping can handle. But the lemma asks about
the raw, unevaluated term `M N`.

---

## Case T-Asc

```
Γ ⊢ M ⇒ M'
Γ ⊢ A ⇒ A'
Γ ⊢ M' ⊑ A'
─────────────────
Γ ⊢ (M : A) ⇒ A'
```

Goal: `Γ ⊢ (M : A) ⊑ A'`

By the induction hypothesis:
- IH on premise 1: `Γ ⊢ M ⊑ M'`
- IH on premise 2: `Γ ⊢ A ⊑ A'`

We have `Γ ⊢ M ⊑ M'` and `Γ ⊢ M' ⊑ A'` (the latter is premise 3).
By S-Trans: `Γ ⊢ M ⊑ A'`.

But the goal is `Γ ⊢ (M : A) ⊑ A'`, not `Γ ⊢ M ⊑ A'`.

**STUCK.** The subtyping rules have no way to derive `(M : A) ⊑ A'` for
an ascription term `(M : A)` on the left.

The available rules that could apply to `(M : A)` on the left are:
- **S-Top**: gives `(M : A) ⊑ ⊤`, but A' is not necessarily ⊤.
- **S-Refl**: gives `(M : A) ⊑ (M : A)`, but A' is not syntactically `(M : A)`.
- **S-Trans**: same problem — no rule produces `(M : A) ⊑ B` for useful B.

There is no **S-Asc** rule that decomposes ascription on the left of ⊑.

---

## Summary of Stuck Cases

The lemma **cannot be proved** from the existing subtyping rules. Two cases
are stuck:

| Case | Goal | Blocked because |
|------|------|-----------------|
| T-App | `Γ ⊢ M N ⊑ R` | No subtyping rule decomposes application |
| T-Asc | `Γ ⊢ (M : A) ⊑ A'` | No subtyping rule decomposes ascription |

Both failures share the same root cause: subtyping is defined structurally
over values (⊤, variables, functions), but application and ascription are
*computations* — they are eliminated by evaluation, not by subtyping.

---

## Proposed Fix: New Subtyping Rules

To make S-Eval provable, we would need rules that allow subtyping to "see
through" computations. Two candidate rules:

### Candidate Rule: S-App

```
[S-App]
Γ ⊢ M ⊑ (x: A) → B
Γ ⊢ N ⊑ N'
Γ ⊢ N' ⊑ A
Γ ⊢ B[x ≔ N'] ⊑ R
────────────────────
Γ ⊢ M N ⊑ R
```

This essentially embeds typing (T-App) into subtyping. It says: "if we can
type-check the application and the result is R, then the application is at
least as precise as R."

### Candidate Rule: S-Asc

```
[S-Asc]
Γ ⊢ M ⊑ A
Γ ⊢ A ⊑ B
────────────────
Γ ⊢ (M : A) ⊑ B
```

This says: "an ascription `(M : A)` is at least as precise as anything A
is at least as precise as, provided M actually satisfies A." This treats
ascription as transparent — the ascription contributes A's precision.

A simpler variant:

```
[S-Asc-simple]
Γ ⊢ A ⊑ B
────────────────
Γ ⊢ (M : A) ⊑ B
```

This ignores M entirely and just uses the ascription target. This is
simpler but discards information about M.

---

## Risk Analysis: Could These Rules Break Monotonicity?

The monotonicity counterexample (from `och.md` and `och-sharp-edges.md`)
relies on being able to derive `False ⊑ b` where `b: Bool`. This lets
`False : b` type-check under T-Asc, and then narrowing `b` to `True`
breaks monotonicity.

### S-Asc and the counterexample

S-Asc does NOT enable the counterexample. The dangerous term is `False : b`.
Under T-Asc, we need `Γ ⊢ False ⊑ b'` where `b'` is the evaluation of `b`.
S-Asc is about *ascription terms on the left of ⊑*, i.e., `(M : A) ⊑ B`.
It does not help derive `False ⊑ b` because `False` is not an ascription
term — it is a function literal. The counterexample remains blocked by
the one-directional nature of S-Var.

### S-App and the counterexample

S-App also does NOT directly enable the counterexample. The dangerous
judgment `False ⊑ b` requires `b` or a variable on the right side of ⊑.
S-App puts an *application* on the left. The counterexample term `False`
is a function literal, not an application. So S-App does not help derive
`False ⊑ b`.

### Broader concerns

Adding S-App embeds typing logic into subtyping, which creates a
circularity concern: subtyping already appears in typing (T-App premise 3,
T-Asc premise 3), and now typing would appear in subtyping. This does not
immediately create a logical cycle (the induction measure still decreases
on term size), but it significantly complicates the metatheory:

1. **Substitution lemmas** for subtyping become harder because S-App
   introduces substitution into subtyping derivations.
2. **Decidability** of subtyping becomes tied to decidability of typing.
3. **Transitivity elimination** (if desired) becomes much more complex.

S-Asc is less dangerous — it only adds a structural decomposition for a
syntax form, similar to how S-Fun decomposes functions.

---

## Alternative: Add S-Eval Directly as an Axiom

Instead of adding structural rules for each computation form, add S-Eval
itself as a subtyping rule:

```
[S-Eval]
Γ ⊢ M ⇒ M'
────────────
Γ ⊢ M ⊑ M'
```

This is the most direct fix. It says: "a term is at least as precise as
its type." This is conceptually sound — abstract evaluation only loses
precision.

**Pros:**
- Closes both stuck cases at once.
- Conceptually clean: terms are more precise than their types.
- Does not require separate S-App and S-Asc rules.

**Cons:**
- Embeds the entire typing judgment into subtyping, making subtyping
  at least as complex as typing.
- Every property of subtyping (weakening, substitution, transitivity)
  now needs the corresponding property of typing as a dependency.
- The lemma we were trying to prove (S-Eval) becomes an axiom — we are
  no longer proving it, we are assuming it. Its soundness is then
  justified by the intuition that "typing only loses precision," which
  is what we wanted to prove in the first place.

**Risk for monotonicity:** S-Eval as a rule lets us derive `M ⊑ M'`
whenever `Γ ⊢ M ⇒ M'`. Could this derive `False ⊑ b`? Only if there
exists a typing derivation `Γ ⊢ False ⇒ b`. But False is a function
literal, and T-Fun gives `Γ ⊢ False ⇒ False`, not `Γ ⊢ False ⇒ b`.
No typing rule produces a variable as the type of a function literal.
So **S-Eval does not enable the monotonicity counterexample**.

---

## Conclusion

**The lemma S-Eval cannot be proved from the existing Och₀ subtyping rules.**

The proof succeeds for T-Top, T-Var, T-Fun, and T-App-Top, but gets stuck
on T-App and T-Asc because subtyping has no structural rules for
application or ascription terms.

Three possible remedies, in order of recommendation:

1. **Add S-Eval as a subtyping rule (axiom).** Cleanest conceptually, but
   makes subtyping depend on typing. Does not break monotonicity.

2. **Add S-Asc only.** Fixes the T-Asc case. The T-App case would still
   require either S-App or S-Eval. S-Asc alone is insufficient.

3. **Add both S-App and S-Asc.** Fixes both cases structurally, but
   S-App significantly complicates the metatheory by embedding typing
   logic into subtyping.

If S-Eval is added as an axiom, the proof becomes:

### Revised proof with S-Eval as axiom

Every case is immediate: given `Γ ⊢ M ⇒ M'`, apply S-Eval to get
`Γ ⊢ M ⊑ M'`. The lemma is the rule itself. The real question then
becomes: **is S-Eval consistent with the rest of the system?** That is,
does adding it preserve soundness and monotonicity? The analysis above
suggests it does not enable the known monotonicity counterexample, but a
full proof of soundness with S-Eval in the system would need to verify
that all subtyping lemmas (weakening, substitution, transitivity) still
hold with the new rule.
