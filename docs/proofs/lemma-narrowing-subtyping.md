# Lemma (Narrowing Preserves Subtyping)

**Statement.**
If `Gamma |- A <: B` and `Gamma' <: Gamma` (pointwise: for each `x: D in Gamma`, there exists `x: D' in Gamma'` with `Gamma' |- D' <: D`), then `Gamma' |- A <: B`.

**Mutual dependency.** This lemma has a mutual dependency with typing monotonicity through S-Eval. The S-Eval case of this proof invokes typing monotonicity, and the T-Asc case of typing monotonicity invokes this lemma. The full argument requires a combined/mutual induction, where the measure is the total derivation size. This works because:

- S-Eval invokes typing monotonicity on the typing derivation `Gamma |- M => M'`, which is strictly smaller than the S-Eval derivation that contains it.
- T-Asc invokes narrowing on the subtyping derivation `Gamma |- M' <: A_0`, which is strictly smaller than the T-Asc derivation that contains it.

So the combined measure (total derivation size) strictly decreases at every mutual call, and the induction is well-founded.

**Proof.** By induction on the derivation of `Gamma |- A <: B`, with the understanding that typing monotonicity is proved simultaneously by mutual induction.

---

## Case S-Top

```
Gamma |- M <: top
```

Goal: `Gamma' |- M <: top`
  by S-Top ✓

(S-Top applies to any term on the left in any environment.)

---

## Case S-Refl

```
Gamma |- M <: M
```

Goal: `Gamma' |- M <: M`
  by S-Refl ✓

---

## Case S-Trans

```
Gamma |- A <: H    Gamma |- H <: C
────────────────────────────────────
         Gamma |- A <: C
```

Goal: `Gamma' |- A <: C`
  by S-Trans, need:
  1. `Gamma' |- A <: H`
     by induction hypothesis on the first premise ✓
  2. `Gamma' |- H <: C`
     by induction hypothesis on the second premise ✓

---

## Case S-Var

```
x: D in Gamma    Gamma |- D <: B
─────────────────────────────────
        Gamma |- x <: B
```

Goal: `Gamma' |- x <: B`

By `Gamma' <: Gamma` (pointwise), from `x: D in Gamma` we get:
  `x: D' in Gamma'`  with  `Gamma' |- D' <: D`    — (*)

By induction hypothesis on the second premise:
  `Gamma' |- D <: B`                                 — (**)

By S-Trans on (*) and (**):
  `Gamma' |- D' <: B`

By S-Var using `x: D' in Gamma'` and `Gamma' |- D' <: B`:
  `Gamma' |- x <: B` ✓

---

## Case S-Fun

```
Gamma |- B_1 <: A_1    Gamma, x: B_1 |- M_1 <: M_2
─────────────────────────────────────────────────────
    Gamma |- (x: A_1) -> M_1 <: (x: B_1) -> M_2
```

Goal: `Gamma' |- (x: A_1) -> M_1 <: (x: B_1) -> M_2`

By S-Fun, need:

1. `Gamma' |- B_1 <: A_1`
   by induction hypothesis on the first premise ✓

2. `Gamma', x: B_1 |- M_1 <: M_2`

   The extended environment `(Gamma', x: B_1)` is pointwise narrower than
   `(Gamma, x: B_1)`:
   - For all `y: D in Gamma`, we have `y: D' in Gamma'` with
     `Gamma' |- D' <: D` (by `Gamma' <: Gamma`), which gives
     `Gamma', x: B_1 |- D' <: D` (by weakening with `x: B_1`).
   - For `x: B_1`, we have `x: B_1 in (Gamma', x: B_1)` with
     `Gamma', x: B_1 |- B_1 <: B_1` (by S-Refl).

   So `(Gamma', x: B_1) <: (Gamma, x: B_1)` pointwise.

   By induction hypothesis on the second premise:
     `Gamma', x: B_1 |- M_1 <: M_2` ✓

---

## Case S-App

```
Gamma |- M_1 <: M_2    Gamma |- N_1 <: N_2
────────────────────────────────────────────
       Gamma |- M_1 N_1 <: M_2 N_2
```

Goal: `Gamma' |- M_1 N_1 <: M_2 N_2`
  by S-App, need:
  1. `Gamma' |- M_1 <: M_2`
     by induction hypothesis on the first premise ✓
  2. `Gamma' |- N_1 <: N_2`
     by induction hypothesis on the second premise ✓

---

## Case S-Asc

```
Gamma |- M_1 <: M_2    Gamma |- A_1 <: A_2
────────────────────────────────────────────
     Gamma |- (M_1 : A_1) <: (M_2 : A_2)
```

Goal: `Gamma' |- (M_1 : A_1) <: (M_2 : A_2)`
  by S-Asc, need:
  1. `Gamma' |- M_1 <: M_2`
     by induction hypothesis on the first premise ✓
  2. `Gamma' |- A_1 <: A_2`
     by induction hypothesis on the second premise ✓

---

## Case S-Eval

```
Gamma |- M => M'
─────────────────
Gamma |- M <: M'
```

Goal: `Gamma' |- M <: M'`

This is the case that creates the mutual dependency with typing monotonicity.

By typing monotonicity (mutual IH) applied to `Gamma |- M => M'`:
  `Gamma' |- M => M''`  with  `Gamma' |- M'' <: M'`    — (*)

Note: this invocation is valid because the typing derivation `Gamma |- M => M'`
is strictly smaller than the S-Eval derivation that wraps it, so the combined
measure decreases.

By S-Eval applied to `Gamma' |- M => M''`:
  `Gamma' |- M <: M''`                                    — (**)

By S-Trans on (**) and (*):
  `Gamma' |- M <: M'` ✓

---

**QED.** All cases are discharged; the lemma holds by mutual induction with typing monotonicity, where the combined measure is the total derivation size. ∎
