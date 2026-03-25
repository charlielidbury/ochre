# Soundness & Monotonicity Proof — Decomposition Plan

## Task DAG

### Layer 0 — No dependencies, fully parallel (9 tasks)

| # | Task | Context needed |
|---|------|---------------|
| 1 | **Lemma: Weakening** | Subtyping rules only |
| 2 | **Lemma: Equal Substitution** | Subtyping rules only |
| 3 | **Lemma: S-Eval** (key conjecture) | Typing + subtyping rules. May conclude a new rule is needed |
| 4 | **Soundness: T-Top case** | Typing + eval + subtyping rules, assume IH |
| 5 | **Soundness: T-Var case** | Same |
| 6 | **Soundness: T-Fun case** | Same (this is where E-Fun erasure matters) |
| 7 | **Soundness: T-App-Top case** | Same (trivial — everything ⊑ ⊤) |
| 8 | **Soundness: T-Asc case** | Same + S-Trans |
| 9 | **Monotonicity: easy cases (T-Top, T-Var, T-Fun, T-App-Top, T-Asc)** | Typing + subtyping rules, assume IH |

Tasks 4-8 are individually tiny (1-5 lines), but keeping them separate
means each agent needs zero awareness of the others. Monotonicity easy
cases (task 9) are grouped since they're symmetric to their soundness
counterparts and all straightforward.

### Layer 1 — Depends on lemmas 1-3 being correctly stated (2 tasks, parallel with each other)

| # | Task | Depends on | Context needed |
|---|------|-----------|---------------|
| 10 | **Soundness: T-App case** | 1, 2, 3 (statements) | All rules + lemma statements + monotonicity IH |
| 11 | **Monotonicity: T-App case** | 1, 2, 3 (statements) | All rules + lemma statements + soundness IH |

These are the hard cases. Each assumes the IH of *both* theorems (mutual
induction) and uses the lemmas. They're parallel with each other because
mutual induction means each just assumes the other's IH — neither needs
the other's completed proof text.

**Risk:** If lemma 3 (S-Eval) turns out to need a modified statement or
a new subtyping rule, tasks 10/11 may need rework. This is the main
reason to sequence them after the lemmas.

### Layer 2 — Assembly (1 task)

| # | Task | Depends on |
|---|------|-----------|
| 12 | **Assemble & verify** | All of 1-11 |

Checks mutual induction is well-founded (induction measure = derivation
size), stitches cases together, identifies any gaps or contradictions
between sub-proofs.

## The DAG

```
Layer 0:  [1] [2] [3] [4] [5] [6] [7] [8] [9]
              \  |  /
Layer 1:      [10] [11]
                \  /
Layer 2:       [12]
```

## Key design choices

- **Why S-Eval is its own task:** It's the most uncertain lemma — it
  might not hold, might need a new rule, or might need a different
  statement. Isolating it means one agent can explore this freely
  without blocking the others.

- **Why T-App cases are in Layer 1:** They consume lemma *statements*.
  If a lemma's statement changes during proving, these need to know.
  But they can proceed in parallel with each other.

- **Why the easy cases are separate from T-App:** Each easy case needs
  only the rules + IH. An agent can prove it with zero knowledge of the
  lemmas or the other theorem's hard cases. Minimal context = fewer ways
  to go wrong.
