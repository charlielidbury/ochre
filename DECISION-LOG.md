# Decision Log

## 2026-04-03: Implemented "unfolded structural mu" in VCompat

**Agent:** ochre-lean-20260403-014631

### Decision

Replaced VCompat's structural mu disjunct from raw bodies to self-substituted
(unfolded) bodies:
```lean
-- Old: VCompat n bodyV bodyT
-- New: VCompat n (bodyV.subst 0 (mu annV bodyV)) (bodyT.subst 0 (mu annT bodyT))
```

### Why

The old definition made VCompat.adequacy FALSE (proven constructively by
previous agent, Tests.lean §13). The root cause: raw body VCompat doesn't
imply unfolded body VCompat (VCompat.subst_congr is FALSE).

### Consequences

**Positive:**
- Adequacy counterexample no longer holds (proven: `adequacy_cex_now_incompat`)
- Self-elim fixpoint subcases now proven (Cases 2 and 4 of adequacy)
- All sorrys are now potentially true (none known false)

**Negative:**
- soundness_gen mu case now sorry'd (needs closedness lemma)
- adequacy mu/mu structural cases now sorry'd (need subCheckNF for subst'd forms)
- Sorry count increased from 6 to 9 (but 4 of the old 6 were unprovable)

### Alternative considered

Removing structural mu entirely (Option B from DECISION-LOG) — rejected because
it doesn't help soundness_gen's mu case either, and the unfolded variant
preserves more proof structure from the existing approach.


## 2026-04-03: VCompat.adequacy is FALSE — structural mu must change

**Agent:** ochre-lean-20260403-011825

### Finding

VCompat.adequacy (`VCompat n v σ → subCheckNF σ τ → VCompat n v τ`) is
**FALSE** with the current VCompat definition. Constructive proof in
Tests.lean (§13).

### Counterexample

```
v = mu type (app (bvar 0) type)     — non-fixpoint mu
σ = mu type (lam type (bvar 0))     — fixpoint mu
τ = lam type type                    — function type

VCompat 3 v σ = True   (structural mu: same ann, bodies VCompat via inferType)
subCheckNF σ τ = True   (self-elim → fixpoint unfold → structural lam → top)
VCompat 3 v τ = False   (mu-left unfolds v to app(v, type); inferType of mu = none)
```

### Root cause

The **structural mu disjunct** in VCompat allows `VCompat n (mu ann bodyV)
(mu ann bodyT)` when `VCompat (n-1) bodyV bodyT`, even though the bodies
are unrelated by substitution. After subCheckNF does **self-elim** (unfolds
σ = mu to bodyS.subst 0 σ), the adequacy proof needs VCompat for the
VALUE's unfolded form (bodyV.subst 0 v). But VCompat for raw bodies does NOT
imply VCompat for substituted bodies — **VCompat.subst_congr is FALSE**
(also proven in Tests.lean §11.6).

The structural mu disjunct + self-elim = subst_congr, which is FALSE.

### Impact

- `VCompat.adequacy` is sorry'd at exactly the problematic cases (lines 540,
  642, 644) — the sorry'd cases are unprovable, not just hard
- The `soundness` theorem is "sorry-free" as a corollary of `soundness_gen`,
  but `soundness_gen`'s asc case uses `adequacy`. Since adequacy is false,
  the proof chain has an unsound sorry'd dependency
- The 3 adequacy sorrys and the 1 `from_self_intro_gen` sorry that depend
  on adequacy-with-seen are ALL unprovable with the current VCompat

### What must change

The structural mu disjunct must be replaced. Options:

1. **Remove structural mu entirely.** Use only mu-right/mu-left (equi-recursive
   unfolding). Pro: adequacy becomes provable for these cases. Con: the
   soundness_gen mu case needs a new approach — currently it uses structural
   mu from the IH on bodies.

2. **Replace with "unfolded structural mu":** Require VCompat for substituted
   bodies instead of raw bodies:
   ```
   ∃ ann bodyV bodyT, v = mu ann bodyV ∧ τ = mu ann bodyT ∧
     VCompat n (bodyV.subst 0 v) (bodyT.subst 0 τ)
   ```
   Pro: directly compatible with adequacy (self-elim unfolds match). Con:
   soundness_gen mu case needs VCompat for substituted forms, not raw bodies.

3. **Switch to fully semantic VCompat** (already recommended in SUGGESTIONS.md).
   Define function/mu compatibility semantically: "for all compatible args,
   application gives compatible results." Pro: app case becomes trivial, mu
   case is handled uniformly. Con: major refactor, lam case of soundness_gen
   becomes harder.

### Recommendation

Option 2 is the most surgical fix. The key question is whether soundness_gen's
mu case can produce VCompat for the substituted bodies. Since both evaluators
extend the env with `(mu ann body)`, the IH gives VCompat for the normalized
body. The substituted form `bodyV'.subst 0 (mu ann bodyV')` is what you'd get
from evaluating `body` with the mu actually substituted. We may need an
env-substitution equivalence lemma to bridge the gap.

Option 3 (semantic VCompat) is the long-term answer but requires more work.
