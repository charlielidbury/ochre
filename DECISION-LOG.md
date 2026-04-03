# Decision Log

## 2026-04-03: Semantic VCompat for lam

**Agent:** ochre-lean-20260403-053631

### Decision

Replaced VCompat's structural lam disjunct (VCompat n bodyV bodyT) with a
semantic one (∀ compatible args, evaluating bodies gives compatible results).

### Rationale

The structural lam was a dead end for the app case:
- After beta-reduction, bodyV.subst 0 aV is not a source sub-expression
- VCompat.subst_congr is FALSE (Tests.lean §11.6)
- The asc-free approach has a hole (evaluator outputs aren't always asc-free)

The semantic property makes the app lam×lam case trivial (instantiate the
quantifier from ih_f at step m+2 with ih_a at step m+1).

### Trade-offs

- **Gained:** App lam×lam semantic sub-case PROVED
- **Lost:** 5 cases that were proved with structural lam need sorry (all the
  same problem: derive semantic property from structural knowledge)
- **Net:** Better architecture. The problem is concentrated in one place
  (semantic property proof) instead of scattered across 13 app sub-cases.

### What didn't work for the refl sub-case

When ih_f gives VCompat via refl (bodyV = bodyT), the semantic property isn't
available. The bridge idea (IH on `asc (body.subst 0 aV) (body.subst 0 aT)`)
needs WellTyped for body.subst 0 aV, which WellTyped app doesn't provide.

## 2026-04-03: Unconditional ascFree of eval outputs is FALSE; conditional form proven

**Agent:** ochre-lean-20260403-050103

### Finding

The previous agent claimed "evaluator outputs are always asc-free." This is FALSE.
Lambda domains and mu annotations pass through unevaluated, so asc in those
positions persists in the output. Additionally, the mu-app catch-all leaks the
raw mu body (which comes from the evaluator output, not the source, but can still
contain asc from domain/annotation passthrough).

Counterexamples (added to Tests.lean §17.1):
- `absEval 5 [] (lam (asc type type) (bvar 0))` → `lam (asc type type) (bvar 0)` (NOT ascFree)
- `absEval 5 [] (mu type (app (bvar 0) (asc type type)))` → output has asc

### What was proven instead

The CONDITIONAL version is TRUE: if the INPUT is ascFree and the ENV is ascFree,
then the OUTPUT is ascFree. This is because:
- Domains/annotations come from the source (ascFree by hypothesis)
- The mu env entry `.mu ann body` inherits ascFree from the source
- Beta-reduced expressions are ascFree (by ascFree_subst)

All three sorry'd Eval.lean theorems are now FULLY PROVEN:
- `absEval_ascFree`: `e.ascFree → env ascFree → output.ascFree` (NEW precondition: `e.ascFree`)
- `concEvalE_ascFree`: identical
- `ascFree_eval_equiv`: `e.ascFree → env ascFree → concEvalE = absEval` (uses above two)

### Impact on the app case

The conditional `ascFree_eval_equiv` does NOT directly solve the soundness_gen
app case. After beta-reduction, `bodyV.subst 0 aV` is NOT guaranteed ascFree
because `bodyV` and `aV` come from evaluating a source program WITH asc.

This means the asc-free approach for the app case is a dead end — the cross-
evaluator problem cannot be reduced to a single evaluator this way. The most
promising alternative is semantic VCompat for lam (quantify over compatible
arguments instead of requiring structural body compatibility). See PROGRESS.md.

### Sorry count change

11 → 8 declarations with sorry. All 3 Eval.lean sorrys eliminated.

## 2026-04-03: Asc-free evaluator equivalence for app case

**Agent:** ochre-lean-20260403-042336

### Decision

Decomposed the soundness_gen app case into 36 sub-cases (fV × fT constructor
shapes). Proved 23, sorry'd 13. All sorry'd cases involve active computation
(beta-reduction or mu-app).

### Key insight: asc-free evaluator equivalence

Both concEvalE and absEval strip ascription from their outputs (by evaluating
the lhs/rhs respectively). Therefore evaluator outputs are always **asc-free**.
On asc-free inputs, concEvalE and absEval are **identical** — they differ only
at the `.asc` case, which never fires for asc-free input.

After beta-reduction, the intermediate expression `bodyV.subst 0 aV` is asc-free
(both `bodyV` and `aV` are evaluator outputs, hence asc-free, and subst preserves
asc-free). So concEvalE and absEval agree on it:

```
v = concEvalE k env (bodyV.subst 0 aV) = absEval k env (bodyV.subst 0 aV)
```

This **reduces the cross-evaluator problem to single-evaluator congruence**:
does absEval preserve VCompat through substitution and evaluation?

### Formalization

Added to Eval.lean:
- `Expr.ascFree` / `Expr.ascFreeB`: predicates
- `ascFree_shift`, `ascFree_subst`: preservation lemmas (PROVEN)
- `Env.extend_ascFree`: env extension preservation (PROVEN)
- `ascFree_eval_equiv`: concEvalE = absEval on asc-free input (partially proven)
- `concEvalE_ascFree`, `absEval_ascFree`: output is asc-free (sorry'd)

### Impact

The app case is now the clearest blocker. The 13 sorry'd sub-cases all reduce
to absEval-congruence for VCompat-related asc-free inputs. This is a much
simpler problem than the original cross-evaluator formulation.

## 2026-04-03: Implemented vEquiv approach for soundness_gen mu case

**Agent:** ochre-lean-20260403-025516

### Decision

Implemented the VCompat-equivalence (vEquiv) approach for the soundness_gen
mu case. The mu case is now PROVED (modulo one sorry in a sub-lemma).

The proof uses `mu_body_subst_vcompat`, which has three cases:
- **Case A (proved):** bodyT = type → trivial (type.subst = type → VCompat top)
- **Case B (proved):** bodyV = bodyT → subst gives equal → VCompat refl
- **Case C (sorry'd):** the vEquiv chain (closedEvalB → subst vEquiv → VCompat)

### Key finding: closedEvalB is NOT universally true

During implementation, discovered that `closedEvalB 0` does NOT hold for all
evaluator outputs. The mu-app catch-all (`| _, _ => some (.app body aVal)`)
leaks the raw mu body into the output, which can have free `bvar 0` in
evaluated positions. Example: `mu type (app (bvar 0) (bvar 0))`.

However, brute-force testing shows that whenever closedEvalB fails AND
evaluators produce different results, `bodyT = type`. This means Case A
handles all closedEvalB-failing cases with different outputs. Case C is
only needed when closedEvalB holds AND bodyV ≠ bodyT ∧ bodyT ≠ type.

### What was implemented

1. `Expr.vEquivB`: Bool-valued VCompat-equivalence
2. `Expr.closedEvalB`: Bool-valued eval-closedness
3. `closedEvalB_subst_vEquiv`: FULLY PROVEN — subst is vEquiv-no-op
4. `mu_body_subst_vcompat`: Cases A+B proved, Case C sorry'd
5. soundness_gen mu case: now proved using mu_body_subst_vcompat
6. Tests.lean §16: brute-force tests for the full chain + trichotomy

### Impact

- soundness_gen mu case: was sorry, now PROVED (modulo sub-lemma)
- New sorry'd declarations: 4 (mu_body_subst_vcompat, VCompat_of_vEquivB,
  concEvalE_closedEvalB, absEval_closedEvalB). Only mu_body_subst_vcompat
  is on the critical path; the other 3 are infrastructure for Case C.
- Total sorry'd declarations: 8 (was 4, but the old mu sorry was a bare
  sorry in soundness_gen; now it's factored into focused sub-lemmas)

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


## 2026-04-03: Closedness lemma is FALSE — need VCompat-equivalence

**Agent:** ochre-lean-20260403-021117

### Finding

The naive closedness lemma (`v.subst 0 X = v` for evaluator outputs when
`env.length > 0`) is **FALSE**. The evaluators (`concEvalE`, `absEval`) do
not evaluate lambda domains or mu annotations — they copy them from the
source expression. If the source has `bvar 0` in a domain position (e.g.,
`mu type (lam (bvar 0) (bvar 0))`), the evaluator output retains this
free `bvar 0`.

Concrete counterexample in Tests.lean §14:
```
mu type (lam (bvar 0) (bvar 0))
env' = [mu type (lam (bvar 0) (bvar 0))]
concEvalE 10 env' (lam (bvar 0) (bvar 0)) = some (lam (bvar 0) (bvar 0))
(lam (bvar 0) (bvar 0)).subst 0 (mu...) = lam (mu...) (bvar 0) ≠ input
```

### But the soundness_gen mu sorry IS true

Brute-force testing (Tests.lean §15) of 51 small mu bodies confirms no
counterexample to the soundness_gen mu case. Of these, 5 bodies produce
genuinely different `concEvalE`/`absEval` results, and ALL pass the VCompat
check on substituted forms.

### Why it works despite closedness failing

VCompat's structural cases for lambda and mu do NOT compare domains or
annotations. The structural lam compares only bodies; the structural mu
compares only unfolded bodies. Since `subst 0` only changes un-evaluated
positions (domains, annotations), and VCompat ignores those positions,
the substitution is invisible to VCompat.

### Proposed approach: VCompat-equivalence (vEquiv)

Define `vEquiv`: two expressions agree on everything except lambda domains
and mu annotations. Then prove:
1. VCompat respects vEquiv (congruence)
2. subst preserves vEquiv for "eval-closed" expressions
3. Evaluator outputs are eval-closed

See SUGGESTIONS.md Priority 1 for the full plan.

### Impact

- The soundness_gen mu sorry CANNOT be resolved by a simple closedness lemma
- The previously recommended approach in SUGGESTIONS.md was incorrect
- A more sophisticated VCompat-equivalence approach is needed
- The sorry count remains at 4 declarations, same 9 individual sorrys
