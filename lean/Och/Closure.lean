import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Soundness
import Och.Monotonicity
import Och.Tests

/-!
# Closure-based evaluators — GUTTED for mu unification

This file previously contained closure-based concrete and abstract evaluators
(concEvalC, absEvalC) with CVal/AVal types, readback functions, and partial
soundness proofs.

It was gutted during the mu unification (replacing fix+iota with mu) because:
1. CVal/AVal had explicit `cfix` and `ciota`/`aiota` constructors
2. The evaluators had separate fix/iota/lam cases
3. The soundness proofs matched on fix_cong/iota_body Subtype' constructors

Rebuilding for mu is straightforward but large (~1000+ lines). The key changes:
- Replace cfix/ciota/aiota with a single `cmu`/`amu` constructor
- Update concEvalC: mu unrolls (like fix did)
- Update absEvalC: mu normalizes body under binder (like iota did)
- Update readback and VR_abs relation
- Redo soundness proofs with mu_body instead of fix_cong/iota_body

This is deferred to a future session. The core mu semantics (Eval.lean) and
subtyping (Subtyping.lean) are the priority.
-/
