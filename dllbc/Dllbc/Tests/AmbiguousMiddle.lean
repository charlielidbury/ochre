import Dllbc.ElabCheck
import Dllbc.StdLemmas
import Dllbc.Tests.Functions

/-!
# The ambiguous middle, and why the author's word is load-bearing

**THIS FILE IS LOAD-BEARING FOR A CLAIM docs/05 MAKES, not an illustration of
one.** §2b and §6 assert that the surface cannot be blamed for picking an arrow
where a term is legal under both, and that no classifier could have replaced the
author's word. That assertion is only worth something if the class it describes is
non-empty and the three verdicts really do diverge — which is a fact about this
corpus, checkable, and checked here. If these witnesses ever stop diverging, the
doc's argument has lost its subject and should be re-read rather than trusted.

A term written bare has no consumer, and this calculus's central claim about
fragments is that **the consumer decides**: "a term's fragment is not a property
of where it was WRITTEN, it is a property of which arrow CONSUMES it"
(`ProgMacro`'s header, M29 γ). Auto-checking `prog{ }` has to pick an arrow
before any consumer exists, so the question is what happens to terms that are
legal under BOTH — and whether the surface can be blamed for picking one.

It cannot, and this file is the closed demonstration. There is a non-empty class
of terms for which:

  * `readC` — the kernel's own ⇝ judgment, whose refusal list IS this calculus's
    definition of the pure sub-grammar (§1.3) — **ACCEPTS**, computing a value;
  * `checkProgram` — the ⇒-walk — **REJECTS**, with a real program error;
  * and the two disagree for a REASON, not by accident.

**The block-level classifier this file was originally written against is gone.**
`Term.needsRuntime` routed `prog{ }` between checkers and agreed with `readC`
here, which is what the original third assertion pinned. Under the final design
there is no router: `prog{ }` always ⇒-walks and per-binder capitalization does
the intra-term staging. The finding survives the classifier's retirement intact,
because it was never about the classifier — it is about the two ARROWS.

Both arrows are right. Under ⇝ these are ordinary comptime computations that
normalize. Under ⇒ the same syntax is a runtime call whose argument must have
the parameter type, and it does not. The verdicts differ because the ARROWS
differ, not because either is wrong about the term.

**What this means for the surface.** A bare `prog{ }` gets no check here, and
that is the information rule's fourth row working correctly rather than a hole:
no `fn`, no ascription, so no specification exists and nothing can be asked. The
suite's `progRejects` assertions on these same terms are not in conflict with
that — they SUPPLY the missing consumer, stating "read this one with ⇒", which
is information the definition site does not carry. **The author's word is
load-bearing, and no classifier could have replaced it**: deciding these by
analysis would mean deciding which arrow the author meant, and the calculus is
explicit that this is not a property of the term.

Concretely, this is why the ten walk-passing twins in the corpus need no fence.
They elaborate green (classified pure, nothing asked) and their `progRejects`
assertions still hold (⇒ supplied explicitly). The two compose because they are
about different arrows.
-/

open Dllbc

namespace Dllbc.Tests.AmbiguousMiddle

set_option trace.Dllbc.check false

/-- `readC`'s verdict, as a Bool: does the kernel's ⇝ accept this term? -/
def comptimeAccepts (t : Term) : Bool :=
  match (readC 2000 t).run (seedPure [] []) with
  | .ok _ _ => true
  | .error _ _ => false

/-! ## The witnesses

    `S26Seal.c7` is `let F = λ (x : Nat). x; let z = F(Nil); ()` — a let-bound λ
    applied to an argument of the wrong type. `c10` moves its callee away before
    calling it. Both are written bare, and both are in the middle. -/

-- ⇝ ACCEPTS both, and computes `unit`.
example : comptimeAccepts Dllbc.Tests.S26Seal.c7 = true := by native_decide
example : comptimeAccepts Dllbc.Tests.S26Seal.c10 = true := by native_decide

-- And ⇒ REJECTS both, with real program errors. This is the assertion the suite
-- makes about them, and it remains true and remains live.
example : progRejects Dllbc.Tests.S26Seal.c7 "does not have its parameter type" = true := by
  native_decide
example : progRejects Dllbc.Tests.S26Seal.c10 "holds ⊥" = true := by native_decide

/-! ## THE CONTROLS

    Without these the file would pass if `comptimeAccepts` were constantly true.
    A term that is unambiguously a program must come out the other way. -/

def realProgram : Term := prog defer_check {
  fn F (b : Bool) -> Unit { () };
  let x = Cons(1, Nil);
  let v = &m x;
  let r = F(True);
  () }

example : comptimeAccepts realProgram = false := by native_decide

-- …and a term that is unambiguously pure is accepted by ⇝ too, so "⇝ accepts"
-- alone is not what makes a term ambiguous — the ⇒ verdict is the other half.
example : comptimeAccepts ty{ λ (N : Nat). N } = true := by native_decide

end Dllbc.Tests.AmbiguousMiddle
