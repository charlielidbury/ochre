import Dllbc.ElabCheck
import Dllbc.StdLemmas
import Dllbc.Tests.Functions

/-!
# The ambiguous middle

A term written bare (no `fn`, no ascription) has no fixed consumer, so it can be
legal under both the pure `⇝` reading and the checked `⇒` walk, and the two
verdicts can genuinely disagree: `readC` accepts and computes a value, while
`checkProgram` rejects with a real program error. This file exhibits terms
where that disagreement holds, showing the class is non-empty and the
divergence is real rather than accidental. That is why the surface needs the
author's word (capitalization) to pick an arrow instead of inferring one from
the term alone — see docs/05.
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
    calling it. Both are written bare. -/

-- `⇝` accepts both and computes `unit`: as ordinary comptime computations they
-- normalize fine, the type mismatch never gets checked.
example : comptimeAccepts Dllbc.Tests.S26Seal.c7 = true := by native_decide
example : comptimeAccepts Dllbc.Tests.S26Seal.c10 = true := by native_decide

-- `⇒` rejects both with real program errors: as runtime calls the argument
-- must have the parameter type, and it does not.
example : progRejects Dllbc.Tests.S26Seal.c7 "does not have its parameter type" = true := by
  native_decide
example : progRejects Dllbc.Tests.S26Seal.c10 "holds ⊥" = true := by native_decide

/-! ## The controls

    Without these, the file would still pass if `comptimeAccepts` were
    constantly true. A term that is unambiguously a program must come out the
    other way. -/

def realProgram : Term := prog defer_check {
  fn F (b : Bool) -> Unit { () };
  let x = Cons(1, Nil);
  let v = &m x;
  let r = F(True);
  () }

example : comptimeAccepts realProgram = false := by native_decide

-- A term that is unambiguously pure is accepted by `⇝` too, so acceptance
-- alone does not make a term ambiguous — it is the `⇒` rejection that does.
example : comptimeAccepts ty{ λ (N : Nat). N } = true := by native_decide

end Dllbc.Tests.AmbiguousMiddle
