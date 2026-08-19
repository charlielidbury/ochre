import Dllbc.ElabCheck
import Dllbc.StdLemmas

/-!
# What the fence does, and — more importantly — what it does NOT do

`prog defer_check { … }` suppresses the **elaboration-time** check. 275 sites in
this suite carry it, and almost all of them are programs that exist BECAUSE they
fail: a `progRejects` twin's rejection is its assertion, so failing to elaborate
would delete the test rather than strengthen it.

That makes the fence the single most dangerous thing in this port. A fence that
quietly changed the assembled `Term`, or that suppressed more than the
elaboration check, would turn 275 live assertions into 275 that pass for the
wrong reason — and nothing else in the suite would notice, because every one of
those files would still be green. This file is what notices.

Each pair below is an assertion and its control. The control is the half that
matters: `progRejects` on a needle that does not occur must be `false`, or the
positive assertion is vacuous and proves only that some string was returned.
-/

open Dllbc

namespace Dllbc.Tests.Fence

set_option trace.Dllbc.check false

/-! ## (1) THE FENCE CHANGES NO VALUE

    `prog defer_check { … }` and `ty{ … }` on the same source must be the same
    `Term`. `ty{ }` is the non-checking brace below the checker, so this compares
    the fenced form against the one spelling that provably does nothing but
    elaborate. If this ever fails, every fenced assertion in the suite is
    asserting about a different program than the one written. -/

example :
    ((prog defer_check { fn F (b : Bool) -> Unit { () }; let r = F(True); () })
     == (ty{ fn F (b : Bool) -> Unit { () }; let r = F(True); () })) = true := by
  native_decide

/-! ## (2) A FENCED LIE STILL REJECTS, AND THE NEEDLE IS REAL

    `F` takes a `Bool` and is passed `3`. The fence stops the ELABORATOR from
    complaining; `progRejects` must still run, still walk, and still see it. -/

def lying : Term := prog defer_check {
  fn F (b : Bool) -> Unit { () };
  let r = F(3);
  () }

example : progRejects lying "does not have its parameter type" = true := by native_decide

-- THE CONTROL. A needle that occurs nowhere must be `false`. Without this,
-- assertion (2) would also pass if `progRejects` returned true unconditionally.
example : progRejects lying "no such message anywhere" = false := by native_decide

/-! ## (3) A FENCED HONEST PROGRAM STILL PASSES

    The fence is not a blanket "assume good": `progOk` still discriminates
    through it, in both directions. -/

def honest : Term := prog defer_check {
  fn F (b : Bool) -> Unit { () };
  let r = F(True);
  () }

example : progOk honest = true := by native_decide

-- THE CONTROL for (3), and the other direction of (2).
example : progOk lying = false := by native_decide

/-! ## (4) THE FENCE IS THE ONLY THING SUPPRESSED

    Unfenced, `lying` would not elaborate at all — that is the whole feature. The
    assertion that it still rejects under `progOk` (above) plus the fact that this
    file compiles (below, unfenced and honest) is the pair that says the fence
    suppresses the elaboration check and nothing else. -/

def honestUnfenced : Term := prog{
  fn F (b : Bool) -> Unit { () };
  let r = F(True);
  () }

example : (honestUnfenced == honest) = true := by native_decide

end Dllbc.Tests.Fence
