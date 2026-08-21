import Dllbc.ElabCheck
import Dllbc.StdLemmas

/-!
# What the fence does, and what it does not do

`prog defer_check { … }` suppresses only the elaboration-time check. Rejection
tests are programs that exist to fail, so they need this to still elaborate.

This file pins that the fence changes nothing else: the fenced form assembles
the same `Term` as the non-checking `ty{ }` spelling, a fenced bad program is
still rejected by the checker, a fenced good one is still accepted, and each
positive assertion has a control showing the needle test can return false.
-/

open Dllbc

namespace Dllbc.Tests.Fence

set_option trace.Dllbc.check false

/-! ## (1) The fence changes no value

    `prog defer_check { … }` and `ty{ … }` on the same source must build the
    same `Term`; `ty{ }` is the non-checking brace below the checker. -/

example :
    ((prog defer_check { fn F (b : Bool) -> Unit { () }; let r = F(True); () })
     == (ty{ fn F (b : Bool) -> Unit { () }; let r = F(True); () })) = true := by
  native_decide

/-! ## (2) A fenced bad program still rejects

    `F` takes a `Bool` and is passed `3`. The fence stops the elaborator from
    complaining, but `progRejects` must still catch the type error. -/

def lying : Term := prog defer_check {
  fn F (b : Bool) -> Unit { () };
  let r = F(3);
  () }

example : progRejects lying "does not have its parameter type" = true := by native_decide

-- Control: a needle that occurs nowhere must be `false`, or (2) would also
-- pass if `progRejects` returned true unconditionally.
example : progRejects lying "no such message anywhere" = false := by native_decide

/-! ## (3) A fenced good program still accepts

    The fence is not a blanket "assume good": `progOk` still discriminates
    through it, in both directions. -/

def honest : Term := prog defer_check {
  fn F (b : Bool) -> Unit { () };
  let r = F(True);
  () }

example : progOk honest = true := by native_decide

-- Control for (3), and the other direction of (2).
example : progOk lying = false := by native_decide

/-! ## (4) The fence suppresses only elaboration

    Unfenced, `lying` would not elaborate at all — that is the whole feature.
    Its rejection under `progOk` above, together with this unfenced honest
    program elaborating below, shows the fence suppresses the elaboration
    check and nothing else. -/

def honestUnfenced : Term := prog{
  fn F (b : Bool) -> Unit { () };
  let r = F(True);
  () }

example : (honestUnfenced == honest) = true := by native_decide

end Dllbc.Tests.Fence
