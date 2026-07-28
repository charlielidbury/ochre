import Dllbc.DeclMacro
import Dllbc.AlphaEq
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.S17Spec

/-!
# Unified-grammar round-trips — splice-free bodies (§ points 1–4)

The previous phase could express `nthS`'s telescope/back in the surface but had to
splice its body (`= %term`), because the `Nil` branch `botElim Unit p` — a pure
application spine — was outside the runtime `dllb` grammar. With the unified
`uterm`/`ublk` grammar the body is now written DIRECTLY:

  * `botElim Unit p` — a juxtaposition application spine (const `botElim` applied
    to const `Unit` and runtime var `p`);
  * `&mut *hd`, `nth(&mut *tl, k, p)` — runtime borrow and call, in the same body.

The disambiguation rule at work: `nth(&mut *tl, k, p)` (identifier + comma-paren)
is a runtime **call**; `botElim Unit p` (space-separated juxtaposition) is a pure
**application**.

`nthS`'s hand-numbered ids happen to coincide with the macro's linear pre-order
threading, so the produced body is EXACTLY the corpus body (not merely alphaEq) —
demonstrated by the exact `body ==` below and confirmed by `alphaEq` over the
whole Decl. (The multi-branch bodies whose ids genuinely diverge — partScanE,
quicksort — are the stretch; `Decl.alphaEq` is the machinery that reaches them.)
-/

open Dllbc
open Dllbc.StdLemmas (set)

namespace Dllbc.Tests.SDeclUnified

def nthU : Decl :=
  decl{ fn nth (v : &mut List Nat, i : Nat, p : Le (S i) (len *v)) -> &mut Nat
        back = λ (r : Nat). set i r (*v)
        { match v {
            Nil => botElim Unit p,
            Cons(hd, tl) => match i {
              Z => &mut *hd,
              S(k) => nth(&mut *tl, k, p)
            }
        } } }

-- The body is now written splice-free and is EXACTLY the corpus body:
example : (nthU.body == Dllbc.Tests.S17Spec.nthS.body) = true := by native_decide
-- ...and the whole Decl is alphaEq (here: exactly equal) to the corpus nthS:
example : Decl.alphaEq nthU Dllbc.Tests.S17Spec.nthS = true := by native_decide

-- alphaEq sanity: reflexive, and it sees through a body-id permutation. `permuted`
-- is nthS with two branch-binder ids renamed to fresh values — exact BEq of the
-- bodies fails, alphaEq holds.
def permuted : Decl :=
  { Dllbc.Tests.S17Spec.nthS with
    body := .matchE ⟨0, "v"⟩ [
      .mk "Nil" [] (.app (.app (.const "botElim") (.const "Unit")) (.var ⟨2, "p"⟩)),
      .mk "Cons" [⟨30, "hd"⟩, ⟨40, "tl"⟩] (
        .matchE ⟨1, "i"⟩ [
          .mk "Z" [] (.borrow (.deref (.var ⟨30, "hd"⟩))),
          .mk "S" [⟨50, "k"⟩] (.call "nth" [.borrow (.deref (.var ⟨40, "tl"⟩)), .var ⟨50, "k"⟩, .var ⟨2, "p"⟩]) ]) ] }
example : (permuted.body == Dllbc.Tests.S17Spec.nthS.body) = false := by native_decide
example : Decl.alphaEq permuted Dllbc.Tests.S17Spec.nthS = true := by native_decide

end Dllbc.Tests.SDeclUnified
