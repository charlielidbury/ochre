import Dllbc.ElabCheck
import Dllbc.StdLemmas

/-!
# `x : τ` — hovering a DLLBC variable answers (docs/10)

Every case below is a block that ELABORATES; the assertion is not in the build
output but in what `textDocument/hover` returns at a named position, recorded
beside each case as a comment.

**These are machine-checkable, but not by `lake build`.** There is no
`#guard_msgs` analogue for hover — the info tree is consulted by the language
server, not by the elaborator's message log — so re-verification is one
`lean_hover_info` call per case, at the line and column in its comment. The
comments are the pinned record; the tool is the checker.

Two sources of truth, and the cases are grouped by which one answers:

* **S1**, from the SOURCE — a parameter's annotation, a callee's signature.
  Exact, no checker involvement, and therefore alive inside
  `prog defer_check { }` too.
* **S2**, from the CHECKER — a `let`'s type, which exists only in Ω at the
  binding step. Green checks only, first path.
-/

open Dllbc

namespace Dllbc.Tests.HoverSpans

set_option trace.Dllbc.check false

/-! ## (1) A parameter BINDER — S1, the annotation's own text
    ## (2) An OCCURRENCE of that parameter, in the body
    ## (8) The CALLEE NAME, at its declaration and at the call

    `hoverProbe` positions:
      (1)  L47 C9   `b`  ⇒  **b : `Bool`**
      (2)  L47 C37  `b`  ⇒  **b : `Bool`**
      (8a) L47 C6   `F`  ⇒  **F : `(b : Bool) -> Unit`**
      (8b) L48 C10  `F`  ⇒  **F : `(b : Bool) -> Unit`**
-/

example : Term := prog{
  fn F (b : Bool) -> Unit { let c = b; () };
  let r = F(True);
  () }

/-! ## (3) A `let` BINDER — S2, from the checker's Ω
    ## (4) An occurrence of it on the NEXT statement
    ## (5) An occurrence further down, past an intervening statement

    A top-level `let` binds a CONCRETE value, and the checker records the value
    rather than a type because it has one — see `letTooltip`. The `x : τ` form
    appears in case (6), where the value is symbolic.

      (3) L64 C7   `x`  ⇒  **x ≡ `S Z`** — comptime-known value
      (4) L65 C11  `x`  ⇒  **x ≡ `S Z`** — comptime-known value
      (5) L67 C11  `x`  ⇒  **x ≡ `S Z`** — comptime-known value
-/

example : Term := prog{
  let x = S(Z);
  let y = x;
  let z = True;
  let w = x;
  () }

/-! ## (6) A `let` whose value is SYMBOLIC — the `x : τ` case

    Inside a `fn` body a parameter is a σ, so a `let` that reads one binds a σ
    too, and `sctx` has its type. This is the shape the plan is named for.

      (6a) L82 C24  `n`  ⇒  **n : `Nat`**            (S1, the parameter)
      (6b) L82 C33  `m`  ⇒  **m : `Nat`**            (S2, from the checker)
      (6c) L82 C41  `m`  ⇒  **m : `Nat`**            (S2, an occurrence)
-/

example : Term := prog{
  fn G (n : Nat) -> Unit { let m = n; let p = m; () };
  () }

/-! ## (7) SHADOWING — the inner binder wins, and by construction

    A body-local `let v` shadows the parameter `v`. Runtime ids distinguish them,
    and S1's table is keyed by id as well as name, so the occurrence below the
    `let` does NOT report the parameter's annotation.

      (7a) L98 C9   `v`  ⇒  **v : `Bool`**            (the PARAMETER)
      (7b) L98 C33  `v`  ⇒  **v ≡ `S Z`** …           (the `let`, not the param)
      (7c) L98 C44  `v`  ⇒  **v ≡ `S Z`** …           (an occurrence of the `let`)
-/

example : Term := prog{
  fn H (v : Bool) -> Unit { let v = S(Z); let q = v; () };
  () }

/-! ## (9) `defer_check` — S1 PRESENT, S2 ABSENT

    Nothing walked, so no Ω existed and no `let` has a type. The parameter
    annotations are still written in the source, so they still answer. This is
    the design's own line — checking is where types come from — stated as a test
    rather than as a paragraph.

      (9a) L115 C9   `b`  ⇒  **b : `Bool`**   (S1 alive)
      (9b) L115 C37  `b`  ⇒  **b : `Bool`**   (S1 alive at an occurrence)
      (9c) L115 C33  `c`  ⇒  no DLLBC tooltip (S2 absent — nothing checked)
-/

example : Term := prog defer_check {
  fn F (b : Bool) -> Unit { let c = b; () };
  () }

/-! ## (10) A BORROW parameter — the spec's headline shape

    `&mut List Nat` is rendered from the source text, so the tooltip is the type
    as written rather than the `borrowT τ (weaken τ)` it elaborates to.

      (10a) L131 C9   `v`  ⇒  **v : `&mut List Nat`**
      (10b) L131 C41  `v`  ⇒  **v : `&mut List Nat`**
-/

example : Term := prog{
  fn K (v : &mut List Nat) -> Unit { let a = *v; *v := a; () };
  () }

end Dllbc.Tests.HoverSpans
