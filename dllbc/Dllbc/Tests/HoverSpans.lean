import Dllbc.ElabCheck
import Dllbc.StdLemmas

/-!
# `x : τ` — hovering a DLLBC variable answers (docs/16)

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

    Verified through `textDocument/hover`:
      (1)  L44 C9   `b`  ⇒  **b : `Bool`**
      (2)  L44 C37  `b`  ⇒  **b : `Bool`**
      (8a) L44 C6   `F`  ⇒  **F : `(b : Bool) -> Unit`**
      (8b) L45 C11  `F`  ⇒  **F : `(b : Bool) -> Unit`**
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

      (3) L62 C7   `x`  ⇒  **x ≡ `S Z`** — comptime-known value
      (4) L63 C11  `x`  ⇒  **x ≡ `S Z`** — comptime-known value
      (5) L65 C11  `x`  ⇒  **x ≡ `S Z`** — comptime-known value
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

      (6a) L79 C9   `n`  ⇒  **n : `Nat`**            (S1, the parameter)
      (6b) L79 C32  `m`  ⇒  **m : `Nat`**            (S2, from the checker)
      (6c) L79 C47  `m`  ⇒  **m : `Nat`**            (S2, an occurrence)
-/

example : Term := prog{
  fn G (n : Nat) -> Unit { let m = n; let p = m; () };
  () }

/-! ## (7) SHADOWING — the inner binder wins, and by construction

    A body-local `let v` shadows the parameter `v`. Runtime ids distinguish them,
    and S1's table is keyed by id as well as name, so the occurrence below the
    `let` does NOT report the parameter's annotation.

      (7a) L94 C9   `v`  ⇒  **v : `Bool`**            (the PARAMETER)
      (7b) L94 C33  `v`  ⇒  **v ≡ `S Z`** …           (the `let`, not the param)
      (7c) L94 C51  `v`  ⇒  **v ≡ `S Z`** …           (an occurrence of the `let`)
-/

example : Term := prog{
  fn H (v : Bool) -> Unit { let v = S(Z); let q = v; () };
  () }

/-! ## (9) `defer_check` — S1 PRESENT, S2 ABSENT

    Nothing walked, so no Ω existed and no `let` has a type. The parameter
    annotations are still written in the source, so they still answer. This is
    the design's own line — checking is where types come from — stated as a test
    rather than as a paragraph.

      (9a) L110 C9   `b`  ⇒  **b : `Bool`**   (S1 alive)
      (9b) L110 C37  `b`  ⇒  **b : `Bool`**   (S1 alive at an occurrence)
      (9c) L110 C33  `c`  ⇒  no DLLBC tooltip (S2 absent — nothing checked)
-/

example : Term := prog defer_check {
  fn F (b : Bool) -> Unit { let c = b; () };
  () }

/-! ## (10) A BORROW parameter — the spec's headline shape

    `&mut List Nat` is rendered from the source text, so the tooltip is the type
    as written rather than the `borrowT τ (weaken τ)` it elaborates to.

      (10a) L124 C9   `v`  ⇒  **v : `&mut List Nat`**
      (10b) L124 C42  `a`  ⇒  **a : `List Nat`**        (S2, a deref's payload)
      (10c) L124 C47  `v`  ⇒  **v : `&mut List Nat`**
-/

example : Term := prog{
  fn K (v : &mut List Nat) -> Unit { let a = *v; *v := a; () };
  () }

/-! ## (11) PATH-SENSITIVITY — one binder, two binding-time answers

    `pushContinuations` duplicates a match's continuation into every arm, so a
    `let` written after a fork is checked once per path — one binder, one id,
    and legitimately more than one type. v1 shows the FIRST path's and says that
    the others disagreed; it does not merge them and does not list them.

      (11a) L139 C9   `b`  ⇒  **b ≡ `True`** … *(differs per path)*
      (11b) L140 C13  `b`  ⇒  **b ≡ `True`** … *(differs per path)* -/

example : Term := prog{
  fn P (n : Nat) -> Unit {
    let b = match n { Z => True, S(k) => False };
    let c = b;
    () };
  () }

/-! ## (12) A LET-BOUND BORROW — the tooltip is a BINDING-TIME SNAPSHOT

    A borrow renders as both of its parts, `borrowₘ ℓ<loan> <payload>`, straight
    out of `Val.prettyPrec`'s `borrowM` case.

    **The two tooltips on L169 disagree about the same memory, and both are
    right.** `*b := Cons(2, Nil)` on L168 changes what the borrow points at. `b`
    hovered AFTER that write still renders the payload it had when `b` was BOUND,
    because `letStep` files once and never updates; `d`, bound from `*b` on the
    very next statement, renders what Ω holds now. So a borrow's tooltip is its
    binding-time snapshot, not its present payload — which is the S2 semantics
    stated in the plan, made visible without the eye leaving the line.

      (12a) L166 C7   `b`  ⇒  **b ≡ `borrowₘ ℓ0 (Cons (S Z) Nil)`** — comptime-known value
      (12b) L167 C7   `a`  ⇒  **a ≡ `Cons (S Z) Nil`** — comptime-known value
      (12c) L168 C4   `b`  ⇒  **b ≡ `borrowₘ ℓ0 (Cons (S Z) Nil)`** — comptime-known value
      (12d) L169 C12  `b`  ⇒  **b ≡ `borrowₘ ℓ0 (Cons (S Z) Nil)`** — the PRE-write payload
      (12e) L169 C7   `d`  ⇒  **d ≡ `Cons (S (S Z)) Nil`** — the POST-write value
-/

example : Term := prog{
  let x = Cons(1, Nil);
  let b = &m x;
  let a = *b;
  *b := Cons(2, Nil);
  let d = *b;
  () }

/-! ## (13) A REBORROW — distinct loan ids, and no loan graph

    `t` gets its own loan (ℓ1 against `b`'s ℓ0). The nesting is NOT shown as a
    borrow-of-borrow: what a `letStep` records is the payload, so a reborrow's
    tooltip names its own loan and the value beneath it, not the chain between.

      (13a) L184 C7  `b`  ⇒  **b ≡ `borrowₘ ℓ0 (Cons (S Z) Nil)`** — comptime-known value
      (13b) L185 C7  `t`  ⇒  **t ≡ `borrowₘ ℓ1 (Cons (S Z) Nil)`** — comptime-known value
-/

example : Term := prog{
  let x = Cons(1, Nil);
  let b = &m x;
  let t = &m *b;
  let a = *t;
  *t := a;
  () }

/-! ## (14) MATCH — the scrutinee answers; a pattern binder does not

    The SCRUTINEE is an occurrence like any other and hovers by S1. It did not
    until the `noteIdent` call in `elabScrut` was added: the plain-variable path
    answers there and never reaches the ident row, so a parameter used to hover
    everywhere except in `match n { … }`. This case is that fix's pin.

    A PATTERN BINDER hovers as nothing, binder and occurrence alike, and that is
    the filed limit: binders are bound by the match rather than by `letStep`, so
    the one shared binding site never sees them (docs/16, §"What is deliberately
    not built").

    **No refinement is visible, and `q` is the case that shows why.** `let q = m`
    goes through `letStep`, so it answers — with `Nat`, m's own `sctx` type,
    correct and unnarrowed. The narrowing lives in the relation between `n` and
    `S m`, not in m's type, so copying the binder cannot reveal it.

      (14a) L215 C9   `n`  ⇒  **n : `Nat`**   (the parameter, S1)
      (14b) L216 C11  `n`  ⇒  **n : `Nat`**   (the SCRUTINEE — the fix)
      (14c) L218 C9   `m`  ⇒  no DLLBC tooltip (pattern binder — filed limit)
      (14d) L218 C25  `m`  ⇒  no DLLBC tooltip (its occurrence — same cause)
      (14e) L218 C21  `q`  ⇒  **q : `Nat`**   (a `let`, so S2 answers; unnarrowed)
-/

example : Term := prog{
  fn M (n : Nat) -> Unit {
    match n {
      Z => (),
      S(m) => { let q = m; () }
    } };
  () }

end Dllbc.Tests.HoverSpans
