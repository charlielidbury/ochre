import Dllbc.ElabCheck

/-!
# Marked twins — the honest program is the original, the liars are mutations of it (docs/21)

**This file asserts itself, and it states its e2e standing up front.** Alongside
the accepted/rejected assertions it pins Term-VALUE equalities by
`native_decide` — `stripMarkers marked == plain`, `twin != honest`, the
`replaceMarked?` error contract. These are the sanctioned mutation-ledger style
(the S4Pure-class exemption): the claim under test is precisely a fact about
`Term` values — that the sharing between an honest program and its lying twin
is value-level rather than a trusted construction — and no accepted/rejected
verdict can state it.
-/

open Dllbc

namespace Dllbc.Tests.MarkedTwins

set_option trace.Dllbc.check false

/-! ## (T1) TRANSPARENCY — `@name(e)` is `e`

    The same small program written twice, marked and unmarked. The strip
    recovers the plain program EXACTLY — same `Term`, ids included, because the
    marker row consumes nothing from the elaborator's counters — and the marked
    program checks. The third pin keeps the first honest: a marker is a real
    node, so only the strip erases it, and `==` on the unstripped pair says the
    two sources did not elaborate identically by accident. -/

def markedProg : Term := prog{
  let x = @seed(Cons(1, Nil));
  let b = &m x;
  *b := @update(Cons(2, Nil));
  let d = *b;
  () }

def plainProg : Term := prog{
  let x = Cons(1, Nil);
  let b = &m x;
  *b := Cons(2, Nil);
  let d = *b;
  () }

example : (Term.stripMarkers markedProg == plainProg) = true := by native_decide
example : (markedProg == plainProg) = false := by native_decide
example : progOk markedProg = true := by native_decide

-- A CALL inside a marker. `fn` declarations retarget every later `f(…)` into an
-- app spine on the binding (`FnMacro.retarget`, via `bindFn`) — a pass that
-- runs BEFORE the boundary strip and has a catch-all, so without its marker
-- row the call under `@site` would have stayed an unresolved `.call` and the
-- strip equality below would fail (the plain program's call is a spine). Found
-- on the rebase onto module states, where the same pass resolves imports.
def markedCall : Term := prog{
  fn F () -> Nat { S Z };
  let y = @site F();
  () }

def plainCall : Term := prog{
  fn F () -> Nat { S Z };
  let y = F();
  () }

example : (Term.stripMarkers markedCall == plainCall) = true := by native_decide
example : progOk markedCall = true := by native_decide

/-! ## (T2) THE CONTRACT — zero and duplicate hits are loud

    `replaceMarked?` is the Edit-tool contract (docs/21 §3): exactly one marker
    of the given name, or a loud error that also says which markers the term
    DOES have — so a renamed claim site can never make a twin silently test
    nothing. The duplicate is built directly from `Term` constructors: the
    surface has no reason to make writing one convenient. -/

example : (match Term.replaceMarked? "nope" Term.unit markedProg with
           | .error e => strContains e "marker 'nope' not found"
                         && strContains e "'seed'" && strContains e "'update'"
           | .ok _ => false) = true := by native_decide

def twoSame : Term := .seq (.marker "m" .unit) (.marker "m" .unit)

example : (match Term.replaceMarked? "m" Term.unit twoSame with
           | .error e => strContains e "marker 'm' occurs 2 times"
           | .ok _ => false) = true := by native_decide

/-! ## (T3) THE POINT — an honest fn, and its twin lies in the return type

    `pinHonest` is Direct.lean's `PinOne` with its claim NAMED: the return type
    pins the result to `S Z`, and `@claim …` declares that pin as the attack
    surface — BARE, no brackets, marking the whole `Id` spine up to the body's
    `{` (the loose λ-style extent). The twin is not written — it is MINTED, by
    swapping the claim's body for `Id Nat r (S (S Z))` in the honest `Term`
    value. The body still returns `Refl` for `S Z`, so the twin is rejected at
    its own declaration, for the meaningful reason (the certificate does not
    prove the strengthened claim), and `twin != honest` pins that the mutation
    landed. -/

def pinHonest : Term := prog{
  fn PinOne () -> Σ (r : Nat). @claim Id Nat r (S Z) { Pair(S Z, Refl) };
  () }

example : progOk pinHonest = true := by native_decide

def pinTwin : Term :=
  match Term.replaceMarked? "claim" prog_parse { Id Nat r (S(S(Z))) } pinHonest with
  | .ok t => t
  -- Unreachable while T2 holds; `.unit` cannot satisfy the rejection pin below,
  -- so a contract regression fails T3 rather than passing it vacuously.
  | .error _ => .unit

example : (pinTwin == pinHonest) = false := by native_decide
-- The needle carries the LIE, not just the verdict: the audit names the
-- strengthened claim (the `S (S Z)` the twin swapped in, which the printer
-- renders `2`) that the certificate cannot meet, so this pin cannot be
-- satisfied by a twin that was rejected for being garbage.
example : progRejects pinTwin
  "does not have return type (Σ(§0 : Nat). Id §0 2)" = true := by native_decide

/-! ## (T4) THE SEAM — `show` answers identically in marked code (docs/21 §5)

    Surface statement keys are built from EMITTED syntax, markers included; the
    machine's delta keys come from the stripped walk. The two `#guard_msgs`
    below are the same program marked and unmarked, and their `show` texts are
    IDENTICAL — which is exactly what the elaborator's key strip protects.

    The probe is chosen to be COUNTERFACTUALLY discriminating: it anchors to
    the marked `:=` statement (an assign KEEPS its rhs in `stmtKeyOf`, so the
    marker survives into the surface key — a `let`'s key is binder-only and
    would not exercise the seam), and it sits where the point answer (⊥, the
    payload is moved out) differs from the binder-fact fallback (the payload at
    binding time). If the key strip were missing, the point answer would
    silently decline, the fallback would answer `Cons (S Z) Nil`, and the pin
    would fail — a miss cannot hide behind an identical fallback. -/

/--
info: b ↦ borrowₘ ℓ₀ ⊥
-/
#guard_msgs in
example : Term := prog{
  let x = Cons(1, Nil);
  let b = &m x;
  let a = *b;
  show b;
  *b := @update(Cons(2, Nil));
  let d = *b;
  () }

/--
info: b ↦ borrowₘ ℓ₀ ⊥
-/
#guard_msgs in
example : Term := prog{
  let x = Cons(1, Nil);
  let b = &m x;
  let a = *b;
  show b;
  *b := Cons(2, Nil);
  let d = *b;
  () }

/-! ## (T5) THE SPELLINGS AND THE EXTENT — one row, pinned truth

    `@name E` is ONE loose grammar row (λ-style prefix); `@name(E)` and
    `@name (E)` are the same row reading a grouped uterm, not a second
    spelling. The extent of a bare marker is MAXIMAL: everything a level-10
    parse absorbs to its right — a whole application spine, a whole arrow —
    stopping only at a real delimiter. So inside an argument list the comma
    delimits (`Cons(@m Z, Nil)` marks `Z` alone), and `@m Nat → Nat` marks the
    ARROW, not its domain. Each pin below is one of those sentences as a
    `Term` equality. -/

example : (ty{ @m Z } == Term.marker "m" (.ctorApp "Z" [])) = true := by native_decide
example : (ty{ @m(Z) } == ty{ @m Z }) = true := by native_decide
example : (ty{ @m (Z) } == ty{ @m Z }) = true := by native_decide
example : (ty{ Cons(@m Z, Nil) }
           == Term.ctorApp "Cons" [.marker "m" (.ctorApp "Z" []), .ctorApp "Nil" []]) = true := by
  native_decide
example : (ty{ @m Cons(Z, Nil) } == Term.marker "m" (ty{ Cons(Z, Nil) })) = true := by
  native_decide
example : (ty{ @m Nat → Nat } == Term.marker "m" (ty{ Nat → Nat })) = true := by native_decide

/-! ## (T6) NEGATIVE CONTROL — a marker cannot impersonate a kernel spelling

    `@old(…)` is the kernel's own entry-snapshot spine (surface: `old *v`) and
    `@res` is the kernel form of `*res`; a marker by either name would mean
    its body's CURRENT value, silently. Neither gets through, and the two pins
    below the comment record how, which DIFFERS between the two: `old` is a
    KEYWORD of the grammar (the `old *v` row), so `@old Z` dies in the PARSER
    — "unexpected token 'old'; expected identifier" — which is also why it has
    no `#guard_msgs` pin here: a term that fails to parse fails the whole
    command before `#guard_msgs` can guard it (tried; the pin form does not
    exist). `res` is an ordinary identifier (`*res` matches it as one), so
    `@res` parses under the generic row and the ELABORATOR refuses the name —
    that one pins. The magic spellings themselves never enter the marker row —
    their surface forms are `old *v` and `*res`, no `@` in either — and the
    full suite's `old`/`res` tests pin that they still parse as themselves. -/

/--
error: '@res' cannot be a marker name: it collides with the kernel spelling `@res(…)` (the exit payload, written `*res`), and a marker named 'res' would silently mean its body's CURRENT value instead. Pick another name.
-/
#guard_msgs in
example : Term := ty{ @res Z }

/-! ## (T7) A SEEDED TWIN — docs/21 §6's first request, met by the module lane

    docs/21 §6 asked docs/20 for a CALLABLE seeded rejection check, so that a
    twin under a module state could be a mutated `Checked.term` re-checked
    against the same seed. The module lane delivered it as
    `progRejectsFrom`/`progOkFrom` (docs/20 stage 6), and this section is that
    request verified against reality rather than taken on the promise:

    * a library module declares `PinOne`, unmarked;
    * a golden consumer seeded from it carries a marked claim in its OWN
      return type, and checks (`progOkFrom` on its persisted term);
    * the twin is minted from the golden's PERSISTED term — `Checked.term` is
      stored before the module boundary, so its markers survive, and
      `FnMacro.retarget` (the one pre-boundary pass) has a transparent marker
      row so the call inside the claim's fn was resolved against the seed —
      and is rejected FROM THE SAME SEED with its real message pinned.

    The second boundary matters here: a seeded walk enters through
    `moduleBoundary`, never `atBoundary`, and the strip lives in both. -/

def pinLib : Checked := prog () {
  fn PinOne () -> Σ (r : Nat). Id Nat r (S Z) { Pair(S Z, Refl) };
  () }

def pinUse : Checked := prog (pinLib) {
  fn Relay () -> Σ (r : Nat). @claim Id Nat r (S Z) {
    let Pair(a, h) = PinOne();
    Pair(a, h) };
  () }

example : progOkFrom pinLib pinUse.term = true := by native_decide

def pinUseTwin : Term :=
  match Term.replaceMarked? "claim" prog_parse { Id Nat r (S(S(Z))) } pinUse.term with
  | .ok t => t
  | .error _ => .unit

example : (pinUseTwin == pinUse.term) = false := by native_decide
-- The relayed result is the seed's opaque pair (σ₃, σ₄), and the audit names
-- the strengthened claim it cannot meet — the lie, in the seeded message.
example : progRejectsFrom pinLib pinUseTwin
  "result (Pair σ₃ σ₄) does not have return type (Σ(§0 : Nat). Id §0 2)" = true := by
  native_decide

end Dllbc.Tests.MarkedTwins
