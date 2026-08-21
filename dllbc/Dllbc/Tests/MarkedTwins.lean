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
    pins the result to `S Z`, and `@claim(…)` declares that pin as the attack
    surface. The twin is not written — it is MINTED, by swapping the claim's
    body for `Id Nat r (S (S Z))` in the honest `Term` value. The body still
    returns `Refl` for `S Z`, so the twin is rejected at its own declaration,
    for the meaningful reason (the certificate does not prove the strengthened
    claim), and `twin != honest` pins that the mutation landed. -/

def pinHonest : Term := prog{
  fn PinOne () -> Σ (r : Nat). @claim(Id Nat r (S Z)) { Pair(S Z, Refl) };
  () }

example : progOk pinHonest = true := by native_decide

def pinTwin : Term :=
  match Term.replaceMarked? "claim" ty{ Id Nat %(Dllbc.Term.pvar "r") (S(S(Z))) } pinHonest with
  | .ok t => t
  -- Unreachable while T2 holds; `.unit` cannot satisfy the rejection pin below,
  -- so a contract regression fails T3 rather than passing it vacuously.
  | .error _ => .unit

example : (pinTwin == pinHonest) = false := by native_decide
-- The needle carries the LIE, not just the verdict: the audit names the
-- strengthened claim (`S (S Z)`) the certificate cannot meet, so this pin
-- cannot be satisfied by a twin that was rejected for being garbage.
example : progRejects pinTwin
  "does not have return type (Σ(§0 : Nat). Id #§0 (S (S Z)))" = true := by native_decide

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

end Dllbc.Tests.MarkedTwins
