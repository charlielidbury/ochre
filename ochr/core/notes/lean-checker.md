# lean-checker: an executable checker for RULES v1, and what running it found

**Verdict:** RULES v1 is implementable as written plus about a dozen clarifications; every example of §7 (E1–E4) is accepted and every round-1 attack (e346 `Bad`, `Oops2`, `Loop`/`Bot'`; meta-model C1, C2; breaker-close A1, A2, A3a, A3b) is rejected, each by the rule that was meant to stop it (shown by switching that rule off and watching the attack go through).
**Most important finding:** v1 is unsound as written (L1): `[Rec]` only looks at recursive *calls*, so a function that passes *itself as a value* to a helper (`Knot x := Apply(Knot, x)`) never makes a recursive call and is accepted at any type, giving a closed proof `Knot(0) : Eq Nat 0 1`. Fix used here: the function may occur in its own body only as the head of a call.
**RULES.md must change:** [Rec] needs the head-only clause (L1). Several clarifications (§3 below) change no verdict but must be written down. D18 (owners are sets) is not exercised by any attack expressible in v1: the only known attack (C2) needs a Π-type that captures a borrow, which v1 already forbids (§4).
**Confidence:** high that the verdicts are what the implementation computes (each is an assertion in a green build, and the traces reproduce the round-1 hand derivations symbol for symbol); medium that the implementation matches the intended reading at every clarification point (§3 lists them).
**Not checked:** metatheory; universe levels beyond `Type_i : Type_{i+1}`; `[Split]` on a sealed program (not in v1, rejected with a clear error); performance beyond the examples.

Location: `ochr/core/lean/` on branch `ochr-core-lean`. Build: `cd ochr/core/lean && lake build`. Run the suite with its table: `lake exe tests`.

## 1. Bugs in RULES v1 (concrete failing runs)

### L1. [Rec] misses a function used as a value in its own body (closed proof of ⊥)

(breaker-close's summary mentions this as its A4, but the note was truncated before A4 was written up, and v1's [Rec] does not address it.)

```
def Apply (f : Π(x : Nat). Eq Nat 0 1) (x : Nat) : Eq Nat 0 1 := f(x)
def Knot (x : Nat) : Eq Nat 0 1 := Apply(Knot, x)
def KnotBoom : Eq Nat 0 1 := Knot(0)
```

With fix L1 switched off (`Config.selfHeadOnly := false`) the checker accepts all three:

```
[Def] Knot: generic call, x ↦ σ0; goal Eq Nat 0 1
  Apply(Knot, x)                     // [Call-type]: Knot : Π(x : Nat). Eq Nat 0 1 matches Apply's parameter; result type Eq Nat 0 1
                                     // [Rec]: the call's head is Apply, not Knot: no recursive call, nothing to check
                                     // P5: Apply's result is a proposition, so the call is not run (and nothing loops)
  Eq Nat 0 1 ≡ goal ✓
[Def] KnotBoom: Knot(0) : Eq Nat 0 1 ✓  // a closed proof of ⊥
```

Without P5 the checker would loop instead of accepting (the pre-v1 situation of e346's `Bot'`); P5 is exactly what turns this into a clean closed proof. Fix: in the body of `fix f`, `f` may occur only as the head of a call (the recursive calls [Rec] then sees are all of its uses). Rejected with the fix: `[Rec] Knot occurs in its own body other than as the head of a call (fix L1)`.

## 2. Verdicts
(filled in at the end)

## 3. Clarifications (ambiguities in v1 and the reading implemented)
(filled in below as they arise)

## 4. D18 is not exercised by any v1-expressible attack
(below)
