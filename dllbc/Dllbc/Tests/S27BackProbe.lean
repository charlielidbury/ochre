import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.DeclMacro
import Dllbc.Tests.S9Diff
import Dllbc.Tests.S17Spec

/-!
# §27 — `back` as an Id-ensures, PROBED on the cursor chain

The hypothesis under test: a declared `back = M` is encodable as the ensures
`-> Id τ (*v) (M (old *v))`, so S19's Architecture-A stratum (the back-carrying
`nth`/`nth2`/`swapS` chain) CONVERTS rather than retires.

The leaf case is already mechanized and is not in doubt: `S23Direct.setAt` /
`swapAt` carry exactly that shape with no `back` anywhere. What this file probes
is the case S19 is actually made of — bodies that do not walk the structure but
**call a cursor**, and cursors that return BORROWS.

## The verdict

**MUTATORS CONVERT. CURSORS RETIRE.** The split is not a matter of degree, and it
falls exactly where the calculus says it should:

* A **Unit-returning mutator** — `swapS`, `partScan` — converts. `swapS` with its
  back deleted and `Id (List Nat) (*v) (swapL i j (old *v))` in its place checks
  (§C3), still calling `nth2`, at a cost of three `let` lines and one cited lemma
  (`swapL_set`, already in `StdLemmas`). Its callers compose (§E1).
* A **borrow-returning cursor** — `nth`, `nth2` — does not, and cannot. Delete
  `nth2`'s back and §C3's caller fails immediately, its list now a bare fresh
  existential (§C5). No ensures recovers it, for a reason that is about the
  calculus rather than the machinery: **a return type is read at exit, and a
  cursor's release is a function of writes that have not happened yet.** `back` is
  precisely the binder for those future values, and a return type has no such
  binder. The three candidate encodings each fail at a different place — the pin
  through `*x` (§B1), the `~>` owed type (§D1), the release itself (§C5).

What a cursor CAN carry is the FRAME class — statements invariant under every
filling of the holes, `len` being the type case. §D2 checks one end to end with no
back anywhere, and §D3 flip-validates the channel. So the ensures channel for a
borrow-returning function is real; it is the value-level statement that is out of
reach.

§F closes the last route. With mixed return types refused, a cursor's contract
could only live in the OWED TYPES, and neither side of the borrow will hold it:

* an **issued** borrow's owed type is checked at BOTH ends against the same `S`
  (issue-time in `collectResultBorrows`, end-time in `endIssued`), so it is an
  invariant of the payload and cannot express a transition (§F1) — and it reaches
  the caller as an OBLIGATION, never as knowledge;
* the **captured** borrow's owed type IS knowledge for the caller (the release σ
  is minted at it), and it still fails: the owed type binds only the ENTRY
  payload, so the caller's future writes must be existentially quantified, which
  loses the identification the swap needs (§F2c).

Same wall both times, which is the point: `back`'s binder for the values that do
not exist yet has no counterpart in a return type OR an owed type.

## The findings that outrank the verdict

Two closed `Bot`s, by two independent rules, both found while establishing that a
green check in this territory means anything at all.

* **§A** — a borrow-carrying return type's non-borrow components are never judged.
  `fn closedBot () -> Bot`. This is the hazard the M27 line walks into, since
  moving every contract into the return type is what makes a declaration both
  borrow-returning and ensures-carrying. **CLOSED** on main by the mixed-return
  containment (eb510a0f); §A's witnesses now assert the refusal, and §G records
  what else the containment took with it.
* **§F2d** — a parameter's owed type is never judged when the body consumes that
  parameter into its result, which for a cursor is always. `fn closedBot2 () ->
  Bot`. §6.1's exemption is sound for the PAYLOAD (there is none to audit — it is
  out on loan) but extends silently to the owed TYPE, which the caller's group end
  then treats as established. **Refusing mixed borrow/non-borrow return types does
  not close this one**: `nth01B` returns `Σ (x : &mut Nat) → &mut Nat`, all
  borrows. F2e is the control — the same lie on a parameter NOT consumed into the
  result is rejected. **OPEN** — the mixed-return containment does not reach it
  (measured in §G, not assumed).
-/

open Dllbc
open Dllbc.StdLemmas (set swapL nth len Le le_refl znots id_congr id_trans id_sym le_rw_r len_set swapL_set count count_swapL')

namespace Dllbc.Tests.S27BackProbe

/-- Rejections are asserted on the message, never on a Bool (S26Seal's rule):
    `hasType` returning `false` and a stuckness error are different verdicts. -/
def ok (d : Decl) (table : List Decl := [d]) : Bool :=
  match checkFn table d with | .ok _ => true | .error _ => false

def rejects (d : Decl) (needle : String) (table : List Decl := [d]) : Bool :=
  match checkFn table d with | .ok _ => false | .error e => strContains e needle

/-- The error a declaration produces, for reading off WHICH rule refused. -/
def why (d : Decl) (table : List Decl := [d]) : String :=
  match checkFn table d with | .ok _ => "<accepted>" | .error e => e

/-! ## §A. The vacuity question, asked FIRST

    Everything downstream depends on it. `checkFn` pins and checks the return
    type as a value ONLY when `hasBorrowT decl.retType` is false (Boundary.lean:63);
    `auditAction`'s borrow-carrying branch checks the ISSUED BORROWS' owed types
    and the argument obligations, and nothing else (Machine.lean:2571-2578). So a
    non-borrow component of a borrow-carrying return type is never judged.

    If that is so, a cursor can STATE any ensures and no body has to earn it — the
    contract would be trusted, not checked, and the hypothesis would be "confirmed"
    by a checker that is not looking. -/

-- A1. A cursor into a list, returning the head borrow beside a FALSE claim
-- (`Id Nat Z (S Z)`) discharged by a `Refl` that cannot inhabit it.
def a1lie : Decl :=
  decl{ fn head_lie (v : &mut List Nat, hi : Le (S Z) (len *v))
        -> Σ (x : &mut Nat) → Id Nat Z (S Z)
        { match v {
            Nil => botElim Unit hi,
            Cons(hd, tl) => Pair(&mut *hd, Refl)
        } } }

-- A2. The value-returning twin of the SAME lie — no borrow in the return type,
-- so the pin-and-check path runs and the lie is caught. The difference between
-- A1 and A2 is exactly `hasBorrowT`.
def a2lie : Decl :=
  decl{ fn val_lie (v : &mut List Nat, hi : Le (S Z) (len *v))
        -> Σ (x : Nat) → Id Nat Z (S Z)
        { Pair(Z, Refl) } }


-- A3. Is the hole VACUOUS or UNSOUND? The caller's `buildResult` mints a σ at
-- the leaf's type, so the caller RECEIVES the unchecked claim as a proof.
def a3use : Decl :=
  decl{ fn absurd (x : &mut List Nat, hx : Le (S Z) (len *x)) -> Id Nat Z (S Z)
        { let p = head_lie(&mut *x, hx);
          match p { Pair(b, h) => h } } }


-- A4. The break, CLOSED: no hypotheses at all, and `Bot` at the return type.
def a4bot : Decl :=
  decl{ fn closedBot () -> Bot
        { let l = Cons(1, Nil);
          let b = &mut l;
          let p = head_lie(b, ());
          match p { Pair(bb, h) => znots Z h } } }


-- A5. CONTROLS. (a) Without the cursor the same absurdity is refused: `Refl`
-- does not inhabit `Id Z (S Z)` when the body is judged. (b) The lie needs the
-- BORROW in the return type, not the Σ: the Σ-of-values twin is A2, rejected.
-- (c) An HONEST claim in the same position is accepted too — which is the point:
-- the position accepts everything, so acceptance there carries no information.
def a5direct : Decl :=
  decl{ fn direct () -> Bot { znots Z Refl } }

def a5honest : Decl :=
  decl{ fn head_true (v : &mut List Nat, hi : Le (S Z) (len *v))
        -> Σ (x : &mut Nat) → Id Nat Z Z
        { match v { Nil => botElim Unit hi, Cons(hd, tl) => Pair(&mut *hd, Refl) } } }

-- ACCEPTED — the claim is never judged.
-- POST-CONTAINMENT (main eb510a0f): REFUSED at its own definition site.
example : rejects a1lie "may not also carry VALUE components" = true := by native_decide
-- REJECTED — the same claim, in a return type with no borrow in it.
example : rejects a2lie "does not have return type" = true := by native_decide
-- ACCEPTED — so the hole is not vacuous: the caller RECEIVES the false proof and
-- returns it at its own (value) return type, where the pin-and-check path DOES
-- run and passes, because the σ genuinely carries that sctx type.
-- a3use and a4bot still check, and that is the containment's SHAPE rather than a
-- residual hole: the gate is at the DEFINITION site, while these hand `a1lie` to
-- the checker inside a TABLE, which `checkFn` consumes without re-checking its
-- entries. In a real program — M26's let-chain, where a callee is a binding
-- lexically above its caller and is checked in place — no such callee exists.
-- Kept green as the pin for exactly that reading.
example : ok a3use [a1lie, a3use] = true := by native_decide
-- ACCEPTED — `fn closedBot () -> Bot`, no hypotheses. The break, closed.
example : ok a4bot [a1lie, a4bot] = true := by native_decide
-- The controls: the direct route to the same absurdity is refused, and the
-- honest claim in the same position is accepted too.
example : rejects a5direct "does not have return type" = true := by native_decide
-- The HONEST claim in the same position is refused too. The containment is
-- shape-based by design, and this is the measurement of what that costs.
example : rejects a5honest "may not also carry VALUE components" = true := by native_decide


/-! ## §B. The three candidate forms for a cursor's contract

    §A says a green check at a cursor's ensures is worthless, so the question is
    re-posed as a STATABILITY question, asked at the CALLER, where the type is
    really consumed: `buildResult` readC's each leaf of the return type at the
    call site and mints a σ at it, so a form the caller cannot read is a form
    that does not exist, whatever the callee's audit says.

    A cursor's contract has two halves, and they are not the same problem:
      (i)  PINNING — what the ISSUED borrows hold at issue (`*x = nth i (old *v)`);
      (ii) THE RELEASE — what the CAPTURED loan becomes when they end. This is
           `back`: a function of values that do not exist yet at the cursor's exit. -/

/-! ### B1. Pinning via `*x` on the returned Σ binder — refused at the caller -/

-- The callee. Accepted, but §A says that is no evidence.
def b1pin : Decl :=
  decl{ fn nth0_pin (v : &mut List Nat, hi : Le (S Z) (len *v))
        -> Σ (x : &mut Nat) → Id Nat (*x) (nth Z (old *v))
        { match v { Nil => botElim Unit hi, Cons(hd, tl) => Pair(&mut *hd, Refl) } } }

-- The caller is where the form is really tested — and this is the refusal.
def b1use : Decl :=
  decl{ fn usePin (v : &mut List Nat, hi : Le (S Z) (len *v)) -> Unit
        { let p = nth0_pin(&mut *v, hi);
          match p { Pair(x, h) => { *x := Z; () } } } }

-- The callee is accepted, and §A says that is no evidence.
-- POST-CONTAINMENT: refused one step earlier, at the shape.
example : rejects b1pin "may not also carry VALUE components" = true := by native_decide
-- The CALLER is the refusal, and it is §D5's refusal arriving on the return side:
-- `buildResult` readC's each leaf BEFORE substituting the components already
-- built (Machine.lean:1038), and `Val` has no deref former for a `*x` to survive
-- as. So the pin cannot be written this way — a bounded machinery gap (thread the
-- built components through the reflect), not a design wall.
example : rejects b1use "dereferenced value is not a borrow" [b1pin, b1use] = true := by native_decide

/-! ## §C. `swapS` CONVERTED — and the one thing the caller has to change

    Probe step 2: back deleted, return type is the ensures, body still calling
    `nth2`. Three readings of `*v` at the audit, measured off the rejection
    messages, and they are the whole story:

      C1  `nth2(v, …)`      — `*v` = `σ5`, a FREE symbol (never defined)
      C2  `nth2(&mut *v, …)`— `*v` = `set i σ8 (set j σ7 (old *v))`
      C3  values read first — `*v` = `set i (nth j s) (set j (nth i s) s)` ✓

    C2 is M22's finding in the ensures form. C3 is the repair, and it is a
    PROGRAM-level one, in the same family as M23's "walk the structure yourself":
    the body stops reading the values back out of the cursors it was handed and
    reads them off the entry snapshot instead, where they are definitional. -/

open Dllbc.Tests.S17Spec (nthS nth2S swapSN)

-- C1. Back deleted from swapS, return type is the ensures, body UNCHANGED.
-- `nth2` still carries its back here, so the release is COMPUTED — the most
-- favourable case for the hypothesis.
def c1swap : Decl :=
  decl{ fn swapS_e (v : &mut List Nat, i : Nat, j : Nat,
                    pij : Le (S i) j, p2 : Le (S j) (len *v))
        -> Id (List Nat) (*v) (swapL i j (old *v))
        { let pr = nth2(v, i, j, pij, p2);
          match pr { Pair(ei, ej) => {
            let t = *ei;
            *ei := *ej;
            *ej := t;
            Refl } } } }


-- C2. The same, but reborrowing (`&mut *v`) instead of moving `v` into the call
-- — the convention every M23 body uses, and the one that leaves `v` locatable at
-- the audit so its exit snapshot has a definition at all.
def c2swap : Decl :=
  decl{ fn swapS_e2 (v : &mut List Nat, i : Nat, j : Nat,
                     pij : Le (S i) j, p2 : Le (S j) (len *v))
        -> Id (List Nat) (*v) (swapL i j (old *v))
        { let pr = nth2(&mut *v, i, j, pij, p2);
          match pr { Pair(ei, ej) => {
            let t = *ei;
            *ei := *ej;
            *ej := t;
            Refl } } } }


-- C3. The gap C2 measures is `σ8`/`σ7` — the values the body wrote, which it
-- read back OUT of the cursors and therefore only knows opaquely. But the caller
-- does not have to learn them from `nth2`: it can read them off the entry
-- snapshot BEFORE the call, exactly as `S23Direct.swap_at` does, and write those
-- instead. Then the pins are DEFINITIONAL and the M22 bridge closes it directly.
def c3swap : Decl :=
  decl{ fn swapS_e3 (v : &mut List Nat, i : Nat, j : Nat,
                     pij : Le (S i) j, p2 : Le (S j) (len *v))
        -> Id (List Nat) (*v) (swapL i j (old *v))
        { let a = nth i (*v);
          let b = nth j (*v);
          let bridge = swapL_set i j (old *v) pij p2;
          let p = nth2(&mut *v, i, j, pij, p2);
          match p { Pair(ei, ej) => {
            *ei := b;
            *ej := a;
            bridge } } } }


-- C4. Flip-validation for C3 (its return type carries no borrow, so the audit's
-- pin-and-check path really runs — §A does not apply here). Two spec lies and one
-- BODY lie: writing the two values back where they came from is a no-op.
def dvT : Term := .deref (.var ⟨0, "v"⟩)
def oldvT : Term := .app (.const "old") dvT
def listNatT : Term := .app (.const "List") (.const "Nat")
def swapT (a b l : Term) : Term := .app (.app (.app swapL a) b) l
def iT : Term := .var ⟨1, "i"⟩
def jT : Term := .var ⟨2, "j"⟩
def sucT (t : Term) : Term := .ctorApp "S" [t]

def c4LieIdx : Decl := { c3swap with retType := .idT listNatT dvT (swapT (sucT iT) jT oldvT) }
def c4LieNoop : Decl := { c3swap with retType := .idT listNatT dvT oldvT }
def c4LieBody : Decl :=
  decl{ fn swapS_e3 (v : &mut List Nat, i : Nat, j : Nat,
                     pij : Le (S i) j, p2 : Le (S j) (len *v))
        -> Id (List Nat) (*v) (swapL i j (old *v))
        { let a = nth i (*v);
          let b = nth j (*v);
          let bridge = swapL_set i j (old *v) pij p2;
          let p = nth2(&mut *v, i, j, pij, p2);
          match p { Pair(ei, ej) => {
            *ei := a;
            *ej := b;
            bridge } } } }

-- C5. THE DECISIVE ONE. The same caller against a `nth2` with its back DELETED —
-- which is what "the stratum converts" would mean. Nothing else changes.
-- (`back` is a token of the `decl{…}` syntax, so the field needs escaping.)
def dropBack (d : Decl) : Decl :=
  { name := d.name, telescope := d.telescope, retType := d.retType, body := d.body,
    «back» := none, dec := d.dec }
def c5nth2NoBack : Decl := dropBack nth2S
def c5nthNoBack : Decl := dropBack nthS

-- C1 — REJECTED, and the exit reading is the free symbol `σ5`: passing `v` itself
-- (rather than `&mut *v`) moves the borrow into the call, so at the audit it is
-- not locatable and its exit snapshot never gets DEFINED. The claim is then
-- neither provable nor refutable — a staging accident, not the real obstacle.
example : rejects c1swap "does not have return type" [nthS, nth2S, c1swap] = true := by native_decide
-- C2 — REJECTED, and this is the real reading: `set i σ8 (set j σ7 (old *v))`.
-- The release IS computed (nth2's back composes), but the two written values are
-- opaque: the body read them back OUT of cursors that were issued opaquely. This
-- is M22's finding reproduced in the ensures form, and the gap it measures is
-- exactly `σ8 = nth j (old *v)`, `σ7 = nth i (old *v)`.
example : rejects c2swap "does not have return type" [nthS, nth2S, c2swap] = true := by native_decide
-- C3 — ACCEPTED. The caller does not need `nth2` to pin anything.
example : ok c3swap [nthS, nth2S, c3swap] = true := by native_decide
-- Flip-validated three ways.
example : rejects c4LieIdx "does not have return type" [nthS, nth2S, c4LieIdx] = true := by native_decide
example : rejects c4LieNoop "does not have return type" [nthS, nth2S, c4LieNoop] = true := by native_decide
example : rejects c4LieBody "does not have return type" [nthS, nth2S, c4LieBody] = true := by native_decide

/-! ## §D. The two forms that remain, measured

    §C leaves `nth2`'s back in place. The hypothesis needs it gone, so §C5 tries
    that and §D asks whether any ensures replaces what is lost. -/

-- D1. The `~>` escape hatch (S27SigProbe §D5) on a RETURNED cursor borrow: state
-- the pin as the borrow's OWED TYPE, entry-relatively. It cannot be paid, and the
-- reason is structural rather than incidental — an owed type is a property of the
-- payload's OWN type, and a cursor's payload is an element of the CALLER's list,
-- whose type the callee does not own.
def d1hatch : Decl :=
  decl{ fn nth0_hatch (v : &mut List Nat, hi : Le (S Z) (len *v))
        -> &mut (t : Nat ~> Σ (r : Nat) → Id Nat r (nth Z (old *v)))
        { match v { Nil => botElim Unit hi, Cons(hd, tl) => &mut *hd } } }

-- D2. The FRAME class. A cursor's exit is a suspension tree with holes where the
-- issued borrows sit, so the statements it can honestly make are exactly those
-- invariant under every filling of the holes. `len` is one: it never reads an
-- element. This is `nth2` with NO back, carrying length preservation as its
-- ensures — and a caller that uses it to prove its OWN length preservation.
def d2nth2len : Decl :=
  decl{ fn nth2L [i] (v : &mut List Nat, i : Nat, j : Nat,
                      pij : Le (S i) j, p2 : Le (S j) (len *v))
        -> Σ (x : &mut Nat) → Σ (y : &mut Nat) → Id Nat (len (*v)) (len (old *v))
        { match v {
            Nil => botElim Unit p2,
            Cons(hd, tl) => match i {
              Z => match j {
                Z => botElim Unit pij,
                S(jjv) => Pair(&mut *hd, Pair(nth(&mut *tl, jjv, p2), Refl))
              },
              S(k) => match j {
                Z => botElim Unit pij,
                S(jj2) => nth2L(&mut *tl, k, jj2, pij, p2)
              }
            }
        } } }

def d2use : Decl :=
  decl{ fn lenPres (v : &mut List Nat, i : Nat, j : Nat,
                    pij : Le (S i) j, p2 : Le (S j) (len *v))
        -> Id Nat (len (*v)) (len (old *v))
        { let p = nth2L(&mut *v, i, j, pij, p2);
          match p { Pair(ei, q) => match q { Pair(ej, h) => {
            *ei := Z;
            *ej := Z;
            h } } } } }

-- D3. The lie twin for D2's CALLER side: the same body against a callee claiming
-- length preservation SHIFTED. If the caller's proof is really the callee's
-- claim, the shifted one cannot discharge the honest goal.
def d3nth2lie : Decl :=
  decl{ fn nth2L [i] (v : &mut List Nat, i : Nat, j : Nat,
                      pij : Le (S i) j, p2 : Le (S j) (len *v))
        -> Σ (x : &mut Nat) → Σ (y : &mut Nat) → Id Nat (S (len (*v))) (len (old *v))
        { match v {
            Nil => botElim Unit p2,
            Cons(hd, tl) => match i {
              Z => match j {
                Z => botElim Unit pij,
                S(jjv) => Pair(&mut *hd, Pair(nth(&mut *tl, jjv, p2), Refl))
              },
              S(k) => match j {
                Z => botElim Unit pij,
                S(jj2) => nth2L(&mut *tl, k, jj2, pij, p2)
              }
            }
        } } }


/-! ## §E. THE CALLER SURVIVES — composition through the converted `swapS` -/

-- E1. `exitAccept`'s shape against the CONVERTED swapS (c3swap: no back, ensures
-- in the return type). The group release is now a fresh σ carrying no computed
-- value, so the caller cannot say `Refl` — it must compose the callee's EQUATION.
-- That is the composition step the hypothesis needs, and it is one term.
def e1accept : Decl :=
  decl{ fn exitAcceptE (v : &mut List Nat, i : Nat, j : Nat,
                        pij : Le (S i) j, p2 : Le (S j) (len *v))
        -> Id (List Nat) (*v) (swapL i j (old *v))
        { swapS_e3(&mut *v, i, j, pij, p2) } }

-- E2. The control: `Refl` in the same position, which is what the BACK-carrying
-- swapS let `S19Partition.exitAccept` write. With the back gone the computed
-- release is gone with it, so this must fail — otherwise E1 proves nothing.
def e2refl : Decl :=
  decl{ fn exitReflE (v : &mut List Nat, i : Nat, j : Nat,
                      pij : Le (S i) j, p2 : Le (S j) (len *v))
        -> Id (List Nat) (*v) (swapL i j (old *v))
        { swapS_e3(&mut *v, i, j, pij, p2); Refl } }

-- E3. A second composition rung: count preservation (swapSE's postcondition)
-- proven from the converted swapS's equation plus the pure lemma, with no back
-- anywhere in the chain below `nth2`.
def e3count : Decl :=
  decl{ fn swapSE_e (v : &mut List Nat, i : Nat, j : Nat,
                     pij : Le (S i) j, p2 : Le (S j) (len *v))
        -> Π (n : Nat) → Id Nat (count n (*v)) (count n (old *v))
        { let cert = (λ (n : Nat). count_swapL' n i j (old *v) pij p2);
          swapS_e3(&mut *v, i, j, pij, p2);
          cert } }


-- E4. E3's repair, and the cost it measures. Under the BACK, the release WAS
-- `swapL i j (old *v)` definitionally, so `swapSE`'s cert matched the goal with
-- no work (S19Partition.swapSE is three lines). With the back converted to an
-- ensures the release is a fresh σ related to the model only PROPOSITIONALLY, so
-- every caller must transport its cert along the equation. That transport is the
-- conversion's per-caller tax, and here it is, in full.
def e4count : Decl :=
  decl{ fn swapSE_e4 (v : &mut List Nat, i : Nat, j : Nat,
                      pij : Le (S i) j, p2 : Le (S j) (len *v))
        -> Π (n : Nat) → Id Nat (count n (*v)) (count n (old *v))
        { let cert = (λ (n : Nat). count_swapL' n i j (old *v) pij p2);
          let h = swapS_e3(&mut *v, i, j, pij, p2);
          (λ (n : Nat).
            id_trans Nat (count n (*v)) (count n (swapL i j (old *v))) (count n (old *v))
              (id_congr (List Nat) Nat (λ (l : List Nat). count n l)
                 (*v) (swapL i j (old *v)) h)
              (cert n)) } }


/-! ### The executing differential — the converted body really swaps

    C3's body no longer READS through the cursors (`let t = *ei; *ei := *ej`); it
    writes values it read off the entry snapshot. That is a different program, so
    the concrete machine has to agree that it is still a swap. -/

def tnat : Nat → Term | 0 => .ctorApp "Z" [] | k + 1 => .ctorApp "S" [tnat k]
def tlist : List Nat → Term | [] => .ctorApp "Nil" [] | x :: xs => .ctorApp "Cons" [tnat x, tlist xs]
def pv (t : Term) : Val := Val.nfV 4000 (Val.Term.toValPure t)

def e5caller (l : List Nat) (i j : Nat) : Term :=
  .letIn ⟨0, "z"⟩ (tlist l)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "z"⟩))
      (.seq (.call "swapS_e3" [.var ⟨1, "b"⟩, tnat i, tnat j, .unit, .unit])
        (.letIn ⟨2, "y"⟩ (.var ⟨0, "z"⟩) .unit)))
def e5run (l : List Nat) (i j : Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec [nthS, nth2S, c3swap] (e5caller l i j) with
  | .ok env =>
    match l.get? i, l.get? j with
    | some a, some b => env.lookup "y" == some (pv (tlist ((l.set i b).set j a)))
    | _, _ => false
  | .error _ => false

example : e5run [1,2,3] 0 2 = true := by native_decide
example : e5run [1,2,3,4] 1 2 = true := by native_decide
example : e5run [4,1,3,2,5] 0 4 = true := by native_decide
example : ok e4count [nthS, nth2S, c3swap, e4count] = true := by native_decide
-- E1 — ACCEPTED: the caller composes the converted callee's equation.
example : ok e1accept [nthS, nth2S, c3swap, e1accept] = true := by native_decide
-- E2 — REJECTED: `Refl`, which the BACK-carrying swapS allowed here
-- (S19Partition.exitAccept), no longer works. So E1 is composition, not luck.
example : rejects e2refl "does not have return type" [nthS, nth2S, c3swap, e2refl] = true := by native_decide
-- E3 — REJECTED: `swapSE`'s three-line body does NOT survive the conversion. Its
-- cert has the model function where the goal now has a σ related to it only
-- propositionally.
example : rejects e3count "does not have return type" [nthS, nth2S, c3swap, e3count] = true := by native_decide
-- D1 — REJECTED: "returned borrow's payload (σ3) does not have its owed type".
example : rejects d1hatch "does not have its owed type" = true := by native_decide
-- D2 — the frame-class ensures WORKS, end to end, with no back anywhere: the
-- caller writes through both cursors and still proves its own length
-- preservation, entirely from the callee's claim.
-- POST-CONTAINMENT: the frame-class ensures is refused at the definition site
-- too — see §G. The two assertions below still measure the CHANNEL, through a
-- table entry, which is what they were for.
example : rejects d2nth2len "may not also carry VALUE components" [nthS, d2nth2len] = true := by native_decide
example : ok d2use [nthS, d2nth2len, d2use] = true := by native_decide
-- D3 — and the caller's proof really IS the callee's claim: a callee claiming a
-- SHIFTED length cannot discharge the honest goal. (The callee side of D2 is
-- unearned until §A is fixed; what D3 validates is the CHANNEL.)
example : rejects d2use "does not have return type" [nthS, d3nth2lie, d2use] = true := by native_decide
-- C5 — the decisive one. `nth2` still CHECKS with its back deleted…
example : ok c5nth2NoBack [nthS, c5nth2NoBack] = true := by native_decide
-- …and C3's caller then FAILS, with the exit reading a bare fresh existential
-- `σ6`: with no back the group releases an unconstrained σ, and the caller's
-- knowledge of its own list is gone. Deleting the back from `nth` too changes
-- nothing — the loss is at `nth2`'s own group end.
example : rejects c3swap "does not have return type" [nthS, c5nth2NoBack, c3swap] = true := by native_decide
example : rejects c3swap "does not have return type" [c5nthNoBack, c5nth2NoBack, c3swap] = true := by native_decide

/-! ## §F. The owed-type route, under the containment

    With mixed borrow/non-borrow return types refused, a cursor's contract can
    only live where the audit already checks: the OWED TYPES. §F asks whether it
    can, on both borrows a cursor touches — the ISSUED ones it hands out (F1) and
    the CAPTURED one it was given (F2). -/

/-! ### F1. An ISSUED borrow's owed type is checked at BOTH ends against the same
    `S`, so it cannot express a transition

    `collectResultBorrows` (callee) substitutes the ISSUE-time payload into `S`
    and checks the issue-time payload against the result; `endIssued` (caller,
    Machine.lean:1326) checks the FINAL payload against the same `S`. One type,
    two moments. So an issued borrow's owed type is an INVARIANT of its payload —
    it cannot say "changed from", and it cannot say "points at position i", which
    is a property of the aliasing rather than of the payload at all. -/

-- F1a. The trivial owed type is all a `Nat` cursor can carry.
def f1triv : Decl :=
  decl{ fn nth0T (v : &mut List Nat, hi : Le (S Z) (len *v)) -> &mut (t : Nat ~> Nat)
        { match v { Nil => botElim Unit hi, Cons(hd, tl) => &mut *hd } } }

-- F1b. A refinement that is TRUE AT END for a caller that writes `Z` is still
-- refused, and refused at the CALLEE — because the same `S` is demanded at issue,
-- where the payload is whatever the caller's list happened to hold.
def f1refine : Decl :=
  decl{ fn nth0R (v : &mut List Nat, hi : Le (S Z) (len *v))
        -> &mut (t : Nat ~> Σ (r : Nat) → Id Nat r Z)
        { match v { Nil => botElim Unit hi, Cons(hd, tl) => &mut *hd } } }

-- F1c. …and the caller learns nothing from it either way: `buildResult` puts the
-- issued σ in `sctx` at the payload TYPE (Machine.lean:1024), never at the owed
-- type. On an issued borrow the owed type is an OBLIGATION ON the caller, not
-- knowledge FOR it — the wrong direction for a contract.
def f1use : Decl :=
  decl{ fn useT (v : &mut List Nat, hi : Le (S Z) (len *v)) -> Id Nat Z Z
        { let r = nth0T(&mut *v, hi);
          *r := Z;
          Refl } }


/-! ### F2. The CAPTURED borrow's owed type — the one direction that is knowledge

    Unlike an issued borrow's, the captured borrow's owed type reaches the caller
    as a FACT: the call rule mints one σ' per captured borrow AND TYPES IT AT THE
    OWED TYPE (Machine.lean:3827-3830), then the group end releases that very σ'
    (Machine.lean:1352). So `&mut (s : List Nat ~> S)` on `nth2`'s parameter is a
    real channel for a release contract. This is the only route left. -/

-- F2a. A fixed-position cursor (i = 0, j = 1) so the probe is about the MECHANISM
-- and not about threading an owed type through a recursion. Its parameter's owed
-- type states the release relationally, entry-relatively, in `s`.
def f2cursor : Decl :=
  decl{ fn nth01H (v : &mut (s : List Nat ~> Σ (l : List Nat) → Σ (r1 : Nat) →
                               Σ (r2 : Nat) → Id (List Nat) l (set Z r1 (set (S Z) r2 s))),
                   p : Le (S (S Z)) (len *v))
        -> Σ (x : &mut Nat) → &mut Nat
        { match v {
            Nil => botElim Unit p,
            Cons(hd, tl) => match tl {
              Nil => botElim Unit p,
              Cons(hd2, tl2) => Pair(&mut *hd, &mut *hd2)
            }
        } } }

-- F2b. THE SOUNDNESS TEST FOR THE ROUTE. The same cursor claiming the release is
-- the ENTRY value unchanged — false for any caller that writes. `v` is consumed
-- into the result, so §6.1's audit EXEMPTS it ("being issued is its exemption"),
-- and nothing else looks. If this is accepted, the captured owed type is an
-- unearned claim exactly as §A's return-type components were.
def f2lie : Decl :=
  decl{ fn nth01L (v : &mut (s : List Nat ~> Σ (l : List Nat) → Id (List Nat) l s),
                   p : Le (S (S Z)) (len *v))
        -> Σ (x : &mut Nat) → &mut Nat
        { match v {
            Nil => botElim Unit p,
            Cons(hd, tl) => match tl {
              Nil => botElim Unit p,
              Cons(hd2, tl2) => Pair(&mut *hd, &mut *hd2)
            }
        } } }

-- F2c. The caller, in M16's unpack style: after the group ends, `*v` holds the
-- PAIR the owed type promised, so the body takes it out, puts the list back, and
-- keeps the evidence. The question is whether that evidence discharges the swap.
def f2use : Decl :=
  decl{ fn swap01H (v : &mut List Nat, p : Le (S (S Z)) (len *v))
        -> Id (List Nat) (*v) (swapL Z (S Z) (old *v))
        { let a = nth Z (*v);
          let b = nth (S Z) (*v);
          let q = nth01H(&mut *v, p);
          match q { Pair(ei, ej) => {
            *ei := b;
            *ej := a;
            let pk = *v;
            match pk { Pair(l, w1) => {
              *v := l;
              match w1 { Pair(r1, w2) => match w2 { Pair(r2, h) => h } }
            } }
          } } } }


-- F2d. THE SECOND BREAK. F2b's lie is accepted, so the captured borrow's owed
-- type on a cursor is unchecked — and it is unchecked for ANY proposition, not
-- just a plausible one. Here it is a flat falsehood, and the caller collects it.
-- NOTE FOR THE CONTAINMENT: this one is NOT closed by refusing mixed
-- borrow/non-borrow RETURN types. `nth01B` returns `Σ (x : &mut Nat) → &mut Nat`
-- — all borrows, perfectly within the containment. The lie is in a PARAMETER's
-- owed type, and it is unchecked because §6.1 exempts an argument borrow consumed
-- into the result ("being issued is its exemption, its story continuing
-- caller-side through the group") — while the caller, for its part, mints the
-- release AT that owed type without ever checking it.
def f2botCursor : Decl :=
  decl{ fn nth01B (v : &mut (s : List Nat ~> Σ (l : List Nat) → Id Nat Z (S Z)),
                   p : Le (S (S Z)) (len *v))
        -> Σ (x : &mut Nat) → &mut Nat
        { match v {
            Nil => botElim Unit p,
            Cons(hd, tl) => match tl {
              Nil => botElim Unit p,
              Cons(hd2, tl2) => Pair(&mut *hd, &mut *hd2)
            }
        } } }

def f2bot : Decl :=
  decl{ fn closedBot2 () -> Bot
        { let x = Cons(1, Cons(2, Nil));
          let b = &mut x;
          let q = nth01B(b, ());
          match q { Pair(ei, ej) => {
            *ei := Z;
            *ej := Z;
            let pk = x;
            match pk { Pair(l, h) => znots Z h }
          } } } }

-- F2e. THE CONTROL that isolates the cause. The same lying owed type on a
-- parameter the body does NOT consume into its result is REJECTED — the audit
-- checks it wherever the borrow is still locatable. So the hole is exactly §6.1's
-- exemption, and nothing else.
def f2ctl : Decl :=
  decl{ fn keepsIt (v : &mut (s : List Nat ~> Σ (l : List Nat) → Id Nat Z (S Z)),
                    p : Le (S (S Z)) (len *v)) -> Unit { () } }

-- F2a — the relational owed type seeds and the cursor checks.
example : ok f2cursor = true := by native_decide
-- F2b — and so does the LIE. Nothing checks it.
example : ok f2lie = true := by native_decide
-- F2d — `fn closedBot2 () -> Bot`. The second break, closed.
example : ok f2botCursor = true := by native_decide
-- POST-CONTAINMENT: STILL ACCEPTED. `nth01B` returns `Σ (x : &mut Nat) → &mut
-- Nat` — all borrows — so the mixed-return gate never sees it. The second break
-- is untouched by the first fix, measured rather than predicted.
example : ok f2bot [f2botCursor, f2bot] = true := by native_decide
-- F2e — the control: not consumed into the result, and it IS checked.
example : rejects f2ctl "does not have its owed type" = true := by native_decide
-- F2c — and even granting the claim, the composition fails. The owed type binds
-- only `s` (the ENTRY payload), so the values the caller will write are
-- unnameable in it and have to be EXISTENTIALLY quantified — which loses exactly
-- the identification the swap needs. This is the same wall as §C5, reached
-- through the owed type instead of the return type.
example : rejects f2use "does not have return type" [f2cursor, f2use] = true := by native_decide
-- F1a — the trivial owed type is accepted.
example : ok f1triv = true := by native_decide
-- F1b — a refinement is refused AT THE CALLEE, at the ISSUE-time check, even
-- though a caller writing `Z` would satisfy it at end. One `S`, two moments.
example : rejects f1refine "does not have its owed type" = true := by native_decide
-- F1c — and the caller learns nothing from it either way.
example : ok f1use [f1triv, f1use] = true := by native_decide

/-! ## §G. Status against the containment (main eb510a0f)

    The mixed-return-type containment landed while this probe was running, so
    every section above was re-run against it. Four assertions flipped, one did
    not, and the pattern is worth recording because it is the containment's exact
    reach.

    REFUSED NOW, as intended: `a1lie` (§A's witness), `b1pin` (§B1's pinning
    form), and — the one worth flagging — `d2nth2len`, §D2's FRAME-CLASS ensures.

    **The containment closes the frame class too.** §D2 was the one honest thing a
    cursor could say: `len` never reads an element, so length preservation holds
    under every filling of the suspension tree's holes, and §D2/§D3 checked it end
    to end with a live lie twin. The containment is shape-based, so it refuses that
    along with the value claims. `a5honest` is the same point in miniature — a TRUE
    claim in that position is refused.

    That is coherent with RETIRE and is not an argument against the containment:
    §F1 shows the alternative home the containment names for a cursor's contract —
    its issued borrows' owed types — can only hold payload INVARIANTS, so after
    the containment a cursor says nothing at all. What is recorded here is that
    this is a decision with a price, and §D2/§D3 are the measurement of the price
    rather than an objection to paying it.

    UNTOUCHED: §F2's second break (`f2bot`). `nth01B`'s return type is all borrows,
    so the gate never sees it; the lie is in a parameter's owed type. Confirmed by
    running it, not by reasoning about it.

    STILL GREEN through table entries: `a3use`, `a4bot`, `b1use`, `d2use`, `d3`.
    These pass an unchecked declaration to `checkFn` in its `table`, which is not
    re-checked — the gate being at the definition site. In M26's let-chain, where a
    callee is a binding checked in place, no such callee can exist, so these are
    the pins for that reading rather than evidence of a residual hole. -/

end Dllbc.Tests.S27BackProbe
